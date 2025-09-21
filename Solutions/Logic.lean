section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro hp;
  intro hnp;
  apply hnp hp;

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro hnnp;
  by_cases lem : P;
  {
    assumption;
  }
  {
    have  boom := hnnp lem;
    contradiction;
  }

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
  constructor;
  {
    intro hnnp;
    by_cases lem : P;
    {
      assumption;
    }
    {
      have  boom := hnnp lem;
      contradiction;
    }
  }
  intro hp;
  intro hnp;
  apply hnp hp;


------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro hpouq;
  rcases hpouq with (hp|hq);
  {
    right;
    exact hp;
  }
  {
    left;
    exact hq;
  }

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro hpeq;
  rcases hpeq with ⟨hp , hq⟩;
  constructor;
  {
    exact hq;
  }
  {
    exact hp;
  }


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro npouq;
  intro hp;
  rcases npouq with (hnp | hq);
  {
    have := hnp hp;
    contradiction;
  }
  {
    exact hq;
  }

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro pouq;
  intro hnp;
  rcases pouq with (hp | hq);
  {
    have := hnp hp;
    contradiction;
  }
  {
    exact hq;
  }


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
  intro pimplyq;
  intro hnq;
  intro hp;
  have q := pimplyq hp;
  have := hnq q;
  contradiction;

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
  intro nqimplynp;
  intro hp;
  sorry;

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
  constructor;
  {
    intro pimplyq;
    intro hnq;
    intro hp;
    have q := pimplyq hp;
    have := hnq q;
    contradiction;
  }
  {
    intro nqimplynp;
    intro hp;
    sorry;
  }


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
  intro n_pounp;
  apply n_pounp;
  by_cases lem : P;
  {
    left;
    exact lem;
  }
  {
    right;
    exact lem;
  }


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
  intro pemq_emp;
  intro np;
  apply np;
  apply pemq_emp;
  intro p;
  have := np p;
  contradiction;



------------------------------------------------
-- Linearity of →
------------------------------------------------

theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
  sorry;


------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
  intro pouq;
  intro npenq;
  rcases npenq with ⟨ np, nq ⟩
  rcases pouq with (p | q)
  {
    apply np p;
  }
  {
    apply nq q;
  }

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
  intro peq;
  intro npounq;
  rcases peq with ⟨ p, q ⟩
  rcases npounq with (np | nq)
  {
    apply np p;
  }
  {
    apply nq q;
  }


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
  intro n_pouq;
  constructor;
  {
    intro p;
    apply n_pouq;
    left;
    exact p;
  }
  {
    intro q;
    apply n_pouq;
    right;
    exact q;
  }

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
  intro npenq;
  intro pouq;
  rcases npenq with ⟨ np , nq ⟩
  rcases pouq with (p | q)
  {
    apply np p;
  }
  {
    apply nq q;
  }

theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
  intro n_peq;
  by_cases lemp : P;
  {
    by_cases lemq : Q;
    constructor;
    {
      intro q;
      apply n_peq;
      constructor;
      {
        exact lemp;
      }
      {
        exact lemq;
      }
    }
    {
      left;
      exact lemq;
    }
  }
  {
    right;
    exact lemp;
  }

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
  sorry;

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  sorry

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  sorry


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  sorry

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  sorry

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  sorry

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  sorry


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  sorry

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  sorry


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  sorry


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  sorry

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  sorry

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  sorry

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  sorry


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  sorry

theorem conj_idem :
  (P ∧ P) ↔ P := by
  sorry


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  sorry

theorem true_top :
  P → True  := by
  sorry


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Type)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  sorry

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  sorry

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  sorry

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  sorry

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  sorry

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  sorry

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  sorry

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  sorry


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  sorry

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  sorry

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  sorry

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  sorry

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  sorry


end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
  sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
  sorry


end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
