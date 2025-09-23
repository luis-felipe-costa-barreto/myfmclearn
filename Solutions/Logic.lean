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
  by_cases lem : Q;
  {
    exact lem;
  }
  {
    have nq := nqimplynp lem;
    have := nq hp;
    contradiction;
  }

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
    by_cases lem : Q;
    {
      exact lem;
    }
    {
      have nq := nqimplynp lem;
      have := nq hp;
      contradiction;
    }
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
  by_cases lemp: P;
  {
    right;
    intro q;
    exact lemp;
  }
  {
    left;
    intro p;
    have := lemp p;
    contradiction;
  }


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
  intro nqounp;
  intro peq;
  rcases peq with ⟨ p, q ⟩
  rcases nqounp with (nq | np)
  {
    apply nq q;
  }
  {
    apply np p;
  }

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
  constructor;
  {
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
  }
  {
    intro nqounp;
    intro peq;
    rcases peq with ⟨ p, q ⟩
    rcases nqounp with (nq | np)
    {
      apply nq q;
    }
    {
      apply np p;
    }

  }

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
  constructor;
  {
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
  }
  {
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
  }


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
  intro pe_qour;
  rcases pe_qour with ⟨p , qour ⟩
  rcases qour with ( q | r )
  {
    left;
    constructor;
    {
      exact p;
    }
    {
      exact q;
    }
  }
  {
    right;
    constructor;
    {
      exact p;
    }
    {
      exact r;
    }
  }

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
  intro peq_ou_per;
  rcases peq_ou_per with (peq | per);
  {
    rcases peq with ⟨p , q ⟩
    constructor;
    {
      exact p;
    }
    {
      left;
      exact q;
    }
  }
  {
    rcases per with ⟨p , r ⟩
    constructor;
    {
      exact p;
    }
    {
      right;
      exact r;
    }
  }

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
  intro pou_qer;
  constructor;
  {
    rcases pou_qer with (p | qer);
    {
      left;
      exact p;
    }
    {
      rcases qer with ⟨ q, r ⟩
      right;
      exact q;
    }
  }
  {
    rcases pou_qer with (p | qer);
    {
      left;
      exact p;
    }
    {
      rcases qer with ⟨ q, r ⟩
      right;
      exact r;
    }
  }

theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
  intro pouq_e_pour;
  rcases pouq_e_pour with ⟨ pouq, pour ⟩
  rcases pouq with ( p | q)
  {
    left;
    exact p;
  }
  {
    rcases pour with (p | r)
    {
      left;
      exact p;
    }
    {
      right;
      constructor;
      {
        exact q;
      }
      {
        exact r;
      }
    }

  }


------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
  intro peq_emr;
  intro p;
  intro q;
  apply peq_emr;
  constructor;
  {
    exact p;
  }
  {
    exact q;
  }

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
  intro pem_qemr;
  intro peq;
  rcases peq with ⟨ p, q ⟩
  have r := pem_qemr p q
  exact r;


------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p;
  exact p;


------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
  intro p;
  left;
  exact p;

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
  intro q;
  right;
  exact q;

-- have nome_hipotese : hipotese := by

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
  intro peq;
  rcases peq with ⟨p, q ⟩
  exact p;

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
  intro peq;
  rcases peq with ⟨p, q ⟩
  exact q;


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
  constructor;
  {
    intro poup;
    rcases poup with (p | p)
    {
      exact p;
    }
    {
      exact p;
    }
  }
  {
    intro p;
    left;
    exact p;
  }

theorem conj_idem :
  (P ∧ P) ↔ P := by
  constructor;
  {
    intro pep;
    rcases pep with ⟨ p, p ⟩
    exact p;
  }
  {
    intro p;
    constructor;
    {
      exact p;
    }
    {
      exact p;
    }
  }


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
  intro x;
  contradiction;

theorem true_top :
  P → True  := by
  intro p;
  trivial;


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

-- have nome_hipotese : hipotese := by

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
  intro h;
  intro x;
  intro pdex;
  have ha_xtqpdex : (∃ x, P x) := by
    apply Exists.intro x pdex;
  apply h;
  exact ha_xtqpdex;

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
  intro ha;
  intro hb;
  obtain ⟨ x, pdex ⟩ := hb;
  apply ha x;
  exact pdex;

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
  intro ha;
  sorry;


theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
  intro ha;
  intro hb;
  obtain ⟨ x, npdex ⟩ := ha;
  have pdex := hb x;
  apply npdex;
  exact pdex;

theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
  constructor;
  {
    sorry;
  }
  {
    intro ha;
    intro hb;
    obtain ⟨ x, npdex ⟩ := ha;
    have pdex := hb x;
    apply npdex;
    exact pdex;
  }

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
  constructor;
  {
    intro h;
    intro x;
    intro pdex;
    have ha_xtqpdex : (∃ x, P x) := by
      apply Exists.intro x pdex;
    apply h;
    exact ha_xtqpdex;
  }
  {
    intro ha;
    intro hb;
    obtain ⟨ x, pdex ⟩ := hb;
    apply ha x;
    exact pdex;
  }


------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
  intro ha;
  intro hb;
  obtain ⟨ x, pdex ⟩ := ha;
  apply hb x;
  exact pdex;

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
  intro ha;
  intro hb;
  obtain ⟨ x, npdex ⟩ := hb;
  have pdex := ha x;
  apply npdex pdex;

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
  intro ha;
  intro x;
  sorry;

theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
  intro ha;
  sorry;

theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
  constructor;
  {
    intro ha;
    intro hb;
    obtain ⟨ x, npdex ⟩ := hb;
    have pdex := ha x;
    apply npdex pdex;
  }
  {
    sorry;
  }

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
  constructor;
  {
    intro ha;
    intro hb;
    obtain ⟨ x, pdex ⟩ := ha;
    apply hb x;
    exact pdex;
  }
  {
    sorry;
  }


------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
  intro ha;
  obtain ⟨ x, pdexeqdex ⟩ := ha;
  rcases pdexeqdex with ⟨ pdex, qdex ⟩
  constructor;
  {
    apply Exists.intro x pdex;
  }
  {
    apply Exists.intro x qdex;
  }


theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
  intro ha;
  obtain ⟨ x, pdexouqdex ⟩ := ha;
  rcases pdexouqdex with (pdex | qdex)
  {
    left;
    apply Exists.intro x pdex;
  }
  {
    right;
    apply Exists.intro x qdex;
  }

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
  intro ha;
  rcases ha with ( xpdex | xqdex)
  {
    obtain ⟨ x, pdex ⟩ := xpdex;
    apply Exists.intro x;
    left;
    exact pdex;
  }
  {
    obtain ⟨ x, qdex ⟩ := xqdex;
    apply Exists.intro x;
    right;
    exact qdex;
  }

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
  intro ha;
  constructor;
  {
    intro x;
    have pdexeqdex := ha x;
    rcases pdexeqdex with ⟨ pdex, qdex ⟩
    exact pdex;
  }
  {
    intro x;
    have pdexeqdex := ha x;
    rcases pdexeqdex with ⟨ pdex, qdex ⟩
    exact qdex;
  }

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
  intro ha;
  intro x;
  rcases ha with ⟨ xpdex, xqdex ⟩
  have pdex := xpdex x;
  have qdex := xqdex x;
  constructor;
  {
    exact pdex;
  }
  {
    exact qdex;
  }

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
  intro ha;
  intro x;
  rcases ha with ( xpdex | xqdex)
  {
    left;
    apply xpdex x;
  }
  {
    right;
    apply xqdex x;
  }


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
  sorry;

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
  intro ha;
  obtain ⟨ b, hb ⟩ := ha;
  have hc := hb b;
  rcases hc with ⟨ hd, he ⟩
  sorry;



end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
