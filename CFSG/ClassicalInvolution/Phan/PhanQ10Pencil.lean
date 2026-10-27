module

public import CFSG.ClassicalInvolution.Phan.PhanQ9KGeo

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin Polynomial

section Circle

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

theorem card_norm_le (δ : K) :
    (Finset.univ.filter fun m : K => m * D.τ m = δ).card ≤ Nat.card F + 1 := by
  classical
  set P : K[X] := X ^ (Nat.card F + 1) - C δ with hP
  have hdeg : P.natDegree = Nat.card F + 1 := natDegree_X_pow_sub_C
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  calc (Finset.univ.filter fun m : K => m * D.τ m = δ).card
      ≤ P.roots.toFinset.card := by
        refine Finset.card_le_card fun m hm => ?_
        rw [Finset.mem_filter] at hm
        rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
        simp only [eval_sub, eval_pow, eval_X, eval_C]
        rw [← hm.2, D.tau_pow, pow_succ]
        ring
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = Nat.card F + 1 := hdeg

theorem card_trace_le (hq : 2 ≤ Nat.card F) (A : K) :
    (Finset.univ.filter fun y : K => D.τ y + y + A = 0).card ≤ Nat.card F := by
  classical
  set P : K[X] := X ^ Nat.card F + X + C A with hP
  have hdeg1 : (X ^ Nat.card F + X : K[X]).natDegree = Nat.card F := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow, natDegree_X]
    omega
  have hdeg : P.natDegree = Nat.card F := by
    rw [hP, natDegree_add_eq_left_of_natDegree_lt, hdeg1]
    rw [natDegree_C, hdeg1]
    omega
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  calc (Finset.univ.filter fun y : K => D.τ y + y + A = 0).card
      ≤ P.roots.toFinset.card := by
        refine Finset.card_le_card fun y hy => ?_
        rw [Finset.mem_filter] at hy
        rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, hP]
        simp only [eval_add, eval_pow, eval_X, eval_C]
        rw [← D.tau_pow]
        exact hy.2
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ = Nat.card F := hdeg

theorem circle_card_le (hq : 2 ≤ Nat.card F) {A C : K} (E : K) (hC : D.τ C = C)
    (h : ¬ (A = 0 ∧ E = 0 ∧ C = 0)) :
    (Finset.univ.filter fun μ : K => A + D.τ μ * E + μ * D.τ E + μ * D.τ μ * C = 0).card ≤
      Nat.card F + 1 := by
  by_cases hC0 : C = 0
  · by_cases hE0 : E = 0
    · have hA0 : A ≠ 0 := fun hA0 => h ⟨hA0, hE0, hC0⟩
      have : (Finset.univ.filter fun μ : K => A + D.τ μ * E + μ * D.τ E + μ * D.τ μ * C = 0) =
          ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun μ _ => ?_
        rw [hE0, hC0]
        simpa using hA0
      rw [this]
      simp
    · have hτE : D.τ E ≠ 0 := fun h0 => hE0 (by simpa [D.tau_tau] using congrArg D.τ h0)
      calc (Finset.univ.filter fun μ : K => A + D.τ μ * E + μ * D.τ E + μ * D.τ μ * C = 0).card
          ≤ (Finset.univ.filter fun y : K => D.τ y + y + A = 0).card := by
            refine Finset.card_le_card_of_injOn (fun μ => μ * D.τ E) (fun μ hμ => ?_)
              (fun μ _ μ' _ hμμ' => mul_right_cancel₀ hτE hμμ')
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hμ ⊢
            rw [hC0] at hμ
            rw [map_mul, D.tau_tau]
            linear_combination hμ
        _ ≤ Nat.card F := card_trace_le D hq A
        _ ≤ Nat.card F + 1 := Nat.le_succ _
  · set e : K := E / C with he
    have hCe : C * e = E := by rw [he]; field_simp
    have hτe : D.τ E = C * D.τ e := by rw [← hCe, map_mul, hC]
    set δ : K := (C * (e * D.τ e) - A) / C with hδ
    calc (Finset.univ.filter fun μ : K => A + D.τ μ * E + μ * D.τ E + μ * D.τ μ * C = 0).card
        ≤ (Finset.univ.filter fun m : K => m * D.τ m = δ).card := by
          refine Finset.card_le_card_of_injOn (fun μ => μ + e) (fun μ hμ => ?_)
            (fun μ _ μ' _ hμμ' => add_right_cancel hμμ')
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hμ ⊢
          rw [map_add, hδ]
          field_simp
          rw [← hCe, map_mul, hC] at hμ
          linear_combination hμ
      _ ≤ Nat.card F + 1 := card_norm_le D δ

end Circle

section PencilForms

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem her_pencil_left (s t u : V8 K) (μ : K) :
    her D (s + μ • t) u = her D s u + μ * her D t u := by
  rw [her_add_left, her_smul_left]

theorem her_pencil_right (s t u : V8 K) (μ : K) :
    her D u (s + μ • t) = her D u s + D.τ μ * her D u t := by
  rw [her_add_right, her_smul_right]

theorem her_pencil_self (s t : V8 K) (μ : K) :
    her D (s + μ • t) (s + μ • t) = her D s s + D.τ μ * her D s t + μ * D.τ (her D s t) +
      μ * D.τ μ * her D t t := by
  rw [her_pencil_left, her_pencil_right, her_pencil_right, her_conj_symm D s t]
  ring

theorem gram_pencil (s t x : V8 K) (μ : K) :
    gram D (s + μ • t) x =
      (her D x x * her D s s - her D s x * D.τ (her D s x)) +
        D.τ μ * (her D x x * her D s t - her D s x * D.τ (her D t x)) +
        μ * D.τ (her D x x * her D s t - her D s x * D.τ (her D t x)) +
        μ * D.τ μ * (her D x x * her D t t - her D t x * D.τ (her D t x)) := by
  unfold gram
  rw [her_pencil_self, her_pencil_left, her_pencil_right, her_conj_symm D s x,
    her_conj_symm D t x]
  rw [map_sub, map_mul, map_mul, D.tau_tau, her_self_fixed]
  ring

theorem gram_pencil_ne {s t x : V8 K} (hG : gram D s t ≠ 0) (hx : her D x x ≠ 0) :
    ¬ (her D x x * her D s s - her D s x * D.τ (her D s x) = 0 ∧
      her D x x * her D s t - her D s x * D.τ (her D t x) = 0 ∧
      her D x x * her D t t - her D t x * D.τ (her D t x) = 0) := by
  rintro ⟨h1, h3, h2⟩
  apply hG
  have h3' : her D x x * D.τ (her D s t) - D.τ (her D s x) * her D t x = 0 := by
    have := congrArg D.τ h3
    rw [map_sub, map_mul, map_mul, D.tau_tau, her_self_fixed, map_zero] at this
    exact this
  have key : her D x x ^ 2 * gram D s t = 0 := by
    have e : her D x x ^ 2 * gram D s t =
        (her D x x * her D s s) * (her D x x * her D t t) -
          (her D x x * her D s t) * (her D x x * D.τ (her D s t)) := by
      unfold gram
      rw [her_conj_symm D s t]
      ring
    rw [e, show her D x x * her D s s = her D s x * D.τ (her D s x) by linear_combination h1,
      show her D x x * her D t t = her D t x * D.τ (her D t x) by linear_combination h2,
      show her D x x * her D s t = her D s x * D.τ (her D t x) by linear_combination h3,
      show her D x x * D.τ (her D s t) = D.τ (her D s x) * her D t x by linear_combination h3']
    ring
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (pow_eq_zero_iff (two_ne_zero)|>.1 h) hx
  · exact h

end PencilForms

section Pencil

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε) [Fintype K]
  [DecidableEq K]

theorem exists_good_pencil (hq : 2 ≤ Nat.card F) {m : ℕ}
    (hm : (m + 1) * (Nat.card F + 1) < Nat.card F ^ 2) {s t : V8 K} (hs : Q8 s = 0)
    (ht : Q8 t = 0) (hst : B8 s t = 0) (hG : gram D s t ≠ 0) (x : Fin m → V8 K)
    (hx : ∀ i, ffK D (x i)) (hsx : ∀ i, B8 s (x i) = 0) (htx : ∀ i, B8 t (x i) = 0) :
    ∃ μ : K, ffK D (s + μ • t) ∧ ∀ i, ColK D (s + μ • t) (x i) := by
  by_contra hcon
  have hQ : ∀ μ : K, Q8 (s + μ • t) = 0 := by
    intro μ
    have h2 := Q8_lin (1 : K) μ s t
    rw [one_smul] at h2
    rw [h2, hs, ht, hst]
    ring
  have hB : ∀ (μ : K) (i : Fin m), B8 (s + μ • t) (x i) = 0 := by
    intro μ i
    have := B8_lin_left (1 : K) μ s t (x i)
    rw [one_smul] at this
    rw [this, hsx, htx]
    ring
  have hbad : ∀ μ : K, her D (s + μ • t) (s + μ • t) = 0 ∨
      ∃ i, gram D (s + μ • t) (x i) = 0 := by
    intro μ
    by_contra h
    apply hcon
    refine ⟨μ, ⟨hQ μ, fun h1 => h (Or.inl h1)⟩, fun i => ⟨hB μ i, fun h2 => h (Or.inr ⟨i, h2⟩)⟩⟩
  set Z0 : Finset K := Finset.univ.filter fun μ => her D (s + μ • t) (s + μ • t) = 0 with hZ0
  set Z : Fin m → Finset K := fun i => Finset.univ.filter fun μ => gram D (s + μ • t) (x i) = 0
    with hZ
  have hZ0card : Z0.card ≤ Nat.card F + 1 := by
    have hF0 : ¬ (her D s s = 0 ∧ her D s t = 0 ∧ her D t t = 0) := by
      rintro ⟨h1, h2, h3⟩
      apply hG
      unfold gram
      rw [her_conj_symm D s t, h1, h2, h3]
      simp
    have := circle_card_le D hq (her D s t) (her_self_fixed D t) hF0
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext μ
    simp only [hZ0, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [her_pencil_self]
  have hZcard : ∀ i, (Z i).card ≤ Nat.card F + 1 := by
    intro i
    have hne := gram_pencil_ne D hG (hx i).2 (s := s) (t := t)
    have hCfix : D.τ (her D (x i) (x i) * her D t t - her D t (x i) * D.τ (her D t (x i))) =
        her D (x i) (x i) * her D t t - her D t (x i) * D.τ (her D t (x i)) := by
      rw [map_sub, map_mul, map_mul, D.tau_tau, her_self_fixed, her_self_fixed]
      ring
    have := circle_card_le D hq (her D (x i) (x i) * her D s t - her D s (x i) *
      D.τ (her D t (x i))) hCfix hne
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext μ
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [gram_pencil]
  have hsub : (Finset.univ : Finset K) ⊆ Z0 ∪ Finset.univ.biUnion Z := by
    intro μ _
    rcases hbad μ with h | ⟨i, hi⟩
    · exact Finset.mem_union_left _ (by simp [hZ0, h])
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp [hZ, hi]⟩)
  have hcard : Fintype.card K ≤ (Nat.card F + 1) + m * (Nat.card F + 1) := by
    calc Fintype.card K = (Finset.univ : Finset K).card := Finset.card_univ.symm
      _ ≤ (Z0 ∪ Finset.univ.biUnion Z).card := Finset.card_le_card hsub
      _ ≤ Z0.card + (Finset.univ.biUnion Z).card := Finset.card_union_le _ _
      _ ≤ (Nat.card F + 1) + m * (Nat.card F + 1) := by
        refine add_le_add hZ0card ?_
        calc (Finset.univ.biUnion Z).card ≤ ∑ i, (Z i).card := Finset.card_biUnion_le
          _ ≤ ∑ _i : Fin m, (Nat.card F + 1) := Finset.sum_le_sum fun i _ => hZcard i
          _ = m * (Nat.card F + 1) := by simp
  rw [← Nat.card_eq_fintype_card, D.card_K] at hcard
  nlinarith [hm]

end Pencil

end CFSG.ClassicalInvolution.PhanQ
