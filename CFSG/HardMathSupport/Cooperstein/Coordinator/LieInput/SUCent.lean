module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpCent

public section

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.AGLEmbedding.LieOut
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.RootSystem CFSG.LieType.BorelTits

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section Cum

theorem cumE_of_diff {N : ℕ} (e γ c : Fin N → ℤ)
    (he : ∀ a : Fin N, e a = c a * γ a - (if h : 0 < a.val then γ ⟨a.val - 1, by omega⟩ else 0))
    (hc : ∀ a : Fin N, 0 < a.val → c ⟨a.val - 1, by omega⟩ = 1) (j : Fin N) :
    cumE e j = c j * γ j := by
  obtain ⟨j, hj⟩ := j
  induction j with
  | zero =>
    rw [cumE_zero e ⟨0, hj⟩ rfl, he]
    simp
  | succ k ih =>
    have hk : k < N := by omega
    rw [cumE_succ e ⟨k + 1, hj⟩ (by simp)]
    have h1 := ih hk
    have h2 : (⟨(k + 1) - 1, by simp; omega⟩ : Fin N) = ⟨k, hk⟩ := by ext; simp
    simp only [h2, h1]
    rw [he ⟨k + 1, hj⟩]
    have h3 := hc ⟨k + 1, hj⟩ (by simp)
    simp only [Nat.add_sub_cancel] at h3
    rw [h3]
    simp

theorem cumE_toStd (n : ℕ) (γ : Fin (n / 2) → ℤ) (j : Fin (n / 2)) :
    cumE (Unitary.toStd n γ) j =
      (if Even n ∧ j.val + 1 = n / 2 then 2 else 1) * γ j := by
  by_cases hn : Even n
  · refine cumE_of_diff _ γ (fun a => if Even n ∧ a.val + 1 = n / 2 then 2 else 1) ?_ ?_ j
    · intro a
      simp only [Unitary.toStd, hn, if_true, Symplectic.toStd, true_and]
    · intro a ha
      simp only [hn, true_and]
      rw [if_neg]
      have := a.isLt
      omega
  · have h1 : (if Even n ∧ j.val + 1 = n / 2 then (2 : ℤ) else 1) = 1 := by simp [hn]
    rw [h1]
    refine cumE_of_diff _ γ (fun _ => 1) ?_ (fun _ _ => rfl) j
    intro a
    have : Unitary.toStd n γ a = γ a - (if h : 0 < a.val then γ ⟨a.val - 1, by omega⟩ else 0) := by
      unfold Unitary.toStd
      simp [hn]
    rw [this]; simp

theorem cumE_inj {N : ℕ} {e e' : Fin N → ℤ} (h : ∀ j, cumE e j = cumE e' j) : e = e' := by
  funext a
  by_cases ha : 0 < a.val
  · have h1 := cumE_succ e a ha
    have h2 := cumE_succ e' a ha
    have h3 := h ⟨a.val - 1, by omega⟩
    have h4 := h a
    linarith
  · have h1 := cumE_zero e a (by omega)
    have h2 := cumE_zero e' a (by omega)
    have h4 := h a
    linarith

@[expose] def phi {n : ℕ} (j : Fin (n / 2)) (x : Fin n) : ℤ :=
  (if x.val ≤ j.val then 1 else 0) - (if n - 1 - x.val ≤ j.val then 1 else 0)

theorem cumE_weight {n : ℕ} (x : Fin n) (j : Fin (n / 2)) : cumE (weight n x) j = phi j x := by
  have hj := j.isLt
  have hx := x.isLt
  unfold weight phi
  by_cases h1 : x.val < n / 2
  · rw [dif_pos h1, cumE_single]
    have h3 : ¬ (n - 1 - x.val ≤ j.val) := by omega
    simp only [Fin.le_def, if_neg h3]
    simp
  · by_cases h2 : n - 1 - x.val < n / 2
    · rw [dif_neg h1, dif_pos h2, cumE_neg, cumE_single]
      have h3 : ¬ (x.val ≤ j.val) := by omega
      simp [Fin.le_def, h3]
    · rw [dif_neg h1, dif_neg h2]
      have h3 : ¬ (x.val ≤ j.val) := by omega
      have h4 : ¬ (n - 1 - x.val ≤ j.val) := by omega
      simp [cumE, h3, h4]

end Cum

section Rad

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

theorem exists_gamma_toStd (e : Fin (n / 2) → ℤ)
    (hdiv : ∀ l : Fin (n / 2), Even n → l.val + 1 = n / 2 → 2 ∣ cumE e l) :
    ∃ γ, Unitary.toStd n γ = e := by
  refine ⟨fun a => cumE e a / (if Even n ∧ a.val + 1 = n / 2 then 2 else 1), ?_⟩
  apply cumE_inj
  intro j
  rw [cumE_toStd]
  by_cases hc : Even n ∧ j.val + 1 = n / 2
  · simp only [hc, and_self, if_true]
    exact Int.mul_ediv_cancel' (hdiv j hc.1 hc.2)
  · simp only [hc, if_false]; simp

theorem pos_coord_iff (γ : Fin (n / 2) → ℤ) (j : Fin (n / 2)) :
    0 < γ j ↔ 0 < cumE (Unitary.toStd n γ) j := by
  rw [cumE_toStd]; split_ifs <;> omega

theorem phi_last_odd {l : Fin (n / 2)} (hn : Even n) (hl : l.val + 1 = n / 2) (x : Fin n) :
    phi l x = 1 ∨ phi l x = -1 := by
  obtain ⟨r, hr⟩ := hn
  have := x.isLt
  unfold phi
  split_ifs <;> omega

theorem radical_of_pos (γ : Fin (n / 2) → ℤ) (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (j : Fin (n / 2)) (hpos : 0 < γ j) {x : SU (unitaryInvolution F p f) n}
    (hx : x ∈ rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ) :
    x ∈ radical (rootDatum hF n) j :=
  rootGroup_le_radical (D := rootDatum hF n) hγ hpos hx

theorem rootHom_mem_radical {i k : Fin n} (hik : i ≠ k) (hi : i ≠ Fin.rev i) (hk : k ≠ Fin.rev k)
    (hki : k ≠ Fin.rev i) {j : Fin (n / 2)} (hpos : 0 < phi j i - phi j k) (c : Multiplicative F) :
    rootHom (unitaryInvolution F p f) (unitaryInvolution_involutive hF) hik hi hk c ∈
      radical (rootDatum hF n) j := by
  obtain ⟨γ, hγ⟩ := exists_gamma_toStd (n := n) (weight n i - weight n k) (by
    intro l hn _
    rw [cumE_sub, cumE_weight, cumE_weight]
    rcases phi_last_odd hn ‹_› i with h1 | h1 <;> rcases phi_last_odd hn ‹_› k with h2 | h2 <;>
      rw [h1, h2] <;> norm_num)
  have hw : weight n i - weight n k = Unitary.toStd n γ := hγ.symm
  have hroot := mem_roots_of_weight_sub hik hw
  refine radical_of_pos hF γ hroot j ?_ (rootHom_mem _ hik hi hk hki hw c)
  rw [pos_coord_iff, hγ, cumE_sub, cumE_weight, cumE_weight]
  exact hpos

theorem longRootHom_mem_radical {i : Fin n} (hi : i ≠ Fin.rev i) {j : Fin (n / 2)}
    (hpos : 0 < phi j i) (c : Multiplicative (traceZero (unitaryInvolution F p f))) :
    longRootHom (unitaryInvolution F p f) hi c ∈ radical (rootDatum hF n) j := by
  have h2 : (2 : ℕ) • weight n i = weight n i + weight n i := two_nsmul _
  obtain ⟨γ, hγ⟩ := exists_gamma_toStd (n := n) (weight n i + weight n i) (by
    intro l hn _
    rw [cumE_add, cumE_weight]
    rcases phi_last_odd hn ‹_› i with h1 | h1 <;> rw [h1] <;> norm_num)
  have hw : 2 • weight n i = Unitary.toStd n γ := by rw [h2, hγ]
  have hroot : γ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]; exact Or.inr (Or.inl ⟨i, hi, hw.symm⟩)
  refine radical_of_pos hF γ hroot j ?_ (longRootHom_mem _ hi hw c)
  rw [pos_coord_iff, hγ, cumE_add, cumE_weight]
  omega

theorem heisenberg_le_radical {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (hodd : ¬ Even n) {j : Fin (n / 2)} (hpos : 0 < phi j i)
    {x : SU (unitaryInvolution F p f) n}
    (hx : x ∈ heisenbergSubgroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) hi hik hk) :
    x ∈ radical (rootDatum hF n) j := by
  obtain ⟨γ, hγ⟩ := exists_gamma_toStd (n := n) (weight n i) (fun l hn _ => absurd hn hodd)
  have hw : weight n i = Unitary.toStd n γ := hγ.symm
  have hroot : γ ∈ roots (isFiniteType_cartan n) (divisible n) := by
    rw [roots_eq]; exact Or.inr (Or.inr ⟨hodd, i, hi, hw.symm⟩)
  refine radical_of_pos hF γ hroot j ?_ (heisenberg_le _ hi hik hk hw hx)
  rw [pos_coord_iff, hγ, cumE_weight]
  exact hpos

end Rad

section MatLayer

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem mul_single_apply' (M : Matrix (Fin n) (Fin n) F) (a b : Fin n) (c : F) (x y : Fin n) :
    (M * Matrix.single a b c) x y = if y = b then M x a * c else 0 := by
  by_cases h : y = b
  · subst h; simp [Matrix.mul_single_apply_same]
  · simp [h, Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

theorem single_mul_apply' (M : Matrix (Fin n) (Fin n) F) (a b : Fin n) (c : F) (x y : Fin n) :
    (Matrix.single a b c * M) x y = if x = a then c * M b y else 0 := by
  by_cases h : x = a
  · subst h; simp [Matrix.single_mul_apply_same]
  · simp [h, Matrix.single_mul_apply_of_ne _ _ _ _ _ h]

theorem mul_rootMatrix_apply (M : Matrix (Fin n) (Fin n) F) (i k : Fin n) (c : F) (x y : Fin n) :
    (M * rootMatrix σ i k c) x y = M x y + (if y = k then M x i * c else 0) -
      (if y = Fin.rev i then M x (Fin.rev k) * σ c else 0) := by
  simp only [rootMatrix, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.sub_apply,
    Matrix.add_apply, mul_single_apply']

theorem rootMatrix_mul_apply (M : Matrix (Fin n) (Fin n) F) (i k : Fin n) (c : F) (x y : Fin n) :
    (rootMatrix σ i k c * M) x y = M x y + (if x = i then c * M k y else 0) -
      (if x = Fin.rev k then σ c * M (Fin.rev i) y else 0) := by
  simp only [rootMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.add_apply, single_mul_apply']

theorem mul_longRootMatrix_apply (M : Matrix (Fin n) (Fin n) F) (i : Fin n) (c : F) (x y : Fin n) :
    (M * longRootMatrix i c) x y = M x y + (if y = Fin.rev i then M x i * c else 0) := by
  simp only [longRootMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, mul_single_apply']

theorem longRootMatrix_mul_apply (M : Matrix (Fin n) (Fin n) F) (i : Fin n) (c : F) (x y : Fin n) :
    (longRootMatrix i c * M) x y = M x y + (if x = i then c * M (Fin.rev i) y else 0) := by
  simp only [longRootMatrix, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, single_mul_apply']

theorem mul_heisenbergMatrix_apply (M : Matrix (Fin n) (Fin n) F) (i k : Fin n) (a b : F)
    (x y : Fin n) :
    (M * heisenbergMatrix σ i k a b) x y = M x y + (if y = k then M x i * a else 0) -
      (if y = Fin.rev i then M x k * σ a else 0) + (if y = Fin.rev i then M x i * b else 0) := by
  simp only [heisenbergMatrix, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_one, Matrix.sub_apply,
    Matrix.add_apply, mul_single_apply']

theorem heisenbergMatrix_mul_apply (M : Matrix (Fin n) (Fin n) F) (i k : Fin n) (a b : F)
    (x y : Fin n) :
    (heisenbergMatrix σ i k a b * M) x y = M x y + (if x = i then a * M k y else 0) -
      (if x = k then σ a * M (Fin.rev i) y else 0) + (if x = i then b * M (Fin.rev i) y else 0) := by
  simp only [heisenbergMatrix, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.add_apply, single_mul_apply']

end MatLayer

section ShapeSU

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

abbrev InA (j : Fin (n / 2)) (x : Fin n) : Prop := x.val ≤ j.val

abbrev InA' (j : Fin (n / 2)) (x : Fin n) : Prop := (Fin.rev x).val ≤ j.val

@[expose] def AllowedU (j : Fin (n / 2)) (x y : Fin n) : Prop :=
  (InA j x ∧ ¬ InA j y) ∨ (¬ InA j x ∧ ¬ InA' j x ∧ InA' j y)

theorem InA_not_InA' {j : Fin (n / 2)} {x : Fin n} (h : InA j x) : ¬ InA' j x := by
  have := j.isLt
  simp only [InA, InA', Fin.val_rev] at h ⊢
  omega

theorem InA_ne_rev {j : Fin (n / 2)} {x : Fin n} (h : InA j x) : x ≠ Fin.rev x := by
  have := j.isLt
  intro e
  have := congrArg Fin.val e
  simp only [InA, Fin.val_rev] at h this
  omega

theorem shape_of_comm (G : Matrix (Fin n) (Fin n) F) (j : Fin (n / 2)) (aj : Fin n)
    (haj : aj.val = j.val)
    (hunit : ∀ a b, ∑ t, σ (G t a) * G (Fin.rev t) b = if b = Fin.rev a then 1 else 0)
    (hL : ∀ a : Fin n, InA j a →
      G * longRootMatrix a (1 : F) = longRootMatrix a 1 * G)
    (hR : ∀ a y : Fin n, InA j a → ¬ InA j y → y ≠ Fin.rev a → y ≠ Fin.rev y →
      G * rootMatrix σ a y (1 : F) = rootMatrix σ a y 1 * G)
    (hH : ∀ k : Fin n, Fin.rev k = k → ∃ b : F, b + σ b + σ 1 * 1 = 0 ∧
      G * heisenbergMatrix σ aj k (1 : F) b = heisenbergMatrix σ aj k 1 b * G) :
    ∃ gs : F, σ gs * gs = 1 ∧ ∀ x y, ¬ AllowedU j x y → G x y = if x = y then gs else 0 := by
  have hjn := j.isLt
  have hajA : InA j aj := by simp [InA, haj]
  have hrevaj : ¬ InA j (Fin.rev aj) := by
    simp only [InA, Fin.val_rev]; omega
  have L : ∀ a, InA j a → (∀ x, x ≠ a → G x a = 0) ∧ (∀ y, y ≠ Fin.rev a → G (Fin.rev a) y = 0) ∧
      G a a = G (Fin.rev a) (Fin.rev a) := by
    intro a ha
    have key := fun x y => congrFun (congrFun (hL a ha) x) y
    simp only [mul_longRootMatrix_apply, longRootMatrix_mul_apply, mul_one, one_mul,
      add_right_inj] at key
    refine ⟨fun x hx => ?_, fun y hy => ?_, ?_⟩
    · have := key x (Fin.rev a)
      simpa [hx] using this
    · have := key a y
      simpa [hy] using this.symm
    · simpa using key a (Fin.rev a)
  have hN : ∀ a, InA j a → σ (G a a) * G a a = 1 := by
    intro a ha
    obtain ⟨L1, L2, L3⟩ := L a ha
    have h := hunit a (Fin.rev a)
    rw [if_pos rfl, Finset.sum_eq_single a] at h
    · rw [← L3] at h; exact h
    · intro t _ ht; rw [L1 t ht, map_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have R : ∀ a y, InA j a → ¬ InA j y → y ≠ Fin.rev a → y ≠ Fin.rev y →
      ∀ v, G y v = (if v = y then G a a else 0) - (if v = Fin.rev a then G a (Fin.rev y) else 0) := by
    intro a y ha hy hya hyy v
    have key := congrFun (congrFun (hR a y ha hy hya hyy) a) v
    simp only [mul_rootMatrix_apply, rootMatrix_mul_apply, map_one, mul_one, one_mul] at key
    have hay : a ≠ Fin.rev y := fun e => hya (by rw [e, Fin.rev_rev])
    simp only [hay, if_true, if_false, sub_zero] at key
    linear_combination -key
  have gsame : ∀ a, InA j a → G a a = G aj aj := by
    intro a ha
    by_cases hae : a = aj
    · rw [hae]
    · have hya : Fin.rev aj ≠ Fin.rev a := fun e => hae (Fin.rev_injective e).symm
      have hyy : Fin.rev aj ≠ Fin.rev (Fin.rev aj) := by
        rw [Fin.rev_rev]; exact (InA_ne_rev hajA).symm
      have h1 := R a (Fin.rev aj) ha hrevaj hya hyy (Fin.rev aj)
      simp only [if_true] at h1
      have h2 : (Fin.rev aj : Fin n) ≠ Fin.rev a := hya
      simp only [h2, if_false, sub_zero] at h1
      have h3 := (L aj hajA).2.2
      rw [h3, h1]
  have Lrow : ∀ v, G (Fin.rev aj) v = if v = Fin.rev aj then G aj aj else 0 := by
    intro v
    obtain ⟨L1, L2, L3⟩ := L aj hajA
    by_cases hv : v = Fin.rev aj
    · rw [if_pos hv, hv, L3]
    · rw [if_neg hv, L2 v hv]
  have Hrow : ∀ k, Fin.rev k = k → ∀ v, G k v =
      (if v = k then G aj aj else 0) - (if v = Fin.rev aj then G aj k else 0) := by
    intro k hk v
    obtain ⟨b, hb, hcomm⟩ := hH k hk
    have key := congrFun (congrFun hcomm aj) v
    simp only [mul_heisenbergMatrix_apply, heisenbergMatrix_mul_apply, map_one, mul_one,
      one_mul] at key
    have hka : aj ≠ k := fun e => InA_ne_rev hajA (by rw [e, hk])
    simp only [hka, if_true, if_false, sub_zero, add_zero, Lrow v] at key
    by_cases hv : v = Fin.rev aj
    · simp only [hv, if_true] at key ⊢
      have hvk : (Fin.rev aj : Fin n) ≠ k := fun e => hka (by rw [← Fin.rev_rev aj, e, hk])
      simp only [hvk, if_false] at key ⊢
      linear_combination -key
    · simp only [hv, if_false] at key ⊢
      linear_combination -key
  refine ⟨G aj aj, hN aj hajA, fun x y hxy => ?_⟩
  by_cases hy : InA j y
  · obtain ⟨L1, L2, L3⟩ := L y hy
    by_cases hxy' : x = y
    · subst hxy'; rw [if_pos rfl, gsame x hy]
    · rw [if_neg hxy', L1 x hxy']
  · have hx : ¬ InA j x := fun hx => hxy (Or.inl ⟨hx, hy⟩)
    by_cases hx' : InA' j x
    · have hxa : InA j (Fin.rev x) := hx'
      obtain ⟨L1, L2, L3⟩ := L (Fin.rev x) hxa
      have e : Fin.rev (Fin.rev x) = x := Fin.rev_rev x
      rw [e] at L2 L3
      by_cases hxy' : y = x
      · rw [if_pos hxy'.symm, hxy']
        rw [← gsame _ hxa]
        exact L3.symm
      · rw [if_neg (Ne.symm hxy'), L2 y hxy']
    · have hy' : ¬ InA' j y := fun hy' => hxy (Or.inr ⟨hx, hx', hy'⟩)
      have hyne : y ≠ Fin.rev aj := fun e => hy' (by
        simp only [InA', e, Fin.rev_rev]; exact hajA)
      by_cases hmid : x = Fin.rev x
      · have := Hrow x hmid.symm y
        rw [this, if_neg hyne, sub_zero]
        simp only [eq_comm]
      · have hxne : x ≠ Fin.rev aj := fun e => hx' (by
          simp only [InA', e, Fin.rev_rev]; exact hajA)
        have := R aj x hajA hx hxne hmid y
        rw [this, if_neg hyne, sub_zero]
        simp only [eq_comm]

end ShapeSU

section Elts

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

@[expose] noncomputable def heisElt {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) : SU σ n :=
  ⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a),
    by
      rw [heisenbergMatrix_mul σ hi hik hk]
      have h1 : a + -a = 0 := add_neg_cancel a
      have h2 : b + (-b - a * σ a) - a * σ (-a) = 0 := by rw [map_neg]; ring
      rw [h1, h2, heisenbergMatrix_zero],
    by
      rw [heisenbergMatrix_mul σ hi hik hk]
      have h1 : -a + a = 0 := neg_add_cancel a
      have h2 : -b - a * σ a + b - -a * σ a = 0 := by ring
      rw [h1, h2, heisenbergMatrix_zero]⟩,
    det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk hab⟩

theorem heisElt_mem {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k)
    (hk : Fin.rev k = k) (a b : F) (hab : b + σ b + σ a * a = 0) :
    heisElt hσ hi hik hk a b hab ∈ heisenbergSubgroup σ hσ hi hik hk := ⟨a, b, hab, rfl⟩

theorem mat_rootHom {i k : Fin n} (hik : i ≠ k) (hi : i ≠ Fin.rev i) (hk : k ≠ Fin.rev k) (c : F) :
    mat σ n (rootHom σ hσ hik hi hk (Multiplicative.ofAdd c)) = rootMatrix σ i k c := rfl

end Elts

section StageX

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def ShS (j : Fin (n / 2)) (gs : F) (G : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ x y, ¬ AllowedU j x y → G x y = if x = y then gs else 0

theorem InA'_not_InA {j : Fin (n / 2)} {x : Fin n} (h : InA' j x) : ¬ InA j x := fun h' =>
  InA_not_InA' h' h

theorem InA_rev_InA' {j : Fin (n / 2)} {x : Fin n} (h : InA j x) : InA' j (Fin.rev x) := by
  simpa [InA', Fin.rev_rev] using h

theorem sh_colA {j : Fin (n / 2)} {gs : F} {G : Matrix (Fin n) (Fin n) F} (hS : ShS j gs G)
    {v : Fin n} (hv : InA j v) (u : Fin n) : G u v = if u = v then gs else 0 :=
  hS u v (by
    rintro (⟨_, h⟩ | ⟨_, _, h⟩)
    · exact h hv
    · exact InA_not_InA' hv h)

theorem sh_rowA' {j : Fin (n / 2)} {gs : F} {G : Matrix (Fin n) (Fin n) F} (hS : ShS j gs G)
    {u : Fin n} (hu : InA' j u) (v : Fin n) : G u v = if u = v then gs else 0 :=
  hS u v (by
    rintro (⟨h, _⟩ | ⟨_, h, _⟩)
    · exact InA'_not_InA hu h
    · exact h hu)

theorem sh_diagA {j : Fin (n / 2)} {gs : F} {G : Matrix (Fin n) (Fin n) F} (hS : ShS j gs G)
    {x : Fin n} (hx : InA j x) : G x x = gs := by
  rw [sh_colA hS hx, if_pos rfl]

theorem stepX_root (G : Matrix (Fin n) (Fin n) F) {j : Fin (n / 2)} {gs : F} (hgs : gs ≠ 0)
    (hS : ShS j gs G) {x y : Fin n} (hx : InA j x) (hy : ¬ InA j y) (hy' : ¬ InA' j y)
    (c : F) (hc : c = - G x y / gs) :
    ShS j gs (G * rootMatrix σ x y c) ∧ (G * rootMatrix σ x y c) x y = 0 ∧
      ∀ x' y', InA j x' → ¬ InA j y' → ¬ InA' j y' → (x', y') ≠ (x, y) →
        (G * rootMatrix σ x y c) x' y' = G x' y' := by
  have hxy : x ≠ y := fun e => hy (e ▸ hx)
  have hxA' : InA' j (Fin.rev x) := InA_rev_InA' hx
  have hyrx : y ≠ Fin.rev x := fun e => hy' (e ▸ hxA')
  have hcol := sh_colA hS hx
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    rw [mul_rootMatrix_apply, hS u v huv]
    have t1 : (if v = y then G u x * c else 0) = 0 := by
      by_cases hvy : v = y
      · subst hvy
        have hu : ¬ InA j u := fun hu => huv (Or.inl ⟨hu, hy⟩)
        rw [if_pos rfl, hcol u, if_neg (fun e => hu (by rw [e]; exact hx)), zero_mul]
      · rw [if_neg hvy]
    have t2 : (if v = Fin.rev x then G u (Fin.rev y) * σ c else 0) = 0 := by
      by_cases hvx : v = Fin.rev x
      · subst hvx
        have hu1 : ¬ InA j u := fun hu => huv (Or.inl ⟨hu, InA'_not_InA hxA'⟩)
        have hu2 : InA' j u := by
          by_contra hu'
          exact huv (Or.inr ⟨hu1, hu', hxA'⟩)
        rw [if_pos rfl, sh_rowA' hS hu2 (Fin.rev y), if_neg, zero_mul]
        intro e
        apply hy
        have : y = Fin.rev u := by rw [e, Fin.rev_rev]
        rw [this]; exact hu2
      · rw [if_neg hvx]
    rw [t1, t2]; simp
  · rw [mul_rootMatrix_apply, if_pos rfl, if_neg hyrx, sh_diagA hS hx, hc]
    field_simp
    ring
  · intro x' y' hx' hy1 hy2 hne
    rw [mul_rootMatrix_apply]
    have t1 : (if y' = y then G x' x * c else 0) = 0 := by
      by_cases hvy : y' = y
      · subst hvy
        have : x' ≠ x := fun e => hne (by rw [e])
        rw [if_pos rfl, hcol x', if_neg this, zero_mul]
      · rw [if_neg hvy]
    have t2 : (if y' = Fin.rev x then G x' (Fin.rev y) * σ c else 0) = 0 := by
      by_cases hvx : y' = Fin.rev x
      · exact absurd (by rw [hvx]; exact hxA') hy2
      · rw [if_neg hvx]
    rw [t1, t2]; simp

theorem stepX_heis (G : Matrix (Fin n) (Fin n) F) {j : Fin (n / 2)} {gs : F} (hgs : gs ≠ 0)
    (hS : ShS j gs G) {x k : Fin n} (hx : InA j x) (hk : ¬ InA j k) (hk' : ¬ InA' j k)
    (c b : F) (hc : c = - G x k / gs) :
    ShS j gs (G * heisenbergMatrix σ x k c b) ∧ (G * heisenbergMatrix σ x k c b) x k = 0 ∧
      ∀ x' y', InA j x' → ¬ InA j y' → ¬ InA' j y' → (x', y') ≠ (x, k) →
        (G * heisenbergMatrix σ x k c b) x' y' = G x' y' := by
  have hxA' : InA' j (Fin.rev x) := InA_rev_InA' hx
  have hkrx : k ≠ Fin.rev x := fun e => hk' (e ▸ hxA')
  have hcol := sh_colA hS hx
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    rw [mul_heisenbergMatrix_apply, hS u v huv]
    have t1 : (if v = k then G u x * c else 0) = 0 := by
      by_cases hvy : v = k
      · subst hvy
        have hu : ¬ InA j u := fun hu => huv (Or.inl ⟨hu, hk⟩)
        rw [if_pos rfl, hcol u, if_neg (fun e => hu (by rw [e]; exact hx)), zero_mul]
      · rw [if_neg hvy]
    by_cases hvx : v = Fin.rev x
    · subst hvx
      have hu1 : ¬ InA j u := fun hu => huv (Or.inl ⟨hu, InA'_not_InA hxA'⟩)
      have hu2 : InA' j u := by
        by_contra hu'
        exact huv (Or.inr ⟨hu1, hu', hxA'⟩)
      have e1 : G u k = 0 := by
        rw [sh_rowA' hS hu2 k, if_neg]
        intro e
        apply hk'
        rw [← e]; exact hu2
      have e2 : G u x = 0 := by
        rw [hcol u, if_neg]
        intro e
        exact hu1 (by rw [e]; exact hx)
      rw [e2, e1]; simp
    · rw [t1]; simp [hvx]
  · have hkx : k ≠ Fin.rev x := hkrx
    rw [mul_heisenbergMatrix_apply, if_pos rfl, if_neg hkx, sh_diagA hS hx, hc]
    simp only [if_neg hkx]
    field_simp
    ring
  · intro x' y' hx' hy1 hy2 hne
    rw [mul_heisenbergMatrix_apply]
    have t1 : (if y' = k then G x' x * c else 0) = 0 := by
      by_cases hvy : y' = k
      · subst hvy
        have : x' ≠ x := fun e => hne (by rw [e])
        rw [if_pos rfl, hcol x', if_neg this, zero_mul]
      · rw [if_neg hvy]
    have hvx : ¬ y' = Fin.rev x := fun e => hy2 (by rw [e]; exact hxA')
    simp only [hvx, if_false, t1]; ring

theorem phi_A {j : Fin (n / 2)} {a : Fin n} (h : InA j a) : phi j a = 1 := by
  have := InA_not_InA' h
  simp only [InA, InA', Fin.val_rev, not_le] at h this
  have h1 : ¬ (n - 1 - a.val ≤ j.val) := by omega
  simp only [phi]
  rw [if_pos h, if_neg h1]; norm_num

theorem phi_A' {j : Fin (n / 2)} {a : Fin n} (h : InA' j a) : phi j a = -1 := by
  have := InA'_not_InA h
  simp only [InA, InA', Fin.val_rev, not_le] at h this
  have h1 : n - 1 - a.val ≤ j.val := by omega
  simp only [phi]
  rw [if_neg (by omega), if_pos h1]; norm_num

theorem sh_diagA' {j : Fin (n / 2)} {gs : F} {G : Matrix (Fin n) (Fin n) F} (hS : ShS j gs G)
    {x : Fin n} (hx : InA' j x) : G x x = gs := by
  rw [sh_rowA' hS hx, if_pos rfl]

@[expose] def ShS0 (j : Fin (n / 2)) (gs : F) (G : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ x y, ¬ (InA j x ∧ InA' j y) → G x y = if x = y then gs else 0

theorem ShS0.toShS {j : Fin (n / 2)} {gs : F} {G : Matrix (Fin n) (Fin n) F} (h : ShS0 j gs G) :
    ShS j gs G := fun x y hxy => h x y (by
  rintro ⟨hx, hy⟩
  exact hxy (Or.inl ⟨hx, fun h' => InA_not_InA' h' hy⟩))

theorem relY {G : Matrix (Fin n) (Fin n) F} {j : Fin (n / 2)} {gs : F} (h : ShS0 j gs G)
    (hunit : ∀ a b, ∑ t, σ (G t a) * G (Fin.rev t) b = if b = Fin.rev a then 1 else 0)
    {c d : Fin n} (hc : InA j c) (hd : InA j d) :
    σ gs * G c (Fin.rev d) + gs * σ (G d (Fin.rev c)) = 0 := by
  have key := hunit (Fin.rev c) (Fin.rev d)
  have hcd : Fin.rev d ≠ Fin.rev (Fin.rev c) := by
    rw [Fin.rev_rev]
    intro e
    exact InA'_not_InA (InA_rev_InA' hd) (by rw [e]; exact hc)
  rw [if_neg hcd] at key
  have hne : d ≠ Fin.rev c := fun e => InA'_not_InA (InA_rev_InA' hc) (by rw [← e]; exact hd)
  rw [Finset.sum_eq_add d (Fin.rev c) hne] at key
  · have h1 : G (Fin.rev d) (Fin.rev d) = gs := sh_diagA' h.toShS (InA_rev_InA' hd)
    have h2 : G (Fin.rev c) (Fin.rev c) = gs := sh_diagA' h.toShS (InA_rev_InA' hc)
    rw [h1, Fin.rev_rev, h2] at key
    linear_combination key
  · intro t _ ht
    by_cases hta : InA j t
    · have hrow := sh_rowA' h.toShS (InA_rev_InA' hta) (Fin.rev d)
      have : (Fin.rev t : Fin n) ≠ Fin.rev d := fun e => ht.1 (Fin.rev_injective e)
      rw [hrow, if_neg this, mul_zero]
    · have hcol := h t (Fin.rev c) (fun ⟨h1, _⟩ => hta h1)
      rw [hcol, if_neg ht.2, map_zero, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem stepY_long (G : Matrix (Fin n) (Fin n) F) {j : Fin (n / 2)} {gs : F}
    (hS : ShS0 j gs G) {a : Fin n} (ha : InA j a) (c0 : F) (hc : G a (Fin.rev a) + gs * c0 = 0) :
    ShS0 j gs (G * longRootMatrix a c0) ∧ (G * longRootMatrix a c0) a (Fin.rev a) = 0 ∧
      ∀ x y, (x, y) ≠ (a, Fin.rev a) → (G * longRootMatrix a c0) x y = G x y := by
  have hcol : ∀ u, G u a = if u = a then gs else 0 := fun u => sh_colA hS.toShS ha u
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rw [mul_longRootMatrix_apply, hS x y hxy]
    have : (if y = Fin.rev a then G x a * c0 else 0) = 0 := by
      by_cases hy : y = Fin.rev a
      · subst hy
        have hx : x ≠ a := fun e => hxy ⟨by rw [e]; exact ha, InA_rev_InA' ha⟩
        rw [if_pos rfl, hcol x, if_neg hx, zero_mul]
      · rw [if_neg hy]
    rw [this, add_zero]
  · rw [mul_longRootMatrix_apply, if_pos rfl, hcol a, if_pos rfl]
    linear_combination hc
  · intro x y hxy
    rw [mul_longRootMatrix_apply]
    have : (if y = Fin.rev a then G x a * c0 else 0) = 0 := by
      by_cases hy : y = Fin.rev a
      · subst hy
        have hx : x ≠ a := fun e => hxy (by rw [e])
        rw [if_pos rfl, hcol x, if_neg hx, zero_mul]
      · rw [if_neg hy]
    rw [this, add_zero]

theorem stepY_root (G : Matrix (Fin n) (Fin n) F) {j : Fin (n / 2)} {gs : F}
    (hS : ShS0 j gs G) {a b : Fin n} (ha : InA j a) (hb : InA' j b) (hba : b ≠ Fin.rev a)
    (c0 : F) (hc : G a b + gs * c0 = 0) :
    ShS0 j gs (G * rootMatrix σ a b c0) ∧ (G * rootMatrix σ a b c0) a b = 0 ∧
      ∀ x y, (x, y) ≠ (a, b) → (x, y) ≠ (Fin.rev b, Fin.rev a) →
        (G * rootMatrix σ a b c0) x y = G x y := by
  have hbA : InA j (Fin.rev b) := hb
  have hcolA : ∀ u, G u a = if u = a then gs else 0 := fun u => sh_colA hS.toShS ha u
  have hcolB : ∀ u, G u (Fin.rev b) = if u = Fin.rev b then gs else 0 := fun u =>
    sh_colA hS.toShS hbA u
  have hextra : ∀ x y, (G * rootMatrix σ a b c0) x y = G x y +
      ((if y = b then (if x = a then gs * c0 else 0) else 0) -
        (if y = Fin.rev a then (if x = Fin.rev b then gs * σ c0 else 0) else 0)) := by
    intro x y
    rw [mul_rootMatrix_apply, hcolA x, hcolB x]
    by_cases h1 : y = b <;> by_cases h2 : y = Fin.rev a <;> by_cases h3 : x = a <;>
      by_cases h4 : x = Fin.rev b <;> simp [h1, h2, h3, h4] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rw [hextra, hS x y hxy]
    have e1 : (if y = b then (if x = a then gs * c0 else 0) else 0) = 0 := by
      by_cases h1 : y = b
      · by_cases h3 : x = a
        · exact absurd ⟨by rw [h3]; exact ha, by rw [h1]; exact hb⟩ hxy
        · simp [h1, h3]
      · simp [h1]
    have e2 : (if y = Fin.rev a then (if x = Fin.rev b then gs * σ c0 else 0) else 0) = 0 := by
      by_cases h1 : y = Fin.rev a
      · by_cases h3 : x = Fin.rev b
        · exact absurd ⟨by rw [h3]; exact hbA, by rw [h1]; exact InA_rev_InA' ha⟩ hxy
        · simp [h1, h3]
      · simp [h1]
    rw [e1, e2]; simp
  · rw [hextra, if_pos rfl, if_pos rfl, if_neg hba]
    linear_combination hc
  · intro x y h1 h2
    rw [hextra]
    have e1 : (if y = b then (if x = a then gs * c0 else 0) else 0) = 0 := by
      by_cases h3 : y = b
      · have : x ≠ a := fun e => h1 (by rw [e, h3])
        simp [h3, this]
      · simp [h3]
    have e2 : (if y = Fin.rev a then (if x = Fin.rev b then gs * σ c0 else 0) else 0) = 0 := by
      by_cases h3 : y = Fin.rev a
      · have : x ≠ Fin.rev b := fun e => h2 (by rw [e, h3])
        simp [h3, this]
      · simp [h3]
    rw [e1, e2]; simp

end StageX

section GroupStages

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}

open Classical in
@[expose] noncomputable def cntYU (j : Fin (n / 2)) (G : Matrix (Fin n) (Fin n) F) : ℕ :=
  (Finset.univ.filter fun q : Fin n × Fin n =>
    (InA j q.1 ∧ InA' j q.2 ∧ q.1.val ≤ (Fin.rev q.2).val) ∧ G q.1 q.2 ≠ 0).card

theorem stageY {gs : F} (hgs : gs ≠ 0) (hN : unitaryInvolution F p f gs * gs = 1)
    (j : Fin (n / 2)) :
    ∀ g : SU (unitaryInvolution F p f) n, ShS0 j gs (mat (unitaryInvolution F p f) n g) →
      g ∈ radical (rootDatum hF n) j ⊔ Subgroup.center (SU (unitaryInvolution F p f) n) := by
  classical
  have hσ := unitaryInvolution_involutive (K := F) (p := p) (f := f) hF
  set σ₀ := unitaryInvolution F p f with hσ₀
  refine mem_of_peel _ (fun g => ShS0 j gs (mat σ₀ n g)) (fun g => cntYU j (mat σ₀ n g)) ?_ ?_
  · intro g hg h0
    set G := mat σ₀ n g with hG
    have hunit := sum_mat_mul_mat g
    have hz : ∀ x y, InA j x → InA' j y → G x y = 0 := by
      intro x y hx hy
      rcases le_or_gt x.val (Fin.rev y).val with hle | hlt
      · exact card_zero_entries (p := fun q : Fin n × Fin n =>
          InA j q.1 ∧ InA' j q.2 ∧ q.1.val ≤ (Fin.rev q.2).val)
          (f := fun q : Fin n × Fin n => G q.1 q.2) h0 (x, y) ⟨hx, hy, hle⟩
      · have hd : InA j (Fin.rev y) := hy
        have hrel := relY (σ := σ₀) hg hunit hx hd
        rw [Fin.rev_rev] at hrel
        have h1 : G (Fin.rev y) (Fin.rev x) = 0 :=
          card_zero_entries (p := fun q : Fin n × Fin n =>
            InA j q.1 ∧ InA' j q.2 ∧ q.1.val ≤ (Fin.rev q.2).val)
            (f := fun q : Fin n × Fin n => G q.1 q.2) h0 (Fin.rev y, Fin.rev x)
            ⟨hd, InA_rev_InA' hx, by rw [Fin.rev_rev]; exact hlt.le⟩
        rw [h1, map_zero, mul_zero, add_zero] at hrel
        have hσgs : σ₀ gs ≠ 0 := fun e => hgs (by simpa using (map_eq_zero_iff σ₀ σ₀.injective).mp e)
        exact (mul_eq_zero.mp hrel).resolve_left hσgs
    have hmat : G = gs • (1 : Matrix (Fin n) (Fin n) F) := by
      ext x y
      by_cases hxy : InA j x ∧ InA' j y
      · rw [hz x y hxy.1 hxy.2]
        have : x ≠ y := fun e => InA_not_InA' hxy.1 (by rw [e]; exact hxy.2)
        simp [Matrix.one_apply, this]
      · rw [hg x y hxy]
        by_cases e : x = y <;> simp [Matrix.one_apply, e]
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_center_iff]
    intro h
    apply mat_injective
    rw [map_mul, map_mul, ← hG, hmat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro g hg h
    set G := mat σ₀ n g with hG
    have hunit := sum_mat_mul_mat g
    obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hab
    obtain ⟨⟨ha, hb, hle⟩, hne⟩ := hab
    set c0 : F := -(G a b * σ₀ gs) with hc0
    have hcc : G a b + gs * c0 = 0 := by
      rw [hc0]; linear_combination (-(G a b)) * hN
    have hpos : 0 < phi j a - phi j b := by rw [phi_A ha, phi_A' hb]; norm_num
    by_cases hbr : b = Fin.rev a
    · subst hbr
      have hi : a ≠ Fin.rev a := InA_ne_rev ha
      have hrel := relY (σ := σ₀) hg hunit ha ha
      have htz : c0 + σ₀ c0 = 0 := by
        rw [hc0, map_neg, map_mul, hσ]
        linear_combination (-1 : F) * hrel
      let u := longRootHom σ₀ hi (Multiplicative.ofAdd (⟨c0, htz⟩ : traceZero σ₀))
      have hmu : mat σ₀ n (g * u) = G * longRootMatrix a c0 := by
        rw [map_mul]; rfl
      obtain ⟨hS', h0', hsame⟩ := stepY_long G hg ha c0 hcc
      refine ⟨u, Subgroup.mem_sup_left (longRootHom_mem_radical hF hi (by rw [phi_A ha]; norm_num) _),
        ?_, ?_⟩
      · rw [hmu]; exact hS'
      · rw [hmu]
        unfold cntYU
        apply card_lt_of_kill _ (fun q : Fin n × Fin n => G q.1 q.2)
          (fun q : Fin n × Fin n => (G * longRootMatrix a c0) q.1 q.2) (a, Fin.rev a)
        · exact ⟨⟨ha, hb, hle⟩, hne⟩
        · exact h0'
        · intro q _ hq
          exact hsame q.1 q.2 hq
    · have hik : a ≠ b := fun e => InA_not_InA' ha (by rw [e]; exact hb)
      have hi : a ≠ Fin.rev a := InA_ne_rev ha
      have hk : b ≠ Fin.rev b := by
        intro e
        have := InA_ne_rev (show InA j (Fin.rev b) from hb)
        rw [Fin.rev_rev] at this
        exact this e.symm
      let u := rootHom σ₀ hσ hik hi hk (Multiplicative.ofAdd c0)
      have hmu : mat σ₀ n (g * u) = G * rootMatrix σ₀ a b c0 := by
        rw [map_mul]; rfl
      obtain ⟨hS', h0', hsame⟩ := stepY_root G hg ha hb hbr c0 hcc
      refine ⟨u, Subgroup.mem_sup_left (rootHom_mem_radical hF hik hi hk hbr hpos _), ?_, ?_⟩
      · rw [hmu]; exact hS'
      · rw [hmu]
        unfold cntYU
        apply card_lt_of_kill _ (fun q : Fin n × Fin n => G q.1 q.2)
          (fun q : Fin n × Fin n => (G * rootMatrix σ₀ a b c0) q.1 q.2) (a, b)
        · exact ⟨⟨ha, hb, hle⟩, hne⟩
        · exact h0'
        · intro q hq hq'
          refine hsame q.1 q.2 hq' ?_
          intro e
          obtain ⟨⟨hq1, hq2, hq3⟩⟩ := (⟨hq⟩ : Nonempty _)
          have e1 : q.1 = Fin.rev b := congrArg Prod.fst e
          have e2 : q.2 = Fin.rev a := congrArg Prod.snd e
          rw [e1, e2, Fin.rev_rev] at hq3
          have hlt : a.val < (Fin.rev b).val := by
            rcases hle.lt_or_eq with h1 | h1
            · exact h1
            · exact absurd (Fin.ext h1) (fun e' => hbr (by rw [e', Fin.rev_rev]))
          have : (Fin.rev b).val ≤ a.val := hq3
          omega

open Classical in
@[expose] noncomputable def cntXU (j : Fin (n / 2)) (G : Matrix (Fin n) (Fin n) F) : ℕ :=
  (Finset.univ.filter fun q : Fin n × Fin n =>
    (InA j q.1 ∧ ¬ InA j q.2 ∧ ¬ InA' j q.2) ∧ G q.1 q.2 ≠ 0).card

theorem sh0_of_xZero {σ₀ : F ≃+* F} {G : Matrix (Fin n) (Fin n) F} {j : Fin (n / 2)} {gs : F}
    (hgs : gs ≠ 0) (hS : ShS j gs G)
    (hunit : ∀ a b, ∑ t, σ₀ (G t a) * G (Fin.rev t) b = if b = Fin.rev a then 1 else 0)
    (hX : ∀ x y, InA j x → ¬ InA j y → ¬ InA' j y → G x y = 0) : ShS0 j gs G := by
  intro x y hxy
  by_cases hy : InA j y
  · exact sh_colA hS hy x
  · by_cases hy' : InA' j y
    · by_cases hx' : InA' j x
      · exact sh_rowA' hS hx' y
      · by_cases hx : InA j x
        · exact absurd ⟨hx, hy'⟩ hxy
        · have hxy' : x ≠ y := fun e => hx' (by rw [e]; exact hy')
          rw [if_neg hxy']
          have hcolrx : ∀ s, G s (Fin.rev x) = if s = Fin.rev x then gs else 0 := by
            intro s
            have h1 : ¬ InA j (Fin.rev x) := hx'
            have h2 : ¬ InA' j (Fin.rev x) := by simpa [InA', Fin.rev_rev] using hx
            by_cases hs : InA j s
            · rw [hX s _ hs h1 h2, if_neg]
              intro e; exact h1 (by rw [← e]; exact hs)
            · exact hS s _ (by
                rintro (⟨h, _⟩ | ⟨_, _, h⟩)
                · exact hs h
                · exact h2 h)
          have key := hunit y (Fin.rev x)
          rw [if_neg (fun e => hxy' (Fin.rev_injective e))] at key
          rw [Finset.sum_eq_single x] at key
          · rw [hcolrx (Fin.rev x), if_pos rfl] at key
            have h0 : σ₀ (G x y) = 0 := (mul_eq_zero.mp key).resolve_right hgs
            rw [(map_eq_zero_iff σ₀ σ₀.injective).mp h0]
          · intro t _ ht
            rw [hcolrx (Fin.rev t), if_neg (fun e => ht (Fin.rev_injective e)), mul_zero]
          · intro h'; exact absurd (Finset.mem_univ _) h'
    · by_cases hx : InA j x
      · rw [hX x y hx hy hy', if_neg]
        intro e; exact hy (by rw [← e]; exact hx)
      · exact hS x y (by
          rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · exact hx h
          · exact hy' h)

theorem stageX {gs : F} (hgs : gs ≠ 0) (hN : unitaryInvolution F p f gs * gs = 1)
    (j : Fin (n / 2)) :
    ∀ g : SU (unitaryInvolution F p f) n, ShS j gs (mat (unitaryInvolution F p f) n g) →
      g ∈ radical (rootDatum hF n) j ⊔ Subgroup.center (SU (unitaryInvolution F p f) n) := by
  classical
  have hσ := unitaryInvolution_involutive (K := F) (p := p) (f := f) hF
  set σ₀ := unitaryInvolution F p f with hσ₀
  refine mem_of_peel _ (fun g => ShS j gs (mat σ₀ n g)) (fun g => cntXU j (mat σ₀ n g)) ?_ ?_
  · intro g hg h0
    exact stageY hF hgs hN j g (sh0_of_xZero hgs hg (sum_mat_mul_mat g) (fun x y hx hy hy' =>
      card_zero_entries (p := fun q : Fin n × Fin n => InA j q.1 ∧ ¬ InA j q.2 ∧ ¬ InA' j q.2)
        (f := fun q : Fin n × Fin n => mat σ₀ n g q.1 q.2) h0 (x, y) ⟨hx, hy, hy'⟩))
  · intro g hg h
    set G := mat σ₀ n g with hG
    obtain ⟨⟨x, y⟩, hxy⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    obtain ⟨⟨hx, hy, hy'⟩, hne⟩ := hxy
    have hpos : 0 < phi j x := by rw [phi_A hx]; norm_num
    have hxi : x ≠ Fin.rev x := InA_ne_rev hx
    have hxy : x ≠ y := fun e => hy (by rw [← e]; exact hx)
    by_cases hmid : y = Fin.rev y
    ·
      have hodd : ¬ Even n := by
        rintro ⟨r, hr⟩
        have := congrArg Fin.val hmid
        simp only [Fin.val_rev] at this
        omega
      set c : F := -G x y / gs with hc
      have hexists : ∃ b : F, b + σ₀ b = -(σ₀ c * c) := by
        refine exists_add_unitaryInvolution_eq hF ?_
        rw [map_neg, map_mul, hσ]; ring
      obtain ⟨b, hb⟩ := hexists
      have hab : b + σ₀ b + σ₀ c * c = 0 := by linear_combination hb
      let u := heisElt hσ hxi hxy hmid.symm c b hab
      have hmu : mat σ₀ n (g * u) = G * heisenbergMatrix σ₀ x y c b := by
        rw [map_mul]; rfl
      obtain ⟨hS', h0', hsame⟩ := stepX_heis (σ := σ₀) G hgs hg hx hy hy' c b hc
      refine ⟨u, Subgroup.mem_sup_left (heisenberg_le_radical hF hxi hxy hmid.symm hodd hpos
        (heisElt_mem hσ hxi hxy hmid.symm c b hab)), ?_, ?_⟩
      · rw [hmu]; exact hS'
      · rw [hmu]
        unfold cntXU
        apply card_lt_of_kill _ (fun q : Fin n × Fin n => G q.1 q.2)
          (fun q : Fin n × Fin n => (G * heisenbergMatrix σ₀ x y c b) q.1 q.2) (x, y)
        · exact ⟨⟨hx, hy, hy'⟩, hne⟩
        · exact h0'
        · intro q hq hq'
          exact hsame q.1 q.2 hq.1 hq.2.1 hq.2.2 hq'
    · have hk : y ≠ Fin.rev y := hmid
      have hyrx : y ≠ Fin.rev x := fun e => hy' (by rw [e]; exact InA_rev_InA' hx)
      set c : F := -G x y / gs with hc
      let u := rootHom σ₀ hσ hxy hxi hk (Multiplicative.ofAdd c)
      have hmu : mat σ₀ n (g * u) = G * rootMatrix σ₀ x y c := by
        rw [map_mul]; rfl
      obtain ⟨hS', h0', hsame⟩ := stepX_root (σ := σ₀) G hgs hg hx hy hy' c hc
      have hpos2 : 0 < phi j x - phi j y := by
        have : phi j y = 0 := by
          have h1 : ¬ (y.val ≤ j.val) := hy
          have h2 : ¬ (n - 1 - y.val ≤ j.val) := by
            simp only [InA', Fin.val_rev] at hy'; omega
          simp only [phi]
          rw [if_neg h1, if_neg h2]; norm_num
        rw [phi_A hx, this]; norm_num
      refine ⟨u, Subgroup.mem_sup_left (rootHom_mem_radical hF hxy hxi hk hyrx hpos2 _), ?_, ?_⟩
      · rw [hmu]; exact hS'
      · rw [hmu]
        unfold cntXU
        apply card_lt_of_kill _ (fun q : Fin n × Fin n => G q.1 q.2)
          (fun q : Fin n × Fin n => (G * rootMatrix σ₀ x y c) q.1 q.2) (x, y)
        · exact ⟨⟨hx, hy, hy'⟩, hne⟩
        · exact h0'
        · intro q hq hq'
          exact hsame q.1 q.2 hq.1 hq.2.1 hq.2.2 hq'

end GroupStages

section FinalSU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem phi_nonpos {j : Fin (n / 2)} {y : Fin n} (hy : ¬ InA j y) : phi j y ≤ 0 := by
  have h1 : ¬ (y.val ≤ j.val) := hy
  simp only [phi]
  rw [if_neg h1]
  split_ifs <;> norm_num

theorem centOb_su {I : Set (Fin (rootDatum hF n).rank)} (hI : I ≠ Set.univ) :
    CentOb (rootDatum hF n) I := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := unitaryInvolution_involutive (K := F) (p := 2) (f := f) hF
  set σ₀ := unitaryInvolution F 2 f with hσ₀
  obtain ⟨j, hj⟩ : ∃ j : Fin (rootDatum hF n).rank, j ∉ I := by
    by_contra h
    push Not at h
    exact hI (Set.eq_univ_of_forall h)
  let j' : Fin (n / 2) := j
  intro k hk
  have hkr : ∀ u ∈ radical (rootDatum hF n) j, k * u = u * k :=
    fun u hu => hk u (radical_le_leviRad hj hu)
  have hmat : ∀ u ∈ radical (rootDatum hF n) j, mat σ₀ n k * mat σ₀ n u = mat σ₀ n u * mat σ₀ n k :=
    fun u hu => by rw [← map_mul, ← map_mul, hkr u hu]
  have hjn := j'.isLt
  let aj : Fin n := ⟨j'.val, by omega⟩
  have haj : aj.val = j'.val := rfl
  have hajA : InA j' aj := by simp [InA, haj]
  have htz1 : (1 : F) + σ₀ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero (1 : F)
  have hshape := shape_of_comm (mat σ₀ n k) j' aj haj (sum_mat_mul_mat k)
    (fun a ha => by
      have hi : a ≠ Fin.rev a := InA_ne_rev ha
      have := hmat _ (longRootHom_mem_radical hF hi (j := j') (by rw [phi_A ha]; norm_num)
        (Multiplicative.ofAdd (⟨1, htz1⟩ : traceZero σ₀)))
      exact this)
    (fun a y ha hy hya hyy => by
      have hi : a ≠ Fin.rev a := InA_ne_rev ha
      have hay : a ≠ y := fun e => hy (by rw [← e]; exact ha)
      have hpos : 0 < phi j' a - phi j' y := by
        have := phi_nonpos (j := j') hy
        rw [phi_A ha]; omega
      exact hmat _ (rootHom_mem_radical hF hay hi hyy hya hpos (j := j') (Multiplicative.ofAdd (1 : F))))
    (fun kk hkk => by
      have hodd : ¬ Even n := by
        rintro ⟨r, hr⟩
        have := congrArg Fin.val hkk
        simp only [Fin.val_rev] at this
        omega
      have hi : aj ≠ Fin.rev aj := InA_ne_rev hajA
      have hik : aj ≠ kk := fun e => hi (by rw [e, hkk])
      have hexists : ∃ b : F, b + σ₀ b = -(σ₀ 1 * 1) := by
        refine exists_add_unitaryInvolution_eq hF ?_
        rw [map_neg, map_mul, hσ]; simp
      obtain ⟨b, hb⟩ := hexists
      have hab : b + σ₀ b + σ₀ 1 * 1 = 0 := by linear_combination hb
      exact ⟨b, hab, hmat _ (heisenberg_le_radical hF hi hik hkk hodd (j := j')
        (by rw [phi_A hajA]; norm_num) (heisElt_mem hσ hi hik hkk 1 b hab))⟩)
  obtain ⟨gs, hN, hsh⟩ := hshape
  have hgs : gs ≠ 0 := by
    rintro rfl
    simp at hN
  have := stageX hF hgs hN j' k hsh
  exact (sup_le_sup_right (radical_le_leviRad hj) _) this

end FinalSU

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
