module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionHermitianBasic
public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace MatrixExtension

open Matrix
open scoped commutatorElement

section Decomposition

variable {K : Type*} [Field K] {r : ℕ}

theorem hconj_apply (B : Matrix (Fin r) (Fin r) K) (x y : Fin r) : hconj B x y = B y x ^ 2 :=
  rfl

theorem hermO_apply (i j : Fin r) (u : K) (x y : Fin r) :
    hermO i j u x y = (if i = x ∧ j = y then u else 0) + if j = x ∧ i = y then u ^ 2 else 0 := by
  rw [hermO, Matrix.add_apply, single_apply, single_apply]

theorem hermO_apply_eq_zero {i j x y : Fin r} (u : K) (h₁ : ¬(i = x ∧ j = y))
    (h₂ : ¬(j = x ∧ i = y)) : hermO i j u x y = 0 := by
  rw [hermO_apply, ite_eq_right h₁, ite_eq_right h₂, add_zero]

theorem hermO_apply_left {i j : Fin r} (hij : i ≠ j) (u : K) : hermO i j u i j = u := by
  rw [hermO_apply, ite_eq_left (show i = i ∧ j = j from ⟨rfl, rfl⟩),
    ite_eq_right (show ¬(j = i ∧ i = j) from fun h => hij h.2), add_zero]

theorem hermO_apply_right {i j : Fin r} (hij : i ≠ j) (u : K) : hermO i j u j i = u ^ 2 := by
  rw [hermO_apply, ite_eq_right (show ¬(i = j ∧ j = i) from fun h => hij h.1),
    ite_eq_left (show j = j ∧ i = i from ⟨rfl, rfl⟩), zero_add]

theorem hermD_apply (k x y : Fin r) :
    (hermD k : Matrix (Fin r) (Fin r) K) x y = if k = x ∧ k = y then 1 else 0 :=
  single_apply ..

theorem herm_diag {B : Matrix (Fin r) (Fin r) K} (hB : hconj B = B) (k : Fin r) :
    B k k = 0 ∨ B k k = 1 := by
  have h : B k k ^ 2 = B k k := (hconj_apply B k k).symm.trans (congrFun₂ hB k k)
  have h' : B k k * (B k k - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

theorem sum_single_diag_apply (B : Matrix (Fin r) (Fin r) K) (x y : Fin r) :
    (∑ k, single k k (B k k)) x y = if x = y then B x x else 0 := by
  simp only [Matrix.sum_apply, single_apply]
  by_cases h : x = y
  · subst h
    simp
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun k _ => ite_eq_right fun hk => h (hk.1.symm.trans hk.2)

theorem upperSum_hermO_apply (f : Matrix (Fin r) (Fin r) K) (x y : Fin r) :
    (∑ p ∈ binaryUpperPairs r, hermO p.1 p.2 (f p.1 p.2)) x y =
      if x < y then f x y else if y < x then f y x ^ 2 else 0 := by
  have h1 : ∀ p : Fin r × Fin r, (p.1 = x ∧ p.2 = y) ↔ p = (x, y) := fun p => by
    rw [Prod.ext_iff]
  have h2 : ∀ p : Fin r × Fin r, (p.2 = x ∧ p.1 = y) ↔ p = (y, x) := fun p => by
    rw [Prod.ext_iff, and_comm]
  simp only [Matrix.sum_apply, hermO_apply, h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [binaryUpperPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with hab hba hba <;> first | exact absurd hab (lt_asymm hba) | simp

theorem herm_decomp {B : Matrix (Fin r) (Fin r) K} (hB : hconj B = B) :
    B = ∑ k, single k k (B k k) + ∑ p ∈ binaryUpperPairs r, hermO p.1 p.2 (B p.1 p.2) := by
  ext x y
  rw [Matrix.add_apply, sum_single_diag_apply, upperSum_hermO_apply]
  rcases lt_trichotomy x y with h | rfl | h
  · rw [ite_eq_right h.ne, ite_eq_left h, zero_add]
  · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl x), ite_eq_right (lt_irrefl x), add_zero]
  · rw [ite_eq_right h.ne', ite_eq_right (lt_asymm h), ite_eq_left h, zero_add, ← hconj_apply,
      hB]

theorem herm_mem {S : AddSubgroup (Matrix (Fin r) (Fin r) K)} (hD : ∀ k, hermD k ∈ S)
    (hO : ∀ i j, i < j → ∀ u, hermO i j u ∈ S) {B : Matrix (Fin r) (Fin r) K}
    (hB : hconj B = B) : B ∈ S := by
  rw [herm_decomp hB]
  refine add_mem (sum_mem fun k _ => ?_)
    (sum_mem fun p hp => hO _ _ (Finset.mem_filter.mp hp).2 _)
  rcases herm_diag hB k with h | h
  · rw [h, single_zero]
    exact zero_mem S
  · rw [h]
    exact hD k

end Decomposition

section Separation

variable {K : Type*} [Field K] {r : ℕ}

theorem herm_exists_ne_three (hr : 4 ≤ r) (a b c : Fin r) :
    ∃ l : Fin r, l ≠ a ∧ l ≠ b ∧ l ≠ c := by
  classical
  by_contra! h
  have hsub : (Finset.univ : Finset (Fin r)) ⊆ {a, b, c} := fun z _ => by
    by_cases hza : z = a
    · simp [hza]
    by_cases hzb : z = b
    · simp [hzb]
    simp [h z hza hzb]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_three (a := a) (b := b) (c := c)
  omega

theorem exists_sep_units {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {a b i j : Fin r} (hij : i ≠ j)
    (h₁ : ¬(i = a ∧ j = b)) (h₂ : ¬(i = b ∧ j = a)) :
    ∃ e : Fin r → Kˣ, e a = e b ∧ e i ≠ e j := by
  classical
  have hw : Units.mk0 ω hω0 ≠ 1 := fun h => hω1 (by simpa using congrArg Units.val h)
  by_cases hi : i ≠ a ∧ i ≠ b
  · refine ⟨Pi.mulSingle i (Units.mk0 ω hω0), ?_, ?_⟩
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hi.1), Pi.mulSingle_eq_of_ne (Ne.symm hi.2)]
    · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hij)]
      exact hw
  · have hj : j ≠ a ∧ j ≠ b := by
      rcases not_and_or.mp hi with h | h
      · obtain rfl := not_not.mp h
        exact ⟨Ne.symm hij, fun h' => h₁ ⟨rfl, h'⟩⟩
      · obtain rfl := not_not.mp h
        exact ⟨fun h' => h₂ ⟨rfl, h'⟩, Ne.symm hij⟩
    refine ⟨Pi.mulSingle j (Units.mk0 ω hω0), ?_, ?_⟩
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hj.1), Pi.mulSingle_eq_of_ne (Ne.symm hj.2)]
    · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij]
      exact Ne.symm hw

theorem exists_sep_units_prod_aux (hK : Nat.card K = 4) (hr : 4 ≤ r) {ω : K} (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) {a b c p : Fin r} (hca : c ≠ a) (hcb : c ≠ b) (hcp : c ≠ p) :
    ∃ e : Fin r → Kˣ, ∏ k, (e k : K) = 1 ∧ e a = e b ∧ e c ≠ e p := by
  obtain ⟨c', hc'a, hc'b, hc'c⟩ := herm_exists_ne_three hr a b c
  have hw : Units.mk0 ω hω0 ≠ 1 := fun h => hω1 (by simpa using congrArg Units.val h)
  refine ⟨twoPoint c c' (Units.mk0 ω hω0) (Units.mk0 ω hω0 ^ 2), ?_, ?_, ?_⟩
  · rw [prod_twoPoint (Ne.symm hc'c), Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_succ']
    exact four_pow_three hK hω0
  · rw [twoPoint_apply_of_ne (Ne.symm hca) (Ne.symm hc'a),
      twoPoint_apply_of_ne (Ne.symm hcb) (Ne.symm hc'b)]
  · rw [twoPoint_apply_left]
    by_cases hpc' : p = c'
    · subst hpc'
      rw [twoPoint_apply_right (Ne.symm hc'c)]
      intro h
      have h' : ω = ω ^ 2 := by simpa using congrArg Units.val h
      have h'' : ω * (ω - 1) = 0 := by linear_combination -h'
      rcases mul_eq_zero.mp h'' with h0 | h1
      · exact hω0 h0
      · exact hω1 (sub_eq_zero.mp h1)
    · rw [twoPoint_apply_of_ne (Ne.symm hcp) hpc']
      exact hw

theorem exists_sep_units_prod (hK : Nat.card K = 4) (hr : 4 ≤ r) {ω : K} (hω0 : ω ≠ 0)
    (hω1 : ω ≠ 1) {a b i j : Fin r} (hij : i ≠ j) (h₁ : ¬(i = a ∧ j = b))
    (h₂ : ¬(i = b ∧ j = a)) : ∃ e : Fin r → Kˣ, ∏ k, (e k : K) = 1 ∧ e a = e b ∧ e i ≠ e j := by
  by_cases hi : i ≠ a ∧ i ≠ b
  · exact exists_sep_units_prod_aux hK hr hω0 hω1 hi.1 hi.2 hij
  · have hj : j ≠ a ∧ j ≠ b := by
      rcases not_and_or.mp hi with h | h
      · obtain rfl := not_not.mp h
        exact ⟨Ne.symm hij, fun h' => h₁ ⟨rfl, h'⟩⟩
      · obtain rfl := not_not.mp h
        exact ⟨fun h' => h₂ ⟨rfl, h'⟩, Ne.symm hij⟩
    obtain ⟨e, he, hab, hji⟩ := exists_sep_units_prod_aux hK hr hω0 hω1 hj.1 hj.2 (Ne.symm hij)
    exact ⟨e, he, hab, Ne.symm hji⟩

end Separation

section Core

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ} {Γ : Subgroup (GL (Fin r) K)}
  {M : Type*} [AddCommGroup M] [DistribMulAction Γ M] {π : M →+ Matrix (Fin r) (Fin r) K}

@[expose] def elemΓ (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    {a b : Fin r} (h : a ≠ b) (t : K) : Γ :=
  ⟨hElemGL h t, hSL _ (hElemGL_det h t)⟩

omit [CharP K 2] in
theorem elemΓ_coe (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    {a b : Fin r} (h : a ≠ b) (t : K) :
    (((elemΓ hSL h t : Γ) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) = hElem a b t :=
  rfl

omit [CharP K 2] in
theorem elemΓ_mul (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    {a b : Fin r} (h : a ≠ b) (t u : K) :
    elemΓ hSL h t * elemΓ hSL h u = elemΓ hSL h (t + u) :=
  Subtype.ext (hElemGL_mul h t u)

omit [CharP K 2] in
theorem elemΓ_zero (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    {a b : Fin r} (h : a ≠ b) : elemΓ hSL h (0 : K) = 1 :=
  Subtype.ext (hElemGL_zero h)

theorem elemΓ_inv (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    {a b : Fin r} (h : a ≠ b) (t : K) : (elemΓ hSL h t)⁻¹ = elemΓ hSL h t :=
  Subtype.ext (by rw [Subgroup.coe_inv]; exact hElemGL_inv h t)

omit [CharP K 2] in
theorem commutatorElement_elemΓ
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (s t : K) :
    ⁅elemΓ hSL hab s, elemΓ hSL hbc t⁆ = elemΓ hSL hac (s * t) :=
  Subtype.ext (by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (commutatorElement_def _ _).symm.trans (commutatorElement_hElemGL hab hbc hac s t))

@[expose] def torusΓ (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (d : Fin r → Kˣ) (hd : ∏ i, (d i : K) = 1) : Γ :=
  ⟨hTorusGL d, hSL _ (by rw [hTorusGL_det, hd])⟩

omit [CharP K 2] in
theorem act_eq_of_pow_three [Module (ZMod 2) M] (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {g : Γ}
    (hg : g ^ 3 = 1) {x : M} (h : g • x - x ∈ π.ker) : g • x = x := by
  obtain ⟨c, hc, e⟩ : ∃ c ∈ π.ker, g • x = x + c := ⟨_, h, by abel⟩
  have h3 : (g ^ 3) • x = x + c + c + c := by
    rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, e, smul_add, e, hC g c hc, smul_add,
      smul_add, e, hC g c hc]
  rw [hg, one_smul] at h3
  have h2 : c + c = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [e]
  linear_combination (norm := abel) h3 + (2 : ℤ) • h2

section Torus

variable [Module (ZMod 2) M]

omit [CharP K 2] [Module (ZMod 2) M] in
theorem torus_pow_three (hK : Nat.card K = 4) {s : Γ} {d : Fin r → Kˣ}
    (hs : (s : GL (Fin r) K) = hTorusGL d) : s ^ 3 = 1 :=
  Subtype.ext (by rw [Subgroup.coe_pow, hs, hTorusGL_pow_three hK, Subgroup.coe_one])

omit [CharP K 2] [Module (ZMod 2) M] in
theorem torus_mul_elemΓ
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ) {s : Γ}
    {d : Fin r → Kˣ} (hs : (s : GL (Fin r) K) = hTorusGL d) {a b : Fin r} (hab : a ≠ b) (t : K) :
    s * elemΓ hSL hab t = elemΓ hSL hab ((d a : K) * t * ((d b : K))⁻¹) * s :=
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs]
    exact hTorusGL_mul_hElemGL d hab t)

theorem torus_fix_diag (hK : Nat.card K = 4)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {s : Γ} {d : Fin r → Kˣ}
    (hs : (s : GL (Fin r) K) = hTorusGL d) {k : Fin r} {x : M} (hx : π x = hermD k) :
    s • x = x := by
  refine act_eq_of_pow_three hC (torus_pow_three hK hs) ?_
  rw [AddMonoidHom.mem_ker, map_sub, hπact, hs, hTorusGL_coe, hx,
    diagonal_congr_hermD _ k (four_pow_three hK (d k).ne_zero)]
  exact sub_self _

omit [Module (ZMod 2) M] in
theorem torus_act_hermO (hK : Nat.card K = 4)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    {s : Γ} {d : Fin r → Kˣ} (hs : (s : GL (Fin r) K) = hTorusGL d) {i j : Fin r} {u : K}
    {x : M} (hx : π x = hermO i j u) :
    π (s • x) = hermO i j ((d i : K) * (d j : K) ^ 2 * u) := by
  rw [hπact, hs, hTorusGL_coe, hx, diagonal_congr_hermO hK]

omit [CharP K 2] [Module (ZMod 2) M] in
theorem exists_torus_omega (hK : Nat.card K = 4)
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ) {ω : K}
    (hω0 : ω ≠ 0) {a b : Fin r} (hab : a ≠ b) :
    ∃ (s : Γ) (d : Fin r → Kˣ), (s : GL (Fin r) K) = hTorusGL d ∧ (d a : K) = ω ^ 2 ∧
      (d b : K) = ω ∧ ∀ i, i ≠ a → i ≠ b → (d i : K) = 1 := by
  set w := Units.mk0 ω hω0
  refine ⟨torusΓ hSL (twoPoint a b (w ^ 2) w) (by
      rw [prod_twoPoint hab, Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_succ]
      exact four_pow_three hK hω0), twoPoint a b (w ^ 2) w, rfl, ?_, ?_, ?_⟩
  · rw [twoPoint_apply_left, Units.val_pow_eq_pow_val, Units.val_mk0]
  · rw [twoPoint_apply_right hab, Units.val_mk0]
  · intro i hia hib
    rw [twoPoint_apply_of_ne hia hib, Units.val_one]

theorem elem_fix_diag (hK : Nat.card K = 4)
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {a b : Fin r}
    (hab : a ≠ b) (t : K) {k : Fin r} (hkb : k ≠ b) {x : M} (hx : π x = hermD k) :
    elemΓ hSL hab t • x = x := by
  obtain ⟨s, d, hs, hda, hdb, -⟩ := exists_torus_omega hK hSL hω0 hab
  have hsx : s • x = x := torus_fix_diag hK hπact hC hs hx
  have hconj : ∀ t, s * elemΓ hSL hab t = elemΓ hSL hab (ω * t) * s := fun t => by
    rw [torus_mul_elemΓ hSL hs hab, hda, hdb]
    congr 2
    field_simp
  have hmem : ∀ t, elemΓ hSL hab t • x - x ∈ π.ker := fun t => by
    rw [AddMonoidHom.mem_ker, map_sub, hπact, elemΓ_coe, hx, hElem_congr_hermD,
      ite_eq_right hkb, add_zero]
    exact sub_self _
  have hadd : ∀ t u, elemΓ hSL hab (t + u) • x - x =
      (elemΓ hSL hab t • x - x) + (elemΓ hSL hab u • x - x) := by
    intro t u
    obtain ⟨c, hc, e⟩ : ∃ c ∈ π.ker, elemΓ hSL hab u • x = x + c := ⟨_, hmem u, by abel⟩
    rw [← elemΓ_mul, mul_smul, e, smul_add, hC _ c hc]
    abel
  have hω : ∀ t, elemΓ hSL hab (ω * t) • x - x = elemΓ hSL hab t • x - x := by
    intro t
    have h1 : elemΓ hSL hab (ω * t) • x = s • (elemΓ hSL hab t • x) := by
      conv_lhs => rw [← hsx]
      rw [← mul_smul, ← hconj, mul_smul]
    obtain ⟨c, hc, e⟩ : ∃ c ∈ π.ker, elemΓ hSL hab t • x = x + c := ⟨_, hmem t, by abel⟩
    rw [h1, e, smul_add, hsx, hC s c hc]
  have h1 : elemΓ hSL hab 1 • x - x = 0 := by
    have hω1' := hω 1
    have hωω := hω ω
    rw [mul_one] at hω1'
    rw [show ω * ω = ω + 1 by rw [← sq, four_omega_sq hK hω0 hω1], hadd, hω1'] at hωω
    exact add_eq_left.mp hωω
  have hω' : elemΓ hSL hab ω • x - x = 0 := by
    have h := hω 1
    rwa [mul_one, h1] at h
  rw [← sub_eq_zero]
  rcases four_cases hK hω0 hω1 t with rfl | rfl | rfl | rfl
  · rw [elemΓ_zero, one_smul, sub_self]
  · exact h1
  · exact hω'
  · rw [hadd, hω', h1, add_zero]

end Torus

section OffLifts

variable [Module (ZMod 2) M]

omit [CharP K 2] in
theorem smul_zmod_two_comm (g : Γ) (c : ZMod 2) (m : M) : g • (c • m) = c • (g • m) := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, zero_smul, smul_zero]
  · rw [one_smul, one_smul]

omit [CharP K 2] in
theorem zmod_two_smul_hermO [Algebra (ZMod 2) K] (c : ZMod 2) (i j : Fin r) (v : K) :
    c • hermO i j v = hermO i j (algebraMap (ZMod 2) K c * v) := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, map_zero, zero_mul, hermO_zero]
  · rw [one_smul, map_one, one_mul]

omit [CharP K 2] in
theorem map_zmod_two_smul' [Algebra (ZMod 2) K] (c : ZMod 2) (m : M) :
    π (c • m) = c • π m := by
  rcases zmod_two_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, map_zero, zero_smul]
  · rw [one_smul, one_smul]

omit [CharP K 2] in
theorem torus_comm {s h : Γ} {d e : Fin r → Kˣ} (hs : (s : GL (Fin r) K) = hTorusGL d)
    (hh : (h : GL (Fin r) K) = hTorusGL e) : h * s = s * h :=
  Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hs, hh, hTorusGL_comm])

omit [Module (ZMod 2) M] in
theorem eq_zero_of_omega_invariant {ω : K} (hω1 : ω ≠ 1) (F : K →+ M) (hF2 : ∀ u, F u + F u = 0)
    (hFω : ∀ u, F (ω * u) = F u) (v : K) : F v = 0 := by
  have hne : ω + 1 ≠ 0 := fun h => hω1 (by
    have h' := eq_neg_of_add_eq_zero_left h
    rwa [four_neg] at h')
  have h : ∀ u, F ((ω + 1) * u) = 0 := fun u => by rw [add_mul, one_mul, map_add, hFω, hF2]
  rw [← mul_inv_cancel_left₀ hne v]
  exact h _

theorem exists_hermO_lift (hK : Nat.card K = 4) [Algebra (ZMod 2) K]
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B) {i j : Fin r}
    (hij : i ≠ j) :
    ∃ o : K →+ M, (∀ u, π (o u) = hermO i j u) ∧ ∀ (h : Γ) (e : Fin r → Kˣ),
      (h : GL (Fin r) K) = hTorusGL e → ∀ u, h • o u = o ((e i : K) * (e j : K) ^ 2 * u) := by
  obtain ⟨s, d, hs, hdi, hdj, -⟩ := exists_torus_omega hK hSL hω0 hij
  have hχ : (d i : K) * (d j : K) ^ 2 = ω := by
    rw [hdi, hdj, ← pow_add]
    exact four_pow_four hK ω
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  obtain ⟨x, hx⟩ := hsurj (hermO i j 1) (hconj_hermO hK i j 1)
  have hsπ : ∀ {z : M} {v : K}, π z = hermO i j v → π (s • z) = hermO i j (ω * v) :=
    fun hz => by rw [torus_act_hermO hK hπact hs hz, hχ]
  obtain ⟨y, hy⟩ : ∃ y, y = s • x + s • s • x := ⟨_, rfl⟩
  have hyπ : π y = hermO i j 1 := by
    rw [hy, map_add, hsπ hx, hsπ (hsπ hx), ← hermO_add]
    congr 1
    rw [mul_one, ← sq, four_omega_sq hK hω0 hω1]
    linear_combination four_add_self ω
  have hs3 : ∀ z : M, s • s • s • z = z := fun z => by
    rw [← mul_smul, ← mul_smul, ← pow_three', torus_pow_three hK hs, one_smul]
  have hy3 : s • s • y = y + s • y := by
    rw [hy, smul_add, smul_add, hs3]
    linear_combination (norm := abel) (-1 : ℤ) • h2 (s • s • x)
  have hsy : π (s • y) = hermO i j ω := by rw [hsπ hyπ, mul_one]
  let tr := Algebra.trace (ZMod 2) K
  let o : K →+ M :=
    { toFun := fun u => tr (ω ^ 2 * u) • y + tr u • (s • y)
      map_zero' := by simp
      map_add' := fun u v => by
        simp only [mul_add, map_add, add_smul]
        abel }
  have ho : ∀ u, o u = tr (ω ^ 2 * u) • y + tr u • (s • y) := fun _ => rfl
  have hoπ : ∀ u, π (o u) = hermO i j u := fun u => by
    rw [ho, map_add, map_zmod_two_smul', map_zmod_two_smul', hyπ, hsy, zmod_two_smul_hermO,
      zmod_two_smul_hermO, ← hermO_add, mul_one]
    exact congrArg _ (four_coord hK hω0 hω1 u).symm
  have hoω : ∀ u, s • o u = o (ω * u) := fun u => by
    have htr : tr (ω ^ 2 * u) + tr u = tr (ω * u) := by
      rw [← map_add]
      congr 1
      linear_combination u * four_omega_sq hK hω0 hω1 + u * four_add_self (1 : K)
    rw [ho, ho, smul_add, smul_zmod_two_comm, smul_zmod_two_comm, hy3,
      show ω ^ 2 * (ω * u) = ω ^ 3 * u by ring, four_pow_three hK hω0, one_mul, ← htr,
      smul_add, add_smul]
    abel
  refine ⟨o, hoπ, fun h e hh u => ?_⟩
  set χ := (e i : K) * (e j : K) ^ 2 with hχe
  let F : K →+ M :=
    { toFun := fun u => h • o u - o (χ * u)
      map_zero' := by simp
      map_add' := fun u v => by
        rw [map_add, smul_add, mul_add, map_add]
        abel }
  have hFker : ∀ u, F u ∈ π.ker := fun u => by
    change h • o u - o (χ * u) ∈ π.ker
    rw [AddMonoidHom.mem_ker, map_sub, torus_act_hermO hK hπact hh (hoπ u), hoπ]
    exact sub_self _
  have hFω : ∀ u, F (ω * u) = F u := fun u => by
    change h • o (ω * u) - o (χ * (ω * u)) = h • o u - o (χ * u)
    rw [← hoω, show χ * (ω * u) = ω * (χ * u) by ring, ← hoω, ← mul_smul,
      torus_comm hs hh, mul_smul, ← smul_sub]
    exact hC s _ (hFker u)
  have h0 := eq_zero_of_omega_invariant hω1 F (fun u => h2 _) hFω u
  exact sub_eq_zero.mp h0

theorem hermO_lift_unique (hK : Nat.card K = 4)
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {i j : Fin r}
    (hij : i ≠ j) {o o' : K →+ M} (ho : ∀ u, π (o u) = hermO i j u)
    (ho' : ∀ u, π (o' u) = hermO i j u)
    (heq : ∀ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e →
      ∀ u, h • o u = o ((e i : K) * (e j : K) ^ 2 * u))
    (heq' : ∀ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e →
      ∀ u, h • o' u = o' ((e i : K) * (e j : K) ^ 2 * u)) : o = o' := by
  obtain ⟨s, d, hs, hdi, hdj, -⟩ := exists_torus_omega hK hSL hω0 hij
  have hχ : (d i : K) * (d j : K) ^ 2 = ω := by
    rw [hdi, hdj, ← pow_add]
    exact four_pow_four hK ω
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hker : ∀ u, (o - o') u ∈ π.ker := fun u => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, map_sub, ho, ho']
    exact sub_self _
  have hω : ∀ u, (o - o') (ω * u) = (o - o') u := fun u => by
    rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply, ← hχ, ← heq s d hs, ← heq' s d hs,
      ← smul_sub]
    exact hC s _ (hker u)
  ext u
  exact sub_eq_zero.mp (eq_zero_of_omega_invariant hω1 (o - o') (fun u => h2 _) hω u)

theorem exists_hermO_lifts (hK : Nat.card K = 4) [Algebra (ZMod 2) K]
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    (hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B) :
    ∃ o : Fin r → Fin r → K →+ M, (∀ i j, i ≠ j → ∀ u, π (o i j u) = hermO i j u) ∧
      (∀ i j, i ≠ j → ∀ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e →
        ∀ u, h • o i j u = o i j ((e i : K) * (e j : K) ^ 2 * u)) ∧
      (∀ i j u, o j i u = o i j (u ^ 2)) ∧ ∀ i, o i i = 0 := by
  classical
  choose o₀ ho₀π ho₀eq using fun i j (h : i ≠ j) =>
    exists_hermO_lift hK hSL hπact hC hω0 hω1 hsurj h
  let o : Fin r → Fin r → K →+ M := fun i j => if h : i = j then 0 else o₀ i j h
  have ho : ∀ i j (h : i ≠ j), o i j = o₀ i j h := fun i j h => dite_eq_right h
  have hfrob : ∀ u v : K, (u + v) ^ 2 = u ^ 2 + v ^ 2 := four_sq_add
  refine ⟨o, fun i j h u => by rw [ho i j h]; exact ho₀π i j h u,
    fun i j h g e hg u => by rw [ho i j h]; exact ho₀eq i j h g e hg u, fun i j u => ?_,
    fun i => dite_eq_left rfl⟩
  by_cases hij : i = j
  · subst hij
    rw [show o i i = 0 from dite_eq_left rfl, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
  let o' : K →+ M :=
    { toFun := fun u => o₀ i j hij (u ^ 2)
      map_zero' := by simp
      map_add' := fun u v => by rw [hfrob, map_add] }
  have h := hermO_lift_unique hK hSL hC hω0 hω1 (Ne.symm hij) (o := o₀ j i (Ne.symm hij))
    (o' := o') (ho₀π j i (Ne.symm hij))
    (fun u => (ho₀π i j hij (u ^ 2)).trans (hermO_swap hK i j u).symm)
    (ho₀eq j i (Ne.symm hij))
    (fun g e hg u => by
      change g • o₀ i j hij (u ^ 2) = o₀ i j hij (((e j : K) * (e i : K) ^ 2 * u) ^ 2)
      rw [ho₀eq i j hij g e hg]
      congr 1
      rw [mul_pow, mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, four_pow_four hK]
      ring)
  rw [ho j i (Ne.symm hij), ho i j hij]
  exact DFunLike.congr_fun h u

end OffLifts

section ElemOff

variable [Module (ZMod 2) M]

omit [Module (ZMod 2) M] in
theorem eq_of_commuting_torus (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c)
    (h2 : ∀ m : M, m + m = 0) {g h : Γ} (hgh : h * g = g * h) {o R : K →+ M} {χ : K}
    (hχ : χ ≠ 1) (hker : ∀ u, g • o u - R u ∈ π.ker) (ho : ∀ u, h • o u = o (χ * u))
    (hR : ∀ u, h • R u = R (χ * u)) (u : K) : g • o u = R u := by
  let F : K →+ M :=
    { toFun := fun u => g • o u - R u
      map_zero' := by simp
      map_add' := fun u v => by
        rw [map_add, smul_add, map_add]
        abel }
  have hF : ∀ u, F (χ * u) = F u := fun u => by
    change g • o (χ * u) - R (χ * u) = g • o u - R u
    rw [← ho, ← hR, ← mul_smul, ← hgh, mul_smul, ← smul_sub]
    exact hC h _ (hker u)
  exact sub_eq_zero.mp (eq_zero_of_omega_invariant hχ F (fun _ => h2 _) hF u)

omit [CharP K 2] [Module (ZMod 2) M] in
theorem torus_comm_elemΓ
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ) {h : Γ}
    {e : Fin r → Kˣ} (hh : (h : GL (Fin r) K) = hTorusGL e) {a b : Fin r} (hab : a ≠ b)
    (heab : e a = e b) (t : K) : h * elemΓ hSL hab t = elemΓ hSL hab t * h := by
  rw [torus_mul_elemΓ hSL hh hab, heab, mul_comm _ t, mul_assoc,
    mul_inv_cancel₀ (e b).ne_zero, mul_one]

omit [CharP K 2] in
theorem chi_ne_one (hK : Nat.card K = 4) {e : Fin r → Kˣ} {i j : Fin r} (h : e i ≠ e j) :
    (e i : K) * (e j : K) ^ 2 ≠ 1 := by
  intro h1
  apply h
  apply Units.ext
  have h3 := four_pow_three hK (e j).ne_zero
  calc (e i : K) = (e i : K) * (e j : K) ^ 2 * (e j : K) := by
        rw [mul_assoc, ← pow_succ, h3, mul_one]
    _ = (e j : K) := by rw [h1, one_mul]

theorem elem_act_hermO (hK : Nat.card K = 4)
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c)
    (hsep : ∀ a b i j : Fin r, a ≠ b → i ≠ j → ¬(i = a ∧ j = b) → ¬(i = b ∧ j = a) →
      ∃ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e ∧ e a = e b ∧ e i ≠ e j)
    {o : Fin r → Fin r → K →+ M} (hoπ : ∀ i j, i ≠ j → ∀ u, π (o i j u) = hermO i j u)
    (hoeq : ∀ i j, i ≠ j → ∀ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e →
      ∀ u, h • o i j u = o i j ((e i : K) * (e j : K) ^ 2 * u))
    {a b : Fin r} (hab : a ≠ b) (t : K) {i j : Fin r} (hij : i ≠ j) (h₁ : ¬(i = a ∧ j = b))
    (h₂ : ¬(i = b ∧ j = a)) (u : K) :
    elemΓ hSL hab t • o i j u = o i j u + (if i = b then o a j (t * u) else 0) +
      (if j = b then o i a (u * t ^ 2) else 0) := by
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  obtain ⟨h, e, hh, heab, heij⟩ := hsep a b i j hab hij h₁ h₂
  have hgh := torus_comm_elemΓ hSL hh hab heab t
  have hχ := chi_ne_one hK heij
  have hπg : ∀ u, π (elemΓ hSL hab t • o i j u) = hermO i j u +
      (if i = b then hermO a j (t * u) else 0) + (if j = b then hermO i a (u * t ^ 2) else 0) :=
    fun u => by rw [hπact, elemΓ_coe, hoπ i j hij, hElem_congr_hermO hK a b t u hij]
  by_cases hib : i = b
  · subst hib
    have hja : j ≠ a := fun h' => h₂ ⟨rfl, h'⟩
    let R : K →+ M := o i j + (o a j).comp (AddMonoidHom.mulLeft t)
    have := eq_of_commuting_torus hC h2 hgh hχ (R := R) (fun u => by
        rw [AddMonoidHom.mem_ker, map_sub, hπg, ite_eq_left rfl, ite_eq_right hij.symm,
          add_zero]
        change _ - π (o i j u + o a j (t * u)) = 0
        rw [map_add, hoπ i j hij, hoπ a j (Ne.symm hja)]
        exact sub_self _)
      (hoeq i j hij h e hh) (fun u => by
        change h • (o i j u + o a j (t * u)) = o i j _ + o a j (t * _)
        rw [smul_add, hoeq i j hij h e hh, hoeq a j (Ne.symm hja) h e hh, heab]
        congr 2
        ring) u
    rw [this, ite_eq_left rfl, ite_eq_right hij.symm, add_zero]
    rfl
  · by_cases hjb : j = b
    · subst hjb
      have hia : i ≠ a := fun h' => h₁ ⟨h', rfl⟩
      let R : K →+ M := o i j + (o i a).comp (AddMonoidHom.mulRight (t ^ 2))
      have := eq_of_commuting_torus hC h2 hgh hχ (R := R) (fun u => by
          rw [AddMonoidHom.mem_ker, map_sub, hπg, ite_eq_right hib, ite_eq_left rfl, add_zero]
          change _ - π (o i j u + o i a (u * t ^ 2)) = 0
          rw [map_add, hoπ i j hij, hoπ i a hia]
          exact sub_self _)
        (hoeq i j hij h e hh) (fun u => by
          change h • (o i j u + o i a (u * t ^ 2)) = o i j _ + o i a (_ * t ^ 2)
          rw [smul_add, hoeq i j hij h e hh, hoeq i a hia h e hh, heab]
          congr 2
          ring) u
      rw [this, ite_eq_right hib, ite_eq_left rfl, add_zero]
      rfl
    · have := eq_of_commuting_torus hC h2 hgh hχ (R := o i j) (fun u => by
          rw [AddMonoidHom.mem_ker, map_sub, hπg, ite_eq_right hib, ite_eq_right hjb, add_zero,
            add_zero, hoπ i j hij]
          exact sub_self _) (hoeq i j hij h e hh) (hoeq i j hij h e hh) u
      rw [this, ite_eq_right hib, ite_eq_right hjb, add_zero, add_zero]

end ElemOff

section EqualPair

variable [Module (ZMod 2) M]

theorem additive_ext_one_omega (hK : Nat.card K = 4) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {N : Type*} [AddCommGroup N] (f g : K →+ N) (h1 : f 1 = g 1) (hω : f ω = g ω) (t : K) :
    f t = g t := by
  rcases four_cases hK hω0 hω1 t with rfl | rfl | rfl | rfl
  · rw [map_zero, map_zero]
  · exact h1
  · exact hω
  · rw [map_add, map_add, h1, hω]

theorem diag_mult_fix (hK : Nat.card K = 4)
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)
    {x y : Fin r} (hxy : x ≠ y) (t : K) {a : Fin r} (hay : a ≠ y) {c : K} (hc : c = 0 ∨ c = 1)
    {z : M} (hz : π z = single a a c) : elemΓ hSL hxy t • z = z := by
  rcases hc with rfl | rfl
  · exact hC _ z (by rw [AddMonoidHom.mem_ker, hz, single_zero])
  · exact elem_fix_diag hK hSL hπact hC hω0 hω1 hxy t hay hz

omit [CharP K 2] in
theorem trace_val_eq_zero_or_one [Algebra (ZMod 2) K] (hK : Nat.card K = 4) (v : K) :
    v + v ^ 2 = 0 ∨ v + v ^ 2 = 1 := by
  rw [← four_algebraMap_trace hK]
  rcases zmod_two_eq_zero_or_one (Algebra.trace (ZMod 2) K v) with h | h
  · left
    rw [h, map_zero]
  · right
    rw [h, map_one]

end EqualPair

structure HermCtx (K : Type*) [Field K] [CharP K 2] (r : ℕ) (Γ : Subgroup (GL (Fin r) K))
    (M : Type*) [AddCommGroup M] [DistribMulAction Γ M] (π : M →+ Matrix (Fin r) (Fin r) K) where
  hK : Nat.card K = 4
  hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ
  hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
    π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)
  hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c
  ω : K
  hω0 : ω ≠ 0
  hω1 : ω ≠ 1
  hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B
  hsep : ∀ a b i j : Fin r, a ≠ b → i ≠ j → ¬(i = a ∧ j = b) → ¬(i = b ∧ j = a) →
    ∃ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e ∧ e a = e b ∧ e i ≠ e j
  o : Fin r → Fin r → K →+ M
  hoπ : ∀ i j, i ≠ j → ∀ u, π (o i j u) = hermO i j u
  hoeq : ∀ i j, i ≠ j → ∀ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e →
    ∀ u, h • o i j u = o i j ((e i : K) * (e j : K) ^ 2 * u)
  hosw : ∀ i j u, o j i u = o i j (u ^ 2)
  hod : ∀ i, o i i = 0

section Delta

variable [Module (ZMod 2) M] (X : HermCtx K r Γ M π)

@[expose] def hdelta {a b : Fin r} (hab : a ≠ b) (t u : K) : M :=
  elemΓ X.hSL hab t • X.o a b u - X.o a b u

omit [Module (ZMod 2) M] in
theorem hdelta_π {a b : Fin r} (hab : a ≠ b) (t u : K) :
    π (hdelta X hab t u) = single a a (u * t ^ 2 + (u * t ^ 2) ^ 2) := by
  rw [hdelta, map_sub, X.hπact, elemΓ_coe, X.hoπ a b hab, hElem_congr_hermO X.hK a b t u hab,
    ite_eq_right hab, ite_eq_left rfl, add_zero, add_sub_cancel_left, hermO, single_add]

theorem hdelta_fix [Algebra (ZMod 2) K] {a b : Fin r} (hab : a ≠ b) (t u : K) {x y : Fin r}
    (hxy : x ≠ y) (t' : K) (hay : a ≠ y) :
    elemΓ X.hSL hxy t' • hdelta X hab t u = hdelta X hab t u :=
  diag_mult_fix X.hK X.hSL X.hπact X.hC X.hω0 X.hω1 hxy t' hay
    (trace_val_eq_zero_or_one X.hK _) (hdelta_π X hab t u)

omit [Module (ZMod 2) M] in
theorem hdelta_add_right {a b : Fin r} (hab : a ≠ b) (t u u' : K) :
    hdelta X hab t (u + u') = hdelta X hab t u + hdelta X hab t u' := by
  simp only [hdelta, map_add, smul_add]
  abel

theorem hdelta_add_left [Algebra (ZMod 2) K] {a b : Fin r} (hab : a ≠ b) (t t' u : K) :
    hdelta X hab (t + t') u = hdelta X hab t u + hdelta X hab t' u := by
  have h := hdelta_fix X hab t' u hab t hab
  simp only [hdelta] at h ⊢
  rw [← elemΓ_mul, mul_smul]
  rw [smul_sub] at h
  linear_combination (norm := abel) h

theorem hdelta_self [Algebra (ZMod 2) K] {a b : Fin r} (hab : a ≠ b) (t : K) :
    hdelta X hab t t = 0 := by
  by_cases ht : t = 0
  · subst ht
    rw [hdelta, elemΓ_zero, one_smul, sub_self]
  obtain ⟨da, hda⟩ := X.hsurj (hermD a) (hconj_hermD a)
  obtain ⟨db, hdb⟩ := X.hsurj (hermD b) (hconj_hermD b)
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  obtain ⟨c, hc, e⟩ : ∃ c ∈ π.ker, elemΓ X.hSL hab t • db = db + da + X.o a b t + c :=
    ⟨elemΓ X.hSL hab t • db - db - da - X.o a b t, by
      rw [AddMonoidHom.mem_ker, map_sub, map_sub, map_sub, X.hπact, elemΓ_coe, hdb, hda,
        X.hoπ a b hab, hElem_congr_hermD, ite_eq_left rfl, four_pow_three X.hK ht]
      change hermD b + (hermO a b t + hermD a) - hermD b - hermD a - hermO a b t = 0
      abel, by abel⟩
  have hfa := elem_fix_diag X.hK X.hSL X.hπact X.hC X.hω0 X.hω1 hab t hab hda
  have htt : elemΓ X.hSL hab t • elemΓ X.hSL hab t • db = db := by
    rw [← mul_smul, elemΓ_mul, four_add_self, elemΓ_zero, one_smul]
  have hd : elemΓ X.hSL hab t • X.o a b t = X.o a b t + hdelta X hab t t := by
    rw [hdelta]
    abel
  rw [e, smul_add, smul_add, smul_add, e, hfa, hd, X.hC _ c hc] at htt
  linear_combination (norm := abel) htt - h2 da - h2 c - h2 (X.o a b t)

theorem hdelta_formula [Algebra (ZMod 2) K] {a b : Fin r} (hab : a ≠ b) (t u : K) :
    hdelta X hab t u = Algebra.trace (ZMod 2) K (t * u ^ 2) • hdelta X hab 1 X.ω := by
  set D' := hdelta X hab 1 X.ω with hD'
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have htr1 := four_trace_one X.hK (K := K)
  have htrω := four_trace_omega X.hK X.hω0 X.hω1
  have htrω2 := four_trace_omega_sq X.hK X.hω0 X.hω1
  have hω1 : hdelta X hab X.ω 1 = D' := by
    have h := hdelta_self X hab (1 + X.ω)
    rw [hdelta_add_left, hdelta_add_right, hdelta_add_right, hdelta_self, hdelta_self] at h
    linear_combination (norm := abel) h - h2 D'
  let F : K → K →+ M := fun u =>
    { toFun := fun t => hdelta X hab t u
      map_zero' := by rw [hdelta, elemΓ_zero, one_smul, sub_self]
      map_add' := fun t t' => hdelta_add_left X hab t t' u }
  let G : K → K →+ M := fun u =>
    { toFun := fun t => Algebra.trace (ZMod 2) K (t * u ^ 2) • D'
      map_zero' := by rw [zero_mul, map_zero, zero_smul]
      map_add' := fun t t' => by rw [add_mul, map_add, add_smul] }
  let A : K → K →+ M := fun t =>
    { toFun := fun u => hdelta X hab t u
      map_zero' := by rw [hdelta, map_zero, smul_zero, sub_zero]
      map_add' := fun u u' => hdelta_add_right X hab t u u' }
  let B : K → K →+ M := fun t =>
    { toFun := fun u => Algebra.trace (ZMod 2) K (t * u ^ 2) • D'
      map_zero' := by rw [zero_pow two_ne_zero, mul_zero, map_zero, zero_smul]
      map_add' := fun u u' => by rw [four_sq_add, mul_add, map_add, add_smul] }
  have hA1 : ∀ u, A 1 u = B 1 u := additive_ext_one_omega X.hK X.hω0 X.hω1 (A 1) (B 1)
    (by
      change hdelta X hab 1 1 = Algebra.trace (ZMod 2) K (1 * 1 ^ 2) • D'
      rw [hdelta_self, one_pow, one_mul, htr1, zero_smul])
    (by
      change hdelta X hab 1 X.ω = Algebra.trace (ZMod 2) K (1 * X.ω ^ 2) • D'
      rw [one_mul, htrω2, one_smul])
  have hAω : ∀ u, A X.ω u = B X.ω u := additive_ext_one_omega X.hK X.hω0 X.hω1 (A X.ω) (B X.ω)
    (by
      change hdelta X hab X.ω 1 = Algebra.trace (ZMod 2) K (X.ω * 1 ^ 2) • D'
      rw [hω1, one_pow, mul_one, htrω, one_smul])
    (by
      change hdelta X hab X.ω X.ω = Algebra.trace (ZMod 2) K (X.ω * X.ω ^ 2) • D'
      rw [hdelta_self, ← pow_succ', four_pow_three X.hK X.hω0, htr1, zero_smul])
  exact additive_ext_one_omega X.hK X.hω0 X.hω1 (F u) (G u) (hA1 u) (hAω u) t

theorem elem_act_o [Algebra (ZMod 2) K] {a b : Fin r} (hab : a ≠ b) (t : K) {i j : Fin r}
    (hij : i ≠ j) (h₁ : ¬(i = a ∧ j = b)) (h₂ : ¬(i = b ∧ j = a)) (u : K) :
    elemΓ X.hSL hab t • X.o i j u = X.o i j u + (if i = b then X.o a j (t * u) else 0) +
      (if j = b then X.o i a (u * t ^ 2) else 0) :=
  elem_act_hermO X.hK X.hSL X.hπact X.hC X.hsep X.hoπ X.hoeq hab t hij h₁ h₂ u

theorem hdelta_indep [Algebra (ZMod 2) K] {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : hdelta X hac 1 X.ω = hdelta X hab 1 X.ω := by
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hcomm : elemΓ X.hSL hac (1 : K) = elemΓ X.hSL hab 1 * elemΓ X.hSL hbc 1 *
      elemΓ X.hSL hab 1 * elemΓ X.hSL hbc 1 := by
    have h := commutatorElement_elemΓ X.hSL hab hbc hac (1 : K) 1
    rw [mul_one] at h
    rw [← h, commutatorElement_def, elemΓ_inv, elemΓ_inv]
  have e₁ : elemΓ X.hSL hbc 1 • X.o a c X.ω = X.o a c X.ω + X.o a b X.ω := by
    rw [elem_act_o X hbc 1 hac (fun h => hab h.1) (fun h => hac h.1), ite_eq_right hac,
      ite_eq_left rfl, add_zero, one_pow, mul_one]
  have e₂ : elemΓ X.hSL hab 1 • X.o a c X.ω = X.o a c X.ω := by
    rw [elem_act_o X hab 1 hac (fun h => hbc (h.2 ▸ rfl)) (fun h => hab h.1),
      ite_eq_right hab, ite_eq_right (Ne.symm hbc), add_zero, add_zero]
  have e₃ : elemΓ X.hSL hab 1 • X.o a b X.ω = X.o a b X.ω + hdelta X hab 1 X.ω := by
    rw [hdelta]
    abel
  have e₄ : elemΓ X.hSL hbc 1 • X.o a b X.ω = X.o a b X.ω := by
    rw [elem_act_o X hbc 1 hab (fun h => hab h.1) (fun h => hac h.1), ite_eq_right hac,
      ite_eq_right hbc, add_zero, add_zero]
  have f₁ := hdelta_fix X hab 1 X.ω hbc 1 hac
  have f₂ := hdelta_fix X hab 1 X.ω hab 1 hab
  have h : elemΓ X.hSL hac 1 • X.o a c X.ω = X.o a c X.ω + hdelta X hab 1 X.ω := by
    rw [hcomm, mul_smul, mul_smul, mul_smul]
    simp only [smul_add, e₁, e₂, e₃, e₄, f₁, f₂]
    linear_combination (norm := abel) h2 (X.o a b X.ω) + h2 (hdelta X hab 1 X.ω)
  rw [hdelta, h]
  abel

theorem exists_hermD_lifts [Algebra (ZMod 2) K] (hr : 2 ≤ r) :
    ∃ d : Fin r → M, (∀ k, π (d k) = hermD k) ∧
      (∀ a b (hab : a ≠ b), hdelta X hab 1 X.ω = d a) ∧
      ∀ a b (hab : a ≠ b) (t : K), t ≠ 0 →
        elemΓ X.hSL hab t • d b = d b + d a + X.o a b t := by
  classical
  have h2 : ∀ m : M, m + m = 0 := fun m => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hex : ∀ a : Fin r, ∃ b, b ≠ a := fun a => by
    by_contra! h
    have : (Finset.univ : Finset (Fin r)) ⊆ {a} := fun z _ => by simp [h z]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at this
    omega
  choose β hβ using hex
  set d : Fin r → M := fun a => hdelta X (hβ a).symm 1 X.ω with hd
  have hdπ : ∀ k, π (d k) = hermD k := fun k => by
    rw [hd, hdelta_π, one_pow, mul_one, four_omega_sq X.hK X.hω0 X.hω1, ← add_assoc,
      four_add_self, zero_add]
    rfl
  have hδ : ∀ a b (hab : a ≠ b), hdelta X hab 1 X.ω = d a := fun a b hab => by
    by_cases hb : b = β a
    · subst hb
      rfl
    · exact hdelta_indep X (hβ a).symm (Ne.symm hb) hab
  refine ⟨d, hdπ, hδ, fun a b hab t ht => ?_⟩
  have hmem : ∀ t : K, t ≠ 0 →
      elemΓ X.hSL hab t • d b - d b - d a - X.o a b t ∈ π.ker := fun t ht => by
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, map_sub, X.hπact, elemΓ_coe, hdπ, hdπ,
      X.hoπ a b hab, hElem_congr_hermD, ite_eq_left rfl, four_pow_three X.hK ht]
    change hermD b + (hermO a b t + hermD a) - hermD b - hermD a - hermO a b t = 0
    abel
  obtain ⟨s, e, hs, hea, heb, -⟩ := exists_torus_omega X.hK X.hSL X.hω0 hab
  have hχ : (e a : K) * (e b : K) ^ 2 = X.ω := by
    rw [hea, heb, ← pow_add]
    exact four_pow_four X.hK X.ω
  have hsd : ∀ k, s • d k = d k := fun k => torus_fix_diag X.hK X.hπact X.hC hs (hdπ k)
  have hconj : ∀ t, s * elemΓ X.hSL hab t = elemΓ X.hSL hab (X.ω * t) * s := fun t => by
    rw [torus_mul_elemΓ X.hSL hs hab, hea, heb]
    congr 2
    have := X.hω0
    field_simp
  have hcω : ∀ t : K, t ≠ 0 →
      elemΓ X.hSL hab (X.ω * t) • d b - d b - d a - X.o a b (X.ω * t) =
        elemΓ X.hSL hab t • d b - d b - d a - X.o a b t := fun t ht => by
    have h1 : elemΓ X.hSL hab (X.ω * t) • d b = s • (elemΓ X.hSL hab t • d b) := by
      conv_lhs => rw [← hsd b]
      rw [← mul_smul, ← hconj, mul_smul]
    obtain ⟨c, hc, ec⟩ : ∃ c ∈ π.ker, elemΓ X.hSL hab t • d b = d b + d a + X.o a b t + c :=
      ⟨_, hmem t ht, by abel⟩
    rw [h1, ec, smul_add, smul_add, smul_add, hsd, hsd, X.hoeq a b hab s e hs, hχ, X.hC s c hc]
    abel
  have hcadd : elemΓ X.hSL hab (1 + X.ω) • d b - d b - d a - X.o a b (1 + X.ω) =
      (elemΓ X.hSL hab 1 • d b - d b - d a - X.o a b 1) +
        (elemΓ X.hSL hab X.ω • d b - d b - d a - X.o a b X.ω) := by
    obtain ⟨c, hc, ec⟩ : ∃ c ∈ π.ker, elemΓ X.hSL hab X.ω • d b =
        d b + d a + X.o a b X.ω + c := ⟨_, hmem X.ω X.hω0, by abel⟩
    have hfa := elem_fix_diag X.hK X.hSL X.hπact X.hC X.hω0 X.hω1 hab 1 hab (hdπ a)
    have ho : elemΓ X.hSL hab 1 • X.o a b X.ω = X.o a b X.ω + d a := by
      rw [← hδ a b hab, hdelta]
      abel
    rw [← elemΓ_mul, mul_smul, ec, smul_add, smul_add, smul_add, hfa, ho, X.hC _ c hc, map_add]
    linear_combination (norm := abel) h2 (d a)
  have hc1 : elemΓ X.hSL hab 1 • d b - d b - d a - X.o a b 1 = 0 := by
    have hω := hcω 1 one_ne_zero
    rw [mul_one] at hω
    have hωω := hcω X.ω X.hω0
    rw [show X.ω * X.ω = 1 + X.ω by rw [← sq, four_omega_sq X.hK X.hω0 X.hω1, add_comm],
      hcadd, hω] at hωω
    exact add_eq_left.mp hωω
  have hcω' : elemΓ X.hSL hab X.ω • d b - d b - d a - X.o a b X.ω = 0 := by
    have hω := hcω 1 one_ne_zero
    rwa [mul_one, hc1] at hω
  have hct : elemΓ X.hSL hab t • d b - d b - d a - X.o a b t = 0 := by
    rcases four_cases X.hK X.hω0 X.hω1 t with rfl | rfl | rfl | rfl
    · exact absurd rfl ht
    · exact hc1
    · exact hcω'
    · rw [add_comm, hcadd, hc1, hcω', add_zero]
  rw [← sub_eq_zero, ← hct]
  abel

end Delta

section Exponent

theorem two_nsmul_eq_zero (hK : Nat.card K = 4)
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) (hC2 : ∀ c ∈ π.ker, 2 • c = 0)
    (hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B)
    (hπV : ∀ m, hconj (π m) = π m) (hr : 2 ≤ r) (m : M) : 2 • m = 0 := by
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  have hπ2 : ∀ x : M, 2 • x ∈ π.ker := fun x => by
    rw [AddMonoidHom.mem_ker, map_nsmul, two_nsmul]
    ext i j
    exact four_add_self _
  have hs2 : ∀ (g : Γ) (x : M), 2 • (g • x) = 2 • x := fun g x => by
    rw [two_nsmul, ← smul_add, ← two_nsmul]
    exact hC g _ (hπ2 x)
  have hoff : ∀ i j, i ≠ j → ∀ (u : K) (x : M), π x = hermO i j u → 2 • x = 0 := by
    intro i j hij u x hx
    obtain ⟨s, d, hs, hdi, hdj, -⟩ := exists_torus_omega hK hSL hω0 hij
    have hχ : (d i : K) * (d j : K) ^ 2 = ω := by
      rw [hdi, hdj, ← pow_add]
      exact four_pow_four hK ω
    have h1 : π (s • x) = hermO i j (ω * u) := by rw [torus_act_hermO hK hπact hs hx, hχ]
    have h2 : π (s • s • x) = hermO i j (ω * (ω * u)) := by
      rw [torus_act_hermO hK hπact hs h1, hχ]
    have hc : x + s • x + s • s • x ∈ π.ker := by
      rw [AddMonoidHom.mem_ker, map_add, map_add, hx, h1, h2, ← hermO_add, ← hermO_add]
      convert hermO_zero i j using 2
      linear_combination u * four_omega_sq hK hω0 hω1 +
        (u + ω * u) * (CharTwo.two_eq_zero : (2 : K) = 0)
    have h6 := hC2 _ hc
    simp only [nsmul_add, hs2] at h6
    have h4 := hC2 _ (hπ2 x)
    rw [two_nsmul (2 • x)] at h4
    rw [h4, zero_add] at h6
    exact h6
  have hne : ∀ a : Fin r, ∃ b, a ≠ b := fun a => by
    by_contra! h
    have : (Finset.univ : Finset (Fin r)) ⊆ {a} := fun z _ => by simp [← h z]
    have := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at this
    omega
  have hdiag : ∀ (a : Fin r) (x : M), π x = hermD a → 2 • x = 0 := by
    intro a x hx
    obtain ⟨b, hab⟩ := hne a
    obtain ⟨y, hy⟩ := hsurj (hermD b) (hconj_hermD b)
    have hz : π (elemΓ hSL hab 1 • y - y - x) = hermO a b 1 := by
      rw [map_sub, map_sub, hπact, elemΓ_coe, hy, hx, hElem_congr_hermD, ite_eq_left rfl,
        one_pow]
      change hermD b + (hermO a b 1 + hermD a) - hermD b - hermD a = hermO a b 1
      abel
    have h := hoff a b hab 1 _ hz
    rw [smul_sub, smul_sub, hs2, sub_self, zero_sub, neg_eq_zero] at h
    exact h
  let W : AddSubgroup M :=
    { carrier := {x | 2 • x = 0}
      add_mem' := fun {a b} (ha : 2 • a = 0) (hb : 2 • b = 0) => show 2 • (a + b) = 0 by
        rw [nsmul_add, ha, hb, add_zero]
      zero_mem' := show 2 • (0 : M) = 0 from smul_zero 2
      neg_mem' := fun {a} (ha : 2 • a = 0) => show 2 • (-a) = 0 by rw [smul_neg, ha, neg_zero] }
  have hD : ∀ k, hermD k ∈ W.map π := fun k => by
    obtain ⟨x, hx⟩ := hsurj (hermD k) (hconj_hermD k)
    exact ⟨x, hdiag k x hx, hx⟩
  have hO : ∀ i j, i < j → ∀ u, hermO i j u ∈ W.map π := fun i j hij u => by
    obtain ⟨x, hx⟩ := hsurj (hermO i j u) (hconj_hermO hK i j u)
    exact ⟨x, hoff i j hij.ne u x hx, hx⟩
  obtain ⟨w, hw, hwm⟩ := herm_mem hD hO (hπV m)
  have h := hC2 (m - w) (by rw [AddMonoidHom.mem_ker, map_sub, hwm, sub_self])
  rw [smul_sub, show 2 • w = 0 from hw, sub_zero] at h
  exact h

end Exponent

section Splitting

variable [Module (ZMod 2) M] (X : HermCtx K r Γ M π)

omit [CharP K 2] [Module (ZMod 2) M] in
theorem smul_mem_closure_of_gen {G : Set M} {g : Γ}
    (h : ∀ x ∈ G, g • x ∈ AddSubgroup.closure G) {x : M} (hx : x ∈ AddSubgroup.closure G) :
    g • x ∈ AddSubgroup.closure G := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy => exact h y hy
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

omit [Module (ZMod 2) M] in
@[expose] def hermSpan (d : Fin r → M) : AddSubgroup M :=
  AddSubgroup.closure (Set.range d ∪ Set.range fun p : Fin r × Fin r × K => X.o p.1 p.2.1 p.2.2)

omit [Module (ZMod 2) M] in
theorem d_mem_hermSpan (d : Fin r → M) (k : Fin r) : d k ∈ hermSpan X d :=
  AddSubgroup.subset_closure (Or.inl ⟨k, rfl⟩)

omit [Module (ZMod 2) M] in
theorem o_mem_hermSpan (d : Fin r → M) (i j : Fin r) (u : K) : X.o i j u ∈ hermSpan X d :=
  AddSubgroup.subset_closure (Or.inr ⟨(i, j, u), rfl⟩)

theorem elem_smul_mem_hermSpan [Algebra (ZMod 2) K] {d : Fin r → M}
    (hdπ : ∀ k, π (d k) = hermD k) (hδ : ∀ a b (hab : a ≠ b), hdelta X hab 1 X.ω = d a)
    (hdb : ∀ a b (hab : a ≠ b) (t : K), t ≠ 0 →
      elemΓ X.hSL hab t • d b = d b + d a + X.o a b t)
    {a b : Fin r} (hab : a ≠ b) (t : K) {x : M} (hx : x ∈ hermSpan X d) :
    elemΓ X.hSL hab t • x ∈ hermSpan X d := by
  refine smul_mem_closure_of_gen (fun y hy => ?_) hx
  have hpair : ∀ u, elemΓ X.hSL hab t • X.o a b u ∈ hermSpan X d := fun u => by
    have e : elemΓ X.hSL hab t • X.o a b u =
        X.o a b u + Algebra.trace (ZMod 2) K (t * u ^ 2) • d a := by
      rw [← hδ a b hab, ← hdelta_formula X hab t u, hdelta]
      abel
    rw [e]
    exact add_mem (o_mem_hermSpan X d a b u) (zmod_two_smul_mem _ _ (d_mem_hermSpan X d a))
  rcases hy with ⟨k, rfl⟩ | ⟨⟨i, j, u⟩, rfl⟩
  · by_cases hkb : k = b
    · subst hkb
      by_cases ht : t = 0
      · rw [ht, elemΓ_zero, one_smul]
        exact d_mem_hermSpan X d k
      · rw [hdb a k hab t ht]
        exact add_mem (add_mem (d_mem_hermSpan X d k) (d_mem_hermSpan X d a))
          (o_mem_hermSpan X d a k t)
    · rw [elem_fix_diag X.hK X.hSL X.hπact X.hC X.hω0 X.hω1 hab t hkb (hdπ k)]
      exact d_mem_hermSpan X d k
  · change elemΓ X.hSL hab t • X.o i j u ∈ hermSpan X d
    by_cases hij : i = j
    · subst hij
      rw [X.hod i, AddMonoidHom.zero_apply, smul_zero]
      exact zero_mem _
    by_cases h₁ : i = a ∧ j = b
    · rw [h₁.1, h₁.2]
      exact hpair u
    by_cases h₂ : i = b ∧ j = a
    · rw [h₂.1, h₂.2, X.hosw a b u]
      exact hpair _
    rw [elem_act_o X hab t hij h₁ h₂ u]
    refine add_mem (add_mem (o_mem_hermSpan X d i j u) ?_) ?_
    · split_ifs
      · exact o_mem_hermSpan X d a j _
      · exact zero_mem _
    · split_ifs
      · exact o_mem_hermSpan X d i a _
      · exact zero_mem _

theorem torus_smul_mem_hermSpan {d : Fin r → M} (hdπ : ∀ k, π (d k) = hermD k) {h : Γ}
    {e : Fin r → Kˣ} (hh : (h : GL (Fin r) K) = hTorusGL e) {x : M} (hx : x ∈ hermSpan X d) :
    h • x ∈ hermSpan X d := by
  refine smul_mem_closure_of_gen (fun y hy => ?_) hx
  rcases hy with ⟨k, rfl⟩ | ⟨⟨i, j, u⟩, rfl⟩
  · rw [torus_fix_diag X.hK X.hπact X.hC hh (hdπ k)]
    exact d_mem_hermSpan X d k
  · change h • X.o i j u ∈ hermSpan X d
    by_cases hij : i = j
    · subst hij
      rw [X.hod i, AddMonoidHom.zero_apply, smul_zero]
      exact zero_mem _
    · rw [X.hoeq i j hij h e hh u]
      exact o_mem_hermSpan X d i j _

omit [CharP K 2] in
theorem hTorusGL_inv (e : Fin r → Kˣ) : (hTorusGL e)⁻¹ = hTorusGL e⁻¹ :=
  Units.ext rfl

omit [CharP K 2] [Module (ZMod 2) M] in
theorem closure_elem_torus_eq_top
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hdet : ∀ g : Γ, ∃ (t : Γ) (e : Fin r → Kˣ), (t : GL (Fin r) K) = hTorusGL e ∧
      Matrix.GeneralLinearGroup.det (t : GL (Fin r) K) =
        Matrix.GeneralLinearGroup.det (g : GL (Fin r) K)) :
    Subgroup.closure ({g : Γ | ∃ (a b : Fin r) (h : a ≠ b) (t : K), elemΓ hSL h t = g} ∪
      {g : Γ | ∃ e : Fin r → Kˣ, (g : GL (Fin r) K) = hTorusGL e}) = ⊤ := by
  set T := ({g : Γ | ∃ (a b : Fin r) (h : a ≠ b) (t : K), elemΓ hSL h t = g} ∪
      {g : Γ | ∃ e : Fin r → Kˣ, (g : GL (Fin r) K) = hTorusGL e}) with hT
  let φ : SpecialLinearGroup (Fin r) K →* Γ :=
    SpecialLinearGroup.toGL.codRestrict Γ fun A => hSL _ A.2
  have hφ : ∀ A, φ A ∈ Subgroup.closure T := by
    intro A
    have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet r K) := by
      rw [CFSG.LinearGroups.special_linear_elementary_generation]
      exact Subgroup.mem_top A
    have h := Subgroup.mem_map_of_mem φ hA
    rw [MonoidHom.map_closure] at h
    refine (Subgroup.closure_le _).mpr ?_ h
    rintro _ ⟨B, ⟨i, j, hij, c, rfl⟩, rfl⟩
    exact Subgroup.subset_closure (Or.inl ⟨i, j, hij, c, Subtype.ext (Units.ext rfl)⟩)
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨t, e, ht, hdt⟩ := hdet g
  have h1 : (((g * t⁻¹ : Γ) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_inv, ← hdt, mul_inv_cancel, Units.val_one]
  have hg : g = φ ⟨_, h1⟩ * t := by
    have : φ ⟨_, h1⟩ = g * t⁻¹ := Subtype.ext (Units.ext rfl)
    rw [this, inv_mul_cancel_right]
  rw [hg]
  exact mul_mem (hφ _) (Subgroup.subset_closure (Or.inr ⟨e, ht⟩))

theorem smul_mem_hermSpan [Algebra (ZMod 2) K] {d : Fin r → M}
    (hdπ : ∀ k, π (d k) = hermD k) (hδ : ∀ a b (hab : a ≠ b), hdelta X hab 1 X.ω = d a)
    (hdb : ∀ a b (hab : a ≠ b) (t : K), t ≠ 0 →
      elemΓ X.hSL hab t • d b = d b + d a + X.o a b t)
    (hgen : Subgroup.closure
      ({g : Γ | ∃ (a b : Fin r) (h : a ≠ b) (t : K), elemΓ X.hSL h t = g} ∪
        {g : Γ | ∃ e : Fin r → Kˣ, (g : GL (Fin r) K) = hTorusGL e}) = ⊤)
    (g : Γ) {x : M} (hx : x ∈ hermSpan X d) : g • x ∈ hermSpan X d := by
  refine act_mem_of_closure_eq_top (DistribMulAction.toAddMonoidEnd Γ M) hgen ?_ ?_ g x hx
  · rintro _ (⟨a, b, hab, t, rfl⟩ | ⟨e, he⟩)
    · exact Or.inl ⟨a, b, hab, t, (elemΓ_inv X.hSL hab t).symm⟩
    · exact Or.inr ⟨e⁻¹, by rw [Subgroup.coe_inv, he, hTorusGL_inv]⟩
  · rintro _ (⟨a, b, hab, t, rfl⟩ | ⟨e, he⟩) y hy
    · exact elem_smul_mem_hermSpan X hdπ hδ hdb hab t hy
    · exact torus_smul_mem_hermSpan X hdπ he hy

@[expose] noncomputable def hermSection [Algebra (ZMod 2) K] (d : Fin r → M) :
    Matrix (Fin r) (Fin r) K →+ M where
  toFun B := ∑ k, Algebra.trace (ZMod 2) K (X.ω ^ 2 * B k k) • d k +
    ∑ p ∈ binaryUpperPairs r, X.o p.1 p.2 (B p.1 p.2)
  map_zero' := by simp
  map_add' B B' := by
    simp only [Matrix.add_apply, mul_add, map_add, add_smul, Finset.sum_add_distrib]
    abel

theorem hermSection_apply [Algebra (ZMod 2) K] (d : Fin r → M) (B : Matrix (Fin r) (Fin r) K) :
    hermSection X d B = ∑ k, Algebra.trace (ZMod 2) K (X.ω ^ 2 * B k k) • d k +
      ∑ p ∈ binaryUpperPairs r, X.o p.1 p.2 (B p.1 p.2) :=
  rfl

theorem hermSection_mem [Algebra (ZMod 2) K] (d : Fin r → M) (B : Matrix (Fin r) (Fin r) K) :
    hermSection X d B ∈ hermSpan X d := by
  rw [hermSection_apply]
  exact add_mem (sum_mem fun k _ => zmod_two_smul_mem _ _ (d_mem_hermSpan X d k))
    (sum_mem fun p _ => o_mem_hermSpan X d _ _ _)

theorem hermSection_hermD [Algebra (ZMod 2) K] (d : Fin r → M) (k : Fin r) :
    hermSection X d (hermD k) = d k := by
  rw [hermSection_apply, Finset.sum_eq_single k, hermD_apply,
    ite_eq_left (show k = k ∧ k = k from ⟨rfl, rfl⟩), mul_one,
    four_trace_omega_sq X.hK X.hω0 X.hω1, one_smul]
  · refine add_eq_left.mpr (Finset.sum_eq_zero fun p hp => ?_)
    rw [hermD_apply, ite_eq_right fun h => (Finset.mem_filter.mp hp).2.ne (h.1.symm.trans h.2),
      map_zero]
  · intro l _ hl
    rw [hermD_apply, ite_eq_right fun h => hl h.1.symm, mul_zero, map_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem hermSection_hermO [Algebra (ZMod 2) K] (d : Fin r → M) {i j : Fin r} (hij : i ≠ j)
    (u : K) : hermSection X d (hermO i j u) = X.o i j u := by
  have hdiag : ∀ k, hermO i j u k k = 0 := fun k =>
    hermO_apply_eq_zero u (fun h => hij (h.1.trans h.2.symm)) fun h => hij (h.2.trans h.1.symm)
  rw [hermSection_apply]
  simp only [hdiag, mul_zero, map_zero, zero_smul, Finset.sum_const_zero, zero_add]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [Finset.sum_eq_single (i, j)]
    · change X.o i j (hermO i j u i j) = X.o i j u
      rw [hermO_apply_left hij]
    · intro p hp hne
      have hp' := (Finset.mem_filter.mp hp).2
      have h₁ : ¬(i = p.1 ∧ j = p.2) := fun h' => hne (Prod.ext h'.1.symm h'.2.symm)
      have h₂ : ¬(j = p.1 ∧ i = p.2) := fun h' => lt_asymm h (by rw [h'.1, h'.2]; exact hp')
      rw [hermO_apply_eq_zero u h₁ h₂, map_zero]
    · intro hn
      exact absurd (show (i, j) ∈ binaryUpperPairs r from
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) hn
  · rw [Finset.sum_eq_single (j, i)]
    · change X.o j i (hermO i j u j i) = X.o i j u
      rw [hermO_apply_right hij, X.hosw, ← pow_mul, four_pow_four X.hK]
    · intro p hp hne
      have hp' := (Finset.mem_filter.mp hp).2
      have h₁ : ¬(i = p.1 ∧ j = p.2) := fun h' => lt_asymm h (by rw [h'.1, h'.2]; exact hp')
      have h₂ : ¬(j = p.1 ∧ i = p.2) := fun h' => hne (Prod.ext h'.1.symm h'.2.symm)
      rw [hermO_apply_eq_zero u h₁ h₂, map_zero]
    · intro hn
      exact absurd (show (j, i) ∈ binaryUpperPairs r from
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) hn

theorem π_hermSection [Algebra (ZMod 2) K] {d : Fin r → M} (hdπ : ∀ k, π (d k) = hermD k)
    {B : Matrix (Fin r) (Fin r) K} (hB : hconj B = B) : π (hermSection X d B) = B := by
  rw [hermSection_apply, map_add, map_sum, map_sum]
  conv_rhs => rw [herm_decomp hB]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zmod_two_smul', hdπ]
    rcases herm_diag hB k with h | h <;> rw [h]
    · rw [mul_zero, map_zero, zero_smul, single_zero]
    · rw [mul_one, four_trace_omega_sq X.hK X.hω0 X.hω1, one_smul]
      rfl
  · exact Finset.sum_congr rfl fun p hp => X.hoπ _ _ (Finset.mem_filter.mp hp).2.ne _

theorem hermSection_π [Algebra (ZMod 2) K] {d : Fin r → M} (hdπ : ∀ k, π (d k) = hermD k)
    {x : M} (hx : x ∈ hermSpan X d) : hermSection X d (π x) = x := by
  unfold hermSpan at hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨k, rfl⟩ | ⟨⟨i, j, u⟩, rfl⟩
    · rw [hdπ]
      exact hermSection_hermD X d k
    · change hermSection X d (π (X.o i j u)) = X.o i j u
      by_cases hij : i = j
      · subst hij
        rw [X.hod i, AddMonoidHom.zero_apply, map_zero, map_zero]
      · rw [X.hoπ i j hij]
        exact hermSection_hermO X d hij u
  | zero => rw [map_zero, map_zero]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | neg y _ hy => rw [map_neg, map_neg, hy]

theorem herm_splitting [Algebra (ZMod 2) K] (hr : 2 ≤ r) (hπV : ∀ m, hconj (π m) = π m)
    (hgen : Subgroup.closure
      ({g : Γ | ∃ (a b : Fin r) (h : a ≠ b) (t : K), elemΓ X.hSL h t = g} ∪
        {g : Γ | ∃ e : Fin r → Kˣ, (g : GL (Fin r) K) = hTorusGL e}) = ⊤) :
    ∃ M₀ : AddSubgroup M, (∀ g : Γ, ∀ x ∈ M₀, g • x ∈ M₀) ∧ π.ker ⊓ M₀ = ⊥ ∧
      π.ker ⊔ M₀ = ⊤ ∧ (∀ x ∈ M₀, π x = 0 → x = 0) ∧
      ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ x ∈ M₀, π x = B := by
  obtain ⟨d, hdπ, hδ, hdb⟩ := exists_hermD_lifts X hr
  have hinj : ∀ x ∈ hermSpan X d, π x = 0 → x = 0 := fun x hx h0 => by
    rw [← hermSection_π X hdπ hx, h0, map_zero]
  refine ⟨hermSpan X d, fun g x hx => smul_mem_hermSpan X hdπ hδ hdb hgen g hx, ?_, ?_, hinj,
    fun B hB => ⟨hermSection X d B, hermSection_mem X d B, π_hermSection X hdπ hB⟩⟩
  · rw [eq_bot_iff]
    rintro x ⟨hk, hx⟩
    exact (AddSubgroup.mem_bot).mpr (hinj x hx hk)
  · rw [eq_top_iff]
    intro m _
    refine AddSubgroup.mem_sup.mpr ⟨m - hermSection X d (π m), ?_, hermSection X d (π m),
      hermSection_mem X d _, sub_add_cancel _ _⟩
    rw [AddMonoidHom.mem_ker, map_sub, π_hermSection X hdπ (hπV m), sub_self]

end Splitting

end Core

theorem herm_splitting_of_sep {K : Type*} [Field K] (hK : Nat.card K = 4) {r : ℕ} (hr : 2 ≤ r)
    {Γ : Subgroup (GL (Fin r) K)}
    (hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 → g ∈ Γ)
    (hdet : ∀ g : Γ, ∃ (t : Γ) (e : Fin r → Kˣ), (t : GL (Fin r) K) = hTorusGL e ∧
      Matrix.GeneralLinearGroup.det (t : GL (Fin r) K) =
        Matrix.GeneralLinearGroup.det (g : GL (Fin r) K))
    (hsep : ∀ a b i j : Fin r, a ≠ b → i ≠ j → ¬(i = a ∧ j = b) → ¬(i = b ∧ j = a) →
      ∃ (h : Γ) (e : Fin r → Kˣ), (h : GL (Fin r) K) = hTorusGL e ∧ e a = e b ∧ e i ≠ e j)
    {M : Type*} [AddCommGroup M] [DistribMulAction Γ M] (π : M →+ Matrix (Fin r) (Fin r) K)
    (hπV : ∀ m, hconj (π m) = π m)
    (hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC2 : ∀ c ∈ π.ker, 2 • c = 0) (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) :
    (∀ m : M, 2 • m = 0) ∧ ∃ M₀ : AddSubgroup M, (∀ g : Γ, ∀ x ∈ M₀, g • x ∈ M₀) ∧
      π.ker ⊓ M₀ = ⊥ ∧ π.ker ⊔ M₀ = ⊤ ∧ (∀ x ∈ M₀, π x = 0 → x = 0) ∧
      ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ x ∈ M₀, π x = B := by
  have : CharP K 2 := four_charP hK
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have h2 : ∀ m : M, 2 • m = 0 := two_nsmul_eq_zero hK hSL hπact hC hC2 hsurj hπV hr
  refine ⟨h2, ?_⟩
  let : Module (ZMod 2) M := AddCommGroup.zmodModule h2
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  obtain ⟨o, hoπ, hoeq, hosw, hod⟩ := exists_hermO_lifts hK hSL hπact hC hω0 hω1 hsurj
  let X : HermCtx K r Γ M π :=
    ⟨hK, hSL, hπact, hC, ω, hω0, hω1, hsurj, hsep, o, hoπ, hoeq, hosw, hod⟩
  exact herm_splitting X hr hπV (closure_elem_torus_eq_top hSL hdet)

end MatrixExtension

open Matrix MatrixExtension in
theorem four_element_hermitian_trivial_module_extension_splitting {K : Type*} [Field K]
    (hK : Nat.card K = 4) {r : ℕ} {Γ : Subgroup (GL (Fin r) K)}
    (hΓ : (3 ≤ r ∧ Γ = ⊤) ∨
      (4 ≤ r ∧ Γ = (GeneralLinearGroup.det : GL (Fin r) K →* Kˣ).ker))
    {M : Type*} [AddCommGroup M] (_hfin : Finite M) (_hM : ∀ m : M, ∃ n : ℕ, 2 ^ n • m = 0)
    [DistribMulAction Γ M] (π : M →+ Matrix (Fin r) (Fin r) K)
    (hπV : ∀ m, hconj (π m) = π m)
    (hsurj : ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ m, π m = B)
    (hπact : ∀ (g : Γ) (m : M), π (g • m) = ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *
      π m * hconj ((g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
    (hC2 : ∀ c ∈ π.ker, 2 • c = 0) (hC : ∀ g : Γ, ∀ c ∈ π.ker, g • c = c) :
    (∀ m : M, 2 • m = 0) ∧ ∃ M₀ : AddSubgroup M, (∀ g : Γ, ∀ x ∈ M₀, g • x ∈ M₀) ∧
      π.ker ⊓ M₀ = ⊥ ∧ π.ker ⊔ M₀ = ⊤ ∧ (∀ x ∈ M₀, π x = 0 → x = 0) ∧
      ∀ B : Matrix (Fin r) (Fin r) K, hconj B = B → ∃ x ∈ M₀, π x = B := by
  classical
  obtain ⟨ω, hω0, hω1⟩ := four_exists_omega hK
  rcases hΓ with ⟨hr, rfl⟩ | ⟨hr, rfl⟩
  · refine herm_splitting_of_sep hK (by omega) (fun g _ => Subgroup.mem_top g) (fun g => ?_)
      (fun a b i j _ hij h₁ h₂ => ?_) π hπV hsurj hπact hC2 hC
    · let i₀ : Fin r := ⟨0, by omega⟩
      refine ⟨⟨hTorusGL (Pi.mulSingle i₀ (GeneralLinearGroup.det (g : GL (Fin r) K))),
        Subgroup.mem_top _⟩, _, rfl, Units.ext ?_⟩
      rw [GeneralLinearGroup.val_det_apply, hTorusGL_det, ← Units.coe_prod,
        Finset.prod_pi_mulSingle', ite_eq_left (Finset.mem_univ _)]
    · obtain ⟨e, he₁, he₂⟩ := exists_sep_units hω0 hω1 hij h₁ h₂
      exact ⟨⟨hTorusGL e, Subgroup.mem_top _⟩, e, rfl, he₁, he₂⟩
  · have hSL : ∀ g : GL (Fin r) K, (g : Matrix (Fin r) (Fin r) K).det = 1 →
        g ∈ (GeneralLinearGroup.det : GL (Fin r) K →* Kˣ).ker := fun g hg => by
      rw [MonoidHom.mem_ker]
      exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, hg, Units.val_one])
    refine herm_splitting_of_sep hK (by omega) hSL (fun g => ⟨1, 1, ?_, ?_⟩)
      (fun a b i j _ hij h₁ h₂ => ?_) π hπV hsurj hπact hC2 hC
    · exact Units.ext (by rw [hTorusGL_coe]; simp)
    · rw [Subgroup.coe_one, map_one, MonoidHom.mem_ker.mp g.2]
    · obtain ⟨e, hprod, he₁, he₂⟩ := exists_sep_units_prod hK hr hω0 hω1 hij h₁ h₂
      exact ⟨torusΓ hSL e hprod, e, rfl, he₁, he₂⟩

end CFSG.LocalAnalysis.ComponentInitial
