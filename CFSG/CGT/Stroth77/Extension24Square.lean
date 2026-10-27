module

public import CFSG.CGT.Stroth77.Extension24Comm
public import CFSG.CGT.Stroth77.Extension22FourBasis

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {n : ℕ}

theorem t300_k_pos (hn : 1 ≤ n) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t300 n).k i := by
  fin_cases i <;> exact hn

theorem parityTorus_zsmul_gens {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (p q r : ℤ) :
    parityTorus k hk (p • gen k 0 + q • gen k 1 + r • gen k 2) =
      ![(p : ZMod 2), (q : ZMod 2), (r : ZMod 2)] := by
  funext i
  fin_cases i
  · change ZMod.castHom (pow_dvd_pow 2 (hk 0)) (ZMod 2)
      ((p • gen k 0 + q • gen k 1 + r • gen k 2) 0) = _
    rw [zsmul_gens_apply_zero, map_intCast]
    rfl
  · change ZMod.castHom (pow_dvd_pow 2 (hk 1)) (ZMod 2)
      ((p • gen k 0 + q • gen k 1 + r • gen k 2) 1) = _
    rw [zsmul_gens_apply_one, map_intCast]
    rfl
  · change ZMod.castHom (pow_dvd_pow 2 (hk 2)) (ZMod 2)
      ((p • gen k 0 + q • gen k 1 + r • gen k 2) 2) = _
    rw [zsmul_gens_apply_two, map_intCast]
    rfl

theorem parityTorus_eq_zero_iff {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (x : Torus k) :
    parityTorus k hk x = 0 ↔ ∃ z : Torus k, 2 • z = x := by
  constructor
  · intro h
    have hi : ∀ i, ∃ y : ZMod (2 ^ k i), 2 * y = x i := fun i =>
      (zmod_castHom_eq_zero_iff_two_mul (hk i) (x i)).mp (congrFun h i)
    choose y hy using hi
    exact ⟨y, funext fun i => by simpa [two_nsmul, two_mul] using hy i⟩
  · rintro ⟨z, rfl⟩
    rw [map_nsmul]
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat]
    exact mul_eq_zero_of_left (by decide) _

@[expose] def rhoBar300 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![v 0, v 2, v 1 + v 2]

theorem parityTorus_rho300 (hk : ∀ i, 1 ≤ Type300.k n i) (y : Torus (Type300.k n)) :
    parityTorus _ hk ((Type300.action n).φρ y) = rhoBar300 (parityTorus _ hk y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens (Type300.k n) y
  rw [type300_rho_apply_gens, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext t
  fin_cases t
  · simp [rhoBar300, h4]
  · simp [rhoBar300, ZMod.neg_eq_self_mod_two]
  · simp [rhoBar300, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem rhoBar300_check : ∀ v w : Fin 3 → ZMod 2, (v ≠ 0 ∧ w ≠ 0 ∧ v ≠ w ∧
    (rhoBar300 v = 0 ∨ rhoBar300 v = v ∨ rhoBar300 v = w ∨ rhoBar300 v = v + w) ∧
    (rhoBar300 w = 0 ∨ rhoBar300 w = v ∨ rhoBar300 w = w ∨ rhoBar300 w = v + w)) →
    v = Pi.single 1 1 ∨ w = Pi.single 1 1 ∨ v + w = Pi.single 1 1 := by
  unfold rhoBar300
  decide

section Cosets

variable [hN : (B.subgroupOf C).Normal]

theorem mem_cosets_Idx4 (hcard : Nat.card (C ⧸ B.subgroupOf C) = 4)
    (hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1) {x₁ x₂ : C}
    (h1 : x₁ ∉ B.subgroupOf C) (h2 : x₂ ∉ B.subgroupOf C) (h12 : x₁ * x₂⁻¹ ∉ B.subgroupOf C)
    (y : C) :
    y ∈ B.subgroupOf C ∨ y * x₁⁻¹ ∈ B.subgroupOf C ∨ y * x₂⁻¹ ∈ B.subgroupOf C ∨
      y * (x₁ * x₂)⁻¹ ∈ B.subgroupOf C := by
  classical
  let Q := C ⧸ B.subgroupOf C
  let π : C →* Q := QuotientGroup.mk' (B.subgroupOf C)
  have hmem : ∀ x : C, x ∈ B.subgroupOf C ↔ π x = 1 := fun x =>
    (QuotientGroup.eq_one_iff x).symm
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Nontrivial Q := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Fintype.card_eq_nat_card, hcard]; norm_num)
  haveI : IsKleinFour Q := by
    refine ⟨hcard, ?_⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro q hq
    have hdvd : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using hexp q)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq
    · exact h
  have hq1 : π x₁ ≠ 1 := fun h => h1 ((hmem x₁).mpr h)
  have hq2 : π x₂ ≠ 1 := fun h => h2 ((hmem x₂).mpr h)
  have hq12 : π x₁ ≠ π x₂ := by
    intro h
    apply h12
    rw [hmem, map_mul, map_inv, h, mul_inv_cancel]
  by_cases hy0 : π y = 1
  · exact Or.inl ((hmem y).mpr hy0)
  by_cases hy1 : π y = π x₁
  · exact Or.inr (Or.inl ((hmem _).mpr (by rw [map_mul, map_inv, hy1, mul_inv_cancel])))
  by_cases hy2 : π y = π x₂
  · exact Or.inr (Or.inr (Or.inl ((hmem _).mpr (by rw [map_mul, map_inv, hy2, mul_inv_cancel]))))
  have hy3 : π y = π x₁ * π x₂ := IsKleinFour.eq_mul_of_ne_all hq1 hq2 hq12 hy0 hy1 hy2
  exact Or.inr (Or.inr (Or.inr ((hmem _).mpr (by
    rw [map_mul, map_inv, hy3, map_mul, mul_inv_cancel]))))

theorem exists_gens_Idx4 (hcard : Nat.card (C ⧸ B.subgroupOf C) = 4)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ x₁ x₂ : C, x₁ ∉ B.subgroupOf C ∧ x₂ ∉ B.subgroupOf C ∧ x₁ * x₂⁻¹ ∉ B.subgroupOf C := by
  classical
  let Q := C ⧸ B.subgroupOf C
  let π : C →* Q := QuotientGroup.mk' (B.subgroupOf C)
  have hmem : ∀ x : C, x ∈ B.subgroupOf C ↔ π x = 1 := fun x =>
    (QuotientGroup.eq_one_iff x).symm
  haveI : Fintype Q := Fintype.ofFinite Q
  have hone_lt : 1 < Fintype.card Q := by
    rw [Fintype.card_eq_nat_card, hcard]; norm_num
  obtain ⟨q₁, hq₁⟩ := Fintype.exists_ne_of_one_lt_card hone_lt (1 : Q)
  have hq₁top : Subgroup.zpowers q₁ ≠ ⊤ := fun htop =>
    hncyc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨q₁, htop⟩)
  have hnot : ¬ (⊤ : Set Q) ⊆ (Subgroup.zpowers q₁ : Set Q) := fun h =>
    hq₁top (le_antisymm le_top h)
  obtain ⟨q₂, -, hq₂⟩ := Set.not_subset.mp hnot
  obtain ⟨x₁, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₁
  obtain ⟨x₂, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₂
  refine ⟨x₁, x₂, fun h => hq₁ ((hmem x₁).mp h), fun h => hq₂ ?_, fun h => hq₂ ?_⟩
  · rw [(hmem x₂).mp h]
    exact Subgroup.one_mem _
  · have h' : π x₁ * (π x₂)⁻¹ = 1 := by rw [← map_inv, ← map_mul]; exact (hmem _).mp h
    rw [mul_inv_eq_one] at h'
    change π x₂ ∈ Subgroup.zpowers (π x₁)
    rw [← h']
    exact Subgroup.mem_zpowers _

end Cosets

theorem eq_zpow_c_a_b_Idx4 {τ : StrothTypeIndex} (D : StrothTypeData B τ) {β : B} {i j l : ℤ}
    (h : D.ec β = i • gen τ.k 0 + j • gen τ.k 1 + l • gen τ.k 2) :
    β = D.c ^ i * D.a ^ j * D.b ^ l := by
  apply D.ec_injective
  rw [h, D.ec_mul, D.ec_mul, D.ec_zpow, D.ec_zpow, D.ec_zpow, D.ec_c, D.ec_a, D.ec_b]

section Square

variable (D : StrothTypeData B (StrothTypeIndex.t300 n)) (hn : 1 ≤ n)
  (hsq : ∀ x : C, (x : S) * x ∈ B)

@[expose] noncomputable def sqParity300 (x : C) : Fin 3 → ZMod 2 :=
  parityTorus _ (t300_k_pos hn) (D.ec ⟨(x : S) * x, hsq x⟩)

variable {D hn hsq}

theorem sqParity300_mul (hcomm : ∀ x y : C, x * y = y * x) (x y : C) :
    sqParity300 D hn hsq (x * y) = sqParity300 D hn hsq x + sqParity300 D hn hsq y := by
  have hxy : (⟨((x * y : C) : S) * ((x * y : C) : S), hsq (x * y)⟩ : B) =
      ⟨(x : S) * x, hsq x⟩ * ⟨(y : S) * y, hsq y⟩ := by
    apply Subtype.ext
    have h := congrArg Subtype.val (hcomm x y)
    simp only [Subgroup.coe_mul] at h ⊢
    calc (x : S) * y * ((x : S) * y) = x * ((y : S) * x) * y := by group
      _ = x * ((x : S) * y) * y := by rw [← h]
      _ = (x : S) * x * ((y : S) * y) := by group
  simp only [sqParity300]
  rw [hxy, D.ec_mul, map_add]

theorem sqParity300_of_mem (x : C) (hx : (x : S) ∈ B) : sqParity300 D hn hsq x = 0 := by
  simp only [sqParity300]
  rw [parityTorus_eq_zero_iff]
  refine ⟨D.ec ⟨x, hx⟩, ?_⟩
  have h : (⟨(x : S) * x, hsq x⟩ : B) = ⟨x, hx⟩ * ⟨x, hx⟩ := rfl
  rw [h, D.ec_mul, two_nsmul]

theorem mem_of_sqParity300_eq_zero (hcomm : ∀ x y : C, x * y = y * x)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') (hBC : B ≤ C) (x : C) (h : sqParity300 D hn hsq x = 0) :
    (x : S) ∈ B := by
  simp only [sqParity300] at h
  rw [parityTorus_eq_zero_iff] at h
  obtain ⟨z, hz⟩ := h
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = ⟨(x : S) * x, hsq x⟩ := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  have hσS : (σ : S) * σ = (x : S) * x := by
    simpa using congrArg Subtype.val hσ
  let σC : C := ⟨σ, hBC σ.2⟩
  let w : C := x * σC⁻¹
  have hww : (w : S) * w = 1 := by
    have hwC : w * w = 1 := by
      calc w * w = x * (σC⁻¹ * x) * σC⁻¹ := by simp only [w]; group
        _ = x * (x * σC⁻¹) * σC⁻¹ := by rw [hcomm σC⁻¹ x]
        _ = (x * x) * (σC * σC)⁻¹ := by group
        _ = 1 := by
          rw [mul_inv_eq_one]
          apply Subtype.ext
          simpa [σC] using hσS.symm
    simpa using congrArg Subtype.val hwC
  have hwB : (w : S) ∈ B := hH w (hcS w.2) hww (hC w.2)
  have hx : (x : S) = w * σ := by simp [w, σC]
  rw [hx]
  exact B.mul_mem hwB σ.2

theorem sqParity300_conj_ρ (hL : D.L ≤ Subgroup.normalizer C) (x : C) :
    sqParity300 D hn hsq (conjBy (hL D.ρ_mem_L) x) = rhoBar300 (sqParity300 D hn hsq x) := by
  have h : (⟨((conjBy (hL D.ρ_mem_L) x : C) : S) * (conjBy (hL D.ρ_mem_L) x : C),
      hsq _⟩ : B) = conjBy D.ρ_mem ⟨(x : S) * x, hsq x⟩ := by
    apply Subtype.ext
    simp only [conjBy_val]
    group
  simp only [sqParity300]
  rw [h]
  have hconj : D.ec (conjBy D.ρ_mem ⟨(x : S) * x, hsq x⟩) =
      (Type300.action n).φρ (D.ec ⟨(x : S) * x, hsq x⟩) := D.ρ_conj _
  rw [hconj]
  exact parityTorus_rho300 (t300_k_pos hn) _

theorem sqParity300_of_sq_eq_a (hBC : B ≤ C) {x : C} (hx : x * x = ⟨D.a, hBC D.a.2⟩) :
    sqParity300 D hn hsq x = Pi.single 1 1 := by
  have h : (⟨(x : S) * x, hsq x⟩ : B) = D.a := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hx
  simp only [sqParity300]
  rw [h, D.ec_a]
  exact parityTorus_gen _ _ 1

theorem sqParity300_of_sq_eq_b (hBC : B ≤ C) {x : C} (hx : x * x = ⟨D.b, hBC D.b.2⟩) :
    sqParity300 D hn hsq x = Pi.single 2 1 := by
  have h : (⟨(x : S) * x, hsq x⟩ : B) = D.b := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hx
  simp only [sqParity300]
  rw [h, D.ec_b]
  exact parityTorus_gen _ _ 2

end Square

section Main

variable [hN : (B.subgroupOf C).Normal]

theorem exists_sq_eq_a300_of_data (D : StrothTypeData B (StrothTypeIndex.t300 n)) (hn : 1 ≤ n)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ e : C, e * e = ⟨D.a, hBC D.a.2⟩ := by
  classical
  have hcommC : IsMulCommutative C := isMulCommutative_of_relIndex_four_t300_of_data D hBC hC hrel hL hncyc
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  let P : C → Fin 3 → ZMod 2 := sqParity300 D hn hsq
  have hPmul : ∀ x y, P (x * y) = P x + P y := sqParity300_mul hcomm
  have hPB : ∀ x : C, x ∈ B.subgroupOf C → P x = 0 := fun x hx =>
    sqParity300_of_mem x (Subgroup.mem_subgroupOf.mp hx)
  have hP0 : ∀ x : C, P x = 0 → x ∈ B.subgroupOf C := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (mem_of_sqParity300_eq_zero hcomm hC hH hcS hBC x hx)
  have hPinv : ∀ x, P x⁻¹ = -P x := by
    intro x
    have h := hPmul x⁻¹ x
    rw [inv_mul_cancel, hPB 1 (Subgroup.one_mem _)] at h
    exact (neg_eq_of_add_eq_zero_left h.symm).symm
  obtain ⟨x₁, x₂, h1, h2, h12⟩ := exists_gens_Idx4 hcardQ hncyc
  have hrange : ∀ y : C, P y = 0 ∨ P y = P x₁ ∨ P y = P x₂ ∨ P y = P x₁ + P x₂ := by
    intro y
    have hcoset := mem_cosets_Idx4 hcardQ hexp h1 h2 h12 y
    have key : ∀ x : C, y * x⁻¹ ∈ B.subgroupOf C → P y = P x := by
      intro x hx
      have h := hPmul (y * x⁻¹) x
      rw [inv_mul_cancel_right, hPB _ hx, zero_add] at h
      exact h
    rcases hcoset with h | h | h | h
    · exact Or.inl (hPB y h)
    · exact Or.inr (Or.inl (key x₁ h))
    · exact Or.inr (Or.inr (Or.inl (key x₂ h)))
    · exact Or.inr (Or.inr (Or.inr ((key _ h).trans (hPmul x₁ x₂))))
  have hv1 : P x₁ ≠ 0 := fun h => h1 (hP0 x₁ h)
  have hv2 : P x₂ ≠ 0 := fun h => h2 (hP0 x₂ h)
  have hv12 : P x₁ ≠ P x₂ := by
    intro h
    apply h12
    apply hP0
    rw [hPmul, hPinv, h]
    exact add_neg_cancel _
  have hρ1 := hrange (conjBy (hL D.ρ_mem_L) x₁)
  have hρ2 := hrange (conjBy (hL D.ρ_mem_L) x₂)
  rw [show P (conjBy (hL D.ρ_mem_L) x₁) = rhoBar300 (P x₁) from sqParity300_conj_ρ hL x₁]
    at hρ1
  rw [show P (conjBy (hL D.ρ_mem_L) x₂) = rhoBar300 (P x₂) from sqParity300_conj_ρ hL x₂]
    at hρ2
  obtain ⟨y, hy⟩ : ∃ y : C, P y = Pi.single 1 1 := by
    rcases rhoBar300_check (P x₁) (P x₂) ⟨hv1, hv2, hv12, hρ1, hρ2⟩ with h | h | h
    · exact ⟨x₁, h⟩
    · exact ⟨x₂, h⟩
    · exact ⟨x₁ * x₂, (hPmul x₁ x₂).trans h⟩
  have hpar : parityTorus _ (t300_k_pos hn) (D.ec (⟨(y : S) * y, hsq y⟩ * D.a⁻¹)) = 0 := by
    have hy' : parityTorus _ (t300_k_pos hn) (D.ec ⟨(y : S) * y, hsq y⟩) = Pi.single 1 1 := hy
    rw [D.ec_mul, D.ec_inv, map_add, map_neg, D.ec_a, parityTorus_gen, hy']
    exact add_neg_cancel _
  rw [parityTorus_eq_zero_iff] at hpar
  obtain ⟨z, hz⟩ := hpar
  let σ : B := Additive.toMul (D.e.symm z)
  have hσz : D.ec σ = z := D.e.apply_symm_apply z
  have hσ : σ * σ = ⟨(y : S) * y, hsq y⟩ * D.a⁻¹ := by
    apply D.ec_injective
    rw [D.ec_mul, ← two_nsmul, hσz, hz]
  let aC : C := ⟨D.a, hBC D.a.2⟩
  let σC : C := ⟨σ, hBC σ.2⟩
  have hσC2 : σC * σC = y * y * aC⁻¹ := by
    apply Subtype.ext
    simpa [σC, aC] using congrArg Subtype.val hσ
  refine ⟨y * σC⁻¹, ?_⟩
  change y * σC⁻¹ * (y * σC⁻¹) = aC
  calc y * σC⁻¹ * (y * σC⁻¹) = y * (σC⁻¹ * y) * σC⁻¹ := by group
    _ = y * (y * σC⁻¹) * σC⁻¹ := by rw [hcomm σC⁻¹ y]
    _ = (y * y) * (σC * σC)⁻¹ := by group
    _ = (y * y) * (y * y * aC⁻¹)⁻¹ := by rw [hσC2]
    _ = aC := by
      rw [mul_inv_rev, inv_inv, ← mul_assoc, hcomm (y * y) aC, mul_assoc, mul_inv_cancel,
        mul_one]

theorem exists_sq_eq_a300 (hB : HasStrothType B (StrothTypeIndex.t300 n)) (hn : 1 ≤ n)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) :
    ∃ e : C, e * e = ⟨hB.data.a, hBC hB.data.a.2⟩ :=
  exists_sq_eq_a300_of_data hB.data hn hBC hC hrel hL hH hcS hncyc

end Main

end CFSG.CGT.Stroth77
