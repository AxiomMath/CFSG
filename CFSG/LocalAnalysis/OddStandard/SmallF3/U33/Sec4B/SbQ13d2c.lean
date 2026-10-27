module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2c0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d2a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma orderOf_z4pow2_single_zero :
    orderOf (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4)) : Outside.Z4pow 2) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4)) : Outside.Z4pow 2) ^ 2 ≠ 1 := by
    intro hc
    rw [← ofAdd_nsmul, ofAdd_eq_one] at hc
    have h0 := congr_fun hc 0
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply] at h0
    rw [Nat.smul_one_eq_cast] at h0
    exact absurd h0 (by decide)
  have h4 : (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4)) : Outside.Z4pow 2) ^ 4 = 1 := by
    rw [← ofAdd_nsmul, ofAdd_eq_one]
    funext j
    fin_cases j <;> decide
  have h := orderOf_eq_prime_pow
    (x := (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4)) : Outside.Z4pow 2))
    (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  simpa using h

private lemma orderOf_z4pow2_single_one :
    orderOf (Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 4)) : Outside.Z4pow 2) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 4)) : Outside.Z4pow 2) ^ 2 ≠ 1 := by
    intro hc
    rw [← ofAdd_nsmul, ofAdd_eq_one] at hc
    have h0 := congr_fun hc 1
    simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply] at h0
    rw [Nat.smul_one_eq_cast] at h0
    exact absurd h0 (by decide)
  have h4 : (Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 4)) : Outside.Z4pow 2) ^ 4 = 1 := by
    rw [← ofAdd_nsmul, ofAdd_eq_one]
    funext j
    fin_cases j <;> decide
  have h := orderOf_eq_prime_pow
    (x := (Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 4)) : Outside.Z4pow 2))
    (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)
  simpa using h

private lemma z4pow2_basis_inf :
    zpowers (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4)) : Outside.Z4pow 2) ⊓
      zpowers (Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 4)) : Outside.Z4pow 2) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.mp hx).1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_inf.mp hx).2
  have hfun : m • (Pi.single 1 (1 : ZMod 4) : Fin 2 → ZMod 4) =
      n • (Pi.single 0 (1 : ZMod 4) : Fin 2 → ZMod 4) := by
    apply Multiplicative.ofAdd.injective
    rw [ofAdd_zsmul, ofAdd_zsmul]
    exact hm
  have h0 : (n • (Pi.single 0 (1 : ZMod 4) : Fin 2 → ZMod 4)) 0 = 0 := by
    have hne : (0 : Fin 2) ≠ 1 := by decide
    have h := congr_fun hfun 0
    simp only [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero] at h
    simpa only [Pi.smul_apply, Pi.single_eq_same] using h.symm
  rw [show (Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4)) : Outside.Z4pow 2) ^ n =
      Multiplicative.ofAdd (n • (Pi.single 0 (1 : ZMod 4) : Fin 2 → ZMod 4)) from
    (ofAdd_zsmul n _).symm, ofAdd_eq_one]
  funext j
  fin_cases j
  · exact h0
  · simp

theorem q13d_P_iso (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    IsZ4pow 3 (q13P t tau x₁ x₂ rho om) := by
  classical
  obtain ⟨e⟩ := q13a_A_iso h
  let v0 : Outside.Z4pow 2 := Multiplicative.ofAdd (Pi.single 0 (1 : ZMod 4))
  let v1 : Outside.Z4pow 2 := Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 4))
  let aA : ↥(q13A t tau x₁ x₂ rho) := e.symm v0
  let bA : ↥(q13A t tau x₁ x₂ rho) := e.symm v1
  let a : G := aA
  let b : G := bA
  have haA : a ∈ q13A t tau x₁ x₂ rho := aA.2
  have hbA : b ∈ q13A t tau x₁ x₂ rho := bA.2
  have hea : (e : ↥(q13A t tau x₁ x₂ rho) →* Outside.Z4pow 2) aA = v0 := by
    change e (e.symm v0) = v0
    simp
  have heb : (e : ↥(q13A t tau x₁ x₂ rho) →* Outside.Z4pow 2) bA = v1 := by
    change e (e.symm v1) = v1
    simp
  have ha4 : orderOf a = 4 := by
    change orderOf (aA : G) = 4
    rw [Subgroup.orderOf_coe]
    change orderOf (e.symm v0) = 4
    rw [MulEquiv.orderOf_eq]
    exact orderOf_z4pow2_single_zero
  have hb4 : orderOf b = 4 := by
    change orderOf (bA : G) = 4
    rw [Subgroup.orderOf_coe]
    change orderOf (e.symm v1) = 4
    rw [MulEquiv.orderOf_eq]
    exact orderOf_z4pow2_single_one
  have hab : a * b = b * a := q13a_A_comm h a haA b hbA
  have hc4 : orderOf (t * om) = 4 := q13d_orderOf_gam h
  have hac : a * (t * om) = (t * om) * a := (q13d_gam_cent_A h hII a haA).symm
  have hbc : b * (t * om) = (t * om) * b := (q13d_gam_cent_A h hII b hbA).symm
  have hmap2 : ((zpowers aA ⊓ zpowers bA).map
      (e : ↥(q13A t tau x₁ x₂ rho) →* Outside.Z4pow 2)) = zpowers v0 ⊓ zpowers v1 := by
    rw [Subgroup.map_inf _ _ _ e.injective, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hea, heb]
  have h1' : zpowers aA ⊓ zpowers bA = ⊥ :=
    Subgroup.map_injective (f := (e : ↥(q13A t tau x₁ x₂ rho) →* Outside.Z4pow 2)) e.injective
      (by rw [hmap2, z4pow2_basis_inf, Subgroup.map_bot])
  have hmap : ((zpowers aA ⊓ zpowers bA).map (q13A t tau x₁ x₂ rho).subtype)
      = zpowers a ⊓ zpowers b := by
    rw [Subgroup.map_inf _ _ _ (q13A t tau x₁ x₂ rho).subtype_injective,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have h1 : zpowers a ⊓ zpowers b = ⊥ := by
    rw [← hmap, h1', Subgroup.map_bot]
  have hle : zpowers a ⊔ zpowers b ≤ q13A t tau x₁ x₂ rho :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hbA)
  have hK : ∀ k ∈ zpowers b, ∀ x ∈ zpowers a, k * x * k⁻¹ ∈ zpowers a := by
    intro k hk x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : b ^ m * a ^ n = a ^ n * b ^ m :=
      ((commute_iff_eq a b).mpr hab).symm.zpow_zpow m n |>.eq
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers a n
  have hcard : Nat.card ↥(zpowers a ⊔ zpowers b) = 16 := by
    rw [card_sup_eq_mul hK h1, Nat.card_zpowers, Nat.card_zpowers, ha4, hb4]
  have hAeq : zpowers a ⊔ zpowers b = q13A t tau x₁ x₂ rho := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard, q13a_card_A h]
    norm_num
  have h2 : (zpowers a ⊔ zpowers b) ⊓ zpowers (t * om) = ⊥ := by
    rw [hAeq]
    apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact q13d_A_inf_gam h x (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
  obtain ⟨f⟩ := q13d_exists_mulEquiv_Z4cube (a := a) (b := b) (c := t * om)
    hab hac hbc ha4 hb4 hc4 h1 h2
  have hP : q13P t tau x₁ x₂ rho om = zpowers a ⊔ zpowers b ⊔ zpowers (t * om) := by
    rw [q13P, ← hAeq]
  exact ⟨(MulEquiv.subgroupCongr hP).trans f⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
