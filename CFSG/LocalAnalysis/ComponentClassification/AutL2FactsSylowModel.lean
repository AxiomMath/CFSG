module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2TwoPartArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

universe u

variable {F : Type u} [Field F]

theorem swp_mul_self (ε : Bool) : swp F ε * swp F ε = 1 := by
  rw [swp_mul_swp, Bool.xor_self, swp_false]

theorem swp_inv (ε : Bool) : (swp F ε)⁻¹ = swp F ε :=
  inv_eq_of_mul_eq_one_right (swp_mul_self ε)

theorem twist_mem {U : Subgroup Fˣ} {y : Fˣ} (hy : y ∈ U) (ε : Bool) : twist F ε y ∈ U := by
  cases ε
  · exact hy
  · exact U.inv_mem hy

variable (F) in
@[expose] def torSub (U : Subgroup Fˣ) : Subgroup (PGL2 F) where
  carrier := {g | ∃ y ∈ U, ∃ ε : Bool, g = tor F y * swp F ε}
  mul_mem' := by
    rintro _ _ ⟨y, hy, ε, rfl⟩ ⟨y', hy', ε', rfl⟩
    refine ⟨y * twist F ε y', U.mul_mem hy (twist_mem hy' ε), xor ε ε', ?_⟩
    rw [mul_assoc, ← mul_assoc (swp F ε), swp_mul_tor, mul_assoc, swp_mul_swp, ← mul_assoc,
      ← map_mul]
  one_mem' := ⟨1, U.one_mem, false, by simp⟩
  inv_mem' := by
    rintro _ ⟨y, hy, ε, rfl⟩
    refine ⟨twist F ε y⁻¹, twist_mem (U.inv_mem hy) ε, ε, ?_⟩
    rw [mul_inv_rev, swp_inv, ← map_inv, swp_mul_tor]

theorem mem_torSub {U : Subgroup Fˣ} {g : PGL2 F} :
    g ∈ torSub F U ↔ ∃ y ∈ U, ∃ ε : Bool, g = tor F y * swp F ε := Iff.rfl

theorem card_torSub [Finite F] (U : Subgroup Fˣ) : Nat.card (torSub F U) = Nat.card U * 2 := by
  let g : U × Bool → torSub F U := fun x => ⟨tor F x.1 * swp F x.2, x.1, x.1.2, x.2, rfl⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨y, ε⟩ ⟨y', ε'⟩ h
      obtain ⟨h1, h2⟩ := tor_mul_swp_injective (congrArg Subtype.val h)
      simp only at h1 h2
      rw [Subtype.ext h1, h2]
    · rintro ⟨_, y, hy, ε, rfl⟩
      exact ⟨⟨⟨y, hy⟩, ε⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective g hg), Nat.card_prod, show Nat.card Bool = 2 by simp]

theorem sw_mem_range (hsq : IsSquare (-1 : F)) :
    sw F ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  rw [sw, pgl2_mk_mem_psl2_range_iff_det_isSquare]
  convert hsq using 1
  simp [swGL, Matrix.det_fin_two]

theorem tor_mem_range {y : Fˣ} (hy : IsSquare (y : F)) :
    tor F y ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F y) ∈ _
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare]
  convert hy using 1
  simp [pGammaL2FullSplitTorusGL]

theorem torSub_le_range (hsq : IsSquare (-1 : F)) {U : Subgroup Fˣ}
    (hU : ∀ y ∈ U, IsSquare (y : F)) :
    torSub F U ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  rintro _ ⟨y, hy, ε, rfl⟩
  refine mul_mem (tor_mem_range (hU y hy)) ?_
  cases ε
  · exact one_mem _
  · exact sw_mem_range hsq

abbrev twoVal (F : Type*) : ℕ := (Nat.card F - 1).factorization 2

theorem two_pow_twoVal_dvd (F : Type*) : 2 ^ twoVal F ∣ Nat.card F - 1 := Nat.ordProj_dvd _ _

theorem not_two_pow_twoVal_succ_dvd (F : Type*) (hq : 2 ≤ Nat.card F) :
    ¬ 2 ^ (twoVal F + 1) ∣ Nat.card F - 1 :=
  Nat.pow_succ_factorization_not_dvd (by omega) Nat.prime_two

section TwoPart

variable [Finite F]

theorem exists_orderOf_twoVal : ∃ a₀ : Fˣ, orderOf a₀ = 2 ^ twoVal F := by
  have : IsCyclic Fˣ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  rw [Nat.card_units] at hg
  obtain ⟨m, hm⟩ := two_pow_twoVal_dvd F
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    have := Finite.one_lt_card (α := F)
    omega
  refine ⟨g ^ m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hg, hm]; exact dvd_mul_left _ _), hg, hm,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

variable (F) in
@[expose] def stdGen : Fˣ := (exists_orderOf_twoVal (F := F)).choose

theorem orderOf_stdGen : orderOf (stdGen F) = 2 ^ twoVal F :=
  (exists_orderOf_twoVal (F := F)).choose_spec

theorem one_le_twoVal (hodd : IsOddPrimePower (Nat.card F)) : 1 ≤ twoVal F := by
  have h2 : 2 ∣ Nat.card F - 1 := by
    obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hodd
    rw [hc]
    exact (Nat.odd_iff.mp (hpodd.pow (n := n))) ▸ (Nat.dvd_sub_mod (p ^ n))
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (by omega)).mp h2
  exact this

theorem orderOf_stdGen_sq (hodd : IsOddPrimePower (Nat.card F)) :
    orderOf (stdGen F ^ 2) = 2 ^ (twoVal F - 1) := by
  have h1 := one_le_twoVal hodd
  rw [orderOf_pow_of_dvd (by norm_num) (by
      rw [orderOf_stdGen]; exact dvd_pow_self 2 (by omega)), orderOf_stdGen]
  obtain ⟨k, hk⟩ : ∃ k, twoVal F = k + 1 := ⟨twoVal F - 1, by omega⟩
  rw [hk, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]

variable (F) in
@[expose] def stdT : Subgroup (PSL2 F) :=
  (torSub F (zpowers (stdGen F ^ 2))).comap
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F))

theorem torSub_stdGen_le_range (hsq : IsSquare (-1 : F)) :
    torSub F (zpowers (stdGen F ^ 2)) ≤
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  apply torSub_le_range hsq
  rintro _ ⟨i, rfl⟩
  refine ⟨((stdGen F ^ i : Fˣ) : F), ?_⟩
  simp only [← zpow_natCast, ← zpow_mul, Units.val_zpow_eq_zpow_val]
  rw [← zpow_add₀ (Units.ne_zero _)]
  congr 1
  push_cast
  ring

theorem map_stdT (hsq : IsSquare (-1 : F)) :
    (stdT F).map (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)) =
      torSub F (zpowers (stdGen F ^ 2)) :=
  Subgroup.map_comap_eq_self (torSub_stdGen_le_range hsq)

theorem card_stdT (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) :
    Nat.card (stdT F) = 2 ^ twoVal F := by
  rw [← Subgroup.card_map_of_injective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F)),
    map_stdT hsq, card_torSub, Nat.card_zpowers, orderOf_stdGen_sq hodd, ← pow_succ,
    Nat.sub_add_cancel (one_le_twoVal hodd)]

theorem psl2_factorization_two (hodd : IsOddPrimePower (Nat.card F)) (hq4 : Nat.card F % 4 = 1) :
    (Nat.card (PSL2 F)).factorization 2 = twoVal F := by
  have hq : Odd (Nat.card F) := by
    obtain ⟨p, n, hp, hpodd, hn, hc⟩ := hodd
    rw [hc]; exact hpodd.pow
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have heven : Even ((Nat.card F - 1) / 2) := ⟨(Nat.card F - 1) / 4, by omega⟩
  rw [psl2_card_formula F hodd, psl2_order_two_factorization_split hq hq1 heven]
  have h2 : Nat.card F - 1 = 2 * ((Nat.card F - 1) / 2) := by omega
  rw [twoVal, h2, Nat.factorization_mul (by norm_num) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, add_comm, Nat.mul_div_cancel_left _ two_pos]

variable (F) in
@[expose] def stdSylow (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) : Sylow 2 (PSL2 F) :=
  Sylow.ofCard (stdT F) (by rw [card_stdT hodd hsq, psl2_factorization_two hodd hq4])

theorem coe_stdSylow (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) : (stdSylow F hodd hsq hq4 : Subgroup (PSL2 F)) = stdT F :=
  Sylow.coe_ofCard _ _

end TwoPart

end CFSG.ComponentClassification.AutL2Facts
