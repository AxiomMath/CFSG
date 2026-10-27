module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.GroupTheory.WeirSylow

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

open Classical in
theorem nonempty_quotient_center_omegaGroup_mulEquiv (hQ : Q.Nondegenerate)
    (h0 : 0 < Module.finrank (ZMod 3) V)
    (hZ : Nat.card (Subgroup.center (omegaGroup hQ)) = if piOrth Q ∈ omegaGroup hQ then 2 else 1) :
    Nonempty (omegaGroup hQ ⧸ Subgroup.center (omegaGroup hQ) ≃* omegaProj hQ) := by
  set φ : omegaGroup hQ →* ProjOrth Q :=
    (toProj Q).comp (omegaGroup hQ).subtype with hφ
  have hrange : φ.range = omegaProj hQ := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker_le : φ.ker ≤ Subgroup.center (omegaGroup hQ) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    have hg1 : toProj Q (g : OGroup Q) = 1 := by
      rw [hφ] at hg
      exact MonoidHom.mem_ker.mp hg
    have hgpi : (g : OGroup Q) ∈ piGroup Q := by
      rw [← QuotientGroup.ker_mk' (piGroup Q), MonoidHom.mem_ker]
      exact hg1
    rcases mem_piGroup_iff.mp hgpi with h1 | hp
    · apply Subtype.ext
      show (h : OGroup Q) * (g : OGroup Q) = (g : OGroup Q) * (h : OGroup Q)
      rw [h1, mul_one, one_mul]
    · apply Subtype.ext
      show (h : OGroup Q) * (g : OGroup Q) = (g : OGroup Q) * (h : OGroup Q)
      rw [hp]
      exact Subgroup.mem_center_iff.mp piOrth_mem_center (h : OGroup Q)
  have hcardker : Nat.card φ.ker = if piOrth Q ∈ omegaGroup hQ then 2 else 1 := by
    by_cases hmem : piOrth Q ∈ omegaGroup hQ
    · rw [if_pos hmem]
      let πΩ : omegaGroup hQ := ⟨piOrth Q, hmem⟩
      have hπmem : πΩ ∈ φ.ker := by
        rw [hφ, MonoidHom.mem_ker]
        exact toProj_piOrth
      have hker_eq : φ.ker = Subgroup.zpowers πΩ := by
        apply le_antisymm
        · intro g hg
          have hg1 : toProj Q (g : OGroup Q) = 1 := by
            rw [hφ] at hg
            exact MonoidHom.mem_ker.mp hg
          have hgpi : (g : OGroup Q) ∈ piGroup Q := by
            rw [← QuotientGroup.ker_mk' (piGroup Q), MonoidHom.mem_ker]
            exact hg1
          rcases mem_piGroup_iff.mp hgpi with h1 | hp
          · rw [show g = 1 from Subtype.ext h1]
            exact Subgroup.one_mem _
          · rw [show g = πΩ from Subtype.ext hp]
            exact Subgroup.mem_zpowers πΩ
        · exact Subgroup.zpowers_le.mpr hπmem
      rw [hker_eq, Nat.card_zpowers]
      apply orderOf_eq_prime
      · rw [pow_two]
        apply Subtype.ext
        exact piOrth_mul_self
      · intro h
        exact piOrth_ne_one h0 (Subtype.ext_iff.mp h)
    · rw [if_neg hmem]
      have hker_bot : φ.ker = ⊥ := by
        apply le_antisymm _ bot_le
        intro g hg
        rw [Subgroup.mem_bot]
        have hg1 : toProj Q (g : OGroup Q) = 1 := by
          rw [hφ] at hg
          exact MonoidHom.mem_ker.mp hg
        have hgpi : (g : OGroup Q) ∈ piGroup Q := by
          rw [← QuotientGroup.ker_mk' (piGroup Q), MonoidHom.mem_ker]
          exact hg1
        rcases mem_piGroup_iff.mp hgpi with h1 | hp
        · exact Subtype.ext h1
        · exact absurd (hp ▸ g.2) hmem
      rw [hker_bot, Subgroup.card_bot]
  haveI : Finite (Subgroup.center (omegaGroup hQ)) :=
    Nat.finite_of_card_ne_zero (by
      by_cases hmem : piOrth Q ∈ omegaGroup hQ <;> simp [hZ, hmem])
  have hcenter_eq : φ.ker = Subgroup.center (omegaGroup hQ) := by
    apply Subgroup.eq_of_le_of_card_ge hker_le
    rw [hZ, hcardker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenter_eq.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem natCard_omegaGroup_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) : Nat.card (omegaGroup hQ) = 25920 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hpolar : (QuadraticMap.polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hchar : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  have hcard := Subgroup.card_mul_index (H := omegaGroup hQ)
  rw [index_omegaGroup hQ h2] at hcard
  have hOint : (Nat.card (OGroup Q) : ℤ) = 103680 := by
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_odd (K := ZMod 3) (V := V)
      hchar hpolar (n := 2) (by rw [hdim])
    have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (2 ^ 2) *
        (∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 103680 := by
      rw [Nat.card_zmod]
      decide +kernel
    exact h.trans hval
  have hO_nat : Nat.card (OGroup Q) = 103680 := by exact_mod_cast hOint
  rw [hO_nat] at hcard
  omega

theorem natCard_omegaGroup_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Nat.card (omegaGroup hQ) = 6065280 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hpolar : (QuadraticMap.polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hplus : IsPlusType Q :=
    (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by rw [hdim])).mpr hs
  have hcard := Subgroup.card_mul_index (H := omegaGroup hQ)
  rw [index_omegaGroup hQ h2] at hcard
  have hOint : (Nat.card (OGroup Q) : ℤ) = 24261120 := by
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
      hpolar (m := 2) (by rw [hdim]) (ε := 1) (Or.inl ⟨rfl, hplus⟩)
    have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (2 * (2 + 1)) *
        ((Nat.card (ZMod 3) : ℤ) ^ (2 + 1) - 1) *
        (∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 24261120 := by
      rw [Nat.card_zmod]
      decide +kernel
    exact h.trans hval
  have hO_nat : Nat.card (OGroup Q) = 24261120 := by exact_mod_cast hOint
  rw [hO_nat] at hcard
  omega

theorem natCard_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Nat.card (omegaGroup hQ) = 6531840 := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by rw [hdim]; norm_num
  have hpolar : (QuadraticMap.polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hnplus : ¬ IsPlusType Q := fun h => by
    have h1 : quadSign Q = 1 :=
      (isPlusType_iff_quadSign_eq_one hQ (d := 3) (by rw [hdim])).mp h
    rw [hs] at h1
    exact (by decide : (-1 : ℤˣ) ≠ 1) h1
  have hcard := Subgroup.card_mul_index (H := omegaGroup hQ)
  rw [index_omegaGroup hQ h2] at hcard
  have hOint : (Nat.card (OGroup Q) : ℤ) = 26127360 := by
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 3) (V := V)
      hpolar (m := 2) (by rw [hdim]) (ε := -1) (Or.inr ⟨rfl, hnplus⟩)
    have hval : 2 * (Nat.card (ZMod 3) : ℤ) ^ (2 * (2 + 1)) *
        ((Nat.card (ZMod 3) : ℤ) ^ (2 + 1) - (-1)) *
        (∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 3) : ℤ) ^ 2) ^ i - 1)) = 26127360 := by
      rw [Nat.card_zmod]
      decide +kernel
    exact h.trans hval
  have hO_nat : Nat.card (OGroup Q) = 26127360 := by exact_mod_cast hOint
  rw [hO_nat] at hcard
  omega

end CFSG.OddStandard.SmallF3.Omega
