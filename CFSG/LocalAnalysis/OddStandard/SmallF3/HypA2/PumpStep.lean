module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PumpStepKK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotTransferQS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.A2Cases
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaTStep1

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.GH74.GLS

private abbrev fixSub {G : Type*} [Group G] (σ : MulAut G) : Subgroup G :=
  CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup σ

private theorem fixedSubgroup_conjAut {G : Type} [Group G] (K : Subgroup G) (x : G)
    (hx : K.map (MulAut.conj x).toMonoidHom = K) :
    fixSub (conjAut K x hx) = (K ⊓ centralizer ({x} : Set G)).subgroupOf K := by
  ext k
  rw [CFSG.LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hk
    have hk' : x * (k : G) * x⁻¹ = (k : G) := by
      have hval := congrArg Subtype.val hk
      rwa [coe_conjAut_apply] at hval
    refine ⟨k.2, fun a ha => ?_⟩
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    calc x * (k : G) = x * (k : G) * x⁻¹ * x := by group
      _ = (k : G) * x := by rw [hk']
  · rintro ⟨-, hc⟩
    apply Subtype.ext
    rw [coe_conjAut_apply, hc x (by simp)]
    group

theorem pumpStep {G : Type} [Group G] [Finite G]
    (hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {x x' : G} {K K' : Subgroup G} (h : PumpUpLT 2 x K x' K') :
    IsQuasisimple ↥K ∧ IsQuasisimple ↥K' ∧
      (Nonempty (↥K ⧸ center ↥K ≃* ↥K' ⧸ center ↥K') ∨
        ∃ (σ : MulAut (↥K' ⧸ center ↥K')) (P : Subgroup (↥K' ⧸ center ↥K')),
          ProperFixedComp σ P ∧ Nonempty (↥K ⧸ center ↥K ≃* ↥P ⧸ center ↥P)) := by
  have hKq : IsQuasisimple ↥K := isQuasisimple_of_isILo hbal h.1
  have hK'q : IsQuasisimple ↥K' := isQuasisimple_of_isILo hbal h.2.1
  have hA2 : A2Config G x x' K K' := a2Config_of_pumpUpLT hbal h
  have hbal' : oddCore (centralizer ({x'} : Set G)) = ⊥ := hbal x' h.2.1.1
  obtain ⟨-, hcases⟩ := a2Config_cases hbal' hA2
  refine ⟨hKq, hK'q, ?_⟩
  rcases hcases with ⟨hfix, hKK'le, h2comp⟩ | ⟨hne, hcomm, φ, hφapply, hKrange, hker⟩
  ·
    by_cases hKK' : K = K'
    · subst hKK'
      exact Or.inl ⟨MulEquiv.refl _⟩
    ·
      have hx2 : x * x = 1 := by
        have hpow := pow_orderOf_eq_one x
        rw [h.1.1] at hpow
        simpa [pow_two] using hpow
      have hx2inv : x⁻¹ * x⁻¹ = 1 := by
        rw [← mul_inv_rev, hx2, inv_one]
      have hσ : ∀ y : ↥K', conjAut K' x hfix (conjAut K' x hfix y) = y := by
        intro k
        apply Subtype.ext
        rw [coe_conjAut_apply, coe_conjAut_apply]
        calc x * (x * (k : G) * x⁻¹) * x⁻¹
            = (x * x) * (k : G) * (x⁻¹ * x⁻¹) := by group
          _ = (k : G) := by rw [hx2, hx2inv, one_mul, mul_one]
      let X' : Subgroup ↥K' := K.subgroupOf K'
      have hX'top : X' ≠ ⊤ := by
        intro htop
        exact hKK' (le_antisymm hKK'le (Subgroup.subgroupOf_eq_top.mp htop))
      have hXF : X' ≤ fixSub (conjAut K' x hfix) := by
        intro k hk
        rw [CFSG.LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff]
        apply Subtype.ext
        rw [coe_conjAut_apply]
        have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
        have hcm : x * (k : G) = (k : G) * x :=
          Subgroup.mem_centralizer_iff.mp (h.1.2.2.1 hkK) x (by simp)
        rw [hcm]
        group
      have hqX : IsQuasisimple ↥(X'.subgroupOf (fixSub (conjAut K' x hfix))) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv
          ((Subgroup.subgroupOfEquivOfLe hXF).trans
            (Subgroup.subgroupOfEquivOfLe hKK'le)).symm hKq
      have hsubX : (X'.subgroupOf (fixSub (conjAut K' x hfix))).IsSubnormal := by
        let C : Subgroup G := K' ⊓ centralizer ({x} : Set G)
        have hC_le : C ≤ K' := inf_le_left
        have hFixEq : fixSub (conjAut K' x hfix) = C.subgroupOf K' :=
          fixedSubgroup_conjAut K' x hfix
        let Φ : ↥(fixSub (conjAut K' x hfix)) ≃* ↥C :=
          (MulEquiv.subgroupCongr hFixEq).trans (Subgroup.subgroupOfEquivOfLe hC_le)
        have hcomap : (K.subgroupOf C).comap Φ.toMonoidHom =
            X'.subgroupOf (fixSub (conjAut K' x hfix)) := by
          ext y
          simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
          rfl
        have h2 : (K.subgroupOf C).IsSubnormal := h2comp.2.1
        rw [← hcomap]
        exact h2.comap Φ.toMonoidHom
      have hXcomp : IsComponent (X'.subgroupOf (fixSub (conjAut K' x hfix))) :=
        ⟨hqX, hsubX⟩
      obtain ⟨σ', P, hprop, he⟩ :=
        exists_properFixedComp_quotient (K := ↥K') (σ := conjAut K' x hfix)
          hK'q hσ hXF hXcomp hX'top
      obtain ⟨e⟩ := he
      exact Or.inr ⟨σ', P, hprop,
        ⟨(CFSG.ComponentClassification.Sol78.centerQuotCongr
          (Subgroup.subgroupOfEquivOfLe hKK'le).symm).trans e⟩⟩
  ·
    have hK'q_range : IsQuasisimple ↥φ.range := by
      rw [← hKrange]
      exact hKq
    obtain ⟨e⟩ := centralQuot_equiv_of_surjective hK'q hK'q_range φ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective φ) (by
        rw [MonoidHom.ker_rangeRestrict]
        exact hker)
    exact Or.inl ⟨(CFSG.ComponentClassification.Sol78.centerQuotCongr
      (MulEquiv.subgroupCongr hKrange)).trans e.symm⟩

end CFSG.OddStandard.SmallF3.HypA2
