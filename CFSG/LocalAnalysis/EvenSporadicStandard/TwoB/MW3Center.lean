module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Equiv
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Co1Class
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.MW3Group
public import CFSG.Monster.Existence.BabyW3Griess

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB.MW3

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Census CFSG.Monster.Spin CFSG.Blueprint CFSG.Monster.GMS
  CFSG.Monster.Existence.Co1Bridge CFSG.Sporadic.Co1.Module.Odd CFSG.Monster.ScalarKernel


theorem natCard_centralizer_inf_rhoQvis :
    Nat.card ↥(rhoQvis ⊓ Subgroup.centralizer ({cosetRep 1} : Set Gvis)) = 2 ^ 17 := by
  have h := ncard_conj_mul_natCard_inf_centralizer rhoQvis (cosetRep 1)
  have h1 : {u : Gvis | ∃ g ∈ rhoQvis, u = g⁻¹ * cosetRep 1 * g}.ncard = 256 :=
    ncard_qmatClass_h1
  rw [h1, natCard_rhoQvis] at h
  omega

theorem natCard_map_piVis_centralizer :
    Nat.card ((Subgroup.centralizer ({cosetRep 1} : Set Gvis)).map piVis) =
      2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have h := natCard_eq_natCard_map_mul piVis (Subgroup.centralizer ({cosetRep 1} : Set Gvis))
  rw [ker_piVis, inf_comm, natCard_centralizer_inf_rhoQvis, natCard_centralizer_cosetRep_one] at h
  omega

theorem map_piVis_centralizer_eq :
    (Subgroup.centralizer ({cosetRep 1} : Set Gvis)).map piVis =
      Subgroup.centralizer ({piVis (cosetRep 1)} :
        Set (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ) := by
  refine eq_of_le_of_natCard_le ?_ ?_ ?_
  · rintro _ ⟨c, hc, rfl⟩
    have hc' := Subgroup.mem_centralizer_singleton_iff.1 hc
    exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hc'])
  · rw [natCard_centralizer_piVis_cosetRep_one]
    norm_num
  · rw [natCard_centralizer_piVis_cosetRep_one, natCard_map_piVis_centralizer]

theorem eq_one_or_eq_kappa {ζ : (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ}
    (hζ : ∀ d ∈ Subgroup.centralizer ({piVis (cosetRep 1)} :
      Set (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ), ζ * d = d * ζ) :
    ζ = 1 ∨ ζ = piVis (cosetRep 1) := by
  let e : (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ ≃* NativeSporadic.Co1 :=
    OLqOpEquivHvis.trans co1EquivHvis.symm
  have heκ : e (piVis (cosetRep 1)) = rCo1 := by
    change co1EquivHvis.symm (OLqOpEquivHvis (piVis (cosetRep 1))) = co1EquivHvis.symm uHvis
    rw [OLqOpEquivHvis_piVis_cosetRep_one]
  have key : e ζ = 1 ∨ e ζ = rCo1 := by
    refine eq_one_or_eq_of_commute_of_fix orderOf_rCo1 ncard_fix_rCo1 fun d hd => ?_
    have hd' : e.symm d ∈ Subgroup.centralizer ({piVis (cosetRep 1)} :
        Set (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hd ⊢
      apply e.injective
      rw [map_mul, map_mul, heκ, MulEquiv.apply_symm_apply]
      exact hd
    have h := congrArg e (hζ _ hd')
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  rcases key with h | h
  · exact Or.inl (e.injective (h.trans (map_one e).symm))
  · exact Or.inr (e.injective (h.trans heκ.symm))

theorem mem_zpowers_of_commute {z : Gvis} (hz : z ∈ rhoQvis)
    (hc : ∀ c ∈ Subgroup.centralizer ({cosetRep 1} : Set Gvis), c * z = z * c) :
    z ∈ Subgroup.zpowers (rhoGvis zQ) := by
  have hq : ∀ s ∈ Subgroup.centralizer ({cosetRep 1} : Set Gvis),
      conjVis s (QuotientGroup.mk (⟨z, hz⟩ : rhoQvis)) = QuotientGroup.mk (⟨z, hz⟩ : rhoQvis) := by
    intro s hs
    rw [conjVis_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show s * z * s⁻¹ = z
    rw [hc s hs, mul_inv_cancel_right]
  have hzR := mem_zRho_of_fixed _ natCard_map_piVis_centralizer hq
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzR
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have h1 : ((rhoN zQ : rhoQvis) : Gvis) ^ k = z := by
    rw [← Subgroup.coe_zpow]
    exact congrArg Subtype.val hk
  exact h1

theorem center_centralizer_cosetRep_one :
    (Subgroup.center ↥(Subgroup.centralizer ({cosetRep 1} : Set Gvis))).map
        (Subgroup.centralizer ({cosetRep 1} : Set Gvis)).subtype =
      Subgroup.zpowers (rhoGvis zQ) ⊔ Subgroup.zpowers (cosetRep 1) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨c, hcZ, rfl⟩ := Subgroup.mem_map.1 hz
    show (c : Gvis) ∈ _
    set w : Gvis := (c : Gvis) with hw
    have hcomm : ∀ d ∈ Subgroup.centralizer ({cosetRep 1} : Set Gvis), d * w = w * d := by
      intro d hd
      have := Subgroup.mem_center_iff.1 hcZ ⟨d, hd⟩
      exact congrArg Subtype.val this
    have hh : cosetRep 1 ∈ Subgroup.centralizer ({cosetRep 1} : Set Gvis) :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    have hπ : piVis w = 1 ∨ piVis w = piVis (cosetRep 1) := by
      refine eq_one_or_eq_kappa fun d hd => ?_
      rw [← map_piVis_centralizer_eq] at hd
      obtain ⟨d', hd', rfl⟩ := hd
      rw [← map_mul, ← map_mul, (hcomm d' hd').symm]
    rcases hπ with h | h
    · have hwQ : w ∈ rhoQvis := by
        have h0 : w ∈ piVis.ker := h
        rwa [ker_piVis] at h0
      exact Subgroup.mem_sup_left (mem_zpowers_of_commute hwQ fun d hd => (hcomm d hd))
    · have hwQ : w * cosetRep 1 ∈ rhoQvis := by
        have h0 : w * cosetRep 1 ∈ piVis.ker := by
          rw [MonoidHom.mem_ker, map_mul, h, ← map_mul, cosetRep_one_mul_self, map_one]
        rwa [ker_piVis] at h0
      have hx : w * cosetRep 1 ∈ Subgroup.zpowers (rhoGvis zQ) := by
        refine mem_zpowers_of_commute hwQ fun d hd => ?_
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 hd
        calc d * (w * cosetRep 1) = (d * w) * cosetRep 1 := by rw [mul_assoc]
          _ = (w * d) * cosetRep 1 := by rw [hcomm d hd]
          _ = w * (d * cosetRep 1) := by rw [mul_assoc]
          _ = w * (cosetRep 1 * d) := by rw [h1]
          _ = (w * cosetRep 1) * d := by rw [mul_assoc]
      have hw' : w = (w * cosetRep 1) * cosetRep 1 := by
        rw [mul_assoc, cosetRep_one_mul_self, mul_one]
      rw [hw']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact ⟨⟨rhoGvis zQ, Subgroup.mem_centralizer_singleton_iff.2
        (rhoGvis_zQ_comm (cosetRep 1)).symm⟩, Subgroup.mem_center_iff.2 fun g =>
          Subtype.ext (rhoGvis_zQ_comm g), rfl⟩
    · exact ⟨⟨cosetRep 1, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩,
        Subgroup.mem_center_iff.2 fun g =>
          Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2), rfl⟩

end CFSG.EvenSporadicStandard.TwoB.MW3
