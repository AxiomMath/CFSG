module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmQ3LBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmPair
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Core
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallM2

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TA3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem leaf_d43 {n : ℕ} : TwinLeafS n fun F _ => LieModel F .trialityD4 0 3 1 :=
  TwinLeafS.of_no fun Y _ _ R S t h _ hm => by
    haveI := h.core.simple
    haveI hTn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
    have hC : Subgroup.centralizer ((genFittingFStar Y : Subgroup Y) : Set Y) = ⊥ :=
      Nobq.centralizer_genFittingFStar_eq_bot h.core.nonab
    obtain ⟨htN, s, hsK, hsN, hs4⟩ := exists_u1_of_outTwoCyclic h hC
      (outTwoCyclic_trialityD4 (by decide)
        (Q5G2D4.chevalleyExceptionalModel_of_lieModel hm (by decide) (by decide) (by decide)))
    have ht : orderOf (⟨t, htN⟩ : genFittingFStar Y) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h.core.datum.order
    obtain ⟨F₁, F₂, _, _, _, _, Sh, hc₁, hc₂, hz⟩ :=
      GH74.GLS.IVK.GHInv.exists_shape_D4 Nat.prime_three (by decide) hm _ ht
    have hF₂ : Nat.card F₂ = 3 := by rw [hc₂, pow_one]
    have hF₁ : Nat.card F₁ = 27 := by rw [hc₁]; norm_num
    have h3 : (3 : F₂) = 0 := LieType.HighestRoot.three_eq_zero hF₂
    have hzt : ((Sh.z : genFittingFStar Y) : Y) = t := by rw [hz]
    set P := Q3Sh.toCentShape htN Sh hzt h3 (two_ne_zero_of_three h3) with hP
    have hAq : CFSG.IsQuasisimple ↥P.A :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv P.eA.symm
        (CFSG.GH74.GLS.IVK.Lifted.isQuasisimple_sl2' (by rw [hF₁]; norm_num))
    have hAD : (P.A.subgroupOf (genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff P.le_A]
      intro a c ha hc
      exact P.normal_A c hc a ha
    have hDC : CFSG.Open.IsSubnormal (genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y))
        (Subgroup.centralizer ({t} : Set Y)) := by
      have := isSubnormal_inf_normal (Subgroup.centralizer ({t} : Set Y)) (genFittingFStar Y)
      rwa [inf_comm] at this
    have hAs : CFSG.Open.IsSubnormal P.A (Subgroup.centralizer ({t} : Set Y)) :=
      CFSG.Open.IsSubnormal.step P.le_A hAD hDC
    obtain ⟨g, hgc, hne, -, hz'⟩ := exists_twin h
    have hKsolv := isSolvable_core h
    have hcK := commute_of_solvable_subnormal hAs hAq (isSubnormal_core h) hKsolv
    have hcK' := commute_of_solvable_subnormal hAs hAq
      (isSubnormal_of_hypOmegaGen h.core.hyp ⟨g, rfl⟩ hz') (isSolvable_conjSub g hKsolv)
    have hsC : s ∈ Subgroup.centralizer ({t} : Set Y) :=
      h.core.datum.cent (tightCore_le R hsK)
    have hs'D : g * s * g⁻¹ ∈ genFittingFStar Y ⊓ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_inf.mpr ⟨hTn.conj_mem s hsN g,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgc hsC) (Subgroup.inv_mem _ hgc)⟩
    have hsB : s ∈ P.B :=
      P.cent_A s (Subgroup.mem_inf.mpr ⟨hsN, hsC⟩) fun a ha => (hcK a ha s hsK).symm
    have hs'B : g * s * g⁻¹ ∈ P.B :=
      P.cent_A _ hs'D fun a ha => (hcK' a ha _ (conj_mem_conjSub hsK)).symm
    exact Q3L.false_of_twin_hom h (θ := P.B.subtype) Subtype.val_injective
      (Q3L.sl3_q8 hF₂ P.eB) hgc hne hsK hs4 ⟨⟨s, hsB⟩, rfl⟩ ⟨⟨_, hs'B⟩, rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small
