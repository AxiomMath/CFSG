module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.Small
public import CFSG.ClassicalInvolution.Q3.TA3SmallBase
public import CFSG.ClassicalInvolution.Q3.TL4Conn274

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Generic CFSG.Blueprint

structure SmallLeavesR (r : ℕ) : Prop where
  m11 : SmallLeafR r SmallM11
  m12 : SmallLeafR r SmallM12
  l2 : SmallLeafR r SmallL2
  l3 : SmallLeafR r SmallL3
  u3 : SmallLeafR r SmallU3
  g2 : SmallLeafR r SmallG2
  d4 : SmallLeafR r SmallD4
  psp4 : SmallLeafR r SmallPSp4
  twistedG2 : SmallLeafR r SmallTwistedG2
  l4 : SmallLeafR r SmallL4
  u4 : SmallLeafR r SmallU4
  l5 : SmallLeafR r SmallL5
  u5 : SmallLeafR r SmallU5

@[expose] def NoCentralTwinR (r : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t →
    TightClsR r Y R S t → ¬ TightInO2 t → TightFStarQuasisimple Y →
      TwoSubgroupsFourGenerated (genFittingFStar Y) →
      ∀ c ∈ fstarCenter Y, c ≠ 1 → ∀ y : Y, y * t * y⁻¹ ≠ t * c

section Descent

variable {r : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

theorem twistQ_clsR (hd : TightDatum R S t) (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    (htN : t ∉ N) (hc : TightClsR r Y R S t) :
    TightClsR r (Y ⧸ N) (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S)
      (QuotientGroup.mk' N t) := by
  have hRN := TwistQ.inf_eq_bot hd hN2 htN
  obtain ⟨⟨e⟩, hgen, hO⟩ := hc
  refine ⟨⟨(TwistQ.sylowMapEquiv hRN S).symm.trans e⟩, ?_, TwistQ.oddFree hNc hN2 hO⟩
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  show (⨆ g : Y ⧸ N, conjSub g (tightCore (R.map (QuotientGroup.mk' N)))) = ⊤
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← hgen',
    Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [TwistQ.conjSub_map, TwistQ.tightCore_map hRN]
  exact le_iSup (fun g : Y ⧸ N => conjSub g (tightCore (R.map (QuotientGroup.mk' N))))
    (QuotientGroup.mk' N g)

end Descent

section Assembly

variable {r : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem fstarCenter_le_center_R (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hE2 : ¬ TightInO2 t) : fstarCenter Y ≤ Subgroup.center Y :=
  TL4.center_genFittingFStar_le_of_selfGen hd hc.2.1 hc.2.2 hE2

theorem isPGroup_fstarCenter_R (hc : TightClsR r Y R S t) : IsPGroup 2 ↥(fstarCenter Y) :=
  (isPGroup_two_genFittingFitting hc.2.2).to_le (fstarCenter_le_fitting Y)

theorem not_mem_fstarCenter_R (hc : TightClsR r Y R S t) (hE2 : ¬ TightInO2 t) :
    t ∉ fstarCenter Y :=
  fun h => hE2 ⟨fstarCenter Y, inferInstance, isPGroup_fstarCenter_R hc, h⟩

theorem tightEdgeless_of_quotient (hd : TightDatum R S t) (hc : TightClsR r Y R S t)
    (hE2 : ¬ TightInO2 t)
    (hnt : ∀ y : Y, ∀ n ∈ fstarCenter Y, y * t * y⁻¹ = t * n → n = 1)
    (h : TightEdgeless (R.map (QuotientGroup.mk' (fstarCenter Y)))) : TightEdgeless R := by
  by_contra hne
  exact TwistQ.not_edgeless_map hd (fstarCenter_le_center_R hd hc hE2) (isPGroup_fstarCenter_R hc)
    (not_mem_fstarCenter_R hc hE2) hnt hne h

theorem smallSimpleR_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeavesR r) (Y : Type)
    [Group Y] [Finite Y] [IsSimpleGroup (genFittingFStar Y)]
    (hnab : ∃ a b : genFittingFStar Y, a * b ≠ b * a)
    (hP : TwoSubgroupsFourGenerated (genFittingFStar Y)) (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (hd : TightDatum R S t) (hc : TightClsR r Y R S t) (hE2 : ¬ TightInO2 t) :
    TightEdgeless R := by
  rcases smallList hGH _ hnab hP with
    (h | h | h | h | h | h | h | h | h | h | h | h | h) | hex
  · exact hL.g2 Y hnab hP h R S t hd hc hE2
  · exact hL.d4 Y hnab hP h R S t hd hc hE2
  · exact hL.psp4 Y hnab hP h R S t hd hc hE2
  · exact hL.twistedG2 Y hnab hP h R S t hd hc hE2
  · exact hL.l4 Y hnab hP h R S t hd hc hE2
  · exact hL.u4 Y hnab hP h R S t hd hc hE2
  · exact hL.l5 Y hnab hP h R S t hd hc hE2
  · exact hL.u5 Y hnab hP h R S t hd hc hE2
  · exact hL.m12 Y hnab hP h R S t hd hc hE2
  · exact hL.l2 Y hnab hP h R S t hd hc hE2
  · exact hL.l3 Y hnab hP h R S t hd hc hE2
  · exact hL.u3 Y hnab hP h R S t hd hc hE2
  · exact hL.m11 Y hnab hP h R S t hd hc hE2
  · exfalso
    have := genFittingFStar_normal Y
    obtain ⟨r', hr, ⟨eS⟩⟩ := hd.quat
    exact (Nobq.smallNoDatum_of_dvd Nobq.card_outer_Ly_dvd_two).noDatum _ hex Y
      (genFittingFStar Y) ⟨MulEquiv.refl _⟩ (Nobq.centralizer_genFittingFStar_eq_bot hnab) R S r'
      hr ⟨eS⟩ t hd.mem hd.order hd.cent hd.normal

theorem tightSmallBaseR_of_leaves (hGH : GH74SectionalModels) (hL : SmallLeavesR r)
    (hT : NoCentralTwinR r) : TightSmallBaseR r := by
  intro Y _ _ R S t hd hc hE2 hQ hsmall
  by_cases htw : ∃ c ∈ fstarCenter Y, c ≠ 1 ∧ ∃ y : Y, y * t * y⁻¹ = t * c
  · obtain ⟨c, hcN, hc1, y, hy⟩ := htw
    exact absurd hy (hT Y R S t hd hc hE2 hQ hsmall c hcN hc1 y)
  have hnt : ∀ y : Y, ∀ n ∈ fstarCenter Y, y * t * y⁻¹ = t * n → n = 1 := by
    intro y n hn hy
    by_contra h1
    exact htw ⟨n, hn, h1, y, hy⟩
  have hNc := fstarCenter_le_center_R hd hc hE2
  have hN2 := isPGroup_fstarCenter_R hc
  have htN := not_mem_fstarCenter_R hc hE2
  have hF := genFittingFStar_quotient_fstarCenter Y hQ hNc
  have := isSimpleGroup_fstarBar Y hQ
  have : IsSimpleGroup ↥(genFittingFStar (Y ⧸ fstarCenter Y)) :=
    (MulEquiv.subgroupCongr hF).isSimpleGroup
  have hnab : ∃ a b : genFittingFStar (Y ⧸ fstarCenter Y), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_ne_comm_fstarBar Y hQ
    refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h => ?_⟩
    exact hab (by simpa using congrArg (MulEquiv.subgroupCongr hF) h)
  have hP : TwoSubgroupsFourGenerated (genFittingFStar (Y ⧸ fstarCenter Y)) :=
    twoSubgroupsFourGenerated_of_mulEquiv (MulEquiv.subgroupCongr hF).symm
      (twoSubgroupsFourGenerated_fstarBar Y hsmall)
  exact tightEdgeless_of_quotient hd hc hE2 hnt
    (smallSimpleR_of_leaves hGH hL (Y ⧸ fstarCenter Y) hnab hP _ _ _
      (TwistQ.datum hd hN2 htN hnt) (twistQ_clsR hd hNc hN2 htN hc)
      fun h => hE2 (TwistQ.inO2_of hN2 h))

end Assembly

end CFSG.CGT.PushingUpLit.SolKNA.R4
