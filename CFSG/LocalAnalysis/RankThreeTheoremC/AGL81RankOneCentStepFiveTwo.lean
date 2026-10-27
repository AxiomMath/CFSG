module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFour
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneElevenEleven
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
import Certificates.Kernel.Sporadic.Fi22.C2068
import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem hasNormalPComplement_of_act (hp2 : p ≠ 2) (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1)
    {b : G} (hbC : b ∈ C) (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p) {Y : Subgroup G}
    (hYC : Y ≤ C) (h : CFSG.HasNormalPComplement p ↥((Y.subgroupOf C).map φ)) :
    CFSG.HasNormalPComplement p ↥Y := by
  have hp : p.Prime := Fact.out
  set X := d1PlusCore p C K with hX
  have hXC : X ≤ C := Subgroup.map_subtype_le _
  have hbX : b ∈ X := mem_d1PlusCore_of_central hbC hb K
  set g : ↥Y →* MulAut ↥K := MonoidHom.comp φ (Subgroup.inclusion hYC) with hg
  have hrange : g.range = (Y.subgroupOf C).map φ := by
    ext σ
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hYC y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, Subgroup.mem_subgroupOf.mp hc⟩, rfl⟩
  have hq : CFSG.HasNormalPComplement p (↥Y ⧸ g.ker) :=
    hasNormalPComplement_of_equiv p
      ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hrange)).symm h
  have hkerX : ∀ y : ↥Y, y ∈ g.ker → (y : G) ∈ X := by
    intro y hy
    exact (mem_d1PlusCore_iff_mem_ker (Subgroup.inclusion hYC y)).mpr (MonoidHom.mem_ker.mpr
      (MonoidHom.mem_ker.mp hy))
  set f : ↥g.ker →* G := Y.subtype.comp g.ker.subtype with hf
  have hfi : Function.Injective f := Y.subtype_injective.comp g.ker.subtype_injective
  refine CFSG.LocalAnalysis.RankThreeTheoremC.hasNormalPComplement_of_cyclic_sylow_central_quotient
    g.ker (fun P => ?_) (fun x hx hxo => ?_) hq
  ·
    have hRX : (P : Subgroup ↥g.ker).map f ≤ X := by
      rintro _ ⟨x, -, rfl⟩
      exact hkerX x x.2
    have hRc : IsCyclic ↥((P : Subgroup ↥g.ker).map f) :=
      RankOne.isCyclic_of_le_of_pRank_le_one hp2 hRX (P.2.map f) hXr
    have e := (P : Subgroup ↥g.ker).equivMapOfInjective f hfi
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  ·
    have hxX := hkerX x hx
    have hxo' : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hxo]
    have hxb := mem_zpowers_of_pRank_le_one hp hXr hbX hbo (fun y hy => hb y (hXC hy)) hxX hxo'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxb
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    have hc : Commute b (y : G) := hb y (hYC y.2)
    have := (hc.zpow_left k).eq
    rw [hk] at this
    exact this.symm

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
