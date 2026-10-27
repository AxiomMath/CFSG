module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZBridge
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZMain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineNineSym
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenEmbedded
import CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.CStarGenThree
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

@[expose] def O991Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → (sigmaM G M).Nonempty →
      3 ∉ sigmaM G M →
      ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 →
        rankThreeGamma 1 3 E ≤ M → E ∈ uniqueSet M

theorem o991Gen_of_inputs (h7 : NineSevenTwoInputGen) (h6 : NineSixInputGen)
    (h35 : ThreeFiveA11InputGen) (hk : ZKFacts) : O991Gen := by
  intro G _ _ hC M hM hσ h3 E hEM hE hEc hΓ
  by_contra hU
  have hCG : CStarSettingGen G M := ⟨hC, hM, hσ⟩
  have hEc' : Nat.card E = 3 ^ 2 := by rw [hEc]; norm_num
  obtain ⟨g, Q, hn, hH2, hcore⟩ := exists_nineSettingGen_of_not_mem_uniqueSet hCG Nat.prime_three
    (by norm_num) hEM hE hEc' hΓ hU
  let H : Subgroup G := M.map (MulAut.conj g).toMonoidHom
  have hnH : NineSettingGen G M 3 Q H E 2 := hn
  have hH2' : H ∈ H2Fam M Q := hH2
  have hcore' : pCoreOf 2 H ≠ pCoreOf 2 (H ⊓ M) := hcore
  have hcomp : ZComponentData (↥H ⧸ CFSG.pPrimeCore 3 ↥H) (barInf 3 M H) :=
    hnH.zComponentDataGen h7 h6 h35 hH2' h3 hcore'
  obtain ⟨L, hL, -, -⟩ := hcomp.exists_shape
  have hLns : ¬ Group.IsSolvable ↥L := by
    intro hLsolv
    haveI := hLsolv
    obtain ⟨-, hsimple, a, b, hab⟩ := hL.1
    haveI := hsimple
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance a b)
  have hHns : ¬ Group.IsSolvable ↥H := by
    intro hHsolv
    haveI := hHsolv
    have hLsolv : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := L.subtype) L.subtype_injective
    exact hLns hLsolv
  have hMns : ¬ Group.IsSolvable ↥M := by
    intro hMsolv
    haveI := hMsolv
    let e := Subgroup.equivMapOfInjective M (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    have hHsolv : Group.IsSolvable ↥H :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.toEquiv.surjective
    exact hHns hHsolv
  obtain ⟨d, hd⟩ := hσ
  have hd3 : d ≠ 3 := fun hd3 => h3 (hd3 ▸ hd)
  have hstrong := hC.isStronglyPEmbedded_of_not_isSolvable hM hd hd3 hMns
  obtain ⟨W, hcfg⟩ := hnH.dEmbConfig rfl hd h3 hstrong
  exact DEmbConfig.false hcfg hcomp hk

theorem o991_of_o991Gen (h : O991Gen) : O991 := by
  intro G _ _ hS hUC M hM hwit hstrong h3 E hEM hE hEc hΓ
  obtain ⟨p, hp, -⟩ := hwit
  exact h G (CFSG.LocalAnalysis.AGL81TheoremCD.RankThree.cStarGen_of_rankThreeUC hS hUC) M hM
    ⟨p, hp⟩ h3 E hEM hE hEc hΓ

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
