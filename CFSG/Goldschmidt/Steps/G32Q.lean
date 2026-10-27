module

public import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.Steps.G32QBasic
import CFSG.Goldschmidt.Steps.G32QSz8
import CFSG.Goldschmidt.Steps.G3NewPair
import CFSG.Goldschmidt.Steps.GoldTypeBender
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.Walter.Bender1970.S2.Inner
public import Certificates.Certificate43
public import Certificates.Certificate113
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG
public import CFSG.Goldschmidt.StatementsG2
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.StronglyEmbedded
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)
open scoped MatrixGroups

theorem G32Q : S_G32Q := by
  intro L _ _ hL hI hZ2 A hA T hAT a haA haZ
  have hcl := G32Q.stronglyClosed_of_isSStarIn hA T hAT
  have hAab : IsMulCommutative A := hA.2.1
  have hNA := G32Q.normalizer_le_normalizer hAT hcl
  have haC : A ≤ Subgroup.centralizer ({a} : Set L) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  by_cases hZ : Subgroup.center L = ⊥
  ·
    have : IsSimpleGroup L :=
      (CFSG.QuasithinUnique.RankOneRecog.mulEquivOfCenterEqBot hZ
        (MulEquiv.refl _)).isSimpleGroup_congr.mpr hL.2
    obtain ⟨hX, -⟩ := G3a.typeI_models hI
    obtain ⟨D, h⟩ := G3a.exists_borelSetup hX T
    have hAZ := G32Q.le_sylowCenter h hX hAT hAab (h.le.trans hNA)
    have hTa : (T : Subgroup L) ≤ Subgroup.centralizer ({a} : Set L) := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr ((mem_sylowCenter.mp (hAZ haA)).2 t ht)
    refine ⟨fun M hM hMtop => h.le_normalizer_of_le (hTa.trans hM) hMtop, ?_⟩
    rw [inf_eq_left.mpr hTa]
    exact fun n hn => h.cent hn.2
  have : Group.IsPerfect L := ⟨hL.1⟩
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2
  have hcases : (∃ n : ℕ, 3 ≤ n ∧ Nonempty (L ⧸ Subgroup.center L ≃* PSL(2, GaloisField 2 n))) ∨
      Nonempty (L ⧸ Subgroup.center L ≃* Sz 1) := by
    rcases hI with h1 | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact Or.inl h1
    · rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
      · exact Or.inr ⟨e⟩
      · exact absurd (NewPair.suzuki_center_eq_bot hZ2 hn2 e) hZ
    · exact absurd (CFSG.QuasithinUnique.RankOneRecog.unitary_center_eq_bot hZ2 hn e) hZ
  have hX : fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
    rcases hcases with ⟨n, hn, he⟩ | he
    · exact Or.inl ⟨n, by omega, he⟩
    · exact Or.inr (Or.inr ⟨1, le_rfl, he⟩)
  set π := QuotientGroup.mk' (Subgroup.center L)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.center L := QuotientGroup.ker_mk' _
  have hZT : Subgroup.center L ≤ T := hZ2.le_sylow_of_normal T
  set Tb : Sylow 2 (L ⧸ Subgroup.center L) := T.mapSurjective hπs
  have hTb : (Tb : Subgroup (L ⧸ Subgroup.center L)) = (T : Subgroup L).map π :=
    Sylow.coe_mapSurjective hπs T
  have hcomapT : (Tb : Subgroup (L ⧸ Subgroup.center L)).comap π = T := by
    rw [hTb]
    exact Subgroup.comap_map_eq_self (by rw [hker]; exact hZT)
  have hcomapN : (Subgroup.normalizer
      ((Tb : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L))).comap π =
      Subgroup.normalizer ((T : Subgroup L) : Set L) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective _ hπs, hcomapT]
  obtain ⟨D, h⟩ := G3a.exists_borelSetup hX Tb
  have hAbT : A.map π ≤ Tb := by
    rw [hTb]
    exact Subgroup.map_mono hAT
  have hDA : D ≤ Subgroup.normalizer ((A.map π : Subgroup (L ⧸ Subgroup.center L)) :
      Set (L ⧸ Subgroup.center L)) := by
    intro d hd
    obtain ⟨g, rfl⟩ := hπs d
    have hg : g ∈ Subgroup.normalizer ((T : Subgroup L) : Set L) := by
      rw [← hcomapN]
      exact h.le hd
    exact Subgroup.le_normalizer_map π ⟨g, hNA hg, rfl⟩
  have hA1 : A.map π ≠ ⊥ := by
    intro hbot
    have hmem : π a ∈ A.map π := ⟨a, haA, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact haZ ((QuotientGroup.eq_one_iff a).mp hmem)
  have hAZ : A.map π = sylowCenter (Tb : Subgroup (L ⧸ Subgroup.center L)) :=
    G32Q.eq_sylowCenter h hX hAbT inferInstance hDA hA1
  have hDZ : Nat.card D = Nat.card (sylowCenter (Tb : Subgroup (L ⧸ Subgroup.center L))) - 1 := by
    rcases hcases with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · obtain ⟨-, hDc, hZc⟩ := h.orders_psl2 (by omega) e
      rw [hDc, hZc]
    · obtain ⟨hZc, -, hDc⟩ := h.orders_sz le_rfl e
      rw [hDc, hZc]
  have hkerD := G32Q.inf_centralizer_sylowCenter_eq_bot h hDZ
  refine ⟨fun M hM hMtop => ?_, fun n hn => ?_⟩
  ·
    have hMb : M.map π ≠ ⊤ := by
      intro htop
      apply hMtop
      refine CFSG.Walter.eq_top_of_sup_center_eq_top hL.1 ?_
      rw [← hker, ← Subgroup.comap_map_eq, htop, Subgroup.comap_top]
    have hZM : sylowCenter (Tb : Subgroup (L ⧸ Subgroup.center L)) ≤ M.map π := by
      rw [← hAZ]
      exact Subgroup.map_mono (haC.trans hM)
    have hMN : M.map π ≤ Subgroup.normalizer
        ((Tb : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)) := by
      rcases hcases with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
      · have hab := GoldType.isMulCommutative_of_psl2_even (by omega) e Tb
        have hTZ : (Tb : Subgroup (L ⧸ Subgroup.center L)) ≤
            sylowCenter (Tb : Subgroup (L ⧸ Subgroup.center L)) := fun x hx =>
          mem_sylowCenter.mpr ⟨hx, fun t ht =>
            congrArg Subtype.val (hab.is_comm.comm ⟨t, ht⟩ ⟨x, hx⟩)⟩
        exact h.le_normalizer_of_le (hTZ.trans hZM) hMb
      · have hcard : Nat.card (L ⧸ Subgroup.center L) = 29120 := by
          rw [Nat.card_congr e.toEquiv,
            CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz]
          norm_num
        exact G32Q.le_normalizer_of_sylowCenter_le h hcard hMb hZM
    intro m hm
    rw [← hcomapN]
    exact hMN ⟨m, hm, rfl⟩
  ·
    have hn1 : π n ∈ Subgroup.normalizer
        ((Tb : Subgroup (L ⧸ Subgroup.center L)) : Set (L ⧸ Subgroup.center L)) := by
      have h1 := hn.1
      rw [← hcomapN] at h1
      exact h1
    have hn2 : ∀ z ∈ sylowCenter (Tb : Subgroup (L ⧸ Subgroup.center L)), π n * z = z * π n := by
      rw [← hAZ]
      rintro _ ⟨x, hx, rfl⟩
      have hxC : x ∈ (T : Subgroup L) ⊓ Subgroup.centralizer ({a} : Set L) := ⟨hAT hx, haC hx⟩
      have hxn : x * n = n * x := Subgroup.mem_centralizer_iff.mp hn.2 x hxC
      rw [← map_mul, ← map_mul, hxn]
    have hnT := G32Q.mem_of_commute_sylowCenter h hkerD hn1 hn2
    rw [← hcomapT]
    exact hnT

end CFSG.Goldschmidt
