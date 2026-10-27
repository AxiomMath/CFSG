module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import Certificates.Certificate3119
public import Certificates.Certificate7124
public import CFSG.Sporadic.J1.Setup
public import CFSG.Quasithin.Background.A312SporJ1
import CFSG.Quasithin.H13.NQCatA314J1
import CFSG.Sporadic.Bridge.J1
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

theorem index_modEq_one_of_normalizer_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) {H : Subgroup G}
    (hH : normalizer ((P : Subgroup G) : Set G) ≤ H) : H.index ≡ 1 [MOD p] := by
  have hPH : (P : Subgroup G) ≤ H := le_normalizer.trans hH
  let P' : Sylow p H := P.subtype hPH
  have hG : Nat.card (Sylow p G) = (normalizer ((P : Subgroup G) : Set G)).index :=
    P.card_eq_index_normalizer
  have hH' : Nat.card (Sylow p H) = (normalizer ((P' : Subgroup H) : Set H)).index :=
    P'.card_eq_index_normalizer
  have hN : normalizer ((P' : Subgroup H) : Set H) =
      (normalizer ((P : Subgroup G) : Set G)).subgroupOf H :=
    (Subgroup.subgroupOf_normalizer_eq hPH).symm
  have hrel := Subgroup.relIndex_mul_index hH
  have h1 : Nat.card (Sylow p G) = Nat.card (Sylow p H) * H.index := by
    rw [hG, hH', hN]
    exact hrel.symm
  have hm1 : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  have hm2 : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p H
  have h3 : Nat.card (Sylow p H) * H.index ≡ 1 * H.index [MOD p] := hm2.mul_right _
  rw [one_mul, ← h1] at h3
  exact h3.symm.trans hm1

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.E2P.SporB
  CFSG.Quasithin.A312S in
theorem j1_overgroup_index
    (Z : Subgroup ↥CFSG.Sporadic.J1.J) (hSZ : j1S ≤ Z) :
    Z.index = 1 ∨ ¬ Z.index ≡ 1 [MOD 7] := by
  obtain ⟨j, hj, hZ⟩ := j1_all Z hSZ
  have hcard : Nat.card ↥CFSG.Sporadic.J1.J = 175560 := CFSG.Sporadic.J1.card_J
  have hidx := Subgroup.card_mul_index Z
  rw [hcard] at hidx
  by_cases hj17 : j < 17
  · right
    have hZY : Z = j1Y j := by
      rw [hZ]
      exact list_member (L := #[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21]) hj17
    have hc := j1_Y_card hj17
    rw [← hZY] at hc
    rw [hc] at hidx
    unfold Nat.ModEq
    interval_cases j <;> simp at hidx <;> omega
  · left
    have h17 : j = 17 := by
      have : j ≤ 17 := hj
      omega
    have hZt : Z = ⊤ := by
      rw [hZ, h17]
      unfold memberOrTop
      rw [ite_eq_right (by simp)]
    rw [hZt]
    exact Subgroup.index_top

theorem kFactJ1L27_holds :
    KFactJ1L27 := by
  intro A _ _ L T z hL hT hzL hz7 hzT J hJz hJT
  obtain ⟨e⟩ := hL
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  let φ : ↥L ≃* ↥CFSG.Sporadic.J1.J := (e.trans f.symm).trans CFSG.Sporadic.J1.nativeEquiv
  have hLc : Nat.card ↥L = 175560 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.Sporadic.J1.card_J
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPzL : zpowers z ≤ L := Subgroup.zpowers_le.mpr hzL
  let P0 : Subgroup ↥L := (zpowers z).subgroupOf L
  have hP0card : Nat.card P0 = 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPzL).toEquiv, Nat.card_zpowers, hz7]
  have hP0p : IsPGroup 7 P0 := IsPGroup.of_card (n := 1) (by rw [hP0card]; norm_num)
  have hP0idx : ¬ 7 ∣ P0.index := by
    have h := Subgroup.card_mul_index P0
    rw [hP0card, hLc] at h
    have : P0.index = 25080 := by omega
    rw [this]
    norm_num
  let P : Sylow 7 ↥L := hP0p.toSylow hP0idx
  let H : Subgroup ↥L := J.subgroupOf L
  have hH : normalizer ((P : Subgroup ↥L) : Set ↥L) ≤ H := by
    have hN : normalizer ((P : Subgroup ↥L) : Set ↥L) =
        (normalizer ((zpowers z : Subgroup A) : Set A)).subgroupOf L :=
      (Subgroup.subgroupOf_normalizer_eq hPzL).symm
    rw [hN]
    intro g hg
    exact hJz ⟨hg, g.2⟩
  have hmod : H.index ≡ 1 [MOD 7] := index_modEq_one_of_normalizer_le P hH
  have hT2 := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (T.subgroupOf L) ⊤ :=
    ⟨le_top, hT2.2.1.comap_subtype, by
      have h : ((T.subgroupOf L).subgroupOf ⊤).index = T.relIndex L := by
        change (T.subgroupOf L).relIndex ⊤ = _
        rw [Subgroup.relIndex_top_right]
        rfl
      rw [h]
      exact hT2.2.2⟩
  have hTH : T.subgroupOf L ≤ H := by
    intro g hg
    exact hJT ⟨Subgroup.le_normalizer hg, g.2⟩
  obtain ⟨ψ, hψ⟩ := CFSG.Quasithin.H13.NQCat.A314D.exists_mulEquiv_map_eq φ
    CFSG.Quasithin.E2P.SporB.j1_sylow hT'
  have hSZ : CFSG.Quasithin.E2P.SporB.j1S ≤ H.map ψ.toMonoidHom :=
    hψ ▸ Subgroup.map_mono hTH
  have hZ := j1_overgroup_index _ hSZ
  have hidx : (H.map ψ.toMonoidHom).index = H.index := Subgroup.index_map_equiv H ψ
  rw [hidx] at hZ
  rcases hZ with h1 | h1
  · have hHtop : H = ⊤ := Subgroup.index_eq_one.mp h1
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ H := hHtop ▸ Subgroup.mem_top _
    exact this
  · exact absurd hmod h1

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
