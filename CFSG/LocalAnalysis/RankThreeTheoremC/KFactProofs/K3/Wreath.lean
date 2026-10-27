module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Defs
public import CFSG.RankThree.PartTwo.Sec11.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerBalance
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPFrame
public import CFSG.RankThree.PartTwo.KFacts.K73Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroBase
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614PrimeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEQuaternionDihedral
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.ABGLocalTools (IsSylowOf)

theorem W3_center_le_of_normal {N : Subgroup W3} (hN : N.Normal) (hN1 : N ≠ ⊥) :
    center W3 ≤ N := by
  have hcard : Nat.card W3 = 81 := CFSG.RankThree.PartTwo.Sec11.card_wreath
  haveI : Finite W3 := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial W3 := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hp : IsPGroup 3 W3 := IsPGroup.of_card (n := 4) (hcard.trans (by norm_num))
  haveI : Group.IsNilpotent W3 := hp.isNilpotent
  have hZle : Nat.card (center W3) ≤ 3 := CFSG.RankThree.PartTwo.Sec11.card_center_wreath_le
  have hZgt : 1 < Nat.card (center W3) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hp.bot_lt_center.ne'
  have hZdvd : Nat.card (center W3) ∣ 81 := by
    have := Subgroup.card_subgroup_dvd_card (center W3)
    rwa [hcard] at this
  have hZ : Nat.card (center W3) = 3 := by
    have h2 : Nat.card (center W3) ≠ 2 := by
      intro h
      rw [h] at hZdvd
      omega
    omega
  have hNZ : N ⊓ center W3 ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  have hK : Nat.card ↥(N ⊓ center W3) = 3 := by
    have hKgt : 1 < Nat.card ↥(N ⊓ center W3) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hNZ
    have hKdvd : Nat.card ↥(N ⊓ center W3) ∣ 3 :=
      (Subgroup.card_dvd_of_le inf_le_right).trans (dvd_of_eq hZ)
    rcases (Nat.dvd_prime Nat.prime_three).mp hKdvd with h | h
    · omega
    · exact h
  have hKeq : N ⊓ center W3 = center W3 :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (hZ.trans hK.symm).le
  calc center W3 = N ⊓ center W3 := hKeq.symm
    _ ≤ N := inf_le_left

theorem pRank_top_le_three_of_wreath {H : Type} [Group H] [Finite H] (S : Sylow 3 H)
    (hSW : Nonempty ((S : Subgroup H) ≃* W3)) : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3 := by
  obtain ⟨e⟩ := hSW
  have hcard : Nat.card (S : Subgroup H) = 81 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec11.card_wreath
  have hnc : ¬ ∀ g ∈ (S : Subgroup H), ∀ h ∈ (S : Subgroup H), g * h = h * g := by
    intro hall
    have hcomm : ∀ a b : W3, a * b = b * a := by
      intro a b
      have h := hall ((e.symm a : (S : Subgroup H)) : H) (e.symm a).2
        ((e.symm b : (S : Subgroup H)) : H) (e.symm b).2
      have h2 : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
      simpa using congrArg e h2
    have hZ : center W3 = ⊤ := by
      refine (Subgroup.eq_top_iff' (center W3)).mpr fun z => ?_
      exact Subgroup.mem_center_iff.mpr fun g => hcomm g z
    have h81 : Nat.card (center W3) = 81 := by
      rw [hZ, Subgroup.card_top]
      exact CFSG.RankThree.PartTwo.Sec11.card_wreath
    have h3 : Nat.card (center W3) ≤ 3 := CFSG.RankThree.PartTwo.Sec11.card_center_wreath_le
    omega
  have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.pRank_le_pRank_sylow Nat.prime_three S
    (⊤ : Subgroup H)
  have h2 := CFSG.AGLEmbedding.pRank_le_three_of_card_le (P := (S : Subgroup H)) hcard.le hnc
  exact h1.trans h2

theorem wc_card_base :
    Nat.card CFSG.RankThree.PartTwo.KFacts.wreathBase = 27 :=
  CFSG.LocalAnalysis.RankThreeTheoremC.wreath_card_ker

theorem wc_card_center : Nat.card (Subgroup.center W3) = 3 := by
  have hz : Subgroup.center W3 = Subgroup.zpowers CFSG.RankThree.PartTwo.Sec11.wreathZ :=
    CFSG.RankThree.PartTwo.Sec11.center_eq_zpowers_wreathZ
  have h3 : CFSG.RankThree.PartTwo.Sec11.wreathZ ^ 3 = 1 :=
    CFSG.RankThree.PartTwo.Sec11.pow_three_eq_one_of_right_eq_one
      CFSG.RankThree.PartTwo.Sec11.wreathZ_right
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf CFSG.RankThree.PartTwo.Sec11.wreathZ = 3 :=
    _root_.orderOf_eq_prime h3 CFSG.RankThree.PartTwo.Sec11.wreathZ_ne_one
  rw [hz, Nat.card_zpowers]
  exact hord

theorem wc_nine_le {N : Subgroup W3} (hN : N.Normal) (hNc : ¬ N ≤ center W3) :
    9 ≤ Nat.card N := by
  have hN1 : N ≠ ⊥ := by
    rintro rfl
    exact hNc bot_le
  have hZN : center W3 ≤ N := W3_center_le_of_normal hN hN1
  have hZ : Nat.card (center W3) = 3 := wc_card_center
  have hNZ : 3 < Nat.card N := by
    by_contra h
    have h' : Nat.card N ≤ 3 := not_lt.mp h
    apply hNc
    have heq : center W3 = N := Subgroup.eq_of_le_of_card_ge hZN (by rw [hZ]; exact h')
    exact heq.symm.le
  have hW : Nat.card W3 = 81 := CFSG.RankThree.PartTwo.Sec11.card_wreath
  have hdvd : Nat.card N ∣ 3 ^ 4 := by
    rw [show (3 : ℕ) ^ 4 = 81 by norm_num, ← hW]
    exact Subgroup.card_subgroup_dvd_card N
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hkeq] at hNZ ⊢
  interval_cases k
  · norm_num at hNZ
  · norm_num at hNZ
  · norm_num
  · norm_num
  · norm_num

theorem wc_card_centralizer_le {g : W3} (hg : g.right ≠ 1) :
    Nat.card (Subgroup.centralizer ({g} : Set W3)) ≤ 9 := by
  set C : Subgroup W3 := Subgroup.centralizer ({g} : Set W3)
  let φ : C →* Multiplicative (ZMod 3) :=
    (RegularWreathProduct.rightHom : W3 →* Multiplicative (ZMod 3)).comp C.subtype
  have hker : Nat.card φ.ker ≤ 3 := by
    have hmap : Nat.card (φ.ker.map C.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective C)
    have hle : φ.ker.map C.subtype ≤ center W3 := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      have hcB : (c : W3).right = 1 := MonoidHom.mem_ker.mp hc
      have hcC : (c : W3) ∈ C := c.2
      rw [← CFSG.RankThree.PartTwo.KFacts.inf_centralizer_eq_center hg]
      exact Subgroup.mem_inf.mpr
        ⟨CFSG.RankThree.PartTwo.KFacts.mem_wreathBase.mpr hcB, hcC⟩
    rw [← hmap]
    calc Nat.card (φ.ker.map C.subtype) ≤ Nat.card (center W3) := Subgroup.card_le_of_le hle
      _ = 3 := wc_card_center
  have hidx : φ.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    calc Nat.card φ.range ≤ Nat.card (Multiplicative (ZMod 3)) :=
          Subgroup.card_le_card_group (H := φ.range)
      _ = 3 := by simp
  calc Nat.card C = Nat.card φ.ker * φ.ker.index := (Subgroup.card_mul_index φ.ker).symm
    _ ≤ 3 * 3 := Nat.mul_le_mul hker hidx
    _ = 9 := by norm_num

theorem wc_commutator_le_base :
    ⁅(⊤ : Subgroup W3), (⊤ : Subgroup W3)⁆ ≤ CFSG.RankThree.PartTwo.KFacts.wreathBase := by
  intro y hy
  rw [CFSG.RankThree.PartTwo.KFacts.commutator_eq_ker_wreathAb] at hy
  exact CFSG.RankThree.PartTwo.KFacts.mem_wreathBase.mpr
    (CFSG.RankThree.PartTwo.KFacts.mem_ker_wreathAb.mp hy).1

theorem wc_le_base {N M : Subgroup W3} (hN : N.Normal) (hM : M.Normal)
    (hNc : ¬ N ≤ center W3) (hMc : ¬ M ≤ center W3)
    (hc : ∀ a ∈ N, ∀ b ∈ M, a * b = b * a) :
    N ≤ CFSG.RankThree.PartTwo.KFacts.wreathBase := by
  intro g hgN
  by_contra hgB
  have hg : g.right ≠ 1 := fun h => hgB (CFSG.RankThree.PartTwo.KFacts.mem_wreathBase.mpr h)
  have hMC : M ≤ Subgroup.centralizer ({g} : Set W3) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc g hgN b hb).symm
  have h9M : 9 ≤ Nat.card M := wc_nine_le hM hMc
  have hC9 : Nat.card (Subgroup.centralizer ({g} : Set W3)) ≤ 9 :=
    wc_card_centralizer_le hg
  have heq : M = Subgroup.centralizer ({g} : Set W3) :=
    Subgroup.eq_of_le_of_card_ge hMC (le_trans hC9 h9M)
  have hM9 : Nat.card M = 9 := le_antisymm (by rw [heq]; exact hC9) h9M
  have hgM : g ∈ M := by
    rw [heq, Subgroup.mem_centralizer_singleton_iff]
  have hcomm : M = ⁅(⊤ : Subgroup W3), (⊤ : Subgroup W3)⁆ :=
    CFSG.RankThree.PartTwo.KFacts.eq_commutator_of_normal_of_card_nine hM hM9
  rw [hcomm] at hgM
  exact hgB (wc_commutator_le_base hgM)

theorem wc_eq_base_or {N : Subgroup W3} (hN : N.Normal)
    (hNB : N ≤ CFSG.RankThree.PartTwo.KFacts.wreathBase) (h9 : 9 ≤ Nat.card N) :
    N = CFSG.RankThree.PartTwo.KFacts.wreathBase ∨
      N = ⁅(⊤ : Subgroup W3), (⊤ : Subgroup W3)⁆ := by
  have hdvd : Nat.card N ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← wc_card_base]
    exact Subgroup.card_dvd_of_le hNB
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  interval_cases k
  · norm_num [hkeq] at h9
  · norm_num [hkeq] at h9
  · right
    exact CFSG.RankThree.PartTwo.KFacts.eq_commutator_of_normal_of_card_nine hN
      (by rw [hkeq]; norm_num)
  · left
    exact Subgroup.eq_of_le_of_card_ge hNB (by rw [wc_card_base, hkeq]; norm_num)

theorem wc_chain (X Y : Subgroup W3)
    (hX : X = CFSG.RankThree.PartTwo.KFacts.wreathBase ∨
      X = ⁅(⊤ : Subgroup W3), (⊤ : Subgroup W3)⁆)
    (hY : Y = CFSG.RankThree.PartTwo.KFacts.wreathBase ∨
      Y = ⁅(⊤ : Subgroup W3), (⊤ : Subgroup W3)⁆) :
    X ≤ Y ∨ Y ≤ X := by
  have hC := wc_commutator_le_base
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact Or.inl le_rfl
  · exact Or.inr hC
  · exact Or.inl hC
  · exact Or.inl le_rfl

theorem W3_comparable {N₁ N₂ : Subgroup W3} (h₁ : N₁.Normal) (h₂ : N₂.Normal)
    (h₁c : ¬ N₁ ≤ center W3) (h₂c : ¬ N₂ ≤ center W3)
    (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) : N₁ ≤ N₂ ∨ N₂ ≤ N₁ := by
  have hB₁ : N₁ ≤ CFSG.RankThree.PartTwo.KFacts.wreathBase :=
    wc_le_base h₁ h₂ h₁c h₂c hc
  have hB₂ : N₂ ≤ CFSG.RankThree.PartTwo.KFacts.wreathBase :=
    wc_le_base h₂ h₁ h₂c h₁c (fun a ha b hb => (hc b hb a ha).symm)
  exact wc_chain N₁ N₂ (wc_eq_base_or h₁ hB₁ (wc_nine_le h₁ h₁c))
    (wc_eq_base_or h₂ hB₂ (wc_nine_le h₂ h₂c))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
