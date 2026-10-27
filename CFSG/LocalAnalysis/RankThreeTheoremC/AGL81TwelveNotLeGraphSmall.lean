module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphQuasi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSmallIndex
public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeSmallBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveLeSmallNorm
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCosets

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Small

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.HardMathSupport.Curtis.Proving

theorem relIndex_normalizer_dvd_three {Q : Type} [Group Q]
    (h96 : OvergroupOrder96 (Q ⧸ Subgroup.center Q)) {T P : Subgroup Q}
    (hT : IsSylowTwoOf T ⊤) (hP : P ≠ ⊤) (hNP : Subgroup.normalizer (T : Set Q) ≤ P) :
    (Subgroup.normalizer (T : Set Q)).relIndex P ∣ 3 := by
  obtain ⟨π, hπ⟩ : ∃ π : Q →* Q ⧸ Subgroup.center Q, π = QuotientGroup.mk' (Subgroup.center Q) :=
    ⟨_, rfl⟩
  have hker : π.ker = Subgroup.center Q := by rw [hπ, QuotientGroup.ker_mk']
  have hπs : Function.Surjective π := by
    rw [hπ]
    exact QuotientGroup.mk'_surjective _
  have hZN : Subgroup.center Q ≤ Subgroup.normalizer (T : Set Q) :=
    Subgroup.center_le_normalizer _
  have hZP : Subgroup.center Q ≤ P := hZN.trans hNP
  have hTP : T ≤ P := Subgroup.le_normalizer.trans hNP
  have hTb : IsSylowTwoOf (T.map π) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hT π hπs
  have hPb : P.map π ≠ ⊤ := by
    intro htop
    apply hP
    have hkerP : π.ker ≤ P := by
      rw [hker]
      exact hZP
    rw [← Subgroup.comap_map_eq_self hkerP, htop, Subgroup.comap_top]
  have hTbPb : T.map π ≤ P.map π := Subgroup.map_mono hTP
  have h3 : (T.map π).relIndex (P.map π) ∣ 3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small.relIndex_dvd_three_of_card_dvd hTb hTbPb
      (h96 _ _ hTb hTbPb hPb)
  rw [Subgroup.relIndex_map_map, hker, sup_eq_left.2 hZP] at h3
  have hle : T ⊔ Subgroup.center Q ≤ Subgroup.normalizer (T : Set Q) :=
    sup_le Subgroup.le_normalizer hZN
  exact (Dvd.intro_left _ (Subgroup.relIndex_mul_relIndex _ _ _ hle hNP)).trans h3

theorem relIndex_normalizer_dvd_three_of_parabolic {A : Type} [Group A]
    {Y P T : Subgroup A} (h96 : OvergroupOrder96 (↥Y ⧸ Subgroup.center ↥Y))
    (hT : IsSylowTwoOf T Y) (hPY : P ≤ Y) (hne : P ≠ Y)
    (hNT : Y ⊓ Subgroup.normalizer (T : Set A) ≤ P) :
    (Subgroup.normalizer (T : Set A)).relIndex P ∣ 3 := by
  have hN := Subgroup.subgroupOf_normalizer_eq hT.1
  have hTb : IsSylowTwoOf (T.subgroupOf Y) ⊤ := CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT
  have hPb : P.subgroupOf Y ≠ ⊤ := fun h =>
    hne (le_antisymm hPY (Subgroup.subgroupOf_eq_top.1 h))
  have hNP : Subgroup.normalizer (T.subgroupOf Y : Set ↥Y) ≤ P.subgroupOf Y := by
    intro x hx
    rw [← hN] at hx
    exact Subgroup.mem_subgroupOf.2 (hNT ⟨x.2, Subgroup.mem_subgroupOf.1 hx⟩)
  have h := relIndex_normalizer_dvd_three h96 hTb hPb hNP
  rwa [← hN, Subgroup.relIndex_subgroupOf hPY] at h

theorem noTwoSymThree_of_normalizer_index_dvd_three {A : Type} [Group A] [Finite A]
    {P : Subgroup A} {T : Subgroup ↥P} (hT : IsSylowTwoOf T ⊤)
    (hidx : (Subgroup.normalizer (T : Set ↥P)).index ∣ 3) : NoTwoSymThree P := by
  intro X X' hX hX' hXs hXs'
  have hTb : IsSylowTwoOf (T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective hT _ (QuotientGroup.mk'_surjective _)
  have hodd : ¬ 2 ∣ (T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).index := by
    have h := hTb.2.2
    rwa [show ((T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).subgroupOf ⊤).index =
      (T.map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))).index from
        Subgroup.relIndex_top_right _] at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ((hTb.2.1.toSylow hodd : Sylow 2 (↥P ⧸ CFSG.pCore 2 ↥P)) :
      Subgroup (↥P ⧸ CFSG.pCore 2 ↥P)) ≤ 2 := by
    rw [IsPGroup.toSylow_coe]
    exact card_map_pCore_le_two hT.2.1 hidx
  exact Sym.eq_of_card_sylow_le_two (pCore_two_hat_eq_bot P) hX hX' hXs hXs'
    (hTb.2.1.toSylow hodd) hcard

theorem noTwoSymThree_of_overgroupOrder96 {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (h96 : OvergroupOrder96 (↥Y ⧸ Subgroup.center ↥Y)) (hP : IsParabolicTwo Y P) :
    NoTwoSymThree P := by
  by_cases hPY : P = Y
  · subst hPY
    exact noTwoSymThree_of_quasisimple hY hO
  obtain ⟨hPle, T, hT, hNT⟩ := hP
  have hTP : T ≤ P := fun x hx => hNT ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
  have hTb : IsSylowTwoOf (T.subgroupOf P) ⊤ :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf
      (CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe.Small.isSylowTwoOf_of_le hT hTP hPle)
  have hdvd := relIndex_normalizer_dvd_three_of_parabolic h96 hT hPle hPY hNT
  refine noTwoSymThree_of_normalizer_index_dvd_three hTb ?_
  rw [← Subgroup.subgroupOf_normalizer_eq hTP]
  exact hdvd

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Small
