module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeSporGen
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psl
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016Fi22
public import CFSG.Sporadic.Fi24I301Cover.Row
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294SporRank
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListE1

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree

open CFSG.Open TauCeti

theorem four_le_pRank_of_suzCover {L : Type} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) (h3 : 3 ∣ Nat.card (Subgroup.center L))
    (φ : L ⧸ Subgroup.center L ≃* SporadicName.Suz.Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.1
  have : IsSimpleGroup SporadicName.Suz.Group := φ.symm.isSimpleGroup
  obtain ⟨eX⟩ := CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.nonempty_mulEquiv_suzX
  let f : L →* CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz.suzX :=
    (φ.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hf : Function.Surjective f :=
    (φ.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center L := by
    ext g
    simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz in
  have h := CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift.succ_le_localRank_of_lift hf
    hker.le Nat.prime_three (by norm_num) (hker ▸ h3) (E := suzE)
    (fun x hx y hy => commute_of_mem_suzE hf hker.le hx hy)
    (fun e he => exists_lift_of_mem_suzE hf hker.le he) tX_ne_one tX_sq
    (fun e he => commute_tX he) (r := 3) card_suzE
  exact h.trans (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.localRank_le_pRank
    Nat.prime_three)

theorem four_le_pRank_of_fi22Cover
    {L : Type} [Group L] [Finite L]
    (hL : CFSG.IsQuasisimple L) (h3 : 3 ∣ Nat.card (Subgroup.center L))
    (φ : L ⧸ Subgroup.center L ≃* SporadicName.Fi22.Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.1
  have : IsSimpleGroup SporadicName.Fi22.Group := φ.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Fi22
  let ψ₁ : CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃* CFSG.Blueprint.NativeSporadic.Fi22 :=
    MulEquiv.refl _
  let ψ₂ : CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (CFSG.Blueprint.NativeSporadic.seedMonoid 3 77 1
        CFSG.RankThree.PartTwo.Census.fi22Lift.base.seedA
        CFSG.RankThree.PartTwo.Census.fi22Lift.base.seedB)ˣ := MulEquiv.refl _
  let f : L →* SporadicName.Fi22.Group := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hf : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center L := by
    ext g
    simp [f]
  have h5 := CFSG.RankThree.PartTwo.Sec4.Census.LiftCert.five_le_localRank_of_check'
    (CFSG.SectionRank.spec3 77) CFSG.RankThree.PartTwo.Census.fi22Lift
    CFSG.RankThree.PartTwo.Sec4.Census.fi22Lift_check
    CFSG.RankThree.PartTwo.Sec4.Census.fi22Lift_covers (b.trans (ψ₁.trans ψ₂)) hf hker.le
    (by rw [hker]; exact h3)
  exact (by norm_num : 4 ≤ 5).trans (h5.trans
    (CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.localRank_le_pRank Nat.prime_three))

theorem five_le_pRank_of_split {S : Type} [Group S] {B₁ : Subgroup S} {d : S}
    (hB : Nat.card B₁ = 3 ^ 5)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* S), Function.Surjective π →
      π.ker = Subgroup.center E → Nat.card π.ker = 3 →
      ∃ Bh : Subgroup E, IsElemAbelian 3 Bh ∧ Bh ⊓ Subgroup.center E = ⊥ ∧ Bh.map π = B₁ ∧
        ∃ dh ∈ Bh, π dh = d)
    {L : Type} [Group L] [Finite L] (h3 : Nat.card (Subgroup.center L) = 3)
    (e : L ⧸ Subgroup.center L ≃* S) : 5 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  let π : L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext g
    simp [π]
  obtain ⟨Bh, hBh, hBhZ, hBhmap, -⟩ := hsplit L π hπ hker (by rw [hker]; exact h3)
  have hinj : Function.Injective (π.comp Bh.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxk : (x : L) ∈ π.ker := hx
    rw [hker] at hxk
    have : (x : L) ∈ Bh ⊓ Subgroup.center L := ⟨x.2, hxk⟩
    rw [hBhZ, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hcard : Nat.card Bh = 3 ^ 5 := by
    have h1 : Nat.card (π.comp Bh.subtype).range = Nat.card Bh :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    have h2 : (π.comp Bh.subtype).range = B₁ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hBhmap]
    rw [← h1, h2, hB]
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hBh hcard

theorem four_le_pRank_of_fi24Cover
    {L : Type} [Group L] [Finite L]
    (h3 : Nat.card (Subgroup.center L) = 3)
    (φ : L ⧸ Subgroup.center L ≃* SporadicName.Fi24Prime.Group) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  obtain ⟨j⟩ := CFSG.Sporadic.Fi24I301.nonempty_jEquiv
  exact (by norm_num : 4 ≤ 5).trans (five_le_pRank_of_split CFSG.Sporadic.Fi24I301.fi24_hB.2
    CFSG.Sporadic.Fi24I301Cover.fi24h_split h3 (φ.trans j.symm))

open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.RankThree.PartTwo.Sec4.Census (sporadicMultiplierOrder)
open CFSG.Blueprint (NativeSporadic.Carrier)

theorem card_center_dvd_sporadicMultiplierOrder :
    ∀ (s : SporadicName) (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L →
      Nonempty (L ⧸ Subgroup.center L ≃* s.Group) →
      Nat.card (Subgroup.center L) ∣ sporadicMultiplierOrder s := by
  intro s L _ _ hL ⟨φ⟩
  have h := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hL φ
  have hm :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds.1 s
  exact hm ▸ h

theorem card_outer_sporadic_le_two :
    ∀ s : SporadicName, s ≠ .M → Nat.card (Outer s.Group) ≤ 2 := by
  intro s hs
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  exact (Nat.card_congr (equivalence e).toEquiv).symm.le.trans
    (CFSG.AGLEmbeddingD2.card_outer_carrier_le_two_of_ne_M s hs)

theorem four_le_pRank_of_rankFourSporadic :
    ∀ s : SporadicName, RankFourSporadic s → ∀ (L : Type) [Group L] [Finite L],
      Nonempty (L ≃* s.Group) → 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  intro s hs L _ _ ⟨e⟩
  have : Finite (CFSGIndex.sporadic s).Group := Finite.of_equiv L e.toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3 in
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Suz_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.ON_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Co1_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Co2_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Co3_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Fi22_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Fi23_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Fi24prime_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.HN_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Ly_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.Th_elementary_three_rank_four
  · exact four_le_pRank_of_elem _ hbr CFSG.SectionRank.B_elementary_three_rank_four
  · exact monsterThreeRankFour_holds

theorem not_nine_dvd_card_J1 :
    ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* SporadicName.J1.Group) →
      ¬ 3 ^ 2 ∣ Nat.card L := by
  intro L _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .J1
  rw [Nat.card_congr (e.trans b.symm).toEquiv,
    CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder .J1 (by decide)]
  norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]

theorem sporadicCentGen_three_of_row
    (s : SporadicName) (hs : s = .M23 ∨ s = .HS) :
    CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 s := by
  intro L _ _ ⟨e⟩ A hA hAc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsM : s ≠ .M := by rcases hs with rfl | rfl <;> decide
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
  let eL : L ≃* NativeSporadic.Carrier s := e.trans f.symm
  have hfacts :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.carrierFacts_of_ne_M s hsM
  have : IsSimpleGroup (NativeSporadic.Carrier s) := hfacts.2.1
  have : IsSimpleGroup L := eL.isSimpleGroup
  have hL : Nat.card L = CFSG.AGLEmbeddingD2.d2SporadicOrder s :=
    (Nat.card_congr eL.toEquiv).trans (CFSG.AGLEmbeddingD2.card_carrier_eq_d2SporadicOrder s hsM)
  have hcube : ¬ 3 ^ 3 ∣ Nat.card L := by
    rw [hL]
    rcases hs with rfl | rfl <;> norm_num [CFSG.AGLEmbeddingD2.d2SporadicOrder]
  have hpr : (s, 3) ∈ CFSG.AGLEmbeddingD2.d2SporadicProvedList := by
    rcases hs with rfl | rfl <;> decide
  exact CFSG.LocalAnalysis.AGL81I.Section3.SporGen.centGen_eq_top_of_not_cube hcube
    (CFSG.LocalAnalysis.AGL81I.Section3.SporGen.glbCore_eq_top_of_provedRow
      CFSG.AGLEmbedding.sporProvedRows hpr (by norm_num) ⟨eL⟩ hcube) A hA hAc

theorem sporadicGen24_12Three_of_inputs
    (hJ2 : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 .J2)
    (hM24 : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 .M24)
    (hHe : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 .He)
    (hRu : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 .Ru)
    (hJ4 : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 .J4)
    (hM22 : SporadicCoverGen .M22) (hON : ONTripleCoverFacts)
    (hJ3 : CFSG.LocalAnalysis.RankThreeTheoremC.HasLiftableTriple SporadicName.J3.Group) :
    CFSG.LocalAnalysis.AGL81I.Section3.SporadicGen24_12Three := by
  refine sporadicGen24_12Three_of card_center_dvd_sporadicMultiplierOrder
    card_outer_sporadic_le_two four_le_pRank_of_rankFourSporadic ?_ not_nine_dvd_card_J1 ?_ hM22
    hON
  · intro s hs L _ _ hL h3 ⟨φ⟩
    rcases hs with rfl | rfl | rfl | rfl
    · exact hJ3.four_le_pRank_of_cover φ h3
    · exact four_le_pRank_of_suzCover hL h3 φ
    · exact four_le_pRank_of_fi22Cover hL h3 φ
    · have hdvd := card_center_dvd_sporadicMultiplierOrder .Fi24Prime L hL ⟨φ⟩
      have hd3 : Nat.card (Subgroup.center L) ∣ 3 := hdvd
      exact four_le_pRank_of_fi24Cover (Nat.dvd_antisymm hd3 h3) φ
  · intro s hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sporadicCentGen_three_of_row .M23 (Or.inl rfl)
    · exact sporadicCentGen_three_of_row .HS (Or.inr rfl)
    · exact hJ2
    · exact hM24
    · exact hHe
    · exact hRu
    · exact hJ4

end CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree
