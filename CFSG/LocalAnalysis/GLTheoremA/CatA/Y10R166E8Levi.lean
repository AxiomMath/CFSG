module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE8Levi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG CFSG.Open CFSG.Blueprint CFSG.LieType CFSG.LocalAnalysis.GLTheoremA


open CFSG.ComponentClassification.CatLeafProof CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint

private theorem isQuasisimple_of_map_eq {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {A : Subgroup G} {J : Subgroup H} (hJ : A.map f = J)
    (hA : CFSG.IsQuasisimple ↥A) : CFSG.IsQuasisimple ↥J := by
  subst hJ
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.equivMapOfInjective A f hf) hA

private theorem lieModel_centerQuot_of_map_eq {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {A : Subgroup G} {J : Subgroup H} (hJ : A.map f = J)
    {t : StatedLieTag} {n p q : ℕ} (h : LieModel (↥A ⧸ Subgroup.center ↥A) t n p q) :
    LieModel (↥J ⧸ Subgroup.center ↥J) t n p q := by
  subst hJ
  exact Blueprint.LieModel.of_mulEquiv
    (CFSG.StandardType.centerQuotCongr (Subgroup.equivMapOfInjective A f hf)) h

theorem isQuasisimple_and_lieModel_subsystemGroup_e8D7 {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    CFSG.IsQuasisimple ↥(subsystemGroup Tag.E8 K (Set.range e8D7Node)) ∧
      LieModel (↥(subsystemGroup Tag.E8 K (Set.range e8D7Node)) ⧸
        Subgroup.center ↥(subsystemGroup Tag.E8 K (Set.range e8D7Node))) .POmegaPlus 7 2 f := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf1 : 1 ≤ f := by omega
  obtain ⟨O, C, hE⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e8D7Node e8D7_adj e8D7_nadj
  have hadm : StatedLieAdmissible .POmegaPlus 7 2 f := ⟨Nat.prime_two, hf1, by norm_num⟩
  obtain ⟨Ψ, -, -, hqs, hmodel⟩ :=
    spinPlus_frame_subgroup (n := 7) hadm (by norm_num) hK
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (e8D7Node k))
      hcomm hρ hψ
  have hmap : (⨆ k, CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (e8D7Node k)).map
      (adjointGroup Tag.E8 K).subtype =
      subsystemGroup Tag.E8 K (Set.range e8D7Node) := map_subtype_iSup_rankOne e8D7Node
  exact ⟨isQuasisimple_of_map_eq (adjointGroup Tag.E8 K).subtype_injective hmap hqs,
    lieModel_centerQuot_of_map_eq (adjointGroup Tag.E8 K).subtype_injective hmap hmodel⟩

theorem hasLabel_subsystemGroup_e8D7 {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) :
    HasLabel ↥(subsystemGroup Tag.E8 K (Set.range e8D7Node)) (· = ⟨.D, 7, f⟩) := by
  obtain ⟨hqs, hmodel⟩ := isQuasisimple_and_lieModel_subsystemGroup_e8D7 hf hK
  exact hasLabel_of_statedClassicalModel_POmegaPlus hqs
    (hmodel.statedClassicalModel (by decide))

end CFSG.LocalAnalysis.GLTheoremA.Y10F
