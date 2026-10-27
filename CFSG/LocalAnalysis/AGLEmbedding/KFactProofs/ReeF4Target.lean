module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeReeF4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LieType.Ree.FixedSubgroupData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarTargetTwoData
import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
import CFSG.LieType.Ree.LargeReeModelSchreier
import CFSG.CharacterTheory.Semidihedral.FixedFieldData
import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
import CFSG.LocalAnalysis.SectionRank.SylowWitness
import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixed
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outer_reeGamma
    {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsCyclic (Outer (F4.reeGamma K a)) ∧ Nat.card (Outer (F4.reeGamma K a)) ∣ 2 * a + 1 := by
  obtain ⟨-, -, -, -, hcard, hcyc, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 (2 * a + 1) Nat.prime_two (by omega) K hK
  let ψ : (K ≃+* K) →* Outer (F4.reeGamma K a) :=
    (QuotientGroup.mk' (inner (F4.reeGamma K a))).comp (F4.reeGammaFieldAutHom K a)
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, β, rfl⟩ :=
      (CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form ha hK).1 α
    refine ⟨β, ?_⟩
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, F4.reeGammaFieldAutHom_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner (F4.reeGamma K a))
      (MulAut.conj y)).2 ⟨y, rfl⟩, one_mul]
  exact ⟨isCyclic_of_surjective ψ hsurj, hcard ▸ Subgroup.card_dvd_of_surjective hsurj⟩

theorem exists_elemAbelian_twentyfive_reeGamma
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    ∃ E : Subgroup (F4.reeGamma K 2), CFSG.Open.IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
  obtain ⟨σ, -, hσ, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 5 Nat.prime_two (by norm_num) K (by simpa using hK)
  have hk := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by norm_num : 1 ≤ 5) (by simpa using hK) σ).2
  rw [hσ] at hk
  have hk1 : Nat.card (fixSubfield σ) = 2 ^ 1 := by simpa using hk
  have hfix := CFSG.SignalizerFunctorTheorem.CatalogBridge.fixed_reeGamma_F4_eq_map
    (a := 2) (b := 0) (d := 1) (m := 2) σ hk1 (by norm_num)
  have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hk1
  obtain ⟨x, y, -, hx, hy, hxy, hcard, -, -⟩ :=
    CFSG.SectionRank.Tits_sylow5_square_witness (K := fixSubfield σ) hk2
  let D := commutator (reeFixed ReeTag.F4 (fixSubfield σ) 0)
  let e₁ := ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0
  let φ := (baseChangeGL (fixSubfield σ).subtype).comp
    ((F4.reeGamma (fixSubfield σ) 0).subtype.comp (e₁.toMonoidHom.comp D.subtype))
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective _).comp (Subtype.val_injective.comp
      (e₁.injective.comp Subtype.val_injective))
  have hmem : ∀ d, φ d ∈ F4.reeGamma K 2 := by
    intro d
    have : φ d ∈ (F4.reeGamma (fixSubfield σ) 0).map (baseChangeGL (fixSubfield σ).subtype) :=
      ⟨_, (e₁ d).2, rfl⟩
    rw [← hfix] at this
    obtain ⟨γ, -, hγ⟩ := this
    rw [← hγ]
    exact γ.2
  let ψ := φ.codRestrict _ hmem
  have hψinj : Function.Injective ψ := fun a b h => hφinj (congrArg Subtype.val h)
  refine ⟨(Subgroup.closure {x, y}).map ψ,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 5 ψ _
      (CFSG.SectionRank.isElemAbelian_closure_pair hx hy hxy), ?_⟩
  rw [Subgroup.card_map_of_injective hψinj, hcard]

theorem stmtReeF4Target :
    StmtReeF4Target := by
  intro d hd L _ _ ⟨e⟩
  have hsimple : IsSimpleGroup L := by
    have := isSimpleGroup_of_catGroup_reeF4 hd
    exact e.isSimpleGroup
  have hcard : Nat.card L = 5 ^ 4 * 2109813049279346316323458575652356096 := by
    rw [Nat.card_congr e.toEquiv, card_catGroup_reeF4 hd]
    norm_num [CFSG.Open.ordTwistedF4]
  have hmodel := reeTitsModel_of_catGroup_reeF4 hd
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier (CatGroup d) 2 (2 * 2 + 1) hmodel
  obtain ⟨-, a, hfa, K, _, _, hK, ⟨e'⟩⟩ := hmodel
  have hKc : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  have : CharP K F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  obtain ⟨eΓ⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e'⟩
  have ha : a = 2 := by omega
  subst ha
  obtain ⟨hOutc, hOutn⟩ := outer_reeGamma (a := 2) (K := K) (by norm_num) hKc
  let eO := CFSG.ComponentClassification.OuterAutomorphisms.equivalence (e.trans eΓ)
  have hOutL : IsCyclic (Outer L) :=
    haveI := hOutc
    isCyclic_of_surjective eO.symm.toMonoidHom eO.symm.surjective
  have hOutn' : Nat.card (Outer L) ∣ 5 * 1 := by
    rw [Nat.card_congr eO.toEquiv]
    exact hOutn
  obtain ⟨E, hE, hE25⟩ := exists_elemAbelian_twentyfive_reeGamma (K := K) hKc
  have hrankL : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup L) := by
    refine le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 5 Nat.prime_five _)
      ⟨E.map (e.trans eΓ).symm.toMonoidHom, le_top,
        CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 5 _ _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective (e.trans eΓ).symm.injective, hE25]
  exact KFactProofs.TargetTwo.target_of_data (p := 5) (a := 4)
    (n := 2109813049279346316323458575652356096) (m := 1) (ℓ := 331)
    Nat.prime_five hsimple hcard (by norm_num) (by norm_num) hrankL hOutL hOutn' (by norm_num)
    (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
    (fun k hk hk5 => by interval_cases k <;> norm_num)

end CFSG.AGLEmbedding
