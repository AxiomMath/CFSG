module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Fix
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U48
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Transport
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Goldschmidt.Basic
public import CFSG.Holt.Fixed
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank3
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem tag_of_marks (lab : LargeEvenLabel) (ht : markTag lab = .PSU) (hr : markRank lab = 4)
    (hn : markDeg lab = 3) (h2 : markChar lab = 2) :
    (lab.tag = .twA ∧ lab.rank = 3 ∧ lab.n = 3) ∨ (lab.tag = .twD ∧ lab.rank = 3 ∧ lab.n = 3) := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag <;> simp [markTag, markRank, markDeg, markChar] at ht hr hn h2 ⊢
  · exact ⟨hr, hn⟩
  · by_cases h3 : rank = 3 <;> simp [h3] at ht
  · by_cases h2' : rank = 2
    · simp [h2'] at ht
    · by_cases h3 : rank = 3
      · simp [h2', h3] at hn
        exact ⟨h3, hn⟩
      · simp [h2', h3] at ht

section Dict


theorem label_of_markedModel {lab : LargeEvenLabel} {R : Type} [Group R]
    (hM : MarkedModel lab R) (hX : CFSG.Blueprint.LieModel R .PSU 4 2 3)
    (hcard : Nat.card R = 8 ^ 6 * ((8 ^ 2 - 1) * (8 ^ 3 + 1) * (8 ^ 4 - 1))) :
    (lab.tag = .twA ∧ lab.rank = 3 ∧ lab.n = 3) ∨ (lab.tag = .twD ∧ lab.rank = 3 ∧ lab.n = 3) := by
  by_cases h2 : markChar lab = 2
  · have hM' : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) 2 (markDeg lab) := by
      have := hM
      unfold MarkedModel at this
      rwa [h2] at this
    obtain ⟨ht, hr, hn⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.lieModel_PSU_two_unique_of_card_eq (by norm_num) hX hM' rfl
    exact tag_of_marks lab ht hr hn h2
  · exfalso
    obtain ⟨tag, rank, n⟩ := lab
    cases tag <;> simp [markChar] at h2
    ·
      have h : CFSG.Blueprint.LieModel R .PSL 2 3 2 := hM
      have := CFSG.GH74.card_of_lieModel_PSL (by norm_num) h
      rw [hcard] at this
      norm_num [CFSG.Open.ordA] at this
    ·
      have h : CFSG.Blueprint.LieModel R .PSU 3 3 1 := hM
      have := CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSU33 h
      rw [hcard] at this
      norm_num at this

theorem recipe_of_label {lab : LargeEvenLabel}
    (h : (lab.tag = .twA ∧ lab.rank = 3 ∧ lab.n = 3) ∨ (lab.tag = .twD ∧ lab.rank = 3 ∧ lab.n = 3))
    {Q : LargeEvenRawCont} (hraw : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    LargeEvenRecipeUnitary (3 + 1) (2 ^ 3) Q := by
  obtain ⟨tag, rank, n⟩ := lab
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> simp only at h1 h2 h3 <;> subst h1 h2 h3
  · exact hraw
  · exact hraw

theorem indRel_barAut {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (l : ↥L) :
    indRel 3 L b (QuotientGroup.mk l : PQuot 3 L)
      (barAut L b hb (QuotientGroup.mk l : PQuot 3 L)) :=
  ⟨l, conjL L b hb l, rfl, rfl, rfl⟩

open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 fieldFactor4 card_SU4
  mem_range_conj_of_fieldFactor4_eq_one)

theorem dict_outer {G : Type} [Group G] [Finite G] {L : Subgroup G} {b : G}
    (hcat : catalogIs (PSimple 3 L) S9.isU4eight) (hFO : FieldOn 3 b L)
    (τ : PSimple 3 L ≃* SU4) (γ : MulAut SU4)
    (hγ : ∀ q : PQuot 3 L,
      γ (τ (QuotientGroup.mk q)) = τ (QuotientGroup.mk (barAut L b hFO.1 q))) :
    γ ^ 3 = 1 ∧ γ ∉ (MulAut.conj : SU4 →* MulAut SU4).range := by
  obtain ⟨-, lab, hlab, hraw⟩ := Canonical.largeEvenMarking_markedModel hFO.2
  have hX : CFSG.Blueprint.LieModel (PSimple 3 L) .PSU 4 2 3 := by
    obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU4eight hcat
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
      (hq.trans (by norm_num))
    have hm := lieModel_twistedA' 3 q hv e
    rw [h1, h2] at hm
    exact CFSG.Models.LieModel.toBlueprint (by decide) hm
  have hcard : Nat.card (PSimple 3 L) = 8 ^ 6 * ((8 ^ 2 - 1) * (8 ^ 3 + 1) * (8 ^ 4 - 1)) := by
    rw [Nat.card_congr τ.toEquiv]
    have := card_SU4
    norm_num at this ⊢
    exact this
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, -, hM₀⟩ := hQ₀
  have hM : MarkedModel lab (PSimple 3 L) := MarkedModel.of_mulEquiv θ₀.symm hM₀
  have hlabel := label_of_markedModel hM hX hcard
  obtain ⟨K', _, _, hK', hQ⟩ := recipe_of_label hlabel hraw
  obtain ⟨hs, hna, θ, ⟨-, f, hf, u, hu, hord, hα⟩, -⟩ := hQ
  have hKc : Nat.card K' = (2 ^ 3) ^ 2 := hK'
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K' := ⟨Nat.prime_two, by norm_num, by rw [hKc]; norm_num⟩
  have hInn := CFSG.StandardType.RecipeFieldSU.ggRawInnField_unitary (d := 3 + 1) (n := 3)
    hUFD hKc (by norm_num) (by norm_num) (p := 3) (by norm_num)
  obtain ⟨hmul, hinv, hconj, hfI⟩ := hInn hs hna
  set α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin (3 + 1)) K' (2 ^ 3))) := u * f * u⁻¹ with hαdef
  let κ : LargeEvenProj (LargeEvenSUGroup (Fin (3 + 1)) K' (2 ^ 3)) ≃* SU4 := θ.symm.trans τ
  have hγκ : γ = MulAut.congr κ α := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨z, rfl⟩ := τ.surjective x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hγ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    have h1 : κ.symm (τ (QuotientGroup.mk (QuotientGroup.mk l : PQuot 3 L))) =
        θ (QuotientGroup.mk (QuotientGroup.mk l : PQuot 3 L)) := by simp [κ]
    rw [h1, hα _ _ (indRel_barAut hFO.1 l)]
    simp [κ]
  have hf3 : f ^ 3 = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hord] at this
  have hα3 : α ^ 3 = 1 := by rw [hαdef, conj_pow, hf3, mul_one, mul_inv_cancel]
  refine ⟨by rw [hγκ, ← map_pow, hα3, map_one], ?_⟩
  rintro ⟨g, hg⟩
  have hαg : α = MulAut.conj (κ.symm g) := by
    have h1 : MulAut.congr κ α = MulAut.conj g := by rw [← hγκ, hg]
    have h2 : MulAut.congr κ (MulAut.conj (κ.symm g)) = MulAut.conj g := by
      rw [congr_conj, κ.apply_symm_apply]
    exact (MulAut.congr κ).injective (h1.trans h2.symm)
  have hαI := hαg ▸ hconj (κ.symm g)
  have hfeq : f = u⁻¹ * α * u := by rw [hαdef]; group
  exact hfI f hf hord (by rw [hfeq]; exact hmul _ (hmul _ (hinv u hu) α hαI) u hu)

end Dict

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48
