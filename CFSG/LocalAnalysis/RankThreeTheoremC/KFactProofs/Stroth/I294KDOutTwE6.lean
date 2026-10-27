module

public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutDefs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.SL2Pair
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.PartTwo.Census CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth (c3 u1 c3_pow_three c3_ne_one
  c3_pow_commute_u1)
open scoped MatrixGroups

theorem four_le_pRank_three_of_commuting_sl2 {K : Type} [Field K] {X : Type} [Group X] [Finite X]
    (φ : Fin 4 → SL(2, K) →* X) (hφ : ∀ i, Function.Injective (φ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (φ i A) (φ j B)) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (c3 : SL(2, K)) = 3 := orderOf_eq_prime c3_pow_three c3_ne_one
  have hx3 : ∀ i, (φ i c3) ^ 3 = 1 := fun i => by rw [← map_pow, c3_pow_three, map_one]
  have key : ∀ (i : Fin 4) (n : ℕ) (y : X), (∀ B, Commute y (φ i B)) → (φ i c3) ^ n = y →
      3 ∣ n := by
    intro i n y hy hn
    have h1 : Commute ((φ i c3) ^ n) (φ i u1) := by
      rw [hn]
      exact hy u1
    rw [← map_pow] at h1
    have h2 : Commute ((c3 : SL(2, K)) ^ n) u1 := by
      have := h1.eq
      rw [← map_mul, ← map_mul] at this
      exact hφ i this
    have h3 := c3_pow_commute_u1 h2
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one h3
  have hcomm : ∀ (i j : Fin 4), i ≠ j → ∀ (n : ℕ) (B : SL(2, K)), Commute ((φ i c3) ^ n) (φ j B) :=
    fun i j hij n B => by
      rw [← map_pow]
      exact hc i j hij _ B
  refine four_le_pRank_of_commuting_order_three (φ 0 c3) (φ 1 c3) (φ 2 c3) (φ 3 c3) (hx3 0)
    (hx3 1) (hx3 2) (hx3 3) (hc 0 1 (by decide) _ _) (hc 0 2 (by decide) _ _)
    (hc 0 3 (by decide) _ _) (hc 1 2 (by decide) _ _) (hc 1 3 (by decide) _ _)
    (hc 2 3 (by decide) _ _) ?_
  intro a b c d h
  have hpow : ∀ (i : Fin 4) (n : ℕ), 3 ∣ n → (φ i c3) ^ n = 1 := by
    intro i n hn
    obtain ⟨k, rfl⟩ := hn
    rw [pow_mul, hx3, one_pow]
  have ha : 3 ∣ a := by
    refine key 0 a ((φ 1 c3 ^ b * φ 2 c3 ^ c * φ 3 c3 ^ d)⁻¹) (fun B => ?_) ?_
    · exact Commute.inv_left (((hcomm 1 0 (by decide) b B).mul_left
        (hcomm 2 0 (by decide) c B)).mul_left (hcomm 3 0 (by decide) d B))
    · refine eq_inv_of_mul_eq_one_left ?_
      simpa [mul_assoc] using h
  rw [hpow 0 a ha, one_mul] at h
  have hb : 3 ∣ b := by
    refine key 1 b ((φ 2 c3 ^ c * φ 3 c3 ^ d)⁻¹) (fun B => ?_) ?_
    · exact Commute.inv_left ((hcomm 2 1 (by decide) c B).mul_left (hcomm 3 1 (by decide) d B))
    · refine eq_inv_of_mul_eq_one_left ?_
      simpa [mul_assoc] using h
  rw [hpow 1 b hb, one_mul] at h
  have hc' : 3 ∣ c := by
    refine key 2 c ((φ 3 c3 ^ d)⁻¹) (fun B => ?_) ?_
    · exact Commute.inv_left (hcomm 3 2 (by decide) d B)
    · exact eq_inv_of_mul_eq_one_left h
  rw [hpow 2 c hc', one_mul] at h
  have hd : 3 ∣ d := by
    refine key 3 d 1 (fun B => Commute.one_left _) ?_
    exact h
  exact ⟨ha, hb, hc', hd⟩

theorem exists_four_commuting_injective_sl2_twistedE6
    (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    ∃ (F : Type) (_ : Field F) (φ : Fin 4 → SL(2, F) →* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩),
      (∀ i, Function.Injective (φ i)) ∧ ∀ i j, i ≠ j → ∀ A B, Commute (φ i A) (φ j B) := by
  let d : TypeTwistedE6LieIndex :=
    ⟨⟨.twistedE6 q, hv⟩, (LieTypeIndex.isTypeTwistedE6_iff _).2 trivial⟩
  have hfin : Finite d.1.fixedField := Nat.finite_of_card_ne_zero (by
    rw [ValidLieTypeIndex.card_fixedField]
    have h : (d.1 : ValidLieTypeIndex).fieldOrder = q.card := LieTypeIndex.fieldOrder_twistedE6 q
    rw [h, TauCeti.PrimePower.card_def]
    exact (pow_pos q.prime_p.pos _).ne')
  have : Fintype d.1.fixedField := Fintype.ofFinite _
  have hC := commutator_fixedGroup_quadField d
  have hj : ∀ x, quadFrob d (quadIncl d x) = quadIncl d x := quadFrob_quadIncl d
  have hinj : ∀ i : Fin 4, Function.Injective
      ((toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i)) := fun i =>
    toQuot_comp_injective (te6Embed_injective d) hC _ fun A hA =>
      te6SL2_central (quadFrob d) (quadIncl d) hj i hA
  refine ⟨d.1.fixedField, inferInstance,
    fun i => (toQuot (te6Embed d) hC).comp (te6SL2 (quadFrob d) (quadIncl d) hj i), hinj,
    fun i i' hii' A B => ?_⟩
  have h01 : Commute (te6SL2 (quadFrob d) (quadIncl d) hj i A)
      (te6SL2 (quadFrob d) (quadIncl d) hj i' B) :=
    te6SL2_commute (quadFrob d) (quadIncl d) hj hii' A B
  exact h01.map (toQuot (te6Embed d) hC)

theorem four_le_pRank_three_twistedE6
    {X : Type} [Group X] [Finite X] {q : PrimePower}
    {hv : (LieTypeIndex.twistedE6 q).Valid}
    (e : X ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨F, _, φ, hφ, hc⟩ := exists_four_commuting_injective_sl2_twistedE6 q hv
  refine four_le_pRank_three_of_commuting_sl2 (fun i => e.symm.toMonoidHom.comp (φ i))
    (fun i => e.symm.injective.comp (hφ i)) fun i j hij A B => ?_
  change e.symm (φ i A) * e.symm (φ j B) = e.symm (φ j B) * e.symm (φ i A)
  rw [← map_mul, ← map_mul, (hc i j hij A B).eq]

section Model


theorem twistedE6ThreeRankFour_holds : TwistedE6ThreeRankFour := by
  intro X _ _ ℓ f h
  obtain ⟨⟨hℓ, hf1, -⟩, hm⟩ := h
  have hm' : TwistedChevalleyModel X .E6 (ℓ ^ f) := hm
  obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm'
  let q : PrimePower := ⟨ℓ, f, hℓ, hf1⟩
  have hv : (LieTypeIndex.twistedE6 q).Valid := LieTypeIndex.valid_twistedE6 q
  obtain ⟨b⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [PrimePower.card_def]; exact hK) σ (fun x => by rw [PrimePower.card_def]; exact hσ x)
  exact four_le_pRank_three_twistedE6 (e.trans b)

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
