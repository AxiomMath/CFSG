module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Bridge
public import CFSG.ClassicalInvolution.RouteD.GapsFrBGen

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Spin

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

theorem exists_bridges_spin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 15 ≤ Module.finrank (GaloisField p f) V)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    (hF : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕,
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (R₁.map (spinAction Q))
        (R₂.map (spinAction Q))) → ∃ W, LinearBlockStandardPair (GaloisField p f) W R₁ R₂)
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ 4, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕)
    (hadj : ∀ a < 4, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 4, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 4 → Commutes (R a) (R b))
    (hadjtw : ModelAdj (Subgroup.center _) (R 3) Rtw) (hcommtw : ∀ a, a ≤ 2 → Commutes (R a) Rtw)
    (hcommtw' : Commutes (R 4) Rtw) (hne : Rtw ≠ R 4) :
    ∃ T₁ ∈ 𝓕, ∃ T₂ ∈ 𝓕, (∀ a < 4, Commutes T₁ (R a) ∧ Commutes T₂ (R a)) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (R 4) T₁) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W Rtw T₁) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (R 4) T₂) ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W Rtw T₂) ∧ ¬ Commutes T₁ T₂ ∧ T₁ ≠ T₂ := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim9 : 9 ≤ Module.finrank (GaloisField p f) V := by omega
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen (u := 1) hp2 hq hdim9 cq hRf hRtwf hadj hcomm
    hadjtw hcommtw hcommtw'
  have hex : ∀ a, ∃ i, a ≤ 4 → IsFundamental Q ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ 4
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < 4, ModelAdj (scalars (GaloisField p f) V) ((R a).map (spinAction Q))
      ((R (a + 1)).map (spinAction Q)) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hdata : ∀ a < 4, i a * i (a + 1) = i (a + 1) * i a ∧
      i (a + 1) ∈ Subgroup.normalizer (((R a).map (spinAction Q) : Subgroup _) : Set _) ∧
      i (a + 1) ∉ Subgroup.centralizer (((R a).map (spinAction Q) : Subgroup _) : Set _) :=
    fun a ha => adj_data hodd hdim9 (hi a (by omega)) (hi (a + 1) (by omega)) (hadjV a ha)
  have hVchain : VChain Q 5 (fun a => (R a).map (spinAction Q)) i := by
    refine ⟨fun a ha => hi a (by omega), fun a ha => (hdata a (by omega)).1,
      fun a ha => (hdata a (by omega)).2.1, fun a ha => (hdata a (by omega)).2.2, fun a ha => ?_,
      fun a b hab hb x hx y hy => ?_⟩
    · obtain ⟨W, hW⟩ := hlin a (by omega)
      exact hasSingularVector_of_linearPair hp2 (by omega) (hi a (by omega))
        (hi (a + 1) (by omega)) (hdata a (by omega)).1 (hdata a (by omega)).2.1
        (hdata a (by omega)).2.2 ⟨_, linearBlockStandardPair_map_central hW _ cq.ker_le⟩
    · have hcV := (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))
      rcases orth_or_twin hodd (hi a (by omega)) (hi b (by omega)) hcV with h | h
      · exact h x hx y hy
      · exact absurd h.symm (hdist a b hab (by omega) _ _ (hi a (by omega)) (hi b (by omega)))
  have h5 : IsFundamental Q (Rtw.map (spinAction Q)) (i 4) :=
    htwin (i 4) itw (hi 4 le_rfl) hitw ▸ hitw
  have hne' : Rtw.map (spinAction Q) ≠ (R 4).map (spinAction Q) := fun h =>
    hne (cq.map_inj hRtwf (hRf 4 le_rfl) h)
  obtain ⟨S₁, S₂, hS₁, hS₂, hc, s₁, t₁, s₂, t₂, hnc, hne12⟩ :=
    exists_bridges hodd hQ hdim hVchain h5 hne'
  obtain ⟨T₁, hT₁, rfl⟩ := cq.surj S₁ hS₁
  obtain ⟨T₂, hT₂, rfl⟩ := cq.surj S₂ hS₂
  have lift : ∀ {A B : Subgroup (spinGroup Q)}, A ∈ 𝓕 → B ∈ 𝓕 →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W (A.map (spinAction Q))
        (B.map (spinAction Q))) → ∃ W, LinearBlockStandardPair (GaloisField p f) W A B :=
    fun hA hB h => hF _ hA _ hB h
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha => ⟨?_, ?_⟩, lift (hRf 4 le_rfl) hT₁ ⟨_, s₁⟩,
    lift hRtwf hT₁ ⟨_, t₁⟩, lift (hRf 4 le_rfl) hT₂ ⟨_, s₂⟩, lift hRtwf hT₂ ⟨_, t₂⟩, ?_, ?_⟩
  · exact (cq.commutes_iff hT₁).mp (hc a ha).1
  · exact (cq.commutes_iff hT₂).mp (hc a ha).2
  · exact fun h => hnc ((cq.commutes_iff hT₁).mpr h)
  · exact fun h => hne12 (by rw [h])

end Spin

end CFSG.ClassicalInvolution.RouteD.TWE.B6
