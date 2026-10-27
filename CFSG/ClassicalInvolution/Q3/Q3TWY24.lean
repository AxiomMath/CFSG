module

public import CFSG.ClassicalInvolution.Q3.Q3TWY16
public import CFSG.ClassicalInvolution.Q3.Q3TWY20
public import CFSG.ClassicalInvolution.Q3.Q3TY34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1


namespace DNodes3

variable {G : Type} [Group G] {m : ℕ} {Ω : Set (Subgroup G)} {K : Subgroup G}
  (nd : DNodes3 m Ω K)

theorem commute_w (h2 : (2 : 𝔽₃) ≠ 0) (a b : Fin m) : Commute (nd.w a) (nd.w b) := by
  by_cases hab : a = b
  · subst hab
    exact Commute.refl _
  by_cases hadj : DAdj a b
  · obtain ⟨W, hW⟩ := nd.pair_of_adj hadj
    exact standardPair_involutions_commute h2 hW (nd.cl a).mem (nd.cl b).mem
      (nd.cl a).orderOf_eq_two (nd.cl b).orderOf_eq_two
  · exact (nd.commutes_of_not_adj hab hadj) _ (nd.cl a).mem _ (nd.cl b).mem

theorem conjSub_w (h2 : (2 : 𝔽₃) ≠ 0) {a b : Fin m} (h : DAdj a b) :
    conjSub (nd.w b) (nd.J a) = nd.J a := by
  obtain ⟨W, hW⟩ := nd.pair_of_adj h
  exact conjSub_eq_of_standardPair h2 hW (nd.cl b).mem (nd.cl b).orderOf_eq_two

end DNodes3

section Spin

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] [FiniteDimensional 𝔽₃ V]
  {Q : QuadraticForm 𝔽₃ V}

theorem exists_bridges_spin3 (hQ : (polarBilin Q).Nondegenerate) {u : ℕ}
    (hdim : 2 * (u + 3) + 7 ≤ Module.finrank 𝔽₃ V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ V))
    (hF : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕,
      (∃ W, LinearBlockStandardPair 𝔽₃ W (R₁.map (spinAction Q)) (R₂.map (spinAction Q))) →
        ∃ W, LinearBlockStandardPair 𝔽₃ W R₁ R₂)
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ u + 3, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕)
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair 𝔽₃ W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3)) :
    ∃ T₁ ∈ 𝓕, ∃ T₂ ∈ 𝓕, (∀ a < u + 3, Commutes T₁ (R a) ∧ Commutes T₂ (R a)) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W (R (u + 3)) T₁) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W Rtw T₁) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W (R (u + 3)) T₂) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W Rtw T₂) ∧ ¬ Commutes T₁ T₂ ∧ T₁ ≠ T₂ := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hdim9 : 9 ≤ Module.finrank 𝔽₃ V := by omega
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen3 hdim9 cq hRf hRtwf hadj hcomm hadjtw hcommtw
    hcommtw'
  have hex : ∀ a, ∃ i, a ≤ u + 3 → IsFundamental Q ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ u + 3
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < u + 3, ModelAdj (scalars 𝔽₃ V) ((R a).map (spinAction Q))
      ((R (a + 1)).map (spinAction Q)) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hdata : ∀ a < u + 3, i a * i (a + 1) = i (a + 1) * i a ∧
      i (a + 1) ∈ Subgroup.normalizer (((R a).map (spinAction Q) : Subgroup _) : Set _) ∧
      i (a + 1) ∉ Subgroup.centralizer (((R a).map (spinAction Q) : Subgroup _) : Set _) :=
    fun a ha => adj_data hodd hdim9 (hi a (by omega)) (hi (a + 1) (by omega)) (hadjV a ha)
  have hVchain : VChain Q (u + 3 + 1) (fun a => (R a).map (spinAction Q)) i := by
    refine ⟨fun a ha => hi a (by omega), fun a ha => (hdata a (by omega)).1,
      fun a ha => (hdata a (by omega)).2.1, fun a ha => (hdata a (by omega)).2.2, fun a ha => ?_,
      fun a b hab hb x hx y hy => ?_⟩
    · obtain ⟨W, hW⟩ := hlin a (by omega)
      exact hasSingularVector_of_linearPair3 (hi a (by omega)) (hi (a + 1) (by omega))
        (hdata a (by omega)).1 (hdata a (by omega)).2.1 (hdata a (by omega)).2.2
        ⟨_, linearBlockStandardPair_map_central hW _ cq.ker_le⟩
    · have hcV := (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))
      rcases orth_or_twin hodd (hi a (by omega)) (hi b (by omega)) hcV with h | h
      · exact h x hx y hy
      · exact absurd h.symm (hdist a b hab (by omega) _ _ (hi a (by omega)) (hi b (by omega)))
  have h5 : IsFundamental Q (Rtw.map (spinAction Q)) (i (u + 3)) :=
    htwin (i (u + 3)) itw (hi (u + 3) le_rfl) hitw ▸ hitw
  have hne' : Rtw.map (spinAction Q) ≠ (R (u + 3)).map (spinAction Q) := fun h =>
    hne (cq.map_inj hRtwf (hRf (u + 3) le_rfl) h)
  obtain ⟨S₁, S₂, hS₁, hS₂, hc, s₁, t₁, s₂, t₂, hnc, hne12⟩ :=
    exists_bridges_gen hodd hQ (by omega : 1 ≤ u + 3) hdim hVchain h5 hne'
  obtain ⟨T₁, hT₁, rfl⟩ := cq.surj S₁ hS₁
  obtain ⟨T₂, hT₂, rfl⟩ := cq.surj S₂ hS₂
  refine ⟨T₁, hT₁, T₂, hT₂, fun a ha => ⟨?_, ?_⟩, hF _ (hRf (u + 3) le_rfl) _ hT₁ ⟨_, s₁⟩,
    hF _ hRtwf _ hT₁ ⟨_, t₁⟩, hF _ (hRf (u + 3) le_rfl) _ hT₂ ⟨_, s₂⟩, hF _ hRtwf _ hT₂ ⟨_, t₂⟩,
    ?_, ?_⟩
  · exact (cq.commutes_iff hT₁).mp (hc a ha).1
  · exact (cq.commutes_iff hT₂).mp (hc a ha).2
  · exact fun h => hnc ((cq.commutes_iff hT₁).mpr h)
  · exact fun h => hne12 (by rw [h])

end Spin

end CFSG.ClassicalInvolution.Q3.Q3TWY
