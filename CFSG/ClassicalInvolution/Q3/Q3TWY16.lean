module

public import CFSG.ClassicalInvolution.Q3.Q3TWY15
public import CFSG.ClassicalInvolution.RouteD.TWEB4Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B6 CFSG.ClassicalInvolution.RouteD.TWE.B4
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (exists_noncommuting_pair)
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1


section Spin

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] [FiniteDimensional 𝔽₃ V] {Q : QuadraticForm 𝔽₃ V}

theorem exists_noncommuting_pair_spin3 (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 11 ≤ Module.finrank 𝔽₃ V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ V))
    {R₀ R₁ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair 𝔽₃ W R₀ R₁) :
    ∃ T ∈ 𝓕, ∃ T' ∈ 𝓕, Commutes T R₀ ∧ Commutes T R₁ ∧ Commutes T' R₀ ∧ Commutes T' R₁ ∧
      ¬ Commutes T T' ∧ T ≠ T' := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ h₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ h₁
  have hdata := adj_data hodd (by omega) hi₀ hi₁ (cq.modelAdj h₀ h₁ hadj)
  obtain ⟨W, hW⟩ := hlin
  have hsing := hasSingularVector_of_linearPair3 hi₀ hi₁ hdata.1 hdata.2.1
    hdata.2.2 ⟨_, linearBlockStandardPair_map_central hW _ cq.ker_le⟩
  have hvc : VChain Q 2 (fun a => if a = 0 then R₀.map (spinAction Q) else R₁.map (spinAction Q))
      (fun a => if a = 0 then i₀ else i₁) := by
    refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => ?_⟩
    · rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · exact hi₀
      · exact hi₁
    · obtain rfl : a = 0 := by omega
      exact hdata.1
    · obtain rfl : a = 0 := by omega
      exact hdata.2.1
    · obtain rfl : a = 0 := by omega
      exact hdata.2.2
    · obtain rfl : a = 0 := by omega
      exact hsing
    · exfalso
      omega
  obtain ⟨S, S', hS, hS', hc, hnc, hne⟩ := exists_noncommuting_pair hodd hQ hdim hvc
  obtain ⟨T, hT, rfl⟩ := cq.surj S hS
  obtain ⟨T', hT', rfl⟩ := cq.surj S' hS'
  have c0 := hc 0 (by norm_num)
  have c1 := hc 1 (by norm_num)
  simp only [ite_true, one_ne_zero, ite_false] at c0 c1
  exact ⟨T, hT, T', hT', (cq.commutes_iff hT).mp c0.1, (cq.commutes_iff hT).mp c1.1,
    (cq.commutes_iff hT').mp c0.2, (cq.commutes_iff hT').mp c1.2,
    fun h => hnc ((cq.commutes_iff hT).mpr h), fun h => hne (by rw [h])⟩

end Spin

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem exists_noncommuting_members3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {u}) (hO3 : LocalOddThreeFree3 Ω u)
    (hshape : LocalShapeC3 0 (CompData.model (twinYModel 3 .POmegaOdd 4).1
      (twinYModel 3 .POmegaOdd 4).2) Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember3 K z) (hs : IsClassicalMember3 β s)
    (hKβ : ∃ W, LinearBlockStandardPair 𝔽₃ W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes β N₁ ∧ Commutes K N₂ ∧ Commutes β N₂ ∧ ¬ Commutes N₁ N₂ ∧
        N₁ ≠ N₂ := by
  classical
  have hmod : twinYModel 3 .POmegaOdd 4 = (.POmegaOdd, 5) := by simp [twinYModel]
  rw [hmod] at hshape
  have hadm : StatedLieAdmissible .POmegaOdd 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by norm_num⟩
  have hY := yData3_odd (by norm_num : 3 ≤ 5) hadm
  have : Finite (modelUniv .POmegaOdd 5 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨e⟩ := Layer03.of_shape hΩ hY.sc hK hshape
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have cq := centralQuot3_odd (m := 5) (by norm_num)
  have hQ : (polarBilin (quadOdd 5 𝔽₃)).Nondegenerate := nondegenerate_polarBilin_quadOdd 5 _ h2
  have hdim : 11 ≤ Module.finrank 𝔽₃ (Fin 5 ⊕ Fin 5 ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaOdd 5 3 1 Nat.prime_three).K) R₀ R₁ :=
    e.modelAdj hY hΩ hex hP1 hO3 hK hβ hR₀ hR₁ hKR hβR hz hs
      (ne_of_linearBlockStandardPair hW) (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hY hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T, hT, T', hT', c0, c1, c0', c1', hnc, hne⟩ :=
    exists_noncommuting_pair_spin3 hQ hdim cq hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N, hN, hNT⟩ := e.comp T hT
  obtain ⟨N', hN', hN'T⟩ := e.comp T' hT'
  refine ⟨N, hN, N', hN', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN hK hT hNT hKR).mpr c0)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN hβ hT hNT hβR).mpr c1)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN' hK hT' hN'T hKR).mpr c0')
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN' hβ hT' hN'T hβR).mpr c1')
  · exact fun h => hnc ((e.commutes_iff hY hΩ hex hP1 hO3 hN hN' hT hNT hN'T).mp h)
  · intro h
    refine hne (eq_of_map_eq_of_pow3 e.φ e.ker_le (e.ker_cop hY) (hY.pow3 T hT)
      (hY.pow3 T' hT') ?_)
    rw [← hNT, ← hN'T, h]

end Group

end CFSG.ClassicalInvolution.Q3.Q3TWY
