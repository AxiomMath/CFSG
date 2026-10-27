module

public import CFSG.ClassicalInvolution.Q3.Q3TWY5
public import CFSG.ClassicalInvolution.Q3.Q3TY18
public import CFSG.ClassicalInvolution.RouteD.TWEB3PLeaf

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
open CFSG.ClassicalInvolution.RouteD.TWE.B3 (exists_leaf_pair_three)
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1


section Model

variable {V : Type} [AddCommGroup V] [Module 𝔽₃ V] [FiniteDimensional 𝔽₃ V] {Q : QuadraticForm 𝔽₃ V}

theorem exists_leaf_spin_three3 (hdim : 9 ≤ Module.finrank 𝔽₃ V)
    (hQ : (polarBilin Q).Nondegenerate) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars 𝔽₃ V))
    (hF : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕,
      (∃ W, LinearBlockStandardPair 𝔽₃ W (R₁.map (spinAction Q)) (R₂.map (spinAction Q))) →
        ∃ W, LinearBlockStandardPair 𝔽₃ W R₁ R₂)
    {R₀ R₁ : Subgroup (spinGroup Q)} (h₀ : R₀ ∈ 𝓕) (h₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair 𝔽₃ W R₀ R₁) :
    ∃ T₁ ∈ 𝓕, ∃ T₂ ∈ 𝓕, Commutes T₁ R₀ ∧ Commutes T₂ R₀ ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W R₁ T₁) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W R₁ T₂) ∧ T₁ ≠ T₂ := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ h₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ h₁
  have hdata := adj_data hodd hdim hi₀ hi₁ (cq.modelAdj h₀ h₁ hadj)
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
  obtain ⟨S₁, S₂, hS₁, hS₂, c₁, c₂, s₁, s₂, hne⟩ := exists_leaf_pair_three hodd hQ hdim hvc
  obtain ⟨T₁, hT₁, rfl⟩ := cq.surj S₁ hS₁
  obtain ⟨T₂, hT₂, rfl⟩ := cq.surj S₂ hS₂
  exact ⟨T₁, hT₁, T₂, hT₂, (cq.commutes_iff hT₁).mp c₁, (cq.commutes_iff hT₂).mp c₂,
    hF R₁ h₁ T₁ hT₁ ⟨_, s₁⟩, hF R₁ h₁ T₂ hT₂ ⟨_, s₂⟩, fun h => hne (by rw [h])⟩

end Model

section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem exists_leaf_b3_3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {u}) (hO3 : LocalOddThreeFree3 Ω u)
    (hshape : LocalShapeC3 0 (CompData.model (twinYModel 3 .POmegaOdd 3).1
      (twinYModel 3 .POmegaOdd 3).2) Ω u) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {u}) (hβ : β ∈ centralizingMembers Ω {u})
    (hz : IsClassicalMember3 K z) (hs : IsClassicalMember3 β s)
    (hKβ : ∃ W, LinearBlockStandardPair 𝔽₃ W K β) :
    ∃ N₁ ∈ centralizingMembers Ω {u}, ∃ N₂ ∈ centralizingMembers Ω {u},
      Commutes K N₁ ∧ Commutes K N₂ ∧ (∃ W, LinearBlockStandardPair 𝔽₃ W β N₁) ∧
      (∃ W, LinearBlockStandardPair 𝔽₃ W β N₂) ∧ N₁ ≠ N₂ := by
  classical
  have hmod : twinYModel 3 .POmegaOdd 3 = (.POmegaOdd, 4) := by simp [twinYModel]
  rw [hmod] at hshape
  have hadm : StatedLieAdmissible .POmegaOdd 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by norm_num⟩
  have hY := yData3_odd (by norm_num : 3 ≤ 4) hadm
  have : Finite (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨e⟩ := Layer03.of_shape hΩ hY.sc hK hshape
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have cq := centralQuot3_odd (m := 4) (by norm_num)
  have hQ : (polarBilin (quadOdd 4 𝔽₃)).Nondegenerate := nondegenerate_polarBilin_quadOdd 4 _ h2
  have hdim : 9 ≤ Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 ⊕ Unit → 𝔽₃) := by
    rw [finrank_odd]
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaOdd 4 3 1 Nat.prime_three).K) R₀ R₁ :=
    e.modelAdj hY hΩ hex hP1 hO3 hK hβ hR₀ hR₁ hKR hβR hz hs
      (ne_of_linearBlockStandardPair hW) (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hY hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T₁, hT₁, T₂, hT₂, c₁, c₂, p₁, p₂, hne⟩ := exists_leaf_spin_three3 hdim hQ cq
    (fun A hA B hB hl => exists_lin_of_map3' (not_three_dvd_card_center' hY.cop)
      (spinAction _) (ker_spinAction_le_center _) (hY.pow3 A hA) (hY.pow3 B hB) hl)
    hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨N₁, hN₁, hN₁T⟩ := e.comp T₁ hT₁
  obtain ⟨N₂, hN₂, hN₂T⟩ := e.comp T₂ hT₂
  obtain ⟨W₁, hW₁⟩ := p₁
  obtain ⟨W₂, hW₂⟩ := p₂
  refine ⟨N₁, hN₁, N₂, hN₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN₁ hK hT₁ hN₁T hKR).mpr c₁)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN₂ hK hT₂ hN₂T hKR).mpr c₂)
  · exact e.pair_of_model hΩ hex hP1 hO3 hβ hN₁ hβR hN₁T hW₁
  · exact e.pair_of_model hΩ hex hP1 hO3 hβ hN₂ hβR hN₂T hW₂
  · intro h
    refine hne (eq_of_map_eq_of_pow3 e.φ e.ker_le (e.ker_cop hY) (hY.pow3 T₁ hT₁)
      (hY.pow3 T₂ hT₂) ?_)
    rw [← hN₁T, ← hN₂T, h]

end Group

end CFSG.ClassicalInvolution.Q3.Q3TWY
