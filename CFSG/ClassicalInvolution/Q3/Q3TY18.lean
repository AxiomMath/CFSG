module

public import CFSG.ClassicalInvolution.Q3.Q3TY10
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.RouteD.TwinYStatements
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType
open CFSG.ClassicalInvolution.RouteD.TwinY (twinYModel)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


variable {tY : StatedLieTag} {nY : ℕ}

theorem Layer03.modelAdj (e : Layer03 Ω x tY nY) (hY : YData3 tY nY) (hΩ : InClass3 Ω)
    (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR : R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {w w' : G}
    (hw : IsClassicalMember3 L w) (hw' : IsClassicalMember3 L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    ModelAdj (Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ := e.modelInvComm hY hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (locImg_injOn3 hΩ hex hP1 hO3 hL hL' (by rw [hLR, hLR', h])), ?_, r, r',
    hr, hr', hcen, ?_⟩
  · intro h
    exact hnc ((e.commutes_iff hY hΩ hex hP1 hO3 hL hL' hR hLR hLR').mpr h)
  · intro y hy
    have h := e.conjSub_eq hY hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN
    rw [← h]
    exact ⟨y, hy, rfl⟩

theorem exists_chain_members_td4_3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (hshape : LocalShapeC3 0 (CompData.model (twinYModel 3 .POmegaMinus 4).1
      (twinYModel 3 .POmegaMinus 4).2) Ω x) {K β : Subgroup G} {z s : G}
    (hK : K ∈ centralizingMembers Ω {x}) (hβ : β ∈ centralizingMembers Ω {x})
    (hz : IsClassicalMember3 K z) (hs : IsClassicalMember3 β s)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) :
    ∃ J₁ ∈ centralizingMembers Ω {x}, ∃ N ∈ centralizingMembers Ω {x},
      Commutes K J₁ ∧ (∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J₁) ∧
      Commutes K N ∧ Commutes β N ∧
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W J₁ N := by
  classical
  have hmod : twinYModel 3 .POmegaMinus 4 = (.POmegaPlus, 5) := by simp [twinYModel]
  rw [hmod] at hshape
  have hadm : StatedLieAdmissible .POmegaPlus 5 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hY := yData3_plus (by norm_num : 4 ≤ 5) hadm
  have : Finite (modelUniv .POmegaPlus 5 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  obtain ⟨e⟩ := Layer03.of_shape hΩ hY.sc hK hshape
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨R₀, hR₀, hKR⟩ := e.mem K hK
  obtain ⟨R₁, hR₁, hβR⟩ := e.mem β hβ
  obtain ⟨W, hW⟩ := hKβ
  have hadjR : ModelAdj (Subgroup.center (modelUniv .POmegaPlus 5 3 1 Nat.prime_three).K) R₀ R₁ :=
    e.modelAdj hY hΩ hex hP1 hO3 hK hβ hR₀ hR₁ hKR hβR hz hs
      (ne_of_linearBlockStandardPair hW) (not_commutes_of_linearBlockStandardPair hW)
      (standardPair_involutions_commute h2 hW hz.mem hs.mem hz.orderOf_eq_two hs.orderOf_eq_two)
      (conjSub_eq_of_standardPair h2 hW hs.mem hs.orderOf_eq_two)
  obtain ⟨W', hW'⟩ := e.pair_to_model hY hP1 hK hβ hR₀ hR₁ hKR hβR hW
  obtain ⟨T₁, hT₁, T₂, hT₂, c10, ⟨W₁, hW₁⟩, c20, c21, ⟨W₂, hW₂⟩⟩ :=
    exists_chain_spin_plus3 hR₀ hR₁ hadjR ⟨W', hW'⟩
  obtain ⟨J₁, hJ₁, hJ₁T⟩ := e.comp T₁ hT₁
  obtain ⟨N, hN, hNT⟩ := e.comp T₂ hT₂
  refine ⟨J₁, hJ₁, N, hN, ?_, ?_, ?_, ?_, ?_⟩
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hJ₁ hK hT₁ hJ₁T hKR).mpr c10)
  · exact e.pair_of_model hΩ hex hP1 hO3 hβ hJ₁ hβR hJ₁T hW₁
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN hK hT₂ hNT hKR).mpr c20)
  · exact commutes_symm ((e.commutes_iff hY hΩ hex hP1 hO3 hN hβ hT₂ hNT hβR).mpr c21)
  · exact e.pair_of_model hΩ hex hP1 hO3 hJ₁ hN hJ₁T hNT hW₂

end Layer

end CFSG.ClassicalInvolution.Q3.Q3TY
