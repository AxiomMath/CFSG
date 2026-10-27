module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalAFrame

public section

open CFSG.Open
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaGlobal

open SectionSix DeltaLocal.Five

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem oddCore_le_core (hC : Counterexample G D r Abar) (i : Fin r) :
    (CFSG.oddCore (aschbacherThm5Preimage D (Abar i))).map
        (aschbacherThm5Preimage D (Abar i)).subtype ≤ aschbacherThm5Core D := by
  set A := aschbacherThm5Preimage D (Abar i)
  have hDA : D ≤ Subgroup.normalizer (A : Set G) := le_normalizer_factor hC i
  have : (CFSG.oddCore A).Characteristic := CFSG.ComponentClassification.OddCore.characteristic A
  refine SectionSix.Strong.le_core_of_odd ((Subgroup.map_subtype_le _).trans (preimage_le D _))
    (fun d hd => AschbacherTheorem3.mem_normalizer_map_of_characteristic (CFSG.oddCore A)
      (hDA hd)) ?_
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact AschbacherTheorem3.odd_card_oddCore A

theorem false_of_weaklyClosed_U (hloc : SectionSixLocalResults)
    (hC : Counterexample G D r Abar) {a : Fin r} (d : DeltaDatum D Abar a)
    (hclosed : ∀ c ∈ aschbacherThm5Preimage D (Abar a),
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c ≤
        d.S ⊔ AschbacherTheorem3.omegaOne d.T →
      rightConjugate (AschbacherTheorem3.omegaOne d.T) c = AschbacherTheorem3.omegaOne d.T) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := aschbacherThm5Preimage D (Abar a) with hAdef
  set U := AschbacherTheorem3.omegaOne d.T with hUdef
  have hF := frame_U hC d
  have hsyl : IsSylowOf 2 (d.S ⊔ U) (A ⊔ U) := by
    have h2 := AschbacherTheorem3.isSylowOf_sup_of_frame hF d.sylowS EndHyp.U_le_normalizer_S
    rwa [sup_comm] at h2
  have h42 := AschbacherTheorem3.lemma_4_2_oddCore
    (⟨hF, hsyl, le_sup_right, hclosed⟩ : AschbacherTheorem3.Hyp42 A U (d.S ⊔ U))
  have hle := h42.trans (oddCore_le_core hC a)
  have hU4 : 4 ≤ Nat.card U := four_le_card_U hloc hC d
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU1
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  apply not_centralizes_of_mem_conj hC a (datum_g_not_mem d)
    (twoElt_of_mem (d.sylowT.isPGroup.to_le EndHyp.U_le_T) hu) hu1' (EndHyp.U_le_L hu)
  intro x hx
  have hmem : ⁅u⁻¹, x⁻¹⁆ ∈ ⁅A, U⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (U.inv_mem hu) (A.inv_mem hx)
  have h1 := hle hmem
  rw [commutatorElement_def] at h1
  simpa using h1

end DeltaGlobal

end CFSG.ComponentClassification.AschbacherTheorem5
