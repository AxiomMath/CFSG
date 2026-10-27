module

public import CFSG.CharacterTheory.Wreathed.FourPointUnitaryRecognitionCore
public import CFSG.CharacterTheory.Wreathed.FourPointConnectedGraph
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagonSupport

public noncomputable section

namespace CFSG.Wreathed.FourPointUnitaryRecognition

open Equiv Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.GroupTheory.SevenInvolutionWreathLaw
  CFSG.GroupTheory.InvolutionHexagon CFSG.LinearGroups.UnitaryThreeOverNine

open scoped Classical commutatorElement

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

omit [Fintype G] in
theorem isPerfect_of_simple (hnonab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hmem : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
  · exact h

omit [Fintype G] [IsSimpleGroup G] in
theorem incidenceColoring_conjAction (g : G)
    (v : {x : G // orderOf x = 2} ⊕ InvLine G) :
    incidenceColoring (invInc G) (conjAction G g v) = incidenceColoring (invInc G) v := by
  rcases v with p | T <;> rfl

theorem four_point_actual_simple_group_is_unitary_three_over_nine
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    (∀ (F : Type) [Field F], Nat.card F = 9 →
      (StatedSU 3 3 F : Set (GL (Fin 3) F)) =
        {B : GL (Fin 3) F | (B : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
          ((B : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * B = 1} ∧
      Nonempty (G ≃* StatedSU 3 3 F)) ∧
    StatedClassicalModel G .PSU 3 3 1 := by
  obtain ⟨hn2, -, hG, -, -, hcard, hval, -⟩ :=
    FourPointConnectedGraph.four_point_connected_involution_graph_and_trivial_original_odd_core
      hnonab n hn S e alpha
  subst hn2
  have hconj := all_involutions_conjugate_of_simple_wreathed hnonab 2 hn S e
  have : Finite (Wreath (2 ^ 2)) := Nat.finite_of_card_ne_zero (by rw [card_wreath]; norm_num)
  obtain ⟨hlaw, -⟩ := FourPointInvolutionHexagon.localData hconj S e hval
  have H := involutionHexagonData hcard hlaw hval
  have := isPerfect_of_simple hnonab
  have := H.finite_points
  have := H.finite_lines
  have : Fintype ({x : G // orderOf x = 2} ⊕ InvLine G) := Fintype.ofFinite _
  have hcardΔ : Fintype.card ({x : G // orderOf x = 2} ⊕ InvLine G) = 126 := by
    rw [← Nat.card_eq_fintype_card, H.card_vertices]
  obtain ⟨-, hconnΔ, -⟩ := H.hexagon
  have hdegΔ : ∀ v, (incidenceGraph (invInc G)).degree v = 3 := fun v => by
    rw [degree_eq_ncard, H.ncard_neighborSet]
  have key : ∀ (F : Type) [Field F], Nat.card F = 9 → Nonempty (G ≃* StatedSU 3 3 F) :=
    fun F _ hF => nonempty_mulEquiv_statedSU_of_hexagon_action hG (incidenceGraph (invInc G))
      hcardΔ hconnΔ hdegΔ (incidenceColoring (invInc G)) (fun v c hc => H.twelve_le_length c hc)
      (conjAction G) (conjAction_injective hcard hval) incidenceColoring_conjAction hF
  refine ⟨fun F _ hF => ⟨(coe_statedSU hF).trans (Set.ext fun B => And.comm), key F hF⟩, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF9 : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨f⟩ := key (GaloisField 3 2) hF9
  obtain ⟨hadm, K, hK, hKfin, hKcard, ⟨e'⟩⟩ := classicalModel_statedSU hF9
  exact ⟨hadm, K, hK, hKfin, hKcard, ⟨f.trans e'⟩⟩

end CFSG.Wreathed.FourPointUnitaryRecognition
