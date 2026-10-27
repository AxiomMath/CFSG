module

public import CFSG.ClassicalInvolution.Q3.Sec13End15A
import CFSG.ClassicalInvolution.Q3.TL3T28

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem e15b_four_le {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {U : Subgroup G}
    (hU : U ∈ USet Ω) : 4 ≤ Nat.card ↥U := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  exact h4

private theorem e15b_involution_mem {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {K U : Subgroup G}
    {z : G} (hz : IsUniqueInvolution K z) (hU : U ∈ USet Ω) (hUK : U ≤ K) : z ∈ U :=
  hz.mem_of_le hUK (Sec6Gen.isPGroup_of_mem_USet hΩ hU)
    (by have := e15b_four_le hΩ hU; omega)

private theorem e15b_uset_of_mem_eta {Ω : Set (Subgroup G)} {η : Set (Subgroup G)}
    (hη : η ∈ etaG Ω) {V : Subgroup G} (hV : V ∈ η) : V ∈ USet Ω := by
  obtain ⟨S₀, hS₀, -⟩ := hη
  exact (hS₀.1 hV).1

private theorem e15b_isSylow2In_self {K : Subgroup G} (hK : IsPGroup 2 K) : IsSylow2In K K :=
  ⟨le_rfl, hK, fun _ hV' _ hKV' => le_antisymm hV' hKV'⟩

namespace EndHyp

variable {Ω : Set (Subgroup G)}

theorem exists_wSet_of_mem_omegaStarNbr (h : EndHyp Ω) {K J : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hz : IsUniqueInvolution K z) :
    ∃ W ∈ WSet Ω, z ∈ W ∧ K ∈ DSet Ω W ∧ J ∈ DSet Ω W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := h.thmD.hyp
  obtain ⟨hJΩ, -, U, hU, hUJ, hUK⟩ := hJ
  obtain ⟨S, hS⟩ := ((Sec6Gen.isPGroup_of_mem_USet hΩ hU).to_sup_of_normal_right'
    (h.thmD.two K hK) hUK).exists_le_sylow
  have hKS : K ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hUS : U ≤ (S : Subgroup G) := le_sup_left.trans hS
  obtain ⟨η, hη, hηS, -, hKη⟩ := h.exists_wSet_of_le hK S hKS
  have hW : (⨆ V ∈ η, V) ∈ WSet Ω := ⟨η, hη, rfl⟩
  have hzW : z ∈ (⨆ V ∈ η, V) :=
    (e15b_involution_mem hΩ hz (e15b_uset_of_mem_eta hη hKη) inf_le_left).2
  have hJη : J ⊓ (⨆ V ∈ η, V) ∈ η := Sec6Gen.l6_11Gen G Ω hΩ S η hη hηS J hJΩ (by
    have := Subgroup.card_le_of_le (le_inf hUJ hUS)
    have := e15b_four_le hΩ hU
    omega)
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJΩ
  have htW : t ∈ (⨆ V ∈ η, V) :=
    (e15b_involution_mem hΩ ht (e15b_uset_of_mem_eta hη hJη) inf_le_left).2
  exact ⟨⨆ V ∈ η, V, hW, hzW, h.mem_dSet_of_mem hW hK hz hzW,
    h.mem_dSet_of_mem hW hJΩ ht htW⟩

theorem twin_le_oTwoCore (h : EndHyp Ω) {K K' : Subgroup G} {z : G} (s : TwinSit Ω K K' z) :
    K ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) ∧
      K' ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  have hK' : K' ∈ twinSet Ω K := by
    rw [s.twin]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨hK'Ω, z', hzK, hzK'⟩ := hK'
  have hz' : z' = z := (s.isInv.eq hzK).symm
  rw [hz'] at hzK'
  exact ⟨TC.Thin.le_pCoreOf_centralizer h.thmD.hyp h.thmD.two s.mem s.isInv,
    TC.Thin.le_pCoreOf_centralizer h.thmD.hyp h.thmD.two hK'Ω hzK'⟩

theorem exists_choice (h : EndHyp Ω) (h9 : Perp9 Ω) {K K' : Subgroup G} {z : G}
    (s : TwinSit Ω K K' z) :
    ∃ W ∈ WSet Ω, z ∈ W ∧ K ∈ DSet Ω W ∧
      ∃ J ∈ Ω, J ∈ DSet Ω W ∧ J ∈ omegaStarNbr Ω K ∧ J ∉ twinSet Ω K ∧
        ∃ U ∈ USet Ω, U ≤ J ∧ U ≤ W ∧
          ¬ U ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := h.thmD.hyp
  obtain ⟨W, hW, hzW, -, U, hU, hUW, hUO⟩ := h.exists_wSet_uSet_not_le s.mem s.isInv
  obtain ⟨R, -, J, hJ, hRJ, hUR, -, -, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  have hUJ : U ≤ J := hUR.trans hRJ.1
  have hKO := (h.twin_le_oTwoCore s).1
  have hK'O := (h.twin_le_oTwoCore s).2
  have hJO : ¬ J ≤ oTwoCore (Subgroup.centralizer ({z} : Set G)) :=
    fun hle => hUO (hUJ.trans hle)
  have hJtw : J ∉ twinSet Ω K := by
    intro hJt
    rw [s.twin, Set.mem_insert_iff, Set.mem_singleton_iff] at hJt
    rcases hJt with h1 | h1
    · exact hJO (by rw [h1]; exact hKO)
    · exact hJO (by rw [h1]; exact hK'O)
  have hJK : K ≠ J := by
    intro e
    apply hJtw
    rw [← e]
    exact ⟨s.mem, z, s.isInv, s.isInv⟩
  have hKd : K ∈ DSet Ω W := h.mem_dSet_of_mem hW s.mem s.isInv hzW
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hJd : J ∈ DSet Ω W :=
    h.mem_dSet_of_mem hW hJ ht (hUW (e15b_involution_mem hΩ ht hU hUJ))
  have hJs : J ∈ omegaStarNbr Ω K :=
    (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hW s.mem hJ hJK hKd hJd
      (e15b_isSylow2In_self (h.thmD.two K s.mem)) (e15b_isSylow2In_self (h.thmD.two J hJ))).1
  exact ⟨W, hW, hzW, hKd, J, hJ, hJd, hJs, hJtw, U, hU, hUJ, hUW, hUO⟩

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
