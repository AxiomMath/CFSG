module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutCount
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsSd16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsSylowConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsAutCard

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L33 CFSG.Sporadic.Schreier CFSG.Blueprint

namespace IsL33Model

variable {L : Type} [Group L] {M : AutModel L (Equiv.Perm (Fin 26))}

theorem exists_conj_z_y (h : IsL33Model M) : ∃ a : L, a * h.elX ^ 4 * a⁻¹ = h.elY := by
  obtain ⟨a, ha⟩ :=
    (liftA_inner_iff M h.P_le_A h.modelG1_mem_A).2
      (by rw [h.P_eq]; exact model_inner_mem.2.2.1)
  refine ⟨a, ?_⟩
  have hz := ha (h.elX ^ 4)
  rw [← h.elG1_z]
  exact hz.symm

end IsL33Model

variable {L : Type} [Group L]

theorem l33_involutions_conj (hL : LieModel L .PSL 3 3 1)
    {u v : L} (hu : u ^ 2 = 1) (hu1 : u ≠ 1) (hv : v ^ 2 = 1) (hv1 : v ≠ 1) : IsConj u v := by
  obtain ⟨M, h⟩ := exists_isL33Model hL
  haveI : Finite L := Nat.finite_of_card_ne_zero (by rw [l33_card_L hL]; norm_num)
  let S : Subgroup L := Subgroup.closure ({h.elX, h.elY} : Set L)
  have hcardS : Nat.card S = 16 := h.card_closure_elXY
  have hidx_eq : S.index = 351 := by
    have hc := Subgroup.card_mul_index S
    rw [hcardS, l33_card_L hL] at hc
    omega
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 4) (by rw [hcardS]; norm_num)
  have hidx : ¬ 2 ∣ S.index := by rw [hidx_eq]; norm_num
  have hzy : IsConj h.elY (h.elX ^ 4) := by
    obtain ⟨a, ha⟩ := h.exists_conj_z_y
    exact (isConj_iff.mpr ⟨a, ha⟩).symm
  have key : ∀ {w : L}, w ^ 2 = 1 → w ≠ 1 → IsConj w (h.elX ^ 4) := by
    intro w hw2 hw1
    obtain ⟨g, hgw⟩ := exists_conj_mem_of_sylow_two hS hidx hw2
    set w' : L := g * w * g⁻¹ with hw'
    have hw'S : w' ∈ S := by rw [hw']; exact hgw
    have hw'2 : w' ^ 2 = 1 := by rw [hw', conj_pow, hw2]; group
    have hw'1 : w' ≠ 1 := by
      rw [hw']
      intro h1
      apply hw1
      calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [h1]
        _ = 1 := by group
    have hw'conj : IsConj w w' := isConj_iff.mpr ⟨g, by rw [hw']⟩
    rcases sd16_involution_isConj h.elX_pow_eight h.elX_pow_four_ne_one h.elY_sq h.elY_conj
      hw'S hw'2 hw'1 with hcase | hcase
    · exact hw'conj.trans hcase
    · exact hw'conj.trans (hcase.trans hzy)
  exact (key hu hu1).trans (key hv hv1).symm

end CFSG.OddStandard.SmallF3.L33
