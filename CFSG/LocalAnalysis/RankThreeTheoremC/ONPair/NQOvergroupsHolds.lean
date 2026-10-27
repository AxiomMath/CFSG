module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.NQOrbits
public import Certificates.Certificate753521

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

open CFSG.ONSchreier CFSG.HardMathSupport.Dickson.I271


theorem isCoatom_G2 : IsCoatom G2 := by
  rw [G2, Subgroup.isCoatom_comap]
  exact isCoatom_lineStab _

theorem M1_inf_G2 : M1 ⊓ G2 = Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) := by
  obtain ⟨g, n, m, u, hF⟩ := Certificates.certificate753521
  rcases eq_normalizer_or_eq card_on7F0 card_M1 card_normalizer_on7F0 normalizer_on7F0_le_M1
      noInvariantPlane_on7F0 (le_inf normalizer_on7F0_le_M1 normalizer_on7F0_le_G2)
      inf_le_left with h | h
  · exact h
  · exact absurd (inf_eq_left.1 h (nqM_mem m 1)) (nqM_one_not_mem_G2 (g := g) (n := n) (u := u) hF)

theorem inf_eq_normalizer_of_not_le {W Y : Subgroup Pv} (hY : IsCoatom Y)
    (hcard : Nat.card Y = 3753792)
    (hNY : Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) ≤ Y)
    (hNW : Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) ≤ W) (hW : W ≠ ⊤)
    (hWY : ¬ W ≤ Y) : W ⊓ Y = Subgroup.normalizer ((on7F 0 : Subgroup Pv) : Set Pv) := by
  rcases eq_normalizer_or_eq card_on7F0 hcard card_normalizer_on7F0 hNY noInvariantPlane_on7F0
      (le_inf hNW hNY) inf_le_right with h | h
  · exact h
  · rcases hY.le_iff.1 (inf_eq_right.1 h) with h' | h'
    · exact absurd h' hW
    · exact absurd h'.le hWY

theorem onanNQOvergroups_holds : OnanNQOvergroups := by
  intro W hNW hW
  obtain ⟨g, n, m, u, hF⟩ := Certificates.certificate753521
  have hIW : M1 ⊓ G2 ≤ W := by
    rw [M1_inf_G2]
    exact hNW
  rw [onanM_one_eq, onanM_two_eq]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hW1 := inf_eq_normalizer_of_not_le (isCoatom_lineStab 0) card_M1 normalizer_on7F0_le_M1
    hNW hW h1
  have hW2 := inf_eq_normalizer_of_not_le isCoatom_G2 card_G2 normalizer_on7F0_le_G2 hNW hW h2
  obtain ⟨w, hwW, hwM⟩ := Set.not_subset.1 h1
  obtain ⟨a, ha, c, hc, hca⟩ := nq_orbit hF (lineAct w 0)
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hwM
    rw [SetLike.mem_coe, mem_M1, ← hca, mem_M1.1 (nqG_zero_mem hF), mem_M1.1 hc.1]
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hmM : (nqG g (a' + 1))⁻¹ * c⁻¹ * w ∈ M1 := by
    rw [mem_M1, map_mul, map_mul, map_inv, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ← hca]
    simp
  obtain ⟨i, hi, hmi⟩ := nq_orbit_two hF hmM
  have hk : (nqM m i)⁻¹ * ((nqG g (a' + 1))⁻¹ * c⁻¹ * w) ∈ M1 ⊓ G2 := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (nqM_mem m i)) hmM, ?_⟩
    rw [mem_G2, map_mul, map_inv, Equiv.Perm.mul_apply, hmi]
    simp
  have hγ : nqGamma g m a' i ∈ W := by
    have e : nqGamma g m a' i =
        c⁻¹ * w * ((nqM m i)⁻¹ * ((nqG g (a' + 1))⁻¹ * c⁻¹ * w))⁻¹ := by
      rw [nqGamma]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hIW hc)) hwW) (inv_mem (hIW hk))
  have huW := nqU_mem hF hIW hγ
  rcases nqU_wit hF (a := a') (by omega) hi with ⟨hu1, hu2⟩ | ⟨hu2, hu1⟩
  · exact hu2 (normalizer_on7F0_le_G2 (hW1 ▸ ⟨huW, hu1⟩))
  · exact hu1 (normalizer_on7F0_le_M1 (hW2 ▸ ⟨huW, hu2⟩))

end CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

end
