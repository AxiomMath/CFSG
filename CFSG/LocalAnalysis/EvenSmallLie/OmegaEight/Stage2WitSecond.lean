module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def secondCheckW (E : Enum) (tK uK n : ℕ) (B : ℕ → List ℕ) (Y Z : ℕ → ℕ) : Bool :=
  (List.range E.keys.size).all fun i => mulK (E.keys.getD i 0) (E.keys.getD i 0) != idK ||
    E.keys.getD i 0 == idK ||
    (decide (8 ≤ (B i).length) && fixLB (E.keys.getD i 0) (B i)) ||
    decide (commCount E (E.keys.getD i 0) < n) ||
    (decide (Y i < E.keys.size) &&
      mulK (E.keys.getD (Y i) 0) tK == mulK (E.keys.getD i 0) (E.keys.getD (Y i) 0)) ||
    (decide (Z i < E.keys.size) &&
      mulK (E.keys.getD (Z i) 0) uK == mulK (E.keys.getD i 0) (E.keys.getD (Z i) 0))

theorem conj_of_secondCheckW {gs : Array (ℕ × ℕ)} {E : Enum} {tK uK n : ℕ} {B : ℕ → List ℕ}
    {Y Z : ℕ → ℕ} (hE : enumOK gs E = true) (h : secondCheckW E tK uK n B Y Z = true)
    {tb u : GL12} (ht : Rep tK tb) (hu : Rep uK u) {s : GL12} (hs : s ∈ grpOf gs)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (hfix : Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7)
    (hn : n ≤ Nat.card ↥(grpOf gs ⊓ Subgroup.centralizer ({s} : Set GL12))) :
    ∃ y ∈ grpOf gs, s = y * tb * y⁻¹ ∨ s = y * u * y⁻¹ := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hs
  simp only [secondCheckW, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have hconj : ∀ {vK : ℕ} {v : GL12}, Rep vK v → ∀ j, j < E.keys.size →
      mulK (E.keys.getD j 0) vK = mulK (E.keys.getD i 0) (E.keys.getD j 0) →
        ∃ y ∈ grpOf gs, s = y * v * y⁻¹ := by
    intro vK v hv j hj h1
    obtain ⟨y, hy, hry⟩ := Enum.exists_mem hE j hj
    refine ⟨y, hy, ?_⟩
    have e : y * v = s * y := by
      have h3 := hry.mul hv
      rw [h1] at h3
      exact h3.unique (hr.mul hry)
    calc s = s * y * y⁻¹ := by group
      _ = y * v * y⁻¹ := by rw [← e]
  rcases h i hi with ((((h1 | h1) | ⟨h1, h2⟩) | h1) | ⟨hj, h1⟩) | ⟨hj, h1⟩
  · exact absurd ((hr.mul hr).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h1
  · rw [h1] at hr
    exact absurd (hr.unique rep_one) hs1
  · rw [← fixM_of_rep hr] at hfix
    have := (Nat.pow_le_pow_right (by norm_num) h1).trans (fixLB_sound h2)
    omega
  · have := card_inf_centralizer_le_commCount hE hr
    omega
  · obtain ⟨y, hy, e⟩ := hconj ht _ hj h1
    exact ⟨y, hy, Or.inl e⟩
  · obtain ⟨y, hy, e⟩ := hconj hu _ hj h1
    exact ⟨y, hy, Or.inr e⟩

end CFSG.EvenSmallLie.OmegaEight.Stage2
