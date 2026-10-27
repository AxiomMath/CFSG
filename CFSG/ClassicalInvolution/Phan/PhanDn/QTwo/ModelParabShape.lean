module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.StandardType.QTwo

theorem qTwoShape_ncard_le_three_of_fork_mem {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))}
    (hC : C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)))
    (ha : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∈ C) (hb : Fin.last m ∈ C) :
    C.ncard ≤ 3 := by
  rcases hC.2 with hsmall | ⟨i, k, j, l, rfl, hik, hjl, hij, hil, hkj, hkl⟩
  · exact hsmall
  have near_fork (u v : Fin (m + 1))
      (huv : CFSG.StandardType.ggCoxeterMatrixD (m + 1) u v = 3) :
      ((u.val = m - 1 ∨ u.val = m) → v.val = m - 2) ∧
      ((v.val = m - 1 ∨ v.val = m) → u.val = m - 2) := by
    clear hC ha hb hik hjl hij hil hkj hkl
    rw [qtwoLabel_three_iff hm] at huv
    constructor <;> intro h <;> omega
  have diff (u v : Fin (m + 1))
      (huv : CFSG.StandardType.ggCoxeterMatrixD (m + 1) u v = 2) : u.val ≠ v.val := by
    clear hC ha hb hik hjl hij hil hkj hkl
    intro h
    have heq : u = v := Fin.ext h
    subst v
    rw [qtwoLabel_self] at huv
    omega
  have hik' := near_fork i k hik
  have hjl' := near_fork j l hjl
  have hij' := diff i j hij
  have hil' := diff i l hil
  have hkj' := diff k j hkj
  have hkl' := diff k l hkl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  have ha' : i.val = m - 1 ∨ k.val = m - 1 ∨ j.val = m - 1 ∨ l.val = m - 1 := by
    rcases ha with h | h | h | h
    · exact Or.inl (congrArg Fin.val h).symm
    · exact Or.inr (Or.inl (congrArg Fin.val h).symm)
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h).symm))
    · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val h).symm))
  have hb' : i.val = m ∨ k.val = m ∨ j.val = m ∨ l.val = m := by
    rcases hb with h | h | h | h
    · exact Or.inl (congrArg Fin.val h).symm
    · exact Or.inr (Or.inl (congrArg Fin.val h).symm)
    · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h).symm))
    · exact Or.inr (Or.inr (Or.inr (congrArg Fin.val h).symm))
  exfalso
  clear hC ha hb hik hjl hij hil hkj hkl near_fork diff
  rcases ha' with ha' | ha' | ha' | ha' <;>
    rcases hb' with hb' | hb' | hb' | hb' <;> omega

theorem qTwoShape_eq_fork_triple {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))}
    (hC : C ∈ qTwoShape (CFSG.StandardType.ggCoxeterMatrixD (m + 1)))
    (ha : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∈ C) (hb : Fin.last m ∈ C)
    (hc : (⟨m - 2, by omega⟩ : Fin (m + 1)) ∈ C) :
    C = {⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, Fin.last m} := by
  have hsub : ({⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, Fin.last m} :
      Set (Fin (m + 1))) ⊆ C := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl | rfl <;> assumption
  symm
  apply Set.eq_of_subset_of_ncard_le hsub
  have hcard : ({⟨m - 2, by omega⟩, ⟨m - 1, by omega⟩, Fin.last m} :
      Set (Fin (m + 1))).ncard = 3 := by
    simp [Set.ncard_insert_of_notMem, Set.ncard_pair, Fin.ext_iff, show m - 2 ≠ m - 1 by omega,
      show m - 2 ≠ m by omega, show m - 1 ≠ m by omega]
  rw [hcard]
  exact qTwoShape_ncard_le_three_of_fork_mem hm hC ha hb

end CFSG.ClassicalInvolution.PhanDn.QTwo
