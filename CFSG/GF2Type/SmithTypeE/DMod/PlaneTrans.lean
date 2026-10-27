module

public import CFSG.GF2Type.SmithTypeE.DMod.PlaneAct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

section Transitivity

theorem exists_smul_zero_eq (i : Fin 75735) : ∃ g : TD6, g • (0 : Fin 75735) = i := by
  have key : ∀ v < 75735, ∃ g : TD6, ((g • (0 : Fin 75735) : Fin 75735) : ℕ) = v := by
    refine planeTree_induct (fun v => ∃ g : TD6, ((g • (0 : Fin 75735) : Fin 75735) : ℕ) = v)
      ?_ ?_
    · exact ⟨1, by rw [one_smul]; rfl⟩
    · rintro g hg p hp v hv hgv ⟨c, hc⟩
      refine ⟨⟨tvP ⟨gensArr[g]!, gensArr_lt hg⟩, tvP_mem _⟩ * c, ?_⟩
      rw [mul_smul, tvP_smul]
      show planeImg gensArr[g]! (c • (0 : Fin 75735) : Fin 75735).val = v
      rw [hc]
      exact hgv
  obtain ⟨g, hg⟩ := key i.val i.2
  exact ⟨g, Fin.ext hg⟩

theorem exists_smul_planes_eq (i j : Fin 75735) : ∃ g : TD6, g • i = j := by
  obtain ⟨g, hg⟩ := exists_smul_zero_eq i
  obtain ⟨h, hh⟩ := exists_smul_zero_eq j
  refine ⟨h * g⁻¹, ?_⟩
  rw [mul_smul, ← hg, inv_smul_smul, hh]

theorem exists_fixed_plane (P : Subgroup TD6) (hP : IsPGroup 2 P) :
    ∃ i : Fin 75735, ∀ g ∈ P, g • i = i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hP.card_modEq_card_fixedPoints (Fin 75735)
  have hcard : Nat.card (Fin 75735) = 75735 := by simp
  rw [hcard] at h
  have hne : Nat.card (MulAction.fixedPoints P (Fin 75735)) ≠ 0 := by
    intro h0
    rw [h0] at h
    have : 75735 % 2 = 0 % 2 := h
    omega
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne)).1
  exact ⟨i, fun g hg => hi ⟨g, hg⟩⟩

end Transitivity

end CFSG.GF2Type.SmithTypeE.DMod
