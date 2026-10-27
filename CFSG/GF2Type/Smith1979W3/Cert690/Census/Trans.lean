module

public import CFSG.GF2Type.Smith1979W3.Cert690.Census.BaseFacts
public import CFSG.GF2Type.Smith1979W3.Cert690.Tab

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62

variable {minus : Bool}

theorem mem_singOf {n : ℕ} :
    n ∈ singOf minus ↔ n < 64 ∧ n ≠ 0 ∧ qB minus n = false := by
  simp [singOf, Array.mem_toList_iff, List.mem_toArray, List.mem_filter, List.mem_range]

theorem qB_eq_false_of_qModel_eq_zero {n : ℕ}
    (h : qModel minus (Code.vec n) = 0) : qB minus n = false := by
  cases hq : qB minus n with
  | false => rfl
  | true =>
    rw [qModel_vec, hq] at h
    exact absurd h (by norm_num)

theorem exists_mem_O_map_to_b0 (hb : censusBase minus () = true) {b : V₀}
    (hb0 : b ≠ 0) (hq : qModel minus b = 0) :
    ∃ g ∈ O₀ minus, g b = Code.vec (b0Of minus) := by
  have hfacts := censusBaseFacts_of hb
  have hD := hfacts.grp
  have htrans := hfacts.trans
  obtain ⟨n, hn64, hbvec⟩ := exists_vec b
  have hqn : qModel minus (Code.vec n) = 0 := by rw [hbvec]; exact hq
  have hqB : qB minus n = false := qB_eq_false_of_qModel_eq_zero hqn
  have hn0 : n ≠ 0 := by
    intro hn
    apply hb0
    rw [← hbvec, hn, vec_zero]
  have hmem : n ∈ singOf minus := mem_singOf.mpr ⟨hn64, hn0, hqB⟩
  have hmem' : n ∈ (singOf minus).toList := by
    rw [Array.mem_toList_iff]; exact hmem
  obtain ⟨k, hk, hsing⟩ := List.mem_iff_getElem.mp hmem'
  have hk' : k < (singOf minus).size := by
    rw [← Array.length_toList]; exact hk
  have hsing' : (singOf minus)[k]! = n := by
    rw [array_getElem!_eq_getElem hk']
    rw [← Array.getElem_toList (by simpa [Array.length_toList] using hk)]
    exact hsing
  have ht := htrans
  unfold transOK at ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, and_assoc] at ht
  obtain ⟨_, _, _, hall⟩ := ht
  have hkall := hall k (List.mem_range.mpr hk')
  obtain ⟨hilt, hact⟩ := hkall
  refine ⟨hD.elt ((transWitOf (CertD minus) (singOf minus) (b0Of minus))[k]!),
    hD.elt_mem_O₀ hilt, ?_⟩
  rw [← hbvec, hD.elt_vec hilt n, ← hsing', hact]

end CFSG.GF2Type.Smith1979W3.Cert690

end
