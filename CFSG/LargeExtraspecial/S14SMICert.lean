module

public import CFSG.LargeExtraspecial.S14SMGCert
public import Certificates.Certificate21114
public import Certificates.Certificate21115

public section

namespace CFSG.LargeExtraspecial.S14.SMI

open CFSG.SmithE CFSG.F4.Native SMG

theorem commWtCheck_holds : chkCommWt = true :=
  Certificates.certificate21114

theorem prodCheck_holds : chkProd = true :=
  Certificates.certificate21115

theorem exists_comm_wt {k : Nat}
    (hk : k < 693) : ∃ e < 2 ^ 20, ∃ j < 891, wt j = applyCols (tvCols k) e ^^^ e := by
  have h := commWtCheck_holds
  simp only [chkCommWt, commWt, List.all_eq_true, List.mem_range, List.any_eq_true] at h
  obtain ⟨e, he, hwt⟩ := h k hk
  rw [tvArr_get hk] at hwt
  obtain ⟨j, hj, hje⟩ := (isWt_iff _).mp hwt
  exact ⟨e, lt_trans he (by norm_num), j, hj, hje⟩

theorem prodCols_eq_of {A B C : Array Nat} (hB : B.size = 20) (hC : C.size = 20)
    (h : ∀ c < 2 ^ 20, applyCols C c = applyCols A (applyCols B c)) : prodCols A B = C := by
  refine Array.ext (by simp only [prodCols, Array.size_map, hB, hC]) fun j _ hj2 => ?_
  have hj : j < 20 := by rwa [hC] at hj2
  have hjB : j < B.size := by rw [hB]; exact hj
  have e := h (2 ^ j) (Nat.pow_lt_pow_right (by norm_num) hj)
  rw [applyCols_two_pow C hj2, applyCols_two_pow B hjB, getElem!_pos C j hj2,
    getElem!_pos B j hjB] at e
  simp only [prodCols, Array.getElem_map]
  exact e.symm

theorem prodCols_eq {k l m : Nat}
    (h : ∀ c < 2 ^ 20, applyCols (tvCols m) c = applyCols (tvCols k) (applyCols (tvCols l) c)) :
    prodCols (tvCols k) (tvCols l) = tvCols m :=
  prodCols_eq_of (size_tvCols l) (size_tvCols m) h

theorem prodCols_ne {k l m : Nat} (hkl : k < l) (hl : l < 693)
    (hm : m < 693) (h0 : hermC uPts[k]! uPts[l]! = 0) :
    prodCols (tvCols k) (tvCols l) ≠ tvCols m := by
  intro he
  have h := prodCheck_holds
  simp only [chkProd, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  rcases h k (by omega) l hl with (h1 | h1) | h1
  · omega
  · exact h1 h0
  · rw [tvArr_get (by omega), tvArr_get hl, he] at h1
    have hmem : tvCols m ∈ tvArr := by
      unfold tvArr
      exact Array.mem_ofFn.mpr ⟨⟨m, hm⟩, rfl⟩
    rw [Array.contains_eq_true_of_mem hmem] at h1
    exact absurd h1 (by decide)

end CFSG.LargeExtraspecial.S14.SMI
