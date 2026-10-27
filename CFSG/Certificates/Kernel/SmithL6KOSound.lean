module

public import Certificates.Data.Kernel.SmithL6KO
public import CFSG.Certificates.Kernel.SmithL6KTSound
public import CFSG.Certificates.Kernel.SmithL6KWedge
public import CFSG.Certificates.Kernel.SmithL6CollSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (applyCols)

theorem planeImg_of_wt (hTW : chkTW = true)
    (hinj : ∀ i < 1395, ∀ j < 1395, wt i = wt j → i = j) {k u v : Nat} (hk : k < 1953)
    (hu : u < 1395) (hv : v < 1395) (h : wt v = applyCols (tvCols k) (wt u)) : planeImg k u = v := by
  unfold chkTW at hTW
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hTW
  obtain ⟨⟨hlt, hw⟩, -⟩ := hTW k hk u hu
  rw [wtArr_get hlt, tvArr_get hk, wtArr_get hu, ← h] at hw
  exact hinj _ hlt _ hv hw

section Sums

variable {S : Nat} {Wt : List (Nat × Nat)} (hA : s2AK S = true) (hB : s2BK S Wt = true)
include hA hB

theorem uSums_get {v : Nat} (hv : v < 512) : uSums[v]! = S.testBit v := by
  unfold uSums
  rw [ofFn_get! _ hv]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  constructor
  · rintro ⟨k, hk, l, hl, hkl, rfl⟩
    unfold s2AK at hA
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hA
    exact (hA k hk l hl).resolve_left hkl
  · intro hS
    unfold s2BK at hB
    simp only [List.all_eq_true, List.mem_range] at hB
    have e := hB v hv
    rw [hS] at e
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
      ne_eq, beq_iff_eq] at e
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := e
    exact ⟨_, h1, _, h2, h3, h4⟩

theorem uCls_eq {v : Nat} (hv : v < 512) : uCls uSums v = uClsK S v := by
  have e : uco.contains v = ptMask.testBit v := by
    rw [← ptTab_eq]
    unfold collPtTab
    rw [ofFn_get! _ hv]
  unfold uCls uClsK
  rw [e, uSums_get hA hB hv]

theorem uRoot_eq (c : Nat) : uRoot uSums c = uRootK S c := by
  unfold uRoot uRootK
  rw [find?_congr fun v hv => by rw [uCls_eq hA hB (List.mem_range.mp hv)]]

end Sums

theorem pos0_eq {P : List Nat} (hP : planePts 0 = P.toArray) (q : Nat) :
    pos0 q = P.findIdx (· == q) := by
  unfold pos0
  rw [planePtsArr_get (by decide), hP, List.findIdx_toArray]

theorem ugens_lt : ∀ j < 9, ugens[j]! < 1953 := by decide

theorem ucols_eq {C I : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
    (hI : ∀ n < 4096, fldW 11 I n = tvIdxTab[n]!) {P : List Nat} (hP : planePts 0 = P.toArray)
    {p : Nat} (hp : p < 1953) : ucols p = (ucolsK C I P p).toArray := by
  apply Array.ext
  · simp [ucols, ucolsK]
  · intro j h1 _
    have hj : j < 9 := by simpa [ucols] using h1
    simp only [ucols, ucolsK, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      List.getElem_range]
    rw [tvTab_get hp (ugens_lt j hj), pos0_eq hP, tvImgP_eq hC hI hp (ugens_lt j hj)]

end CFSG.SmithL6.K
