module

public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KS.Raw.Orb

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native CFSG.Certificates
  CFSG.Certificates.ChainArrays CFSG.KS.Raw

variable {n kO : Nat} {S : Array (Array Nat)} {base : Array Nat} {W : Array (List Int)}

theorem mem_Gen_of_siftA (hd : Hd n S base kO W) : ∀ d l, base.size - l = d →
    ∀ (g : Array Nat) (G : Equiv.Perm (Fin n)), Rep n g G →
      siftA n (rawLevels n S base) base l g = true → G ∈ Gen n S kO := by
  intro d
  induction d with
  | zero =>
    intro l hl g G hg h
    have hls : ¬ l < (rawLevels n S base).size := by rw [chainLevels_size]; omega
    rw [siftA, dif_neg hls] at h
    rw [eq_of_eqA hg rep_idA h]
    exact Subgroup.one_mem _
  | succ d ih =>
    intro l hl g G hg h
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    rw [siftA, dif_pos hls, chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    have hT := (tr_spec hd hlb _ hk).1.1
    have hm := ih (l + 1) (by omega) _ _ (rep_compA (rep_trInv hd hlb hk) hg) h
    simpa using (Gen n S kO).mul_mem hT hm

theorem mem_Gen_of_sift (hd : Hd n S base kO W) {g : Array Nat} {G : Equiv.Perm (Fin n)}
    (hg : Rep n g G) (h : siftA n (rawLevels n S base) base 0 g = true) : G ∈ Gen n S kO :=
  mem_Gen_of_siftA hd _ 0 rfl g G hg h

end CFSG.KS.Raw.Orb

end
