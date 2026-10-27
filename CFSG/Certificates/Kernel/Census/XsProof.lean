module

public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CFSG.KC.Census.SP

open CFSG.KC.Enum CFSG.KC.Census CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

variable {n w : Nat}

theorem pid_good_of_le (hn24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) :
    unpackP n w (pid n w) = idA n ∧ canon1 n w (pid n w) = true := by
  have hf := fld_pid (n := n) hw
  have hc : n ≤ 2 ^ clog n := by
    rcases clog_spec' n with h | h
    · rw [h]
      exact hn24
    · exact h
  apply pid_good hw
  apply pvalid_of_inj hw
  · intro i hi
    have := CFSG.KS.PackFld.pg_of_fld hf (i := i) (by
      simp only [show i < 2 ^ clog n by omega, hi, ↓reduceIte]
      omega)
    change at' w (pid n w) i = _ at this
    rw [this]
    simp only [show i < 2 ^ clog n by omega, hi, ↓reduceIte]
  · intro i hi j hj e
    have h1 := CFSG.KS.PackFld.pg_of_fld hf (i := i) (by
      simp only [show i < 2 ^ clog n by omega, hi, ↓reduceIte]
      omega)
    have h2 := CFSG.KS.PackFld.pg_of_fld hf (i := j) (by
      simp only [show j < 2 ^ clog n by omega, hj, ↓reduceIte]
      omega)
    change at' w (pid n w) i = _ at h1
    change at' w (pid n w) j = _ at h2
    rw [h1, h2] at e
    simpa only [show i < 2 ^ clog n by omega, hi, show j < 2 ^ clog n by omega, hj,
      ↓reduceIte] using e

end CFSG.KC.Census.SP

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native

theorem xsOK_of_pxsOK_proved {n w : Nat} {gens xs : Array Nat} {ws : List (List Nat)}
    (hn : n < 2 ^ 32) (hn24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w)
    (hg : gens.toList.all (canon1 n w) = true) (hxs : xs.toList.all (canon1 n w) = true)
    (h : pxsOK n w gens xs ws = true) :
    xsOK n (gens.map (unpackP n w)) (xs.map (unpackP n w)) ws = true := by
  obtain ⟨e1, e2⟩ := SP.pid_good_of_le hn24 hw
  have G : SP.Good n w := ⟨hn, hw, e1, e2⟩
  have hg' := SP.canon_get (List.all_eq_true.1 hg)
  have hx' := SP.canon_get (List.all_eq_true.1 hxs)
  unfold pxsOK at h
  unfold xsOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.blt_eq, Array.size_map,
    decide_eq_true_eq] at h ⊢
  intro k hk
  obtain ⟨h1, h2⟩ := h k hk
  refine ⟨h1, ?_⟩
  have hl : ∀ x ∈ (ws.getD k []).map (fun i => gens[i]!), canon1 n w x = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hg' i (h1 i hi)
  obtain ⟨hp, hpc⟩ := SP.pprod_eq G hl
  rw [SP.map_get _ _ hk, wordG]
  have e : List.map ((fun i => (gens.map (unpackP n w))[i]!)) (ws.getD k []) =
      List.map (unpackP n w ∘ fun i => gens[i]!) (ws.getD k []) :=
    List.map_congr_left fun i hi => SP.map_get _ _ (h1 i hi)
  rw [e, ← List.map_map, ← hp, SP.eqA_unpack (hx' k hk) hpc]
  exact h2
