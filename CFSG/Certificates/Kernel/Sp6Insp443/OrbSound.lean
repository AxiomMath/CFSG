module

public import Certificates.Data.Kernel.Sp6Insp443.Orb
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.Sporadic.Th.Native
open CFSG.KC.Child3 (tabP tabP_get tabP_size)

variable {n w : Nat}

theorem cellOK_spec (hsz : szOK n w = true) {c : Nat} {T : Table} (h : cellOK n w c T = true) :
    CFSG.KC.BfsPin.PP n w c ∧ T = tabP n w c := by
  unfold cellOK at h
  rw [Orb.bAnd_eq, Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hs : T.size = n := Nat.eq_of_beq_eq_true h1
  refine ⟨CFSG.KC.BfsPin.PP_of_permOK hsz h2, ?_⟩
  apply Array.ext (by rw [hs, tabP_size])
  intro i hi _
  have hin : i < n := hs ▸ hi
  rw [← getElem!_pos T i hi, ← getElem!_pos (tabP n w c) i (by rw [tabP_size]; exact hin),
    tabP_get hin]
  have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h3 i hin)
  rw [e]
  unfold ap
  exact (UInt32.ofNat_toNat).symm

theorem rowOK_spec (hsz : szOK n w = true) : ∀ {cs : List Nat} {Ts : List Table},
    rowOK n w cs Ts = true → (∀ c ∈ cs, CFSG.KC.BfsPin.PP n w c) ∧ Ts = cs.map (tabP n w)
  | [], [], _ => ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: cs, T :: Ts, h => by
    have h' : bAnd(cellOK n w c T, rowOK n w cs Ts) = true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    obtain ⟨hc, eT⟩ := cellOK_spec hsz h'.1
    obtain ⟨hcs, eTs⟩ := rowOK_spec hsz h'.2
    refine ⟨fun d hd => ?_, by rw [eT, eTs, List.map_cons]⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hc
    · exact hcs d hd

theorem gridOK_spec (hsz : szOK n w = true) : ∀ {C : List (List Nat)} {Ts : List (List Table)},
    gridOK n w C Ts = true →
      (∀ c ∈ C, ∀ b ∈ c, CFSG.KC.BfsPin.PP n w b) ∧ Ts = C.map (List.map (tabP n w))
  | [], [], _ => ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | c :: C, T :: Ts, h => by
    have h' : bAnd(rowOK n w c T, gridOK n w C Ts) = true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    obtain ⟨hc, eT⟩ := rowOK_spec hsz h'.1
    obtain ⟨hC, eTs⟩ := gridOK_spec hsz h'.2
    refine ⟨fun d hd => ?_, by rw [eT, eTs, List.map_cons]⟩
    rcases List.mem_cons.1 hd with rfl | hd
    · exact hc
    · exact hC d hd

end CFSG.KS.Sp6I

end
