module

public import Certificates.Data.Kernel.TwistDce3.Tuple
public import CFSG.Certificates.Kernel.TwistDce3.CoverSound

public section

namespace CFSG.Certificates.TwDce3

open CFSG.KC.TwDce3 CFSG.KC.YModel
open CFSG.KC.TwDce (fld)
open CFSG.Certificates.TwDce2.Words (kandB_iff)

theorem tupleOK_sound {PO PB : ℕ} {FO F TU : ℕ → ℕ} {BS NB NL NP NQ : ℕ}
    (h : tupleOK PO FO PB F TU BS NB NL NP NQ = true) :
    TU 0 = BS ∧ ∀ p < NP, (∀ i < NB, fld (TU p) (16 * i) 65535 < NQ) ∧
      ∀ c < NL, ∀ i < NB, fld (TU (fieldAt PO (FO c) p)) (16 * i) 65535 =
        fieldAt PB (F c) (fld (TU p) (16 * i) 65535) := by
  unfold tupleOK at h
  rw [kandB_iff] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun p hp => ?_⟩
  have hp' := allRange_sound h.2 p hp
  rw [Nat.zero_add, kandB_iff] at hp'
  refine ⟨fun i hi => ?_, fun c hc i hi => ?_⟩
  · have := allRange_sound hp'.1 i hi
    rw [Nat.zero_add] at this
    exact Nat.blt_eq.mp this
  · have := allRange_sound (allRange_sound hp'.2 c hc) i hi
    simp only [Nat.zero_add] at this
    exact Nat.eq_of_beq_eq_true this

theorem tuple_foldl {PO PB : ℕ} {FO F TU : ℕ → ℕ} {NB NL NP : ℕ}
    (hL : ∀ c < NL, ∀ x < NP, fieldAt PO (FO c) x < NP)
    (hT : ∀ p < NP, ∀ c < NL, ∀ i < NB, fld (TU (fieldAt PO (FO c) p)) (16 * i) 65535 =
      fieldAt PB (F c) (fld (TU p) (16 * i) 65535)) :
    ∀ (w : List ℕ), (∀ c ∈ w, c < NL) → ∀ p < NP,
      w.foldl (fun q c => fieldAt PO (FO c) q) p < NP ∧ ∀ i < NB,
        fld (TU (w.foldl (fun q c => fieldAt PO (FO c) q) p)) (16 * i) 65535 =
          w.foldl (fun q c => fieldAt PB (F c) q) (fld (TU p) (16 * i) 65535)
  | [], _, p, hp => ⟨hp, fun _ _ => rfl⟩
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    obtain ⟨h1, h2⟩ := tuple_foldl hL hT w (fun d hd => hw d (List.mem_cons_of_mem _ hd))
      (fieldAt PO (FO c) p) (hL c hc p hp)
    refine ⟨h1, fun i hi => ?_⟩
    rw [List.foldl_cons, h2 i hi, hT p hp c hc i hi]
    rfl

end CFSG.Certificates.TwDce3

end
