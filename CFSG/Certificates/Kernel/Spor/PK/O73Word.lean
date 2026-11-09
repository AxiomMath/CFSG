module

public import CFSG.Certificates.Kernel.Spor.PK.MiscPerm

public section

namespace CFSG.KC.Misc.O73

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def relSK (LP A B : List Nat) : Bool :=
  letB (idP 1134 11) fun e => letB (wordP 1134 11 LP A) fun a => letB (wordP 1134 11 LP B) fun b =>
    andB (notB (Nat.beq a e)) <| andB (Nat.beq (compP 1134 11 a (compP 1134 11 a a)) e) <|
      allN 8 fun i => letB (wordP 1134 11 LP [i]) fun c =>
        Nat.beq (compP 1134 11 c (compP 1134 11 a (compP 1134 11 c b))) e

end CFSG.KC.Misc.O73

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73

private theorem wordPF_lt_o73w {n w : Nat} (Ps : List Nat)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (wd : List Nat) :
    ∀ x < n, wordPF w Ps wd x < n := by
  induction wd with
  | nil => intro x hx; exact hx
  | cons c wd ih =>
    intro x hx
    change (if c < Ps.length then fd w (Ps.getD c 0) (wordPF w Ps wd x) else wordPF w Ps wd x) < n
    split
    next hc => exact hPs c hc _ (ih x hx)
    next => exact ih x hx

theorem o73WordP_append {n w : Nat} (hw : n ≤ 2 ^ w) (Ps : List Nat)
    (hPs : ∀ c < Ps.length, ∀ x < n, fd w (Ps.getD c 0) x < n) (a b : List Nat) :
    wordP n w Ps (a ++ b) = compP n w (wordP n w Ps a) (wordP n w Ps b) := by
  simp only [wordP_eq_of_maps hw Ps hPs, compP_eq]
  apply enc_congr
  intro x hx
  have hb := wordPF_lt_o73w Ps hPs b x hx
  rw [fd_enc (fun i hi => Nat.lt_of_lt_of_le (wordPF_lt_o73w Ps hPs b i hi) hw) hx,
    fd_enc (fun i hi => Nat.lt_of_lt_of_le (wordPF_lt_o73w Ps hPs a i hi) hw) hb]
  unfold wordPF
  rw [List.foldr_append]

theorem relPK_of_wordP {LP : List Nat} {E : List (List Nat)} {k : Nat}
    (h : wordP 1134 11 LP (E.getD k []) = idP 1134 11) : relPK LP E k 1 = true := by
  unfold relPK
  rw [allN_lqt_iff]
  intro d hd
  obtain rfl : d = 0 := by omega
  have e : Nat.add k 0 = k := rfl
  simp only [letB_eq, impB_eq, e, nthL_eq, lenLLN_eq, h, Bool.or_eq_true, Bool.not_eq_true',
    Nat.beq_eq, or_true]

theorem relSK_sound {cL LP A B : List Nat} (hl : liftTextK cL LP = true)
    (h : relSK LP A B = true) :
    spK LP A = true ∧ wordP 1134 11 LP (A ++ (A ++ A)) = idP 1134 11 ∧
      ∀ i < 8, wordP 1134 11 LP ([i] ++ (A ++ ([i] ++ B))) = idP 1134 11 := by
  unfold liftTextK at hl
  simp only [andB_eq, Bool.and_eq_true, allN_lqt_iff, nthN_eq] at hl
  obtain ⟨-, -, hlines, hperm⟩ := hl
  unfold linesK at hlines
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenN_misc_eq] at hlines
  obtain ⟨-, hlen, -⟩ := hlines
  have hw : (1134 : Nat) ≤ 2 ^ 11 := by decide
  have hPs : ∀ c < LP.length, ∀ x < 1134, fd 11 (LP.getD c 0) x < 1134 := fun c hc x hx =>
    ((permK_iff.1 (hperm c (hlen ▸ hc))).2).1 x hx
  unfold relSK at h
  simp only [letB_eq, andB_eq, Bool.and_eq_true, allN_lqt_iff] at h
  obtain ⟨hs, h3, h8⟩ := h
  refine ⟨hs, ?_, fun i hi => ?_⟩
  · rw [o73WordP_append hw LP hPs, o73WordP_append hw LP hPs]
    exact Nat.eq_of_beq_eq_true h3
  · rw [o73WordP_append hw LP hPs, o73WordP_append hw LP hPs, o73WordP_append hw LP hPs]
    exact Nat.eq_of_beq_eq_true (h8 i hi)

end CFSG.KS.PK

end
