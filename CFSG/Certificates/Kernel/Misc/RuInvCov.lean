module

public import CFSG.Certificates.Kernel.Misc.RuInvClass
public import CFSG.Certificates.Kernel.Spor.RawAgree
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KC.Misc.RuInv.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier CFSG.Certificates.Native

section Levels

variable {kS BP : Nat} {PS PSI LR TR TRI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds 4060 12 PS kS 2 BP S base)
  (hp : allN kS (fun j => permOK 4060 12 (mask 12) (4060 * 12) (PS j) (PSI j)) = true)
  (hl : LevelsOK 4060 12 PS PSI LR TR TRI kS 2 BP)
include hb hl

theorem base_lt2 : ∀ t < 2, base[t]! < 4060 := fun t ht => by
  obtain ⟨-, -, hR, -⟩ := Raw.Orb.levelK_facts (hl t ht)
  rw [hb.2.2.2.2.2.2 t ht, ← hR.root]
  exact (hR.pt 0 hR.c_pos).1

include hp

theorem lev2 {i : Nat} (hi : i < 2) :
    (rawLevels 4060 S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), ∃ g : G, Rep 4060 (rawLevels 4060 S base)[i]!.tr[k]! g ∧
        PRep 4060 12 (TR (roff 4060 (4060 * 12) (LR i) + k)) g := by
  obtain ⟨A, hP⟩ := Raw.Orb.agree_levelK hb hp (base_lt2 hb hl) hi (hl i hi)
  refine ⟨A.cnt.symm, fun k hk => ⟨_, (A.tr k (A.cnt ▸ hk)).1, (hP k hk).1⟩⟩

end Levels

theorem bIf_eq' (c a b : Bool) : Bool.rec (motive := fun _ => Bool) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem covOne_cases {E : Nat → Nat} {T0 T1 h : Nat} (hc : covOne E T0 T1 h = true) :
    (h < 1391 ∧ E h = mulP T0 T1) ∨
      (∃ x < 4060, apP T0 (apP T1 (apP T0 (apP T1 x))) ≠ x) ∨
      foldN 4060 (fun x c => nIf(Nat.beq (apP T0 (apP T1 x)) x, Nat.succ c, c)) 0 ≠ 92 := by
  unfold covOne at hc
  simp only [bIf_eq', strictB_eq'] at hc
  by_cases h1 : Nat.blt h 1391 = true
  · rw [if_pos h1] at hc
    exact Or.inl ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true hc⟩
  · rw [if_neg h1] at hc
    by_cases h2 : Nat.blt h 5451 = true
    · rw [if_pos h2] at hc
      refine Or.inr (Or.inl ⟨h - 1391, ?_, fun e => ?_⟩)
      · have := Nat.blt_eq.mp h2
        have : ¬ h < 1391 := fun hh => h1 (Nat.blt_eq.mpr hh)
        omega
      · have e' : Nat.beq (apP T0 (apP T1 (apP T0 (apP T1 (Nat.sub h 1391))))) (Nat.sub h 1391) = true :=
          Nat.beq_eq.mpr e
        rw [if_pos e'] at hc
        exact Bool.false_ne_true hc
    · rw [if_neg h2] at hc
      refine Or.inr (Or.inr fun e => ?_)
      rw [if_pos (Nat.beq_eq.mpr e)] at hc
      exact Bool.false_ne_true hc

theorem foldN_count (p : Nat → Bool) (n : Nat) :
    foldN n (fun x c => nIf(p x, Nat.succ c, c)) 0 = ((List.range n).filter p).length := by
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  induction (List.range n) with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    cases p x <;> rfl

end CFSG.KC.Misc.RuInv.P

end
