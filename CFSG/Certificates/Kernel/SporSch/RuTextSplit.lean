module

public import Certificates.Data.Kernel.Misc.HexDrop
public import CFSG.Certificates.Kernel.Spor.TextJoin
public import CFSG.Certificates.Kernel.Misc.HexDropSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.Text

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexFlat

@[expose] noncomputable def takeL (m : Nat) (cs : List Char) : List Char :=
  List.rec (motive := fun _ => Nat → List Char) (fun _ => List.nil)
    (fun c _ ih k => Nat.rec (motive := fun _ => List Char) List.nil
      (fun k' _ => List.cons c (ih k')) k)
    cs m

theorem takeL_eq : ∀ (cs : List Char) (m : Nat), takeL m cs = cs.take m
  | [], m => by cases m <;> rfl
  | _ :: _, 0 => rfl
  | c :: t, m + 1 => by
    change c :: takeL m t = (c :: t).take (m + 1)
    rw [takeL_eq t m, List.take_succ_cons]

@[expose] noncomputable def shF (F : Nat → Nat) (d j : Nat) : Nat := F (Nat.add d j)

noncomputable def sufR (wd n w lines : Nat) (F : Nat → Nat) (B : List Char) (L : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (nilC lines)
    (stepC wd n w 0 lines F) B L 0 0 0 0

theorem sufR_append {A B : List Char} {wd n w lines la d : Nat} {F : Nat → Nat}
    (hA : hexBind A wd n w la 0 la (shF F d) = true) (hle : d + la ≤ lines) :
    sufR wd n w lines F (A ++ B) d = sufR wd n w lines F B (d + la) := by
  unfold hexBind at hA
  obtain ⟨-, hA2⟩ := (bAnd_iff _ _).1 hA
  obtain ⟨-, hA⟩ := (bAnd_iff _ _).1 hA2
  rw [run_eq] at hA
  have hc : ∀ L' a, 0 ≤ L' → L' < la →
      cmpC 0 la (shF F d) L' a = cmpC 0 lines F (L' + d) a := by
    intro L' a _ hL
    have h0 : Nat.ble 0 L' = true := Nat.ble_eq.mpr (Nat.zero_le L')
    have h0' : Nat.ble 0 (L' + d) = true := Nat.ble_eq.mpr (Nat.zero_le _)
    have h1 : Nat.blt L' (Nat.add 0 la) = true := Nat.blt_eq.mpr (by change L' < 0 + la; omega)
    have h2 : Nat.blt (L' + d) (Nat.add 0 lines) = true :=
      Nat.blt_eq.mpr (by change L' + d < 0 + lines; omega)
    unfold cmpC
    rw [h0, h0', h1, h2]
    try dsimp only
    have e : Nat.sub (L' + d) 0 = Nat.add d (Nat.sub L' 0) := by
      change L' + d - 0 = d + (L' - 0)
      omega
    rw [e]
    rfl
  have s := sim wd n w la 0 la 0 lines d (shF F d) F
    (List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool) (nilC lines)
      (stepC wd n w 0 lines F) B) A 0 0 0 0 0 hA (fun _ => rfl) (fun _ => rfl) hc
  rw [Nat.zero_add] at s
  unfold sufR
  rw [rec_append (fun _ _ _ _ => rfl), s, Nat.add_comm la d]

theorem dropL2 (cs : List Char) (x y : Nat) : dropL x (dropL y cs) = cs.drop (y + x) := by
  simp only [dropL_eq, List.drop_drop]
  all_goals (congr 1; omega)

theorem sufR_step {cs : List Char} {wd n w lines la d d' K x y x' y' : Nat} {F : Nat → Nat}
    (hA : hexBind (takeL K (dropL x (dropL y cs))) wd n w la 0 la (shF F d) = true)
    (hm : y + x + K = y' + x') (hd : d + la = d') (hle : d + la ≤ lines)
    (hnext : sufR wd n w lines F (dropL x' (dropL y' cs)) d' = true) :
    sufR wd n w lines F (dropL x (dropL y cs)) d = true := by
  rw [takeL_eq, dropL2] at hA
  rw [dropL2, ← hm] at hnext
  rw [dropL2, ← List.take_append_drop K (cs.drop (y + x)), sufR_append hA hle, hd,
    List.drop_drop]
  first
    | exact hnext
    | (rw [Nat.add_comm] at hnext; exact hnext)

theorem sufR_last {cs : List Char} {wd n w lines la d x y : Nat} {F : Nat → Nat}
    (hA : hexBind (dropL x (dropL y cs)) wd n w la 0 la (shF F d) = true) (hd : d + la = lines) :
    sufR wd n w lines F (dropL x (dropL y cs)) d = true := by
  rw [← List.append_nil (dropL x (dropL y cs)), sufR_append hA (Nat.le_of_eq hd), hd]
  unfold sufR nilC
  rw [bAnd_iff, bAnd_iff]
  exact ⟨Nat.beq_refl _, rfl, rfl⟩

theorem hexBind_of_sufR {cs : List Char} {wd n w lines : Nat} {F : Nat → Nat} (hwd : 0 < wd)
    (h : sufR wd n w lines F (dropL 0 (dropL 0 cs)) 0 = true) :
    hexBind cs wd n w lines 0 lines F = true := by
  rw [dropL2, List.drop_zero] at h
  unfold hexBind
  rw [bAnd_iff, bAnd_iff]
  refine ⟨Nat.blt_eq.mpr hwd, Nat.ble_eq.mpr (by change 0 + lines ≤ lines; omega), ?_⟩
  rw [run_eq]
  exact h

end CFSG.KS.Text

end
