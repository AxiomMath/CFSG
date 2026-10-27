module

public import CFSG.Certificates.Kernel.Spor.TabWords
public import Certificates.Data.CFSGNative.Bridge.SurjA

public section

namespace CFSG.KS.RelTR

open CFSG.KS.TW CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native

@[expose] def letterF (fa fai fb fbi : Nat → Nat) (l : Nat × Bool) : Nat → Nat :=
  if l.1 = 0 then (if l.2 then fa else fai) else if l.2 then fb else fbi

@[expose] def wordF (F : Nat × Bool → Nat → Nat) (v : List (Nat × Bool)) (x : Nat) : Nat :=
  v.foldr (fun l y => F l y) x

theorem wordF_cons (F : Nat × Bool → Nat → Nat) (l : Nat × Bool) (v : List (Nat × Bool))
    (x : Nat) : wordF F (l :: v) x = F l (wordF F v x) := rfl

theorem wordF_append (F : Nat × Bool → Nat → Nat) (u v : List (Nat × Bool)) (x : Nat) :
    wordF F (u ++ v) x = wordF F u (wordF F v x) := by
  unfold wordF
  rw [List.foldr_append]

theorem letterTab_TR {n : Nat} {α αi β βi : Table} {fa fai fb fbi : Nat → Nat}
    (ha : TR n α fa) (hai : TR n αi fai) (hb : TR n β fb) (hbi : TR n βi fbi) (l : Nat × Bool) :
    TR n (letterTab α αi β βi l) (letterF fa fai fb fbi l) := by
  unfold letterTab letterF
  split
  · split
    · exact ha
    · exact hai
  · split
    · exact hb
    · exact hbi

theorem compT_TR {n : Nat} {P Q : Table} {f g : Nat → Nat} (hP : TR n P f) (hQ : TR n Q g) :
    TR n (compT n P Q) fun x => f (g x) := by
  refine ⟨by simp [compT], fun i hi => ?_⟩
  obtain ⟨hg, hgl⟩ := hQ.2 i hi
  obtain ⟨hf, hfl⟩ := hP.2 (g i) hgl
  refine ⟨?_, hfl⟩
  unfold ap compT
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  unfold ap at hg hf
  rw [hg, hf]

theorem wordTab_TR {n : Nat} (hn : n < 2 ^ 32) {α αi β βi : Table} {F : Nat × Bool → Nat → Nat}
    (hL : ∀ l, TR n (letterTab α αi β βi l) (F l)) :
    ∀ v : List (Nat × Bool), TR n (wordTab n α αi β βi v) (wordF F v)
  | [] => idT_TR hn
  | l :: v => by
    have h := compT_TR (hL l) (wordTab_TR hn hL v)
    exact h

theorem eq_idT_of_TR {n : Nat} (hn : n < 2 ^ 32) {t : Table} {f : Nat → Nat} (h : TR n t f)
    (hf : ∀ i < n, f i = i) : t = idT n := by
  have hs : t.size = (idT n).size := by rw [h.1]; simp [idT]
  refine Array.ext hs fun i h1 h2 => ?_
  have hi : i < n := by rw [h.1] at h1; exact h1
  have e1 : (t[i]!).toNat = i := by
    have := (h.2 i hi).1
    unfold ap at this
    rw [this, hf i hi]
  have e2 : ((idT n)[i]!).toNat = i := (idT_TR hn).2 i hi |>.1
  rw [getElem!_pos t i h1] at e1
  rw [getElem!_pos (idT n) i h2] at e2
  exact UInt32.toNat_inj.1 (e1.trans e2.symm)

theorem relCheck_of_TR {n : Nat} (hn : n < 2 ^ 32) {α αi β βi : Table}
    {F : Nat × Bool → Nat → Nat} (hL : ∀ l, TR n (letterTab α αi β βi l) (F l))
    {rels : List (List (Nat × Bool))} (h : ∀ v ∈ rels, ∀ x < n, wordF F v x = x) :
    relCheck n α αi β βi rels = true := by
  unfold relCheck
  rw [List.all_eq_true]
  intro v hv
  rw [beq_iff_eq]
  exact eq_idT_of_TR hn (wordTab_TR hn hL v) (h v hv)

end CFSG.KS.RelTR

end
