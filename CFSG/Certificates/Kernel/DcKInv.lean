module

public import Certificates.Data.CFSGNative.H13.LocDblDc
public import CFSG.Certificates.Kernel.E64FSound
import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.KC.E64F

theorem invTab_eq (s : Array Nat) :
    invTab s = (List.range' 0 s.size).foldl (fun r i => r.set! (s.getD i 0) i)
      (Array.replicate s.size 0) := by
  unfold invTab
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rfl

theorem foldl_set_size (f : Nat → Nat) : ∀ (l : List Nat) (r : Array Nat),
    (l.foldl (fun r i => r.set! (f i) i) r).size = r.size
  | [], _ => rfl
  | a :: l, r => by
    rw [List.foldl_cons, foldl_set_size f l]
    simp

theorem foldl_set_other (f : Nat → Nat) {j : Nat} : ∀ (l : List Nat) (r : Array Nat),
    (∀ i ∈ l, f i ≠ j) → (l.foldl (fun r i => r.set! (f i) i) r).getD j 0 = r.getD j 0
  | [], _, _ => rfl
  | a :: l, r, h => by
    rw [List.foldl_cons, foldl_set_other f l _ fun i hi => h i (List.mem_cons_of_mem _ hi)]
    have ha := h a List.mem_cons_self
    simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne ha]

theorem foldl_set_at (f : Nat → Nat) : ∀ (l : List Nat) (r : Array Nat), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → ∀ i ∈ l, f i < r.size →
    (l.foldl (fun r i => r.set! (f i) i) r).getD (f i) 0 = i
  | [], _, _, _, _, h, _ => absurd h List.not_mem_nil
  | a :: l, r, hnd, hinj, i, hi, hlt => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hi'
    · rw [foldl_set_other f l _ fun b hb e => ?_]
      · simp [Array.getD_eq_getD_getElem?, hlt]
      · have := hinj b (List.mem_cons_of_mem _ hb) i List.mem_cons_self e
        subst this
        exact (List.nodup_cons.1 hnd).1 hb
    · exact foldl_set_at f l _ (List.nodup_cons.1 hnd).2
        (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) i hi'
        (by simpa using hlt)

theorem invTab_good {n : Nat} {s : Array Nat} {f g : Nat → Nat} (hs : Good n s f)
    (hg : ∀ p < n, g p < n) (hgf : ∀ p < n, g (f p) = p) (hfg : ∀ p < n, f (g p) = p) :
    Good n (invTab s) g := by
  have hsz : s.size = n := hs.1
  refine ⟨by rw [invTab_eq, foldl_set_size]; simp [hsz], fun p hp => ⟨?_, hg p hp⟩⟩
  rw [invTab_eq]
  have hf : ∀ i ∈ List.range' 0 s.size, s.getD i 0 = f i := fun i hi => by
    rw [List.mem_range'_1, Nat.zero_add, hsz] at hi
    exact (hs.2 i hi.2).1
  have e : (List.range' 0 s.size).foldl (fun r i => r.set! (s.getD i 0) i)
      (Array.replicate s.size 0) = (List.range' 0 s.size).foldl (fun r i => r.set! (f i) i)
      (Array.replicate s.size 0) := by
    exact CFSG.KC.Str.foldl_congr _ _ _ _ fun i hi r => by rw [hf i hi]
  rw [e]
  have hgi : g p ∈ List.range' 0 s.size := by
    rw [List.mem_range'_1, Nat.zero_add, hsz]
    exact ⟨Nat.zero_le _, hg p hp⟩
  have := foldl_set_at f (List.range' 0 s.size) (Array.replicate s.size 0) List.nodup_range'
    (fun a ha b hb e => by
      rw [List.mem_range'_1, Nat.zero_add, hsz] at ha hb
      rw [← hgf a ha.2, ← hgf b hb.2, e]) (g p) hgi
    (by rw [Array.size_replicate, hsz, hfg p hp]; exact hp)
  rwa [hfg p hp] at this

end CFSG.KC.DcK

end
