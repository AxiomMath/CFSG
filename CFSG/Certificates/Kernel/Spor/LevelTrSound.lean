module

import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Co2

private theorem bfs_trInv (n root : Nat) (steps : Array (Array Nat)) :
    TrInv n steps (Native.bfs n root steps).pts (Native.bfs n root steps).par (Native.bfs n root steps).lab
      (Native.bfs n root steps).tr := by
  unfold CFSG.Monster.B.Co2.Native.bfs
  simp only [Id.run_bind, Id.run_pure]
  refine forIn_range_inv n _ _
    (fun st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat) =>
      TrInv n steps st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2) ?_ ?_
  · refine ⟨rfl, rfl, rfl, by simp, rfl, fun k hk0 hk => ?_⟩
    simp at hk
    omega
  · intro a _ b hb
    split
    · rename_i hab
      simp only [Id.run_bind, Id.run_pure]
      refine (forIn_range_inv steps.size _ _
        (fun st : Array Nat × Array Nat × Array Nat × Array Nat × Array (Array Nat) =>
          TrInv n steps st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2 ∧ a < st.2.1.size)
        ⟨hb, hab⟩ ?_).1
      intro j hj c hc
      split
      · exact ⟨trInv_push hc.1 hc.2 hj, by simp; omega⟩
      · exact hc
    · exact hb

theorem bfs_tr_size {n root : Nat} {steps : Array (Array Nat)} {k : Nat}
    (hk : k < (Native.bfs n root steps).pts.size) : ((Native.bfs n root steps).tr[k]!).size = n := by
  obtain ⟨-, -, -, -, h0, hs⟩ := bfs_trInv n root steps
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [h0, idA, Array.size_ofFn]
  · rw [(hs k hk0 hk).2.2, compA, Array.size_ofFn]

theorem levelTr_sound {n w kS kO nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {D : List (List Int)}
    (hb : Binds n w PS kS nb BP S base)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) {i : Nat} (hi : i < nb) :
    (rawLevels n S base)[i]!.pts.size = rcnt (LR i) ∧
      ∀ k < rcnt (LR i), (rawLevels n S base)[i]!.tr[k]! =
        unpack n w (TR (Nat.add (roff n (n * w) (LR i)) k)) := by
  have hp := (Orb.head_facts hh).1
  have hbl := Orb.base_lt_of_levels hb hl
  obtain ⟨A, P⟩ := Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hi (hl i hi)
  have e : (rawLevels n S base)[i]! = CFSG.Certificates.ChainArrays.lev n S base i := rfl
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  refine ⟨by rw [e, A.cnt], fun k hk => ?_⟩
  have hk' : k < (CFSG.Certificates.ChainArrays.lev n S base i).pts.size := by rw [← A.cnt]; exact hk
  have R := (A.tr k hk').1
  have Q := Orb.rep_unpack (P k hk).1
  have hsz : ((rawLevels n S base)[i]!.tr[k]!).size = n := by
    have hk2 : k < (rawLevels n S base)[i]!.pts.size := hk'
    rw [rawLevels_get (by omega)] at hk2 ⊢
    exact bfs_tr_size hk2
  rw [e] at hsz ⊢
  apply Array.ext
  · rw [hsz, unpack, Array.size_ofFn]
  · intro x h1 h2
    have hx : x < n := by rwa [hsz] at h1
    rw [← getElem!_pos _ x h1, ← getElem!_pos _ x h2, R ⟨x, hx⟩]
    exact (Q ⟨x, hx⟩).symm

end CFSG.KS.Raw

end
