module

public import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.Th.Native

theorem invT_unpack {n w p r : Nat} (hn : n < 4294967296)
    (h : invEqK n w (mask w) (n * w) p r = true) :
    invT n (tabT (unpack n w p)) = tabT (unpack n w r) := by
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hP : ∀ i < n, ((tabT (unpack n w p))[i]!).toNat = pg w (mask w) p i := fun i hi => by
    rw [tabT_get, UInt32.toNat_ofNat', CFSG.KS.Raw.Orb.unpack_get hi,
      Nat.mod_eq_of_lt (by have := (h3 i hi).1; omega)]
  have hinj : ∀ a < n, ∀ b < n, pg w (mask w) p a = pg w (mask w) p b → a = b :=
    fun a ha b hb e => by rw [← (h3 a ha).2, ← (h3 b hb).2, e]
  have hsurj : ∀ j < n, ∃ i < n, pg w (mask w) p i = j := by
    classical
    have himg : (Finset.range n).image (pg w (mask w) p) = Finset.range n := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (h3 i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn fun a ha b hb e =>
          hinj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) e]
    intro j hj
    have : j ∈ (Finset.range n).image (pg w (mask w) p) := by
      rw [himg]
      exact Finset.mem_range.2 hj
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  unfold invT
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have key := CFSG.KS.BfsReplay.forIn_range'_yield n 0 (Array.replicate n (0 : UInt32))
    (fun i (R : Table) =>
      pure (ForInStep.yield (Array.set! R ((tabT (unpack n w p))[i]!).toNat (UInt32.ofNat i))))
    (fun m R => R.size = n ∧ ∀ i < m, R[pg w (mask w) p i]! = UInt32.ofNat i)
    (fun m hm R hR => ⟨_, rfl, by simpa using hR.1, fun i hi => ?_⟩)
    ⟨by simp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · change Id.run (forIn (List.range' 0 n) (Array.replicate n (0 : UInt32)) fun i (R : Table) =>
      pure (ForInStep.yield (Array.set! R ((tabT (unpack n w p))[i]!).toNat (UInt32.ofNat i)))) = _
    generalize Id.run (forIn (List.range' 0 n) (Array.replicate n (0 : UInt32)) _) = R at key ⊢
    obtain ⟨hs, hR⟩ := key
    apply Array.ext (by simp [hs, tabT, unpack])
    intro j h1 h2
    have hj : j < n := by omega
    obtain ⟨i, hi, rfl⟩ := hsurj j hj
    rw [← getElem!_pos R _ h1, ← getElem!_pos (tabT (unpack n w r)) _ h2, hR i hi, tabT_get,
      CFSG.KS.Raw.Orb.unpack_get hj, (h3 i hi).2]
  · rw [Nat.zero_add, hP m (by omega), Array.set!_eq_setIfInBounds]
    have hm' : pg w (mask w) p m < R.size := by rw [hR.1]; exact (h3 m (by omega)).1
    have hi' : pg w (mask w) p i < R.size := by rw [hR.1]; exact (h3 i (by omega)).1
    rw [getElem!_pos _ _ (by simpa using hi')]
    rcases Nat.lt_or_ge i m with a | a
    · rw [Array.getElem_setIfInBounds_ne hi' fun e => absurd (hinj m (by omega) i (by omega) e)
        (by omega), ← getElem!_pos R _ hi']
      exact hR.2 i a
    · have e : i = m := by omega
      subst e
      exact Array.getElem_setIfInBounds_self _

theorem lt_of_canonK {n w m nw p : Nat} (h : canonK n w m nw p = true) : n < 4294967296 := by
  unfold canonK szOK at h
  have h1 := ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 h).1).1
  have : n < 16777216 := Eq.mp Nat.blt_eq h1
  omega

end CFSG.KS.MulH

end
