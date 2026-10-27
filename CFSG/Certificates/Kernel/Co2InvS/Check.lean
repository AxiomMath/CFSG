module

public import CFSG.Certificates.Kernel.Co2InvS.Enum

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2InvS

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Inv
  CFSG.KC.Bfs CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {CF G Y FW : Nat → Nat}

@[expose] def YBind (Y : Nat → Nat) : Prop :=
  candYs.size = 54 ∧ ∀ c < 54, candYs[c]! = unpackR 22 (Y c)

theorem fuseOK_of_K (hY : YBind Y) {X c : Nat} (h : fuseK Y X c = true) :
    fuseOK candYs (unpackR 22 X) = true := by
  unfold fuseK at h
  rw [andK_eq, Bool.and_eq_true] at h
  have hc : c < 54 := blt_iff.1 h.1
  unfold fuseOK
  rw [List.any_eq_true]
  refine ⟨c, List.mem_range.2 (by rw [hY.1]; exact hc), ?_⟩
  rw [hY.2 c hc, mulRows_unpack, oddPowOK_unpack (mulV_lt _ _)]
  exact h.2

theorem enumCheck_of_K (hR : Recs CF G Y FW sOrder) (hY : YBind Y) {RI : Nat → Nat}
    (hreps : ∀ r < 3, RI r < sOrder ∧ co2InvReps[r]! = Lf CF (RI r)) :
    enumCheck enumS candYs = true := by
  obtain ⟨hsize, helem, htree, htbl, hpos⟩ := enum_facts hR
  have hgs := hR.gsize
  have hposk : ∀ k < sOrder, (bfsS co2InvGens sOrder).pos.getD (Lf CF k) 0 = k := by
    intro k hk
    rw [Std.HashMap.getD_eq_getD_getElem?, (hpos _ k).2 ⟨hk, rfl⟩]
    rfl
  have hE : enumS = bfsS co2InvGens sOrder := rfl
  unfold enumCheck
  rw [hE]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨hsize, ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun k hk j hj => ?_⟩,
    fun k hk => ?_⟩, fun k hk => ?_⟩, fun r hr => ?_⟩
  · rw [helem 0 (by decide), Lf, hR.zero, ← idRows_eq]
  · rw [helem k hk, Lf]
    exact wfRows_unpack _
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inl h0
    · obtain ⟨h1, h2, h3⟩ := htree k h0 hk
      rw [hgs] at h2
      exact Or.inr ⟨⟨h1, h2⟩, h3⟩
  · rw [← hgs] at hj
    obtain ⟨ht, hl⟩ := Lf_tbl hR k hk j hj
    rw [htbl k hk j hj, helem _ ht, helem k hk]
    exact ⟨ht, hl⟩
  · rw [helem k hk]
    exact hposk k hk
  · rw [helem k hk, Lf, isInvolRows_unpack (elemAt_lt CF k)]
    cases hi : involK (elemAt CF k)
    · exact Or.inl rfl
    · exact Or.inr (fuseOK_of_K hY ((rec_spec (hR.ok k hk)).2.2.2.2 hi))
  · obtain ⟨h1, h2⟩ := hreps r hr
    rw [h2, hposk _ h1, helem _ h1]
    exact ⟨h1, rfl⟩

end CFSG.KC.Co2InvS

end
