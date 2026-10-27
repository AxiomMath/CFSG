module

public import Certificates.Data.Kernel.LocalComp.Tits
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.TBfsSound

public section

namespace CFSG.KC.LocalComp.TitsSound

open CFSG.KC.Enum CFSG.KS CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th.Native CFSG.KC.LocalComp.Tits

private theorem foldr_range_succ' (f : Nat → Nat → Nat) (M s : Nat) :
    (List.range (M + 1)).foldr f s = (List.range M).foldr f (f M s) := by
  rw [List.range_succ, List.foldr_append]
  rfl

private theorem find_none {TP : Nat → Nat} {v : Nat} :
    ∀ (M s : Nat), (∀ i < M, TP i ≠ v) →
      (List.range M).foldr (fun i s => nIf(Nat.beq (TP i) v, i, s)) s = s
  | 0, _, _ => rfl
  | M + 1, s, h => by
    rw [foldr_range_succ']
    have hb : Nat.beq (TP M) v = false :=
      Bool.eq_false_iff.2 fun e => h M (by omega) (Nat.eq_of_beq_eq_true e)
    rw [hb]
    exact find_none M s (fun i hi => h i (by omega))

private theorem find_some {TP : Nat → Nat} {v j : Nat} (hj : TP j = v)
    (hlt : ∀ i < j, TP i ≠ v) :
    ∀ (M s : Nat), j < M →
      (List.range M).foldr (fun i s => nIf(Nat.beq (TP i) v, i, s)) s = j
  | 0, _, h => by omega
  | M + 1, s, h => by
    rw [foldr_range_succ']
    by_cases hM : j = M
    · subst hM
      have hb : Nat.beq (TP j) v = true := by rw [hj]; exact Nat.beq_refl v
      rw [hb]
      exact find_none j j hlt
    · exact find_some hj hlt M _ (by omega)

private theorem mono_of_inc {N : Nat} {TP : Nat → Nat} (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1)) :
    ∀ j i, i < j → j < N → TP i < TP j
  | 0, i, h, _ => by omega
  | j + 1, i, h, hj => by
    by_cases e : i = j
    · subst e; exact hinc i hj
    · exact Nat.lt_trans (mono_of_inc hinc j i (by omega) (by omega)) (hinc j hj)

theorem idxK_of_eq {N : Nat} {TP : Nat → Nat} (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1))
    {i : Nat} (hi : i < N) : idxK N TP (TP i) = i := by
  unfold idxK
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  exact find_some rfl (fun k hk => Nat.ne_of_lt (mono_of_inc hinc i k hk hi)) N N hi

theorem idxK_of_ne {N : Nat} {TP : Nat → Nat} {v : Nat} (hv : ∀ i < N, TP i ≠ v) :
    idxK N TP v = N := by
  unfold idxK
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  exact find_none N N hv

private theorem le_of_inc {N : Nat} {TP : Nat → Nat} (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1)) :
    ∀ i, i < N → i ≤ TP i
  | 0, _ => Nat.zero_le _
  | i + 1, h => by
    have := le_of_inc hinc i (by omega)
    have := hinc i h
    omega

private def Inv (N : Nat) (TP : Nat → Nat) (v j : Nat) (b : Nat × Nat) : Prop :=
  b.1 ≤ b.2 ∧ b.2 ≤ N ∧ (∀ i < b.1, TP i < v) ∧ (∀ i, b.2 ≤ i → i < N → v ≤ TP i) ∧
    b.2 - b.1 ≤ N / 2 ^ j

private def bsBody (pts : Array Nat) (v : Nat) (_ : Nat) (s : Nat × Nat) :
    Id (ForInStep (Nat × Nat)) :=
  if s.1 < s.2 then
    if pts[(s.1 + s.2) / 2]! < v then pure (ForInStep.yield ((s.1 + s.2) / 2 + 1, s.2))
    else pure (ForInStep.yield (s.1, (s.1 + s.2) / 2))
  else pure (ForInStep.yield (s.1, s.2))

private theorem bsearch_eq (pts : Array Nat) (v : Nat) :
    bsearch pts v =
      (let s := Id.run (forIn (List.range' 0 64) ((0 : Nat), pts.size) (bsBody pts v))
      if (decide (s.1 < pts.size) && pts[s.1]! == v) = true then s.1 else pts.size) := by
  unfold bsearch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private theorem loop_inv {N : Nat} {TP : Nat → Nat} (hN : N ≤ 2 ^ 52)
    (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1)) (v : Nat) :
    Inv N TP v 64 (Id.run (forIn (List.range' 0 64) ((0 : Nat), N)
      (bsBody (Array.ofFn (n := N) fun i => TP i.val) v))) := by
  have hmono := mono_of_inc hinc
  have := CFSG.KS.TBfs.forIn_list_yield (List.range' 0 64) ((0 : Nat), N)
    (bsBody (Array.ofFn (n := N) fun i => TP i.val) v) (fun j b => Inv N TP v j b) ?_ ?_
  · simpa using this
  · intro j hj b hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := hb
    have hd : N / 2 ^ (j + 1) = N / 2 ^ j / 2 := by
      rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
    by_cases hlh : b.1 < b.2
    · by_cases hm : TP ((b.1 + b.2) / 2) < v
      · refine ⟨((b.1 + b.2) / 2 + 1, b.2), ?_, ?_⟩
        · simp only [bsBody, hlh, if_true, CFSG.KS.TBfs.ofFn_get (by omega : (b.1 + b.2) / 2 < N), hm, if_false]
        · refine ⟨by simp only; omega, by simp only; omega, fun i hi => ?_, h4, ?_⟩
          · simp only at hi
            rcases Nat.lt_or_ge i b.1 with hi' | hi'
            · exact h3 i hi'
            · rcases Nat.eq_or_lt_of_le (by omega : i ≤ (b.1 + b.2) / 2) with e | e
              · rw [e]; exact hm
              · exact Nat.lt_trans (hmono _ i e (by omega)) hm
          · simp only
            rw [hd]
            omega
      · refine ⟨(b.1, (b.1 + b.2) / 2), ?_, ?_⟩
        · simp only [bsBody, hlh, if_true, CFSG.KS.TBfs.ofFn_get (by omega : (b.1 + b.2) / 2 < N), hm, if_false]
        · refine ⟨by simp only; omega, by simp only; omega, h3, fun i hi hiN => ?_, ?_⟩
          · simp only at hi
            rcases Nat.eq_or_lt_of_le hi with e | e
            · rw [← e]; omega
            · have := hmono i _ e hiN
              omega
          · simp only
            rw [hd]
            omega
    · refine ⟨b, by simp only [bsBody, hlh, if_false], h1, h2, h3, h4, ?_⟩
      rw [hd]; omega
  · refine ⟨Nat.zero_le _, Nat.le_refl _, fun i hi => by omega, fun i hi hiN => by omega, ?_⟩
    simp

theorem bsearch_ofFn {N : Nat} {TP : Nat → Nat} (hlt : ∀ i < N, TP i < 2 ^ 52)
    (hinc : ∀ i, i + 1 < N → TP i < TP (i + 1)) (v : Nat) :
    bsearch (Array.ofFn (n := N) fun i => TP i.val) v = idxK N TP v := by
  have hsz : (Array.ofFn (n := N) fun i => TP i.val).size = N := by simp
  have hN : N ≤ 2 ^ 52 := by
    refine Nat.le_of_not_lt fun hc => ?_
    have h1 := le_of_inc hinc (2 ^ 52) (by omega)
    have h2 := hlt (2 ^ 52) (by omega)
    omega
  have hmono := mono_of_inc hinc
  rw [bsearch_eq, hsz]
  have key := loop_inv hN hinc v
  generalize Id.run (forIn (List.range' 0 64) ((0 : Nat), N)
      (bsBody (Array.ofFn (n := N) fun i => TP i.val) v)) = s at key ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := key
  have h0 : N / 2 ^ 64 = 0 := Nat.div_eq_of_lt (Nat.lt_of_le_of_lt hN
    (Nat.pow_lt_pow_right (by decide) (by decide)))
  have hs : s.1 = s.2 := by omega
  dsimp only
  by_cases hlo : s.1 < N
  · rw [CFSG.KS.TBfs.ofFn_get hlo]
    by_cases he : TP s.1 = v
    · have : (decide (s.1 < N) && TP s.1 == v) = true := by simp [hlo, he]
      rw [if_pos this, ← he, idxK_of_eq hinc hlo]
    · have : ¬ (decide (s.1 < N) && TP s.1 == v) = true := by simp [hlo, he]
      rw [if_neg this]
      refine (idxK_of_ne fun i hi hiv => ?_).symm
      rcases Nat.lt_or_ge i s.1 with e | e
      · have := h3 i e; omega
      · rcases Nat.eq_or_lt_of_le e with e' | e'
        · rw [e'] at he; exact he hiv
        · have := h4 s.1 (by omega) hlo
          have := hmono i s.1 (by omega) hi
          omega
  · have : ¬ (decide (s.1 < N) && (Array.ofFn (n := N) fun i => TP i.val)[s.1]! == v) = true := by
      simp [hlo]
    rw [if_neg this]
    refine (idxK_of_ne fun i hi hiv => ?_).symm
    have := h3 i (by omega); omega

end CFSG.KC.LocalComp.TitsSound

end
