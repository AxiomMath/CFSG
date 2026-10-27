module

public import CFSG.Certificates.Kernel.SporSch.HNF5RankSound
public import CFSG.Certificates.Kernel.SporSch.HNF5KronSound

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

@[expose] def KrOK (MT OP L R : Nat → Nat) (k : Nat) : Prop :=
  Canon5 (slice5 MT k) ∧
    (OP k = 0 → Canon5 (slice5 MT (L k)) → Canon5 (slice5 MT (R k)) →
      ∀ i < 133, vm5 (slice5 MT (R k)) (slice5 MT (L k) i) = slice5 MT k i) ∧
    (OP k = 1 → ∀ i < 133, slice5 MT (L k) i = slice5 MT k i)

theorem krOK_of_blk {MT OP L R : Nat → Nat} {a n k : Nat} (h : krBlk MT OP L R a n = true)
    (hk1 : a ≤ k) (hk2 : k < a + n) : KrOK MT OP L R k :=
  F5Kron.krBlk_sound h hk1 hk2

theorem krOK_mul {MT OP L R : Nat → Nat} {k l r : Nat} (h : KrOK MT OP L R k)
    (hcl : Canon5 (slice5 MT l)) (hcr : Canon5 (slice5 MT r)) (ho : OP k = 0) (hl : L k = l)
    (hr : R k = r) :
    mulM 5 133 (rows5 (slice5 MT l)) (rows5 (slice5 MT r)) = rows5 (slice5 MT k) := by
  subst hl hr
  exact mulM5_sound hcl hcr (h.2.1 ho hcl hcr)

theorem krOK_copy {MT OP L R : Nat → Nat} {k l : Nat} (h : KrOK MT OP L R k) (ho : OP k = 1)
    (hl : L k = l) : rows5 (slice5 MT l) = rows5 (slice5 MT k) := by
  subst hl
  exact rows5_congr (h.2.2 ho)

theorem chain5K_eq {MT OP L R : Nat → Nat} {n : Nat} (hok : ∀ k < n, KrOK MT OP L R k)
    {S Si : Array (Array (Array Nat))} {lt : Int → Nat} {w : List Int} {o : Nat}
    (hlet : ∀ l ∈ w, mletter S Si l = rows5 (slice5 MT (lt l)))
    (h : chainOK OP L R lt n w o = true) :
    mword S Si w = rows5 (slice5 MT (o + w.length - 1)) := by
  have hcan : ∀ k < n, Canon5 (slice5 MT k) := fun k hk => (hok k hk).1
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, hlen⟩, hl⟩, ho⟩, hL⟩, hs⟩ := h
  have hlt : ∀ t < w.length, mletter S Si (w.getD t 0) = rows5 (slice5 MT (lt (w.getD t 0))) ∧
      lt (w.getD t 0) < n := fun t ht => by
    have hm : w.getD t 0 ∈ w := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    exact ⟨hlet _ hm, hl _ hm⟩
  have key : ∀ t, t < w.length →
      mword S Si (w.drop (w.length - 1 - t)) = rows5 (slice5 MT (o + t)) := by
    intro t
    induction t with
    | zero =>
      intro _
      have e : w.drop (w.length - 1 - 0) = [w.getD (w.length - 1) 0] := by
        rw [Nat.sub_zero, List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
          List.getD_eq_getElem _ _ (by omega)]
      rw [e, mword_one, (hlt _ (by omega)).1, mulM5_idR (hcan _ (hlt _ (by omega)).2),
        Nat.add_zero]
      exact krOK_copy (hok o (by omega)) ho hL
    | succ t ih =>
      intro ht
      obtain ⟨⟨a, b⟩, c⟩ := hs t (by omega)
      have e : w.drop (w.length - 1 - (t + 1)) =
          w.getD (w.length - 2 - t) 0 :: w.drop (w.length - 1 - t) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ (by omega)]
        congr 2 <;> omega
      rw [e, mword, ih (by omega), (hlt _ (by omega)).1,
        krOK_mul (hok _ (by omega)) (hcan _ (hlt _ (by omega)).2) (hcan _ (by omega)) a b c]
      rfl
  have := key (w.length - 1) (by omega)
  have e1 : w.length - 1 - (w.length - 1) = 0 := by omega
  have e2 : o + (w.length - 1) = o + w.length - 1 := by omega
  rwa [e1, List.drop_zero, e2] at this

end CFSG.KS.SporSch

end
