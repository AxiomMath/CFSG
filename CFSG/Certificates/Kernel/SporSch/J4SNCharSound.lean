module

public import Certificates.Data.Kernel.SporSch.J4SNChar
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound
public import CFSG.Sporadic.Schreier.J4SNCharData
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.SporSch.C11

open CFSG.Sporadic.J4Schreier

private theorem j4n_t1 (t : Nat × Nat × Nat) : t1 t = t.1 := by
  rcases t with ⟨a, b, c⟩
  rfl

private theorem j4n_t2 (t : Nat × Nat × Nat) : t2 t = t.2.1 := by
  rcases t with ⟨a, b, c⟩
  rfl

private theorem j4n_t3 (t : Nat × Nat × Nat) : t3 t = t.2.2 := by
  rcases t with ⟨a, b, c⟩
  rfl

private theorem j4n_lenT : ∀ L : List (Nat × Nat × Nat), lenT L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (j4n_lenT L)

private theorem j4n_nthT : ∀ (L : List (Nat × Nat × Nat)) (k : Nat), k < L.length →
    nthT L k = L[k]!
  | [], k, h => absurd h (Nat.not_lt_zero k)
  | x :: L, 0, _ => (List.getElem!_cons_zero).symm
  | x :: L, k + 1, h => by
    rw [List.getElem!_cons_succ]
    exact j4n_nthT L k (Nat.lt_of_succ_lt_succ h)

private theorem j4n_quad_eq {E : Nat → Nat} (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    {c c' : Nat} (hc : c < 1024) (hc' : c' < 1024) (v : Nat) :
    quadAt c c' v = quadK (E c) (E c') v := by
  have e1 := hE c hc
  have e2 := hE c' hc'
  simp only [quadAt, quadK, e1, e2, app_eq, CFSG.KS.Raw.Orb.strictB_eq]
  rw [Bool.eq_iff_iff]
  simp [Nat.beq_eq]

theorem quadK_sound {E : Nat → Nat} (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    {c c' v : Nat} (hc : c < 1024) (hc' : c' < 1024) (h : quadK (E c) (E c') v = true) :
    quadAt c c' v = true := by
  rw [j4n_quad_eq hE hc hc']
  exact h

theorem forestK_sound {CJ : Nat → Nat}
    (hC : conjTab.size = 4 ∧ ∀ i < 4, conjTab[i]! = unpackW 10 1024 (CJ i))
    {L : List (Nat × Nat × Nat)} (h : forestK CJ L = true) : classForestOK L = true := by
  unfold forestK at h
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1⟩ := h
  rw [j4n_lenT] at h0 h1
  have key : ∀ k < L.length, (L[k]!).1 < 1024 ∧ (k = 0 ∨ ((L[k]!).2.1 < k ∧ (L[k]!).2.2 < 4 ∧
      (L[k]!).1 = ent 10 (CJ (L[k]!).2.2) (L[(L[k]!).2.1]!).1)) := by
    intro k hk
    have hk' := CFSG.KS.Raw.Orb.allN_iff.1 h1 k hk
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, j4n_t1, j4n_t2, j4n_t3,
      j4n_nthT L k hk, Nat.blt_eq, Nat.beq_eq] at hk'
    split_ifs at hk' with hx hk0 hp hg
    · exact ⟨hx, Or.inl hk0⟩
    · refine ⟨hx, Or.inr ⟨hp, hg, ?_⟩⟩
      rw [j4n_nthT L _ (by omega)] at hk'
      exact Nat.eq_of_beq_eq_true hk'
  unfold classForestOK
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨?_, fun k hk => ?_⟩
  · have h0' : 0 < L.length := Nat.blt_eq.mp h0
    cases L with
    | nil => exact absurd h0' (Nat.lt_irrefl 0)
    | cons x L => rfl
  · have hk' := List.mem_range.1 hk
    obtain ⟨hx, hr⟩ := key k hk'
    rw [Bool.and_eq_true]
    refine ⟨by simpa using hx, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rcases hr with hk0 | ⟨hp, hg, hxe⟩
    · exact Or.inl hk0
    ·
      have hy := (key _ (by omega : (L[k]!).2.1 < L.length)).1
      have ec : (conjTab[(L[k]!).2.2]!)[(L[(L[k]!).2.1]!).1]! =
          ent 10 (CJ (L[k]!).2.2) (L[(L[k]!).2.1]!).1 := by
        rw [hC.2 _ hg, unpackW_get hy]
      exact Or.inr ⟨⟨hp, hg⟩, by rw [ec]; exact hxe⟩

private theorem j4n_k3K : ∀ L : List (Nat × Nat × Nat), k3K L = true →
    L.all (fun x => x.1 == 118 || x.1 == 448 || x.1 == 502) = true
  | [], _ => rfl
  | x :: L, h => by
    unfold k3K at h
    dsimp only at h
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, j4n_k3K L h.2⟩
    have hx : t1 x = 118 ∨ t1 x = 448 ∨ t1 x = 502 := by
      have h1 := h.1
      rw [CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bIf_eq] at h1
      split_ifs at h1 with h2 h3
      · exact Or.inl (Nat.eq_of_beq_eq_true h2)
      · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h3))
      · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h1))
    rw [j4n_t1] at hx
    simp only [Bool.or_eq_true, beq_iff_eq]
    omega

theorem witK_sound {E : Nat → Nat} (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    {L : List (Nat × Nat × Nat)} {w : Option (Nat × Nat × Nat)} (h : witK E L w = true) :
    classWitOK L w = true := by
  rcases w with _ | ⟨a, b, v⟩
  · exact j4n_k3K L h
  · unfold witK at h
    dsimp only at h
    simp only [j4n_t1, j4n_t2, j4n_t3, CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq, j4n_lenT] at h
    obtain ⟨ha, hb, hv, hea, heb, hq⟩ := h
    rw [j4n_nthT L a ha] at hea hq
    rw [j4n_nthT L b hb] at heb hq
    rw [← j4n_quad_eq hE hea heb v] at hq
    simp only [classWitOK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨ha, hb⟩, hv⟩, hq⟩

private theorem j4n_memK_inner (e : Nat) : ∀ L : List (Nat × Nat × Nat),
    List.rec (motive := fun _ => Bool) false
      (fun x _ ih2 => bIf(Nat.beq (t1 x) e, true, ih2)) L = true → e ∈ L.map Prod.fst
  | [], h => absurd h Bool.false_ne_true
  | x :: L, h => by
    dsimp only at h
    rw [CFSG.KS.Raw.Orb.bIf_eq] at h
    split_ifs at h with h1
    · exact List.mem_cons.2 (Or.inl ((Nat.eq_of_beq_eq_true h1).symm.trans (j4n_t1 x)))
    · exact List.mem_cons_of_mem _ (j4n_memK_inner e L h)

private theorem j4n_memK (e : Nat) : ∀ LL : List (List (Nat × Nat × Nat)), memK e LL = true →
    ∃ c < LL.length, e ∈ (LL[c]!).map Prod.fst
  | [], h => absurd h Bool.false_ne_true
  | L :: LL, h => by
    unfold memK at h
    dsimp only at h
    rw [CFSG.KS.Raw.Orb.bIf_eq] at h
    split_ifs at h with h1
    · exact ⟨0, Nat.succ_pos _, by rw [List.getElem!_cons_zero]; exact j4n_memK_inner e L h1⟩
    · obtain ⟨c, hc, hmem⟩ := j4n_memK e LL h
      exact ⟨c + 1, Nat.succ_lt_succ hc, by rw [List.getElem!_cons_succ]; exact hmem⟩

theorem coverK_sound {E : Nat → Nat} (hE : ∀ e < 1024, elementColumns[e]! = unpack11 (E e))
    {LL : List (List (Nat × Nat × Nat))} (h : coverK E LL = true) :
    ∀ e < 1024, e ≠ 0 → quadSelf e = true → ∃ c < LL.length, e ∈ (LL[c]!).map Prod.fst := by
  intro e he hne hq
  unfold coverK at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h e he
  have hne' : Nat.beq e 0 = false := by
    cases hb : Nat.beq e 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  simp only [CFSG.KS.Raw.Orb.bIf_eq, hne'] at h1
  by_cases hm : memK e LL = true
  · exact j4n_memK e LL hm
  ·
    exfalso
    rw [if_neg hm] at h1
    have hall : CFSG.KC.Enum.allN 2048 (fun v => quadK (E e) (E e) v) = true := by
      rw [CFSG.KS.Raw.Orb.allN_iff]
      intro v hv
      rw [← j4n_quad_eq hE he he v]
      unfold quadSelf at hq
      exact List.all_eq_true.1 hq v (List.mem_range.2 hv)
    rw [hall] at h1
    exact absurd h1 (by decide)

private theorem j4n_foldr_range {f : Nat → Nat → Nat} {g : Nat → Nat}
    (hf : ∀ i s, f i s = s + g i) : ∀ n s : Nat,
    (List.range n).foldr f s = s + ∑ i ∈ Finset.range n, g i
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil,
      j4n_foldr_range hf n (f n s), hf, Finset.sum_range_succ]
    omega

theorem fix2_sound {P Q n : Nat} (h : Nat.beq (fix2CntK P Q) n = true) :
    ((Finset.range 2048).filter fun a =>
      app11 (unpack11 P) a = a ∧ app11 (unpack11 Q) a = a).card = n := by
  rw [← Nat.eq_of_beq_eq_true h, fix2CntK, CFSG.KS.Raw.Orb.foldN_eq,
    j4n_foldr_range (g := fun a => if appK P a = a ∧ appK Q a = a then 1 else 0), Nat.zero_add,
    Finset.card_filter]
  · simp only [app_eq]
  · intro i s
    rw [CFSG.KS.Raw.Orb.nIf_eq, CFSG.KS.Raw.Orb.bAnd_eq]
    by_cases e1 : appK P i = i <;> by_cases e2 : appK Q i = i <;> simp [e1, e2, Nat.beq_eq]

end CFSG.KS.SporSch.C11

end
