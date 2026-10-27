module

public import CFSG.Certificates.Kernel.MonsterB.BfsCore
public import CFSG.RankThree.PartTwo.Sec4.Ronan148VJ2OverInputs

public section

namespace CFSG.KC.OrbLoop

open CFSG.KC.Bfs CFSG.RankThree.PartTwo.Sec4.Ronan148V CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem eqA_refl (n : ℕ) (t : Array ℕ) : eqA n t t = true := by
  rw [eqA, allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem eq_of_eqA_size {n : ℕ} {t u : Array ℕ} (h : eqA n t u = true) (ht : t.size = n)
    (hu : u.size = n) : t = u := by
  rw [eqA, allLt_iff] at h
  refine Array.ext (ht.trans hu.symm) fun i hi1 hi2 => ?_
  have := h i (ht ▸ hi1)
  rwa [beq_iff_eq, getElem!_pos t i hi1, getElem!_pos u i hi2] at this

variable (T : Finset (Array ℕ))

structure Inv (S : Array (Array ℕ)) (i : ℕ) : Prop where
  sub : ∀ x ∈ S, x ∈ T
  nd : S.toList.Nodup
  le : i ≤ S.size
  pos : 0 < S.size
  root : S[0]! = zArr
  done : ∀ j < i, ∀ k < 2, zConj k S[j]! ∈ S

variable {T}

theorem size_le {S : Array (Array ℕ)} (hS : ∀ x ∈ S, x ∈ T) (hnd : S.toList.Nodup) :
    S.size ≤ T.card := by
  have h1 : S.toList.toFinset ⊆ T := fun x hx => hS x (by simpa using hx)
  have h2 := Finset.card_le_card h1
  rwa [List.toFinset_card_of_nodup hnd, Array.length_toList] at h2

theorem push_spec (hsz : ∀ x ∈ T, x.size = 315) {S : Array (Array ℕ)} {y : Array ℕ}
    (hS : ∀ x ∈ S, x ∈ T) (hnd : S.toList.Nodup) (hy : y ∈ T) :
    (∀ x, x ∈ orbPush S y ↔ x ∈ S ∨ x = y) ∧ (orbPush S y).toList.Nodup ∧
      S.size ≤ (orbPush S y).size ∧ ∀ j < S.size, (orbPush S y)[j]! = S[j]! := by
  unfold orbPush
  split
  · rename_i h
    rw [Array.any_eq_true] at h
    obtain ⟨i, hi, he⟩ := h
    have hm : S[i] ∈ S := Array.getElem_mem hi
    have e : y = S[i] := eq_of_eqA_size he (hsz y hy) (hsz _ (hS _ hm))
    refine ⟨fun x => ⟨Or.inl, ?_⟩, hnd, le_rfl, fun _ _ => rfl⟩
    rintro (h | rfl)
    · exact h
    · rw [e]
      exact hm
  · rename_i h
    have hn : y ∉ S := by
      intro hm
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hm
      exact h (Array.any_eq_true.2 ⟨i, hi, eqA_refl _ _⟩)
    refine ⟨fun x => Array.mem_push, ?_, by simp, fun j hj => push_get_lt S y hj⟩
    rw [Array.toList_push, List.nodup_append]
    refine ⟨hnd, List.nodup_singleton y, ?_⟩
    intro a ha b hb e
    rw [List.mem_singleton] at hb
    subst hb e
    exact hn (Array.mem_toList_iff.1 ha)

theorem step_spec (hsz : ∀ x ∈ T, x.size = 315) (hcl : ∀ x ∈ T, ∀ k < 2, zConj k x ∈ T)
    {S : Array (Array ℕ)} {i : ℕ} (hI : Inv T S i) (hi : i < S.size) :
    Inv T (orbStep S i) (i + 1) := by
  have e : orbStep S i = orbPush (orbPush S (zConj 0 S[i]!)) (zConj 1 S[i]!) := rfl
  rw [e]
  have hx : S[i]! ∈ T := by
    rw [getElem!_pos S i hi]
    exact hI.sub _ (Array.getElem_mem hi)
  obtain ⟨m1, n1, l1, g1⟩ := push_spec hsz hI.sub hI.nd (hcl _ hx 0 (by norm_num))
  have hS1 : ∀ x ∈ orbPush S (zConj 0 S[i]!), x ∈ T := by
    intro x hx'
    rcases (m1 x).1 hx' with h | rfl
    · exact hI.sub x h
    · exact hcl _ hx 0 (by norm_num)
  obtain ⟨m2, n2, l2, g2⟩ := push_spec hsz hS1 n1 (hcl _ hx 1 (by norm_num))
  have hsub : ∀ x ∈ S, x ∈ orbPush (orbPush S (zConj 0 S[i]!)) (zConj 1 S[i]!) :=
    fun x h => (m2 x).2 (Or.inl ((m1 x).2 (Or.inl h)))
  have hget : ∀ j < S.size,
      (orbPush (orbPush S (zConj 0 S[i]!)) (zConj 1 S[i]!))[j]! = S[j]! := by
    intro j hj
    rw [g2 j (lt_of_lt_of_le hj l1), g1 j hj]
  refine ⟨fun x hx' => ?_, n2, by omega, by omega, ?_, fun j hj k hk => ?_⟩
  · rcases (m2 x).1 hx' with h | rfl
    · exact hS1 x h
    · exact hcl _ hx 1 (by norm_num)
  · rw [hget 0 hI.pos]
    exact hI.root
  · rw [hget j (by omega)]
    rcases Nat.lt_or_ge j i with hj' | hj'
    · exact hsub _ (hI.done j hj' k hk)
    · have : j = i := by omega
      subst this
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · exact (m2 _).2 (Or.inl ((m1 _).2 (Or.inr rfl)))
      · exact (m2 _).2 (Or.inr rfl)

theorem loop_spec (hsz : ∀ x ∈ T, x.size = 315) (hcl : ∀ x ∈ T, ∀ k < 2, zConj k x ∈ T) :
    ∀ (f : ℕ) (S : Array (Array ℕ)) (i : ℕ), Inv T S i → T.card < f + i →
      (∀ x ∈ orbLoop f S i, x ∈ T) ∧ 0 < (orbLoop f S i).size ∧ (orbLoop f S i)[0]! = zArr ∧
        ∀ j < (orbLoop f S i).size, ∀ k < 2, zConj k (orbLoop f S i)[j]! ∈ orbLoop f S i
  | 0, S, i, hI, hf => by
    have hb := size_le hI.sub hI.nd
    rw [orbLoop]
    exact ⟨hI.sub, hI.pos, hI.root, fun j hj => hI.done j (by omega)⟩
  | f + 1, S, i, hI, hf => by
    rw [orbLoop]
    split
    · rename_i hi
      exact loop_spec hsz hcl f _ (i + 1) (step_spec hsz hcl hI hi) (by omega)
    · rename_i hi
      exact ⟨hI.sub, hI.pos, hI.root, fun j hj => hI.done j (by omega)⟩

theorem zOrbit_spec (hroot : zArr ∈ T) (hcl : ∀ x ∈ T, ∀ k < 2, zConj k x ∈ T)
    (hR : ∀ x ∈ T, Reach zConj 2 zArr x) (hsz : ∀ x ∈ T, x.size = 315) (hcard : T.card ≤ 560) :
    (∀ x, x ∈ zOrbit () ↔ x ∈ T) ∧ 0 < (zOrbit ()).size ∧ (zOrbit ())[0]! = zArr := by
  have h0 : Inv T #[zArr] 0 := by
    refine ⟨fun x hx => ?_, by simp, by simp, by simp, by simp, fun j hj => absurd hj (by omega)⟩
    rw [Array.mem_singleton] at hx
    rw [hx]
    exact hroot
  obtain ⟨hsub, hpos, h0', hdone⟩ := loop_spec hsz hcl 1000 #[zArr] 0 h0 (by omega)
  unfold zOrbit
  generalize orbLoop 1000 #[zArr] 0 = R at hsub hpos h0' hdone ⊢
  have hreach : ∀ y, Reach zConj 2 zArr y → y ∈ R := by
    intro y hy
    induction hy with
    | root =>
      rw [← h0', getElem!_pos _ 0 hpos]
      exact Array.getElem_mem hpos
    | step k hk _ ih =>
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ih
      have := hdone j hj k hk
      rwa [getElem!_pos _ j hj] at this
  exact ⟨fun x => ⟨hsub x, fun hx => hreach x (hR x hx)⟩, hpos, h0'⟩

end CFSG.KC.OrbLoop

end
