module

public import CFSG.Certificates.Kernel.M24G.ListChecksSound
public import Mathlib.Data.List.Perm.Subperm

public section

namespace CFSG.KC.M24G

open CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

def six (t : Nat × Nat × Nat) : List (Nat × Nat) :=
  [(t.1, t.2.1), (t.2.1, t.1), (t.1, t.2.2), (t.2.2, t.1), (t.2.1, t.2.2), (t.2.2, t.2.1)]

theorem trioItem_facts {t : Nat × Nat × Nat} (h : trioItem t = true) :
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 &&& t.2.1 = 0 ∧ t.1 &&& t.2.2 = 0 ∧ t.2.1 &&& t.2.2 = 0 ∧
      t.1 ||| t.2.1 ||| t.2.2 = Native.full := by
  unfold trioItem at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, d1⟩, d2⟩, d3⟩, f⟩ := h
  exact ⟨a1, a2, d1, d2, d3, f⟩

theorem xor_of_disj {x y z : Nat} (h1 : x &&& y = 0) (h2 : x &&& z = 0) (h3 : y &&& z = 0) :
    x ||| y ||| z = x ^^^ y ^^^ z := by
  apply Nat.eq_of_testBit_eq
  intro i
  have a := congrArg (Nat.testBit · i) h1
  have b := congrArg (Nat.testBit · i) h2
  have c := congrArg (Nat.testBit · i) h3
  simp only [Nat.testBit_and, Nat.zero_testBit] at a b c
  simp only [Nat.testBit_or, Nat.testBit_xor]
  revert a b c
  cases x.testBit i <;> cases y.testBit i <;> cases z.testBit i <;> decide

theorem sort3_six {t : Nat × Nat × Nat} (h : trioItem t = true) {p : Nat × Nat} (hp : p ∈ six t) :
    Native.sort3 p.1 p.2 (Native.full ^^^ p.1 ^^^ p.2) = t := by
  obtain ⟨x, y, z⟩ := t
  obtain ⟨a1, a2, d1, d2, d3, f⟩ := trioItem_facts h
  simp only at a1 a2 d1 d2 d3 f
  rw [← f, xor_of_disj d1 d2 d3]
  simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hp
  have c : ∀ u v w : Nat, (u ^^^ v ^^^ w) ^^^ u ^^^ v = w := by
    intro u v w
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases u.testBit i <;> cases v.testBit i <;> cases w.testBit i <;> rfl
  have c' : ∀ u v w : Nat, (u ^^^ v ^^^ w) ^^^ v ^^^ u = w := by
    intro u v w
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases u.testBit i <;> cases v.testBit i <;> cases w.testBit i <;> rfl
  have c2 : ∀ u v w : Nat, (u ^^^ v ^^^ w) ^^^ u ^^^ w = v := by
    intro u v w
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases u.testBit i <;> cases v.testBit i <;> cases w.testBit i <;> rfl
  have c2' : ∀ u v w : Nat, (u ^^^ v ^^^ w) ^^^ w ^^^ u = v := by
    intro u v w
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases u.testBit i <;> cases v.testBit i <;> cases w.testBit i <;> rfl
  have c3 : ∀ u v w : Nat, (u ^^^ v ^^^ w) ^^^ v ^^^ w = u := by
    intro u v w
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases u.testBit i <;> cases v.testBit i <;> cases w.testBit i <;> rfl
  have c3' : ∀ u v w : Nat, (u ^^^ v ^^^ w) ^^^ w ^^^ v = u := by
    intro u v w
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor]
    cases u.testBit i <;> cases v.testBit i <;> cases w.testBit i <;> rfl
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [c, c', c2, c2', c3, c3'] <;> unfold Native.sort3 <;> split_ifs <;>
    simp only [Prod.mk.injEq] <;> omega

theorem six_nodup {t : Nat × Nat × Nat} (h : trioItem t = true) : (six t).Nodup := by
  obtain ⟨a1, a2, -⟩ := trioItem_facts h
  obtain ⟨x, y, z⟩ := t
  simp only at a1 a2
  simp [six]
  omega

theorem sum_six : ∀ l : List (Nat × Nat × Nat), (l.map fun t => (six t).length).sum = 6 * l.length
  | [] => rfl
  | t :: l => by
    rw [List.map_cons, List.sum_cons, sum_six l, List.length_cons]
    have : (six t).length = 6 := rfl
    omega

variable {O oP oG : List Nat} {posO : KTree (Nat × Nat)}
  (hO : replayOK id (Native.genTabs.map Native.img) 255 1000 O oP oG posO = true)
  (hOl : O.length = 759) (hB : baseOK posO = true)
  {T : List (Nat × Nat × Nat)} {tP tG : List Nat} {posT : KTree (Nat × Nat)}
  (hT : replayOK Native.key3 (Native.genTabs.map Native.imgTrio) Native.baseTrio 5000 T tP tG posT =
    true)
  (hTl : T.length = 3795) (hTi : T.all trioItem = true)

include hT in
theorem trio_nodup : T.Nodup := by
  have hpos := (replay_facts hT).1
  refine List.pairwise_iff_getElem.2 fun i j hi hj hij e => ?_
  have := posOK_inj hpos hi hj (congrArg Native.key3 e)
  omega

include hO hOl hB hT hTl hTi in
theorem pairsOK_of_count (hc : disjCount O = 6 * 3795) : pairsOK O posT = true := by
  have hti : ∀ t ∈ T, trioItem t = true := fun t ht => List.all_eq_true.1 hTi t ht
  let D := O.flatMap fun a => (O.filter fun b => a &&& b == 0 && a != b).map (a, ·)
  let E := T.flatMap six
  have hD : D.length = 6 * 3795 := by
    rw [← hc, List.length_flatMap]
    simp only [List.length_map, disjCount]
  have hE : E.length = 6 * 3795 := by
    rw [List.length_flatMap, ← hTl]
    exact sum_six T
  have hEn : E.Nodup := by
    refine List.nodup_flatMap.2 ⟨fun t ht => six_nodup (hti t ht), ?_⟩
    refine (trio_nodup hT).imp_of_mem fun {t t'} ht ht' hne => ?_
    intro p hp hp'
    exact hne ((sort3_six (hti t ht) hp).symm.trans (sort3_six (hti t' ht') hp'))
  have hED : E ⊆ D := by
    intro p hp
    obtain ⟨t, ht, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨a1, a2, d1, d2, d3, -⟩ := trioItem_facts (hti t ht)
    have hoc := trio_octs hO hOl hB hT ht
    have m1 : t.1 ∈ O := hoc _ (by simp [Native.octsT])
    have m2 : t.2.1 ∈ O := hoc _ (by simp [Native.octsT])
    have m3 : t.2.2 ∈ O := hoc _ (by simp [Native.octsT])
    simp only [six, List.mem_cons, List.not_mem_nil, or_false] at hp
    refine List.mem_flatMap.2 ?_
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, m1, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨m2, by simp [d1]; omega⟩, rfl⟩⟩
    · exact ⟨_, m2, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨m1, by simp [Nat.and_comm, d1]; omega⟩,
        rfl⟩⟩
    · exact ⟨_, m1, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨m3, by simp [d2]; omega⟩, rfl⟩⟩
    · exact ⟨_, m3, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨m1, by simp [Nat.and_comm, d2]; omega⟩,
        rfl⟩⟩
    · exact ⟨_, m2, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨m3, by simp [d3]; omega⟩, rfl⟩⟩
    · exact ⟨_, m3, List.mem_map.2 ⟨_, List.mem_filter.2 ⟨m2, by simp [Nat.and_comm, d3]; omega⟩,
        rfl⟩⟩
  have hperm := (hEn.subperm hED).perm_of_length_le (by rw [hD, hE])
  unfold pairsOK
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
  by_cases h1 : a &&& b = 0
  · by_cases h2 : a = b
    · exact Or.inl (Or.inr h2)
    · right
      have hpD : (a, b) ∈ D :=
        List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, List.mem_filter.2 ⟨hb, by simp [h1, h2]⟩, rfl⟩⟩
      obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.1 (hperm.mem_iff.2 hpD)
      have e := sort3_six (hti t ht) hpt
      simp only at e
      rw [e]
      exact idxK_mem (replay_facts hT).1 hTl ht
  · exact Or.inl (Or.inl h1)

end CFSG.KC.M24G
