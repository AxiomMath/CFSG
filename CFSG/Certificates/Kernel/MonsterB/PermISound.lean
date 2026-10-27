module

public import CFSG.Monster.B.TwoA.Census.SignCls

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.Code

theorem testBit_add_two_pow {a e : ℕ} (h : a.testBit e = false) (j : ℕ) :
    (a + 2 ^ e).testBit j = true ↔ (a.testBit j = true ∨ j = e) := by
  have h2 : 2 ^ (e + 1) = 2 * 2 ^ e := by ring
  have hlt : a % 2 ^ (e + 1) < 2 ^ (e + 1) := Nat.mod_lt _ (by positivity)
  have hr : a % 2 ^ (e + 1) < 2 ^ e := by
    by_contra hc
    have h3 := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (Nat.le_of_not_lt hc) hlt
    rw [Nat.testBit_mod_two_pow] at h3
    simp [h] at h3
  have ha : a = 2 ^ (e + 1) * (a / 2 ^ (e + 1)) ||| a % 2 ^ (e + 1) := by
    rw [← Nat.two_pow_add_eq_or_of_lt hlt]
    exact (Nat.div_add_mod _ _).symm
  have hb : a % 2 ^ (e + 1) + 2 ^ e < 2 ^ (e + 1) := by omega
  have e1 : a + 2 ^ e = 2 ^ (e + 1) * (a / 2 ^ (e + 1)) ||| (a % 2 ^ (e + 1) ||| 2 ^ e) := by
    rw [Nat.or_two_pow_eq_add_of_lt hr, ← Nat.two_pow_add_eq_or_of_lt hb]
    have := Nat.div_add_mod a (2 ^ (e + 1))
    omega
  rw [e1, Nat.testBit_or, Nat.testBit_or, Nat.testBit_two_pow, ← Bool.or_assoc,
    ← Nat.testBit_or, ← ha, Bool.or_eq_true, decide_eq_true_iff]
  exact or_congr_right eq_comm

theorem testBit_fold {p : Array ℕ} {n : ℕ} : ∀ (L : List ℕ) (a : ℕ),
    (L.map fun j => p[j]!).Nodup → (∀ j ∈ L, a.testBit p[j]! = false) → ∀ i,
    ((L.foldl (fun acc j => if n.testBit j then acc + 2 ^ p[j]! else acc) a).testBit i = true ↔
      (a.testBit i = true ∨ ∃ j ∈ L, p[j]! = i ∧ n.testBit j = true))
  | [], a, _, _, i => by simp
  | j :: L, a, hnd, ha, i => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hj, hnd⟩ := hnd
    rw [List.foldl_cons]
    have hne : ∀ k ∈ L, p[k]! ≠ p[j]! := fun k hk e => hj (List.mem_map.2 ⟨k, hk, e⟩)
    have hbit : ∀ k ∈ L, (if n.testBit j then a + 2 ^ p[j]! else a).testBit p[k]! = false := by
      intro k hk
      split
      · rw [← Bool.not_eq_true, testBit_add_two_pow (ha j (by simp))]
        rw [ha k (by simp [hk])]
        simp [hne k hk]
      · exact ha k (by simp [hk])
    rw [testBit_fold L _ hnd hbit i]
    split
    · rename_i hn
      rw [testBit_add_two_pow (ha j (by simp))]
      constructor
      · rintro ((h | h) | ⟨k, hk, e⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, by simp, h.symm, hn⟩
        · exact Or.inr ⟨k, by simp [hk], e⟩
      · rintro (h | ⟨k, hk, e⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 hk with rfl | hk
          · exact Or.inl (Or.inr e.1.symm)
          · exact Or.inr ⟨k, hk, e⟩
    · rename_i hn
      constructor
      · rintro (h | ⟨k, hk, e⟩)
        · exact Or.inl h
        · exact Or.inr ⟨k, by simp [hk], e⟩
      · rintro (h | ⟨k, hk, e⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 hk with rfl | hk
          · simp [hn] at e
          · exact Or.inr ⟨k, hk, e⟩

theorem nodup_images {p : Array ℕ} (hp : PermArr p = true) :
    ((List.range 24).map fun j => p[j]!).Nodup := by
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj e
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  have := (decode p).injective (a₁ := ⟨i, hi'⟩) (a₂ := ⟨j, hj'⟩)
    (Fin.ext (by rw [decode_apply hp, decode_apply hp]; exact e))
  exact congrArg Fin.val this

theorem testBit_permI {p : Array ℕ} (hp : PermArr p = true) (n i : ℕ) :
    (permI p n).testBit i = true ↔ ∃ j < 24, p[j]! = i ∧ n.testBit j = true := by
  rw [permI, testBit_fold _ 0 (nodup_images hp) (fun _ _ => Nat.zero_testBit _) i,
    Nat.zero_testBit]
  simp

theorem permI_lt {p : Array ℕ} (hp : PermArr p = true) (n : ℕ) : permI p n < 2 ^ 24 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [← Bool.not_eq_true, testBit_permI hp]
  rintro ⟨j, hj, e, -⟩
  have := PermArr_lt hp ⟨j, hj⟩
  simp only at this
  omega

theorem bvec_permI {p : Array ℕ} (hp : PermArr p = true) (n : ℕ) :
    bvec 24 (permI p n) = bvec 24 n ∘ arrFun (ainv p) := by
  funext i
  have hpi := PermArr_ainv hp
  rw [Function.comp_apply, bvec, bvec, arrFun_val hpi]
  obtain ⟨h1, h2⟩ := ainv_getElem_spec hp i
  have hp2 : p[(ainv p)[(i : ℕ)]!]! = i := by
    have := congrArg Fin.val h2
    rwa [decode_apply hp] at this
  have key : (permI p n).testBit i = n.testBit (ainv p)[(i : ℕ)]! := by
    apply Bool.eq_iff_iff.2
    rw [testBit_permI hp]
    constructor
    · rintro ⟨j, hj, hji, hn⟩
      have e : j = (ainv p)[(i : ℕ)]! := congrArg Fin.val ((decode p).injective
        (a₁ := ⟨j, hj⟩) (a₂ := ⟨_, h1⟩)
        (Fin.ext (by rw [decode_apply hp, decode_apply hp, hji, hp2])))
      rw [← e]
      exact hn
    · intro hn
      exact ⟨_, h1, hp2, hn⟩
  rw [key]

end CFSG.Monster.B.TwoA.Census

end
