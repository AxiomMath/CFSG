module

public import CFSG.Certificates.Kernel.L52Insp443.Bridge

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.Misc.GLM.Ech
  CFSG.Literature.GL52 Matrix

theorem orB_true {a b : Bool} : CFSG.KC.Ord.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem notB_true {a : Bool} : CFSG.KC.Ord.notB a = true ↔ a = false := by
  cases a <;> decide

theorem allK_iff {α : Type} (p : α → Bool) : ∀ L : List α, allK p L = true ↔ ∀ x ∈ L, p x = true
  | [] => by simp [allK]
  | x :: L => by
    change CFSG.KC.Ord.andB (p x) (allK p L) = true ↔ _
    rw [andB_true, allK_iff p L, List.forall_mem_cons]

theorem anyK_iff {α : Type} (p : α → Bool) : ∀ L : List α, anyK p L = true ↔ ∃ x ∈ L, p x = true
  | [] => by simp [anyK]
  | x :: L => by
    change CFSG.KC.Ord.orB (p x) (anyK p L) = true ↔ _
    rw [orB_true, anyK_iff p L]
    simp only [List.mem_cons, exists_eq_or_imp]

theorem memK_iff (x : ℕ) (L : List ℕ) : memK x L = true ↔ x ∈ L := by
  unfold memK
  rw [anyK_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    rwa [← Nat.eq_of_beq_eq_true h] at hy
  · intro h
    exact ⟨x, h, Nat.beq_refl x⟩

theorem bvo5_inj {v w : ℕ} (hv : v < 32) (hw : w < 32) (e : bvo 5 0 v = bvo 5 0 w) : v = w := by
  apply Nat.eq_of_testBit_eq
  intro q
  rcases Nat.lt_or_ge q 5 with hq | hq
  · have e1 := congrFun e ⟨q, hq⟩
    change (if v.testBit (q + 0) then (1 : ZMod 2) else 0) = if w.testBit (q + 0) then 1 else 0
      at e1
    rw [Nat.add_zero] at e1
    cases h1 : v.testBit q <;> cases h2 : w.testBit q <;> rw [h1, h2] at e1 <;> simp_all
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show v < 2 ^ 5 from hv)
      (Nat.pow_le_pow_right (by norm_num) hq)),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show w < 2 ^ 5 from hw)
      (Nat.pow_le_pow_right (by norm_num) hq))]

theorem mvK_mul (g h : G) {v : ℕ} (hv : v < 32) :
    mvK (mcode ((g * h : G) : Mat)) v = mvK (mcode (g : Mat)) (mvK (mcode (h : Mat)) v) := by
  obtain ⟨h1, e1⟩ := mvK_mcode ((g * h : G) : Mat) hv
  obtain ⟨h2, e2⟩ := mvK_mcode (h : Mat) hv
  obtain ⟨h3, e3⟩ := mvK_mcode (g : Mat) h2
  refine bvo5_inj h1 h3 ?_
  rw [e1, e3, e2, Units.val_mul, mulVec_mulVec]

theorem mvK_one {v : ℕ} (hv : v < 32) : mvK (mcode ((1 : G) : Mat)) v = v := by
  obtain ⟨h1, e1⟩ := mvK_mcode ((1 : G) : Mat) hv
  refine bvo5_inj h1 hv ?_
  rw [e1, Units.val_one, one_mulVec]

theorem bitK_eq_testBit (x i : ℕ) : bitK x i = x.testBit i := bitK_testBit x i

theorem lor_testBit (x y v : ℕ) : (Nat.lor x y).testBit v = (x.testBit v || y.testBit v) :=
  Nat.testBit_or x y v

theorem shl_one_testBit (u v : ℕ) : (Nat.shiftLeft 1 v).testBit u = decide (u = v) := by
  change (1 <<< v).testBit u = _
  rw [Nat.testBit_shiftLeft]
  by_cases h : u = v
  · subst h
    simp
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [show ¬ v ≤ u by omega, h]
    · have : 1 < 2 ^ (u - v) := Nat.one_lt_two_pow (by omega)
      simp [show v ≤ u by omega, h, Nat.testBit_lt_two_pow this]

theorem actRec_testBit (c F u : ℕ) : ∀ k : ℕ,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun v acc => Bool.rec (motive := fun _ => ℕ) acc
      (Nat.lor acc (Nat.shiftLeft 1 (mvK c v))) (bitK F v)) k : ℕ).testBit u = true ↔
      ∃ v < k, F.testBit v = true ∧ mvK c v = u
  | 0 => by simp
  | k + 1 => by
    change (Bool.rec (motive := fun _ => ℕ) _ (Nat.lor _ (Nat.shiftLeft 1 (mvK c k)))
      (bitK F k)).testBit u = true ↔ _
    rw [bitK_eq_testBit]
    cases hF : F.testBit k
    · change (Nat.rec (motive := fun _ => ℕ) 0 _ k : ℕ).testBit u = true ↔ _
      rw [actRec_testBit c F u k]
      constructor
      · rintro ⟨v, hv, h⟩
        exact ⟨v, by omega, h⟩
      · rintro ⟨v, hv, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · exact ⟨v, hv, h1, h2⟩
        · rw [hF] at h1
          exact absurd h1 Bool.false_ne_true
    · change (Nat.lor (Nat.rec (motive := fun _ => ℕ) 0 _ k : ℕ) _).testBit u = true ↔ _
      rw [lor_testBit, Bool.or_eq_true, actRec_testBit c F u k, shl_one_testBit,
        decide_eq_true_iff]
      constructor
      · rintro (⟨v, hv, h⟩ | h)
        · exact ⟨v, by omega, h⟩
        · exact ⟨k, by omega, hF, h.symm⟩
      · rintro ⟨v, hv, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · exact Or.inl ⟨v, hv, h1, h2⟩
        · exact Or.inr h2.symm

theorem actK_testBit (c F u : ℕ) :
    (actK c F).testBit u = true ↔ ∃ v < 32, F.testBit v = true ∧ mvK c v = u :=
  actRec_testBit c F u 32

theorem mvK_lt (g : G) {v : ℕ} (hv : v < 32) : mvK (mcode (g : Mat)) v < 32 :=
  (mvK_mcode (g : Mat) hv).1

theorem actK_lt (g : G) (F : ℕ) : actK (mcode (g : Mat)) F < 2 ^ 32 := by
  refine Nat.lt_pow_two_of_testBit _ fun u hu => ?_
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨v, hv, -, e⟩ := (actK_testBit _ F u).mp h
  have := mvK_lt g hv
  omega

theorem actK_mul (g h : G) {F : ℕ} (hF : F < 2 ^ 32) :
    actK (mcode ((g * h : G) : Mat)) F = actK (mcode (g : Mat)) (actK (mcode (h : Mat)) F) := by
  apply Nat.eq_of_testBit_eq
  intro u
  rw [Bool.eq_iff_iff, actK_testBit, actK_testBit]
  constructor
  · rintro ⟨v, hv, hFv, e⟩
    refine ⟨mvK (mcode (h : Mat)) v, mvK_lt h hv, (actK_testBit _ F _).mpr ⟨v, hv, hFv, rfl⟩, ?_⟩
    rw [← e, mvK_mul g h hv]
  · rintro ⟨w, -, hw, e⟩
    obtain ⟨v, hv, hFv, rfl⟩ := (actK_testBit _ F w).mp hw
    exact ⟨v, hv, hFv, by rw [mvK_mul g h hv, e]⟩

theorem actK_one {F : ℕ} (hF : F < 2 ^ 32) : actK (mcode ((1 : G) : Mat)) F = F := by
  apply Nat.eq_of_testBit_eq
  intro u
  rw [Bool.eq_iff_iff, actK_testBit]
  constructor
  · rintro ⟨v, hv, hFv, e⟩
    rw [mvK_one hv] at e
    rwa [← e]
  · intro h
    have hu : u < 32 := by
      by_contra hu
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hF
        (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h
      exact Bool.false_ne_true h
    exact ⟨u, hu, h, mvK_one hu⟩

theorem fixK_testBit (bs : List ℕ) (v : ℕ) :
    (fixK bs).testBit v = true ↔ v < 32 ∧ v ≠ 0 ∧ ∀ b ∈ bs, mvK b v = v := by
  have key : ∀ k : ℕ, (Nat.rec (motive := fun _ => ℕ) 0 (fun v acc =>
      Bool.rec (motive := fun _ => ℕ) acc (Nat.lor acc (Nat.shiftLeft 1 v))
        (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq v 0)) (allK (fun b => Nat.beq (mvK b v) v) bs))) k : ℕ).testBit v =
        true ↔ v < k ∧ v ≠ 0 ∧ ∀ b ∈ bs, mvK b v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      change (Bool.rec (motive := fun _ => ℕ) _ (Nat.lor _ (Nat.shiftLeft 1 k))
        (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq k 0)) (allK (fun b => Nat.beq (mvK b k) k) bs))).testBit v = true ↔ _
      have hc : CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq k 0)) (allK (fun b => Nat.beq (mvK b k) k) bs) = true ↔
          k ≠ 0 ∧ ∀ b ∈ bs, mvK b k = k := by
        rw [andB_true, notB_true, allK_iff]
        refine and_congr ?_ (forall₂_congr fun b _ => ⟨Nat.eq_of_beq_eq_true, fun h => by
          rw [h]
          exact Nat.beq_refl _⟩)
        rw [Bool.eq_false_iff]
        exact ⟨fun h e => h (e ▸ Nat.beq_refl 0), fun h e => h (Nat.eq_of_beq_eq_true e)⟩
      cases hb : CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq k 0)) (allK (fun b => Nat.beq (mvK b k) k) bs)
      · change (Nat.rec (motive := fun _ => ℕ) 0 _ k : ℕ).testBit v = true ↔ _
        rw [ih]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨by omega, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
          · exact ⟨h1, h2, h3⟩
          · rw [hc.mpr ⟨h2, h3⟩] at hb
            exact absurd hb (by decide)
      · change (Nat.lor (Nat.rec (motive := fun _ => ℕ) 0 _ k : ℕ) _).testBit v = true ↔ _
        rw [lor_testBit, Bool.or_eq_true, ih, shl_one_testBit, decide_eq_true_iff]
        obtain ⟨hk0, hkb⟩ := hc.mp hb
        constructor
        · rintro (⟨h1, h2, h3⟩ | rfl)
          · exact ⟨by omega, h2, h3⟩
          · exact ⟨by omega, hk0, hkb⟩
        · rintro ⟨h1, h2, h3⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
          · exact Or.inl ⟨h1, h2, h3⟩
          · exact Or.inr rfl
  exact key 32

end CFSG.KC.L52I

end
