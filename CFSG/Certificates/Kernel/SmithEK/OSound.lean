module

public import Certificates.Data.Kernel.SmithEKO
public import CFSG.Certificates.Kernel.Spor.PK.MiscPerm

public section

set_option exponentiation.threshold 1000

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73 CFSG.KS.PK

theorem bitK_eq (M x : Nat) : bitK M x = M.testBit x := by
  have e : bitK M x = Nat.beq ((M >>> x) % 2) 1 := by
    unfold bitK
    rw [← Nat.and_one_is_mod]
    rfl
  rw [e, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (M >>> x) with h | h <;> rw [h] <;> rfl

theorem maskK_testBit (q : Nat) : ∀ l : List Nat, (maskK l).testBit q = true ↔ q ∈ l
  | [] => by simp [maskK]
  | x :: l => by
    have e : maskK (x :: l) = 2 ^ x ||| maskK l := by
      change Nat.lor (Nat.shiftLeft 1 x) (maskK l) = _
      rw [← Nat.one_shiftLeft]
      rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, maskK_testBit q l,
      decide_eq_true_iff, List.mem_cons, eq_comm]

theorem lenK_eq : ∀ l : List Nat, lenK l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenK_eq l)

theorem ltK_iff (n : Nat) : ∀ l : List Nat, ltK n l = true ↔ ∀ x ∈ l, x < n
  | [] => by simp [ltK]
  | x :: l => by
    have e : ltK n (x :: l) = (Nat.blt x n && ltK n l) := rfl
    rw [e, Bool.and_eq_true, ltK_iff n l, Nat.blt_eq, List.forall_mem_cons]

theorem memK_iff (x : Nat) : ∀ l : List Nat, memK x l = true ↔ x ∈ l
  | [] => by simp [memK]
  | y :: l => by
    have e : memK x (y :: l) = (Nat.beq y x || memK x l) := rfl
    rw [e, Bool.or_eq_true, memK_iff x l, Nat.beq_eq, List.mem_cons, eq_comm]

theorem fd_cons_zero {w m X : Nat} (hm : m < 2 ^ w) : fd w (m + X * 2 ^ w) 0 = m := by
  unfold fd
  rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]

theorem fd_cons {w m X : Nat} (hm : m < 2 ^ w) (j : Nat) :
    fd w (m + X * 2 ^ w) (j + 1) = fd w X j := by
  unfold fd
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * j)) (2 ^ w), ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt hm, Nat.zero_add]

theorem fd_zero (w j : Nat) : fd w 0 j = 0 := by
  unfold fd
  rw [Nat.zero_div, Nat.zero_mod]

theorem at'_packK : ∀ (P : List Nat), (∀ m ∈ P, m < 2 ^ 693) → ∀ j, at' 693 (packK P) j = P.getD j 0
  | [], _, j => by
    rw [at'_eq]
    exact fd_zero _ _
  | m :: P, h, j => by
    have hm := h m List.mem_cons_self
    have e : packK (m :: P) = m + packK P * 2 ^ 693 := lor_shiftLeft_eq_add hm
    rw [at'_eq, e]
    cases j with
    | zero => rw [fd_cons_zero hm, List.getD_cons_zero]
    | succ j =>
      rw [fd_cons hm, ← at'_eq, at'_packK P (fun x hx => h x (List.mem_cons_of_mem _ hx)) j,
        List.getD_cons_succ]

theorem at'_pack10 : ∀ (l : List Nat), (∀ x ∈ l, x < 1024) → ∀ p, at' 10 (pack10 l) p = l.getD p 0
  | [], _, p => by
    rw [at'_eq]
    exact fd_zero _ _
  | x :: l, h, p => by
    have hx : x < 2 ^ 10 := h x List.mem_cons_self
    have e : pack10 (x :: l) = x + pack10 l * 2 ^ 10 := by
      change Nat.add x (Nat.mul 1024 (pack10 l)) = _
      rw [Nat.mul_comm]
      rfl
    rw [at'_eq, e]
    cases p with
    | zero => rw [fd_cons_zero hx, List.getD_cons_zero]
    | succ p =>
      rw [fd_cons hx, ← at'_eq, at'_pack10 l (fun y hy => h y (List.mem_cons_of_mem _ hy)) p,
        List.getD_cons_succ]

theorem plK_sound : ∀ {P : List Nat} {PL : List (List Nat)}, plK P PL = true →
    ∀ j < P.length, (PL.getD j []).length = 21 ∧ (∀ x ∈ PL.getD j [], x < 693) ∧
      maskK (PL.getD j []) = P.getD j 0
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | m :: P, PL, h, j, hj => by
    have e : plK (m :: P) PL = (Nat.beq (lenK (PL.headD [])) 21 && ltK 693 (PL.headD []) &&
        Nat.beq (maskK (PL.headD [])) m && plK P PL.tail) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.beq_eq, lenK_eq, ltK_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    cases PL with
    | nil => simp at h1
    | cons l PL =>
      cases j with
      | zero => exact ⟨h1, h2, by rw [List.getD_cons_zero, List.getD_cons_zero]; exact h3⟩
      | succ j =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact plK_sound h4 j (by simpa using hj)

theorem imgK_iff (M T : Nat) : ∀ l : List Nat,
    imgK M T l = true ↔ ∀ x ∈ l, M.testBit (at' 10 T x) = true
  | [] => by simp [imgK]
  | x :: l => by
    have e : imgK M T (x :: l) = (bitK M (at' 10 T x) && imgK M T l) := rfl
    rw [e, Bool.and_eq_true, bitK_eq, imgK_iff M T l, List.forall_mem_cons]

theorem genImgK_sound {PK T : Nat} : ∀ {PL : List (List Nat)} {J : List Nat},
    genImgK PK T PL J = true → ∀ j < PL.length, J.getD j 0 < 891 ∧
      ∀ x ∈ PL.getD j [], (at' 693 PK (J.getD j 0)).testBit (at' 10 T x) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | l :: PL, J, h, j, hj => by
    have e : genImgK PK T (l :: PL) J = (Nat.blt (J.headD 0) 891 &&
        imgK (at' 693 PK (J.headD 0)) T l && genImgK PK T PL J.tail) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.blt_eq, imgK_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hJ : ∀ i, J.tail.getD i 0 = J.getD (i + 1) 0 := fun i => by
      cases J <;> simp
    cases j with
    | zero =>
      have e0 : J.getD 0 0 = J.headD 0 := by cases J <;> simp
      rw [e0, List.getD_cons_zero]
      exact ⟨h1, h2⟩
    | succ j =>
      rw [← hJ, List.getD_cons_succ]
      exact genImgK_sound h3 j (by simpa using hj)

theorem jpK_sound : ∀ {J : List (List Nat)} {JP : List Nat}, jpK J JP = true →
    ∀ g < J.length, pack10 (J.getD g []) = JP.getD g 0
  | [], _, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | l :: J, JP, h, g, hg => by
    have e : jpK (l :: J) JP = (Nat.beq (pack10 l) (JP.headD 0) && jpK J JP.tail) := rfl
    rw [e, Bool.and_eq_true, Nat.beq_eq] at h
    cases g with
    | zero =>
      rw [List.getD_cons_zero, h.1]
      cases JP <;> simp
    | succ g =>
      rw [List.getD_cons_succ, jpK_sound h.2 g (by simpa using hg)]
      cases JP <;> simp

theorem edgeJ_eq {J : List (List Nat)} {JP : List Nat} (h : jpK J JP = true) {g : Nat}
    (hg : g < J.length) (hJ : ∀ x ∈ J.getD g [], x < 1024) (p v : Nat) :
    edgeJ JP g p v = true ↔ (J.getD g []).getD p 0 = v := by
  unfold edgeJ
  rw [Nat.beq_eq, ← jpK_sound h g hg, at'_pack10 _ hJ]

theorem wImgK_iff (M T₁ T₂ : Nat) : ∀ l : List Nat,
    wImgK M T₁ T₂ l = true ↔ ∀ x ∈ l, M.testBit (at' 10 T₁ (at' 10 T₂ x)) = true
  | [] => by simp [wImgK]
  | x :: l => by
    have e : wImgK M T₁ T₂ (x :: l) = (bitK M (at' 10 T₁ (at' 10 T₂ x)) && wImgK M T₁ T₂ l) := rfl
    rw [e, Bool.and_eq_true, bitK_eq, wImgK_iff M T₁ T₂ l, List.forall_mem_cons]

theorem stabK_sound {TP : Nat → Nat} {M : Nat} {l : List Nat} : ∀ {W : List Nat},
    stabK TP M l W = true → ∀ w ∈ W, ∀ x ∈ l,
      M.testBit (at' 10 (TP (w % 1024)) (at' 10 (TP (w / 1024)) x)) = true
  | [], _ => by simp
  | w :: W, h => by
    have e : stabK TP M l (w :: W) = (wImgK M (TP (w % 1024)) (TP (w / 1024)) l &&
        stabK TP M l W) := rfl
    rw [e, Bool.and_eq_true, wImgK_iff] at h
    rw [List.forall_mem_cons]
    exact ⟨h.1, stabK_sound h.2⟩

theorem recAll_iff (p : Nat → Bool) : ∀ n : Nat,
    Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k) n = true ↔ ∀ k < n, p k = true
  | 0 => ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | n + 1 => by
    have e : Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k) (n + 1) =
        (Nat.rec (motive := fun _ => Bool) true (fun k acc => acc && p k) n && p n) := rfl
    rw [e, Bool.and_eq_true, recAll_iff p n]
    constructor
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h k hk
      · exact hn
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem sgK_sound {TP : Nat → Nat} {l : List Nat} : ∀ {W : List Nat} {SG : List (List Nat)},
    sgK TP l W SG = true → ∀ g < W.length, (SG.getD g []).length = 21 ∧
      (∀ x ∈ SG.getD g [], x < 21) ∧ ∀ k < 21, l.getD ((SG.getD g []).getD k 0) 0 =
        at' 10 (TP (W.getD g 0 % 1024)) (at' 10 (TP (W.getD g 0 / 1024)) (l.getD k 0))
  | [], _, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | w :: W, SG, h, g, hg => by
    have e : sgK TP l (w :: W) SG = (Nat.beq (lenK (SG.headD [])) 21 && ltK 21 (SG.headD []) &&
        Nat.rec (motive := fun _ => Bool) true (fun k acc => acc &&
          Nat.beq (l.getD ((SG.headD []).getD k 0) 0)
            (at' 10 (TP (w % 1024)) (at' 10 (TP (w / 1024)) (l.getD k 0)))) 21 &&
        sgK TP l W SG.tail) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.beq_eq, lenK_eq, ltK_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [recAll_iff] at h3
    cases SG with
    | nil => simp at h1
    | cons s SG =>
      cases g with
      | zero =>
        simp only [List.getD_cons_zero, List.headD_cons] at h1 h2 h3 ⊢
        exact ⟨h1, h2, fun k hk => by simpa using h3 k hk⟩
      | succ g =>
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact sgK_sound h4 g (by simpa using hg)

theorem s2K_inner (C : List Nat) (u v : Nat) : ∀ (n acc : Nat),
    (Nat.rec (motive := fun _ => Nat) acc (fun w acc2 => bif Nat.beq u w then acc2 else
      Nat.lor acc2 (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD w 0)))) n).testBit v = true ↔
      acc.testBit v = true ∨ ∃ w < n, u ≠ w ∧ Nat.xor (C.getD u 0) (C.getD w 0) = v
  | 0, acc => ⟨Or.inl, fun h => h.elim id fun ⟨w, hw, _⟩ => absurd hw (Nat.not_lt_zero w)⟩
  | n + 1, acc => by
    have e : (Nat.rec (motive := fun _ => Nat) acc (fun w acc2 => bif Nat.beq u w then acc2 else
        Nat.lor acc2 (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD w 0)))) (n + 1)) =
        (bif Nat.beq u n then (Nat.rec (motive := fun _ => Nat) acc (fun w acc2 =>
          bif Nat.beq u w then acc2 else
            Nat.lor acc2 (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD w 0)))) n) else
          Nat.lor (Nat.rec (motive := fun _ => Nat) acc (fun w acc2 => bif Nat.beq u w then acc2
            else Nat.lor acc2 (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD w 0)))) n)
            (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD n 0)))) := rfl
    rw [e]
    by_cases hun : u = n
    · subst hun
      rw [Nat.beq_refl, cond_true, s2K_inner C u v u acc]
      refine or_congr_right ⟨fun ⟨w, hw, h⟩ => ⟨w, by omega, h⟩, fun ⟨w, hw, h⟩ => ?_⟩
      exact ⟨w, by have := h.1; omega, h⟩
    · have hb : Nat.beq u n = false := Bool.eq_false_iff.2 fun h => hun (Nat.eq_of_beq_eq_true h)
      rw [hb, cond_false]
      change (_ ||| 1 <<< _).testBit v = true ↔ _
      rw [Nat.testBit_or, Bool.or_eq_true, s2K_inner C u v n acc, Nat.one_shiftLeft,
        Nat.testBit_two_pow, decide_eq_true_iff]
      constructor
      · rintro ((h | ⟨w, hw, h⟩) | h)
        · exact Or.inl h
        · exact Or.inr ⟨w, by omega, h⟩
        · exact Or.inr ⟨n, by omega, hun, h⟩
      · rintro (h | ⟨w, hw, h⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
          · exact Or.inl (Or.inr ⟨w, hw, h⟩)
          · exact Or.inr h.2

theorem s2K_testBit (C : List Nat) (v : Nat) :
    (s2K C).testBit v = true ↔ ∃ u < 21, ∃ w < 21, u ≠ w ∧ Nat.xor (C.getD u 0) (C.getD w 0) = v := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun u acc =>
      Nat.rec (motive := fun _ => Nat) acc (fun w acc2 => bif Nat.beq u w then acc2 else
        Nat.lor acc2 (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD w 0)))) 21) n).testBit v = true ↔
      ∃ u < n, ∃ w < 21, u ≠ w ∧ Nat.xor (C.getD u 0) (C.getD w 0) = v := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun h => ?_, fun ⟨u, hu, _⟩ => absurd hu (Nat.not_lt_zero u)⟩
      change (0 : Nat).testBit v = true at h
      rw [Nat.zero_testBit] at h
      exact absurd h Bool.false_ne_true
    | succ n ih =>
      rw [s2K_inner C n v 21 _, ih]
      constructor
      · rintro (⟨u, hu, h⟩ | h)
        · exact ⟨u, by omega, h⟩
        · exact ⟨n, by omega, h⟩
      · rintro ⟨u, hu, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · exact Or.inl ⟨u, hu, h⟩
        · exact Or.inr h
  exact key 21

theorem countK_eq (C : List Nat) (S2 c : Nat) :
    countK C S2 c = (List.range 512).countP fun v => clsK C S2 v == c := by
  have key : ∀ n, Nat.rec (motive := fun _ => Nat) 0
      (fun v acc => bif Nat.beq (clsK C S2 v) c then Nat.succ acc else acc) n =
      (List.range n).countP fun v => clsK C S2 v == c := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.countP_append, ← ih]
      change (bif Nat.beq (clsK C S2 n) c then Nat.succ _ else _) = _
      cases h : Nat.beq (clsK C S2 n) c
      · have e := Nat.ne_of_beq_eq_false h
        simp [e]
      · have e := Nat.eq_of_beq_eq_true h
        simp [e]
  exact key 512

theorem clsChkK_sound {C : List Nat} {S2 : Nat} (h : clsChkK C S2 = true) :
    clsK C S2 1 = 1 ∧ clsK C S2 3 = 2 ∧ clsK C S2 19 = 3 ∧
      (List.range 512).countP (fun v => clsK C S2 v == 1) = 21 ∧
      (List.range 512).countP (fun v => clsK C S2 v == 2) = 210 ∧
      (List.range 512).countP (fun v => clsK C S2 v == 3) = 280 := by
  unfold clsChkK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, countK_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem plpK_sound {PLP : Nat} : ∀ {PL : List (List Nat)} {i : Nat}, plpK PLP PL i = true →
    ∀ j < PL.length, at' 210 PLP (i + j) = pack10 (PL.getD j [])
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | l :: PL, i, h, j, hj => by
    have e : plpK PLP (l :: PL) i = (Nat.beq (at' 210 PLP i) (pack10 l) && plpK PLP PL (i + 1)) :=
      rfl
    rw [e, Bool.and_eq_true, Nat.beq_eq] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      rw [List.getD_cons_succ, ← plpK_sound h.2 j (by simpa using hj)]
      congr 1
      omega

theorem wImgP_iff (M T₁ T₂ R : Nat) :
    wImgP M T₁ T₂ R = true ↔ ∀ m < 21, M.testBit (at' 10 T₁ (at' 10 T₂ (at' 10 R m))) = true := by
  unfold wImgP
  simp only [recAll_iff, bitK_eq]

theorem dsK_sound {PK M₀ : Nat} {DS : List Nat} (h : dsK PK M₀ DS = true) :
    (∀ j < 891, meetK PK M₀ j = 21 ∨ meetK PK M₀ j = 5 ∨ meetK PK M₀ j = 1 ∨
        meetK PK M₀ j = 0) ∧ DS.length = 4 ∧ (∀ d ∈ DS, d < 891) ∧
      ∀ cd ∈ List.zip [21, 5, 1, 0] DS, meetK PK M₀ cd.2 = cd.1 ∧
        ∀ j < cd.2, meetK PK M₀ j ≠ cd.1 := by
  unfold dsK at h
  simp only [Bool.and_eq_true, Nat.beq_eq, lenK_eq, ltK_iff, recAll_iff, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun j hj => ?_, h2, h3, fun cd hcd => ?_⟩
  · have := h1 j hj
    unfold dClsK at this
    simpa only [Bool.or_eq_true, Nat.beq_eq, or_assoc] using this
  · have := h4 cd hcd
    simp only [Bool.and_eq_true, Nat.beq_eq, recAll_iff, Bool.not_eq_true'] at this
    exact ⟨this.1, fun j hj => Nat.ne_of_beq_eq_false (this.2 j hj)⟩

end CFSG.SmithE.K
