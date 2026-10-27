module

public import CFSG.Certificates.Kernel.G28.R2Sound
import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.G28R

open CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.Quasithin CFSG.KC.Misc.Clos CFSG.KC.LQT

abbrev genMon (gens : List ℕ) : Submonoid (Matrix (Fin 6) (Fin 6) GF8) :=
  Submonoid.closure {x | ∃ g ∈ gens, dec2 g = x}

theorem beqT {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem beqF {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (beqT.1 hb) h

theorem getD_mem {gens : List ℕ} {j : ℕ} (hj : j < gens.length) : gens.getD j 0 ∈ gens := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

variable {gens : List ℕ} {N : ℕ} {E RG RP RC W IL TL CC : ℕ → ℕ}

theorem mem_of_tree (hG : ∀ j < gens.length, RG j = gens.getD j 0)
    (ht : ∀ k < N, treeAt m2K idK RG gens.length E RP k = true) :
    ∀ k < N, dec2 (E k) ∈ genMon gens := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h0 : Nat.beq (E 0) idK = true := ht 0 hk
      rw [beqT.1 h0, dec2_idK]
      exact one_mem _
    | succ k =>
      have h : P.letB (RP (k + 1)) (fun r => P.letB (Nat.land r 16777215) fun p =>
          P.letB (Nat.shiftRight r 24) fun l => CFSG.KC.Ord.andB (Nat.blt p (k + 1))
            (CFSG.KC.Ord.andB (Nat.blt l gens.length) (Nat.beq (E (k + 1)) (m2K (E p) (RG l))))) =
          true := ht (k + 1) hk
      rw [CFSG.KC.Misc.Clos.letB_eq, CFSG.KC.Misc.Clos.letB_eq, CFSG.KC.Misc.Clos.letB_eq] at h
      obtain ⟨hp, h⟩ := CFSG.KC.Misc.Clos.andB_eq_true h
      obtain ⟨hl, h⟩ := CFSG.KC.Misc.Clos.andB_eq_true h
      have hp' := Nat.blt_eq.mp hp
      have hl' := Nat.blt_eq.mp hl
      rw [beqT.1 h, dec2_m2K, hG _ hl']
      exact mul_mem (ih _ hp' (by omega)) (Submonoid.subset_closure ⟨_, getD_mem hl', rfl⟩)

theorem exists_of_closed (hG : ∀ j < gens.length, RG j = gens.getD j 0) (hN : 0 < N)
    (h0 : E 0 = idK) (hc : ∀ k < N, closedAt m2K RG gens.length N E RC k = true) :
    ∀ x ∈ genMon gens, ∃ k < N, dec2 (E k) = x := by
  intro x hx
  induction hx using Submonoid.closure_induction_right with
  | one => exact ⟨0, hN, by rw [h0, dec2_idK]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨k, hk, rfl⟩ := ih
    obtain ⟨g, hg, rfl⟩ := hy
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have h := (CFSG.KC.Misc.Clos.allN_iff _ _).1 (hc k hk) j hj
    rw [CFSG.KC.Misc.Clos.letB_eq] at h
    obtain ⟨h1, h2⟩ := CFSG.KC.Misc.Clos.andB_eq_true h
    refine ⟨_, Nat.blt_eq.mp h1, ?_⟩
    rw [beqT.1 h2, dec2_m2K, hG j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some]

theorem powOK_spec {s w s2 s3 s7 s21 : ℕ} (h : powOK E IL TL N s w s2 s3 s7 s21 = true) :
    s < 2 ^ 36 ∧ (s21 = idK → s3 = idK ∨ s7 = idK) ∧
      (s2 = idK → s ≠ idK → invOK E IL N s w = true) ∧
      (s3 = idK → s ≠ idK → o3OK TL s w = true) := by
  unfold powOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨Nat.blt_eq.mp h1, fun e => ?_, fun e ne => ?_, fun e ne => ?_⟩
  · rw [e, Nat.beq_refl] at h2
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h2
    exact h2.imp beqT.1 beqT.1
  · rw [e, Nat.beq_refl, beqF ne] at h3
    simpa using h3
  · rw [e, Nat.beq_refl, beqF ne] at h4
    simpa using h4

theorem invOK_spec {s w : ℕ} (h : invOK E IL N s w = true) :
    ∃ ii < 315, IL ii = s ∧ ∃ a < N, ∃ b < N, ∃ r < 2,
      m2K (E a) (E b) = idK ∧ m2K (E a) s = m2K (IL r) (E a) := by
  unfold invOK at h
  simp only [letB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6, h7⟩ := h
  exact ⟨_, Nat.blt_eq.mp h1, beqT.1 h2, _, Nat.blt_eq.mp h3, _, Nat.blt_eq.mp h4, _,
    Nat.blt_eq.mp h5, beqT.1 h6, beqT.1 h7⟩

theorem o3OK_spec {s w : ℕ} (h : o3OK TL s w = true) : ∃ ti < 728, TL ti = s := by
  unfold o3OK at h
  simp only [letB_eq, Bool.and_eq_true] at h
  exact ⟨_, Nat.blt_eq.mp h.1, beqT.1 h.2⟩

theorem code_eq {a b : ℕ} (ha : a < 2 ^ 36) (hb : b < 2 ^ 36) (h : dec2 a = dec2 b) : a = b :=
  dec2_injective ha hb h

structure ElemFacts (R : Submonoid (Matrix (Fin 6) (Fin 6) GF8)) (N : ℕ) (E IL TL : ℕ → ℕ) :
    Prop where
  code : ∀ x ∈ R, ∃ s, s < 2 ^ 36 ∧ dec2 s = x
  f3 : ∀ x ∈ R, x ^ 21 = 1 → x ^ 3 = 1 ∨ x ^ 7 = 1
  inv : ∀ x ∈ R, x ^ 2 = 1 → x ≠ 1 → ∃ ii < 315, dec2 (IL ii) = x ∧ ∃ g ∈ R, ∃ h ∈ R, ∃ r < 2,
    g * h = 1 ∧ g * x = dec2 (IL r) * g
  o3 : ∀ x ∈ R, x ^ 3 = 1 → x ≠ 1 → ∃ ti < 728, dec2 (TL ti) = x

theorem dec2_pow2 (s : ℕ) : dec2 (m2K s s) = dec2 s ^ 2 := by
  rw [dec2_m2K, pow_two]

theorem dec2_pow3 (s : ℕ) : dec2 (m2K (m2K s s) s) = dec2 s ^ 3 := by
  rw [dec2_m2K, dec2_pow2, ← pow_succ]

theorem dec2_pow7 (s : ℕ) :
    dec2 (m2K (m2K (m2K (m2K s s) s) (m2K (m2K s s) s)) s) = dec2 s ^ 7 := by
  rw [dec2_m2K, dec2_m2K, dec2_pow3, ← pow_add, ← pow_succ]

theorem dec2_pow21 (s : ℕ) :
    let s7 := m2K (m2K (m2K (m2K s s) s) (m2K (m2K s s) s)) s
    dec2 (m2K (m2K s7 s7) s7) = dec2 s ^ 21 := by
  intro s7
  rw [dec2_m2K, dec2_m2K, dec2_pow7, ← pow_add, ← pow_add]

theorem eq_one_iff {s : ℕ} (hs : s < 2 ^ 36) : dec2 s = 1 ↔ s = idK := by
  rw [← dec2_idK]
  exact ⟨code_eq hs idK_lt, fun h => h ▸ rfl⟩

theorem elemFacts_of (hG : ∀ j < gens.length, RG j = gens.getD j 0) (hN : 0 < N)
    (ht : ∀ k < N, treeAt m2K idK RG gens.length E RP k = true)
    (hc : ∀ k < N, closedAt m2K RG gens.length N E RC k = true)
    (he : ∀ k < N, elemAt E W IL TL N k = true) : ElemFacts (genMon gens) N E IL TL := by
  have h0 : E 0 = idK := beqT.1 (ht 0 hN)
  have hmem := mem_of_tree hG ht
  have hex := exists_of_closed hG hN h0 hc
  have hk : ∀ k < N, _ := fun k hk => by
    have h := he k hk
    rw [elemAt, letB_eq, letB_eq, letB_eq, letB_eq, letB_eq] at h
    exact powOK_spec h
  refine ⟨fun x hx => ?_, fun x hx h21 => ?_, fun x hx h2 h1 => ?_, fun x hx h3 h1 => ?_⟩
  · obtain ⟨k, hkN, rfl⟩ := hex x hx
    exact ⟨_, (hk k hkN).1, rfl⟩
  · obtain ⟨k, hkN, rfl⟩ := hex x hx
    obtain ⟨-, hf, -, -⟩ := hk k hkN
    have e21 : m2K (m2K (m2K (m2K (m2K (m2K (E k) (E k)) (E k)) (m2K (m2K (E k) (E k)) (E k)))
        (E k)) (m2K (m2K (m2K (m2K (E k) (E k)) (E k)) (m2K (m2K (E k) (E k)) (E k))) (E k)))
        (m2K (m2K (m2K (m2K (E k) (E k)) (E k)) (m2K (m2K (E k) (E k)) (E k))) (E k)) = idK :=
      (eq_one_iff (m2K_lt _ _)).1 (by rw [dec2_pow21]; exact h21)
    rcases hf e21 with h | h
    · exact Or.inl (by rw [← dec2_pow3, (eq_one_iff (m2K_lt _ _)).2 h])
    · exact Or.inr (by rw [← dec2_pow7, (eq_one_iff (m2K_lt _ _)).2 h])
  · obtain ⟨k, hkN, rfl⟩ := hex x hx
    obtain ⟨hlt, -, hi, -⟩ := hk k hkN
    have e2 : m2K (E k) (E k) = idK := (eq_one_iff (m2K_lt _ _)).1 (by rw [dec2_pow2]; exact h2)
    have ne : E k ≠ idK := fun h => h1 ((eq_one_iff hlt).2 h)
    obtain ⟨ii, hii, hIL, a, ha, b, hb, r, hr, hab, hconj⟩ := invOK_spec (hi e2 ne)
    refine ⟨ii, hii, by rw [hIL], _, hmem a ha, _, hmem b hb, r, hr, ?_, ?_⟩
    · rw [← dec2_m2K, hab, dec2_idK]
    · rw [← dec2_m2K, ← dec2_m2K, hconj]
  · obtain ⟨k, hkN, rfl⟩ := hex x hx
    obtain ⟨hlt, -, -, ho⟩ := hk k hkN
    have e3 : m2K (m2K (E k) (E k)) (E k) = idK :=
      (eq_one_iff (m2K_lt _ _)).1 (by rw [dec2_pow3]; exact h3)
    have ne : E k ≠ idK := fun h => h1 ((eq_one_iff hlt).2 h)
    obtain ⟨ti, hti, hTL⟩ := o3OK_spec (ho e3 ne)
    exact ⟨ti, hti, by rw [hTL]⟩

theorem commK_of {a b : ℕ} (h : dec2 a * dec2 b = dec2 b * dec2 a) : commK a b = true := by
  unfold commK
  rw [code_eq (m2K_lt a b) (m2K_lt b a) (by rw [dec2_m2K, dec2_m2K, h])]
  exact Nat.beq_refl _

theorem rep_facts {R : Submonoid (Matrix (Fin 6) (Fin 6) GF8)} {r : ℕ}
    (EF : ElemFacts R N E IL TL) (hr : repAt IL TL CC r = true) :
    (∀ e ∈ R, ∀ u ∈ R, e ^ 3 = 1 → e ≠ 1 → u ^ 3 = 1 → u ≠ 1 → u ≠ e → u ≠ e * e →
      dec2 (IL r) * e = e * dec2 (IL r) → dec2 (IL r) * u = u * dec2 (IL r) → u * e = e * u →
        False) ∧
    (∀ t' ∈ R, ∀ e ∈ R, e ^ 3 = 1 → e ≠ 1 → t' ^ 2 = 1 → t' ≠ 1 → dec2 (IL r) ≠ t' →
      dec2 (IL r) * e = e * dec2 (IL r) → t' * e = e * t' →
        dec2 (IL r) * t' = t' * dec2 (IL r) → False) := by
  unfold repAt at hr
  rw [letB_eq] at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  have hCC : ∀ e ∈ R, e ^ 3 = 1 → e ≠ 1 → dec2 (IL r) * e = e * dec2 (IL r) →
      ∃ m < 8, dec2 (CC (Nat.add (Nat.mul 8 r) m)) = e := by
    intro e he e3 e1 hte
    obtain ⟨ti, hti, hTL⟩ := EF.o3 e he e3 e1
    have h := (allN_iff _ _).1 h1 ti hti
    rw [letB_eq] at h
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · rw [commK_of (by rw [hTL]; exact hte)] at h
      cases h
    · obtain ⟨m, hm, hb⟩ := (anyN_iff _ _).1 h
      exact ⟨m, hm, by rw [← hTL, ← beqT.1 hb]⟩
  refine ⟨fun e he u hu e3 e1 u3 u1 hue hue2 hte htu hue' => ?_,
    fun t' ht' e he e3 e1 t2 t1 htt' hte ht'e htt'c => ?_⟩
  · obtain ⟨me, hme, hCe⟩ := hCC e he e3 e1 hte
    obtain ⟨mu, hmu, hCu⟩ := hCC u hu u3 u1 htu
    have h := (allN_iff _ _).1 h2 me hme
    rw [letB_eq] at h
    have h' := (allN_iff _ _).1 h mu hmu
    rw [letB_eq] at h'
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h'
    rcases h' with (h' | h') | h'
    · exact hue (by rw [← hCu, ← hCe, beqT.1 h'])
    · exact hue2 (by rw [← hCu, ← hCe, beqT.1 h', dec2_m2K])
    · rw [commK_of (by rw [hCu, hCe]; exact hue')] at h'
      cases h'
  · obtain ⟨me, hme, hCe⟩ := hCC e he e3 e1 hte
    obtain ⟨ii, hii, hIL, -⟩ := EF.inv t' ht' t2 t1
    have h := (allN_iff _ _).1 h3 ii hii
    rw [letB_eq] at h
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · exact htt' (by rw [← hIL, beqT.1 h])
    · rw [commK_of (by rw [hIL]; exact htt'c)] at h
      cases h
    · have h' := (allN_iff _ _).1 h me hme
      simp only [Bool.not_eq_true'] at h'
      rw [commK_of (by rw [hIL, hCe]; exact ht'e)] at h'
      cases h'

theorem conj_props {M : Type*} [Monoid M] {g h : M} (hgh : g * h = 1) (hhg : h * g = 1) :
    (∀ x y, g * (x * y) * h = (g * x * h) * (g * y * h)) ∧
      (∀ x (n : ℕ), (g * x * h) ^ n = g * x ^ n * h) ∧
      (∀ x y, g * x * h = g * y * h → x = y) ∧ g * 1 * h = 1 := by
  have hmul : ∀ x y, g * (x * y) * h = (g * x * h) * (g * y * h) := by
    intro x y
    have e : g * x * h * (g * y * h) = g * x * (h * g) * y * h := by simp only [mul_assoc]
    rw [e, hhg, mul_one]
    simp only [mul_assoc]
  have hone : g * 1 * h = 1 := by rw [mul_one, hgh]
  refine ⟨hmul, fun x n => ?_, fun x y hxy => ?_, hone⟩
  · induction n with
    | zero => rw [pow_zero, pow_zero, hone]
    | succ n ih => rw [pow_succ, ih, ← hmul, pow_succ]
  · have ex : x = h * (g * x * h) * g := by
      have e : h * (g * x * h) * g = (h * g) * x * (h * g) := by simp only [mul_assoc]
      rw [e, hhg, one_mul, mul_one]
    rw [ex, hxy]
    have e : h * (g * y * h) * g = (h * g) * y * (h * g) := by simp only [mul_assoc]
    rw [e, hhg, one_mul, mul_one]

theorem facts_of (hG : ∀ j < gens.length, RG j = gens.getD j 0) (hN : 0 < N)
    (ht : ∀ k < N, treeAt m2K idK RG gens.length E RP k = true)
    (hc : ∀ k < N, closedAt m2K RG gens.length N E RC k = true)
    (he : ∀ k < N, elemAt E W IL TL N k = true) (hr : ∀ r < 2, repAt IL TL CC r = true) :
    (∀ e ∈ genMon gens, ∀ y ∈ genMon gens, e ^ 3 = 1 → e ≠ 1 → y ^ 7 = 1 → y ≠ 1 →
      e * y ≠ y * e) ∧
    (∀ e ∈ genMon gens, ∀ t ∈ genMon gens, ∀ t' ∈ genMon gens, e ^ 3 = 1 → e ≠ 1 →
      t ^ 2 = 1 → t ≠ 1 → t' ^ 2 = 1 → t' ≠ 1 → t ≠ t' → t * e = e * t → t' * e = e * t' →
        t * t' = t' * t → False) ∧
    (∀ e ∈ genMon gens, ∀ u ∈ genMon gens, ∀ t ∈ genMon gens, e ^ 3 = 1 → e ≠ 1 →
      u ^ 3 = 1 → u ≠ 1 → u ≠ e → u ≠ e * e → t ^ 2 = 1 → t ≠ 1 → t * e = e * t →
        t * u = u * t → u * e = e * u → False) := by
  have EF := elemFacts_of hG hN ht hc he
  refine ⟨fun e he y hy e3 e1 y7 y1 hey => ?_, fun e he t ht t' ht' e3 e1 t2 t1 t'2 t'1 htt'
    hte ht'e htt'c => ?_, fun e he u hu t ht e3 e1 u3 u1 hue hue2 t2 t1 hte htu hue' => ?_⟩
  · have hcom : Commute e y := hey
    have h21 : (e * y) ^ 21 = 1 := by
      rw [hcom.mul_pow, show (21 : ℕ) = 3 * 7 from rfl, pow_mul, e3, one_pow, one_mul,
        show (3 * 7 : ℕ) = 7 * 3 from rfl, pow_mul, y7, one_pow]
    have ey7 : y ^ 7 = (y ^ 3) ^ 2 * y := by rw [← pow_mul, ← pow_succ]
    have ee7 : e ^ 7 = (e ^ 3) ^ 2 * e := by rw [← pow_mul, ← pow_succ]
    rcases EF.f3 _ (mul_mem he hy) h21 with h | h
    · rw [hcom.mul_pow, e3, one_mul] at h
      rw [ey7, h, one_pow, one_mul] at y7
      exact y1 y7
    · rw [hcom.mul_pow, y7, mul_one] at h
      rw [ee7, e3, one_pow, one_mul] at h
      exact e1 h
  · obtain ⟨-, -, -, g, hg, h, hh, r, hr2, hgh, hgt⟩ := EF.inv t ht t2 t1
    have hhg : h * g = 1 := mul_eq_one_comm.1 hgh
    obtain ⟨hmul, hpow, hinj, hone⟩ := conj_props hgh hhg
    have hmem : ∀ x ∈ genMon gens, g * x * h ∈ genMon gens := fun x hx =>
      mul_mem (mul_mem hg hx) hh
    have hT : g * t * h = dec2 (IL r) := by rw [hgt, mul_assoc, hgh, mul_one]
    have hne : ∀ {x}, x ≠ 1 → g * x * h ≠ 1 := fun hx h1 => hx (hinj _ _ (h1.trans hone.symm))
    refine (rep_facts EF (hr r hr2)).2 _ (hmem t' ht') _ (hmem e he)
      (by rw [hpow, e3, hone]) (hne e1) (by rw [hpow, t'2, hone]) (hne t'1)
      (fun h => htt' (hinj _ _ (hT.trans h))) ?_ ?_ ?_
    · rw [← hT, ← hmul, ← hmul, hte]
    · rw [← hmul, ← hmul, ht'e]
    · rw [← hT, ← hmul, ← hmul, htt'c]
  · obtain ⟨-, -, -, g, hg, h, hh, r, hr2, hgh, hgt⟩ := EF.inv t ht t2 t1
    have hhg : h * g = 1 := mul_eq_one_comm.1 hgh
    obtain ⟨hmul, hpow, hinj, hone⟩ := conj_props hgh hhg
    have hmem : ∀ x ∈ genMon gens, g * x * h ∈ genMon gens := fun x hx =>
      mul_mem (mul_mem hg hx) hh
    have hT : g * t * h = dec2 (IL r) := by rw [hgt, mul_assoc, hgh, mul_one]
    have hne : ∀ {x}, x ≠ 1 → g * x * h ≠ 1 := fun hx h1 => hx (hinj _ _ (h1.trans hone.symm))
    refine (rep_facts EF (hr r hr2)).1 _ (hmem e he) _ (hmem u hu)
      (by rw [hpow, e3, hone]) (hne e1) (by rw [hpow, u3, hone]) (hne u1)
      (fun h => hue (hinj _ _ h)) (fun h => hue2 (hinj _ _ (h.trans (hmul e e).symm))) ?_ ?_ ?_
    · rw [← hT, ← hmul, ← hmul, hte]
    · rw [← hT, ← hmul, ← hmul, htu]
    · rw [← hmul, ← hmul, hue']

end CFSG.KC.G28R

end
