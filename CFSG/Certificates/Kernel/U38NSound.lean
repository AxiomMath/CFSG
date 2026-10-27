module

public import Certificates.Data.Kernel.U38N
public import Certificates.Data.HuppertU38F.Check
public import CFSG.Certificates.Kernel.OuterNSound

public section

namespace CFSG.KC.HeisN

open CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F

namespace FK

variable {K : FK} {d : ℕ → GF8}

@[expose] def colL (K : FK) (d : ℕ → GF8) (c : ColN) : Col :=
  (dec K d c.1, dec K d c.2.1, dec K d c.2.2)

theorem ofCols_colL (a b c : ColN) :
    ofCols (colL K d a) (colL K d b) (colL K d c) = toL K d (ofColsN a b c) := rfl

section
variable (hK : K.Sound d) {w : ℕ} (hw : dec K d w = w0)
include hK

theorem beq_dec {x n : ℕ} (hx : x < K.p * K.p) (hn : n < K.p * K.p) :
    Nat.beq x n = decide (dec K d x = dec K d n) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
  exact ⟨fun h => h ▸ rfl, dec_inj hK hx hn⟩

theorem zero_lt_sq : 0 < K.p * K.p := by have := one_lt_sq hK; omega

theorem mMul_lt (A B : M3 ℕ) :
    (K.mMul A B).a00 < K.p * K.p ∧ (K.mMul A B).a01 < K.p * K.p ∧ (K.mMul A B).a02 < K.p * K.p ∧
      (K.mMul A B).a10 < K.p * K.p ∧ (K.mMul A B).a11 < K.p * K.p ∧
      (K.mMul A B).a12 < K.p * K.p ∧ (K.mMul A B).a20 < K.p * K.p ∧
      (K.mMul A B).a21 < K.p * K.p ∧ (K.mMul A B).a22 < K.p * K.p :=
  ⟨eAdd_lt hK _ _, eAdd_lt hK _ _, eAdd_lt hK _ _, eAdd_lt hK _ _, eAdd_lt hK _ _,
    eAdd_lt hK _ _, eAdd_lt hK _ _, eAdd_lt hK _ _, eAdd_lt hK _ _⟩

theorem isScalarN_sound (A : M3 ℕ) (h : isScalarN A = true) : isScalar (toL K d A) = true := by
  simp only [isScalarN, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine decide_eq_true ?_
  simp [toL, h1, h2, h3, h4, h5, h6, h7, h8, dec_zero hK]

theorem isScalarN_of_mMul (A B : M3 ℕ) (h : isScalar (toL K d (K.mMul A B)) = true) :
    isScalarN (K.mMul A B) = true := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := mMul_lt hK A B
  have z := zero_lt_sq hK
  unfold isScalar at h
  rw [decide_eq_true_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have e0 := (dec_zero hK (d := d)).symm
  simp only [isScalarN, Bool.and_eq_true, Nat.beq_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨dec_inj hK l1 z (h1.trans e0), dec_inj hK l2 z (h2.trans e0)⟩,
    dec_inj hK l3 z (h3.trans e0)⟩, dec_inj hK l5 z (h4.trans e0)⟩, dec_inj hK l6 z (h5.trans e0)⟩,
    dec_inj hK l7 z (h6.trans e0)⟩, dec_inj hK l4 l0 h7⟩, dec_inj hK l8 l0 h8⟩

theorem unitaryOkN_sound (A : M3 ℕ) (h : K.unitaryOkN A = true) : unitaryOk (toL K d A) = true := by
  refine decide_eq_true ?_
  rw [← toL_mPowTr hK, ← toL_mMul hK, mEq_sound h, toL_mOne hK]

theorem sgOkN_sound (A : M3 ℕ) (h : K.sgOkN A = true) : sgOk (toL K d A) = true := by
  simp only [sgOkN, Bool.and_eq_true, Nat.beq_eq] at h
  simp only [sgOk, Bool.and_eq_true, decide_eq_true_iff]
  refine ⟨?_, unitaryOkN_sound hK A h.2⟩
  rw [← toL_mDet hK, h.1, dec_one hK]

theorem commutesN_sound (A B : M3 ℕ) (h : K.commutesN A B = true) :
    commutes (toL K d A) (toL K d B) = true := by
  refine decide_eq_true ?_
  rw [← toL_mMul hK, ← toL_mMul hK, mEq_sound h]

include hw

theorem l4N_map : (K.l4N w).map (dec K d) = l4 := by
  simp only [l4N, l4, List.map_cons, List.map_nil, dec_zero hK, dec_one hK, dec_eMul hK, hw]

theorem f4nzN_map : (K.f4nzN w).map (dec K d) = f4nz := by
  simp only [f4nzN, f4nz, List.map_cons, List.map_nil, dec_one hK, dec_eMul hK, hw]

theorem inL_sound {x : ℕ} (h : inL (K.l4N w) x = true) : dec K d x ∈ l4 := by
  rw [← l4N_map hK hw]
  simp only [inL, List.any_eq_true, Nat.beq_eq] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact List.mem_map_of_mem hy

theorem entriesL4N_sound (A : M3 ℕ) (h : K.entriesL4N w A = true) :
    entriesL4 (toL K d A) = true := by
  simp only [entriesL4N, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact decide_eq_true ⟨inL_sound hK hw h0, inL_sound hK hw h1, inL_sound hK hw h2,
    inL_sound hK hw h3, inL_sound hK hw h4, inL_sound hK hw h5, inL_sound hK hw h6,
    inL_sound hK hw h7, inL_sound hK hw h8⟩

theorem cols4_eq : cols4 = (K.cols4N w).map (colL K d) := by
  simp only [cols4, cols4N, ← l4N_map hK hw, List.flatMap_map, List.map_flatMap, List.map_map]
  rfl

end

section
variable (hK : K.Sound d)
include hK

theorem ip_colL (c c' : ColN) : ip (colL K d c) (colL K d c') = dec K d (K.ipN c c') := by
  simp only [ip, ipN, colL, dec_eAdd hK, dec_eMul hK, dec_ePow hK]

theorem ipN_lt (c c' : ColN) : K.ipN c c' < K.p * K.p := eAdd_lt hK _ _

theorem stage1_colL (c : ColN) : stage1 (colL K d c) = K.stage1N c := by
  rw [stage1, stage1N, beq_dec hK (ipN_lt hK c c) (one_lt_sq hK), ip_colL hK, dec_one hK]

theorem stage2_colL (c c' : ColN) : stage2 (colL K d c) (colL K d c') = K.stage2N c c' := by
  rw [stage2, stage2N, beq_dec hK (ipN_lt hK c' c') (one_lt_sq hK),
    beq_dec hK (ipN_lt hK c c') (zero_lt_sq hK), ip_colL hK, ip_colL hK, dec_one hK, dec_zero hK,
    Bool.decide_and]

theorem stage3_colL (c c' c'' : ColN) :
    stage3 (colL K d c) (colL K d c') (colL K d c'') = K.stage3N c c' c'' := by
  rw [stage3, stage3N, beq_dec hK (ipN_lt hK c'' c'') (one_lt_sq hK),
    beq_dec hK (ipN_lt hK c c'') (zero_lt_sq hK), beq_dec hK (ipN_lt hK c' c'') (zero_lt_sq hK),
    ip_colL hK, ip_colL hK, ip_colL hK, dec_one hK, dec_zero hK, Bool.decide_and,
    Bool.decide_and, Bool.and_assoc]

variable {w : ℕ} (hw : dec K d w = w0)
include hw

theorem forallUnitary_eq (P : M3 Q8 → Bool) :
    forallUnitary P = K.forallUnitaryN w (fun A => P (toL K d A)) := by
  simp only [forallUnitary, forallUnitaryN, cols4_eq hK hw, List.all_map, Function.comp_def,
    stage1_colL hK, stage2_colL hK, stage3_colL hK]
  rfl

theorem guList_eq : guList = (K.guListN w).map (toL K d) := by
  simp only [guList, guListN, cols4_eq hK hw, List.flatMap_map, List.map_flatMap, stage1_colL hK,
    stage2_colL hK, stage3_colL hK, apply_ite (List.map (toL K d)), List.map_nil,
    List.map_filterMap, List.filterMap_map, Function.comp_def, apply_ite (Option.map (toL K d)),
    Option.map_some, Option.map_none]
  rfl

theorem mem_orbitOf (gu : List (M3 ℕ)) (Y A : M3 ℕ) (l : ℕ) (hl : l ∈ K.f4nzN w)
    (hA : K.mSmul l A ∈ K.orbitN gu Y) :
    toL K d A ∈ orbitOf (gu.map (toL K d)) (toL K d Y) := by
  obtain ⟨g, hg, hgA⟩ := List.mem_map.mp hA
  have e := congrArg (toL K d) hgA
  rw [toL_mMul hK, toL_mMul hK, toL_mPowTr hK, toL_mSmul hK] at e
  have hl' : dec K d l ∈ f4nz := by
    rw [← f4nzN_map hK hw]
    exact List.mem_map_of_mem hl
  have hinv : ∃ m ∈ f4nz, m * dec K d l = 1 := by
    simp only [f4nz, w0, List.mem_cons, List.not_mem_nil, or_false] at hl' ⊢
    have h3 := QExt.omega_pow_three (F := GF8)
    rcases hl' with h | h | h <;> rw [h]
    · exact ⟨1, Or.inl rfl, one_mul 1⟩
    · exact ⟨QExt.omega * QExt.omega, Or.inr (Or.inr rfl), by rw [← h3, pow_three, mul_assoc]⟩
    · exact ⟨QExt.omega, Or.inr (Or.inl rfl), by rw [← h3, pow_three]⟩
  obtain ⟨m, hm, hml⟩ := hinv
  simp only [orbitOf, List.mem_flatMap, List.mem_map]
  refine ⟨toL K d g, ⟨g, hg, rfl⟩, m, hm, ?_⟩
  rw [gstar, e]
  ext <;> simp only [M3.smul, ← mul_assoc, hml, one_mul]

end

theorem forallUnitaryN_mono (w : ℕ) {P Q : M3 ℕ → Bool} (hPQ : ∀ A, P A = true → Q A = true)
    (h : K.forallUnitaryN w P = true) : K.forallUnitaryN w Q = true := by
  simp only [forallUnitaryN, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
  intro c₀ h₀
  refine (h c₀ h₀).imp_right fun h₁ c₁ hc₁ => (h₁ c₁ hc₁).imp_right fun h₂ c₂ hc₂ => ?_
  exact (h₂ c₂ hc₂).imp_right (hPQ _)

theorem codeN_spec {w x c : ℕ} (h : K.codeN w x = some c) : c < 4 ∧ (K.l4N w).getD c 0 = x := by
  unfold codeN at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨by decide, (Nat.eq_of_beq_eq_true (by assumption)).symm⟩
  · split at h
    · obtain rfl := Option.some.inj h
      exact ⟨by decide, (Nat.eq_of_beq_eq_true (by assumption)).symm⟩
    · split at h
      · obtain rfl := Option.some.inj h
        exact ⟨by decide, (Nat.eq_of_beq_eq_true (by assumption)).symm⟩
      · split at h
        · obtain rfl := Option.some.inj h
          exact ⟨by decide, (Nat.eq_of_beq_eq_true (by assumption)).symm⟩
        · exact absurd h (by simp)

theorem keyL_cons {w x : ℕ} {xs : List ℕ} {k : ℕ} (h : K.keyL w (x :: xs) = some k) :
    ∃ c k', K.codeN w x = some c ∧ K.keyL w xs = some k' ∧ k = c + 4 * k' := by
  unfold keyL at h
  split at h
  · next c k' hc hk => exact ⟨c, k', hc, hk, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

theorem keyL_inj (w : ℕ) : ∀ (xs ys : List ℕ) (k : ℕ), K.keyL w xs = some k →
    K.keyL w ys = some k → xs.length = ys.length → xs = ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hl => absurd hl (by simp)
  | _ :: _, [], _, _, _, hl => absurd hl (by simp)
  | x :: xs, y :: ys, k, hx, hy, hl => by
    obtain ⟨c, k₁, hc, hk₁, rfl⟩ := keyL_cons hx
    obtain ⟨c', k₂, hc', hk₂, e⟩ := keyL_cons hy
    obtain ⟨c4, hcx⟩ := codeN_spec hc
    obtain ⟨c4', hcy⟩ := codeN_spec hc'
    have e1 : c = c' := by omega
    have e2 : k₁ = k₂ := by omega
    subst e1 e2
    rw [← hcx, hcy, keyL_inj w xs ys k₁ hk₁ hk₂ (by simpa using hl)]

theorem keyF4_inj {w k : ℕ} {A B : M3 ℕ} (hA : K.keyF4 w A = some k) (hB : K.keyF4 w B = some k) :
    A = B := by
  have e := keyL_inj w _ _ k hA hB rfl
  cases A
  cases B
  simp only [entriesOf, List.cons.injEq, and_true] at e
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := e
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem testBit_pack (x s j : ℕ) (hs : s < 2 ^ 64) :
    ((x <<< 64) ||| s).testBit (j + 64) = x.testBit j := by
  have hs' : s.testBit (j + 64) = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))
  rw [Nat.testBit_or, hs', Bool.or_false, Nat.testBit_shiftLeft]
  simp

theorem mem_of_bitsF4 (w : ℕ) (vs : List (M3 ℕ)) (k : ℕ) (h : (K.bitsF4 w vs).testBit (k + 64)) :
    ∃ V ∈ vs, K.keyF4 w V = some k := by
  induction vs with
  | nil => simp [bitsF4] at h
  | cons V vs ih =>
    simp only [bitsF4] at h
    split at h
    · rename_i k' hk'
      rw [testBit_pack _ _ _ (Nat.mod_lt _ (by decide)), Nat.testBit_or, Bool.or_eq_true,
        Nat.testBit_shiftRight, Nat.add_comm 64 k] at h
      rcases h with h | h
      · obtain ⟨W, hW, hk⟩ := ih h
        exact ⟨W, List.mem_cons_of_mem _ hW, hk⟩
      · rw [Nat.testBit_shiftLeft] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at h
        refine ⟨V, List.mem_cons_self, ?_⟩
        rw [hk']
        congr 1
        omega
    · obtain ⟨W, hW, hk⟩ := ih h
      exact ⟨W, List.mem_cons_of_mem _ hW, hk⟩

section
variable (hK : K.Sound d) {w : ℕ} (hw : dec K d w = w0)
include hK hw

theorem classOkN_sound (gu : List (M3 ℕ)) (table : List (M3 ℕ)) (A : M3 ℕ)
    (h : K.classOkN w (K.bitsF4 w (table.flatMap fun Y => K.orbitN gu Y)) A = true) :
    classOk (table.map fun Y => orbitOf (gu.map (toL K d)) (toL K d Y)) (toL K d A) = true := by
  simp only [classOkN, Bool.or_eq_true] at h
  simp only [classOk, Bool.or_eq_true]
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (isScalarN_sound hK A h))
  · refine Or.inl (Or.inr ?_)
    rw [Bool.not_eq_true'] at h ⊢
    rw [← toL_mMul hK, ← toL_mMul hK]
    cases e : isScalar (toL K d (K.mMul (K.mMul A A) A))
    · rfl
    · rw [isScalarN_of_mMul hK _ _ e] at h
      exact absurd h (by decide)
  · refine Or.inr ?_
    rw [List.any_eq_true] at h
    obtain ⟨l, hl, h⟩ := h
    split at h
    · rename_i k hk
      obtain ⟨V, hV, hVk⟩ := mem_of_bitsF4 w _ k h
      obtain rfl := keyF4_inj hVk hk
      obtain ⟨Y, hY, hVY⟩ := List.mem_flatMap.mp hV
      rw [List.any_eq_true]
      exact ⟨_, List.mem_map_of_mem hY, decide_eq_true (mem_orbitOf hK hw gu Y A l hl hVY)⟩
    · exact absurd h (by decide)

theorem u38EntryOkN_sound (letters : List (M3 ℕ)) (Y : M3 ℕ) (gens : List (M3 ℕ))
    (ws : List (List ℕ)) (h : K.u38EntryOkN w letters Y gens ws = true) :
    u38EntryOk (letters.map (toL K d)) ⟨toL K d Y, gens.map (toL K d), ws⟩ = true := by
  simp only [u38EntryOkN, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true] at h
  obtain ⟨hg, hw'⟩ := h
  simp only [u38EntryOk, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true]
  refine ⟨fun G' hG' => ?_, decide_eq_true ?_⟩
  · obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hG'
    obtain ⟨h1, h2⟩ := hg G hG
    refine ⟨sgOkN_sound hK G h1, h2.imp (entriesL4N_sound hK hw G) (commutesN_sound hK G Y)⟩
  · rw [evalsN_toL hK, mListEq_sound hw']

theorem u38N_sound (raw ws₁ ws₂ : List (List ℕ))
    (table : List (List ℕ × List (M3 ℕ) × List (List ℕ))) (h : K.u38N w raw ws₁ ws₂ table = true) :
    u38Check (ws₁.map (evalW (raw.map fun l => toL K d (matN l)))) ws₂
      (table.map fun r => ⟨toL K d (matN r.1), r.2.1.map (toL K d), r.2.2⟩) = true := by
  have hg : raw.map (fun l => toL K d (matN l)) = (raw.map matN).map (toL K d) := by
    rw [List.map_map]
    rfl
  simp only [u38N, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hgu, hc⟩, ht⟩, hu⟩ := h
  rw [hg, evalsN_toL hK]
  unfold u38Check
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨fun g' hg' => ?_, ?_⟩, fun e he => ?_⟩, ?_⟩
  · rw [guList_eq hK hw] at hg'
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
    exact ⟨unitaryOkN_sound hK g (hgu g hg).1, entriesL4N_sound hK hw g (hgu g hg).2⟩
  · unfold coverBool
    refine decide_eq_true ?_
    rw [evalsN_toL hK]
    exact coverN_sound hK 8 _ hc
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact u38EntryOkN_sound hK hw _ _ _ _ (ht r hr)
  · rw [forallUnitary_eq hK hw, guList_eq hK hw, List.map_map]
    refine forallUnitaryN_mono w (fun A hA => ?_) hu
    have e := classOkN_sound hK hw (K.guListN w) (table.map fun r => matN r.1) A
      (by rwa [List.flatMap_map])
    rwa [List.map_map] at e

end

end FK

end CFSG.KC.HeisN
