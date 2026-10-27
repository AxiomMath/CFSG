module

public import CFSG.Certificates.Kernel.B45M12Sound
public import Certificates.Data.Kernel.B45M22.Defs
public import Certificates.Data.SmithB45MatM22Nor

public section

namespace CFSG.KC.B45M22

open CFSG.KC.B45M12 CFSG.Quasithin.B45Mat CFSG.CharacterTheory.SteinbergBY
open CFSG.Quasithin.H.Mathieu (act10 actC10 act10_lt actC10_lt)

theorem untab_maskTab {n : ℕ} {f : ℕ → ℕ} {cols : List ℕ} (h : colsK n f cols = true) :
    untab (M22.maskTab n f) = maskMat n n cols := by
  simp only [colsK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at h
  ext i j
  rw [untab_apply, maskMat_apply, ← h.2 j j.2]
  simp only [M22.maskTab, Fin.getElem_fin, Vector.getElem_ofFn]

theorem lt_of_colsK {n : ℕ} {f : ℕ → ℕ} {cols : List ℕ} (hf : ∀ x, f x < 2 ^ n)
    (h : colsK n f cols = true) : ∀ c ∈ cols, c < 2 ^ n := by
  simp only [colsK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at h
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have e := h.2 j (h.1 ▸ hj)
  rw [List.getD_eq_getElem _ _ hj] at e
  rw [← e]
  exact hf _

theorem length_of_colsK {n : ℕ} {f : ℕ → ℕ} {cols : List ℕ} (h : colsK n f cols = true) :
    cols.length = n := by
  simp only [colsK, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1

theorem untab_tab10a {g : M22.G22} {C : List ℕ}
    (h : colsK 10 (act10 (M22.psiArr (g : Equiv.Perm (Fin 22)))) C = true) :
    untab (M22.tab10a g) = maskMat 10 10 C :=
  untab_maskTab h

theorem untab_tab10b {g : M22.G22} {C : List ℕ}
    (h : colsK 10 (actC10 (M22.psiArr (g : Equiv.Perm (Fin 22)))) C = true) :
    untab (M22.tab10b g) = maskMat 10 10 C :=
  untab_maskTab h

theorem untab_kronTab_maskMat {m n : ℕ} {A : Vector (Vector (ZMod 2) m) m}
    {B : Vector (Vector (ZMod 2) n) n} {C D : List ℕ} (hA : untab A = maskMat m m C)
    (hB : untab B = maskMat n n D) (hD : ∀ c ∈ D, c < 2 ^ n) :
    untab (kronTab A B) = maskMat (m * n) (m * n) (kronM m n C D) := by
  rw [untab_kronTab, hA, hB, maskMat_kronM C D hD]

theorem untab_kronBB {g : M22.G22} {C : List ℕ}
    (h : colsK 10 (actC10 (M22.psiArr (g : Equiv.Perm (Fin 22)))) C = true) :
    untab (M22.kronBB g) = maskMat (10 * 10) (10 * 10) (kronM 10 10 C C) :=
  untab_kronTab_maskMat (untab_tab10b h) (untab_tab10b h) (lt_of_colsK (actC10_lt _) h)

theorem untab_kronAB {g : M22.G22} {C D : List ℕ}
    (hC : colsK 10 (act10 (M22.psiArr (g : Equiv.Perm (Fin 22)))) C = true)
    (hD : colsK 10 (actC10 (M22.psiArr (g : Equiv.Perm (Fin 22)))) D = true) :
    untab (M22.kronAB g) = maskMat (10 * 10) (10 * 10) (kronM 10 10 C D) :=
  untab_kronTab_maskMat (untab_tab10a hC) (untab_tab10b hD) (lt_of_colsK (actC10_lt _) hD)

theorem length_ofF2 (X : List ℕ) : (ofF2 X).length = X.length := List.length_map _

theorem untab_tab340 {g : M22.G22} {C T : List ℕ} (hC : untab (M22.tab10b g) = maskMat 10 10 C)
    (hT : untab (M22.tab34 g) = maskMat 34 34 T) (hCl : C.length = 10) (hTl : T.length = 34) :
    untab (M22.tab340 g) = pairMat (10 * 34) (10 * 34) (k340 C T) := by
  rw [M22.tab340, untab_kronTab, untab_mapTab, untab_mapTab, hC, hT, ← pairMat_ofF2,
    ← pairMat_ofF2, k340]
  exact (CFSG.Quasithin.HM22.PM.toMat_kron (dA := 10) (dB := 34) (ofF2 C) (ofF2 T)
    (by rw [length_ofF2, hCl]) (by rw [length_ofF2, hTl])).symm

theorem length_k340 {C T : List ℕ} (hC : C.length = 10) (hT : T.length = 34) :
    (k340 C T).length = 10 * 34 := by
  rw [k340, CFSG.Quasithin.HM22.PM.length_kron, length_ofF2, length_ofF2, hC, hT]

theorem untab_decF2_cols (m n : ℕ) (rows : List ℕ) :
    untab (M22.decF2 m n rows) = maskMat m n (trM n rows) := by
  rw [maskMat_trM n m rows]
  exact untab_decF2 m n rows

theorem deint_zero : ∀ k, deint k 0 = (0, 0)
  | 0 => rfl
  | _ + 1 => rfl

theorem deint_lt : ∀ k r, (deint k r).1 < 2 ^ 2 ^ k ∧ (deint k r).2 < 2 ^ 2 ^ k
  | 0, r => ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩
  | k + 1, r => by
    have hp : 2 ^ 2 ^ (k + 1) = 2 ^ 2 ^ k * 2 ^ 2 ^ k := by
      rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
    have hb : ∀ a b : ℕ, a < 2 ^ 2 ^ k → b < 2 ^ 2 ^ k → a + 2 ^ 2 ^ k * b < 2 ^ 2 ^ (k + 1) := by
      intro a b ha hb'
      rw [hp]
      have : 2 ^ 2 ^ k * b + 2 ^ 2 ^ k ≤ 2 ^ 2 ^ k * 2 ^ 2 ^ k := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hb'
      omega
    cases hr : Nat.beq r 0
    · simp only [deint, hr, cond_false]
      exact ⟨hb _ _ (deint_lt k _).1 (deint_lt k _).1, hb _ _ (deint_lt k _).2 (deint_lt k _).2⟩
    · simp only [deint, hr, cond_true]
      exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _⟩

theorem testBit_add_two_pow_mul {w a b i : ℕ} (ha : a < 2 ^ w) :
    (a + 2 ^ w * b).testBit i = if i < w then a.testBit i else b.testBit (i - w) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ ha]

theorem testBit_deint : ∀ (k r j : ℕ), j < 2 ^ k →
    (deint k r).1.testBit j = r.testBit (2 * j) ∧ (deint k r).2.testBit j = r.testBit (2 * j + 1)
  | 0, r, j, hj => by
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    refine ⟨?_, ?_⟩
    · change (r % 2).testBit 0 = r.testBit 0
      rw [Nat.testBit_zero, Nat.testBit_zero, Nat.mod_mod]
    · change (r / 2 % 2).testBit 0 = r.testBit 1
      rw [Nat.testBit_zero, testBit_eq_decide r 1, Nat.pow_one, Nat.mod_mod]
  | k + 1, r, j, hj => by
    have h4 : 4 ^ 2 ^ k = 2 ^ (2 * 2 ^ k) := by rw [Nat.pow_mul]
    cases hr : Nat.beq r 0
    · have hlo := deint_lt k (r % 4 ^ 2 ^ k)
      have hd : deint (k + 1) r =
          ((deint k (r % 4 ^ 2 ^ k)).1 + 2 ^ 2 ^ k * (deint k (r / 4 ^ 2 ^ k)).1,
            (deint k (r % 4 ^ 2 ^ k)).2 + 2 ^ 2 ^ k * (deint k (r / 4 ^ 2 ^ k)).2) := by
        simp only [deint, hr, cond_false]
      rw [hd]
      rw [testBit_add_two_pow_mul hlo.1, testBit_add_two_pow_mul hlo.2]
      by_cases hjk : j < 2 ^ k
      · rw [if_pos hjk, if_pos hjk]
        obtain ⟨e1, e2⟩ := testBit_deint k (r % 4 ^ 2 ^ k) j hjk
        rw [e1, e2, h4, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
        have a1 : 2 * j < 2 * 2 ^ k := by omega
        have a2 : 2 * j + 1 < 2 * 2 ^ k := by omega
        simp [a1, a2]
      · rw [if_neg hjk, if_neg hjk]
        have hj' : j - 2 ^ k < 2 ^ k := by
          rw [Nat.pow_succ] at hj
          omega
        obtain ⟨e1, e2⟩ := testBit_deint k (r / 4 ^ 2 ^ k) (j - 2 ^ k) hj'
        rw [e1, e2, h4, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
        constructor <;> congr 1 <;> omega
    · have : r = 0 := by simpa using hr
      subst this
      rw [deint_zero]
      simp

theorem getD_map_deint (k : ℕ) (rows : List ℕ) (i : ℕ) :
    (rows.map (deint k)).getD i (0, 0) = deint k (rows.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases rows[i]? with
  | none => exact (deint_zero k).symm
  | some r => rfl

theorem untab_decF4_deint {m n k : ℕ} (hn : n ≤ 2 ^ k) (rows : List ℕ) :
    untab (M22.decF4 m n rows) = (pairMat n m (rows.map (deint k))).transpose := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.transpose_apply]
  simp only [untab, M22.decF4, pairMat, Matrix.of_apply, Fin.getElem_fin, Vector.getElem_map,
    Vector.getElem_ofFn]
  rw [getD_map_deint]
  obtain ⟨h1, h2⟩ := testBit_deint k (rows.getD i 0) j (lt_of_lt_of_le j.2 hn)
  exact FieldFour.ext h1.symm h2.symm

theorem untab_decF4_colsD {m n k : ℕ} (hn : n ≤ 2 ^ k) (rows : List ℕ) :
    untab (M22.decF4 m n rows) = pairMat m n (colsD n k rows) := by
  rw [colsD, pairMat_trF4, untab_decF4_deint hn]

theorem untab_decF4_of_eqF4 {m n k : ℕ} (hn : n ≤ 2 ^ k) {rows : List ℕ} {X : List (ℕ × ℕ)}
    (h : eqF4 n (trF4 m X) (rows.map (deint k)) = true) :
    untab (M22.decF4 m n rows) = pairMat m n X := by
  rw [untab_decF4_deint hn, ← pairMat_eq_of_eqF4 h, pairMat_trF4, Matrix.transpose_transpose]

theorem subOK_of_subOKM {m d : ℕ} {Ka Kb : Vector (Vector (ZMod 2) m) m}
    {B : Vector (Vector (ZMod 2) d) m} {P : Vector (Vector (ZMod 2) m) d} {Ka' Kb' B' P' : List ℕ}
    (hKa : untab Ka = maskMat m m Ka') (hKb : untab Kb = maskMat m m Kb')
    (hB : untab B = maskMat m d B') (hP : untab P = maskMat d m P')
    (h : subOKM m d Ka' Kb' B' P' = true) : subOK Ka Kb B P = true := by
  obtain ⟨hPB, hK⟩ := subOKM_spec h
  have step : ∀ {K : Vector (Vector (ZMod 2) m) m} {K' : List ℕ}, untab K = maskMat m m K' →
      K' ∈ [Ka', Kb'] → untab (mulT K B) = untab (mulT B (mulT P (mulT K B))) := by
    intro K K' hK' hmem
    rw [untab_mulT, untab_mulT, untab_mulT, untab_mulT, hK', hB, hP,
      ← Matrix.mul_assoc (maskMat d m P')]
    exact hK K' hmem
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨?_, step hKa (by simp), step hKb (by simp)⟩
  rw [untab_mulT, hP, hB, hPB]

theorem quotOK_of_quotOKM {m d : ℕ} {Ka Kb : Vector (Vector (ZMod 2) m) m}
    {B : Vector (Vector (ZMod 2) d) m} {P : Vector (Vector (ZMod 2) m) d} {Ka' Kb' B' P' : List ℕ}
    (hKa : untab Ka = maskMat m m Ka') (hKb : untab Kb = maskMat m m Kb')
    (hB : untab B = maskMat m d B') (hP : untab P = maskMat d m P')
    (h : quotOKM m d Ka' Kb' B' P' = true) : quotOK Ka Kb B P = true := by
  obtain ⟨hPB, hK⟩ := quotOKM_spec h
  have step : ∀ {K : Vector (Vector (ZMod 2) m) m} {K' : List ℕ}, untab K = maskMat m m K' →
      K' ∈ [Ka', Kb'] → untab (mulT P K) = untab (mulT (mulT (mulT P K) B) P) := by
    intro K K' hK' hmem
    rw [untab_mulT, untab_mulT, untab_mulT, untab_mulT, hK', hB, hP]
    exact hK K' hmem
  simp only [quotOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨?_, step hKa (by simp), step hKb (by simp)⟩
  rw [untab_mulT, hP, hB, hPB]

theorem untab_mulT_mulT {m d : ℕ} {K : Vector (Vector (ZMod 2) m) m}
    {B : Vector (Vector (ZMod 2) d) m} {P : Vector (Vector (ZMod 2) m) d} {K' B' P' : List ℕ}
    (hK : untab K = maskMat m m K') (hB : untab B = maskMat m d B')
    (hP : untab P = maskMat d m P') (hKl : K'.length ≤ m) (hPl : P'.length ≤ m) :
    untab (mulT (mulT P K) B) = maskMat d d (mulM P' (mulM K' B')) := by
  rw [maskMat_mulM P' _ hPl, maskMat_mulM K' B' hKl, untab_mulT, untab_mulT, Matrix.mul_assoc,
    hK, hB, hP]

theorem untab_mulT_of_subK {m d : ℕ} {K : Vector (Vector (ZMod 2) m) m}
    {B : Vector (Vector (ZMod 2) d) m} {P : Vector (Vector (ZMod 2) m) d} {K' B' P' T : List ℕ}
    {KT : List (List ℕ × List ℕ)} (hK : untab K = maskMat m m K')
    (hB : untab B = maskMat m d B') (hP : untab P = maskMat d m P')
    (h : subK m d B' P' KT = true) (hKT : (K', T) ∈ KT) :
    untab (mulT (mulT P K) B) = maskMat d d T := by
  obtain ⟨-, hPl, -, hKT'⟩ := subK_spec h
  obtain ⟨hKl, rfl, -⟩ := hKT' _ _ hKT
  exact untab_mulT_mulT hK hB hP hKl hPl

theorem untab_mulT_of_quotK {m d : ℕ} {K : Vector (Vector (ZMod 2) m) m}
    {B : Vector (Vector (ZMod 2) d) m} {P : Vector (Vector (ZMod 2) m) d} {K' B' P' T : List ℕ}
    {KT : List (List ℕ × List ℕ)} (hK : untab K = maskMat m m K')
    (hB : untab B = maskMat m d B') (hP : untab P = maskMat d m P')
    (h : quotK m d B' P' KT = true) (hKT : (K', T) ∈ KT) :
    untab (mulT (mulT P K) B) = maskMat d d T := by
  obtain ⟨-, hPl, -, hKT'⟩ := quotK_spec h
  obtain ⟨hKl, rfl, -⟩ := hKT' _ _ hKT
  exact untab_mulT_mulT hK hB hP hKl hPl

theorem subF4K_spec {m d : ℕ} {B P : List (ℕ × ℕ)} {KT : List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (h : subF4K m d B P KT = true) :
    B.length ≤ d ∧ P.length ≤ m ∧ pairMat d d (mulF4 P B) = 1 ∧ ∀ K T, (K, T) ∈ KT →
      K.length ≤ m ∧ pairMat d d T = pairMat d d (mulF4 P (mulF4 K B)) ∧
        pairMat m d (mulF4 K B) = pairMat m d (mulF4 B T) := by
  simp only [subF4K, subStepF4K, Bool.and_eq_true, Nat.ble_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hB, hP⟩, hPB⟩, hKT⟩ := h
  refine ⟨hB, hP, by rw [pairMat_eq_of_eqF4 hPB, pairMat_idF4], fun K T hKT' => ?_⟩
  obtain ⟨hK, hT, hKB⟩ := hKT _ hKT'
  exact ⟨hK, (pairMat_eq_of_eqF4 hT).symm, pairMat_eq_of_eqF4 hKB⟩

theorem subOK_of_subF4K {m d : ℕ} {Ka Kb : Vector (Vector FieldFour m) m}
    {B : Vector (Vector FieldFour d) m} {P : Vector (Vector FieldFour m) d}
    {Ka' Kb' Ta Tb B' P' : List (ℕ × ℕ)} {KT₁ KT₂ : List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (hKa : untab Ka = pairMat m m Ka') (hKb : untab Kb = pairMat m m Kb')
    (hB : untab B = pairMat m d B') (hP : untab P = pairMat d m P')
    (h₁ : subF4K m d B' P' KT₁ = true) (h₂ : subF4K m d B' P' KT₂ = true)
    (ha : (Ka', Ta) ∈ KT₁) (hb : (Kb', Tb) ∈ KT₂) : subOK Ka Kb B P = true := by
  obtain ⟨hBl, hPl, hPB, h₁⟩ := subF4K_spec h₁
  obtain ⟨-, -, -, h₂⟩ := subF4K_spec h₂
  have step : ∀ {K : Vector (Vector FieldFour m) m} {K' T : List (ℕ × ℕ)},
      untab K = pairMat m m K' → K'.length ≤ m →
        pairMat d d T = pairMat d d (mulF4 P' (mulF4 K' B')) →
          pairMat m d (mulF4 K' B') = pairMat m d (mulF4 B' T) →
            untab (mulT K B) = untab (mulT B (mulT P (mulT K B))) := by
    intro K K' T hK hl hT hKB
    rw [untab_mulT, untab_mulT, untab_mulT, untab_mulT, hK, hB, hP, ← pairMat_mulF4 _ _ hl,
      ← pairMat_mulF4 _ _ hPl, ← hT, hKB, pairMat_mulF4 _ _ hBl]
  obtain ⟨hKa', hTa, hKBa⟩ := h₁ _ _ ha
  obtain ⟨hKb', hTb, hKBb⟩ := h₂ _ _ hb
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨?_, step hKa hKa' hTa hKBa, step hKb hKb' hTb hKBb⟩
  rw [untab_mulT, hP, hB, ← pairMat_mulF4 _ _ hPl, hPB]

theorem untab_mulT_mulT_F4 {m d : ℕ} {K : Vector (Vector FieldFour m) m}
    {B : Vector (Vector FieldFour d) m} {P : Vector (Vector FieldFour m) d}
    {K' B' P' : List (ℕ × ℕ)} (hK : untab K = pairMat m m K') (hB : untab B = pairMat m d B')
    (hP : untab P = pairMat d m P') (hKl : K'.length ≤ m) (hPl : P'.length ≤ m) :
    untab (mulT (mulT P K) B) = pairMat d d (mulF4 P' (mulF4 K' B')) := by
  rw [pairMat_mulF4 P' _ hPl, pairMat_mulF4 K' B' hKl, untab_mulT, untab_mulT, Matrix.mul_assoc,
    hK, hB, hP]

theorem untab_mulT_of_subF4K {m d : ℕ} {K : Vector (Vector FieldFour m) m}
    {B : Vector (Vector FieldFour d) m} {P : Vector (Vector FieldFour m) d}
    {K' B' P' T : List (ℕ × ℕ)} {KT : List (List (ℕ × ℕ) × List (ℕ × ℕ))}
    (hK : untab K = pairMat m m K') (hB : untab B = pairMat m d B')
    (hP : untab P = pairMat d m P') (h : subF4K m d B' P' KT = true) (hKT : (K', T) ∈ KT) :
    untab (mulT (mulT P K) B) = pairMat d d T := by
  obtain ⟨-, hPl, -, hKT'⟩ := subF4K_spec h
  obtain ⟨hKl, hT, -⟩ := hKT' _ _ hKT
  rw [hT]
  exact untab_mulT_mulT_F4 hK hB hP hKl hPl

theorem frob_ofPrime (x : ZMod 2) : FieldFour.frob (FieldFour.ofPrime x) = FieldFour.ofPrime x := by
  rw [← RingHom.comp_apply, RingHom.ext_zmod (FieldFour.frob.comp FieldFour.ofPrime)
    FieldFour.ofPrime]

theorem map_frob_tab340 (g : M22.G22) :
    (untab (M22.tab340 g)).map FieldFour.frob = untab (M22.tab340 g) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, untab_apply, M22.tab340, kronTab, mapTab, Fin.getElem_fin,
    Vector.getElem_ofFn, Vector.getElem_map, map_mul, frob_ofPrime]

theorem subOK_frob {m d : ℕ} {Ka Kb : Vector (Vector FieldFour m) m}
    {B B' : Vector (Vector FieldFour d) m} {P P' : Vector (Vector FieldFour m) d}
    (hKa : (untab Ka).map FieldFour.frob = untab Ka)
    (hKb : (untab Kb).map FieldFour.frob = untab Kb)
    (hB : untab B' = (untab B).map FieldFour.frob) (hP : untab P' = (untab P).map FieldFour.frob)
    (h : subOK Ka Kb B P = true) : subOK Ka Kb B' P' = true := by
  obtain ⟨hPB, hK⟩ := subOK_spec h
  have step : ∀ K ∈ [Ka, Kb], (untab K).map FieldFour.frob = untab K →
      untab (mulT K B') = untab (mulT B' (mulT P' (mulT K B'))) := by
    intro K hK' hf
    rw [untab_mulT, untab_mulT, untab_mulT, untab_mulT, hB, hP, ← hf, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc (untab P), ← hK K hK']
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true]
  refine ⟨?_, step Ka (by simp) hKa, step Kb (by simp) hKb⟩
  rw [untab_mulT, hB, hP, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero _) (map_one _)]

theorem untab_mulT_frob {m d : ℕ} {K : Vector (Vector FieldFour m) m}
    {B B' : Vector (Vector FieldFour d) m} {P P' : Vector (Vector FieldFour m) d}
    (hK : (untab K).map FieldFour.frob = untab K)
    (hB : untab B' = (untab B).map FieldFour.frob) (hP : untab P' = (untab P).map FieldFour.frob) :
    untab (mulT (mulT P' K) B') = (untab (mulT (mulT P K) B)).map FieldFour.frob := by
  rw [untab_mulT, untab_mulT, untab_mulT, untab_mulT, hB, hP, ← hK, ← Matrix.map_mul,
    ← Matrix.map_mul, hK]

theorem trace_map_frob {n : ℕ} (A : Matrix (Fin n) (Fin n) FieldFour) :
    Matrix.trace (A.map FieldFour.frob) = FieldFour.frob (Matrix.trace A) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem ofPrime_trace_maskMat {n c : ℕ} {X : List ℕ} (h : traceK n (ofF2 X) c = true) :
    FieldFour.ofPrime (Matrix.trace (maskMat n n X)) = M12.ofCode4 c := by
  rw [← traceK_sound h, pairMat_ofF2]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem trace_maskMat_eq {n c : ℕ} {X : List ℕ} {t : ZMod 2} (h : traceK n (ofF2 X) c = true)
    (ht : FieldFour.ofPrime t = M12.ofCode4 c) : Matrix.trace (maskMat n n X) = t :=
  FieldFour.ofPrime.injective ((ofPrime_trace_maskMat h).trans ht.symm)

theorem spinF2_eq : @M22.spinF2 = @M12.spinF2 := rfl

theorem spinF4_eq : @M22.spinF4 = @M12.spinF4 := rfl

theorem norF2_sound' {n : ℕ} [NeZero n] {tw : List (List ℕ)} {tc : List ℕ}
    {Q Qi R Si Ti : List ℕ} {w : ℕ} {spin dual : List (ℕ × ℕ)} {Ga Gb : List ℕ}
    {Ma Mb : Vector (Vector (ZMod 2) n) n} (ha : untab Ma = maskMat n n Ga)
    (hb : untab Mb = maskMat n n Gb) (h : norF2 n tw tc Q Qi R Si Ti w spin dual Ga Gb = true) :
    (M22.spinF2 n tw tc Q Qi R Si Ti w spin dual).check Ma Mb = true := by
  rw [spinF2_eq]
  exact norF2_sound ha hb h

theorem norF4_sound' {n : ℕ} [NeZero n] {tw : List (List ℕ)} {tc : List ℕ}
    {Q Qi R Si Ti : List ℕ} {w : ℕ} {spin dual : List (ℕ × ℕ)} {Ga Gb : List (ℕ × ℕ)}
    {Ma Mb : Vector (Vector FieldFour n) n} (ha : untab Ma = pairMat n n Ga)
    (hb : untab Mb = pairMat n n Gb) (h : norF4 n tw tc Q Qi R Si Ti w spin dual Ga Gb = true) :
    (M22.spinF4 n tw tc Q Qi R Si Ti w spin dual).check Ma Mb = true := by
  rw [spinF4_eq]
  exact norF4_sound ha hb h

end CFSG.KC.B45M22

end
