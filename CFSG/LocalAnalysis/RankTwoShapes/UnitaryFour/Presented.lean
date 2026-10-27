module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation

public section

namespace CFSG.RankTwoShapes

namespace UnitaryFourPresented

abbrev genX : UnitaryFourPresented := PresentedGroup.of 0

abbrev genY : UnitaryFourPresented := PresentedGroup.of 1

abbrev genG : UnitaryFourPresented := PresentedGroup.of 2

abbrev genH : UnitaryFourPresented := PresentedGroup.of 3

theorem genX_pow_four : genX ^ 4 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels) (x := FreeGroup.of 0 ^ 4)
    (by simp [unitaryFourRels])
  simp only [map_pow] at h
  exact h

theorem genY_pow_four : genY ^ 4 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels) (x := FreeGroup.of 1 ^ 4)
    (by simp [unitaryFourRels])
  simp only [map_pow] at h
  exact h

theorem commute_genX_genY : Commute genX genY := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := (FreeGroup.of 0)⁻¹ * (FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 1)
    (by simp [unitaryFourRels])
  simp only [map_mul, map_inv] at h
  change genX⁻¹ * genY⁻¹ * genX * genY = 1 at h
  calc genX * genY = genY * genX * (genX⁻¹ * genY⁻¹ * genX * genY) := by group
    _ = genY * genX := by rw [h, mul_one]

theorem commute_genG_genH : Commute genG genH := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := (FreeGroup.of 2)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 2 * FreeGroup.of 3)
    (by simp [unitaryFourRels])
  simp only [map_mul, map_inv] at h
  change genG⁻¹ * genH⁻¹ * genG * genH = 1 at h
  calc genG * genH = genH * genG * (genG⁻¹ * genH⁻¹ * genG * genH) := by group
    _ = genH * genG := by rw [h, mul_one]

theorem genG_sq : genG ^ 2 = genY ^ 2 := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := FreeGroup.of 2 ^ 2 * (FreeGroup.of 1 ^ 2)⁻¹) (by simp [unitaryFourRels])
  simp only [map_mul, map_inv, map_pow] at h
  exact mul_inv_eq_one.mp h

theorem genH_sq : genH ^ 2 = genX ^ 2 * genY ^ 2 := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := FreeGroup.of 3 ^ 2 * (FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2)⁻¹)
    (by simp [unitaryFourRels])
  simp only [map_mul, map_inv, map_pow] at h
  exact mul_inv_eq_one.mp h

theorem genX_mul_genG : genX * genG = genG * genX ^ 3 := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := (FreeGroup.of 0)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 0 * FreeGroup.of 2 *
      (FreeGroup.of 0 ^ 2)⁻¹) (by simp [unitaryFourRels])
  simp only [map_mul, map_inv, map_pow] at h
  have h' : genX⁻¹ * genG⁻¹ * genX * genG = genX ^ 2 := mul_inv_eq_one.mp h
  calc genX * genG = genG * genX * (genX⁻¹ * genG⁻¹ * genX * genG) := by group
    _ = genG * genX ^ 3 := by rw [h']; group

theorem genY_mul_genG : genY * genG = genG * (genX ^ 2 * genY ^ 3) := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 2)⁻¹ * FreeGroup.of 1 * FreeGroup.of 2 *
      (FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2)⁻¹) (by simp [unitaryFourRels])
  simp only [map_mul, map_inv, map_pow] at h
  have h' : genY⁻¹ * genG⁻¹ * genY * genG = genX ^ 2 * genY ^ 2 := mul_inv_eq_one.mp h
  calc genY * genG = genG * (genY * (genY⁻¹ * genG⁻¹ * genY * genG)) := by group
    _ = genG * (genY * genX ^ 2 * genY ^ 2) := by rw [h', mul_assoc]
    _ = genG * (genX ^ 2 * genY ^ 3) := by
      rw [← (commute_genX_genY.pow_left 2).eq, mul_assoc, ← pow_succ']

theorem genX_mul_genH : genX * genH = genH * (genX ^ 3 * genY ^ 2) := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := (FreeGroup.of 0)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 0 * FreeGroup.of 3 *
      (FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2)⁻¹) (by simp [unitaryFourRels])
  simp only [map_mul, map_inv, map_pow] at h
  have h' : genX⁻¹ * genH⁻¹ * genX * genH = genX ^ 2 * genY ^ 2 := mul_inv_eq_one.mp h
  calc genX * genH = genH * (genX * (genX⁻¹ * genH⁻¹ * genX * genH)) := by group
    _ = genH * (genX * genX ^ 2 * genY ^ 2) := by rw [h', mul_assoc]
    _ = genH * (genX ^ 3 * genY ^ 2) := by rw [← pow_succ']

theorem genY_mul_genH : genY * genH = genH * genY ^ 3 := by
  have h := PresentedGroup.one_of_mem (rels := unitaryFourRels)
    (x := (FreeGroup.of 1)⁻¹ * (FreeGroup.of 3)⁻¹ * FreeGroup.of 1 * FreeGroup.of 3 *
      (FreeGroup.of 1 ^ 2)⁻¹) (by simp [unitaryFourRels])
  simp only [map_mul, map_inv, map_pow] at h
  have h' : genY⁻¹ * genH⁻¹ * genY * genH = genY ^ 2 := mul_inv_eq_one.mp h
  calc genY * genH = genH * genY * (genY⁻¹ * genH⁻¹ * genY * genH) := by group
    _ = genH * genY ^ 3 := by rw [h']; group

theorem xy_mul_xy (a b c d : ℕ) :
    genX ^ a * genY ^ b * (genX ^ c * genY ^ d) = genX ^ (a + c) * genY ^ (b + d) := by
  rw [mul_assoc, ← mul_assoc (genY ^ b), ((commute_genX_genY.pow_pow c b).eq).symm,
    mul_assoc (genX ^ c), ← mul_assoc, ← pow_add, ← pow_add]

theorem genX_pow_mul_genG (i : ℕ) : genX ^ i * genG = genG * genX ^ (3 * i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, mul_assoc, genX_mul_genG, ← mul_assoc, ih, mul_assoc, ← pow_add]
    ring_nf

theorem genY_pow_mul_genG (j : ℕ) :
    genY ^ j * genG = genG * (genX ^ (2 * j) * genY ^ (3 * j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_assoc, genY_mul_genG, ← mul_assoc, ih, mul_assoc, xy_mul_xy]
    ring_nf

theorem xy_mul_genG (i j : ℕ) :
    genX ^ i * genY ^ j * genG = genG * (genX ^ (3 * i + 2 * j) * genY ^ (3 * j)) := by
  rw [mul_assoc, genY_pow_mul_genG, ← mul_assoc, genX_pow_mul_genG, mul_assoc,
    ← mul_assoc (genX ^ (3 * i)), ← pow_add]

theorem genX_pow_mul_genH (i : ℕ) :
    genX ^ i * genH = genH * (genX ^ (3 * i) * genY ^ (2 * i)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, mul_assoc, genX_mul_genH, ← mul_assoc, ih, mul_assoc, xy_mul_xy]
    ring_nf

theorem genY_pow_mul_genH (j : ℕ) : genY ^ j * genH = genH * genY ^ (3 * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, mul_assoc, genY_mul_genH, ← mul_assoc, ih, mul_assoc, ← pow_add]
    ring_nf

theorem xy_mul_genH (i j : ℕ) :
    genX ^ i * genY ^ j * genH = genH * (genX ^ (3 * i) * genY ^ (2 * i + 3 * j)) := by
  rw [mul_assoc, genY_pow_mul_genH, ← mul_assoc, genX_pow_mul_genH, mul_assoc, mul_assoc,
    ← pow_add, ← mul_assoc]

theorem commute_genY_sq_genH : Commute (genY ^ 2) genH := by
  change genY ^ 2 * genH = genH * genY ^ 2
  rw [genY_pow_mul_genH, show 3 * 2 = 4 + 2 by rfl, pow_add, genY_pow_four, one_mul]

@[expose] def normalWord (u v i j : ℕ) : UnitaryFourPresented :=
  genG ^ u * genH ^ v * (genX ^ i * genY ^ j)

@[expose] def normalWords : Set UnitaryFourPresented :=
  {p | ∃ u v i j : ℕ, u < 2 ∧ v < 2 ∧ p = normalWord u v i j}

theorem normalWord_mul_genX (u v i j : ℕ) :
    normalWord u v i j * genX = normalWord u v (i + 1) j := by
  have h := xy_mul_xy i j 1 0
  rw [pow_one, pow_zero, mul_one, add_zero] at h
  rw [normalWord, normalWord, mul_assoc, h]

theorem normalWord_mul_genY (u v i j : ℕ) :
    normalWord u v i j * genY = normalWord u v i (j + 1) := by
  rw [normalWord, normalWord, mul_assoc, mul_assoc (genX ^ i), ← pow_succ]

theorem normalWord_mul_genG (u v i j : ℕ) :
    normalWord u v i j * genG = normalWord (u + 1) v (3 * i + 2 * j) (3 * j) := by
  have hc : genH ^ v * genG = genG * genH ^ v := ((commute_genG_genH.pow_right v).eq).symm
  calc normalWord u v i j * genG = genG ^ u * genH ^ v * (genX ^ i * genY ^ j * genG) := by
        rw [normalWord, mul_assoc]
    _ = genG ^ u * (genH ^ v * genG) * (genX ^ (3 * i + 2 * j) * genY ^ (3 * j)) := by
        rw [xy_mul_genG]
        simp only [mul_assoc]
    _ = normalWord (u + 1) v (3 * i + 2 * j) (3 * j) := by
        rw [hc, normalWord, pow_succ]
        simp only [mul_assoc]

theorem normalWord_mul_genH (u v i j : ℕ) :
    normalWord u v i j * genH = normalWord u (v + 1) (3 * i) (2 * i + 3 * j) := by
  rw [normalWord, normalWord, mul_assoc, xy_mul_genH, pow_succ]
  simp only [mul_assoc]

theorem normalWord_two (v i j : ℕ) : normalWord 2 v i j = normalWord 0 v i (j + 2) := by
  have h := xy_mul_xy 0 2 i j
  rw [pow_zero, one_mul, zero_add] at h
  rw [normalWord, normalWord, genG_sq, pow_zero, one_mul, (commute_genY_sq_genH.pow_right v).eq,
    mul_assoc, h, add_comm]

theorem normalWord_two' (u i j : ℕ) : normalWord u 2 i j = normalWord u 0 (i + 2) (j + 2) := by
  rw [normalWord, normalWord, genH_sq, pow_zero, mul_one, mul_assoc, xy_mul_xy, add_comm i,
    add_comm j]

theorem normalWords_mul_gen {p : UnitaryFourPresented} (hp : p ∈ normalWords) (k : Fin 4) :
    p * PresentedGroup.of k ∈ normalWords := by
  obtain ⟨u, v, i, j, hu, hv, rfl⟩ := hp
  fin_cases k
  · exact ⟨u, v, i + 1, j, hu, hv, normalWord_mul_genX u v i j⟩
  · exact ⟨u, v, i, j + 1, hu, hv, normalWord_mul_genY u v i j⟩
  · change normalWord u v i j * genG ∈ normalWords
    rw [normalWord_mul_genG]
    interval_cases u
    · exact ⟨1, v, _, _, by norm_num, hv, rfl⟩
    · exact ⟨0, v, _, _, by norm_num, hv, normalWord_two v _ _⟩
  · change normalWord u v i j * genH ∈ normalWords
    rw [normalWord_mul_genH]
    interval_cases v
    · exact ⟨u, 1, _, _, hu, by norm_num, rfl⟩
    · exact ⟨u, 0, _, _, hu, by norm_num, normalWord_two' u _ _⟩

theorem normalWords_mul_gen_pow {p : UnitaryFourPresented} (hp : p ∈ normalWords) (k : Fin 4)
    (n : ℕ) : p * PresentedGroup.of k ^ n ∈ normalWords := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc]
    exact normalWords_mul_gen ih k

theorem gen_inv_eq (k : Fin 4) :
    ∃ w : List (Fin 4), (PresentedGroup.of k : UnitaryFourPresented)⁻¹ =
      (w.map fun l => (PresentedGroup.of l : UnitaryFourPresented)).prod := by
  fin_cases k
  · refine ⟨[0, 0, 0], ?_⟩
    change genX⁻¹ = genX * (genX * (genX * 1))
    rw [inv_eq_of_mul_eq_one_right]
    rw [mul_one, ← pow_two, ← pow_succ', ← pow_succ']
    exact genX_pow_four
  · refine ⟨[1, 1, 1], ?_⟩
    change genY⁻¹ = genY * (genY * (genY * 1))
    rw [inv_eq_of_mul_eq_one_right]
    rw [mul_one, ← pow_two, ← pow_succ', ← pow_succ']
    exact genY_pow_four
  · refine ⟨[2, 1, 1], ?_⟩
    change genG⁻¹ = genG * (genY * (genY * 1))
    rw [inv_eq_of_mul_eq_one_right]
    rw [mul_one, ← pow_two, ← mul_assoc, ← pow_two, genG_sq, ← pow_add]
    exact genY_pow_four
  · refine ⟨[3, 0, 0, 1, 1], ?_⟩
    change genH⁻¹ = genH * (genX * (genX * (genY * (genY * 1))))
    rw [inv_eq_of_mul_eq_one_right]
    have h : genH * (genH * (genX * (genX * (genY * (genY * 1))))) =
        genH ^ 2 * (genX ^ 2 * genY ^ 2) := by
      simp only [pow_two, mul_one, mul_assoc]
    rw [h, genH_sq, xy_mul_xy]
    norm_num [genX_pow_four, genY_pow_four]

theorem normalWords_mul_list {p : UnitaryFourPresented} (hp : p ∈ normalWords)
    (w : List (Fin 4)) :
    p * (w.map fun l => (PresentedGroup.of l : UnitaryFourPresented)).prod ∈ normalWords := by
  induction w generalizing p with
  | nil => simpa using hp
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih (normalWords_mul_gen hp k)

theorem mem_normalWords (p : UnitaryFourPresented) : p ∈ normalWords := by
  have hp : p ∈ Subgroup.closure (Set.range (PresentedGroup.of (rels := unitaryFourRels))) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top p
  have hone : (1 : UnitaryFourPresented) ∈ normalWords :=
    ⟨0, 0, 0, 0, by norm_num, by norm_num, by simp [normalWord]⟩
  suffices h : ∀ q ∈ normalWords, q * p ∈ normalWords by simpa using h 1 hone
  induction hp using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact fun q hq => normalWords_mul_gen hq k
  | inv_mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨w, hw⟩ := gen_inv_eq k
    rw [hw]
    exact fun q hq => normalWords_mul_list hq w
  | one => exact fun q hq => by simpa using hq
  | mul x y _ _ hx hy =>
    intro q hq
    rw [← mul_assoc]
    exact hy _ (hx q hq)

@[expose] def normalWordFin (t : Fin 2 × Fin 2 × Fin 4 × Fin 4) : UnitaryFourPresented :=
  normalWord t.1 t.2.1 t.2.2.1 t.2.2.2

theorem normalWordFin_surjective : Function.Surjective normalWordFin := by
  intro p
  obtain ⟨u, v, i, j, hu, hv, rfl⟩ := mem_normalWords p
  refine ⟨(⟨u, hu⟩, ⟨v, hv⟩, ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩,
    ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
  simp only [normalWordFin, normalWord]
  rw [← pow_eq_pow_mod i genX_pow_four, ← pow_eq_pow_mod j genY_pow_four]

instance instFinite : Finite UnitaryFourPresented :=
  Finite.of_surjective _ normalWordFin_surjective

theorem natCard_le : Nat.card UnitaryFourPresented ≤ 64 := by
  have h := Nat.card_le_card_of_surjective _ normalWordFin_surjective
  simpa using h

section W

variable {K : Type} [Field K] {hK : Nat.card K = 16}

open UnitaryFourW

theorem lift_rels_eq_one {l c : K} (hl : l ^ 2 + l + 1 = 0) (hc₁ : c + c ^ 4 = 1)
    (hc₅ : c ^ 5 = l ^ 2) {X Y G J : unitaryFourW K hK} (hX : fst X = 1) (hY : fst Y = l)
    (hG : fst G = c) (hJ : fst J = l * c) :
    ∀ r ∈ unitaryFourRels, FreeGroup.lift ![X, Y, G, J] r = 1 := by
  have := charP_two_of_natCard_eq_sixteen hK
  have nX := snd_add_snd_pow_four X
  have nY := snd_add_snd_pow_four Y
  have nG := snd_add_snd_pow_four G
  have nJ := snd_add_snd_pow_four J
  intro r hr
  simp only [unitaryFourRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
  · exact pow_four_eq_one X
  · exact pow_four_eq_one Y
  all_goals
    ext <;> simp only [pow_two, fst_mul, snd_mul, fst_inv, snd_inv, fst_one, snd_one, hX, hY,
      hG, hJ] at nX nY nG nJ ⊢ <;> grind

theorem closure_eq_top {l c : K} (hl : l ^ 2 + l + 1 = 0) (hc₁ : c + c ^ 4 = 1)
    {X Y G J : unitaryFourW K hK} (hX : fst X = 1) (hY : fst Y = l)
    (hG : fst G = c) (hJ : fst J = l * c) (M : Subgroup (unitaryFourW K hK)) (hXM : X ∈ M)
    (hYM : Y ∈ M) (hGM : G ∈ M) (hJM : J ∈ M) : M = ⊤ := by
  have := charP_two_of_natCard_eq_sixteen hK
  have hcen : ∀ k : unitaryFourW K hK, fst k = 0 → k ∈ M := by
    intro k hk
    rcases eq_zero_or_eq_one_or_of_pow_four_eq_self hl (snd_pow_four_of_fst_eq_zero hk) with
      h | h | h | h
    · have : k = 1 := by
        ext
        · rw [hk, fst_one]
        · rw [h, snd_one]
      rw [this]
      exact M.one_mem
    · have : k = X ^ 2 := by
        ext
        · rw [hk, fst_sq]
        · rw [h, snd_sq, hX, one_pow]
      rw [this]
      exact M.pow_mem hXM 2
    · have : k = X ^ 2 * Y ^ 2 := by
        ext
        · rw [hk, fst_mul, fst_sq, fst_sq, add_zero]
        · rw [h, snd_mul, snd_sq, snd_sq, fst_sq, fst_sq, hX, hY]
          grind
      rw [this]
      exact M.mul_mem (M.pow_mem hXM 2) (M.pow_mem hYM 2)
    · have : k = Y ^ 2 := by
        ext
        · rw [hk, fst_sq]
        · rw [h, snd_sq, hY]
          grind
      rw [this]
      exact M.pow_mem hYM 2
  have hfst : ∀ s : K, s ^ 4 = s → ∃ m ∈ M, fst m = s := by
    intro s hs
    rcases eq_zero_or_eq_one_or_of_pow_four_eq_self hl hs with h | h | h | h
    · exact ⟨1, M.one_mem, by rw [fst_one, h]⟩
    · exact ⟨X, hXM, by rw [hX, h]⟩
    · exact ⟨Y, hYM, by rw [hY, h]⟩
    · exact ⟨X * Y, M.mul_mem hXM hYM, by rw [fst_mul, hX, hY, h]; grind⟩
  have hsnd : ∀ t : K, t ^ 4 = t → ∃ m ∈ M, fst m = t * c := by
    intro t ht
    rcases eq_zero_or_eq_one_or_of_pow_four_eq_self hl ht with h | h | h | h
    · exact ⟨1, M.one_mem, by rw [fst_one, h, zero_mul]⟩
    · exact ⟨G, hGM, by rw [hG, h, one_mul]⟩
    · exact ⟨J, hJM, by rw [hJ, h]⟩
    · exact ⟨G * J, M.mul_mem hGM hJM, by rw [fst_mul, hG, hJ, h]; grind⟩
  have hc : c ^ 4 ≠ c := by
    intro h
    grind
  rw [eq_top_iff]
  intro w _
  obtain ⟨s, t, hs, ht, hst⟩ := exists_eq_add_mul_of_pow_four_ne hK hc (fst w)
  obtain ⟨m₁, hm₁, h₁⟩ := hfst s hs
  obtain ⟨m₂, hm₂, h₂⟩ := hsnd t ht
  have hk : w * (m₁ * m₂)⁻¹ ∈ M := hcen _ (by
    rw [fst_mul, fst_inv, fst_mul, h₁, h₂, ← hst]
    grind)
  have hw : w = w * (m₁ * m₂)⁻¹ * (m₁ * m₂) := by group
  rw [hw]
  exact M.mul_mem hk (M.mul_mem hm₁ hm₂)

theorem nonempty_mulEquiv_unitaryFourW (K : Type) [Field K] (hK : Nat.card K = 16) :
    Nonempty (UnitaryFourPresented ≃* unitaryFourW K hK) := by
  obtain ⟨l, hl⟩ := exists_sq_add_self_add_one_eq_zero hK
  obtain ⟨c, hc₁, hc₅⟩ := exists_trace_one_norm_sq hK hl
  obtain ⟨X, hX⟩ := exists_fst_eq (hK := hK) 1
  obtain ⟨Y, hY⟩ := exists_fst_eq (hK := hK) l
  obtain ⟨G, hG⟩ := exists_fst_eq (hK := hK) c
  obtain ⟨J, hJ⟩ := exists_fst_eq (hK := hK) (l * c)
  let φ := PresentedGroup.toGroup (lift_rels_eq_one hl hc₁ hc₅ hX hY hG hJ)
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine closure_eq_top hl hc₁ hX hY hG hJ φ.range ⟨PresentedGroup.of 0, ?_⟩
      ⟨PresentedGroup.of 1, ?_⟩ ⟨PresentedGroup.of 2, ?_⟩ ⟨PresentedGroup.of 3, ?_⟩ <;>
      exact PresentedGroup.toGroup.of _
  have hbij : Function.Bijective φ := hsurj.bijective_of_nat_card_le (by
    rw [natCard_unitaryFourW]
    exact natCard_le)
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end W

end UnitaryFourPresented

open UnitaryFourPresented in
theorem unitaryFourPresented_card : Nat.card UnitaryFourPresented = 64 := by
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := nonempty_mulEquiv_unitaryFourW (GaloisField 2 4) hK
  rw [Nat.card_congr e.toEquiv, UnitaryFourW.natCard_unitaryFourW]

theorem nonempty_unitaryFourPresented_mulEquiv_sylow {H : Type} [Group H]
    (hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2) (U : Sylow 2 H) :
    Nonempty (UnitaryFourPresented ≃* (U : Subgroup H)) := by
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := UnitaryFourPresented.nonempty_mulEquiv_unitaryFourW (GaloisField 2 4) hK
  obtain ⟨e'⟩ := nonempty_sylow_equiv_unitaryFourW hH U (GaloisField 2 4) hK
  exact ⟨e.trans e'.symm⟩

theorem unitaryFourPresented_isSylow :
    ∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧
      Nonempty (CFSG.RankTwoShapes.UnitaryFourPresented ≃* (U : Subgroup H)) := by
  have hH : CFSG.Assembly.LowTwoRank.StatedClassicalModel (CFSG.Theory.Comparator.PSU3Model 2)
      .PSU 3 2 2 :=
    (statedClassicalModel_PSU_three_two_iff _ 2 le_rfl).mpr ⟨MulEquiv.refl _⟩
  obtain ⟨U⟩ := Sylow.nonempty (p := 2) (G := CFSG.Theory.Comparator.PSU3Model 2)
  exact ⟨CFSG.Theory.Comparator.PSU3Model 2, inferInstance, U, hH,
    nonempty_unitaryFourPresented_mulEquiv_sylow hH U⟩

end CFSG.RankTwoShapes
