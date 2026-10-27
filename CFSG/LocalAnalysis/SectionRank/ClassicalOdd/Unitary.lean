module

public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic

public section

namespace CFSG.SectionRank.ClassicalOdd

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type} [Field K]

@[expose] def hstar (σ : K →+* K) {ι : Type} [Fintype ι] (A : Matrix ι ι K) : Matrix ι ι K :=
  (A.map σ)ᵀ

section Hstar

variable (σ : K →+* K) {ι : Type} [Fintype ι]

theorem hstar_mul (A B : Matrix ι ι K) : hstar σ (A * B) = hstar σ B * hstar σ A := by
  rw [hstar, Matrix.map_mul, transpose_mul]
  rfl

theorem hstar_add (A B : Matrix ι ι K) : hstar σ (A + B) = hstar σ A + hstar σ B := by
  rw [hstar, Matrix.map_add _ (map_add σ), transpose_add]
  rfl

theorem hstar_one [DecidableEq ι] : hstar σ (1 : Matrix ι ι K) = 1 := by
  rw [hstar, Matrix.map_one _ (map_zero σ) (map_one σ), transpose_one]

theorem hstar_smul (c : K) (A : Matrix ι ι K) : hstar σ (c • A) = σ c • hstar σ A := by
  rw [hstar, Matrix.map_smul' _ _ _ (map_mul σ), transpose_smul]
  rfl

theorem hstar_neg (A : Matrix ι ι K) : hstar σ (-A) = -hstar σ A := by
  rw [hstar, Matrix.map_neg _ (map_neg σ), transpose_neg]
  rfl

end Hstar

theorem exists_unitary_elems [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    ∃ u η : K, u ^ (p ^ f) * u = -1 ∧ η ≠ 0 ∧ η ^ (p ^ f) = -η := by
  have := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hchar
  have hg0 : g ≠ 0 := fun h => hg (h ▸ IsSquare.zero)
  have hgpow : g ^ (Fintype.card K / 2) = -1 :=
    (FiniteField.pow_dichotomy hchar hg0).resolve_left fun h =>
      hg ((FiniteField.isSquare_iff hchar hg0).2 h)
  have hodd : Odd (p ^ f) := (((Fact.out : p.Prime).eq_two_or_odd').resolve_left hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have hcard : Fintype.card K / 2 = 2 * m * m + 2 * m := by
    rw [← Nat.card_eq_fintype_card, hK, hm,
      show (2 * m + 1) ^ 2 = 1 + 2 * (2 * m * m + 2 * m) by ring, Nat.add_mul_div_left _ _ two_pos]
    simp
  refine ⟨g ^ m, g ^ (m + 1), ?_, pow_ne_zero _ hg0, ?_⟩
  · rw [← pow_mul, ← pow_add, hm, show m * (2 * m + 1) + m = 2 * m * m + 2 * m by ring, ← hcard,
      hgpow]
  · rw [← pow_mul, hm, show (m + 1) * (2 * m + 1) = (2 * m * m + 2 * m) + (m + 1) by ring,
      pow_add, ← hcard, hgpow, neg_one_mul]

section Three

variable (σ : K →+* K) (u : K)

@[expose] def uM₁ : Matrix (Fin 3) (Fin 3) K := !![0, 0, -1; 0, 0, -u; 1, σ u, 0]

@[expose] def uM₂ : Matrix (Fin 3) (Fin 3) K := !![1, σ u, 0; u, -1, 0; 0, 0, 0]

variable {σ u}

theorem uM₁_mul_uM₁ (hu : σ u * u = -1) : uM₁ σ u * uM₁ σ u = -uM₂ σ u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM₁, uM₂, mul_apply, Fin.sum_univ_three] <;>
    linear_combination -hu

theorem uM₁_mul_uM₂ (hu : σ u * u = -1) : uM₁ σ u * uM₂ σ u = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM₁, uM₂, mul_apply, Fin.sum_univ_three]
  linear_combination hu

theorem uM₂_mul_uM₁ (hu : σ u * u = -1) : uM₂ σ u * uM₁ σ u = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM₁, uM₂, mul_apply, Fin.sum_univ_three]
  linear_combination -hu

theorem uM₂_mul_uM₂ (hu : σ u * u = -1) : uM₂ σ u * uM₂ σ u = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM₂, mul_apply, Fin.sum_univ_three] <;>
    linear_combination hu

theorem hstar_uM₁ (hσ : ∀ x, σ (σ x) = x) : hstar σ (uM₁ σ u) = -uM₁ σ u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, uM₁, hσ]

theorem hstar_uM₂ (hσ : ∀ x, σ (σ x) = x) : hstar σ (uM₂ σ u) = uM₂ σ u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hstar, uM₂, hσ]

theorem uM_mul (hu : σ u * u = -1) (a b c d : K) :
    (1 + a • uM₁ σ u + b • uM₂ σ u) * (1 + c • uM₁ σ u + d • uM₂ σ u) =
      1 + (a + c) • uM₁ σ u + (b + d - a * c) • uM₂ σ u := by
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, uM₁_mul_uM₁ hu,
    uM₁_mul_uM₂ hu, uM₂_mul_uM₁ hu, uM₂_mul_uM₂ hu, smul_zero, smul_neg]
  module

@[expose] def uA (σ : K →+* K) (x : K) : K := (x + σ x) / 2

@[expose] def uB (σ : K →+* K) (x : K) : K := -uA σ x ^ 2 / 2 + (x - σ x) / 2

@[expose] def uT (σ : K →+* K) (u x : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + uA σ x • uM₁ σ u + uB σ x • uM₂ σ u

theorem uT_add (hu : σ u * u = -1) (h2 : (2 : K) ≠ 0) (x y : K) :
    uT σ u (x + y) = uT σ u x * uT σ u y := by
  rw [uT, uT, uT, uM_mul hu]
  congr 3
  · simp only [uA, map_add]
    ring
  · simp only [uB, uA, map_add]
    field_simp
    ring

theorem uT_zero : uT σ u 0 = 1 := by
  simp [uT, uA, uB]

theorem hstar_uT (hσ : ∀ x, σ (σ x) = x) (hu : σ u * u = -1) (h2 : (2 : K) ≠ 0) (x : K) :
    hstar σ (uT σ u x) * uT σ u x = 1 := by
  have hA : σ (uA σ x) = uA σ x := by
    rw [uA, map_div₀, map_add, hσ, map_ofNat, add_comm]
  have hB : σ (uB σ x) = -uA σ x ^ 2 / 2 + (σ x - x) / 2 := by
    rw [uB, map_add, map_div₀, map_div₀, map_neg, map_pow, hA, map_sub, hσ, map_ofNat]
  rw [uT, hstar_add, hstar_add, hstar_one, hstar_smul, hstar_smul, hstar_uM₁ hσ, hstar_uM₂ hσ,
    smul_neg, ← neg_smul, uM_mul hu, hA, hB]
  have e1 : -uA σ x + uA σ x = 0 := neg_add_cancel _
  have e2 : -uA σ x ^ 2 / 2 + (σ x - x) / 2 + uB σ x - -uA σ x * uA σ x = 0 := by
    rw [uB]
    field_simp
    ring
  rw [e1, e2, zero_smul, zero_smul, add_zero, add_zero]

theorem uT_injective (h2 : (2 : K) ≠ 0) : Function.Injective (uT σ u) := by
  intro x y h
  have h20 := congrFun (congrFun h 2) 0
  have h00 := congrFun (congrFun h 0) 0
  simp [uT, uM₁, uM₂] at h20 h00
  have hx : x = uA σ x + (uB σ x + uA σ x ^ 2 / 2) := by
    rw [uB, uA]
    field_simp
    ring
  have hy : y = uA σ y + (uB σ y + uA σ y ^ 2 / 2) := by
    rw [uB, uA]
    field_simp
    ring
  rw [hx, hy, h20, h00]

theorem uM₁_mulVec (hu : σ u * u = -1) : uM₁ σ u *ᵥ ![1, u, 0] = 0 := by
  ext i
  fin_cases i <;> simp [uM₁, mulVec, dotProduct, Fin.sum_univ_three]
  linear_combination hu

theorem uM₂_mulVec (hu : σ u * u = -1) : uM₂ σ u *ᵥ ![1, u, 0] = 0 := by
  ext i
  fin_cases i <;> simp [uM₂, mulVec, dotProduct, Fin.sum_univ_three]
  linear_combination hu

theorem uT_mulVec (hu : σ u * u = -1) (x : K) : uT σ u x *ᵥ ![1, u, 0] = ![1, u, 0] := by
  rw [uT, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec, uM₁_mulVec hu,
    uM₂_mulVec hu, smul_zero, smul_zero, add_zero, add_zero]

@[expose] noncomputable def uHom (σ : K →+* K) (u : K) (hu : σ u * u = -1) (h2 : (2 : K) ≠ 0) :
    Multiplicative K →* GL (Fin 3) K :=
  glOfAdd (uT σ u) uT_zero (uT_add hu h2)

end Three

theorem frob_apply {p f : ℕ} [Fact p.Prime] [CharP K p] (x : K) :
    iterateFrobenius K p f x = x ^ (p ^ f) :=
  iterateFrobenius_def p f x

theorem frob_frob [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (x : K) :
    iterateFrobenius K p f (iterateFrobenius K p f x) = x := by
  have := Fintype.ofFinite K
  rw [frob_apply, frob_apply, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem two_mul_le_pRank_SU_three [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    2 * f ≤ pRank p (⊤ : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))) := by
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := charP_of_card hK'
  obtain ⟨u, -, hu, -, -⟩ := exists_unitary_elems hp2 hK
  set σ := iterateFrobenius K p f
  have hσ := frob_frob hK
  have hu' : σ u * u = -1 := by rw [frob_apply]; exact hu
  have h2 : (2 : K) ≠ 0 := by
    have := Ring.two_ne_zero (R := K) (by rw [ringChar.eq K p]; exact hp2)
    exact this
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) (by rw [Nat.card_congr Multiplicative.toAdd, hK'])
    (uHom σ u hu' h2) (glOfAdd_injective (uT_injective h2)) (fun x => ?_) (v := ![1, u, 0])
    (fun h => by simpa using congrFun h 0) (fun x => uT_mulVec hu' x.toAdd)
  refine Subgroup.subset_closure ⟨det_eq_one_of_hom (p := p) _ x, ?_⟩
  have hmap : ((uHom σ u hu' h2 x : Matrix (Fin 3) (Fin 3) K).map (· ^ (p ^ f))) =
      (uHom σ u hu' h2 x : Matrix (Fin 3) (Fin 3) K).map σ := by
    congr 1
  rw [hmap]
  exact hstar_uT hσ hu' h2 x.toAdd

section Four

variable (σ : K →+* K) (u : K) {n : ℕ} (hn : 4 ≤ n)

@[expose] def uε (j : Fin 2) : Fin n → K :=
  Pi.single ⟨2 * j, by have := j.isLt; omega⟩ 1 + Pi.single ⟨2 * j + 1, by have := j.isLt; omega⟩ u

@[expose] def uεbar (j : Fin 2) : Fin n → K :=
  Pi.single ⟨2 * j, by have := j.isLt; omega⟩ 1 +
    Pi.single ⟨2 * j + 1, by have := j.isLt; omega⟩ (σ u)

@[expose] def uP (j k : Fin 2) : Matrix (Fin n) (Fin n) K := vecMulVec (uε u hn j) (uεbar σ u hn k)

variable {σ u}

theorem uεbar_dotProduct (hu : σ u * u = -1) (k l : Fin 2) :
    uεbar σ u hn k ⬝ᵥ uε u hn l = 0 := by
  fin_cases k <;> fin_cases l <;>
    simp [uε, uεbar, dotProduct_add] <;>
    linear_combination hu

theorem uP_mul_uP (hu : σ u * u = -1) (j k l m : Fin 2) :
    uP σ u hn j k * uP σ u hn l m = 0 := by
  rw [uP, uP, vecMulVec_mul_vecMulVec, uεbar_dotProduct hn hu, zero_smul]
  ext a b
  simp [vecMulVec_apply]

theorem comp_uε (j : Fin 2) : σ ∘ uε u hn j = uεbar σ u hn j := by
  ext m
  simp only [Function.comp, uε, uεbar, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp

theorem comp_uεbar (hσ : ∀ x, σ (σ x) = x) (j : Fin 2) : σ ∘ uεbar σ u hn j = uε u hn j := by
  ext m
  simp only [Function.comp, uε, uεbar, Pi.add_apply, Pi.single_apply]
  split_ifs <;> simp [hσ]

theorem hstar_uP (hσ : ∀ x, σ (σ x) = x) (j k : Fin 2) :
    hstar σ (uP σ u hn j k) = uP σ u hn k j := by
  have h : (uP σ u hn j k).map σ = vecMulVec (σ ∘ uε u hn j) (σ ∘ uεbar σ u hn k) := by
    ext a b
    simp [uP, vecMulVec_apply]
  rw [hstar, h, transpose_vecMulVec, comp_uε, comp_uεbar hn hσ]
  rfl

theorem uP_mulVec (hu : σ u * u = -1) (j k : Fin 2) : uP σ u hn j k *ᵥ uε u hn 0 = 0 := by
  rw [uP, vecMulVec_mulVec, uεbar_dotProduct hn hu]
  simp

@[expose] def uN (σ : K →+* K) (u η : K) (v : K × K) : Matrix (Fin n) (Fin n) K :=
  (v.2 - σ v.2) • uP σ u hn 0 0 + (η * (v.2 + σ v.2)) • uP σ u hn 1 1 + v.1 • uP σ u hn 0 1 +
    (-σ v.1) • uP σ u hn 1 0

variable {η : K}

theorem uN_add (v w : K × K) : uN hn σ u η (v + w) = uN hn σ u η v + uN hn σ u η w := by
  simp only [uN, Prod.fst_add, Prod.snd_add, map_add]
  module

theorem uN_zero : uN hn σ u η 0 = 0 := by
  simp [uN]

theorem uN_mul (hu : σ u * u = -1) (v w : K × K) : uN hn σ u η v * uN hn σ u η w = 0 := by
  simp only [uN, add_mul, mul_add, smul_mul_smul_comm, uP_mul_uP hn hu, smul_zero, add_zero]

theorem hstar_uN (hσ : ∀ x, σ (σ x) = x) (hη : σ η = -η) (v : K × K) :
    hstar σ (uN hn σ u η v) = -uN hn σ u η v := by
  simp only [uN, hstar_add, hstar_smul, hstar_uP hn hσ, map_sub, map_mul, map_add, map_neg, hσ,
    hη]
  module

theorem uN_mulVec (hu : σ u * u = -1) (v : K × K) : uN hn σ u η v *ᵥ uε u hn 0 = 0 := by
  simp only [uN, add_mulVec, smul_mulVec, uP_mulVec hn hu, smul_zero, add_zero]

theorem uN_injective (h2 : (2 : K) ≠ 0) (hη0 : η ≠ 0) : Function.Injective (uN hn σ u η) := by
  intro v w h
  have h02 := congrFun (congrFun h ⟨0, by omega⟩) ⟨2, by omega⟩
  have h00 := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
  have h22 := congrFun (congrFun h ⟨2, by omega⟩) ⟨2, by omega⟩
  simp [uN, uP, uε, uεbar, vecMulVec_apply] at h02 h00 h22
  have h22' : v.2 + σ v.2 = w.2 + σ w.2 := by
    rcases h22 with h22 | h22
    · exact h22
    · exact absurd h22 hη0
  refine Prod.ext h02 ?_
  have h3 : (2 : K) * v.2 = 2 * w.2 := by linear_combination h00 + h22'
  exact mul_left_cancel₀ h2 h3

@[expose] noncomputable def uHom₄ (hu : σ u * u = -1) :
    Multiplicative (K × K) →* GL (Fin n) K :=
  glOfAdd (fun v => 1 + uN hn σ u η v) (by rw [uN_zero, add_zero]) (fun v w => by
    rw [uN_add, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, uN_mul hn hu, add_zero,
      add_assoc])

theorem hstar_uHom₄ (hu : σ u * u = -1) (hσ : ∀ x, σ (σ x) = x) (hη : σ η = -η) (v) :
    hstar σ (uHom₄ hn (η := η) hu v : Matrix (Fin n) (Fin n) K) * uHom₄ hn (η := η) hu v = 1 := by
  rw [uHom₄, coe_glOfAdd, hstar_add, hstar_one, hstar_uN hn hσ hη, mul_add, add_mul, add_mul,
    one_mul, mul_one, one_mul, neg_mul, uN_mul hn hu, neg_zero, add_zero, neg_add_cancel_right]

end Four

theorem four_mul_le_pRank_SU [Finite K] {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hK : Nat.card K = (p ^ f) ^ 2) :
    4 * f ≤ pRank p (⊤ : Subgroup (StatedProj (StatedSU n (p ^ f) K))) := by
  have hK' : Nat.card K = p ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have := charP_of_card hK'
  obtain ⟨u, η, hu, hη0, hη⟩ := exists_unitary_elems hp2 hK
  set σ := iterateFrobenius K p f
  have hσ := frob_frob hK
  have hu' : σ u * u = -1 := by rw [frob_apply]; exact hu
  have hη' : σ η = -η := by rw [frob_apply]; exact hη
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  refine le_pRank_statedProj (Fact.out : p.Prime).one_lt multiplicative_comm
    (pow_char_eq_one (K := K)) ?_ (uHom₄ hn (η := η) hu')
    (glOfAdd_injective fun v w h => uN_injective hn h2 hη0 (add_left_cancel h)) (fun x => ?_)
    (v := uε u hn 0)
    (fun h => by simpa [uε, Pi.single_apply, Fin.ext_iff] using congrFun h ⟨0, by omega⟩)
    (fun x => by
      rw [uHom₄, coe_glOfAdd, add_mulVec, one_mulVec, uN_mulVec hn hu', add_zero])
  · rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, hK', ← pow_add]
    congr 1
    ring
  · refine Subgroup.subset_closure ⟨det_eq_one_of_hom (p := p) _ x, ?_⟩
    have hmap : ((uHom₄ hn (η := η) hu' x : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f))) =
        (uHom₄ hn (η := η) hu' x : Matrix (Fin n) (Fin n) K).map σ := by
      congr 1
    rw [hmap]
    exact hstar_uHom₄ hn hu' hσ hη' x

end CFSG.SectionRank.ClassicalOdd
