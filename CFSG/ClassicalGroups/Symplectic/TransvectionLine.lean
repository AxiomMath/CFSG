module

public import CFSG.ClassicalGroups.Symplectic.TransvectionCentralizer
public import CFSG.Open.StatedAPI

public section

open Matrix CFSG.Open

namespace CFSG.ClassicalGroups.Symplectic

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem dot_apply_of_isometry {J A : Matrix ι ι K} (h : Aᵀ * J * A = J) (x y : ι → K) :
    (A *ᵥ x) ⬝ᵥ J *ᵥ (A *ᵥ y) = x ⬝ᵥ J *ᵥ y := by
  calc (A *ᵥ x) ⬝ᵥ J *ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ (J * A) *ᵥ y := by rw [Matrix.mulVec_mulVec]
    _ = ((A *ᵥ x) ᵥ* (J * A)) ⬝ᵥ y := Matrix.dotProduct_mulVec _ _ _
    _ = (x ᵥ* (Aᵀ * (J * A))) ⬝ᵥ y := by rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul]
    _ = (x ᵥ* J) ⬝ᵥ y := by rw [← Matrix.mul_assoc, h]
    _ = x ⬝ᵥ J *ᵥ y := (Matrix.dotProduct_mulVec _ _ _).symm

theorem exists_transvection_form_of_rank_eq_one {J t : Matrix ι ι K} (hJa : ∀ v, v ⬝ᵥ J *ᵥ v = 0)
    (hJn : ∀ x, (∀ y, x ⬝ᵥ J *ᵥ y = 0) → x = 0) (ht : tᵀ * J * t = J)
    (hrk : (t - 1).rank = 1) :
    ∃ (u : ι → K) (c : K), u ≠ 0 ∧ c ≠ 0 ∧
      ∀ x, (t - 1) *ᵥ x = (c * (u ⬝ᵥ J *ᵥ x)) • u := by
  set N : Matrix ι ι K := t - 1 with hN
  have htN : ∀ y, t *ᵥ y = y + N *ᵥ y := fun y => by
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  obtain ⟨u, hu0, hu⟩ : ∃ u : ι → K, u ≠ 0 ∧ ∀ y, ∃ c : K, N *ᵥ y = c • u := by
    unfold Matrix.rank at hrk
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hrk
    refine ⟨(v : ι → K), fun h => hv0 (Subtype.ext h), fun y => ?_⟩
    obtain ⟨c, hc⟩ := hv ⟨N *ᵥ y, ⟨y, rfl⟩⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  choose a ha using hu
  have hβneg : ∀ x y : ι → K, x ⬝ᵥ J *ᵥ y = -(y ⬝ᵥ J *ᵥ x) := fun x y => by
    have h1 := hJa (x + y)
    simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, hJa x, hJa y] at h1
    linear_combination h1
  have hrel : ∀ x y : ι → K, a y * (x ⬝ᵥ J *ᵥ u) + a x * (u ⬝ᵥ J *ᵥ y) = 0 := fun x y => by
    have h1 := dot_apply_of_isometry ht x y
    rw [htN x, htN y, Matrix.mulVec_add, ha x, ha y] at h1
    simp only [Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hJa u] at h1
    linear_combination h1
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ⬝ᵥ J *ᵥ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hJn u fun y => by rw [hβneg, hcon y, neg_zero])
  have hform : ∀ y, a y = -(a x₀ / (x₀ ⬝ᵥ J *ᵥ u)) * (u ⬝ᵥ J *ᵥ y) := fun y => by
    have h1 := hrel x₀ y
    field_simp
    linear_combination h1
  obtain ⟨y₁, hy₁⟩ : ∃ y₁, a y₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ y, N *ᵥ y = 0 := fun y => by rw [ha y, hcon y, zero_smul]
    have hN0 : N = 0 := by
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this
    rw [hN0, Matrix.rank_zero] at hrk
    exact absurd hrk (by norm_num)
  have hc0 : -(a x₀ / (x₀ ⬝ᵥ J *ᵥ u)) ≠ 0 := fun h => hy₁ (by rw [hform y₁, h, zero_mul])
  exact ⟨u, -(a x₀ / (x₀ ⬝ᵥ J *ᵥ u)), hu0, hc0, fun x => by rw [ha x, hform x]⟩


omit [DecidableEq ι] in
private theorem exists_pairing {J : Matrix ι ι K}
    (hJn : ∀ x, (∀ y, x ⬝ᵥ J *ᵥ y = 0) → x = 0) {u u' : ι → K}
    (hind : ∀ s r : K, s • u + r • u' = 0 → s = 0 ∧ r = 0) :
    ∃ x₁ x₂ : ι → K, u ⬝ᵥ J *ᵥ x₁ = 1 ∧ u' ⬝ᵥ J *ᵥ x₁ = 0 ∧
      u ⬝ᵥ J *ᵥ x₂ = 0 ∧ u' ⬝ᵥ J *ᵥ x₂ = 1 := by
  let φ : (ι → K) → ((ι → K) →ₗ[K] K) := fun v =>
    { toFun := fun x => v ⬝ᵥ J *ᵥ x
      map_add' := fun x y => by simp [Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c x => by simp [Matrix.mulVec_smul, dotProduct_smul] }
  let T : (ι → K) →ₗ[K] (Fin 2 → K) := LinearMap.pi ![φ u, φ u']
  have hT : ∀ x, T x = (u ⬝ᵥ J *ᵥ x) • (Pi.single 0 1 : Fin 2 → K) +
      (u' ⬝ᵥ J *ᵥ x) • (Pi.single 1 1 : Fin 2 → K) := by
    intro x
    ext i
    fin_cases i <;> simp [T, φ]
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ :=
      Submodule.exists_le_ker_of_lt_top (LinearMap.range T) (lt_top_iff_ne_top.mpr hne)
    have key : ∀ x, f (Pi.single 0 1) * (u ⬝ᵥ J *ᵥ x) + f (Pi.single 1 1) * (u' ⬝ᵥ J *ᵥ x) = 0 := by
      intro x
      have h : f (T x) = 0 := hf ⟨x, rfl⟩
      rw [hT x, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
      linear_combination h
    have hvec : f (Pi.single 0 1) • u + f (Pi.single 1 1) • u' = 0 := by
      apply hJn
      intro x
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      exact key x
    obtain ⟨h0, h1⟩ := hind _ _ hvec
    apply hf0
    apply LinearMap.ext
    intro y
    have hy : y = y 0 • (Pi.single 0 1 : Fin 2 → K) + y 1 • (Pi.single 1 1 : Fin 2 → K) := by
      ext i
      fin_cases i <;> simp
    rw [hy, map_add, map_smul, map_smul, h0, h1]
    simp
  obtain ⟨x₁, hx₁⟩ := hsurj (Pi.single 0 1)
  obtain ⟨x₂, hx₂⟩ := hsurj (Pi.single 1 1)
  refine ⟨x₁, x₂, ?_, ?_, ?_, ?_⟩
  · simpa [T, φ] using congrFun hx₁ 0
  · simpa [T, φ] using congrFun hx₁ 1
  · simpa [T, φ] using congrFun hx₂ 0
  · simpa [T, φ] using congrFun hx₂ 1


omit [DecidableEq ι] in
private theorem two_le_rank {J M : Matrix ι ι K}
    (hJn : ∀ x, (∀ y, x ⬝ᵥ J *ᵥ y = 0) → x = 0) {u u' : ι → K} {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hind : ∀ s r : K, s • u + r • u' = 0 → s = 0 ∧ r = 0)
    (hM : ∀ x, M *ᵥ x = (a * (u ⬝ᵥ J *ᵥ x)) • u + (b * (u' ⬝ᵥ J *ᵥ x)) • u') : 2 ≤ M.rank := by
  obtain ⟨x₁, x₂, h11, h12, h21, h22⟩ := exists_pairing hJn hind
  have hu : u ∈ LinearMap.range M.mulVecLin := by
    refine ⟨a⁻¹ • x₁, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hM x₁, h11, h12]
    simp [smul_smul, ha]
  have hu' : u' ∈ LinearMap.range M.mulVecLin := by
    refine ⟨b⁻¹ • x₂, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, hM x₂, h21, h22]
    simp [smul_smul, hb]
  have hli : LinearIndependent K ![u, u'] :=
    LinearIndependent.pair_iff.mpr hind
  have hspan : Submodule.span K (Set.range ![u, u']) ≤ LinearMap.range M.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hu'
  have h2 := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli] at h2
  simpa [Matrix.rank] using h2

theorem exists_eq_smul_of_commute_of_rank_eq_one [CharP K 2] {J t t' : Matrix ι ι K}
    (hJa : ∀ v, v ⬝ᵥ J *ᵥ v = 0) (hJn : ∀ x, (∀ y, x ⬝ᵥ J *ᵥ y = 0) → x = 0)
    (ht : tᵀ * J * t = J) (ht' : t'ᵀ * J * t' = J) (hrk' : (t' - 1).rank = 1)
    (hcomm : t * t' = t' * t) {u u' : ι → K} {c c' : K} (hu0 : u ≠ 0) (hc0 : c ≠ 0)
    (hc0' : c' ≠ 0)
    (hform : ∀ x, (t - 1) *ᵥ x = (c * (u ⬝ᵥ J *ᵥ x)) • u)
    (hform' : ∀ x, (t' - 1) *ᵥ x = (c' * (u' ⬝ᵥ J *ᵥ x)) • u')
    (hprod : t * t' = 1 ∨ (t * t' - 1).rank = 1) : ∃ μ : K, u' = μ • u := by
  by_contra hcon
  push Not at hcon
  have hu0' : u' ≠ 0 := fun h => hcon 0 (by rw [h, zero_smul])
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, u' ⬝ᵥ J *ᵥ x₀ ≠ 0 := by
    by_contra hx
    push Not at hx
    exact hu0' (hJn u' hx)
  have hfix : t *ᵥ u' = u' := by
    have h := mulVec_eq_of_commute_transvection hJa hJn ht' ht hrk' hcomm x₀
    rw [hform' x₀, Matrix.mulVec_smul] at h
    exact smul_right_injective _ (mul_ne_zero hc0' hx₀) h
  have hN : (t - 1) *ᵥ u' = 0 := by
    rw [Matrix.sub_mulVec, hfix, Matrix.one_mulVec, sub_self]
  have hprod_form : ∀ x, (t * t' - 1) *ᵥ x =
      (c * (u ⬝ᵥ J *ᵥ x)) • u + (c' * (u' ⬝ᵥ J *ᵥ x)) • u' := by
    intro x
    have e : t * t' - 1 = (t - 1) * (t' - 1) + (t - 1) + (t' - 1) := by noncomm_ring
    rw [e, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hform' x,
      Matrix.mulVec_smul, hN, smul_zero, zero_add, hform x]
  have hind : ∀ s r : K, s • u + r • u' = 0 → s = 0 ∧ r = 0 := by
    intro s r h
    by_cases hr : r = 0
    · subst hr
      rw [zero_smul, add_zero] at h
      exact ⟨(smul_eq_zero.mp h).resolve_right hu0, rfl⟩
    · exfalso
      apply hcon (-(s / r))
      have h1 : r • u' = (-s) • u := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_right h
      calc u' = r⁻¹ • (r • u') := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
        _ = r⁻¹ • ((-s) • u) := by rw [h1]
        _ = (-(s / r)) • u := by rw [smul_smul]; congr 1; field_simp
  obtain ⟨x₁, x₂, h11, h12, h21, h22⟩ := exists_pairing hJn hind
  rcases hprod with h1 | h1
  · have h := hprod_form x₁
    rw [h1, sub_self, Matrix.zero_mulVec, h11, h12] at h
    simp only [mul_one, mul_zero, zero_smul, add_zero] at h
    exact (smul_eq_zero.mp h.symm).elim hc0 hu0
  · have h2 := two_le_rank hJn hc0 hc0' hind hprod_form
    rw [h1] at h2
    omega


theorem rank_conj_sub_one (g h : GL ι K) :
    ((((h * g * h⁻¹ : GL ι K) : Matrix ι ι K)) - 1).rank =
      (((g : GL ι K) : Matrix ι ι K) - 1).rank := by
  have hHH : ((h : GL ι K) : Matrix ι ι K) * ((h⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul]
    simp
  have hmat : (((h * g * h⁻¹ : GL ι K) : Matrix ι ι K)) - 1 =
      ((h : GL ι K) : Matrix ι ι K) * (((g : GL ι K) : Matrix ι ι K) - 1) *
        ((h⁻¹ : GL ι K) : Matrix ι ι K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hHH]
    simp
  have hdet : IsUnit ((h : GL ι K) : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  have hdet' : IsUnit ((h⁻¹ : GL ι K) : Matrix ι ι K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  rw [hmat, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]

section Char2

variable [CharP K 2] {m : ℕ}

private theorem neg_one_matrix_eq : (-1 : Matrix (Fin m) (Fin m) K) = 1 := by
  ext i j
  simp [Matrix.one_apply, CharTwo.neg_eq]

private theorem fromBlocks_mul_self :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [neg_one_matrix_eq]

omit [CharP K 2] in
private theorem fromBlocks_alternating (v : Fin m ⊕ Fin m → K) :
    v ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = 0 := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, mul_comm]

private theorem fromBlocks_nondegenerate (x : Fin m ⊕ Fin m → K)
    (hx : ∀ y, x ⬝ᵥ (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y = 0) : x = 0 := by
  set J : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.fromBlocks 0 1 (-1) 0 with hJ
  have h1 : x ᵥ* J = 0 := by
    funext i
    have := hx (Pi.single i 1)
    rw [Matrix.dotProduct_mulVec, dotProduct_single_one] at this
    simpa using this
  calc x = x ᵥ* (J * J) := by rw [fromBlocks_mul_self, Matrix.vecMul_one]
    _ = (x ᵥ* J) ᵥ* J := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

theorem card_le_of_forall_rank_eq_one_statedSp [Finite K] {S : Type} [Group S]
    (ρ : S →* StatedSp m K) (hinj : Function.Injective ρ) (hsq : ∀ s : S, s * s = 1)
    (hrk : ∀ s : S, s ≠ 1 →
      ((((ρ s : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1).rank = 1) :
    Nat.card S ≤ Nat.card K := by
  classical
  set J : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.fromBlocks 0 1 (-1) 0 with hJ
  set M : S → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    fun s => (((ρ s : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hM
  have hMmul : ∀ a b, M (a * b) = M a * M b := fun a b => by simp [hM, map_mul]
  have hM1 : M 1 = 1 := by simp [hM]
  have hiso : ∀ s, (M s)ᵀ * J * M s = J := fun s => StatedAPI.mem_statedSp_iff.1 (ρ s).2
  have hinv : ∀ a : S, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  by_cases hS : ∀ s : S, s = 1
  · have h1 : Nat.card S = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hS a).trans (hS b).symm⟩, ⟨1⟩⟩
    rw [h1]
    exact Nat.card_pos
  push Not at hS
  obtain ⟨s₀, hs₀⟩ := hS
  obtain ⟨u₀, c₀, hu₀, hc₀, hform₀⟩ := exists_transvection_form_of_rank_eq_one (J := J) (t := M s₀)
    fromBlocks_alternating fromBlocks_nondegenerate (hiso s₀) (hrk s₀ hs₀)
  have key : ∀ s : S, ∃ c : K, ∀ x, (M s - 1) *ᵥ x = (c * (u₀ ⬝ᵥ J *ᵥ x)) • u₀ := by
    intro s
    by_cases hs : s = 1
    · exact ⟨0, fun x => by simp [hs, hM1]⟩
    · obtain ⟨u, c, hu, hc, hform⟩ := exists_transvection_form_of_rank_eq_one (J := J) (t := M s)
        fromBlocks_alternating fromBlocks_nondegenerate (hiso s) (hrk s hs)
      obtain ⟨μ, hμ⟩ := exists_eq_smul_of_commute_of_rank_eq_one (J := J) (t := M s₀) (t' := M s)
        fromBlocks_alternating fromBlocks_nondegenerate (hiso s₀) (hiso s) (hrk s hs)
        (by rw [← hMmul, ← hMmul, hcomm s₀ s]) hu₀ hc₀ hc hform₀ hform
        (by
          by_cases h : s₀ * s = 1
          · left
            rw [← hMmul, h, hM1]
          · right
            rw [← hMmul]
            exact hrk _ h)
      refine ⟨c * μ ^ 2, fun x => ?_⟩
      rw [hform x, hμ, smul_dotProduct, smul_smul, smul_eq_mul]
      congr 1
      ring
  choose f hf using key
  have hfinj : Function.Injective f := by
    intro a b hab
    apply hinj
    apply Subtype.ext
    apply Units.ext
    have h : ∀ x, (M a - 1) *ᵥ x = (M b - 1) *ᵥ x := fun x => by rw [hf a x, hf b x, hab]
    have h2 : M a - 1 = M b - 1 := by
      ext i j
      simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i
    exact sub_left_injective h2
  exact Nat.card_le_card_of_injective f hfinj

end Char2

end CFSG.ClassicalGroups.Symplectic
