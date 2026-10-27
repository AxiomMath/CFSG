module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LieType.BorelTits

variable {K : Type} [Field K]

@[expose] def mat (g : StatedSp 2 K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

theorem mat_mul (g h : StatedSp 2 K) : mat (g * h) = mat g * mat h := by
  simp [mat]

theorem mat_one : mat (1 : StatedSp 2 K) = 1 := by
  simp [mat]

theorem mat_eq_of_forall (g h : StatedSp 2 K) (hgh : ∀ v : Fin 2 ⊕ Fin 2 → K, mat g *ᵥ v = mat h *ᵥ v) :
    g = h := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  have := congrFun (hgh (Pi.single b 1)) a
  simpa [mat, Matrix.mulVec_single_one] using this

@[expose] def OnPlane (i : Fin 2) (v : Fin 2 ⊕ Fin 2 → K) : Prop :=
  ∀ k, k ≠ Sum.inl i → k ≠ Sum.inr i → v k = 0

theorem onPlane_add {i : Fin 2} {v w : Fin 2 ⊕ Fin 2 → K} (hv : OnPlane i v) (hw : OnPlane i w) :
    OnPlane i (v + w) := fun k h1 h2 => by simp [hv k h1 h2, hw k h1 h2]

theorem onPlane_smul {i : Fin 2} (c : K) {v : Fin 2 ⊕ Fin 2 → K} (hv : OnPlane i v) :
    OnPlane i (c • v) := fun k h1 h2 => by simp [hv k h1 h2]

theorem onPlane_zero (i : Fin 2) : OnPlane i (0 : Fin 2 ⊕ Fin 2 → K) := fun _ _ _ => rfl

theorem mulVec_pairMat_other {i : Fin 2} (X : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K)
    {k : Fin 2 ⊕ Fin 2} (hk1 : k ≠ Sum.inl i) (hk2 : k ≠ Sum.inr i) :
    (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) k = v k := by
  simp [Matrix.mulVec, dotProduct, pairMat_apply_of_ne hk1 hk2 X, Matrix.one_apply]

theorem mulVec_pairMat_inl (i : Fin 2) (X : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K) :
    (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) (Sum.inl i) =
      X 0 0 * v (Sum.inl i) + X 0 1 * v (Sum.inr i) := by
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pairMat]

theorem mulVec_pairMat_inr (i : Fin 2) (X : Matrix (Fin 2) (Fin 2) K) (v : Fin 2 ⊕ Fin 2 → K) :
    (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) (Sum.inr i) =
      X 1 0 * v (Sum.inl i) + X 1 1 * v (Sum.inr i) := by
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, pairMat]

theorem pairMat_mulVec_onPlane (i : Fin 2) (X : Matrix (Fin 2) (Fin 2) K) {v : Fin 2 ⊕ Fin 2 → K}
    (hv : OnPlane i v) : OnPlane i (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v) := by
  intro k h1 h2
  rw [mulVec_pairMat_other X v h1 h2, hv k h1 h2]

theorem quadratic_of_cube [CharP K 2] {X : Matrix (Fin 2) (Fin 2) K} (hdet : X.det = 1)
    (h3 : X * X * X = 1) (hne : X ≠ 1) : X * X + X + 1 = 0 := by
  have hdet' : X 0 0 * X 1 1 - X 0 1 * X 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  set t : K := X 0 0 + X 1 1 with ht
  have hCH : X * X = t • X - 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, ht] <;>
      first | linear_combination (-1 : K) * hdet' | ring1
  have key : t • (t • X - 1) - X = 1 := by
    have h' : X * X * X = t • (t • X - 1) - X := by
      rw [hCH, sub_mul, smul_mul, one_mul, hCH]
    rw [← h']
    exact h3
  have e00 := congrFun (congrFun key 0) 0
  have e01 := congrFun (congrFun key 0) 1
  have e10 := congrFun (congrFun key 1) 0
  have e11 := congrFun (congrFun key 1) 1
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at e00 e01 e10 e11
  by_cases hcase : t ^ 2 - 1 = 0
  · have ht1 : t = -1 := by
      linear_combination (-1 : K) * e00 + X 0 0 * hcase
    rw [hCH, ht1]
    module
  · exfalso
    apply hne
    have hX01 : X 0 1 = 0 := by
      have : (t ^ 2 - 1) * X 0 1 = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_left hcase
    have hX10 : X 1 0 = 0 := by
      have : (t ^ 2 - 1) * X 1 0 = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_left hcase
    have hX00 : X 0 0 = X 1 1 := by
      have : (t ^ 2 - 1) * (X 0 0 - X 1 1) = 0 := by linear_combination e00 - e11
      have := (mul_eq_zero.1 this).resolve_left hcase
      linear_combination this
    have hsq : X 0 0 * X 0 0 = 1 := by
      rw [hX01, hX10, hX00] at hdet'
      rw [hX00]
      linear_combination hdet'
    have h2c : (2 : K) = 0 := CharTwo.two_eq_zero
    have hc : X 0 0 = 1 := by
      have h2 : (X 0 0 - 1) * (X 0 0 - 1) = 0 := by
        linear_combination hsq + (1 - X 0 0) * h2c
      exact sub_eq_zero.1 (mul_self_eq_zero.1 h2)
    have hc11 : X 1 1 = 1 := hX00 ▸ hc
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hX01, hX10, hc, hc11, Matrix.one_apply]

theorem dot_spJ_single_inl (u : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    u ⬝ᵥ (spJ 2 K *ᵥ Pi.single (Sum.inl i) 1) = -u (Sum.inr i) := by
  rw [dotProduct_spJ_mulVec]
  simp [dotProduct, Function.comp_def, Pi.single_apply]

theorem dot_spJ_single_inr (u : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    u ⬝ᵥ (spJ 2 K *ᵥ Pi.single (Sum.inr i) 1) = u (Sum.inl i) := by
  rw [dotProduct_spJ_mulVec]
  simp [dotProduct, Function.comp_def, Pi.single_apply]

theorem beta_mat (g : StatedSp 2 K) (u w : Fin 2 ⊕ Fin 2 → K) :
    (mat g *ᵥ u) ⬝ᵥ (spJ 2 K *ᵥ (mat g *ᵥ w)) = u ⬝ᵥ (spJ 2 K *ᵥ w) := by
  have hJ : (mat g)ᵀ * spJ 2 K * mat g = spJ 2 K := transpose_mul_mul_of_mem_statedSp g.2
  have hdot : ∀ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (x z : Fin 2 ⊕ Fin 2 → K),
      (A *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (Aᵀ *ᵥ z) := by
    intro A x z
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  have hJ' : (mat g)ᵀ * (spJ 2 K * mat g) = spJ 2 K := by
    rw [← Matrix.mul_assoc]
    exact hJ
  have hmul : (mat g)ᵀ *ᵥ (spJ 2 K *ᵥ (mat g *ᵥ w)) = spJ 2 K *ᵥ w := by
    simp only [Matrix.mulVec_mulVec, hJ']
  rw [hdot, hmul]

theorem onPlane_fst_snd {i j : Fin 2} (hij : i ≠ j) {m : Fin 2} (hm : m ≠ j) : m = i := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> simp_all

theorem onPlane_of_fixes {i j : Fin 2} (hij : i ≠ j) {g : StatedSp 2 K}
    (hfix : ∀ v, OnPlane i v → mat g *ᵥ v = v) {v : Fin 2 ⊕ Fin 2 → K} (hv : OnPlane j v) :
    OnPlane j (mat g *ᵥ v) := by
  have hei : OnPlane i (Pi.single (Sum.inl i) (1 : K)) := by
    intro k h1 _
    simp [Pi.single_apply, h1]
  have hfi : OnPlane i (Pi.single (Sum.inr i) (1 : K)) := by
    intro k _ h2
    simp [Pi.single_apply, h2]
  have he := hfix _ hei
  have hf := hfix _ hfi
  have hvi : v (Sum.inr i) = 0 := hv _ (by simp) (fun h => hij (Sum.inr_injective h))
  have hvi' : v (Sum.inl i) = 0 := hv _ (fun h => hij (Sum.inl_injective h)) (by simp)
  have hb1 := beta_mat g v (Pi.single (Sum.inl i) 1)
  rw [he, dot_spJ_single_inl, dot_spJ_single_inl, hvi] at hb1
  have hb2 := beta_mat g v (Pi.single (Sum.inr i) 1)
  rw [hf, dot_spJ_single_inr, dot_spJ_single_inr, hvi'] at hb2
  have hm1 : (mat g *ᵥ v) (Sum.inr i) = 0 := by simpa using hb1
  have hm2 : (mat g *ᵥ v) (Sum.inl i) = 0 := hb2
  intro k h1 h2
  rcases k with m | m
  · have : m = i := onPlane_fst_snd hij (fun h => h1 (h ▸ rfl))
    subst this
    exact hm2
  · have : m = i := onPlane_fst_snd hij (fun h => h2 (h ▸ rfl))
    subst this
    exact hm1

theorem plane_mem_of_ne_zero (i : Fin 2) {X : Matrix (Fin 2) (Fin 2) K} (hX : X * X + X + 1 = 0)
    (hK : ∀ z : K, z ^ 2 + z + 1 ≠ 0) (C : Submodule K (Fin 2 ⊕ Fin 2 → K))
    (hC : ∀ v ∈ C, pairMat (Sum.inl i) (Sum.inr i) X *ᵥ v ∈ C)
    {u : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ C) (hsupp : OnPlane i u) (hu0 : u ≠ 0) :
    ∀ v, OnPlane i v → v ∈ C := by
  have e00 : X 0 0 * X 0 0 + X 0 1 * X 1 0 + X 0 0 + 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 0) 0
  have e01 : X 0 0 * X 0 1 + X 0 1 * X 1 1 + X 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 0) 1
  have e10 : X 1 0 * X 0 0 + X 1 1 * X 1 0 + X 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 1) 0
  have e11 : X 1 0 * X 0 1 + X 1 1 * X 1 1 + X 1 1 + 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using congrFun (congrFun hX 1) 1
  have hw : u (Sum.inl i) ≠ 0 ∨ u (Sum.inr i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hu0
    funext k
    by_cases h1 : k = Sum.inl i
    · subst h1; exact h.1
    by_cases h2 : k = Sum.inr i
    · subst h2; exact h.2
    exact hsupp k h1 h2
  have hu'C : pairMat (Sum.inl i) (Sum.inr i) X *ᵥ u ∈ C := hC u hu
  have hu'1 := mulVec_pairMat_inl i X u
  have hu'2 := mulVec_pairMat_inr i X u
  have hu'supp : OnPlane i (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ u) := pairMat_mulVec_onPlane i X hsupp
  have hD : u (Sum.inl i) * (X 1 0 * u (Sum.inl i) + X 1 1 * u (Sum.inr i)) -
      u (Sum.inr i) * (X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i)) ≠ 0 := by
    intro hD0
    obtain ⟨lam, hr', hs'⟩ : ∃ lam : K, X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i) =
        lam * u (Sum.inl i) ∧ X 1 0 * u (Sum.inl i) + X 1 1 * u (Sum.inr i) = lam * u (Sum.inr i) := by
      by_cases h0 : u (Sum.inl i) = 0
      · have h1 : u (Sum.inr i) ≠ 0 := hw.resolve_left (not_not.2 h0)
        have hr0 : X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i) = 0 := by
          have : u (Sum.inr i) * (X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i)) = 0 := by
            linear_combination (-1 : K) * hD0 + (X 1 0 * u (Sum.inl i) + X 1 1 * u (Sum.inr i)) * h0
          exact (mul_eq_zero.1 this).resolve_left h1
        refine ⟨(X 1 0 * u (Sum.inl i) + X 1 1 * u (Sum.inr i)) / u (Sum.inr i), ?_, ?_⟩
        · rw [hr0, h0]; ring
        · exact (div_mul_cancel₀ _ h1).symm
      · refine ⟨(X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i)) / u (Sum.inl i), ?_, ?_⟩
        · exact (div_mul_cancel₀ _ h0).symm
        · rw [div_mul_eq_mul_div, eq_div_iff h0]
          linear_combination hD0
    have G0 : (lam ^ 2 + lam + 1) * u (Sum.inl i) = 0 := by
      linear_combination (u (Sum.inl i)) * e00 + (u (Sum.inr i)) * e01 -
        (X 0 0 + 1 + lam) * hr' - X 0 1 * hs'
    have G1 : (lam ^ 2 + lam + 1) * u (Sum.inr i) = 0 := by
      linear_combination (u (Sum.inl i)) * e10 + (u (Sum.inr i)) * e11 -
        (X 1 1 + 1 + lam) * hs' - X 1 0 * hr'
    have hq : lam ^ 2 + lam + 1 = 0 := by
      rcases hw with h | h
      · exact (mul_eq_zero.1 G0).resolve_right h
      · exact (mul_eq_zero.1 G1).resolve_right h
    exact hK lam hq
  intro v hv
  obtain ⟨D, hDdef⟩ : ∃ D : K, D = u (Sum.inl i) * (X 1 0 * u (Sum.inl i) + X 1 1 * u (Sum.inr i)) -
      u (Sum.inr i) * (X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i)) := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hveq : v = ((v (Sum.inl i) * (X 1 0 * u (Sum.inl i) + X 1 1 * u (Sum.inr i)) -
        v (Sum.inr i) * (X 0 0 * u (Sum.inl i) + X 0 1 * u (Sum.inr i))) / D) • u +
      ((u (Sum.inl i) * v (Sum.inr i) - u (Sum.inr i) * v (Sum.inl i)) / D) •
        (pairMat (Sum.inl i) (Sum.inr i) X *ᵥ u) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h1 : k = Sum.inl i
    · subst h1
      rw [hu'1, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD, hDdef]
      ring
    · by_cases h2 : k = Sum.inr i
      · subst h2
        rw [hu'2, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD, hDdef]
        ring
      · rw [hv k h1 h2, hsupp k h1 h2, hu'supp k h1 h2]
        ring
  rw [hveq]
  exact C.add_mem (C.smul_mem _ hu) (C.smul_mem _ hu'C)

theorem exists_fixed_ne {G : Type} [Group G] (hG : IsPGroup 2 G) {X : Type} [MulAction G X]
    [Finite X] (hX : Even (Nat.card X)) (x0 : X) (hx0 : ∀ g : G, g • x0 = x0) :
    ∃ x : X, x ≠ x0 ∧ ∀ g : G, g • x = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hG.card_modEq_card_fixedPoints X
  by_contra hcon
  push Not at hcon
  have hset : MulAction.fixedPoints G X = {x0} := by
    ext x
    constructor
    · intro hx
      by_contra hne
      obtain ⟨g, hg⟩ := hcon x hne
      exact hg (hx g)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hx0
  have hone : Nat.card ↥(MulAction.fixedPoints G X) = 1 := by
    rw [hset]
    simp
  rw [hone] at hmod
  have hev := Nat.even_iff.1 hX
  unfold Nat.ModEq at hmod
  omega

theorem natCard_vec [Finite K] : Nat.card (Fin 2 ⊕ Fin 2 → K) = Nat.card K ^ 4 := by
  rw [Nat.card_fun, Nat.card_sum]
  simp

theorem natCard_onPlane [Finite K] (j : Fin 2) :
    Nat.card {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v} = Nat.card K ^ 2 := by
  let c : Fin 2 → Fin 2 ⊕ Fin 2 := fun m => if m = 0 then Sum.inl j else Sum.inr j
  have hc0 : c 0 = Sum.inl j := by simp [c]
  have hc1 : c 1 = Sum.inr j := by simp [c]
  have hcinj : ∀ m, c m = Sum.inl j ↔ m = 0 := by
    intro m; fin_cases m <;> simp [c]
  let e : {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v} ≃ (Fin 2 → K) :=
    { toFun := fun v m => v.1 (c m)
      invFun := fun w => ⟨fun k => if k = Sum.inl j then w 0 else if k = Sum.inr j then w 1 else 0,
        by
          intro k h1 h2
          simp [h1, h2]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext k
        by_cases h1 : k = Sum.inl j
        · subst h1; simp [hc0]
        · by_cases h2 : k = Sum.inr j
          · subst h2; simp [hc1]
          · simp only [h1, h2, if_false]
            exact (v.2 k h1 h2).symm
      right_inv := by
        intro w
        funext m
        fin_cases m <;> simp [c] }
  rw [Nat.card_congr e, Nat.card_fun]
  simp

abbrev vecMulAction (T : Subgroup (StatedSp 2 K)) : MulAction T (Fin 2 ⊕ Fin 2 → K) where
  smul t v := mat t.1 *ᵥ v
  one_smul v := by
    show mat (1 : StatedSp 2 K) *ᵥ v = v
    rw [mat_one, Matrix.one_mulVec]
  mul_smul t s v := by
    show mat (t.1 * s.1) *ᵥ v = mat t.1 *ᵥ (mat s.1 *ᵥ v)
    rw [mat_mul, Matrix.mulVec_mulVec]

abbrev planeMulAction (T : Subgroup (StatedSp 2 K)) (j : Fin 2)
    (hT : ∀ t ∈ T, ∀ v, OnPlane j v → OnPlane j (mat t *ᵥ v)) :
    MulAction T {v : Fin 2 ⊕ Fin 2 → K // OnPlane j v} where
  smul t v := ⟨mat t.1 *ᵥ v.1, hT t.1 t.2 v.1 v.2⟩
  one_smul v := Subtype.ext (by
    show mat (1 : StatedSp 2 K) *ᵥ v.1 = v.1
    rw [mat_one, Matrix.one_mulVec])
  mul_smul t s v := Subtype.ext (by
    show mat (t.1 * s.1) *ᵥ v.1 = mat t.1 *ᵥ (mat s.1 *ᵥ v.1)
    rw [mat_mul, Matrix.mulVec_mulVec])

@[expose] def fixSub (T : Subgroup (StatedSp 2 K)) : Submodule K (Fin 2 ⊕ Fin 2 → K) where
  carrier := {v | ∀ t ∈ T, mat t *ᵥ v = v}
  add_mem' := by
    intro v w hv hw t ht
    simp [Matrix.mulVec_add, hv t ht, hw t ht]
  zero_mem' := by
    intro t _
    simp
  smul_mem' := by
    intro c v hv t ht
    simp [Matrix.mulVec_smul, hv t ht]

theorem mem_fixSub {T : Subgroup (StatedSp 2 K)} {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ fixSub T ↔ ∀ t ∈ T, mat t *ᵥ v = v := Iff.rfl

theorem mat_eq_one_of_forall {g : StatedSp 2 K} (h : ∀ v : Fin 2 ⊕ Fin 2 → K, mat g *ᵥ v = v) :
    g = 1 := by
  apply mat_eq_of_forall
  intro v
  rw [h v, mat_one, Matrix.one_mulVec]

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PSp4Lin
