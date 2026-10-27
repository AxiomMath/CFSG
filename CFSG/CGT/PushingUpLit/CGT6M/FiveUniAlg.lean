module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open Matrix CFSG.Open

variable {K : Type} [Field K] (fb : K →+* K)

@[expose] def suCj (x : Fin 4 → K) : Fin 4 → K := fun i => fb (x i)

@[expose] def suHh (x y : Fin 4 → K) : K := suCj fb x ⬝ᵥ y

theorem su_cj_smul (c : K) (x : Fin 4 → K) : suCj fb (c • x) = fb c • suCj fb x := by
  funext i; simp [suCj]

theorem su_cj_add (x y : Fin 4 → K) : suCj fb (x + y) = suCj fb x + suCj fb y := by
  funext i; simp [suCj]

theorem su_hh_swap (hfb : ∀ x, fb (fb x) = x) (x y : Fin 4 → K) :
    suHh fb x y = fb (suHh fb y x) := by
  simp only [suHh, suCj, dotProduct, map_sum, map_mul, hfb]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem su_hh_smul_left (c : K) (x y : Fin 4 → K) : suHh fb (c • x) y = fb c * suHh fb x y := by
  simp [suHh, su_cj_smul, smul_dotProduct]

theorem su_hh_smul_right (c : K) (x y : Fin 4 → K) : suHh fb x (c • y) = c * suHh fb x y := by
  simp [suHh, dotProduct_smul]

theorem su_hh_add_left (x y z : Fin 4 → K) : suHh fb (x + y) z = suHh fb x z + suHh fb y z := by
  simp [suHh, su_cj_add, add_dotProduct]

theorem su_hh_add_right (x y z : Fin 4 → K) : suHh fb x (y + z) = suHh fb x y + suHh fb x z := by
  simp [suHh, dotProduct_add]

theorem su_hh_eq_zero_of_forall {x : Fin 4 → K} (h : ∀ y, suHh fb x y = 0) : x = 0 := by
  funext i
  have := h (Pi.single i 1)
  simp only [suHh, suCj, dotProduct_single, mul_one] at this
  have h2 : fb (x i) = 0 := by simpa [dotProduct, Pi.single_apply] using this
  simpa using (map_eq_zero_iff fb (RingHom.injective fb)).mp h2

theorem su_dot_mulVec_left4 (M : Matrix (Fin 4) (Fin 4) K) (y w : Fin 4 → K) :
    (M *ᵥ y) ⬝ᵥ w = y ⬝ᵥ (Mᵀ *ᵥ w) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem su_cj_mulVec (A : Matrix (Fin 4) (Fin 4) K) (x : Fin 4 → K) :
    suCj fb (A *ᵥ x) = (A.map fb) *ᵥ suCj fb x := by
  funext i
  simp [suCj, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem su_hh_mulVec_left (A : Matrix (Fin 4) (Fin 4) K) (x y : Fin 4 → K) :
    suHh fb (A *ᵥ x) y = suHh fb x ((A.map fb)ᵀ *ᵥ y) := by
  rw [suHh, su_cj_mulVec, su_dot_mulVec_left4]
  rfl

theorem su_hh_unitary {U : Matrix (Fin 4) (Fin 4) K} (hU : (U.map fb)ᵀ * U = 1) (x y : Fin 4 → K) :
    suHh fb (U *ᵥ x) (U *ᵥ y) = suHh fb x y := by
  rw [su_hh_mulVec_left, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

theorem su_cj_vecMul_eigen {U : Matrix (Fin 4) (Fin 4) K} (hU : (U.map fb)ᵀ * U = 1) {c ε : K}
    (hUU : U * U = c • 1) {b : Fin 4 → K} (hb : U *ᵥ b = ε • b) :
    suCj fb b ᵥ* U = (fb ε * c) • suCj fb b := by
  have key : ∀ x : Fin 4 → K, (suCj fb b ᵥ* U) ⬝ᵥ x = ((fb ε * c) • suCj fb b) ⬝ᵥ x := by
    intro x
    have h1 : (suCj fb b ᵥ* U) ⬝ᵥ x = suHh fb b (U *ᵥ x) := (Matrix.dotProduct_mulVec _ _ _).symm
    have h3 : U *ᵥ (U *ᵥ x) = c • x := by
      rw [Matrix.mulVec_mulVec, hUU, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : suHh fb b (U *ᵥ x) = suHh fb (U *ᵥ b) (U *ᵥ (U *ᵥ x)) :=
      (su_hh_unitary fb hU b _).symm
    rw [h1, h2, h3, hb, su_hh_smul_left, su_hh_smul_right, smul_dotProduct, smul_eq_mul]
    simp only [suHh]
    ring
  funext i
  have := key (Pi.single i 1)
  simpa [dotProduct_single] using this

theorem su_unitary_of_mem_statedSU {q : ℕ} (hfbq : ∀ x : K, fb x = x ^ q) {A : GL (Fin 4) K}
    (hA : A ∈ StatedSU 4 q K) :
    (((A : Matrix (Fin 4) (Fin 4) K).map fb)ᵀ * (A : Matrix (Fin 4) (Fin 4) K) = 1) ∧
      (A : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have e : (fun x : K => x ^ q) = ⇑fb := funext fun x => (hfbq x).symm
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h1, h2⟩ := hx
    rw [e] at h2
    exact ⟨h2, h1⟩
  | one => simp
  | mul x y _ _ hx hy =>
    refine ⟨?_, by simp [Matrix.det_mul, hx.2, hy.2]⟩
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((y : Matrix (Fin 4) (Fin 4) K).map fb)ᵀ * ((x : Matrix (Fin 4) (Fin 4) K).map fb)ᵀ *
        (↑x * ↑y) = ((y : Matrix (Fin 4) (Fin 4) K).map fb)ᵀ *
          (((x : Matrix (Fin 4) (Fin 4) K).map fb)ᵀ * ↑x) * ↑y := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hx.1, Matrix.mul_one, hy.1]
  | inv x _ hx =>
    refine ⟨?_, by simp [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hx.2]⟩
    set B : Matrix (Fin 4) (Fin 4) K := ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hB
    have h1 : (↑x : Matrix (Fin 4) (Fin 4) K) * B = 1 := Units.mul_inv x
    calc (B.map fb)ᵀ * B = (B.map fb)ᵀ * (((x : Matrix (Fin 4) (Fin 4) K).map fb)ᵀ * ↑x) * B := by
          rw [hx.1, Matrix.mul_one]
      _ = (((x : Matrix (Fin 4) (Fin 4) K) * B).map fb)ᵀ * (↑x * B) := by
          simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1]; simp

@[expose] def suX (a b : Fin 4 → K) (α : K) : Matrix (Fin 4) (Fin 4) K :=
  α • vecMulVec a (suCj fb b) - fb α • vecMulVec b (suCj fb a)

theorem suX_add (a b : Fin 4 → K) (α β : K) : suX fb a b (α + β) = suX fb a b α + suX fb a b β := by
  simp only [suX, map_add, add_smul]
  abel

theorem suX_mul_fixed (a b : Fin 4 → K) {r : K} (hr : fb r = r) (γ : K) :
    suX fb a b (r * γ) = r • suX fb a b γ := by
  simp only [suX, map_mul, hr, mul_smul, smul_sub]

theorem suX_mul (a b : Fin 4 → K) (haa : suHh fb a a = 0) (hab : suHh fb a b = 0)
    (hba : suHh fb b a = 0) (hbb : suHh fb b b = 0) (α β : K) :
    suX fb a b α * suX fb a b β = 0 := by
  simp only [suX, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec]
  simp only [suHh] at haa hab hba hbb
  simp [haa, hab, hba, hbb]

theorem suX_adj (hfb : ∀ x, fb (fb x) = x) (a b : Fin 4 → K) (α : K) :
    ((suX fb a b α).map fb)ᵀ = -suX fb a b α := by
  ext i j
  simp only [suX, suCj, Matrix.transpose_apply, Matrix.map_apply, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, map_sub, map_mul, hfb, Matrix.neg_apply]
  ring

theorem suX_unitary (hfb : ∀ x, fb (fb x) = x) (a b : Fin 4 → K) (haa : suHh fb a a = 0)
    (hab : suHh fb a b = 0) (hba : suHh fb b a = 0) (hbb : suHh fb b b = 0) (γ : K) :
    (((1 : Matrix (Fin 4) (Fin 4) K) + suX fb a b γ).map fb)ᵀ * (1 + suX fb a b γ) = 1 := by
  have hXX := suX_mul fb a b haa hab hba hbb γ γ
  rw [Matrix.map_add fb (map_add fb), Matrix.map_one fb (map_zero fb) (map_one fb),
    Matrix.transpose_add, Matrix.transpose_one, suX_adj fb hfb]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
    hXX]
  abel

theorem su_det_one_add_vecMulVec (u v : Fin 4 → K) : (1 + vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v

theorem su_exists_two_indep_eigen {M : Matrix (Fin 4) (Fin 4) K} (hdet : M.det = 1) {μ : K}
    (hμ : μ ≠ 0) (hμ4 : μ ^ 4 = 1) (h2 : (2 : K) ≠ 0) (hMM : M * M = (μ * μ) • 1)
    (hne : M ≠ μ • 1) :
    ∃ x y : Fin 4 → K, LinearIndependent K ![x, y] ∧ M *ᵥ x = (-μ) • x ∧
      M *ᵥ y = (-μ) • y := by
  by_contra hcon
  push Not at hcon
  have hN : M * (M - μ • 1) = (-μ) • (M - μ • 1) := by
    rw [Matrix.mul_sub, hMM, Matrix.mul_smul, Matrix.mul_one]
    module
  let u : Fin 4 → (Fin 4 → K) := fun k => (M - μ • 1) *ᵥ Pi.single k 1
  have hu : ∀ k, M *ᵥ u k = (-μ) • u k := by
    intro k
    show M *ᵥ ((M - μ • 1) *ᵥ Pi.single k 1) = (-μ) • ((M - μ • 1) *ᵥ Pi.single k 1)
    rw [Matrix.mulVec_mulVec, hN, Matrix.smul_mulVec]
  have hex : ∃ k, u k ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    have h0 : M - μ • 1 = 0 := by
      ext i k
      have := congrFun (h k) i
      simpa [u, Matrix.mulVec_single_one] using this
    exact sub_eq_zero.mp h0
  obtain ⟨k₀, hk₀⟩ := hex
  have hdep : ∀ l, ∃ t : K, u l = t • u k₀ := by
    intro l
    by_contra ht
    push Not at ht
    refine hcon (u k₀) (u l) ?_ (hu k₀) (hu l)
    rw [LinearIndependent.pair_iff]
    intro s t' hst
    have ht' : t' = 0 := by
      by_contra ht0
      apply ht (-(s / t'))
      have : t' • u l = -(s • u k₀) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hst
      calc u l = t'⁻¹ • (t' • u l) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
        _ = -(s / t') • u k₀ := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    rw [ht', zero_smul, add_zero] at hst
    refine ⟨?_, ht'⟩
    by_contra hs0
    exact hk₀ (smul_eq_zero.mp hst |>.resolve_left hs0)
  choose t ht using hdep
  have hM : M = μ • 1 + vecMulVec (u k₀) t := by
    ext i l
    have h1 := congrFun (ht l) i
    have h2' : u l i = M i l - μ * (1 : Matrix (Fin 4) (Fin 4) K) i l := by
      simp [u, Matrix.sub_apply]
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, Pi.smul_apply]
      at h1 ⊢
    rw [h2'] at h1
    linear_combination h1
  have hMa : M *ᵥ u k₀ = (-μ) • u k₀ := hu k₀
  have hdot : μ + t ⬝ᵥ u k₀ = -μ := by
    have e : (μ • 1 + vecMulVec (u k₀) t) *ᵥ u k₀ = (μ + t ⬝ᵥ u k₀) • u k₀ := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
        op_smul_eq_smul, add_smul]
    rw [← hM, hMa] at e
    exact (smul_left_injective K hk₀ e).symm
  have hM' : M = μ • (1 + vecMulVec (μ⁻¹ • u k₀) t) := by
    rw [smul_add, smul_vecMulVec, smul_smul, mul_inv_cancel₀ hμ, one_smul]
    exact hM
  have hdet' : M.det = μ ^ 4 * (1 + μ⁻¹ * (t ⬝ᵥ u k₀)) := by
    rw [hM', Matrix.det_smul, su_det_one_add_vecMulVec, dotProduct_smul, smul_eq_mul]
    simp
  have hneg : μ⁻¹ * (t ⬝ᵥ u k₀) = -2 := by
    have : t ⬝ᵥ u k₀ = -2 * μ := by linear_combination hdot
    rw [this]
    field_simp
  rw [hneg, hμ4] at hdet'
  rw [hdet'] at hdet
  apply h2
  linear_combination (-1 : K) * hdet

theorem su_exists_sixth_pow_eq [Finite K] (hK : Nat.card K = 25) {γ : K} (hγ : γ ≠ 0)
    (hγ4 : γ ^ 4 = 1) : ∃ s : K, s ^ 6 = γ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 24 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 γ hγ))
  have h4 : g ^ (4 * k) = 1 := by
    rw [mul_comm, _root_.zpow_mul, hk]
    apply Units.ext
    simpa using hγ4
  have hdvd : (24 : ℤ) ∣ 4 * k := by
    have h := orderOf_dvd_iff_zpow_eq_one.mpr h4
    rw [hord] at h
    exact_mod_cast h
  obtain ⟨j, hj⟩ : (6 : ℤ) ∣ k := by omega
  refine ⟨((g ^ j : Kˣ) : K), ?_⟩
  have e1 : ((g ^ j : Kˣ) : K) ^ 6 = (((g ^ j) ^ 6 : Kˣ) : K) := by simp
  have e2 : (g ^ j) ^ 6 = g ^ k := by
    rw [← zpow_natCast, ← _root_.zpow_mul, hj]
    congr 1
    push_cast
    ring
  rw [e1, e2, hk]
  rfl

theorem su_exists_isotropic_plane [Finite K] (hK : Nat.card K = 25) (hfb : ∀ x, fb (fb x) = x)
    (hfb5 : ∀ x : K, fb x = x ^ 5) {x₁ x₂ : Fin 4 → K} (hli : LinearIndependent K ![x₁, x₂]) :
    ∃ s₁ s₂ : K, s₁ • x₁ + s₂ • x₂ ≠ 0 ∧
      suHh fb (s₁ • x₁ + s₂ • x₂) (s₁ • x₁ + s₂ • x₂) = 0 := by
  have hli' := LinearIndependent.pair_iff.mp hli
  by_contra hno
  push Not at hno
  have hne : ∀ s₁ s₂ : K, (s₁ ≠ 0 ∨ s₂ ≠ 0) → s₁ • x₁ + s₂ • x₂ ≠ 0 := by
    intro s₁ s₂ hs h0
    have := hli' s₁ s₂ h0
    rcases hs with hs | hs
    · exact hs this.1
    · exact hs this.2
  have ha : suHh fb x₁ x₁ ≠ 0 := by
    have := hno 1 0 (by simpa using hne 1 0 (Or.inl one_ne_zero))
    simpa using this
  set α := suHh fb x₁ x₁ with hα
  have hαfix : fb α = α := (su_hh_swap fb hfb x₁ x₁).symm
  set lam : K := suHh fb x₁ x₂ / α with hlam
  set e₂ : Fin 4 → K := x₂ + (-lam) • x₁ with he₂
  have he₂span : e₂ = (-lam) • x₁ + (1 : K) • x₂ := by rw [he₂, one_smul, add_comm]
  have he₂ne : e₂ ≠ 0 := by rw [he₂span]; exact hne (-lam) 1 (Or.inr one_ne_zero)
  have hx₁e₂ : suHh fb x₁ e₂ = 0 := by
    rw [he₂, su_hh_add_right, su_hh_smul_right, hlam, neg_mul, div_mul_cancel₀ _ ha]
    ring
  have he₂x₁ : suHh fb e₂ x₁ = 0 := by rw [su_hh_swap fb hfb, hx₁e₂, map_zero]
  have hβ : suHh fb e₂ e₂ ≠ 0 := by
    have := hno (-lam) 1 (by rw [← he₂span]; exact he₂ne)
    rwa [← he₂span] at this
  set β := suHh fb e₂ e₂ with hβdef
  have hβfix : fb β = β := (su_hh_swap fb hfb e₂ e₂).symm
  set γ : K := -α / β with hγ
  have hγ0 : γ ≠ 0 := div_ne_zero (neg_ne_zero.mpr ha) hβ
  have hγfix : fb γ = γ := by rw [hγ, map_div₀, map_neg, hαfix, hβfix]
  have hγ4 : γ ^ 4 = 1 := by
    have h5 : γ ^ 5 = γ := by rw [← hfb5, hγfix]
    have : γ * γ ^ 4 = γ * 1 := by rw [← pow_succ', h5, mul_one]
    exact mul_left_cancel₀ hγ0 this
  obtain ⟨s, hs⟩ := su_exists_sixth_pow_eq hK hγ0 hγ4
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hs
    exact hγ0 hs.symm
  have hamem : x₁ + s • e₂ = (1 + s * (-lam)) • x₁ + s • x₂ := by
    rw [he₂, smul_add, smul_smul]
    module
  have hane : x₁ + s • e₂ ≠ 0 := by rw [hamem]; exact hne _ _ (Or.inr hs0)
  have hz := hno (1 + s * (-lam)) s (Or.inr hs0 |> hne _ _)
  rw [← hamem] at hz
  apply hz
  rw [su_hh_add_left, su_hh_add_right, su_hh_add_right, su_hh_smul_left, su_hh_smul_left,
    su_hh_smul_right, su_hh_smul_right, hx₁e₂, he₂x₁, hfb5 s]
  have : s ^ 5 * s = γ := by rw [← pow_succ]; exact hs
  have h1 : suHh fb x₁ x₁ + γ * suHh fb e₂ e₂ = 0 := by
    rw [hγ, div_mul_cancel₀ _ hβ]
    ring
  linear_combination h1 + (suHh fb e₂ e₂) * this

end CFSG.CGT.PushingUpLit.CGT6M
