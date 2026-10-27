module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextUnique

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem t0_congr_add_eq_zero (y y' : ZMod 2) (M : M₃) {i j : Fin 3} (hi : i ≠ 0)
    (hj : j ≠ 0) : (t0Mat y y' * M * (t0Mat y y')ᵀ + M) i j = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  fin_cases i <;> fin_cases j
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hi
  · exact absurd rfl hj
  · simp [Matrix.mul_apply, Fin.sum_univ_three, t0Mat, Matrix.vecMul, dotProduct]
    linear_combination M 1 1 * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three, t0Mat, Matrix.vecMul, dotProduct]
    linear_combination M 1 2 * h2
  · exact absurd rfl hj
  · simp [Matrix.mul_apply, Fin.sum_univ_three, t0Mat, Matrix.vecMul, dotProduct]
    linear_combination M 2 1 * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_three, t0Mat, Matrix.vecMul, dotProduct]
    linear_combination M 2 2 * h2

theorem mem_lagrangianT0_of_comm {g : GL (Fin 3) (ZMod 2)}
    (h1 : g * t0Unit 1 0 = t0Unit 1 0 * g) (h2 : g * t0Unit 0 1 = t0Unit 0 1 * g) :
    g ∈ lagrangianT0 := by
  have e1 : (g : M₃) * t0Mat 1 0 = t0Mat 1 0 * (g : M₃) := by
    have h := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : M₃)) h1
    simpa [coe_t0Unit] using h
  have e2 : (g : M₃) * t0Mat 0 1 = t0Mat 0 1 * (g : M₃) := by
    have h := congrArg (fun x : GL (Fin 3) (ZMod 2) => (x : M₃)) h2
    simpa [coe_t0Unit] using h
  have e := fun i j => congrFun (congrFun e1 i) j
  have f := fun i j => congrFun (congrFun e2 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e21 := e 2 1
  have f01 := f 0 1
  have f02 := f 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, t0Mat] at e00 e01 e02 e21 f01 f02
  have g11 : (g : M₃) 1 1 = (g : M₃) 0 0 := by
    rw [add_comm] at e01
    exact (add_left_cancel e01).symm
  have g22 : (g : M₃) 2 2 = (g : M₃) 0 0 := by
    rw [add_comm] at f02
    exact (add_left_cancel f02).symm
  have hg1 : ((g : M₃) * ((g⁻¹ : GL (Fin 3) (ZMod 2)) : M₃)) 1 1 = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  have hg00 : (g : M₃) 0 0 = 1 := by
    rcases zmod_two_eq_zero_or_eq_one ((g : M₃) 0 0) with h | h
    · simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e02, g11, h] at hg1
    · exact h
  refine mem_lagrangianT0.2 ⟨(g : M₃) 0 1, (g : M₃) 0 2, Units.ext ?_⟩
  rw [coe_t0Unit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t0Mat, e00, e02, e21, f01, g11, g22, hg00]

section Generic

variable {X : Type*} [Group X]

theorem conj_mem_of_unique [Finite X] {B P I : Subgroup X} (hPB : P ≤ B)
    (hPsq : ∀ p ∈ P, p ^ 2 = 1)
    (huniq : ∀ Y : Subgroup X, Y ≤ B → Nat.card Y = Nat.card P → (∀ y ∈ Y, y ^ 2 ∈ I) → Y = P)
    {m : X} (hm : m ∈ normalizer (B : Set X)) {p : X} (hp : p ∈ P) : m * p * m⁻¹ ∈ P := by
  have hY : P.map (MulAut.conj m).toMonoidHom = P := by
    refine huniq _ ?_ (card_map_of_injective (MulAut.conj m).injective) ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact (mem_normalizer_iff.1 hm q).1 (hPB hq)
    · rintro _ ⟨q, hq, rfl⟩
      have h : (MulAut.conj m).toMonoidHom q ^ 2 = 1 := by
        rw [← map_pow, hPsq q hq, map_one]
      rw [h]
      exact one_mem _
  rw [← hY]
  exact ⟨p, hp, rfl⟩

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

include he in
theorem inr_mem_pairOrth {j : Fin 3} (hj : j ≠ 0) : e (Sum.inr j) ∈ 𝔼 := by
  rw [mem_pairOrth, bilin_inl he, bilin_inr he]
  simp [Basis.repr_self, hj]

section Sigma

variable (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
  (hσ : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (a : G) (ha : a ∈ L) (B : M₃),
    Bᵀ = B →
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
  (hσcol : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (hn : (n : G) ∈ L) (j : Fin 3),
    linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i))
  (hσker : σ.ker = (radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G)))

include he hnd hzC hsup hz hσcol in
theorem exists_ptA_sigma_eq (y y' : ZMod 2) :
    ∃ a ∈ 𝒜₁, ∃ h : a ∈ 𝒩₂₀, σ ⟨a, h⟩ = t0Unit y y' := by
  have hw : y • e (Sum.inr 1) + y' • e (Sum.inr 2) ∈ 𝔼 :=
    add_mem (Submodule.smul_mem _ _ (inr_mem_pairOrth he (by decide)))
      (Submodule.smul_mem _ _ (inr_mem_pairOrth he (by decide)))
  have haA : ((φ.symm (pointElt hb (mem_pairOrth_left hw) 0) : L) : G) ∈ 𝒜₁ :=
    mem_pullSub.2 ⟨(φ.symm _).2, by
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      exact pointElt_mem_pointRadical hb hw 0⟩
  have haN : ((φ.symm (pointElt hb (mem_pairOrth_left hw) 0) : L) : G) ∈ 𝒩₂₀ := by
    have h := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz (inv_mem haA)
    rwa [inv_inv] at h
  refine ⟨_, haA, haN, ?_⟩
  rw [sigma_eq_t0Unit he hb φ σ hσcol ⟨_, haN⟩ hw 0 rfl]
  simp [Basis.repr_self]

include he hσ in
theorem nu_conj_sigma {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (n : 𝒩₂₀) {d : G} (hd : d ∈ D₂) (hnd : (n : G) * d * (n : G)⁻¹ ∈ D₂) :
    ν₂ ((n : G) * d * (n : G)⁻¹) = symThreeCongr (σ n) (ν₂ d) := by
  have h1 := tauHom_nu he φ hzC hz hν₂z hnd
  have hnz : (n : G) * z = z * (n : G) := mem_centralizer_singleton_iff.1 (mem_inf.1 n.2).2
  have h2 := gamma_conj (z := z) (x := d) hnz
  have h3 : z⁻¹ * (((n : G) * d * (n : G)⁻¹)⁻¹ * z * ((n : G) * d * (n : G)⁻¹)) =
      (n : G) * tauHom φ he (Multiplicative.ofAdd (ν₂ d)) * (n : G)⁻¹ := by
    calc z⁻¹ * (((n : G) * d * (n : G)⁻¹)⁻¹ * z * ((n : G) * d * (n : G)⁻¹)) =
        z⁻¹ * ((n : G) * d * (n : G)⁻¹)⁻¹ * z * ((n : G) * d * (n : G)⁻¹) := by group
      _ = (n : G) * (z⁻¹ * d⁻¹ * z * d) * (n : G)⁻¹ := h2
      _ = (n : G) * (z⁻¹ * (d⁻¹ * z * d)) * (n : G)⁻¹ := by group
      _ = _ := by rw [tauHom_nu he φ hzC hz hν₂z hd]
  rw [h3, conj_tauHom_of_sigma φ he σ hσ n] at h1
  exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1)

end Sigma

section Kernel

variable (σ : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
    centralizer (Singleton.singleton z : Set G) : Subgroup G) →* GL (Fin 3) (ZMod 2))
  (hσ : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (a : G) (ha : a ∈ L) (B : M₃),
    Bᵀ = B →
    LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 B 0 1 →
    ∃ h : (n : G) * a * (n : G)⁻¹ ∈ L,
      LinearMap.toMatrix e e (linOf (φ ⟨(n : G) * a * (n : G)⁻¹, h⟩)) =
        fromBlocks 1 ((σ n : M₃) * B * (σ n : M₃)ᵀ) 0 1)
  (hσcol : ∀ (n : (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G) : Subgroup G)) (hn : (n : G) ∈ L) (j : Fin 3),
    linOf (φ ⟨n, hn⟩) (e (Sum.inl j)) = ∑ i, (σ n : M₃) i j • e (Sum.inl i))
  (hσker : σ.ker = (radSub φ z e).subgroupOf (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
      centralizer (Singleton.singleton z : Set G)))

include he hnd hzC hsup hz hσ hσcol hσker in
theorem degree64_next_kernel [Finite G] {C₁ D₂ C₂ K₀ P B : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) (hRD₂ : ℛ ≤ D₂)
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂A : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d)
    (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (hC₂D : C₂ ≤ D₂) (hC₂n : ∀ m ∈ 𝒩₂, ∀ c ∈ C₂, m * c * m⁻¹ ∈ C₂)
    (hC₂R : C₂ ⊓ ℛ = 𝒜₂) (hC₂sq : ∀ c ∈ C₂, c ^ 2 = 1) (hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂)
    (hDzC : (D₂ : Set G) = (zpowers z : Set G) * (C₂ : Set G))
    (hνmul : ∀ c ∈ C₂, ∀ c' ∈ C₂, ν₂ (c * c') = ν₂ c + ν₂ c')
    (hνk : ∀ c ∈ C₂, ν₂ c = 0 ↔ c ∈ 𝒜₂)
    (hK₀ : K₀ = C₁ ⊓ D₂) (hP : P = 𝒜₂ ⊔ K₀) (hB : B = zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ K₀)
    (hPcard : Nat.card P = 512) (hBNP : B ≤ normalizer (P : Set G))
    (hBB : ∀ x ∈ B, ∀ y ∈ B, x⁻¹ * y⁻¹ * x * y ∈ 𝒜₁ ⊓ 𝒜₂)
    (hJB : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∀ x ∈ B, j * x = x * j)
    (hK₀J : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ K₀, z⁻¹ * (k⁻¹ * z * k) = j)
    (hNP : ∀ m ∈ normalizer (B : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G),
      ∀ p ∈ P, m * p * m⁻¹ ∈ P) :
    (∀ m : G, (m ∈ normalizer (B : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G) ∧
      ∀ x ∈ B, m * x * m⁻¹ * x⁻¹ ∈ P) ↔ m ∈ 𝒜₁ ⊔ D₂) ∧
    (𝒜₁ ⊔ D₂) ⊓ centralizer (P : Set G) = C₂ ∧
    normalizer (B : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G) ≤
      normalizer (C₂ : Set G) := by
  classical
  set N := normalizer (B : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G) with hNdef
  have hzR : z ∈ ℛ := mem_sup_right (mem_zpowers z)
  have hzD₂ : z ∈ D₂ := hRD₂ hzR
  have hzB : z ∈ B := by
    rw [hB]
    exact mem_sup_left (mem_sup_left (mem_sup_left (mem_zpowers z)))
  have hA₁B : 𝒜₁ ≤ B := by
    rw [hB]
    exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hA₂B : 𝒜₂ ≤ B := by
    rw [hB]
    exact le_sup_right.trans le_sup_left
  have hK₀B : K₀ ≤ B := by
    rw [hB]
    exact le_sup_right
  have hA₂P : 𝒜₂ ≤ P := by
    rw [hP]
    exact le_sup_left
  have hK₀P : K₀ ≤ P := by
    rw [hP]
    exact le_sup_right
  have hPB : P ≤ B := by
    rw [hP]
    exact sup_le hA₂B hK₀B
  have hK₀C₂ : K₀ ≤ C₂ := by
    intro k hk
    rw [hK₀, ← hC₁C₂] at hk
    exact (mem_inf.1 hk).2
  have hA₂C₂ : 𝒜₂ ≤ C₂ := radA_le_of_inf_eq φ hC₂R
  have hPC₂ : P ≤ C₂ := by
    rw [hP]
    exact sup_le hA₂C₂ hK₀C₂
  have hAL : 𝒜₁ ≤ L := pullSub_le φ _
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hC₂c : ∀ x ∈ C₂, ∀ y ∈ C₂, x * y = y * x := fun x hx y hy =>
    comm_of_sq_eq_one hC₂sq hx hy
  have hIJ : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ ⊓ 𝒜₂ := zpowers_ptB₁_le he hb φ hzC hz
  have hJP : 𝒜₁ ⊓ 𝒜₂ ≤ P := inf_le_right.trans hA₂P
  have hb₁B : ptB₁ he hb φ hzC hz ∈ B := hPB (hJP (hIJ (mem_zpowers _)))
  have hA₁N₂ : ∀ a ∈ 𝒜₁, a ∈ 𝒩₂ := fun a ha =>
    ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left ha)
  have hzN₂ : z ∈ 𝒩₂ := le_normalizer hzR
  have hz1 : z * z = 1 := z_mul_self hz
  have hC₂z : ∀ c ∈ C₂, c * z = z * c → c ∈ 𝒜₂ := fun c hc hcz => by
    have h : c ∈ C₂ ⊓ ℛ := by
      refine mem_inf.2 ⟨hc, ?_⟩
      rw [← hD₂H]
      exact mem_inf.2 ⟨hC₂D hc, mem_centralizer_singleton_iff.2 hcz⟩
    rw [hC₂R] at h
    exact h
  have hν1 : ν₂ 1 = 0 := by
    have h := hνmul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    exact (add_eq_left.1 h.symm)
  have hνP : ∀ c ∈ C₂, (∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → (ν₂ c : M₃) i j = 0) → c ∈ P := by
    intro c hc hsupp
    have hM := eq_jMat_iff.1 ⟨(ν₂ c).2, hsupp⟩
    have hτJ : tauHom φ he (Multiplicative.ofAdd (ν₂ c)) ∈ 𝒜₁ ⊓ 𝒜₂ := by
      refine (mem_ptA_inf_radA_iff he hb φ).2 ⟨(ν₂ c : M₃) 0 0, (ν₂ c : M₃) 0 1,
        (ν₂ c : M₃) 0 2, ?_⟩
      congr 2
      exact Subtype.ext hM.symm
    obtain ⟨k, hk, hkz⟩ := hK₀J _ hτJ
    have hkν : ν₂ k = ν₂ c := by
      rw [← tauHom_nu he φ hzC hz hν₂z (hC₂D (hK₀C₂ hk))] at hkz
      exact Multiplicative.ofAdd.injective (tauHom_injective φ he hkz)
    have hkinv : ν₂ k⁻¹ = ν₂ k := by
      have h := hνmul k (hK₀C₂ hk) k⁻¹ (inv_mem (hK₀C₂ hk))
      rw [mul_inv_cancel, hν1] at h
      rw [← neg_eq_of_add_eq_zero_right h.symm]
      exact neg_eq_of_add_eq_zero_left (symThree_add_self _)
    have h0 : ν₂ (k⁻¹ * c) = 0 := by
      rw [hνmul _ (inv_mem (hK₀C₂ hk)) c hc, hkinv, hkν, symThree_add_self]
    have hA := (hνk _ (mul_mem (inv_mem (hK₀C₂ hk)) hc)).1 h0
    have h1 : c = k * (k⁻¹ * c) := by group
    rw [h1]
    exact mul_mem (hK₀P hk) (hA₂P hA)
  have hBN : B ≤ N := fun x hx => mem_inf.2 ⟨mem_normalizer_of_conj_mem fun y hy =>
    mul_mem (mul_mem hx hy) (inv_mem hx),
    mem_centralizer_singleton_iff.2 (hJB _ (hIJ (mem_zpowers _)) x hx).symm⟩
  have hNB : ∀ m ∈ N, ∀ x ∈ B, m * x * m⁻¹ ∈ B := fun m hm x hx =>
    (mem_normalizer_iff.1 (mem_inf.1 hm).1 x).1 hx
  have hNB' : ∀ m ∈ N, ∀ x ∈ B, m⁻¹ * x * m ∈ B := fun m hm x hx => by
    have h := hNB m⁻¹ (inv_mem hm) x hx
    rwa [inv_inv] at h
  let Kr : Subgroup G :=
    { carrier := {m | m ∈ N ∧ ∀ x ∈ B, m * x * m⁻¹ * x⁻¹ ∈ P}
      one_mem' := ⟨one_mem _, fun x _ => by
        rw [show (1 : G) * x * 1⁻¹ * x⁻¹ = 1 by group]
        exact one_mem _⟩
      mul_mem' := by
        rintro m m' ⟨hm, hmK⟩ ⟨hm', hm'K⟩
        refine ⟨mul_mem hm hm', fun x hx => ?_⟩
        have he' : m * m' * x * (m * m')⁻¹ * x⁻¹ =
            (m * (m' * x * m'⁻¹ * x⁻¹) * m⁻¹) * (m * x * m⁻¹ * x⁻¹) := by group
        rw [he']
        exact mul_mem (hNP m hm _ (hm'K x hx)) (hmK x hx)
      inv_mem' := by
        rintro m ⟨hm, hmK⟩
        refine ⟨inv_mem hm, fun x hx => ?_⟩
        have h := hmK _ (hNB' m hm x hx)
        have he' : m⁻¹ * x * m⁻¹⁻¹ * x⁻¹ = (m * (m⁻¹ * x * m) * m⁻¹ * (m⁻¹ * x * m)⁻¹)⁻¹ := by
          group
        rw [he']
        exact inv_mem h }
  have hmemKr : ∀ m, m ∈ Kr ↔ m ∈ N ∧ ∀ x ∈ B, m * x * m⁻¹ * x⁻¹ ∈ P := fun m => Iff.rfl
  have hBKr : B ≤ Kr := fun x hx => ⟨hBN hx, fun y hy => by
    have h := hBB x⁻¹ (inv_mem hx) y⁻¹ (inv_mem hy)
    rw [inv_inv, inv_inv] at h
    exact hJP h⟩
  have hC₂Kr : C₂ ≤ Kr := by
    intro c hc
    have hT : ∀ x ∈ B, c * x * c⁻¹ * x⁻¹ ∈ P := by
      let T : Subgroup G :=
        { carrier := {x | x ∈ B ∧ c * x * c⁻¹ * x⁻¹ ∈ P}
          one_mem' := ⟨one_mem _, by
            rw [show c * 1 * c⁻¹ * (1 : G)⁻¹ = 1 by group]
            exact one_mem _⟩
          mul_mem' := by
            rintro x y ⟨hx, h⟩ ⟨hy, h'⟩
            refine ⟨mul_mem hx hy, ?_⟩
            have he' : c * (x * y) * c⁻¹ * (x * y)⁻¹ =
                (c * x * c⁻¹ * x⁻¹) * (x * (c * y * c⁻¹ * y⁻¹) * x⁻¹) := by group
            rw [he']
            exact mul_mem h ((mem_normalizer_iff.1 (hBNP hx) _).1 h')
          inv_mem' := by
            rintro x ⟨hx, h⟩
            refine ⟨inv_mem hx, ?_⟩
            have he' : c * x⁻¹ * c⁻¹ * x⁻¹⁻¹ = x⁻¹ * (c * x * c⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
            rw [he']
            exact (mem_normalizer_iff.1 (hBNP (inv_mem hx)) _).1 (inv_mem h) }
      have hBT : B ≤ T := by
        rw [hB]
        refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
        · rw [zpowers_le]
          refine ⟨hzB, ?_⟩
          have hγ : z⁻¹ * (c⁻¹⁻¹ * z * c⁻¹) ∈ 𝒜₂ := by
            rw [← tauHom_nu he φ hzC hz hν₂z (inv_mem (hC₂D hc))]
            exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
          rw [inv_inv] at hγ
          have h1 : c * z * c⁻¹ * z⁻¹ = z * (z⁻¹ * (c * z * c⁻¹)) * z⁻¹ := by group
          have h2 : z * (z⁻¹ * (c * z * c⁻¹)) * z⁻¹ = z⁻¹ * (c * z * c⁻¹) := by
            rw [mul_inv_eq_iff_eq_mul, hzL _ (hA₂L hγ)]
          rw [h1, h2]
          exact hA₂P hγ
        · intro a ha
          refine ⟨hA₁B ha, ?_⟩
          have haN := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz ha
          obtain ⟨y, y', hyy⟩ := mem_lagrangianT0.1
            (sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol ⟨a⁻¹, haN⟩ (inv_mem ha))
          have hdC : a⁻¹ * c * a⁻¹⁻¹ ∈ C₂ := hC₂n _ (mem_inf.1 haN).1 c hc
          have hdν := nu_conj_sigma he φ hzC hz σ hσ hν₂z ⟨a⁻¹, haN⟩ (hC₂D hc) (hC₂D hdC)
          rw [hyy] at hdν
          rw [inv_inv] at hdC hdν
          have hcinv : ν₂ c⁻¹ = ν₂ c := by
            have h := hνmul c hc c⁻¹ (inv_mem hc)
            rw [mul_inv_cancel, hν1] at h
            rw [← neg_eq_of_add_eq_zero_right h.symm]
            exact neg_eq_of_add_eq_zero_left (symThree_add_self _)
          have hdc : a⁻¹ * c * a * c⁻¹ ∈ P := by
            refine hνP _ (mul_mem hdC (inv_mem hc)) fun i j hi hj => ?_
            rw [hνmul _ hdC _ (inv_mem hc), hdν, hcinv]
            change (t0Mat y y' * (ν₂ c : M₃) * (t0Mat y y')ᵀ + (ν₂ c : M₃)) i j = 0
            exact t0_congr_add_eq_zero y y' _ hi hj
          have h1 : c * a * c⁻¹ * a⁻¹ = a * (a⁻¹ * c * a * c⁻¹)⁻¹⁻¹ * a⁻¹ := by group
          rw [h1, inv_inv]
          exact (mem_normalizer_iff.1 (hBNP (hA₁B ha)) _).1 hdc
        · intro x hx
          refine ⟨hA₂B hx, ?_⟩
          rw [show c * x * c⁻¹ * x⁻¹ = 1 by
            rw [hC₂c c hc x (hA₂C₂ hx)]
            group]
          exact one_mem _
        · intro x hx
          refine ⟨hK₀B hx, ?_⟩
          rw [show c * x * c⁻¹ * x⁻¹ = 1 by
            rw [hC₂c c hc x (hK₀C₂ hx)]
            group]
          exact one_mem _
      exact fun x hx => (hBT hx).2
    refine ⟨mem_inf.2 ⟨mem_normalizer_of_conj_mem fun x hx => ?_, ?_⟩, hT⟩
    · have h1 : c * x * c⁻¹ = (c * x * c⁻¹ * x⁻¹) * x := by group
      rw [h1]
      exact mul_mem (hPB (hT x hx)) hx
    · exact mem_centralizer_singleton_iff.2
        (hC₂c c hc _ (hA₂C₂ (mem_inf.1 (hIJ (mem_zpowers _))).2))
  have hD₂Kr : D₂ ≤ Kr := fun d hd => by
    have hd' : d ∈ (zpowers z : Set G) * (C₂ : Set G) := by
      rw [← hDzC]
      exact hd
    obtain ⟨t, ht, c, hc, rfl⟩ := hd'
    exact mul_mem (hBKr ((zpowers_le.2 hzB) ht)) (hC₂Kr hc)
  have hA₁D₂Kr : 𝒜₁ ⊔ D₂ ≤ Kr := sup_le (hA₁B.trans hBKr) hD₂Kr
  have hKrA₁D₂ : Kr ≤ 𝒜₁ ⊔ D₂ := by
    rintro m ⟨hmN, hmK⟩
    have hp := hmK z hzB
    have hpz : m * z * m⁻¹ = (m * z * m⁻¹ * z⁻¹) * z := by group
    have hpc : (m * z * m⁻¹ * z⁻¹) * z = z * (m * z * m⁻¹ * z⁻¹) := by
      have hp2 : (m * z * m⁻¹ * z⁻¹)⁻¹ = m * z * m⁻¹ * z⁻¹ :=
        inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hC₂sq _ (hPC₂ hp))
      have h3 : (m * z * m⁻¹ * z⁻¹) * z * ((m * z * m⁻¹ * z⁻¹) * z) = 1 := by
        rw [← hpz]
        calc m * z * m⁻¹ * (m * z * m⁻¹) = m * (z * z) * m⁻¹ := by group
          _ = 1 := by rw [hz1]; group
      have h4 : z * (m * z * m⁻¹ * z⁻¹) * z = m * z * m⁻¹ * z⁻¹ := by
        calc z * (m * z * m⁻¹ * z⁻¹) * z =
            (m * z * m⁻¹ * z⁻¹)⁻¹ * ((m * z * m⁻¹ * z⁻¹) * z * ((m * z * m⁻¹ * z⁻¹) * z)) := by
              group
          _ = m * z * m⁻¹ * z⁻¹ := by rw [h3, mul_one, hp2]
      have h5 : z * (m * z * m⁻¹ * z⁻¹) * z * z = z * (m * z * m⁻¹ * z⁻¹) := by
        rw [mul_assoc, hz1, mul_one]
      rw [h4] at h5
      exact h5
    have hpA : m * z * m⁻¹ * z⁻¹ ∈ 𝒜₂ := hC₂z _ (hPC₂ hp) hpc
    have hmA : ∀ a ∈ 𝒜₂, m * a * m⁻¹ ∈ 𝒜₂ := by
      intro a ha
      have hmaP := hNP m hmN a (hA₂P ha)
      have hc1 : (m * a * m⁻¹) * (m * z * m⁻¹) = (m * z * m⁻¹) * (m * a * m⁻¹) := by
        calc (m * a * m⁻¹) * (m * z * m⁻¹) = m * (a * z) * m⁻¹ := by group
          _ = m * (z * a) * m⁻¹ := by rw [hzL a (hA₂L ha)]
          _ = (m * z * m⁻¹) * (m * a * m⁻¹) := by group
      rw [hpz] at hc1
      have hc2 : (m * a * m⁻¹) * (m * z * m⁻¹ * z⁻¹) = (m * z * m⁻¹ * z⁻¹) * (m * a * m⁻¹) :=
        hC₂c _ (hPC₂ hmaP) _ (hPC₂ hp)
      refine hC₂z _ (hPC₂ hmaP) ?_
      have h1 : (m * z * m⁻¹ * z⁻¹) * ((m * a * m⁻¹) * z) =
          (m * z * m⁻¹ * z⁻¹) * (z * (m * a * m⁻¹)) := by
        calc (m * z * m⁻¹ * z⁻¹) * ((m * a * m⁻¹) * z) =
            ((m * z * m⁻¹ * z⁻¹) * (m * a * m⁻¹)) * z := by group
          _ = ((m * a * m⁻¹) * (m * z * m⁻¹ * z⁻¹)) * z := by rw [hc2]
          _ = (m * a * m⁻¹) * ((m * z * m⁻¹ * z⁻¹) * z) := by group
          _ = ((m * z * m⁻¹ * z⁻¹) * z) * (m * a * m⁻¹) := hc1
          _ = (m * z * m⁻¹ * z⁻¹) * (z * (m * a * m⁻¹)) := by group
      exact mul_left_cancel h1
    have hmN₂ : m ∈ 𝒩₂ := by
      refine mem_normalizer_of_conj_mem fun r hr => ?_
      refine (sup_le (fun a ha => ?_) ?_ :
        ℛ ≤ Subgroup.comap (MulAut.conj m).toMonoidHom ℛ) hr
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left (hmA a ha)
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hpz]
        exact mul_mem (mem_sup_left hpA) (mem_sup_right (mem_zpowers z))
    obtain ⟨d, hd, n, hn, rfl⟩ := hprod₂ m hmN₂
    have hnKr : n ∈ Kr := by
      have h := mul_mem (hD₂Kr (inv_mem hd)) (show d * n ∈ Kr from ⟨hmN, hmK⟩)
      rwa [inv_mul_cancel_left] at h
    obtain ⟨hnN, hnK⟩ := hnKr
    have hcomm : ∀ a ∈ 𝒜₁, ∀ ha : a ∈ 𝒩₂₀, σ ⟨n, hn⟩ * σ ⟨a, ha⟩ = σ ⟨a, ha⟩ * σ ⟨n, hn⟩ := by
      intro a ha haN
      have hc := hnK a (hA₁B ha)
      set c : 𝒩₂₀ := ⟨n, hn⟩ * ⟨a, haN⟩ * ⟨n, hn⟩⁻¹ * ⟨a, haN⟩⁻¹ with hcdef
      have hcG : (c : G) = n * a * n⁻¹ * a⁻¹ := rfl
      have hcz : (c : G) * z = z * (c : G) := mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2
      have hcA : (c : G) ∈ 𝒜₂ := by
        rw [hcG] at hcz ⊢
        exact hC₂z _ (hPC₂ hc) hcz
      have hσc : σ c = 1 := sigma_eq_one_of_mem φ σ hσker c (mem_sup_left hcA)
      rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv] at hσc
      calc σ ⟨n, hn⟩ * σ ⟨a, haN⟩ =
          σ ⟨n, hn⟩ * σ ⟨a, haN⟩ * (σ ⟨n, hn⟩)⁻¹ * (σ ⟨a, haN⟩)⁻¹ * (σ ⟨a, haN⟩ * σ ⟨n, hn⟩) := by
            group
        _ = σ ⟨a, haN⟩ * σ ⟨n, hn⟩ := by rw [hσc, one_mul]
    obtain ⟨a₁, ha₁, ha₁N, hσa₁⟩ := exists_ptA_sigma_eq he hb hnd φ hzC hsup hz σ hσcol 1 0
    obtain ⟨a₂, ha₂, ha₂N, hσa₂⟩ := exists_ptA_sigma_eq he hb hnd φ hzC hsup hz σ hσcol 0 1
    have h1 := hcomm a₁ ha₁ ha₁N
    have h2 := hcomm a₂ ha₂ ha₂N
    rw [hσa₁] at h1
    rw [hσa₂] at h2
    obtain ⟨y, y', hyy⟩ := mem_lagrangianT0.1 (mem_lagrangianT0_of_comm h1 h2)
    obtain ⟨a, ha, haN, hσa⟩ := exists_ptA_sigma_eq he hb hnd φ hzC hsup hz σ hσcol y y'
    have hker : (⟨n, hn⟩ * ⟨a, haN⟩⁻¹ : 𝒩₂₀) ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyy, hσa, mul_inv_cancel]
    rw [hσker, mem_subgroupOf] at hker
    have hna : n * a⁻¹ ∈ D₂ := hRD₂ hker
    have h3 : d * n = (d * (n * a⁻¹)) * a := by group
    rw [h3]
    exact mul_mem (mem_sup_right (mul_mem hd hna)) (mem_sup_left ha)
  have hKreq : ∀ m, (m ∈ N ∧ ∀ x ∈ B, m * x * m⁻¹ * x⁻¹ ∈ P) ↔ m ∈ 𝒜₁ ⊔ D₂ := fun m =>
    ⟨fun h => hKrA₁D₂ h, fun h => hA₁D₂Kr h⟩
  have hA₁ND₂ : 𝒜₁ ≤ normalizer (D₂ : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun d hd => hD₂n a (hA₁N₂ a ha) d hd
  have hcen : (𝒜₁ ⊔ D₂) ⊓ centralizer (P : Set G) = C₂ := by
    apply le_antisymm
    · intro m hm
      obtain ⟨hmAD, hmP⟩ := mem_inf.1 hm
      have hm' : m ∈ ((𝒜₁ ⊔ D₂ : Subgroup G) : Set G) := hmAD
      rw [coe_mul_of_left_le_normalizer_right _ _ hA₁ND₂] at hm'
      obtain ⟨a, ha, d, hd, rfl⟩ := hm'
      change a * d ∈ C₂
      change a * d ∈ centralizer (P : Set G) at hmP
      have haA₂ : ∀ x ∈ 𝒜₂, a * x * a⁻¹ = x := by
        intro x hx
        have h1 : (a * d) * x = x * (a * d) := (mem_centralizer_iff.1 hmP x (hA₂P hx)).symm
        have h2 : d * x = x * d := hD₂A d hd x hx
        have h3 : a * x = x * a := by
          calc a * x = a * d * x * d⁻¹ := by rw [mul_assoc a d x, h2]; group
            _ = x * (a * d) * d⁻¹ := by rw [h1]
            _ = x * a := by group
        rw [h3, mul_inv_cancel_right]
      have haN : a ∈ 𝒩₂₀ := by
        have h := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz (inv_mem ha)
        rwa [inv_inv] at h
      obtain ⟨y, y', hyy⟩ := mem_lagrangianT0.1
        (sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol ⟨a, haN⟩ ha)
      have hfix : ∀ M : ↥(binarySymMatrices 3), symThreeCongr (t0Unit y y') M = M := by
        intro M
        have h := conj_tauHom_of_sigma φ he σ hσ ⟨a, haN⟩ M
        rw [hyy] at h
        change a * tauHom φ he (Multiplicative.ofAdd M) * a⁻¹ = _ at h
        rw [haA₂ _ ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩)] at h
        exact (Multiplicative.ofAdd.injective (tauHom_injective φ he h)).symm
      have hdiag : ∀ M : ↥(binarySymMatrices 3), symThreeDiag (t0Mat y y' * (M : M₃) *
          (t0Mat y y')ᵀ + (M : M₃)) = 0 := by
        intro M
        have h := congrArg (fun X : ↥(binarySymMatrices 3) => (X : M₃)) (hfix M)
        change (t0Unit y y' : M₃) * (M : M₃) * (t0Unit y y' : M₃)ᵀ = (M : M₃) at h
        rw [coe_t0Unit] at h
        rw [h]
        funext i
        exact zmod_two_add_self_eq_zero _
      obtain ⟨hy, hy'⟩ := zmod_two_t0_diag y y' (hdiag symE₂₂) (hdiag symE₃₃)
      subst hy hy'
      have hσ1 : σ ⟨a, haN⟩ = 1 := by
        rw [hyy]
        exact Units.ext t0Mat_zero
      have haR : a ∈ ℛ := by
        have h : (⟨a, haN⟩ : 𝒩₂₀) ∈ σ.ker := hσ1
        rw [hσker, mem_subgroupOf] at h
        exact h
      have hmD : a * d ∈ (zpowers z : Set G) * (C₂ : Set G) := by
        rw [← hDzC]
        exact mul_mem (hRD₂ haR) hd
      obtain ⟨t, ht, c, hc, htc⟩ := hmD
      change t * c = a * d at htc
      rcases eq_one_or_eq_of_mem_zpowers hz ht with h | h
      · rw [← htc, h, one_mul]
        exact hc
      · exfalso
        rw [h] at htc
        have hzP : ∀ p ∈ P, p * z = z * p := by
          intro p hp
          have hz' : z = (a * d) * c⁻¹ := by rw [← htc]; group
          have h1 : (a * d) * p = p * (a * d) := (mem_centralizer_iff.1 hmP p hp).symm
          have h2 : c * p = p * c := hC₂c c hc p (hPC₂ hp)
          have h3 : c⁻¹ * p = p * c⁻¹ := by
            rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h2, mul_inv_cancel_right]
          rw [hz']
          calc p * (a * d * c⁻¹) = (a * d) * p * c⁻¹ := by rw [h1]; group
            _ = (a * d) * (p * c⁻¹) := by group
            _ = (a * d) * (c⁻¹ * p) := by rw [h3]
            _ = a * d * c⁻¹ * p := by group
        have hPA : P ≤ 𝒜₂ := fun p hp => hC₂z p (hPC₂ hp) (hzP p hp)
        have h64 := Subgroup.card_le_of_le hPA
        rw [hPcard, card_pullSub_radA he φ] at h64
        norm_num at h64
    · exact le_inf (hC₂D.trans le_sup_right) fun c hc => mem_centralizer_iff.2 fun p hp =>
        hC₂c p (hPC₂ hp) c hc
  refine ⟨hKreq, hcen, fun m hm => mem_normalizer_of_conj_mem fun c hc => ?_⟩
  have hcKr := hC₂Kr hc
  have hmc : m * c * m⁻¹ ∈ Kr := by
    refine ⟨mul_mem (mul_mem hm hcKr.1) (inv_mem hm), fun x hx => ?_⟩
    have h := hcKr.2 _ (hNB' m hm x hx)
    have he' : m * c * m⁻¹ * x * (m * c * m⁻¹)⁻¹ * x⁻¹ =
        m * (c * (m⁻¹ * x * m) * c⁻¹ * (m⁻¹ * x * m)⁻¹) * m⁻¹ := by group
    rw [he']
    exact hNP m hm _ h
  rw [← hcen]
  refine mem_inf.2 ⟨hKrA₁D₂ hmc, mem_centralizer_iff.2 fun p hp => ?_⟩
  have hp' : m⁻¹ * p * m ∈ P := by
    have h := hNP m⁻¹ (inv_mem hm) p hp
    rwa [inv_inv] at h
  have h1 : c * (m⁻¹ * p * m) = (m⁻¹ * p * m) * c := hC₂c c hc _ (hPC₂ hp')
  calc p * (m * c * m⁻¹) = m * ((m⁻¹ * p * m) * c) * m⁻¹ := by group
    _ = m * (c * (m⁻¹ * p * m)) * m⁻¹ := by rw [h1]
    _ = m * c * m⁻¹ * p := by group

end Kernel

local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)

include he hnd hzC hinf hz in
theorem degree64_next_V₁ [Finite G] {D₁ C₁ D₂ C₂ K₀ P V₁ : Subgroup G}
    (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁) (hRD₂ : ℛ ≤ D₂) (hC₂D : C₂ ≤ D₂)
    (hC₂R : C₂ ⊓ ℛ = 𝒜₂) (hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂) (hK₀ : K₀ = C₁ ⊓ D₂)
    (hP : P = 𝒜₂ ⊔ K₀) (hV₁ : V₁ = D₁ ⊔ 𝒜₂) (hPV₁ : P ≤ V₁)
    (hV₁C₂ : V₁ ≤ normalizer (C₂ : Set G)) (hV₁card : Nat.card V₁ = 16384)
    (hPcard : Nat.card P = 512) (hC₂card : Nat.card C₂ = 4096) :
    V₁ ⊓ C₂ = P ∧ C₂.relIndex (V₁ ⊔ C₂) = 32 := by
  have hzD₂ : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  have hA₂C₂ : 𝒜₂ ≤ C₂ := radA_le_of_inf_eq φ hC₂R
  have hK₀C₂ : K₀ ≤ C₂ := by
    intro k hk
    rw [hK₀, ← hC₁C₂] at hk
    exact (mem_inf.1 hk).2
  have hPC₂ : P ≤ C₂ := by
    rw [hP]
    exact sup_le hA₂C₂ hK₀C₂
  have heq : V₁ ⊓ C₂ = P := by
    refine le_antisymm (fun v hv => ?_) (le_inf hPV₁ hPC₂)
    obtain ⟨hvV, hvC⟩ := mem_inf.1 hv
    obtain ⟨a, ha, n, c, hc, rfl⟩ := exists_of_mem_V₁ he hb hnd φ hzC hD₁n hC₁z hzC₁
      (by rw [← hV₁]; exact hvV)
    have h1 : z ^ n * c ∈ C₂ := by
      have h := mul_mem (inv_mem (hA₂C₂ ha)) hvC
      rwa [show a⁻¹ * (a * z ^ n * c) = z ^ n * c by group] at h
    have hcD : c ∈ D₂ := by
      have h := mul_mem (inv_mem (zpow_mem hzD₂ n)) (hC₂D h1)
      rwa [inv_mul_cancel_left] at h
    have hcK : c ∈ K₀ := by
      rw [hK₀]
      exact mem_inf.2 ⟨hc, hcD⟩
    have hzn : z ^ n ∈ C₂ := by
      have h := mul_mem h1 (inv_mem (hK₀C₂ hcK))
      rwa [mul_inv_cancel_right] at h
    rcases eq_one_or_eq_of_mem_zpowers hz (zpow_mem (mem_zpowers z) n) with h | h
    · rw [h, mul_one, hP]
      exact mul_mem (mem_sup_left ha) (mem_sup_right hcK)
    · rw [h] at hzn
      exact absurd hzn (z_not_mem_of_inf_eq φ hinf hz hC₂R)
  refine ⟨heq, ?_⟩
  have h1 := natCard_sup_mul_inf hV₁C₂
  have h2 := Subgroup.relIndex_mul_card (H := C₂) (K := V₁ ⊔ C₂)
  rw [inf_of_le_left le_sup_right] at h2
  rw [heq, hPcard, hV₁card, hC₂card, ← h2, hC₂card] at h1
  omega

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
