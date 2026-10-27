module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtIndex
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtC1

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open SymplecticTorusWeyl
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem mem_lagrangianT0_of_congr {g : GL (Fin 3) (ZMod 2)} (hg : g ∈ vecStabGL)
    (h₁ : ((g : M₃) * (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃) * (g : M₃)ᵀ : M₃) 1 1 = 1)
    (h₂ : ((g : M₃) * (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃) * (g : M₃)ᵀ : M₃) 2 2 = 0)
    (h₃ : ((g : M₃) * (!![0, 0, 0; 0, 0, 0; 0, 0, 1] : M₃) * (g : M₃)ᵀ : M₃) 1 1 = 0)
    (h₄ : ((g : M₃) * (!![0, 0, 0; 0, 0, 0; 0, 0, 1] : M₃) * (g : M₃)ᵀ : M₃) 2 2 = 1) :
    g ∈ lagrangianT0 := by
  rw [mem_vecStabGL] at hg
  obtain ⟨g0, g1, g2⟩ := hg
  simp [Matrix.mul_apply, Fin.sum_univ_three, zmod_two_mul_self] at h₁ h₂ h₃ h₄
  refine mem_lagrangianT0.2 ⟨(g : M₃) 0 1, (g : M₃) 0 2, Units.ext ?_⟩
  rw [coe_t0Unit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t0Mat, g0, g1, g2, h₁, h₂, h₃, h₄]

theorem sq_eq_symE₁₁ : ∀ w : Fin 3 → ZMod 2, symThreeSquare 1 w = symE₁₁ → w = ![1, 0, 0] := by
  decide

theorem symThree_polar_ne :
    (-(symThreeSquare 1 ![1, 0, 0]) + symThreeSquare 1 (![1, 0, 0] + ![0, 1, 0]) -
        symThreeSquare 1 ![0, 1, 0] : binarySymMatrices 3) ≠ 0 ∧
      (-(symThreeSquare 1 ![1, 0, 0]) + symThreeSquare 1 (![1, 0, 0] + ![0, 1, 0]) -
        symThreeSquare 1 ![0, 1, 0] : binarySymMatrices 3) ≠ symE₁₁ := by
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} {he : IsSymplecticBasis b e} {hb : b.IsAlt}
variable {G : Type} [Group G] {L : Subgroup G} {φ : L ≃* bilinIsometryGroup b} {z : G}
  {hzC : z ∈ centralizer (L : Set G)} {hz : orderOf z = 2}
variable {D₂ C₂ E₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
variable {σ : ↥(normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓ centralizer ({z} : Set G)) →*
  GL (Fin 3) (ZMod 2)}
variable {D₁ C₁ F₁ : Subgroup G} {ν₁ : G → pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) × ZMod 2}

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝐛₁" => ptB₁ he hb φ hzC hz
local notation "𝒫₁" => 𝒜₁ ⊔ (C₁ ⊓ C₂)
local notation "𝒫₂" => 𝒜₂ ⊔ (C₁ ⊓ C₂)
local notation "𝔄" => (𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))
local notation "𝔅" => zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))
local notation "𝔑" => normalizer ((zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) :
  Subgroup G) : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G)
local notation "𝒵₁" => Subgroup.map C₁.subtype (center C₁)

theorem B_eq_A₂U₁ : (𝔅 : Subgroup G) = 𝒜₂ ⊔ (zpowers z ⊔ 𝒫₁) :=
  le_antisymm (sup_le (le_sup_left.trans le_sup_right) (sup_le (le_sup_right.trans le_sup_right)
    (sup_le le_sup_left (le_sup_right.trans (le_sup_right.trans le_sup_right)))))
    (sup_le ((le_sup_left.trans le_sup_right).trans le_sup_right) (sup_le le_sup_left
      (le_sup_left.trans le_sup_right)))

section Kernel

variable [Finite G] (h : PtFull he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
include h

theorem PtFull.comm_mem_A {m : G} (hm : m ∈ 𝔑) {y : G} (hy : y ∈ 𝔅) :
    m * y * m⁻¹ * y⁻¹ ∈ 𝔄 := by
  have hzN' : z ∈ 𝔑 := h.B_le_N (mem_sup_left (mem_zpowers z))
  have hzN : zpowers z ≤ normalizer ((𝔄 : Subgroup G) : Set G) := zpowers_le.2
    (mem_normalizer_of_conj_mem fun a ha => h.conj_mem_A hzN' ha)
  have hy' : y ∈ ((zpowers z ⊔ 𝔄 : Subgroup G) : Set G) := hy
  rw [coe_mul_of_left_le_normalizer_right _ _ hzN] at hy'
  obtain ⟨t, ht, a, ha, hta⟩ := hy'
  beta_reduce at hta
  subst hta
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
  have hk : z ^ k = z ^ (k % 2) := by
    rw [← zpow_mod_orderOf z k, hz]
    norm_num
  have hma := h.conj_mem_A hm ha
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [hk, h0, zpow_zero, one_mul]
    exact mul_mem hma (inv_mem ha)
  · rw [hk, h1, zpow_one]
    have h2 := h.conj_z_mem_A hm
    have e1 : m * (z * a) * m⁻¹ * (z * a)⁻¹ =
        z * ((z⁻¹ * (m * z * m⁻¹)) * (m * a * m⁻¹) * a⁻¹) * z⁻¹ := by
      group
    rw [e1]
    exact h.conj_mem_A hzN' (mul_mem (mul_mem h2 hma) (inv_mem ha))

theorem PtFull.A_inf_D₁ : (𝔄 : Subgroup G) ⊓ D₁ = 𝒫₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left h.P₁D₁)
  obtain ⟨hxA, hxD⟩ := mem_inf.1 hx
  have hxU : x ∈ zpowers z ⊔ 𝒫₁ := by
    rw [← h.U₁_eq]
    exact mem_inf.2 ⟨mem_sup_right hxA, hxD⟩
  exact mem_of_mem_zpowers_sup hz le_sup_left h.z_not_mem_A (fun y hy => conj_mem_sup
    (fun a ha => h.hA₁n z z_mem_N₁ a ha) (fun k hk => h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk) hy)
    hxU hxA

theorem PtFull.comm_mem_P₁_of_D₁ {d : G} (hd : d ∈ D₁) {y : G} (hy : y ∈ 𝔅) :
    d * y * d⁻¹ * y⁻¹ ∈ 𝒫₁ := by
  rw [← h.A_inf_D₁]
  refine mem_inf.2 ⟨h.comm_mem_A (h.D₁_le_N hd) hy, ?_⟩
  have h1 := h.hD₁n y (mem_inf.1 (h.B_le hy)).1 d⁻¹ (inv_mem hd)
  rw [show d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) by group]
  exact mul_mem hd h1

theorem PtFull.comm_mem_P₁_of_A₂ {a : G} (ha : a ∈ 𝒜₂) {y : G} (hy : y ∈ 𝔅) :
    a * y * a⁻¹ * y⁻¹ ∈ 𝒫₁ := by
  have hA₂B : 𝒜₂ ≤ 𝔅 := (le_sup_left.trans le_sup_right).trans le_sup_right
  have hUD : zpowers z ⊔ 𝒫₁ ≤ D₁ := sup_le (zpowers_le.2 h.zD₁) h.P₁D₁
  have hUB : zpowers z ⊔ 𝒫₁ ≤ 𝔅 := sup_le le_sup_left (le_sup_left.trans le_sup_right)
  have hUle : 𝒜₂ ≤ normalizer ((zpowers z ⊔ 𝒫₁ : Subgroup G) : Set G) := by
    intro a' ha'
    rw [← h.U₁_eq]
    exact mem_normalizer_of_conj_mem fun u hu => mem_inf.2
      ⟨mul_mem (mul_mem (hA₂B ha') (mem_inf.1 hu).1) (inv_mem (hA₂B ha')),
        h.hD₁n a' (h.A₂N₁ ha') u (mem_inf.1 hu).2⟩
  have hy' : y ∈ ((𝒜₂ ⊔ (zpowers z ⊔ 𝒫₁) : Subgroup G) : Set G) := by
    rw [← B_eq_A₂U₁]
    exact hy
  rw [coe_mul_of_left_le_normalizer_right _ _ hUle] at hy'
  obtain ⟨a', ha', u, hu, hau⟩ := hy'
  beta_reduce at hau
  subst hau
  have huD : u ∈ D₁ := hUD hu
  have hu₂ : u ∈ 𝒩₂ := (mem_inf.1 (h.B_le (hUB hu))).2
  have hc₁ : a * u * a⁻¹ * u⁻¹ ∈ D₁ := mul_mem (h.hD₁n a (h.A₂N₁ ha) u huD) (inv_mem huD)
  have hc₂ : a * u * a⁻¹ * u⁻¹ ∈ 𝒜₂ := by
    rw [show a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) by group]
    exact mul_mem ha (h.conj_A₂_mem hu₂ (inv_mem ha))
  have hc : a * u * a⁻¹ * u⁻¹ ∈ 𝒫₁ := by
    have h1 : a * u * a⁻¹ * u⁻¹ ∈ 𝒜₂ ⊓ D₁ := mem_inf.2 ⟨hc₂, hc₁⟩
    rw [h.A₂_inf_D₁] at h1
    exact mem_sup_left (mem_inf.1 h1).1
  have hcomm : a * a' = a' * a := h.toLagBase.D₂A (h.A₂D₂ ha) ha'
  have e1 : a * (a' * u) * a⁻¹ * (a' * u)⁻¹ = a' * (a * u * a⁻¹ * u⁻¹) * a'⁻¹ := by
    calc a * (a' * u) * a⁻¹ * (a' * u)⁻¹ = a * a' * u * a⁻¹ * u⁻¹ * a'⁻¹ := by group
      _ = a' * a * u * a⁻¹ * u⁻¹ * a'⁻¹ := by rw [hcomm]
      _ = a' * (a * u * a⁻¹ * u⁻¹) * a'⁻¹ := by group
  rw [e1]
  exact h.conj_mem_P₁ (h.B_le_N (hA₂B ha')) hc

theorem PtFull.comm_mem_P₁_of_D₁A₂ {x : G} (hx : x ∈ D₁ ⊔ 𝒜₂) {y : G} (hy : y ∈ 𝔅) :
    x * y * x⁻¹ * y⁻¹ ∈ 𝒫₁ := by
  have hle : 𝒜₂ ≤ normalizer (D₁ : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₁n a (h.A₂N₁ ha) d hd
  have hx' : x ∈ ((D₁ ⊔ 𝒜₂ : Subgroup G) : Set G) := hx
  rw [coe_mul_of_right_le_normalizer_left _ _ hle] at hx'
  obtain ⟨d, hd, a, ha, hda⟩ := hx'
  beta_reduce at hda
  subst hda
  have e1 : d * a * y * (d * a)⁻¹ * y⁻¹ =
      d * (a * y * a⁻¹ * y⁻¹) * d⁻¹ * (d * y * d⁻¹ * y⁻¹) := by
    group
  rw [e1]
  exact mul_mem (h.conj_mem_P₁ (h.D₁_le_N hd) (h.comm_mem_P₁_of_A₂ ha hy))
    (h.comm_mem_P₁_of_D₁ hd hy)

theorem PtFull.comm_mem_P₁_conj {m : G} (hm : m ∈ 𝔑) {x : G}
    (hx : ∀ y ∈ 𝔅, x * y * x⁻¹ * y⁻¹ ∈ 𝒫₁) {y : G} (hy : y ∈ 𝔅) :
    m * x * m⁻¹ * y * (m * x * m⁻¹)⁻¹ * y⁻¹ ∈ 𝒫₁ := by
  have hy' : m⁻¹ * y * m ∈ 𝔅 := by
    have h1 := (mem_normalizer_iff.1 (mem_inf.1 (inv_mem hm)).1 y).1 hy
    rwa [inv_inv] at h1
  have e1 : m * x * m⁻¹ * y * (m * x * m⁻¹)⁻¹ * y⁻¹ =
      m * (x * (m⁻¹ * y * m) * x⁻¹ * (m⁻¹ * y * m)⁻¹) * m⁻¹ := by
    group
  rw [e1]
  exact h.conj_mem_P₁ hm (hx _ hy')

theorem PtFull.mem_D₁A₂_of_comm
    (hK : 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) ≤ 𝒩₁) {x : G} (hxN : x ∈ 𝔑)
    (hx : ∀ y ∈ 𝔅, x * y * x⁻¹ * y⁻¹ ∈ 𝒫₁) : x ∈ D₁ ⊔ 𝒜₂ := by
  have hzN : z ∈ 𝔑 := h.B_le_N (mem_sup_left (mem_zpowers z))
  have hA₂B : 𝒜₂ ≤ 𝔅 := (le_sup_left.trans le_sup_right).trans le_sup_right
  have hxz := hx z (mem_sup_left (mem_zpowers z))
  have hp : z⁻¹ * (x * z * x⁻¹ * z⁻¹) * z ∈ 𝒫₁ := by
    have h1 := h.conj_mem_P₁ (inv_mem hzN) hxz
    rwa [inv_inv] at h1
  have hxK : x ∈ 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) := by
    refine mem_inf.2 ⟨hxN, ?_⟩
    rw [h.U₁_eq]
    exact mem_normalizer_zP (fun m hm q hq => h.conj_mem_P₁ hm hq) hxN hp (by group)
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₁ _ (hK hxK)
  have hdN := h.D₁_le_N hd
  have hcN : c ∈ 𝔑 := by
    have h1 := mul_mem (inv_mem hdN) hxN
    rwa [inv_mul_cancel_left] at h1
  have hc' : ∀ y ∈ 𝔅, c * y * c⁻¹ * y⁻¹ ∈ 𝒫₁ := by
    intro y hy
    have e1 : c * y * c⁻¹ * y⁻¹ =
        d⁻¹ * (d * c * y * (d * c)⁻¹ * y⁻¹) * d⁻¹⁻¹ * (d⁻¹ * y * d⁻¹⁻¹ * y⁻¹) := by
      group
    rw [e1]
    exact mul_mem (h.conj_mem_P₁ (inv_mem hdN) (hx y hy)) (h.comm_mem_P₁_of_D₁ (inv_mem hd) hy)
  obtain ⟨hc₁, hcH⟩ := mem_inf.1 hc
  have hc₂ := h.mem_N₂_of_normalizer_B (mem_inf.1 hcN).1 hcH
  let n : ↥(𝒩₂ ⊓ centralizer ({z} : Set G)) := ⟨c, mem_inf.2 ⟨hc₂, hcH⟩⟩
  have hσ₁ : σ n ∈ vecStabGL := (mem_normalizer_ptSub_iff_sigma he hb h.hnd φ hzC h.hsup h.hinf
    hz σ h.hσcol h.hσker n).1 hc₁
  have hblk : ∀ B : binarySymMatrices 3,
      (symThreeCongr (σ n) B : M₃) 1 1 = (B : M₃) 1 1 ∧
        (symThreeCongr (σ n) B : M₃) 2 2 = (B : M₃) 2 2 := by
    intro B
    have h1 : c * tauHom φ he (Multiplicative.ofAdd B) * c⁻¹ =
        tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ n) B)) :=
      conj_tauHom_of_sigma φ he σ h.hσ n B
    have hτB : tauHom φ he (Multiplicative.ofAdd B) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have hτB' : tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ n) B)) ∈ 𝒜₂ :=
      (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have h2 := hc' _ (hA₂B hτB)
    rw [h1] at h2
    have h3 : tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ n) B)) *
        (tauHom φ he (Multiplicative.ofAdd B))⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ := by
      rw [← h.A₂_inf_D₁]
      exact mem_inf.2 ⟨mul_mem hτB' (inv_mem hτB), h.P₁D₁ h2⟩
    obtain ⟨c', y, y', hj⟩ := (mem_ptA_inf_radA_iff he hb φ).1 h3
    rw [← map_inv, ← map_mul] at hj
    have hj' := congrArg (fun X => ((Multiplicative.toAdd X : binarySymMatrices 3) : M₃))
      (tauHom_injective φ he hj)
    have e11 := congrFun (congrFun hj' 1) 1
    have e22 := congrFun (congrFun hj' 2) 2
    simp [jMat] at e11 e22
    have h2' : (2 : ZMod 2) = 0 := rfl
    constructor
    · linear_combination -e11 - (B : M₃) 1 1 * h2'
    · linear_combination -e22 - (B : M₃) 2 2 * h2'
  have hT : σ n ∈ lagrangianT0 := by
    refine mem_lagrangianT0_of_congr hσ₁ ?_ ?_ ?_ ?_
    · have := (hblk ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], by decide⟩).1
      simpa [symThreeCongr] using this
    · have := (hblk ⟨!![0, 0, 0; 0, 1, 0; 0, 0, 0], by decide⟩).2
      simpa [symThreeCongr] using this
    · have := (hblk ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], by decide⟩).1
      simpa [symThreeCongr] using this
    · have := (hblk ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], by decide⟩).2
      simpa [symThreeCongr] using this
  have hcX : n ∈ (ℬ₁ ⊔ ℛ).subgroupOf (𝒩₂ ⊓ centralizer ({z} : Set G)) := by
    rw [subgroupOf_ptSub_sup_radSub he hb h.hnd φ hzC h.hsup h.hinf hz σ h.hσcol h.hσker
      h.hσsurj]
    exact hT
  have hcX' : c ∈ ℬ₁ ⊔ ℛ := hcX
  have hle : ℬ₁ ⊔ ℛ ≤ D₁ ⊔ 𝒜₂ := sup_le ((h.hBF₁.trans h.hFD₁).trans le_sup_left)
    (sup_le le_sup_right ((zpowers_le.2 h.zD₁).trans le_sup_left))
  exact mul_mem (mem_sup_left hd) (hle hcX')

theorem PtFull.conj_mem_D₁A₂
    (hK : 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) ≤ 𝒩₁) {m : G} (hm : m ∈ 𝔑) {x : G}
    (hx : x ∈ D₁ ⊔ 𝒜₂) : m * x * m⁻¹ ∈ D₁ ⊔ 𝒜₂ := by
  have hA₂B : 𝒜₂ ≤ 𝔅 := (le_sup_left.trans le_sup_right).trans le_sup_right
  have hxN : x ∈ 𝔑 := (sup_le h.D₁_le_N (hA₂B.trans h.B_le_N)) hx
  exact h.mem_D₁A₂_of_comm hK (mul_mem (mul_mem hm hxN) (inv_mem hm)) fun y hy =>
    h.comm_mem_P₁_conj hm (fun y' hy' => h.comm_mem_P₁_of_D₁A₂ hx hy') hy

theorem PtFull.conj_mem_C₁
    (hK : 𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) ≤ 𝒩₁) {m : G} (hm : m ∈ 𝔑) {c : G}
    (hc : c ∈ C₁) : m * c * m⁻¹ ∈ C₁ := by
  have hmb : Commute m 𝐛₁ := mem_centralizer_singleton_iff.1 (mem_inf.1 hm).2
  have hI : ∀ i ∈ zpowers 𝐛₁, m * i * m⁻¹ = i := by
    intro i hi
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hi
    rw [(hmb.zpow_right k).eq, mul_inv_cancel_right]
  have hb₁C : 𝐛₁ ∈ C₁ := by
    have h1 : 𝐛₁ ∈ 𝒵₁ ⊓ 𝒜₁ := by
      rw [h.hZ₁A]
      exact mem_zpowers _
    exact map_subtype_le _ (mem_inf.1 h1).1
  have hsq : ∀ x ∈ C₁, x ^ 2 ∈ zpowers 𝐛₁ := fun x hx => by
    rw [← h.hC₁sq]
    exact subset_closure ⟨x, hx, rfl⟩
  have hcomm : ∀ x ∈ C₁, ∀ y ∈ C₁, x⁻¹ * y⁻¹ * x * y ∈ zpowers 𝐛₁ := fun x hx y hy => by
    rw [← h.hC₁comm]
    have h1 := commutator_mem_commutator (inv_mem hx) (inv_mem hy)
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1
  have hmap : C₁.map (MulAut.conj m).toMonoidHom = C₁ := by
    refine h.eq_C₁_of_le_D₁_sup ?_ ?_ ?_ ?_ ?_
    · rw [zpowers_le]
      exact ⟨𝐛₁, hb₁C, hI _ (mem_zpowers _)⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact h.conj_mem_D₁A₂ hK hm (mem_sup_left (h.hC₁D hx))
    · rw [card_map_of_injective (MulAut.conj m).injective, h.hC₁card]
    · rintro _ ⟨x, hx, rfl⟩
      change (m * x * m⁻¹) ^ 2 ∈ _
      rw [show (m * x * m⁻¹) ^ 2 = m * x ^ 2 * m⁻¹ by rw [sq, sq]; group, hI _ (hsq x hx)]
      exact hsq x hx
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      change (m * x * m⁻¹)⁻¹ * (m * y * m⁻¹)⁻¹ * (m * x * m⁻¹) * (m * y * m⁻¹) ∈ _
      rw [show (m * x * m⁻¹)⁻¹ * (m * y * m⁻¹)⁻¹ * (m * x * m⁻¹) * (m * y * m⁻¹) =
        m * (x⁻¹ * y⁻¹ * x * y) * m⁻¹ by group, hI _ (hcomm x hx y hy)]
      exact hcomm x hx y hy
  rw [← hmap]
  exact ⟨c, hc, rfl⟩

theorem PtFull.not_normalizes_C₁ : ¬ ∀ d ∈ D₂, ∀ c ∈ C₁, d * c * d⁻¹ ∈ C₁ := by
  intro hD
  have hb₁ : 𝐛₁ ∈ ({x | ∃ y ∈ 𝒵₁, y ^ 2 = x} : Set G) := by
    rw [h.sq_center_C₁]
    exact mem_zpowers _
  obtain ⟨t, ht, ht2⟩ := hb₁
  have htC₂ : t ∈ C₂ := h.hZ₁C₂ ht
  have hδt : symThreeDiag (ν₂ t : M₃) = ![1, 0, 0] := by
    have h1 := h.hsq t htC₂
    rw [ht2, ptB₁_eq_tauHom he hb φ hzC hz] at h1
    exact sq_eq_symE₁₁ _ (Multiplicative.ofAdd.injective (tauHom_injective φ he h1)).symm
  obtain ⟨d, hdC, hδd⟩ := h.hδs ![0, 1, 0]
  have hdD : d ∈ D₂ := h.C₂D₂ hdC
  have hdt : d * t * d⁻¹ ∈ 𝒵₁ := by
    obtain ⟨t', ht', rfl⟩ := ht
    have hc : d * (t' : G) * d⁻¹ ∈ C₁ := hD d hdD _ t'.2
    refine ⟨⟨_, hc⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    have hg' : d⁻¹ * (g : G) * d ∈ C₁ := by
      have h1 := hD d⁻¹ (inv_mem hdD) _ g.2
      rwa [inv_inv] at h1
    have h1 : (d⁻¹ * (g : G) * d) * (t' : G) = (t' : G) * (d⁻¹ * (g : G) * d) :=
      congrArg Subtype.val ((mem_center_iff.1 ht') ⟨_, hg'⟩)
    apply Subtype.ext
    change (g : G) * (d * t' * d⁻¹) = d * t' * d⁻¹ * g
    calc (g : G) * (d * t' * d⁻¹) = d * ((d⁻¹ * g * d) * t') * d⁻¹ := by group
      _ = d * ((t' : G) * (d⁻¹ * g * d)) * d⁻¹ := by rw [h1]
      _ = d * t' * d⁻¹ * g := by group
  have hu₁ : t⁻¹ * (d * t * d⁻¹) ∈ 𝒵₁ := mul_mem (inv_mem ht) hdt
  have htd : t * d ∈ C₂ := mul_mem htC₂ hdC
  have hδtd : symThreeDiag (ν₂ (t * d) : M₃) = ![1, 0, 0] + ![0, 1, 0] := by
    rw [h.toLagBase.nu_mul h.hinf (h.C₂D₂ htC₂) hdD, ← hδt, ← hδd, ← symThreeDiag_add]
    rfl
  have hu : t⁻¹ * (d * t * d⁻¹) =
      (tauHom φ he (Multiplicative.ofAdd (symThreeSquare 1 ![1, 0, 0])))⁻¹ *
        tauHom φ he (Multiplicative.ofAdd (symThreeSquare 1 (![1, 0, 0] + ![0, 1, 0]))) *
          (tauHom φ he (Multiplicative.ofAdd (symThreeSquare 1 ![0, 1, 0])))⁻¹ := by
    rw [← hδtd, ← hδt, ← hδd, ← h.hsq t htC₂, ← h.hsq _ htd, ← h.hsq d hdC, sq, sq, sq]
    group
  have hτ : ∀ X : binarySymMatrices 3, tauHom φ he (Multiplicative.ofAdd X) ∈ 𝒜₂ :=
    fun X => (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hu₂ : t⁻¹ * (d * t * d⁻¹) ∈ 𝒜₂ := by
    rw [hu]
    exact mul_mem (mul_mem (inv_mem (hτ _)) (hτ _)) (inv_mem (hτ _))
  have hZD : 𝒵₁ ≤ D₁ := (map_subtype_le _).trans h.hC₁D
  have hu₃ : t⁻¹ * (d * t * d⁻¹) ∈ zpowers 𝐛₁ := by
    rw [← h.hZ₁A]
    have h1 : t⁻¹ * (d * t * d⁻¹) ∈ 𝒜₂ ⊓ D₁ := mem_inf.2 ⟨hu₂, hZD hu₁⟩
    rw [h.A₂_inf_D₁] at h1
    exact mem_inf.2 ⟨hu₁, (mem_inf.1 h1).1⟩
  have hτM : tauHom φ he (Multiplicative.ofAdd (-(symThreeSquare 1 ![1, 0, 0]) +
      symThreeSquare 1 (![1, 0, 0] + ![0, 1, 0]) - symThreeSquare 1 ![0, 1, 0])) =
        t⁻¹ * (d * t * d⁻¹) := by
    rw [hu]
    simp only [ofAdd_sub, ofAdd_add, ofAdd_neg, div_eq_mul_inv, map_mul, map_inv]
  rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) hu₃ with h1 | h1
  · rw [← hτM, ← map_one (tauHom φ he), ← ofAdd_zero] at h1
    exact symThree_polar_ne.1 (Multiplicative.ofAdd.injective (tauHom_injective φ he h1))
  · rw [← hτM, ptB₁_eq_tauHom he hb φ hzC hz] at h1
    exact symThree_polar_ne.2 (Multiplicative.ofAdd.injective (tauHom_injective φ he h1))

theorem PtFull.not_K₁_le_N₁ : ¬ (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) ≤ 𝒩₁) :=
  fun hK => h.not_normalizes_C₁ fun _ hd _ hc => h.conj_mem_C₁ hK (h.D₂_le_N hd) hc

theorem PtFull.relIndex_K₁_eq_two :
    (𝔑 ⊓ 𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) = 2 := by
  have hle := h.relIndex_K₁_le_two
  have h1 : (𝔑 ⊓ 𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) ≠ 1 := by
    rw [Ne, relIndex_eq_one]
    exact fun hK => h.not_K₁_le_N₁ (hK.trans inf_le_right)
  have h0 : (𝔑 ⊓ 𝒩₁).relIndex (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G)) ≠ 0 := by
    intro h0
    have h2 := relIndex_mul_card_of_le h.N_inf_N₁_le
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := (𝔑 ⊓ normalizer ((𝔅 ⊓ D₁ : Subgroup G) : Set G) :
      Subgroup G))).ne' h2.symm
  omega

end Kernel

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
