module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralPoint
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64FixedLift

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

abbrev symE₃₃ : ↥(binarySymMatrices 3) :=
  ⟨!![0, 0, 0; 0, 0, 0; 0, 0, 1], mem_binarySymMatrices.2 (by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl)⟩

theorem zmod_two_t0_diag : ∀ y y' : ZMod 2,
    symThreeDiag (t0Mat y y' * !![0, 0, 0; 0, 1, 0; 0, 0, 0] * (t0Mat y y')ᵀ +
      !![0, 0, 0; 0, 1, 0; 0, 0, 0]) = 0 →
    symThreeDiag (t0Mat y y' * !![0, 0, 0; 0, 0, 0; 0, 0, 1] * (t0Mat y y')ᵀ +
      !![0, 0, 0; 0, 0, 0; 0, 0, 1]) = 0 → y = 0 ∧ y' = 0 := by
  decide

theorem zmod_two_t0_alt : ∀ y y' : ZMod 2,
    (alt3Mat 0 0 1 + t0Mat y y' * alt3Mat 0 0 1 * (t0Mat y y')ᵀ = 0 ∨
      alt3Mat 0 0 1 + t0Mat y y' * alt3Mat 0 0 1 * (t0Mat y y')ᵀ = jMat 1 0 0) →
      y = 0 ∧ y' = 0 := by
  decide

section Generic

variable {X : Type*} [Group X]

theorem gamma_conj {z g x : X} (hg : g * z = z * g) :
    z⁻¹ * (g * x * g⁻¹)⁻¹ * z * (g * x * g⁻¹) = g * (z⁻¹ * x⁻¹ * z * x) * g⁻¹ := by
  have hzg : g * z * g⁻¹ = z := by rw [hg, mul_inv_cancel_right]
  calc z⁻¹ * (g * x * g⁻¹)⁻¹ * z * (g * x * g⁻¹) =
      (g * z * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ * (g * z * g⁻¹) * (g * x * g⁻¹) := by rw [hzg]
    _ = g * (z⁻¹ * x⁻¹ * z * x) * g⁻¹ := by group

theorem gamma_mul {z x y : X} (hp : y * (z⁻¹ * x⁻¹ * z * x) = (z⁻¹ * x⁻¹ * z * x) * y)
    (hq : (z⁻¹ * x⁻¹ * z * x) * (z⁻¹ * y⁻¹ * z * y) =
      (z⁻¹ * y⁻¹ * z * y) * (z⁻¹ * x⁻¹ * z * x)) :
    z⁻¹ * (x * y)⁻¹ * z * (x * y) = (z⁻¹ * x⁻¹ * z * x) * (z⁻¹ * y⁻¹ * z * y) := by
  calc z⁻¹ * (x * y)⁻¹ * z * (x * y) = z⁻¹ * y⁻¹ * z * ((z⁻¹ * x⁻¹ * z * x) * y) := by group
    _ = z⁻¹ * y⁻¹ * z * (y * (z⁻¹ * x⁻¹ * z * x)) := by rw [hp]
    _ = (z⁻¹ * y⁻¹ * z * y) * (z⁻¹ * x⁻¹ * z * x) := by group
    _ = _ := hq.symm

theorem comm_of_inv_mul_mul_eq {d a : X} (h : d⁻¹ * a * d = a) : d * a = a * d := by
  calc d * a = d * (d⁻¹ * a * d) := by rw [h]
    _ = a * d := by group

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
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)
local notation "𝒩₂₀" => (normalizer ((radSub φ z e : Subgroup G) : Set G) ⊓
  centralizer (Singleton.singleton z : Set G) : Subgroup G)

include he in
theorem radA_comm {x y : G} (hx : x ∈ 𝒜₂) (hy : y ∈ 𝒜₂) : x * y = y * x := by
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 hx
  obtain ⟨C, rfl⟩ := (mem_pullSub_iff φ he).1 hy
  rw [← map_mul, ← map_mul, mul_comm]

include he in
theorem tauHom_inv_mul (X Y : ↥(binarySymMatrices 3)) :
    (tauHom φ he (Multiplicative.ofAdd X))⁻¹ * tauHom φ he (Multiplicative.ofAdd Y) =
      tauHom φ he (Multiplicative.ofAdd (X + Y)) := by
  rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add,
    neg_eq_of_add_eq_zero_left (symThree_add_self X)]

omit hb in
include hzC hinf in
theorem mem_radA_of_mem_radSub {x : G} (hxR : x ∈ ℛ) (hxL : x ∈ L) : x ∈ 𝒜₂ := by
  have h : x ∈ (𝒜₂ ⊔ zpowers z) ⊓ L := mem_inf.2 ⟨hxR, hxL⟩
  rwa [sup_inf_eq hzC hinf (pullSub_le φ _)] at h

include he hnd hzC hinf hz in
theorem comm_mem_ptA_inf_radA {a x : G} (ha : a ∈ 𝒜₁) (hx : x ∈ 𝒜₂) :
    x * a * x⁻¹ * a⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ := by
  have hxL : x ∈ L := pullSub_le φ _ hx
  have haL : a ∈ L := (ptA_facts he hb hnd φ).1 ha
  have hxN : x ∈ normalizer (𝒜₁ : Set G) :=
    (mem_normalizer_ptSub_iff_of_mem he hb hnd φ hzC hinf hz hxL).1
      (radSub_le_normalizer_ptSub he hb hnd φ hzC (mem_sup_left hx))
  have haN : a ∈ 𝒩₂ := ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left ha)
  refine mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hxN a).1 ha) (inv_mem ha), ?_⟩
  have h1 : a * x⁻¹ * a⁻¹ ∈ ℛ := (mem_normalizer_iff.1 haN x⁻¹).1 (mem_sup_left (inv_mem hx))
  have h2 : a * x⁻¹ * a⁻¹ ∈ 𝒜₂ :=
    mem_radA_of_mem_radSub φ hzC hinf h1 (mul_mem (mul_mem haL (inv_mem hxL)) (inv_mem haL))
  have h3 : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
  rw [h3]
  exact mul_mem hx h2

include he hnd hzC hinf hz in
theorem comm_mem_ptA_inf_radA' {a x : G} (ha : a ∈ 𝒜₁) (hx : x ∈ 𝒜₂) :
    a * x * a⁻¹ * x⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ := by
  have h := inv_mem (comm_mem_ptA_inf_radA he hb hnd φ hzC hinf hz ha hx)
  have h1 : (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ := by group
  rwa [h1] at h

omit hb hnd hsup hinf in
theorem comm_mem_altSub_of_mem {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)} {κ : ZMod 2}
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    {d : G} (hd : d ∈ D₂) {g : G} (hg : g ∈ 𝒜₂) : d⁻¹ * g⁻¹ * d * g ∈ altSub φ he := by
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 hg
  set X := κ • symThreePolarSym (symThreeDiag (ν₂ d : M₃))
    (symThreeDiag ((Multiplicative.toAdd B : ↥(binarySymMatrices 3)) : M₃)) with hX
  have h := hact₂ d hd (Multiplicative.toAdd B) 0
  rw [zero_smul, add_zero, radHom_tau, radHom_tau, ofAdd_toAdd] at h
  refine ⟨X, ?_, ?_⟩
  · change symThreeDiag (κ • (symThreePolarSym _ _ : M₃)) = 0
    rw [symThreeDiag_smul, symThreeDiag_polarSym, smul_zero]
  · calc tauHom φ he (Multiplicative.ofAdd X) =
        (tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd B + X)))⁻¹ *
          tauHom φ he (Multiplicative.ofAdd (Multiplicative.toAdd B)) := by
          rw [tauHom_inv_mul, add_comm (Multiplicative.toAdd B) X, add_assoc, symThree_add_self,
            add_zero]
      _ = d⁻¹ * (tauHom φ he B)⁻¹ * d * tauHom φ he B := by rw [ofAdd_toAdd, ← h]; group

theorem inv_mul_mul_eq_of_comm {d a : G} (h : d * a = a * d) : d⁻¹ * a * d = a := by
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem exists_mem_inf_conj_eq_of_sup [Finite G] {C₁ D₁ D₂ : Subgroup G}
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁) (hzD₂ : z ∈ D₂)
    {j : G} (hj : j ∈ 𝒜₁ ⊓ 𝒜₂) : ∃ k ∈ C₁ ⊓ D₂, k⁻¹ * z * k = z * j := by
  obtain ⟨k, hk, hkz⟩ := hKz j hj
  have hzN : zpowers z ≤ normalizer (C₁ : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_map_le ?_
    rintro _ ⟨c, hc, rfl⟩
    exact hzC₁ c hc
  have hkD : k ∈ ((zpowers z ⊔ C₁ : Subgroup G) : Set G) := by
    rw [hC₁z]
    exact (mem_inf.1 hk).1
  rw [coe_mul_of_left_le_normalizer_right _ _ hzN] at hkD
  obtain ⟨t, ht, c, hc, rfl⟩ := hkD
  have htz : t * z = z * t := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ht
    exact (Commute.refl z).zpow_left n
  have hcD₂ : c ∈ D₂ := by
    have h := mul_mem (inv_mem ((zpowers_le.2 hzD₂) ht)) (mem_inf.1 hk).2
    rwa [inv_mul_cancel_left] at h
  refine ⟨c, mem_inf.2 ⟨hc, hcD₂⟩, ?_⟩
  rw [← hkz]
  calc c⁻¹ * z * c = c⁻¹ * (t⁻¹ * (t * z)) * c := by group
    _ = c⁻¹ * (t⁻¹ * (z * t)) * c := by rw [htz]
    _ = (t * c)⁻¹ * z * (t * c) := by group

theorem exists_ptA_mul_of_conj_mem [Finite G] {C₁ D₁ D₂ : Subgroup G}
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁) (hzD₂ : z ∈ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁D : C₁ ≤ D₁)
    {c : G} (hc : c ∈ C₁) (hcj : z⁻¹ * c⁻¹ * z * c ∈ 𝒜₁ ⊓ 𝒜₂) :
    ∃ a ∈ 𝒜₁, ∃ k ∈ C₁ ⊓ D₂, c = a * k := by
  obtain ⟨k, hk, hkz⟩ := exists_mem_inf_conj_eq_of_sup hb φ hKz hC₁z hzC₁ hzD₂ hcj
  have hkz' : k⁻¹ * z * k = c⁻¹ * z * c := by
    rw [hkz]
    group
  have hkC : c * k⁻¹ ∈ C₁ := mul_mem hc (inv_mem (mem_inf.1 hk).1)
  have hz1 : c * k⁻¹ * z = z * (c * k⁻¹) := by
    calc c * k⁻¹ * z = c * (k⁻¹ * z * k) * k⁻¹ := by group
      _ = c * (c⁻¹ * z * c) * k⁻¹ := by rw [hkz']
      _ = z * (c * k⁻¹) := by group
  have hB : c * k⁻¹ ∈ C₁ ⊓ ℬ₁ := by
    refine mem_inf.2 ⟨hkC, ?_⟩
    rw [← hD₁H]
    exact mem_inf.2 ⟨hC₁D hkC, mem_centralizer_singleton_iff.2 hz1⟩
  rw [hC₁B] at hB
  exact ⟨c * k⁻¹, hB, k, hk, by group⟩

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

include he hnd hzC hsup hz in
theorem ptA_inv_mem_N₂₀ {a : G} (ha : a ∈ 𝒜₁) : a⁻¹ ∈ 𝒩₂₀ :=
  mem_inf.2 ⟨ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left (inv_mem ha)),
    ptSub_le_centralizer he hb hnd φ hsup (mem_sup_left (inv_mem ha))⟩

include he hσ in
theorem conj_tauHom_inv {a : G} (ha : a⁻¹ ∈ 𝒩₂₀) (B : ↥(binarySymMatrices 3)) :
    a⁻¹ * tauHom φ he (Multiplicative.ofAdd B) * a =
      tauHom φ he (Multiplicative.ofAdd (symThreeCongr (σ ⟨a⁻¹, ha⟩) B)) := by
  have h := conj_tauHom_of_sigma φ he σ hσ ⟨a⁻¹, ha⟩ B
  change a⁻¹ * _ * a⁻¹⁻¹ = _ at h
  rwa [inv_inv] at h

include hnd hzC hsup hinf hz hσ hσcol hσker in
theorem mem_radA_of_comm_mem_altSub {a : G} (ha : a ∈ 𝒜₁)
    (h2 : a⁻¹ * (tauHom φ he (Multiplicative.ofAdd symE₂₂))⁻¹ * a *
      tauHom φ he (Multiplicative.ofAdd symE₂₂) ∈ altSub φ he)
    (h3 : a⁻¹ * (tauHom φ he (Multiplicative.ofAdd symE₃₃))⁻¹ * a *
      tauHom φ he (Multiplicative.ofAdd symE₃₃) ∈ altSub φ he) : a ∈ 𝒜₂ := by
  have haN := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz ha
  obtain ⟨y, y', hT⟩ := mem_lagrangianT0.1
    (sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol ⟨a⁻¹, haN⟩ (inv_mem ha))
  have hdiag : ∀ B : ↥(binarySymMatrices 3),
      a⁻¹ * (tauHom φ he (Multiplicative.ofAdd B))⁻¹ * a * tauHom φ he (Multiplicative.ofAdd B) ∈
        altSub φ he →
      symThreeDiag (t0Mat y y' * (B : M₃) * (t0Mat y y')ᵀ + (B : M₃)) = 0 := by
    intro B hB
    have h1 : a⁻¹ * (tauHom φ he (Multiplicative.ofAdd B))⁻¹ * a *
        tauHom φ he (Multiplicative.ofAdd B) = tauHom φ he (Multiplicative.ofAdd
          (symThreeCongr (σ ⟨a⁻¹, haN⟩) B + B)) := by
      rw [← tauHom_inv_mul, ← conj_tauHom_inv he φ σ hσ haN]
      group
    obtain ⟨B', hB', hB'x⟩ := hB
    rw [h1] at hB'x
    have h2 := Multiplicative.ofAdd.injective (tauHom_injective φ he hB'x)
    rw [h2] at hB'
    rw [hT] at hB'
    exact hB'
  obtain ⟨hy, hy'⟩ := zmod_two_t0_diag y y' (hdiag symE₂₂ h2) (hdiag symE₃₃ h3)
  subst hy hy'
  have hσ1 : σ ⟨a⁻¹, haN⟩ = 1 := by
    rw [hT]
    exact Units.ext t0Mat_zero
  have hker : (⟨a⁻¹, haN⟩ : 𝒩₂₀) ∈ σ.ker := hσ1
  rw [hσker, mem_subgroupOf] at hker
  have haR : a ∈ ℛ := by
    have h := inv_mem hker
    rwa [inv_inv] at h
  exact mem_radA_of_mem_radSub φ hzC hinf haR ((ptA_facts he hb hnd φ).1 ha)

include hnd hsup hinf hσ hσcol hσker in
theorem exists_ptA_comm_not_mem_zpowers [Finite G] :
    ∃ a₀ ∈ 𝒜₁, (tauHom φ he (Multiplicative.ofAdd (altSym 0 0 1)))⁻¹ * a₀⁻¹ *
      tauHom φ he (Multiplicative.ofAdd (altSym 0 0 1)) * a₀ ∉
        zpowers (ptB₁ he hb φ hzC hz) := by
  obtain ⟨a₀, ha₀, ha₀R⟩ : ∃ a₀ ∈ 𝒜₁, a₀ ∉ ℛ := by
    by_contra hne
    push Not at hne
    have hle : 𝒜₁ ≤ 𝒜₁ ⊓ 𝒜₂ := fun a ha =>
      mem_inf.2 ⟨ha, mem_radA_of_mem_radSub φ hzC hinf (hne a ha) ((ptA_facts he hb hnd φ).1 ha)⟩
    have h := Subgroup.card_le_of_le hle
    rw [(ptA_facts he hb hnd φ).2.2.1, card_ptA_inf_radA he hb φ] at h
    omega
  refine ⟨a₀, ha₀, fun hmem => ha₀R ?_⟩
  have haN := ptA_inv_mem_N₂₀ he hb hnd φ hzC hsup hz ha₀
  obtain ⟨y, y', hT⟩ := mem_lagrangianT0.1
    (sigma_mem_lagrangianT0_of_mem_ptA he hb φ σ hσcol ⟨a₀⁻¹, haN⟩ (inv_mem ha₀))
  have h1 : (tauHom φ he (Multiplicative.ofAdd (altSym 0 0 1)))⁻¹ * a₀⁻¹ *
      tauHom φ he (Multiplicative.ofAdd (altSym 0 0 1)) * a₀ = tauHom φ he (Multiplicative.ofAdd
        (altSym 0 0 1 + symThreeCongr (σ ⟨a₀⁻¹, haN⟩) (altSym 0 0 1))) := by
    rw [← tauHom_inv_mul, ← conj_tauHom_inv he φ σ hσ haN]
    group
  rw [h1] at hmem
  have hmat : alt3Mat 0 0 1 + t0Mat y y' * alt3Mat 0 0 1 * (t0Mat y y')ᵀ = 0 ∨
      alt3Mat 0 0 1 + t0Mat y y' * alt3Mat 0 0 1 * (t0Mat y y')ᵀ = jMat 1 0 0 := by
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) hmem with h | h
    · left
      rw [← map_one (tauHom φ he), ← ofAdd_zero] at h
      have h2 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
      rw [hT] at h2
      exact h2
    · right
      rw [ptB₁_eq_tauHom] at h
      have h2 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
      rw [hT] at h2
      exact h2
  obtain ⟨hy, hy'⟩ := zmod_two_t0_alt y y' hmat
  subst hy hy'
  have hσ1 : σ ⟨a₀⁻¹, haN⟩ = 1 := by
    rw [hT]
    exact Units.ext t0Mat_zero
  have hker : (⟨a₀⁻¹, haN⟩ : 𝒩₂₀) ∈ σ.ker := hσ1
  rw [hσker, mem_subgroupOf] at hker
  have h := inv_mem hker
  rwa [inv_inv] at h

include hnd hsup hinf hσ hσcol hσker in
theorem false_of_alpha_eq_one [Finite G] {C₁ D₁ D₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)} {κ : ZMod 2}
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hA₁c : ∀ d ∈ D₁, ∀ a ∈ 𝒜₁, d * a = a * d)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hC₁D : C₁ ≤ D₁) (hC₁n : ∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁)
    (hγA : ∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c ∈ 𝒜₁)
    (hγsurj : ∀ a ∈ 𝒜₁, ∃ c ∈ C₁, z⁻¹ * c⁻¹ * z * c = a)
    (hα1 : ∀ c ∈ C₁, c ^ 2 = 1 → z⁻¹ * (c⁻¹ * z * c) ∈ zpowers (ptB₁ he hb φ hzC hz)) :
    False := by
  have hzD₂ : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  have hzN₁ : z ∈ 𝒩₁ := le_normalizer (mem_sup_right (mem_zpowers z))
  have hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ := hC₁n z hzN₁
  have hAC : ∀ a ∈ 𝒜₁, a ∈ C₁ := fun a ha => by
    have h : a ∈ C₁ ⊓ ℬ₁ := by
      rw [hC₁B]
      exact ha
    exact (mem_inf.1 h).1
  have hcen : ∀ d ∈ D₁, ∀ a ∈ 𝒜₁, d⁻¹ * a * d = a := fun d hd a ha =>
    inv_mul_mul_eq_of_comm (hA₁c d hd a ha)
  have hcenI : ∀ d ∈ D₂, ∀ i ∈ altSub φ he, d⁻¹ * i * d = i := fun d hd i hi => by
    have h := conj_altSub_of_mem he φ hzC hz hact₂ hd hi
    calc d⁻¹ * i * d = d⁻¹ * (d * i * d⁻¹) * d := by rw [h]
      _ = i := by group
  have hstep : ∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c ∈ 𝒜₁ ⊓ 𝒜₂ → ∃ a ∈ 𝒜₁, ∃ k ∈ C₁ ⊓ D₂, c = a * k :=
    fun c hc hcj => exists_ptA_mul_of_conj_mem hb φ hKz hC₁z hzC₁ hzD₂ hD₁H hC₁B hC₁D hc hcj
  have hA₂N : ∀ g ∈ 𝒜₂, g ∈ 𝒩₁ := fun g hg =>
    radSub_le_normalizer_ptSub he hb hnd φ hzC (mem_sup_left hg)
  have hA₂z : ∀ g ∈ 𝒜₂, g * z = z * g := fun g hg => mul_comm_z hzC (pullSub_le φ _ hg)
  have hγmul : ∀ x ∈ C₁, ∀ y ∈ C₁, z⁻¹ * (x * y)⁻¹ * z * (x * y) =
      (z⁻¹ * x⁻¹ * z * x) * (z⁻¹ * y⁻¹ * z * y) := fun x hx y hy =>
    gamma_mul (hA₁c y (hC₁D hy) _ (hγA x hx)) (hA₁c _ (hC₁D (hAC _ (hγA x hx))) _ (hγA y hy))
  have hγinv : ∀ c ∈ C₁, z⁻¹ * c⁻¹⁻¹ * z * c⁻¹ = (z⁻¹ * c⁻¹ * z * c)⁻¹ := fun c hc => by
    have h := hγmul c hc c⁻¹ (inv_mem hc)
    rw [mul_inv_cancel, inv_one, mul_one, mul_one, inv_mul_cancel] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  obtain ⟨a₀, ha₀, ha₀I⟩ :=
    exists_ptA_comm_not_mem_zpowers he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker
  set i₀ := tauHom φ he (Multiplicative.ofAdd (altSym 0 0 1)) with hi₀
  have hi₀I : i₀ ∈ altSub φ he := ⟨altSym 0 0 1, symThreeDiag_altSym 0 0 1, rfl⟩
  have hi₀A : i₀ ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hi₀sq : i₀ * i₀ = 1 := by
    rw [hi₀, ← map_mul, ← ofAdd_add, symThree_add_self, ofAdd_zero, map_one]
  obtain ⟨c, hc, hca⟩ := hγsurj a₀ ha₀
  have hγc' : z⁻¹ * c⁻¹⁻¹ * z * c⁻¹ = a₀⁻¹ := by rw [hγinv c hc, hca]
  have hcI : i₀⁻¹ * c⁻¹ * i₀ ∈ C₁ := by
    have h := hC₁n i₀⁻¹ (inv_mem (hA₂N i₀ hi₀A)) c⁻¹ (inv_mem hc)
    rwa [inv_inv] at h
  have hmC : i₀⁻¹ * c⁻¹ * i₀ * c ∈ C₁ := mul_mem hcI hc
  have hγm : z⁻¹ * (i₀⁻¹ * c⁻¹ * i₀ * c)⁻¹ * z * (i₀⁻¹ * c⁻¹ * i₀ * c) =
      i₀⁻¹ * a₀⁻¹ * i₀ * a₀ := by
    have h1 := gamma_conj (z := z) (x := c⁻¹) (hA₂z _ (inv_mem hi₀A))
    rw [inv_inv] at h1
    rw [hγmul _ hcI c hc, h1, hγc', hca]
  have hγmJ : z⁻¹ * (i₀⁻¹ * c⁻¹ * i₀ * c)⁻¹ * z * (i₀⁻¹ * c⁻¹ * i₀ * c) ∈ 𝒜₁ ⊓ 𝒜₂ := by
    rw [hγm]
    have h := comm_mem_ptA_inf_radA he hb hnd φ hzC hinf hz (inv_mem ha₀) (inv_mem hi₀A)
    simpa only [inv_inv] using h
  obtain ⟨a, ha, k, hk, hmak⟩ := hstep _ hmC hγmJ
  have hkD₁ : k ∈ D₁ := hC₁D (mem_inf.1 hk).1
  have hkD₂ : k ∈ D₂ := (mem_inf.1 hk).2
  have hx : c⁻¹ * i₀ * c = i₀ * (a * k) := by
    rw [← hmak]
    group
  have hcl : ∀ g ∈ 𝒜₂, a⁻¹ * g⁻¹ * a * g ∈ altSub φ he := by
    intro g hg
    have hgc : g⁻¹ * c * g ∈ C₁ := by
      have h := hC₁n g⁻¹ (inv_mem (hA₂N g hg)) c hc
      rwa [inv_inv] at h
    have hm'C : g⁻¹ * c * g * c⁻¹ ∈ C₁ := mul_mem hgc (inv_mem hc)
    have hγm' : z⁻¹ * (g⁻¹ * c * g * c⁻¹)⁻¹ * z * (g⁻¹ * c * g * c⁻¹) ∈ 𝒜₁ ⊓ 𝒜₂ := by
      have h1 := gamma_conj (z := z) (x := c) (hA₂z _ (inv_mem hg))
      rw [inv_inv] at h1
      rw [hγmul _ hgc _ (inv_mem hc), h1, hca, hγc']
      have h := comm_mem_ptA_inf_radA he hb hnd φ hzC hinf hz ha₀ (inv_mem hg)
      simpa only [inv_inv] using h
    obtain ⟨a', ha', k', hk', hm'ak⟩ := hstep _ hm'C hγm'
    have hk'D₁ : k' ∈ D₁ := hC₁D (mem_inf.1 hk').1
    have hk'D₂ : k' ∈ D₂ := (mem_inf.1 hk').2
    have hcg : c * g * c⁻¹ = g * (a' * k') := by
      rw [← hm'ak]
      group
    have hj₁A : i₀⁻¹ * a'⁻¹ * i₀ * a' ∈ 𝒜₁ := by
      have h := comm_mem_ptA_inf_radA he hb hnd φ hzC hinf hz (inv_mem ha') (inv_mem hi₀A)
      simp only [inv_inv] at h
      exact (mem_inf.1 h).1
    have hj₁I : i₀⁻¹ * a'⁻¹ * i₀ * a' ∈ altSub φ he := by
      have h := conj_mem_altSub he φ hzC hz hact₂ hprod₂ σ hσ
        (ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left (inv_mem ha'))) hi₀I
      rw [inv_inv] at h
      have h2 := mul_mem (inv_mem hi₀I) h
      have h3 : i₀⁻¹ * (a'⁻¹ * i₀ * a') = i₀⁻¹ * a'⁻¹ * i₀ * a' := by group
      rwa [h3] at h2
    have hgi₀ : g⁻¹ * i₀ * g = i₀ := inv_mul_mul_eq_of_comm (radA_comm he φ hg hi₀A)
    have hx1 : (c⁻¹ * i₀ * c)⁻¹ * g⁻¹ * (c⁻¹ * i₀ * c) * g = i₀⁻¹ * a'⁻¹ * i₀ * a' := by
      calc (c⁻¹ * i₀ * c)⁻¹ * g⁻¹ * (c⁻¹ * i₀ * c) * g =
          c⁻¹ * (i₀⁻¹ * (c * g * c⁻¹)⁻¹ * i₀ * (c * g * c⁻¹)) * c := by group
        _ = c⁻¹ * (i₀⁻¹ * (g * (a' * k'))⁻¹ * i₀ * (g * (a' * k'))) * c := by rw [hcg]
        _ = c⁻¹ * (i₀⁻¹ * (k'⁻¹ * (a'⁻¹ * (g⁻¹ * i₀ * g) * a') * k')) * c := by group
        _ = c⁻¹ * (i₀⁻¹ * (k'⁻¹ * (i₀ * (i₀⁻¹ * a'⁻¹ * i₀ * a')) * k')) * c := by
          rw [hgi₀]
          group
        _ = c⁻¹ * (i₀⁻¹ * ((k'⁻¹ * i₀ * k') * (k'⁻¹ * (i₀⁻¹ * a'⁻¹ * i₀ * a') * k'))) * c := by
          group
        _ = c⁻¹ * (i₀⁻¹ * a'⁻¹ * i₀ * a') * c := by
          rw [hcenI k' hk'D₂ i₀ hi₀I, hcen k' hk'D₁ _ hj₁A]
          group
        _ = i₀⁻¹ * a'⁻¹ * i₀ * a' := hcen c (hC₁D hc) _ hj₁A
    have hj₂A : a⁻¹ * g⁻¹ * a * g ∈ 𝒜₁ := by
      have h := comm_mem_ptA_inf_radA' he hb hnd φ hzC hinf hz (inv_mem ha) (inv_mem hg)
      simp only [inv_inv] at h
      exact (mem_inf.1 h).1
    have hgi₀' : i₀⁻¹ * g⁻¹ * i₀ = g⁻¹ := inv_mul_mul_eq_of_comm (radA_comm he φ hi₀A (inv_mem hg))
    have hx2 : (c⁻¹ * i₀ * c)⁻¹ * g⁻¹ * (c⁻¹ * i₀ * c) * g =
        (a⁻¹ * g⁻¹ * a * g) * (k⁻¹ * g⁻¹ * k * g) := by
      calc (c⁻¹ * i₀ * c)⁻¹ * g⁻¹ * (c⁻¹ * i₀ * c) * g =
          (i₀ * (a * k))⁻¹ * g⁻¹ * (i₀ * (a * k)) * g := by rw [hx]
        _ = k⁻¹ * a⁻¹ * (i₀⁻¹ * g⁻¹ * i₀) * a * k * g := by group
        _ = k⁻¹ * (a⁻¹ * g⁻¹ * a * g) * k * (k⁻¹ * g⁻¹ * k * g) := by
          rw [hgi₀']
          group
        _ = (a⁻¹ * g⁻¹ * a * g) * (k⁻¹ * g⁻¹ * k * g) := by rw [hcen k hkD₁ _ hj₂A]
    have hj₃ := comm_mem_altSub_of_mem he φ hzC hz hact₂ hkD₂ hg
    have h2 : a⁻¹ * g⁻¹ * a * g = (i₀⁻¹ * a'⁻¹ * i₀ * a') * (k⁻¹ * g⁻¹ * k * g)⁻¹ := by
      rw [← hx1, hx2, mul_inv_cancel_right]
    rw [h2]
    exact mul_mem hj₁I (inv_mem hj₃)
  have haA₂ : a ∈ 𝒜₂ := mem_radA_of_comm_mem_altSub he hb hnd φ hzC hsup hinf hz σ hσ hσcol
    hσker ha (hcl _ ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩)) (hcl _ ((mem_pullSub_iff φ he).2 ⟨_, rfl⟩))
  have hki₀ : k * i₀ = i₀ * k := by
    have h := conj_altSub_of_mem he φ hzC hz hact₂ hkD₂ hi₀I
    calc k * i₀ = k * i₀ * k⁻¹ * k := by group
      _ = i₀ * k := by rw [h]
  have hi₀inv : i₀⁻¹ = i₀ := inv_eq_of_mul_eq_one_right hi₀sq
  have hcomm : (c⁻¹ * i₀ * c) * i₀⁻¹ = i₀⁻¹ * (c⁻¹ * i₀ * c) := by
    rw [hx, hi₀inv]
    calc i₀ * (a * k) * i₀ = i₀ * a * (k * i₀) := by group
      _ = i₀ * a * (i₀ * k) := by rw [hki₀]
      _ = i₀ * (a * i₀) * k := by group
      _ = i₀ * (i₀ * a) * k := by rw [radA_comm he φ haA₂ hi₀A]
      _ = i₀ * (i₀ * (a * k)) := by group
  have hm2 : (i₀⁻¹ * c⁻¹ * i₀ * c) ^ 2 = 1 := by
    have hxx : (c⁻¹ * i₀ * c) * (c⁻¹ * i₀ * c) = 1 := by
      calc (c⁻¹ * i₀ * c) * (c⁻¹ * i₀ * c) = c⁻¹ * (i₀ * i₀) * c := by group
        _ = 1 := by rw [hi₀sq]; group
    rw [sq]
    calc i₀⁻¹ * c⁻¹ * i₀ * c * (i₀⁻¹ * c⁻¹ * i₀ * c) =
        i₀⁻¹ * ((c⁻¹ * i₀ * c) * i₀⁻¹) * (c⁻¹ * i₀ * c) := by group
      _ = i₀⁻¹ * (i₀⁻¹ * (c⁻¹ * i₀ * c)) * (c⁻¹ * i₀ * c) := by rw [hcomm]
      _ = (i₀ * i₀)⁻¹ * ((c⁻¹ * i₀ * c) * (c⁻¹ * i₀ * c)) := by group
      _ = 1 := by rw [hi₀sq, hxx, inv_one, one_mul]
  have h := hα1 _ hmC hm2
  apply ha₀I
  rw [← hγm]
  have h3 : z⁻¹ * (i₀⁻¹ * c⁻¹ * i₀ * c)⁻¹ * z * (i₀⁻¹ * c⁻¹ * i₀ * c) =
      z⁻¹ * ((i₀⁻¹ * c⁻¹ * i₀ * c)⁻¹ * z * (i₀⁻¹ * c⁻¹ * i₀ * c)) := by group
  rw [h3]
  exact h

include hσ hσker in
theorem kappa_eq_zero_of_comm [Finite G] {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    {κ κ₂ : ZMod 2}
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (hκ : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε)))
    {g : G} (hgz : g⁻¹ * z * g = z * ptB₁ he hb φ hzC hz)
    (hcomA : ∀ a ∈ 𝒜₂, g⁻¹ * a⁻¹ * g * a ∈ zpowers (ptB₁ he hb φ hzC hz)) :
    g ∈ D₂ ∧ κ₂ = 0 := by
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  have hb₁A := ptB₁_mem_radA he hb φ hzC hz
  have hb₁inv : (ptB₁ he hb φ hzC hz)⁻¹ = ptB₁ he hb φ hzC hz := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ← hb₁ord, pow_orderOf_eq_one]
  have hgR : g ∈ 𝒩₂ := by
    have hmap : (radSub φ z e).map (MulAut.conj g⁻¹).toMonoidHom ≤ radSub φ z e := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) ?_
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have h2 : g⁻¹ * a * g = a * (g⁻¹ * a⁻¹ * g * a)⁻¹ := by group
        rw [h2]
        exact mem_sup_left (mul_mem ha (inv_mem (zpowers_le.2 hb₁A (hcomA a ha))))
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgz]
        exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hb₁A)
    have h := inv_mem (mem_normalizer_of_map_le hmap)
    rwa [inv_inv] at h
  have hgI : ∀ x ∈ altSub φ he, g * x * g⁻¹ = x := by
    intro x hx
    have hxA : x ∈ 𝒜₂ := by
      obtain ⟨B, -, rfl⟩ := hx
      exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
    have h1 := hcomA x hxA
    have h2 : g⁻¹ * x * g ∈ altSub φ he := by
      have h := conj_mem_altSub he φ hzC hz hact₂ hprod₂ σ hσ (inv_mem hgR) hx
      rwa [inv_inv] at h
    have h3 : (g⁻¹ * x⁻¹ * g * x)⁻¹ ∈ altSub φ he := by
      have h4 : (g⁻¹ * x⁻¹ * g * x)⁻¹ = x⁻¹ * (g⁻¹ * x * g) := by group
      rw [h4]
      exact mul_mem (inv_mem hx) h2
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord h1 with h | h
    · calc g * x * g⁻¹ = x * (g * (g⁻¹ * x⁻¹ * g * x)) * g⁻¹ := by group
        _ = x := by rw [h]; group
    · exfalso
      rw [h, hb₁inv] at h3
      exact ptB₁_not_mem_altSub he hb φ hzC hz h3
  have hgD₂ : g ∈ D₂ :=
    mem_of_centralizes_altSub he φ hzC hz hact₂ hRD₂ hprod₂ σ hσ hσker hgR hgI
  refine ⟨hgD₂, ?_⟩
  have hlab : g⁻¹ * z * g = radHom φ he hzC hz (Multiplicative.ofAdd (symE₁₁, 1)) := by
    rw [hgz, radHom_one_eq φ he hzC hz, ptB₁_eq_tauHom]
  have hτ := hκ g hgD₂ symE₁₁ symE₂₂ 0 hlab
  rw [radHom_tau, radHom_tau] at hτ
  have hτA : tauHom φ he (Multiplicative.ofAdd symE₂₂) ∈ 𝒜₂ := (mem_pullSub_iff φ he).2 ⟨_, rfl⟩
  have hc := hcomA _ hτA
  have hconjτ : g⁻¹ * tauHom φ he (Multiplicative.ofAdd symE₂₂) * g =
      tauHom φ he (Multiplicative.ofAdd symE₂₂) *
        (g⁻¹ * (tauHom φ he (Multiplicative.ofAdd symE₂₂))⁻¹ * g *
          tauHom φ he (Multiplicative.ofAdd symE₂₂))⁻¹ := by group
  have hX : symThreeDiag ((symE₁₁ : ↥(binarySymMatrices 3)) : M₃) = ![1, 0, 0] :=
    symThreeDiag_jMat 1 0 0
  have hY : symThreeDiag ((symE₂₂ : ↥(binarySymMatrices 3)) : M₃) = ![0, 1, 0] := by
    funext k
    fin_cases k <;> rfl
  rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hc with h | h
  · rw [h, inv_one, mul_one] at hconjτ
    rw [hconjτ] at hτ
    have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he hτ))
    change (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃) = !![0, 0, 0; 0, 1, 0; 0, 0, 0] +
      κ₂ • symThreePolar (symThreeDiag ((symE₁₁ : ↥(binarySymMatrices 3)) : M₃))
        (symThreeDiag ((symE₂₂ : ↥(binarySymMatrices 3)) : M₃)) +
          (0 : ZMod 2) • !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] at h1
    rw [hX, hY] at h1
    exact zmod_two_kappa_E22 κ₂ h1
  · exfalso
    rw [h, hb₁inv, ptB₁_eq_tauHom, ← map_mul, ← ofAdd_add] at hconjτ
    rw [hconjτ] at hτ
    have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he hτ))
    change (!![0, 0, 0; 0, 1, 0; 0, 0, 0] : M₃) + !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] =
      !![0, 0, 0; 0, 1, 0; 0, 0, 0] +
      κ₂ • symThreePolar (symThreeDiag ((symE₁₁ : ↥(binarySymMatrices 3)) : M₃))
        (symThreeDiag ((symE₂₂ : ↥(binarySymMatrices 3)) : M₃)) +
          (0 : ZMod 2) • !![(1 : ZMod 2), 0, 0; 0, 0, 0; 0, 0, 0] at h1
    rw [hX, hY] at h1
    exact zmod_two_kappa_E22' κ₂ h1

end Sigma

include hnd hsup hinf in
theorem comm_mem_zpowers_of_fixed [Finite G] {D₁ : Subgroup G}
    (hA₁c : ∀ d ∈ D₁, ∀ a ∈ 𝒜₁, d * a = a * d)
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    {g : G} (hgD : g ∈ D₁) (hgz : g⁻¹ * z * g = z * ptB₁ he hb φ hzC hz)
    (hfix : ∀ s : bilinIsometryGroup (b.restrict 𝔼),
      g⁻¹ * (ptLevi he hb φ s * g * (ptLevi he hb φ s)⁻¹) ∈ zpowers (ptB₁ he hb φ hzC hz))
    {x : G} (hx : x ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G)) :
    g⁻¹ * x⁻¹ * g * x ∈ zpowers (ptB₁ he hb φ hzC hz) := by
  obtain ⟨s, b', hb', rfl⟩ := exists_ptLevi_mul he hb hnd φ hzC hsup hinf hz hx
  have h1 := hfix s⁻¹
  rw [map_inv, inv_inv] at h1
  set i := g⁻¹ * ((ptLevi he hb φ s)⁻¹ * g * ptLevi he hb φ s) with hi
  have hb'N : b' ∈ 𝒩₁ := le_normalizer hb'
  have hib : b' * i = i * b' := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h1
    rw [← hn]
    exact ((Commute.zpow_right (hb₁c b' hb'N) n) : _)
  obtain ⟨v, ε, rfl⟩ := (mem_ptSub_iff he hb φ hzC hz).1 hb'
  set a := ((φ.symm (ptHomV he hb (Multiplicative.ofAdd v)) : L) : G) with ha_def
  have ha : a ∈ 𝒜₁ := (mem_ptA_iff he hb φ).2 ⟨v, rfl⟩
  have hag : a * g = g * a := (hA₁c g hgD a ha).symm
  have hj : g⁻¹ * (zPow z ε)⁻¹ * g * zPow z ε ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    rcases zmod_two_eq_zero_or_eq_one ε with rfl | rfl
    · have h0 : g⁻¹ * (zPow z 0)⁻¹ * g * zPow z 0 = 1 := by
        rw [zPow_zero]
        group
      rw [h0]
      exact one_mem _
    · rw [zPow_one]
      have h2 : g⁻¹ * z⁻¹ * g * z = (ptB₁ he hb φ hzC hz)⁻¹ := by
        calc g⁻¹ * z⁻¹ * g * z = (g⁻¹ * z * g)⁻¹ * z := by group
          _ = (ptB₁ he hb φ hzC hz)⁻¹ := by rw [hgz]; group
      rw [h2]
      exact inv_mem (mem_zpowers _)
  have h3 : g⁻¹ * (ptLevi he hb φ s * (a * zPow z ε))⁻¹ * g *
      (ptLevi he hb φ s * (a * zPow z ε)) =
      (g⁻¹ * (zPow z ε)⁻¹ * g * zPow z ε) * ((a * zPow z ε)⁻¹ * i * (a * zPow z ε)) := by
    have hag' : a⁻¹ * g = g * a⁻¹ := by
      calc a⁻¹ * g = a⁻¹ * (g * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * g) * a⁻¹ := by rw [hag]
        _ = g * a⁻¹ := by group
    rw [hi]
    calc g⁻¹ * (ptLevi he hb φ s * (a * zPow z ε))⁻¹ * g * (ptLevi he hb φ s * (a * zPow z ε)) =
        g⁻¹ * (zPow z ε)⁻¹ * (a⁻¹ * g) * ((g⁻¹ * ((ptLevi he hb φ s)⁻¹ * g *
          ptLevi he hb φ s)) * (a * zPow z ε)) := by group
      _ = g⁻¹ * (zPow z ε)⁻¹ * (g * a⁻¹) * ((g⁻¹ * ((ptLevi he hb φ s)⁻¹ * g *
          ptLevi he hb φ s)) * (a * zPow z ε)) := by rw [hag']
      _ = _ := by group
  have h4 : (a * zPow z ε)⁻¹ * i * (a * zPow z ε) = i := by
    rw [mul_assoc, ← hib, inv_mul_cancel_left]
  rw [h3, h4]
  exact mul_mem hj h1


section Main

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

include hnd hsup hinf hσ hσcol hσker in
theorem degree64_central_lift [Finite G] [FiniteDimensional (ZMod 2) V] {D₁ D₂ : Subgroup G}
    {ν₁ : G → 𝔼 × ZMod 2} {ν₂ : G → ↥(binarySymMatrices 3)} {κ κ₂ lam : ZMod 2}
    (hlam : lam = 0)
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hBD₁ : ℬ₁ ≤ D₁)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hν₁z : ∀ d ∈ D₁, d⁻¹ * z * d = ptHom he hb φ hzC hz (Multiplicative.ofAdd (ν₁ d, 1)))
    (hν₁surj : ∀ v : 𝔼 × ZMod 2, ∃ d ∈ D₁, ν₁ d = v)
    (hact₁ : ∀ d ∈ D₁, ∀ (v : 𝔼 × ZMod 2) (ε : ZMod 2),
      d⁻¹ * ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, ε)) * d =
        ptHom he hb φ hzC hz (Multiplicative.ofAdd
          (v + (lam * b ((ν₁ d).1 : V) (v.1 : V)) • ((0 : 𝔼), (1 : ZMod 2)) + ε • ν₁ d, ε)))
    (hprod₁ : ∀ m ∈ 𝒩₁, ∃ d ∈ D₁, ∃ c ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      m = d * c)
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    (hD₂N : D₂ ≤ 𝒩₂) (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hν₂eq : ∀ d ∈ D₂, ∀ d' ∈ D₂, ν₂ d = ν₂ d' ↔ d⁻¹ * d' ∈ ℛ)
    (hν₂surj : ∀ C : ↥(binarySymMatrices 3), ∃ d ∈ D₂, ν₂ d = C)
    (hact₂ : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ • symThreePolarSym
          (symThreeDiag (ν₂ d : M₃)) (symThreeDiag (B : M₃)) + ε • ν₂ d, ε)))
    (hRD₂ : ℛ ≤ D₂) (hprod₂ : ∀ m ∈ 𝒩₂, ∃ d ∈ D₂, ∃ c ∈ 𝒩₂₀, m = d * c)
    (hκ₂ : ∀ d ∈ D₂, ∀ (C B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (C, 1)) →
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + κ₂ • symThreePolarSym
          (symThreeDiag (C : M₃)) (symThreeDiag (B : M₃)) + ε • C, ε))) :
    κ₂ = 0 ∧ ∃ C₁ : Subgroup G, C₁ ≤ D₁ ∧ (∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁) ∧
      Nat.card C₁ = 1024 ∧ zpowers z ⊔ C₁ = D₁ ∧ C₁ ⊓ ℬ₁ = 𝒜₁ ∧
      closure {x | ∃ y ∈ C₁, y ^ 2 = x} ≤ zpowers (ptB₁ he hb φ hzC hz) ∧
      (∀ x ∈ C₁, z⁻¹ * (x⁻¹ * z * x) ∈ zpowers (ptB₁ he hb φ hzC hz) →
        ∀ y ∈ C₁, x * y = y * x) ∧
      Nat.card ↥((C₁ : Set G) ∩ {d | d ∈ D₁ ∧
        z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)}) = 64 ∧
      ∃ e₀ ∈ C₁, z⁻¹ * (e₀⁻¹ * z * e₀) = ptB₁ he hb φ hzC hz ∧
        (∀ x ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
          e₀⁻¹ * x⁻¹ * e₀ * x ∈ zpowers (ptB₁ he hb φ hzC hz)) ∧ e₀ ∈ D₂ := by
  have hb' : (b.restrict 𝔼).IsAlt := fun x => hb x
  have hnd' : (b.restrict 𝔼).Nondegenerate :=
    hb.restrict_nondegenerate_orthogonal_span_pair (bilin_f_u he) hnd
  have hb₁ord := orderOf_ptB₁ he hb φ hzC hz
  obtain ⟨C₁, τ₁, α, β, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hτz, hτmul, hτsurj, hτker, hτs, hEc,
    hEcard, -, hCC, hα1, hα0⟩ :=
    degree64_central_point he hb hnd φ hzC hsup hinf hz hlam hD₁N hD₁n hBD₁ hν₁surj hact₁ hprod₁
  have hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j := fun j hj =>
    exists_mem_inf_conj_eq he hb hnd φ hzC hsup hinf hz hD₂N hD₂n hν₂z hν₂eq hν₂surj hact₂ hRD₂
      hD₁n hBD₁ hν₁z hact₁ hprod₁ hj
  subst hlam
  have hA₁c : ∀ d ∈ D₁, ∀ a ∈ 𝒜₁, d * a = a * d := by
    intro d hd a ha
    obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 ha
    have h := hact₁ d hd v 0
    rw [zero_mul, zero_smul, add_zero, zero_smul, add_zero, ptHom_pt] at h
    exact comm_of_inv_mul_mul_eq h
  have hγA : ∀ c ∈ C₁, z⁻¹ * c⁻¹ * z * c ∈ 𝒜₁ := fun c hc => by
    rw [hτz c hc, ptHom_pt]
    exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
  have hγsurj : ∀ a ∈ 𝒜₁, ∃ c ∈ C₁, z⁻¹ * c⁻¹ * z * c = a := fun a ha => by
    obtain ⟨v, rfl⟩ := (mem_ptA_iff he hb φ).1 ha
    obtain ⟨c, hc, hcv⟩ := hτsurj v
    exact ⟨c, hc, by rw [hτz c hc, hcv, ptHom_pt]⟩
  have hα : α = 0 := by
    rcases zmod_two_eq_zero_or_eq_one α with h | h
    · exact h
    · exact (false_of_alpha_eq_one he hb hnd φ hzC hsup hinf hz σ hσ hσcol hσker hact₂ hRD₂
        hprod₂ hD₁H hA₁c hKz hC₁D hC₁n hC₁z hC₁B hγA hγsurj (hα1 h)).elim
  have hsq₀ := hα0 hα
  have hAC : 𝒜₁ ≤ C₁ := fun a ha => by
    have h : a ∈ C₁ ⊓ ℬ₁ := by
      rw [hC₁B]
      exact ha
    exact (mem_inf.1 h).1
  have hptA : ∀ v : 𝔼 × ZMod 2, ptHom he hb φ hzC hz (Multiplicative.ofAdd (v, 0)) ∈ 𝒜₁ :=
    fun v => by
      rw [ptHom_pt]
      exact (mem_ptA_iff he hb φ).2 ⟨_, rfl⟩
  have hIA : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ := zpowers_le.2 (hptA _)
  have hpt : ∀ (w : 𝔼) (t : ZMod 2),
      (ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, 0), 0)))⁻¹ *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, t), 0)) ∈
          zpowers (ptB₁ he hb φ hzC hz) := by
    intro w t
    have h : (ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, 0), 0)))⁻¹ *
        ptHom he hb φ hzC hz (Multiplicative.ofAdd ((w, t), 0)) =
          ptHom he hb φ hzC hz (Multiplicative.ofAdd (((0 : 𝔼), t), 0)) := by
      rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
      congr 2
      ext <;> simp
    rw [h]
    rcases zmod_two_eq_zero_or_eq_one t with rfl | rfl
    · rw [Prod.mk_zero_zero, Prod.mk_zero_zero, ofAdd_zero, map_one]
      exact one_mem _
    · exact mem_zpowers _
  have hℓI : ∀ (s : bilinIsometryGroup (b.restrict 𝔼)), ∀ i ∈ zpowers (ptB₁ he hb φ hzC hz),
      ptLevi he hb φ s * i * (ptLevi he hb φ s)⁻¹ ∈ zpowers (ptB₁ he hb φ hzC hz) := by
    intro s i hi
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hi
    have h : ptLevi he hb φ s * ptB₁ he hb φ hzC hz ^ n = ptB₁ he hb φ hzC hz ^ n *
        ptLevi he hb φ s :=
      Commute.zpow_right (hb₁c _ (ptLevi_mem_normalizer he hb φ hzC hz s)) n
    rw [h, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) n
  have hκinj : ∀ x : 𝔼, ptHom he hb φ hzC hz (Multiplicative.ofAdd ((x, 0), 0)) ∈
      zpowers (ptB₁ he hb φ hzC hz) → x = 0 := by
    intro x hx
    rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers hb₁ord hx with h | h
    · rw [← map_one (ptHom he hb φ hzC hz), ← ofAdd_zero] at h
      have h2 := Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h)
      exact congrArg (fun p => p.1.1) h2
    · have h2 := Multiplicative.ofAdd.injective (ptHom_injective he hb φ hzC hz hinf h)
      have h3 : (0 : ZMod 2) = 1 := congrArg (fun p => p.1.2) h2
      exact absurd h3 (by decide)
  obtain ⟨e₀, he₀C, hρe, hfix⟩ := exists_fixed_lift_of_group (Q := ptQuad e) hb' hnd'
    (polarBilin_ptQuad he) (C := C₁) (I := zpowers (ptB₁ he hb φ hzC hz))
    (fun i hi c hc => (hA₁c c (hC₁D hc) i (hIA hi)).symm)
    (fun x hx y hy => hCC (commutator_mem_commutator hx hy))
    (fun x hx => hsq₀ (subset_closure ⟨x, hx, rfl⟩))
    (ptLevi he hb φ) (fun s c hc => hC₁n _ (ptLevi_mem_normalizer he hb φ hzC hz s) c hc) hℓI
    (fun x => ptHom he hb φ hzC hz (Multiplicative.ofAdd ((x, 0), 0))) (fun x => hAC (hptA _))
    (fun x y => by
      rw [show ((x + y, (0 : ZMod 2)), (0 : ZMod 2)) = ((x, 0), 0) + ((y, 0), 0) by simp,
        ofAdd_add, map_mul, inv_mul_cancel]
      exact one_mem _)
    hκinj
    (fun s x => by
      rw [ptLevi_conj_ptHom he hb φ hzC hz s (x, 0) 0, OddQuadraticFive.hV_apply]
      exact hpt _ _)
    τ₁ hτmul hτsurj (fun s c hc => hτs s c hc)
    (fun i hi => (hτker i (hAC (hIA hi))).2 (hIA hi))
    (fun x => (hτker _ (hAC (hptA _))).2 (hptA _))
    (fun c hc hc0 => by
      obtain ⟨⟨w, t⟩, hv⟩ := (mem_ptA_iff he hb φ).1 ((hτker c hc).1 hc0)
      refine ⟨w, ?_⟩
      rw [← hv, ← ptHom_pt he hb φ hzC hz]
      exact hpt w t)
  have hγe : z⁻¹ * e₀⁻¹ * z * e₀ = ptB₁ he hb φ hzC hz := by
    rw [hτz e₀ he₀C, hρe]
  have hgz : e₀⁻¹ * z * e₀ = z * ptB₁ he hb φ hzC hz := by
    rw [← hγe]
    group
  have hcomN : ∀ x ∈ (𝒩₁ ⊓ centralizer ({z} : Set G) : Subgroup G),
      e₀⁻¹ * x⁻¹ * e₀ * x ∈ zpowers (ptB₁ he hb φ hzC hz) := fun x hx =>
    comm_mem_zpowers_of_fixed he hb hnd φ hzC hsup hinf hz hA₁c hb₁c (hC₁D he₀C) hgz hfix hx
  have hcomA : ∀ a ∈ 𝒜₂, e₀⁻¹ * a⁻¹ * e₀ * a ∈ zpowers (ptB₁ he hb φ hzC hz) := fun a ha =>
    hcomN a (mem_inf.2 ⟨radSub_le_normalizer_ptSub he hb hnd φ hzC (mem_sup_left ha),
      radSub_le_centralizer φ hsup (mem_sup_left ha)⟩)
  obtain ⟨he₀D₂, hκ0⟩ := kappa_eq_zero_of_comm he hb φ hzC hz σ hσ hσker hact₂ hRD₂ hprod₂ hκ₂
    hgz hcomA
  refine ⟨hκ0, C₁, hC₁D, hC₁n, hC₁c, hC₁z, hC₁B, hsq₀, hEc, hEcard, e₀, he₀C, ?_, hcomN,
    he₀D₂⟩
  rw [← hγe]
  group

end Main

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
