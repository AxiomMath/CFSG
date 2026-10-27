module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64MiddleElementary

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

section Generic

variable {X : Type*} [Group X]

theorem natCard_sup_mul_inf {H N : Subgroup X} (hHN : H ≤ normalizer (N : Set X)) :
    Nat.card (H ⊔ N : Subgroup X) * Nat.card (H ⊓ N : Subgroup X) =
      Nat.card H * Nat.card N := by
  have : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have : (N.subgroupOf (H ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  have h1 : N.relIndex (H ⊔ N) = N.relIndex H := (Nat.card_congr e.toEquiv).symm
  have h2 := Subgroup.relIndex_mul_card (H := N) (K := H ⊔ N)
  have h3 := Subgroup.relIndex_mul_card (H := N) (K := H)
  rw [inf_of_le_left le_sup_right] at h2
  rw [inf_comm] at h3
  rw [← h2, ← h3, h1]
  ring

theorem gamma_mul_eq (z x y : X) :
    z⁻¹ * ((x * y)⁻¹ * z * (x * y)) =
      (z⁻¹ * (y⁻¹ * z * y)) * (y⁻¹ * (z⁻¹ * (x⁻¹ * z * x)) * y) := by
  group

theorem gamma_conj_eq (z x v : X) :
    z⁻¹ * ((x * v * x⁻¹)⁻¹ * z * (x * v * x⁻¹)) =
      x * ((z⁻¹ * (x⁻¹ * z * x))⁻¹ * (z⁻¹ * (v⁻¹ * z * v)) *
        (v⁻¹ * (z⁻¹ * (x⁻¹ * z * x)) * v)) * x⁻¹ := by
  group

theorem comm_eq_sq_mul_sq (x y : X) :
    x⁻¹ * y⁻¹ * x * y = (x ^ 2)⁻¹ * (x * y⁻¹) ^ 2 * y ^ 2 := by
  rw [sq, sq, sq]
  group

theorem comm_mem_of_sq_mem {C K : Subgroup X} (hsq : ∀ y ∈ C, y ^ 2 ∈ K) {c d : X}
    (hc : c ∈ C) (hd : d ∈ C) : c⁻¹ * d⁻¹ * c * d ∈ K := by
  rw [comm_eq_sq_mul_sq]
  exact mul_mem (mul_mem (inv_mem (hsq c hc)) (hsq _ (mul_mem hc (inv_mem hd)))) (hsq d hd)

theorem mem_normalizer_of_conj_mem [Finite X] {Y : Subgroup X} {g : X}
    (h : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) : g ∈ normalizer (Y : Set X) := by
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨y, hy, rfl⟩
  exact h y hy

end Generic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

theorem elemAbelian_of_sq_eq_one {X : Subgroup G} (hX : ∀ x ∈ X, x ^ 2 = 1) :
    IsElementaryAbelian 2 X :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (comm_of_sq_eq_one hX a.2 b.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hX g g.2) }

omit hb in
include hinf hz in
theorem z_not_mem_radA : z ∉ 𝒜₂ := fun h => by
  have h1 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨pullSub_le φ _ h, mem_zpowers z⟩
  rw [hinf, mem_bot] at h1
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

include hinf hz in
theorem z_not_mem_ptA : z ∉ 𝒜₁ := fun h => by
  have h1 : z ∈ L ⊓ zpowers z := mem_inf.2 ⟨pullSub_le φ _ h, mem_zpowers z⟩
  rw [hinf, mem_bot] at h1
  rw [h1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem ptA_le_of_inf_eq {C₁ : Subgroup G} (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) : 𝒜₁ ≤ C₁ := by
  rw [← hC₁B]
  exact inf_le_left

theorem radA_le_of_inf_eq {C₂ : Subgroup G} (hC₂R : C₂ ⊓ ℛ = 𝒜₂) : 𝒜₂ ≤ C₂ := by
  rw [← hC₂R]
  exact inf_le_left

omit hb in
include hinf hz in
theorem z_not_mem_of_inf_eq {C₂ : Subgroup G} (hC₂R : C₂ ⊓ ℛ = 𝒜₂) : z ∉ C₂ := fun h => by
  have h1 : z ∈ C₂ ⊓ ℛ := mem_inf.2 ⟨h, mem_sup_right (mem_zpowers z)⟩
  rw [hC₂R] at h1
  exact z_not_mem_radA φ hinf hz h1

omit hb in
theorem P_le_and_elemAbelian {C₁ D₂ C₂ : Subgroup G} (hC₂R : C₂ ⊓ ℛ = 𝒜₂)
    (hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂) (hC₂sq : ∀ c ∈ C₂, c ^ 2 = 1) :
    𝒜₂ ⊔ (C₁ ⊓ D₂) ≤ C₂ ∧ IsElementaryAbelian 2 (𝒜₂ ⊔ (C₁ ⊓ D₂) : Subgroup G) := by
  have hle : 𝒜₂ ⊔ (C₁ ⊓ D₂) ≤ C₂ := sup_le (radA_le_of_inf_eq φ hC₂R) (by
    rw [← hC₁C₂]
    exact inf_le_right)
  exact ⟨hle, elemAbelian_of_sq_eq_one fun x hx => hC₂sq x (hle hx)⟩

include he hnd hzC hinf hz in
theorem card_Q₀ [Finite G] {C₁ D₁ D₂ F₁ : Subgroup G}
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hF₁ : ∀ d : G, d ∈ F₁ ↔ d ∈ D₁ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ zpowers (ptB₁ he hb φ hzC hz)) :
    Nat.card ((C₁ ⊓ D₂) ⊓ F₁ : Subgroup G) = 16 := by
  have hzD₂ : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  have hJ := C₁_inf_D₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B
  have hI : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ ⊓ 𝒜₂ := zpowers_ptB₁_le he hb φ hzC hz
  have hconj : conjClass ((C₁ ⊓ D₂) ⊓ F₁) z =
      z • ((zpowers (ptB₁ he hb φ hzC hz) : Subgroup G) : Set G) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_conjClass_iff_right.1 hx
      refine ⟨z⁻¹ * (k⁻¹ * z * k), ((hF₁ k).1 (mem_inf.1 hk).2).2, ?_⟩
      change z * (z⁻¹ * (k⁻¹ * z * k)) = k⁻¹ * z * k
      group
    · rintro _ ⟨j, hj, rfl⟩
      obtain ⟨k, hk, hkz⟩ := exists_mem_inf_conj_eq_of_sup hb φ hKz hC₁z hzC₁ hzD₂ (hI hj)
      have hkF : k ∈ F₁ := (hF₁ k).2 ⟨hC₁D (mem_inf.1 hk).1, by
        rw [hkz, inv_mul_cancel_left]
        exact hj⟩
      change z * j ∈ conjClass ((C₁ ⊓ D₂) ⊓ F₁) z
      exact mem_conjClass_iff_right.2 ⟨k, mem_inf.2 ⟨hk, hkF⟩, hkz⟩
  have hcen : ((C₁ ⊓ D₂) ⊓ F₁) ⊓ centralizer ({z} : Set G) = 𝒜₁ ⊓ 𝒜₂ := by
    apply le_antisymm
    · rw [← hJ]
      exact inf_le_inf_right _ inf_le_left
    · intro x hx
      rw [← hJ] at hx
      obtain ⟨hxK, hxz⟩ := mem_inf.1 hx
      have hxF : x ∈ F₁ := by
        refine (hF₁ x).2 ⟨hC₁D (mem_inf.1 hxK).1, ?_⟩
        have h : x⁻¹ * z * x = z := by
          rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hxz, inv_mul_cancel_left]
        rw [h, inv_mul_cancel]
        exact one_mem _
      exact mem_inf.2 ⟨mem_inf.2 ⟨hxK, hxF⟩, hxz⟩
  rw [card_eq_card_conjClass_mul _ z, hconj, card_smul_set, SetLike.coe_sort_coe,
    Nat.card_zpowers, orderOf_ptB₁ he hb φ hzC hz, hcen, card_ptA_inf_radA he hb φ]

include he hnd hzC in
theorem radA_le_normalizer_D₁ [Finite G] {D₁ : Subgroup G}
    (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) : 𝒜₂ ≤ normalizer (D₁ : Set G) :=
  fun a ha => mem_normalizer_of_conj_mem fun d hd =>
    hD₁n a (radSub_le_normalizer_ptSub he hb hnd φ hzC (mem_sup_left ha)) d hd

theorem zpowers_le_normalizer_C₁ [Finite G] {C₁ : Subgroup G}
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁) : zpowers z ≤ normalizer (C₁ : Set G) := by
  rw [zpowers_le]
  exact mem_normalizer_of_conj_mem hzC₁

include he hnd hzC in
theorem exists_of_mem_V₁ [Finite G] {D₁ C₁ : Subgroup G}
    (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁) {v : G} (hv : v ∈ D₁ ⊔ 𝒜₂) :
    ∃ a ∈ 𝒜₂, ∃ n : ℤ, ∃ c ∈ C₁, v = a * z ^ n * c := by
  have hv' : v ∈ ((𝒜₂ ⊔ D₁ : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hv
  rw [coe_mul_of_left_le_normalizer_right _ _ (radA_le_normalizer_D₁ he hb hnd φ hzC hD₁n)] at hv'
  obtain ⟨a, ha, d, hd, rfl⟩ := hv'
  have hd' : d ∈ ((zpowers z ⊔ C₁ : Subgroup G) : Set G) := by
    rw [hC₁z]
    exact hd
  rw [coe_mul_of_left_le_normalizer_right _ _ (zpowers_le_normalizer_C₁ hzC₁)] at hd'
  obtain ⟨t, ht, c, hc, rfl⟩ := hd'
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 ht
  exact ⟨a, ha, n, c, hc, by rw [mul_assoc]⟩

omit hb in
include hzC in
theorem gamma_of_V₁ {a c : G} (ha : a ∈ 𝒜₂) (n : ℤ) :
    z⁻¹ * ((a * z ^ n * c)⁻¹ * z * (a * z ^ n * c)) = z⁻¹ * (c⁻¹ * z * c) := by
  have haz : a⁻¹ * z * a = z := by
    rw [mul_assoc, ← mul_comm_z hzC (pullSub_le φ _ ha), inv_mul_cancel_left]
  calc z⁻¹ * ((a * z ^ n * c)⁻¹ * z * (a * z ^ n * c)) =
      z⁻¹ * (c⁻¹ * (z ^ n)⁻¹ * (a⁻¹ * z * a) * z ^ n * c) := by group
    _ = z⁻¹ * (c⁻¹ * (z ^ n)⁻¹ * z * z ^ n * c) := by rw [haz]
    _ = z⁻¹ * (c⁻¹ * z * c) := by group

section Block

variable {D₁ C₁ D₂ C₂ K₀ P B V₁ : Subgroup G}

include he hnd hzC hinf hz in
theorem degree64_next_block [Finite G] {ν₂ : G → ↥(binarySymMatrices 3)}
    (hD₁N : D₁ ≤ 𝒩₁) (hD₁n : ∀ n ∈ 𝒩₁, ∀ d ∈ D₁, n * d * n⁻¹ ∈ D₁)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hb₁c : ∀ m ∈ 𝒩₁, m * ptB₁ he hb φ hzC hz = ptB₁ he hb φ hzC hz * m)
    (hC₁D : C₁ ≤ D₁) (hC₁n : ∀ m ∈ 𝒩₁, ∀ c ∈ C₁, m * c * m⁻¹ ∈ C₁)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁c : Nat.card C₁ = 1024)
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) (hRD₂ : ℛ ≤ D₂)
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hC₂R : C₂ ⊓ ℛ = 𝒜₂) (hC₁C₂ : C₁ ⊓ C₂ = C₁ ⊓ D₂)
    (hK₀ : K₀ = C₁ ⊓ D₂) (hP : P = 𝒜₂ ⊔ K₀) (hB : B = zpowers z ⊔ 𝒜₁ ⊔ 𝒜₂ ⊔ K₀)
    (hV₁ : V₁ = D₁ ⊔ 𝒜₂) (hPcard : Nat.card P = 512) :
    Nat.card B = 4096 ∧ Nat.card V₁ = 16384 ∧ B ≤ V₁ ∧
      (∀ v ∈ V₁, ∀ x ∈ B, v * x * v⁻¹ ∈ B) ∧
      V₁ ≤ normalizer (B : Set G) ⊓ centralizer ({ptB₁ he hb φ hzC hz} : Set G) ∧
      P ≤ B ∧ zpowers (ptB₁ he hb φ hzC hz) ≤ P ∧
      (∀ v ∈ V₁, z⁻¹ * (v⁻¹ * z * v) ∈ 𝒜₁) ∧
      (∀ a ∈ 𝒜₁, ∀ v ∈ V₁, a⁻¹ * v⁻¹ * a * v ∈ 𝒜₁ ⊓ 𝒜₂) ∧
      (∀ v ∈ V₁, ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, v * j * v⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂) ∧
      (∀ x ∈ B, z⁻¹ * (x⁻¹ * z * x) ∈ 𝒜₁ ⊓ 𝒜₂) ∧ B ≤ normalizer (P : Set G) := by
  classical
  have hzR : z ∈ ℛ := mem_sup_right (mem_zpowers z)
  have hzD₂ : z ∈ D₂ := hRD₂ hzR
  have hzB₁ : z ∈ ℬ₁ := mem_sup_right (mem_zpowers z)
  have hzN₁ : z ∈ 𝒩₁ := le_normalizer hzB₁
  have hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁ := hC₁n z hzN₁
  have hzD₁ : z ∈ D₁ := by
    rw [← hC₁z]
    exact mem_sup_left (mem_zpowers z)
  have hAC₁ : 𝒜₁ ≤ C₁ := ptA_le_of_inf_eq hb φ hC₁B
  have hAL : 𝒜₁ ≤ L := pullSub_le φ _
  have hA₂L : 𝒜₂ ≤ L := pullSub_le φ _
  have hJA₁ : 𝒜₁ ⊓ 𝒜₂ ≤ 𝒜₁ := inf_le_left
  have hJA₂ : 𝒜₁ ⊓ 𝒜₂ ≤ 𝒜₂ := inf_le_right
  have hIJ : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ ⊓ 𝒜₂ := zpowers_ptB₁_le he hb φ hzC hz
  have hA₂D₂ : 𝒜₂ ≤ D₂ := le_sup_left.trans hRD₂
  have hK₀C₁ : K₀ ≤ C₁ := by
    rw [hK₀]
    exact inf_le_left
  have hK₀D₂ : K₀ ≤ D₂ := by
    rw [hK₀]
    exact inf_le_right
  have hK₀C₂ : K₀ ≤ C₂ := by
    intro k hk
    rw [hK₀, ← hC₁C₂] at hk
    exact (mem_inf.1 hk).2
  have hA₂C₂ : 𝒜₂ ≤ C₂ := radA_le_of_inf_eq φ hC₂R
  have hA₂P : 𝒜₂ ≤ P := by
    rw [hP]
    exact le_sup_left
  have hK₀P : K₀ ≤ P := by
    rw [hP]
    exact le_sup_right
  have hPC₂ : P ≤ C₂ := by
    rw [hP]
    exact sup_le hA₂C₂ hK₀C₂
  have hzP : z ∉ P := fun h => z_not_mem_of_inf_eq φ hinf hz hC₂R (hPC₂ h)
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
  have hPB : P ≤ B := by
    rw [hP]
    exact sup_le hA₂B hK₀B
  have hD₁V₁ : D₁ ≤ V₁ := by
    rw [hV₁]
    exact le_sup_left
  have hA₂V₁ : 𝒜₂ ≤ V₁ := by
    rw [hV₁]
    exact le_sup_right
  have hzL : ∀ x ∈ L, x * z = z * x := fun x hx => mul_comm_z hzC hx
  have hA₂comm : ∀ x ∈ 𝒜₂, ∀ y ∈ 𝒜₂, x * y = y * x := fun x hx y hy => radA_comm he φ hx hy
  have hA₁comm : ∀ x ∈ 𝒜₁, ∀ y ∈ 𝒜₁, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isElementaryAbelian (ptA_facts he hb hnd φ).2.1 hx hy
  have hC₁comm : ∀ c ∈ C₁, ∀ d ∈ C₁, c⁻¹ * d⁻¹ * c * d ∈ zpowers (ptB₁ he hb φ hzC hz) :=
    fun c hc d hd => comm_mem_of_sq_mem hC₁sq hc hd
  have hC₁J : ∀ c ∈ C₁, ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, c * j * c⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ := by
    intro c hc j hj
    have h1 : c * j * c⁻¹ = j * (j⁻¹ * c⁻¹⁻¹ * j * c⁻¹) := by group
    rw [h1]
    exact mul_mem hj (hIJ (hC₁comm j (hAC₁ (hJA₁ hj)) c⁻¹ (inv_mem hc)))
  have hdec : ∀ v ∈ V₁, ∃ a ∈ 𝒜₂, ∃ n : ℤ, ∃ c ∈ C₁, v = a * z ^ n * c := fun v hv =>
    exists_of_mem_V₁ he hb hnd φ hzC hD₁n hC₁z hzC₁ (by rw [← hV₁]; exact hv)
  have hV₁J : ∀ v ∈ V₁, ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, v * j * v⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ := by
    intro v hv j hj
    obtain ⟨a, ha, n, c, hc, rfl⟩ := hdec v hv
    have h1 := hC₁J c hc j hj
    have hz1 : z ^ n * (c * j * c⁻¹) * (z ^ n)⁻¹ = c * j * c⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact ((Commute.zpow_right (hzL _ (hAL (hJA₁ h1))) n).eq).symm
    have ha1 : a * (c * j * c⁻¹) * a⁻¹ = c * j * c⁻¹ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hA₂comm a ha _ (hJA₂ h1)
    have h2 : a * z ^ n * c * j * (a * z ^ n * c)⁻¹ = c * j * c⁻¹ := by
      calc a * z ^ n * c * j * (a * z ^ n * c)⁻¹ =
          a * (z ^ n * (c * j * c⁻¹) * (z ^ n)⁻¹) * a⁻¹ := by group
        _ = c * j * c⁻¹ := by rw [hz1, ha1]
    rw [h2]
    exact h1
  have hγV₁ : ∀ v ∈ V₁, z⁻¹ * (v⁻¹ * z * v) ∈ 𝒜₁ := by
    intro v hv
    obtain ⟨a, ha, n, c, hc, rfl⟩ := hdec v hv
    rw [gamma_of_V₁ φ hzC ha n]
    exact hγD₁ c (hC₁D hc)
  have hA₁V₁ : ∀ a ∈ 𝒜₁, ∀ v ∈ V₁, a⁻¹ * v⁻¹ * a * v ∈ 𝒜₁ ⊓ 𝒜₂ := by
    intro a₁ ha₁ v hv
    obtain ⟨a, ha, n, c, hc, rfl⟩ := hdec v hv
    have hj₁ : a₁⁻¹ * a⁻¹ * a₁⁻¹⁻¹ * a⁻¹⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ :=
      comm_mem_ptA_inf_radA' he hb hnd φ hzC hinf hz (inv_mem ha₁) (inv_mem ha)
    rw [inv_inv, inv_inv] at hj₁
    have h1 : a⁻¹ * a₁ * a = a₁ * (a₁⁻¹ * a⁻¹ * a₁ * a) := by group
    have hz1 : (z ^ n)⁻¹ * (a₁ * (a₁⁻¹ * a⁻¹ * a₁ * a)) * z ^ n =
        a₁ * (a₁⁻¹ * a⁻¹ * a₁ * a) := by
      have hcz : (a₁ * (a₁⁻¹ * a⁻¹ * a₁ * a)) * z ^ n = z ^ n * (a₁ * (a₁⁻¹ * a⁻¹ * a₁ * a)) :=
        (Commute.zpow_right (hzL _ (hAL (mul_mem ha₁ (hJA₁ hj₁)))) n).eq
      rw [mul_assoc, hcz, inv_mul_cancel_left]
    have hc2 : a₁⁻¹ * c⁻¹ * a₁ * c ∈ 𝒜₁ ⊓ 𝒜₂ := hIJ (hC₁comm a₁ (hAC₁ ha₁) c hc)
    have hc3 : c⁻¹ * (a₁⁻¹ * a⁻¹ * a₁ * a) * c⁻¹⁻¹ ∈ 𝒜₁ ⊓ 𝒜₂ :=
      hC₁J c⁻¹ (inv_mem hc) _ hj₁
    rw [inv_inv] at hc3
    have h2 : a₁⁻¹ * (a * z ^ n * c)⁻¹ * a₁ * (a * z ^ n * c) =
        (a₁⁻¹ * c⁻¹ * a₁ * c) * (c⁻¹ * (a₁⁻¹ * a⁻¹ * a₁ * a) * c) := by
      calc a₁⁻¹ * (a * z ^ n * c)⁻¹ * a₁ * (a * z ^ n * c) =
          a₁⁻¹ * (c⁻¹ * ((z ^ n)⁻¹ * (a⁻¹ * a₁ * a) * z ^ n) * c) := by group
        _ = a₁⁻¹ * (c⁻¹ * (a₁ * (a₁⁻¹ * a⁻¹ * a₁ * a)) * c) := by rw [h1, hz1]
        _ = (a₁⁻¹ * c⁻¹ * a₁ * c) * (c⁻¹ * (a₁⁻¹ * a⁻¹ * a₁ * a) * c) := by group
    rw [h2]
    exact mul_mem hc2 hc3
  let S : Subgroup G :=
    { carrier := {v | v ∈ V₁ ∧ z⁻¹ * (v⁻¹ * z * v) ∈ 𝒜₁ ⊓ 𝒜₂}
      one_mem' := ⟨one_mem _, by
        rw [inv_one, one_mul, mul_one, inv_mul_cancel]
        exact one_mem _⟩
      mul_mem' := by
        rintro x y ⟨hx, hxJ⟩ ⟨hy, hyJ⟩
        refine ⟨mul_mem hx hy, ?_⟩
        rw [gamma_mul_eq]
        have h := hV₁J y⁻¹ (inv_mem hy) _ hxJ
        rw [inv_inv] at h
        exact mul_mem hyJ h
      inv_mem' := by
        rintro x ⟨hx, hxJ⟩
        refine ⟨inv_mem hx, ?_⟩
        have h : z⁻¹ * (x⁻¹⁻¹ * z * x⁻¹) = x * (z⁻¹ * (x⁻¹ * z * x))⁻¹ * x⁻¹ := by group
        rw [h]
        exact hV₁J x hx _ (inv_mem hxJ) }
  have hγL : ∀ x ∈ L, z⁻¹ * (x⁻¹ * z * x) = 1 := fun x hx => by
    rw [mul_assoc x⁻¹, ← hzL x hx, inv_mul_cancel_left, inv_mul_cancel]
  have hBS : B ≤ S := by
    rw [hB]
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · rw [zpowers_le]
      refine ⟨hD₁V₁ hzD₁, ?_⟩
      have h : z⁻¹ * (z⁻¹ * z * z) = 1 := by group
      rw [h]
      exact one_mem _
    · intro a ha
      refine ⟨hD₁V₁ (hC₁D (hAC₁ ha)), ?_⟩
      rw [hγL a (hAL ha)]
      exact one_mem _
    · intro a ha
      refine ⟨hA₂V₁ ha, ?_⟩
      rw [hγL a (hA₂L ha)]
      exact one_mem _
    · intro k hk
      have hk' : k ∈ C₁ ⊓ D₂ := by
        rw [← hK₀]
        exact hk
      exact ⟨hD₁V₁ (hC₁D (hK₀C₁ hk)), conj_mem_ptA_inf_radA he hb φ hzC hz hν₂z hγD₁ hC₁D hk'⟩
  have hBV₁ : B ≤ V₁ := fun x hx => (hBS hx).1
  have hSB : S ≤ B := by
    rintro v ⟨hv, hvJ⟩
    obtain ⟨a, ha, n, c, hc, rfl⟩ := hdec v hv
    rw [gamma_of_V₁ φ hzC ha n] at hvJ
    have hcJ : z⁻¹ * c⁻¹ * z * c ∈ 𝒜₁ ⊓ 𝒜₂ := by
      have h : z⁻¹ * c⁻¹ * z * c = z⁻¹ * (c⁻¹ * z * c) := by group
      rw [h]
      exact hvJ
    obtain ⟨a₁, ha₁, k, hk, rfl⟩ := exists_ptA_mul_of_conj_mem hb φ hKz hC₁z hzC₁ hzD₂ hD₁H
      hC₁B hC₁D hc hcJ
    have hk' : k ∈ K₀ := by
      rw [hK₀]
      exact hk
    exact mul_mem (mul_mem (hA₂B ha) (zpow_mem hzB n)) (mul_mem (hA₁B ha₁) (hK₀B hk'))
  have hSeq : S = B := le_antisymm hSB hBS
  have hBn : ∀ v ∈ V₁, ∀ x ∈ B, v * x * v⁻¹ ∈ B := by
    intro v hv x hx
    rw [← hSeq]
    have hxS := hBS hx
    refine ⟨mul_mem (mul_mem hv (hBV₁ hx)) (inv_mem hv), ?_⟩
    rw [gamma_conj_eq]
    refine hV₁J v hv _ ?_
    have hg := hγV₁ v hv
    have hxJ := hxS.2
    have hc : (z⁻¹ * (v⁻¹ * z * v))⁻¹ * (z⁻¹ * (x⁻¹ * z * x)) =
        (z⁻¹ * (x⁻¹ * z * x)) * (z⁻¹ * (v⁻¹ * z * v))⁻¹ :=
      (show Commute (z⁻¹ * (v⁻¹ * z * v)) (z⁻¹ * (x⁻¹ * z * x)) from
        hA₁comm _ hg _ (hJA₁ hxJ)).inv_left
    have h1 : (z⁻¹ * (v⁻¹ * z * v))⁻¹ * (z⁻¹ * (x⁻¹ * z * x)) *
        (x⁻¹ * (z⁻¹ * (v⁻¹ * z * v)) * x) =
        (z⁻¹ * (x⁻¹ * z * x)) * ((z⁻¹ * (v⁻¹ * z * v))⁻¹ * x⁻¹ *
          (z⁻¹ * (v⁻¹ * z * v)) * x) := by
      rw [hc]
      group
    rw [h1]
    exact mul_mem hxJ (hA₁V₁ _ hg x (hBV₁ hx))
  have hzP' : zpowers z ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers hz (mem_inf.1 hx).1 with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (h ▸ (mem_inf.1 hx).2) hzP
  have hzNP : zpowers z ≤ normalizer (P : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hle : P ≤ P.comap (MulAut.conj z).toMonoidHom := by
      rw [hP]
      refine sup_le (fun a ha => ?_) (fun k hk => ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hzL a (hA₂L ha),
          mul_inv_cancel_right]
        exact mem_sup_left ha
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hk' : k ∈ C₁ ⊓ D₂ := by
          rw [← hK₀]
          exact hk
        refine mem_sup_right ?_
        rw [hK₀]
        exact mem_inf.2 ⟨hzC₁ k (mem_inf.1 hk').1,
          hD₂n z (le_normalizer hzR) k (mem_inf.1 hk').2⟩
    exact hle hp
  have hU₂ : Nat.card (zpowers z ⊔ P : Subgroup G) = 1024 := by
    have h := natCard_sup_mul_inf hzNP
    rw [hzP', Subgroup.card_bot, mul_one, Nat.card_zpowers, hz, hPcard] at h
    exact h
  have hBeq : B = 𝒜₁ ⊔ (zpowers z ⊔ P) := by
    apply le_antisymm
    · rw [hB]
      refine sup_le (sup_le (sup_le ?_ le_sup_left) ?_) ?_
      · exact le_sup_left.trans le_sup_right
      · exact hA₂P.trans (le_sup_right.trans le_sup_right)
      · exact hK₀P.trans (le_sup_right.trans le_sup_right)
    · exact sup_le hA₁B (sup_le (zpowers_le.2 hzB) hPB)
  have hA₁NP : 𝒜₁ ≤ normalizer (P : Set G) := by
    intro a ha
    have haN₂ : a ∈ 𝒩₂ := ptSub_le_normalizer_radSub he hb φ hzC hz (mem_sup_left ha)
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    rw [hP] at hy
    refine (sup_le (fun x hx => ?_) (fun k hk => ?_) :
      𝒜₂ ⊔ K₀ ≤ P.comap (MulAut.conj a).toMonoidHom) hy
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h1 : a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
      rw [h1]
      exact hA₂P (mul_mem (hJA₂ (comm_mem_ptA_inf_radA' he hb hnd φ hzC hinf hz ha hx)) hx)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hk' : k ∈ C₁ ⊓ D₂ := by
        rw [← hK₀]
        exact hk
      refine hK₀P ?_
      rw [hK₀]
      exact mem_inf.2 ⟨mul_mem (mul_mem (hAC₁ ha) (mem_inf.1 hk').1) (inv_mem (hAC₁ ha)),
        hD₂n a haN₂ k (mem_inf.1 hk').2⟩
  have hA₁N : 𝒜₁ ≤ normalizer ((zpowers z ⊔ P : Subgroup G) : Set G) := by
    intro a ha
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hle : zpowers z ⊔ P ≤ (zpowers z ⊔ P).comap (MulAut.conj a).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          hzL a (hAL ha), mul_inv_cancel_right]
        exact mem_sup_left (mem_zpowers z)
      · intro y hy
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_right ((mem_normalizer_iff.1 (hA₁NP ha) y).1 hy)
    exact hle hp
  have hUD : zpowers z ⊔ P ≤ D₂ := by
    refine sup_le (zpowers_le.2 hzD₂) ?_
    rw [hP]
    exact sup_le hA₂D₂ hK₀D₂
  have hA₁U₂ : 𝒜₁ ⊓ (zpowers z ⊔ P) = 𝒜₁ ⊓ 𝒜₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxU⟩ := mem_inf.1 hx
      have hxR : x ∈ ℛ := by
        rw [← hD₂H]
        exact mem_inf.2 ⟨hUD hxU, mem_centralizer_singleton_iff.2 (hzL x (hAL hxA))⟩
      exact mem_inf.2 ⟨hxA, mem_radA_of_mem_radSub φ hzC hinf hxR (hAL hxA)⟩
    · exact le_inf hJA₁ (hJA₂.trans (hA₂P.trans le_sup_right))
  have hBcard : Nat.card B = 4096 := by
    have h := natCard_sup_mul_inf hA₁N
    rw [hA₁U₂, card_ptA_inf_radA he hb φ, (ptA_facts he hb hnd φ).2.2.1, hU₂, ← hBeq] at h
    omega
  have hzC₁' : zpowers z ⊓ C₁ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases eq_one_or_eq_of_mem_zpowers hz (mem_inf.1 hx).1 with h | h
    · rw [h]
      exact one_mem _
    · exfalso
      have h1 : z ∈ C₁ ⊓ ℬ₁ := mem_inf.2 ⟨h ▸ (mem_inf.1 hx).2, hzB₁⟩
      rw [hC₁B] at h1
      exact z_not_mem_ptA hb φ hinf hz h1
  have hD₁card : Nat.card D₁ = 2048 := by
    have h := natCard_sup_mul_inf (zpowers_le_normalizer_C₁ hzC₁)
    rw [hzC₁', Subgroup.card_bot, mul_one, Nat.card_zpowers, hz, hC₁z, hC₁c] at h
    exact h
  have hA₂D₁ : 𝒜₂ ⊓ D₁ = 𝒜₁ ⊓ 𝒜₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxD⟩ := mem_inf.1 hx
      have hxB : x ∈ ℬ₁ := by
        rw [← hD₁H]
        exact mem_inf.2 ⟨hxD, mem_centralizer_singleton_iff.2 (hzL x (hA₂L hxA))⟩
      have hxA₁ : x ∈ 𝒜₁ := by
        rw [← (ptSub_facts he hb hnd φ hzC hinf hz).2.2.2]
        exact mem_inf.2 ⟨hxB, hA₂L hxA⟩
      exact mem_inf.2 ⟨hxA₁, hxA⟩
    · exact le_inf hJA₂ (hJA₁.trans (hAC₁.trans hC₁D))
  have hV₁card : Nat.card V₁ = 16384 := by
    have h := natCard_sup_mul_inf (radA_le_normalizer_D₁ he hb hnd φ hzC hD₁n)
    rw [hA₂D₁, card_ptA_inf_radA he hb φ, card_pullSub_radA he φ, hD₁card, sup_comm, ← hV₁] at h
    omega
  have hb₁A₂ : ptB₁ he hb φ hzC hz ∈ 𝒜₂ := hJA₂ (hIJ (mem_zpowers _))
  have hV₁c : V₁ ≤ centralizer ({ptB₁ he hb φ hzC hz} : Set G) := by
    rw [hV₁]
    refine sup_le (fun d hd => ?_) (fun a ha => ?_)
    · exact mem_centralizer_singleton_iff.2 (hb₁c d (hD₁N hd))
    · exact mem_centralizer_singleton_iff.2 (hA₂comm a ha _ hb₁A₂)
  have hBNP : B ≤ normalizer (P : Set G) := by
    rw [hB]
    refine sup_le (sup_le (sup_le hzNP hA₁NP) (hA₂P.trans le_normalizer))
      (hK₀P.trans le_normalizer)
  refine ⟨hBcard, hV₁card, hBV₁, hBn, fun v hv => mem_inf.2
    ⟨mem_normalizer_of_conj_mem fun x hx => hBn v hv x hx, hV₁c hv⟩, hPB,
    hIJ.trans (hJA₂.trans hA₂P), hγV₁, hA₁V₁, hV₁J, fun x hx => (hBS hx).2, hBNP⟩

end Block

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
