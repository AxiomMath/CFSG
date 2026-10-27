module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtBasic
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerLagAction

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

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

section Generic

variable {X : Type*} [Group X]

theorem conj_mem_sup {P Q : Subgroup X} {m : X} (hP : ∀ x ∈ P, m * x * m⁻¹ ∈ P)
    (hQ : ∀ y ∈ Q, m * y * m⁻¹ ∈ Q) {w : X} (hw : w ∈ P ⊔ Q) : m * w * m⁻¹ ∈ P ⊔ Q := by
  have hle : (P ⊔ Q).map (MulAut.conj m).toMonoidHom ≤ P ⊔ Q := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hP x hx
    · rintro _ ⟨y, hy, rfl⟩
      exact hQ y hy
  exact hle ⟨w, hw, rfl⟩

theorem zpowers_inf_eq_bot_of_not_mem {t : X} (ht : orderOf t = 2) {P : Subgroup X}
    (htP : t ∉ P) : zpowers t ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxt, hxP⟩ := mem_inf.1 hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
  have hk : t ^ k = t ^ (k % 2) := by
    rw [← zpow_mod_orderOf t k, ht]
    norm_num
  rw [hk] at hxP ⊢
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero]
    exact one_mem _
  · rw [h1, zpow_one] at hxP
    exact absurd hxP htP

theorem card_zpowers_sup_of_not_mem [Finite X] {t : X} (ht : orderOf t = 2) {P : Subgroup X}
    (htP : t ∉ P) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) :
    Nat.card (zpowers t ⊔ P : Subgroup X) = 2 * Nat.card P := by
  have hle : zpowers t ≤ normalizer (P : Set X) := by
    rw [zpowers_le]
    exact mem_normalizer_of_conj_mem hn
  have h1 := natCard_sup_mul_inf hle
  rw [zpowers_inf_eq_bot_of_not_mem ht htP, Subgroup.card_bot, mul_one, Nat.card_zpowers,
    ht] at h1
  exact h1

end Generic

section Basic

variable (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
include h

omit h in
theorem z_mem_ptSub : z ∈ ℬ₁ := mem_sup_right (mem_zpowers z)

omit h in
theorem z_mem_N₁ : z ∈ 𝒩₁ := le_normalizer z_mem_ptSub

omit h in
theorem z_mem_N₂ : z ∈ 𝒩₂ := le_normalizer (mem_sup_right (mem_zpowers z))

theorem PtBase.zD₁ : z ∈ D₁ := by
  rw [← h.hC₁z]
  exact mem_sup_left (mem_zpowers z)

theorem PtBase.A₁C₁ : 𝒜₁ ≤ C₁ := ptA_le_of_inf_eq hb φ h.hC₁B

theorem PtBase.A₁D₁ : 𝒜₁ ≤ D₁ := h.A₁C₁.trans h.hC₁D

theorem PtBase.A₂D₂ : 𝒜₂ ≤ D₂ := fun _ ha => h.hRD₂ (mem_sup_left ha)

theorem PtBase.K₀_eq : C₁ ⊓ C₂ = C₁ ⊓ D₂ := h.hC₁C₂

theorem PtBase.K₀D₁ : C₁ ⊓ C₂ ≤ D₁ := inf_le_left.trans h.hC₁D

theorem PtBase.K₀D₂ : C₁ ⊓ C₂ ≤ D₂ := inf_le_right.trans h.C₂D₂

theorem PtBase.A₂N₁ : 𝒜₂ ≤ 𝒩₁ := fun _ ha =>
  radSub_le_normalizer_ptSub he hb h.hnd φ hzC (mem_sup_left ha)

omit h in
theorem A₁_le_N₂ (he' : IsSymplecticBasis b e) (hzC' : z ∈ centralizer (L : Set G))
    (hz' : orderOf z = 2) : 𝒜₁ ≤ 𝒩₂ := fun _ ha =>
  ptSub_le_normalizer_radSub he' hb φ hzC' hz' (mem_sup_left ha)

theorem PtBase.z_not_mem_C₁ : z ∉ C₁ := fun hzC₁ => by
  have h1 : z ∈ C₁ ⊓ ℬ₁ := mem_inf.2 ⟨hzC₁, z_mem_ptSub⟩
  rw [h.hC₁B] at h1
  exact z_not_mem_ptA hb φ h.hinf hz h1

theorem PtBase.z_not_mem_C₂ : z ∉ C₂ := h.toLagBase.z_not_mem_C₂ h.hinf

omit h in
include hzC in
theorem mem_of_mem_sup_zpowers {P : Subgroup G} (hPL : P ≤ L) (hinf : L ⊓ zpowers z = ⊥)
    {x : G} (hx : x ∈ P ⊔ zpowers z) (hxL : x ∈ L) : x ∈ P := by
  have hzP : zpowers z ≤ normalizer (P : Set G) := by
    rw [zpowers_le]
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun p hp => ?_)
    exact mul_comm_z hzC (hPL hp)
  have hx' : x ∈ ((zpowers z ⊔ P : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hzP] at hx'
  obtain ⟨t, ht, p, hp, rfl⟩ := hx'
  have htL : t ∈ L := by
    have h1 : t * p * p⁻¹ = t := by group
    rw [← h1]
    exact mul_mem hxL (inv_mem (hPL hp))
  have h2 : t ∈ L ⊓ zpowers z := mem_inf.2 ⟨htL, ht⟩
  rw [hinf, mem_bot] at h2
  change t * p ∈ P
  rw [h2, one_mul]
  exact hp

theorem PtBase.A₁_inf_D₂ : 𝒜₁ ⊓ D₂ = 𝒜₁ ⊓ 𝒜₂ := by
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_left _ h.A₂D₂)
  obtain ⟨hxA, hxD⟩ := mem_inf.1 hx
  have hxH : x ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ hxA))
  have hxR : x ∈ ℛ := by
    rw [← h.hD₂H]
    exact mem_inf.2 ⟨hxD, hxH⟩
  exact mem_inf.2 ⟨hxA, mem_of_mem_sup_zpowers (hzC := hzC) (pullSub_le φ _) h.hinf hxR
    (pullSub_le φ _ hxA)⟩

theorem PtBase.A₂_inf_D₁ : 𝒜₂ ⊓ D₁ = 𝒜₁ ⊓ 𝒜₂ := by
  refine le_antisymm (fun x hx => ?_) (by
    rw [inf_comm]
    exact inf_le_inf_left _ h.A₁D₁)
  obtain ⟨hxA, hxD⟩ := mem_inf.1 hx
  have hxH : x ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ hxA))
  have hxB : x ∈ ℬ₁ := by
    rw [← h.hD₁H]
    exact mem_inf.2 ⟨hxD, hxH⟩
  exact mem_inf.2 ⟨mem_of_mem_sup_zpowers (hzC := hzC) (pullSub_le φ _) h.hinf hxB
    (pullSub_le φ _ hxA), hxA⟩

theorem PtBase.card_A₁ : Nat.card 𝒜₁ = 32 := (ptA_facts he hb h.hnd φ).2.2.1

theorem PtBase.card_K₀ : Nat.card (C₁ ⊓ C₂ : Subgroup G) = 64 := by
  rw [h.K₀_eq]
  exact h.hK₀card

theorem PtBase.A₁_inf_K₀ : 𝒜₁ ⊓ (C₁ ⊓ C₂) = 𝒜₁ ⊓ 𝒜₂ := by
  rw [h.K₀_eq, ← inf_assoc, inf_of_le_left h.A₁C₁, h.A₁_inf_D₂]

theorem PtBase.P₂C₂ : 𝒜₂ ⊔ (C₁ ⊓ C₂) ≤ C₂ := sup_le h.A₂C₂ inf_le_right

theorem PtBase.P₂D₂ : 𝒜₂ ⊔ (C₁ ⊓ C₂) ≤ D₂ := h.P₂C₂.trans h.C₂D₂

theorem PtBase.P₁C₁ : 𝒜₁ ⊔ (C₁ ⊓ C₂) ≤ C₁ := sup_le h.A₁C₁ inf_le_left

theorem PtBase.P₁D₁ : 𝒜₁ ⊔ (C₁ ⊓ C₂) ≤ D₁ := h.P₁C₁.trans h.hC₁D

theorem PtBase.A₁_inf_P₂ : 𝒜₁ ⊓ (𝒜₂ ⊔ (C₁ ⊓ C₂)) = 𝒜₁ ⊓ 𝒜₂ := by
  refine le_antisymm ?_ (inf_le_inf_left _ le_sup_left)
  rw [← h.A₁_inf_D₂]
  exact inf_le_inf_left _ h.P₂D₂

omit h in
theorem A_eq : (𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) = 𝒜₁ ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) :=
  le_antisymm (sup_le (sup_le le_sup_left (le_sup_right.trans le_sup_right)) le_sup_right)
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem PtBase.P₂N₁ : 𝒜₂ ⊔ (C₁ ⊓ C₂) ≤ 𝒩₁ := sup_le h.A₂N₁ (h.K₀D₁.trans h.hD₁N)

theorem PtBase.le_normalizer_A₁ [Finite G] {X : Subgroup G} (hX : X ≤ 𝒩₁) :
    X ≤ normalizer (𝒜₁ : Set G) := fun x hx =>
  mem_normalizer_of_conj_mem fun a ha => h.hA₁n x (hX hx) a ha

theorem PtBase.card_P₁ [Finite G] : Nat.card (𝒜₁ ⊔ (C₁ ⊓ C₂) : Subgroup G) = 2 ^ 8 := by
  have h1 := natCard_sup_mul_inf (h.le_normalizer_A₁ (h.K₀D₁.trans h.hD₁N))
  rw [sup_comm (C₁ ⊓ C₂) 𝒜₁, inf_comm (C₁ ⊓ C₂) 𝒜₁, h.A₁_inf_K₀, card_ptA_inf_radA he hb φ,
    h.card_K₀, h.card_A₁] at h1
  omega

theorem PtBase.card_A [Finite G] :
    Nat.card ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) : Subgroup G) = 2 ^ 11 := by
  rw [A_eq]
  have h1 := natCard_sup_mul_inf (h.le_normalizer_A₁ h.P₂N₁)
  rw [sup_comm (𝒜₂ ⊔ (C₁ ⊓ C₂)) 𝒜₁, inf_comm (𝒜₂ ⊔ (C₁ ⊓ C₂)) 𝒜₁, h.A₁_inf_P₂,
    card_ptA_inf_radA he hb φ, h.card_A₁] at h1
  have hP : Nat.card (𝒜₂ ⊔ (C₁ ⊓ C₂) : Subgroup G) = 512 := by
    rw [h.K₀_eq]
    exact h.hPcard
  rw [hP] at h1
  omega

theorem PtBase.conj_z_mem {m : G} (hm : m ∈ 𝒩₁) : z⁻¹ * (m * z * m⁻¹) ∈ 𝒜₁ := by
  obtain ⟨d, hd, c, hc, rfl⟩ := h.hprod₁ m hm
  have hcz : c * z * c⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2, mul_inv_cancel_right]
  have h1 := h.hγD₁ d⁻¹ (inv_mem hd)
  rw [inv_inv] at h1
  rw [show d * c * z * (d * c)⁻¹ = d * (c * z * c⁻¹) * d⁻¹ by group, hcz]
  exact h1

theorem PtBase.conj_A₂_mem [Finite G] {m : G} (hm : m ∈ 𝒩₂) {a : G} (ha : a ∈ 𝒜₂) :
    m * a * m⁻¹ ∈ 𝒜₂ :=
  h.toLagBase.conj_mem_A₂ h.hinf (h.toLagBase.N₂_le_Q₂ hm) ha

theorem PtBase.conj_K₀_mem {m : G} (hm₁ : m ∈ 𝒩₁) (hm₂ : m ∈ 𝒩₂) {k : G} (hk : k ∈ C₁ ⊓ C₂) :
    m * k * m⁻¹ ∈ C₁ ⊓ C₂ :=
  mem_inf.2 ⟨h.hC₁n m hm₁ k (mem_inf.1 hk).1, h.hC₂n m hm₂ k (mem_inf.1 hk).2⟩

theorem PtBase.conj_B_mem [Finite G] {m : G} (hm₁ : m ∈ 𝒩₁) (hm₂ : m ∈ 𝒩₂) {x : G}
    (hx : x ∈ zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))) :
    m * x * m⁻¹ ∈ zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) := by
  set B := zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) with hB
  have hA₁B : 𝒜₁ ≤ B := le_sup_left.trans (le_sup_left.trans le_sup_right)
  have hA₂B : 𝒜₂ ≤ B := le_sup_left.trans (le_sup_right.trans le_sup_right)
  have hK₀B : C₁ ⊓ C₂ ≤ B := le_sup_right.trans (le_sup_left.trans le_sup_right)
  have hzB : z ∈ B := mem_sup_left (mem_zpowers z)
  have hle : B.map (MulAut.conj m).toMonoidHom ≤ B := by
    rw [hB, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le ?_ (sup_le (sup_le ?_ ?_) (sup_le ?_ ?_))
    · rw [MonoidHom.map_zpowers, zpowers_le]
      change m * z * m⁻¹ ∈ B
      rw [show m * z * m⁻¹ = z * (z⁻¹ * (m * z * m⁻¹)) by group]
      exact mul_mem hzB (hA₁B (h.conj_z_mem hm₁))
    · rintro _ ⟨a, ha, rfl⟩
      exact hA₁B (h.hA₁n m hm₁ a ha)
    · rintro _ ⟨k, hk, rfl⟩
      exact hK₀B (h.conj_K₀_mem hm₁ hm₂ hk)
    · rintro _ ⟨a, ha, rfl⟩
      exact hA₂B (h.conj_A₂_mem hm₂ ha)
    · rintro _ ⟨k, hk, rfl⟩
      exact hK₀B (h.conj_K₀_mem hm₁ hm₂ hk)
  exact hle ⟨x, hx, rfl⟩

theorem PtBase.B_le : zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) ≤ 𝒩₁ ⊓ 𝒩₂ := by
  have hA₁N₁ : 𝒜₁ ≤ 𝒩₁ := fun a ha => le_normalizer (mem_sup_left ha)
  have hA₂N₂ : 𝒜₂ ≤ 𝒩₂ := fun a ha => le_normalizer (mem_sup_left ha)
  refine le_inf ?_ ?_
  · exact sup_le (zpowers_le.2 z_mem_N₁) (sup_le (sup_le hA₁N₁ (h.K₀D₁.trans h.hD₁N)) h.P₂N₁)
  · exact sup_le (zpowers_le.2 z_mem_N₂) (sup_le (sup_le (A₁_le_N₂ he hzC hz)
      (h.K₀D₂.trans h.hD₂N)) (sup_le hA₂N₂ (h.K₀D₂.trans h.hD₂N)))

theorem PtBase.card_B [Finite G] :
    Nat.card (zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) : Subgroup G) = 2 ^ 12 := by
  set A := (𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) with hA
  have hzA : zpowers z ≤ normalizer (A : Set G) := by
    rw [zpowers_le]
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 := h.conj_B_mem z_mem_N₁ z_mem_N₂ (mem_sup_right hx : x ∈ zpowers z ⊔ A)
    have hle : A.map (MulAut.conj z).toMonoidHom ≤ A := by
      rw [hA, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
      refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
      · rintro _ ⟨a, ha, rfl⟩
        exact mem_sup_left (mem_sup_left (h.hA₁n z z_mem_N₁ a ha))
      · rintro _ ⟨k, hk, rfl⟩
        exact mem_sup_left (mem_sup_right (h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk))
      · rintro _ ⟨a, ha, rfl⟩
        exact mem_sup_right (mem_sup_left (h.conj_A₂_mem z_mem_N₂ ha))
      · rintro _ ⟨k, hk, rfl⟩
        exact mem_sup_right (mem_sup_right (h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk))
    exact hle ⟨x, hx, rfl⟩
  have hzA' : z ∉ A := by
    intro hz'
    rw [hA, A_eq] at hz'
    have hP₂ : 𝒜₂ ⊔ (C₁ ⊓ C₂) ≤ normalizer (𝒜₁ : Set G) := h.le_normalizer_A₁ h.P₂N₁
    have hz'' : z ∈ (((𝒜₂ ⊔ (C₁ ⊓ C₂)) ⊔ 𝒜₁ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hz'
    rw [coe_mul_of_left_le_normalizer_right _ _ hP₂] at hz''
    obtain ⟨p, hp, a, ha, hpa⟩ := hz''
    have haD : a ∈ D₂ := by
      have h1 : a = p⁻¹ * z := by rw [← hpa]; group
      rw [h1]
      exact mul_mem (inv_mem (h.P₂D₂ hp)) h.zD₂
    have haJ : a ∈ 𝒜₁ ⊓ 𝒜₂ := by
      rw [← h.A₁_inf_D₂]
      exact mem_inf.2 ⟨ha, haD⟩
    have hzP : z ∈ 𝒜₂ ⊔ (C₁ ⊓ C₂) := by
      change p * a = z at hpa
      rw [← hpa]
      exact mul_mem hp (mem_sup_left (mem_inf.1 haJ).2)
    exact h.z_not_mem_C₂ (h.P₂C₂ hzP)
  have hinf' : zpowers z ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htz, htA⟩ := mem_inf.1 ht
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 htz
    have hk : z ^ k = z ^ (k % 2) := by
      rw [← zpow_mod_orderOf z k, hz]
      norm_num
    rw [hk] at htA ⊢
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero]
      exact one_mem _
    · rw [h1, zpow_one] at htA
      exact absurd htA hzA'
  have h1 := natCard_sup_mul_inf hzA
  rw [hinf', Subgroup.card_bot, mul_one, Nat.card_zpowers, hz, h.card_A] at h1
  rw [h1]
  norm_num

theorem PtBase.B_eq_pCore [Finite G] :
    zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) =
      CFSG.Assembly.pCoreOf 2 (𝒩₁ ⊓ 𝒩₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := le_pCoreOf 2 h.B_le (fun y hy k hk => h.conj_B_mem (mem_inf.1 hy).1
    (mem_inf.1 hy).2 hk) (IsPGroup.of_card h.card_B)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h.hO₁₂, h.card_B]; norm_num)

theorem PtBase.C₁_inf_N₂_le [Finite G] :
    C₁ ⊓ 𝒩₂ ≤ zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.B_eq_pCore]
  refine le_pCoreOf 2 (inf_le_inf_right _ (h.hC₁D.trans h.hD₁N)) (fun y hy k hk => ?_) ?_
  · exact mem_inf.2 ⟨h.hC₁n y (mem_inf.1 hy).1 k (mem_inf.1 hk).1,
      mul_mem (mul_mem (mem_inf.1 hy).2 (mem_inf.1 hk).2) (inv_mem (mem_inf.1 hy).2)⟩
  · exact (IsPGroup.of_card (n := 10) (by rw [h.hC₁card]; norm_num)).to_le inf_le_left

theorem PtBase.C₂_inf_N₁_le [Finite G] :
    C₂ ⊓ 𝒩₁ ≤ zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [h.B_eq_pCore]
  refine le_pCoreOf 2 (fun x hx => mem_inf.2 ⟨(mem_inf.1 hx).2,
    h.hD₂N (h.C₂D₂ (mem_inf.1 hx).1)⟩) (fun y hy k hk => ?_) ?_
  · exact mem_inf.2 ⟨h.hC₂n y (mem_inf.1 hy).2 k (mem_inf.1 hk).1,
      mul_mem (mul_mem (mem_inf.1 hy).1 (mem_inf.1 hk).2) (inv_mem (mem_inf.1 hy).1)⟩
  · exact (IsPGroup.of_card (n := 12) (by rw [h.hC₂card]; norm_num)).to_le inf_le_left

theorem PtBase.card_zP₁ [Finite G] : Nat.card (zpowers z ⊔ (𝒜₁ ⊔ (C₁ ⊓ C₂)) : Subgroup G) =
    2 ^ 9 := by
  rw [card_zpowers_sup_of_not_mem hz (fun h1 => h.z_not_mem_C₁ (h.P₁C₁ h1))
    (fun x hx => conj_mem_sup (fun a ha => h.hA₁n z z_mem_N₁ a ha)
      (fun k hk => h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk) hx), h.card_P₁]
  norm_num

theorem PtBase.card_zP₂ [Finite G] : Nat.card (zpowers z ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) : Subgroup G) =
    2 ^ 10 := by
  rw [card_zpowers_sup_of_not_mem hz (fun h1 => h.z_not_mem_C₂ (h.P₂C₂ h1))
    (fun x hx => conj_mem_sup (fun a ha => h.conj_A₂_mem z_mem_N₂ ha)
      (fun k hk => h.conj_K₀_mem z_mem_N₁ z_mem_N₂ hk) hx)]
  have hP : Nat.card (𝒜₂ ⊔ (C₁ ⊓ C₂) : Subgroup G) = 512 := by
    rw [h.K₀_eq]
    exact h.hPcard
  rw [hP]
  norm_num

theorem PtBase.card_D₁A₂ [Finite G] : Nat.card (D₁ ⊔ 𝒜₂ : Subgroup G) = 2 ^ 14 := by
  have hle : 𝒜₂ ≤ normalizer (D₁ : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₁n a (h.A₂N₁ ha) d hd
  have h1 := natCard_sup_mul_inf hle
  rw [h.A₂_inf_D₁, card_ptA_inf_radA he hb φ, card_pullSub_radA he φ, h.hD₁card, sup_comm] at h1
  omega

theorem PtBase.card_D₂A₁ [Finite G] : Nat.card (D₂ ⊔ 𝒜₁ : Subgroup G) = 2 ^ 15 := by
  have hle : 𝒜₁ ≤ normalizer (D₂ : Set G) := fun a ha =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₂n a (A₁_le_N₂ he hzC hz ha) d hd
  have h1 := natCard_sup_mul_inf hle
  rw [h.A₁_inf_D₂, card_ptA_inf_radA he hb φ, h.card_A₁, h.hD₂card, sup_comm] at h1
  omega

theorem PtBase.U₁_eq [Finite G] :
    (zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))) ⊓ D₁ =
      zpowers z ⊔ (𝒜₁ ⊔ (C₁ ⊓ C₂)) := by
  set B := zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) with hB
  have hle : zpowers z ⊔ (𝒜₁ ⊔ (C₁ ⊓ C₂)) ≤ B ⊓ D₁ := le_inf
    (sup_le le_sup_left (le_sup_left.trans le_sup_right))
    (sup_le (zpowers_le.2 h.zD₁) h.P₁D₁)
  have hBD : B ≤ normalizer (D₁ : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₁n x (mem_inf.1 (h.B_le hx)).1 d hd
  have hsup : B ⊔ D₁ = D₁ ⊔ 𝒜₂ := by
    refine le_antisymm (sup_le ?_ le_sup_left) (sup_le le_sup_right
      ((le_sup_left.trans (le_sup_right.trans le_sup_right)).trans le_sup_left))
    refine sup_le ((zpowers_le.2 h.zD₁).trans le_sup_left) (sup_le (h.P₁D₁.trans le_sup_left)
      (sup_le le_sup_right (h.K₀D₁.trans le_sup_left)))
  have h1 := natCard_sup_mul_inf hBD
  rw [hsup, h.card_D₁A₂, h.card_B, h.hD₁card] at h1
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_zP₁]
  omega

theorem PtBase.U₂_eq [Finite G] :
    (zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)))) ⊓ D₂ =
      zpowers z ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) := by
  set B := zpowers z ⊔ ((𝒜₁ ⊔ (C₁ ⊓ C₂)) ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂))) with hB
  have hle : zpowers z ⊔ (𝒜₂ ⊔ (C₁ ⊓ C₂)) ≤ B ⊓ D₂ := le_inf
    (sup_le le_sup_left (le_sup_right.trans le_sup_right))
    (sup_le (zpowers_le.2 h.zD₂) h.P₂D₂)
  have hBD : B ≤ normalizer (D₂ : Set G) := fun x hx =>
    mem_normalizer_of_conj_mem fun d hd => h.hD₂n x (mem_inf.1 (h.B_le hx)).2 d hd
  have hsup : B ⊔ D₂ = D₂ ⊔ 𝒜₁ := by
    refine le_antisymm (sup_le ?_ le_sup_left) (sup_le le_sup_right
      ((le_sup_left.trans (le_sup_left.trans le_sup_right)).trans le_sup_left))
    refine sup_le ((zpowers_le.2 h.zD₂).trans le_sup_left) (sup_le
      (sup_le le_sup_right (h.K₀D₂.trans le_sup_left)) (h.P₂D₂.trans le_sup_left))
  have h1 := natCard_sup_mul_inf hBD
  rw [hsup, h.card_D₂A₁, h.card_B, h.hD₂card] at h1
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_zP₂]
  omega

end Basic

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
