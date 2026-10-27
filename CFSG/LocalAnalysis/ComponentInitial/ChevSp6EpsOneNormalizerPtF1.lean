module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtBasic

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

namespace PtF1

section Generic

variable {X : Type*} [Group X]

theorem characteristic_subgroupOf_of_map {D K : Subgroup X} (hKD : K ≤ D)
    (h : ∀ ϕ : D ≃* D, ((K.subgroupOf D).map ϕ.toMonoidHom).map D.subtype = K) :
    (K.subgroupOf D).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro ϕ
  apply Subgroup.map_injective D.subtype_injective
  rw [h ϕ, Subgroup.map_subgroupOf_eq_of_le hKD]

theorem mem_map_aut_iff {D K : Subgroup X} (ϕ : D ≃* D) {x : X} :
    x ∈ ((K.subgroupOf D).map ϕ.toMonoidHom).map D.subtype ↔
      ∃ k : D, (k : X) ∈ K ∧ ((ϕ k : D) : X) = x := by
  simp only [mem_map, mem_subgroupOf, MulEquiv.coe_toMonoidHom, coe_subtype]
  constructor
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩

theorem card_map_aut {D K : Subgroup X} (hKD : K ≤ D) (ϕ : D ≃* D) :
    Nat.card (((K.subgroupOf D).map ϕ.toMonoidHom).map D.subtype : Subgroup X) = Nat.card K := by
  rw [Subgroup.card_map_of_injective D.subtype_injective,
    Subgroup.card_map_of_injective ϕ.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hKD).toEquiv

theorem aut_mem_center {D : Subgroup X} (ϕ : D ≃* D) {k : D} (hk : k ∈ center D) :
    ϕ k ∈ center D := by
  rw [mem_center_iff] at hk ⊢
  intro y
  have h := congrArg ϕ (hk (ϕ.symm y))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem conj_mem_of_characteristic {D K : Subgroup X} (hK : (K.subgroupOf D).Characteristic)
    (hKD : K ≤ D) {g : X} (hg : g ∈ normalizer (D : Set X)) {x : X} (hx : x ∈ K) :
    g * x * g⁻¹ ∈ K := by
  have hmem : ∀ r : D, g * (r : X) * g⁻¹ ∈ D := fun r => (mem_normalizer_iff.1 hg r).1 r.2
  have hmem' : ∀ r : D, g⁻¹ * (r : X) * g ∈ D := fun r => by
    have h := (mem_normalizer_iff.1 (inv_mem hg) r).1 r.2
    rwa [inv_inv] at h
  let ϕ : D ≃* D :=
    { toFun := fun r => ⟨g * (r : X) * g⁻¹, hmem r⟩
      invFun := fun r => ⟨g⁻¹ * (r : X) * g, hmem' r⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a c => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have h1 := characteristic_iff_map_eq.1 hK ϕ
  have h2 : ϕ ⟨x, hKD hx⟩ ∈ (K.subgroupOf D).map ϕ.toMonoidHom :=
    mem_map_of_mem _ (mem_subgroupOf.2 hx)
  rw [h1] at h2
  exact mem_subgroupOf.1 h2

theorem normalizer_le_of_characteristic [Finite X] {D K : Subgroup X}
    (hK : (K.subgroupOf D).Characteristic) (hKD : K ≤ D) :
    normalizer (D : Set X) ≤ normalizer (K : Set X) := fun _ hg =>
  mem_normalizer_of_conj_mem fun _ hx => conj_mem_of_characteristic hK hKD hg hx

theorem pow_val_add_four {t : X} (ht : t ^ 4 = 1) (i j : ZMod 4) :
    t ^ (i + j).val = t ^ i.val * t ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ ht, pow_add]

theorem pow_val_neg_four {t : X} (ht : t ^ 4 = 1) (i : ZMod 4) :
    t ^ (-i).val = (t ^ i.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_val_add_four ht, neg_add_cancel, ZMod.val_zero, pow_zero]

private def dihedralFourHom {t s : X} (ht : t ^ 4 = 1) (hs : s ^ 2 = 1)
    (hst : s * t * s⁻¹ = t⁻¹) : DihedralGroup 4 →* X where
  toFun x := match x with
    | DihedralGroup.r i => t ^ i.val
    | DihedralGroup.sr i => s * t ^ i.val
  map_one' := by
    rw [DihedralGroup.one_def]
    change t ^ (0 : ZMod 4).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hss : s * s = 1 := by rw [← sq]; exact hs
    have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hconj : ∀ i : ZMod 4, t ^ (-i).val = s * t ^ i.val * s := fun i => by
      rw [pow_val_neg_four ht, ← inv_pow, ← hst, conj_pow, hs']
    rintro (i | i) (j | j)
    · change t ^ (i + j).val = t ^ i.val * t ^ j.val
      exact pow_val_add_four ht i j
    · change s * t ^ (j - i).val = t ^ i.val * (s * t ^ j.val)
      rw [sub_eq_neg_add, pow_val_add_four ht, hconj i]
      calc s * (s * t ^ i.val * s * t ^ j.val) = (s * s) * t ^ i.val * s * t ^ j.val := by group
        _ = t ^ i.val * (s * t ^ j.val) := by rw [hss]; group
    · change s * t ^ (i + j).val = s * t ^ i.val * t ^ j.val
      rw [pow_val_add_four ht, mul_assoc]
    · change t ^ (j - i).val = s * t ^ i.val * (s * t ^ j.val)
      rw [sub_eq_neg_add, pow_val_add_four ht, hconj i]
      group

end Generic

end PtF1

section Basic

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
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝐛₁" => ptB₁ he hb φ hzC hz
local notation "𝒵₁" => Subgroup.map C₁.subtype (center C₁)

namespace PtF1

theorem zB₁ : z ∈ ℬ₁ :=
  mem_sup_right (mem_zpowers z)

theorem zF₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : z ∈ F₁ :=
  h.hBF₁ zB₁

theorem zD₁' (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : z ∈ D₁ :=
  h.hFD₁ (zF₁ h)

theorem zN₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : z ∈ 𝒩₁ :=
  h.hD₁N (zD₁' h)

theorem A₁F₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : 𝒜₁ ≤ F₁ :=
  le_sup_left.trans h.hBF₁

theorem A₁C₁' (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : 𝒜₁ ≤ C₁ :=
  ptA_le_of_inf_eq hb φ h.hC₁B

theorem I₁A₁ : zpowers 𝐛₁ ≤ 𝒜₁ :=
  (zpowers_ptB₁_le he hb φ hzC hz).trans inf_le_left

theorem z_not_mem_C₁' (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : z ∉ C₁ :=
  fun hzc => by
    have h1 : z ∈ C₁ ⊓ ℬ₁ := mem_inf.2 ⟨hzc, zB₁⟩
    rw [h.hC₁B] at h1
    exact z_not_mem_ptA hb φ h.hinf hz h1

theorem z_inv {x : G} (hx : orderOf x = 2) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, ← hx]; exact pow_orderOf_eq_one x)

theorem I₁_comm (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {i x : G}
    (hi : i ∈ zpowers 𝐛₁) (hx : x ∈ 𝒩₁) : i * x = x * i := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hi
  exact Commute.zpow_left (h.hb₁c x hx).symm n

theorem sq_mem_of_mem_C₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {c : G}
    (hc : c ∈ C₁) : c ^ 2 ∈ zpowers 𝐛₁ := by
  rw [← h.hC₁sq]
  exact subset_closure ⟨c, hc, rfl⟩

theorem mem_D₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {x : G}
    (hx : x ∈ D₁) : x ∈ C₁ ∨ ∃ c ∈ C₁, x = z * c := by
  have hzN : zpowers z ≤ normalizer (C₁ : Set G) :=
    zpowers_le.2 (mem_normalizer_of_conj_mem fun c hc => h.hC₁n z (zN₁ h) c hc)
  have hxD : x ∈ ((zpowers z ⊔ C₁ : Subgroup G) : Set G) := by
    rw [h.hC₁z]
    exact hx
  rw [coe_mul_of_left_le_normalizer_right _ _ hzN] at hxD
  obtain ⟨s, hs, c, hc, rfl⟩ := hxD
  rcases eq_one_or_eq_of_mem_zpowers hz hs with rfl | rfl
  · left
    simpa using hc
  · exact Or.inr ⟨c, hc, rfl⟩

theorem sq_zc_mem_iff (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {c : G}
    (hc : c ∈ C₁) : (z * c) ^ 2 ∈ zpowers 𝐛₁ ↔ c ∈ F₁ := by
  have hc2 := sq_mem_of_mem_C₁ h hc
  have hzc : z * c ∈ 𝒩₁ := mul_mem (zN₁ h) (h.hD₁N (h.hC₁D hc))
  have hcomm := I₁_comm h (inv_mem hc2) hzc
  have hγ : z⁻¹ * (c⁻¹ * z * c) = (z * c) ^ 2 * (c ^ 2)⁻¹ := by
    calc z⁻¹ * (c⁻¹ * z * c) = z * (c * (c ^ 2)⁻¹) * z * c := by rw [z_inv hz]; group
      _ = z * c * ((c ^ 2)⁻¹ * (z * c)) := by group
      _ = z * c * ((z * c) * (c ^ 2)⁻¹) := by rw [hcomm]
      _ = (z * c) ^ 2 * (c ^ 2)⁻¹ := by rw [sq (z * c)]; group
  rw [← h.hγF₁ c (h.hC₁D hc), hγ]
  constructor
  · intro h1
    exact mul_mem h1 (inv_mem hc2)
  · intro h1
    have h2 := mul_mem h1 hc2
    rwa [inv_mul_cancel_right] at h2

theorem mem_F₁_of_sq_mem [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {x : G} (hx : x ∈ D₁) (hxC : x ∉ C₁) (hx2 : x ^ 2 ∈ zpowers 𝐛₁) : x ∈ F₁ := by
  rcases mem_D₁ h hx with hc | ⟨c, hc, rfl⟩
  · exact absurd hc hxC
  · exact mul_mem (zF₁ h) ((sq_zc_mem_iff h hc).1 hx2)

theorem sq_mem_of_mem_F₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {x : G} (hx : x ∈ F₁) : x ^ 2 ∈ zpowers 𝐛₁ := by
  rcases mem_D₁ h (h.hFD₁ hx) with hc | ⟨c, hc, rfl⟩
  · exact sq_mem_of_mem_C₁ h hc
  · refine (sq_zc_mem_iff h hc).2 ?_
    have h1 := mul_mem (inv_mem (zF₁ h)) hx
    rwa [inv_mul_cancel_left] at h1

theorem le_F₁_of_not_le [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {X : Subgroup G} (hXD : X ≤ D₁) (hXsq : ∀ x ∈ X, x ^ 2 ∈ zpowers 𝐛₁) (hXC : ¬ X ≤ C₁) :
    X ≤ F₁ := by
  obtain ⟨x, hx, hxC⟩ := IsConcreteLE.not_le_iff_exists.1 hXC
  have hxF := mem_F₁_of_sq_mem h (hXD hx) hxC (hXsq x hx)
  intro y hy
  by_cases hyC : y ∈ C₁
  · have hxy : x * y ∉ C₁ := fun h' => hxC (by
      have h1 := mul_mem h' (inv_mem hyC)
      rwa [mul_inv_cancel_right] at h1)
    have hxyF := mem_F₁_of_sq_mem h (hXD (mul_mem hx hy)) hxy (hXsq _ (mul_mem hx hy))
    have h1 := mul_mem (inv_mem hxF) hxyF
    rwa [inv_mul_cancel_left] at h1
  · exact mem_F₁_of_sq_mem h (hXD hy) hyC (hXsq y hy)

theorem eq_C₁_of_sq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {C : Subgroup G} (hCD : C ≤ D₁) (hCcard : Nat.card C = 1024)
    (hCsq : ∀ x ∈ C, x ^ 2 ∈ zpowers 𝐛₁) : C = C₁ := by
  by_cases hCC : C ≤ C₁
  · exact Subgroup.eq_of_le_of_card_ge hCC (by rw [hCcard, h.hC₁card])
  · have h1 := Subgroup.card_le_of_le (le_F₁_of_not_le h hCD hCsq hCC)
    rw [hCcard, h.hF₁card] at h1
    norm_num at h1

end PtF1

theorem PtBase.eq_C₁_of_le_D₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {C : Subgroup G} (_hIC : zpowers 𝐛₁ ≤ C) (hCD : C ≤ D₁) (hCcard : Nat.card C = 1024)
    (hCsq : ∀ x ∈ C, x ^ 2 ∈ zpowers 𝐛₁)
    (_hCcomm : ∀ x ∈ C, ∀ y ∈ C, x⁻¹ * y⁻¹ * x * y ∈ zpowers 𝐛₁) : C = C₁ :=
  PtF1.eq_C₁_of_sq h hCD hCcard hCsq

namespace PtF1

theorem mem_center_D₁_iff (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {d : D₁} :
    d ∈ center D₁ ↔ (d : G) ∈ zpowers 𝐛₁ := by
  rw [← h.hZD₁]
  constructor
  · intro hd
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d', hd', hdd'⟩
    rwa [Subtype.ext hdd'] at hd'

theorem aut_mem_I₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (ϕ : D₁ ≃* D₁)
    {d : D₁} (hd : (d : G) ∈ zpowers 𝐛₁) : ((ϕ d : D₁) : G) ∈ zpowers 𝐛₁ :=
  (mem_center_D₁_iff h).1 (aut_mem_center ϕ ((mem_center_D₁_iff h).2 hd))

theorem sq_mem_map_aut (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (ϕ : D₁ ≃* D₁)
    {K : Subgroup G} (hK : ∀ x ∈ K, x ^ 2 ∈ zpowers 𝐛₁) {x : G}
    (hx : x ∈ ((K.subgroupOf D₁).map ϕ.toMonoidHom).map D₁.subtype) : x ^ 2 ∈ zpowers 𝐛₁ := by
  obtain ⟨k, hk, rfl⟩ := (mem_map_aut_iff ϕ).1 hx
  have h1 := aut_mem_I₁ h ϕ (d := k ^ 2) (by rw [Subgroup.coe_pow]; exact hK _ hk)
  rwa [map_pow, Subgroup.coe_pow] at h1

theorem eq_F₁_of_sq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {X : Subgroup G} (hXD : X ≤ D₁) (hXcard : Nat.card X = 128)
    (hXsq : ∀ x ∈ X, x ^ 2 ∈ zpowers 𝐛₁) (hXC : ¬ X ≤ C₁) : X = F₁ :=
  Subgroup.eq_of_le_of_card_ge (le_F₁_of_not_le h hXD hXsq hXC) (by rw [hXcard, h.hF₁card])

end PtF1

theorem PtBase.characteristic_C₁ [Finite G]
    (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : (C₁.subgroupOf D₁).Characteristic :=
  PtF1.characteristic_subgroupOf_of_map h.hC₁D fun ϕ =>
    PtF1.eq_C₁_of_sq h (map_subtype_le _) (by rw [PtF1.card_map_aut h.hC₁D, h.hC₁card])
      (fun _ hx => PtF1.sq_mem_map_aut h ϕ (fun _ hy => PtF1.sq_mem_of_mem_C₁ h hy) hx)

theorem PtBase.characteristic_F₁ [Finite G]
    (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : (F₁.subgroupOf D₁).Characteristic :=
  PtF1.characteristic_subgroupOf_of_map h.hFD₁ fun ϕ => by
    refine PtF1.eq_F₁_of_sq h (map_subtype_le _) (by rw [PtF1.card_map_aut h.hFD₁, h.hF₁card])
      (fun _ hx => PtF1.sq_mem_map_aut h ϕ (fun _ hy => PtF1.sq_mem_of_mem_F₁ h hy) hx) ?_
    intro hle
    have hz' : ((ϕ ⟨z, PtF1.zD₁' h⟩ : D₁) : G) ∈ C₁ :=
      hle ((PtF1.mem_map_aut_iff ϕ).2 ⟨_, PtF1.zF₁ h, rfl⟩)
    apply PtF1.z_not_mem_C₁' h
    have h1 := characteristic_iff_map_eq.1 h.characteristic_C₁ ϕ.symm
    have h2 : ϕ.symm (ϕ ⟨z, PtF1.zD₁' h⟩) ∈ (C₁.subgroupOf D₁).map ϕ.symm.toMonoidHom :=
      mem_map_of_mem _ (mem_subgroupOf.2 hz')
    rw [h1, MulEquiv.symm_apply_apply] at h2
    exact mem_subgroupOf.1 h2

theorem PtBase.sq_center_C₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    {x | ∃ y ∈ 𝒵₁, y ^ 2 = x} = (zpowers 𝐛₁ : Set G) := by
  have hcomm : ∀ y ∈ 𝒵₁, ∀ y' ∈ 𝒵₁, y * y' = y' * y := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', -, rfl⟩
    exact congrArg Subtype.val (mem_center_iff.1 ha a').symm
  let S : Subgroup G :=
    { carrier := {x | ∃ y ∈ 𝒵₁, y ^ 2 = x}
      one_mem' := ⟨1, one_mem _, one_pow 2⟩
      mul_mem' := by
        rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
        exact ⟨y * y', mul_mem hy hy', (Commute.mul_pow (hcomm y hy y' hy') 2)⟩
      inv_mem' := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, inv_mem hy, inv_pow y 2⟩ }
  have hS : closure {x | ∃ y ∈ 𝒵₁, y ^ 2 = x} = S := closure_eq S
  rw [← h.hZ₁sq, hS]
  rfl

namespace PtF1

variable {t : G}

theorem t_mem_C₁ (ht : t ∈ 𝒵₁) : t ∈ C₁ := by
  obtain ⟨c, -, rfl⟩ := ht
  exact c.2

theorem card_Z₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : Nat.card 𝒵₁ = 4 := by
  rw [Subgroup.card_map_of_injective C₁.subtype_injective, h.hZ₁card]

theorem orderOf_t (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (htZ : zpowers t = 𝒵₁) : orderOf t = 4 := by
  rw [← Nat.card_zpowers, htZ, card_Z₁ h]

theorem b₁_sq : 𝐛₁ ^ 2 = 1 := by
  rw [← orderOf_ptB₁ he hb φ hzC hz]
  exact pow_orderOf_eq_one _

theorem b₁_ne_one : 𝐛₁ ≠ 1 := fun h1 => by
  have h2 := orderOf_ptB₁ he hb φ hzC hz
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem sq_ne_one_of_orderOf (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (htZ : zpowers t = 𝒵₁) : t ^ 2 ≠ 1 := fun h2 => by
  have h3 := orderOf_le_of_pow_eq_one (by norm_num) h2
  rw [orderOf_t h htZ] at h3
  exact absurd h3 (by norm_num)

theorem t_sq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (ht : t ∈ 𝒵₁)
    (htZ : zpowers t = 𝒵₁) : t ^ 2 = 𝐛₁ := by
  have h1 : t ^ 2 ∈ (zpowers 𝐛₁ : Set G) := by
    rw [← h.sq_center_C₁]
    exact ⟨t, ht, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) h1 with h2 | h2
  · exact absurd h2 (sq_ne_one_of_orderOf h htZ)
  · exact h2

theorem t_mem_F₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (ht : t ∈ 𝒵₁) :
    t ∈ F₁ := by
  have h1 : t ∈ C₁ ⊓ F₁ := by
    rw [h.hE₁]
    exact mem_sup_right ht
  exact (mem_inf.1 h1).2

theorem t_not_mem_A₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (ht : t ∈ 𝒵₁)
    (htZ : zpowers t = 𝒵₁) : t ∉ 𝒜₁ := fun htA => by
  have h1 : t ∈ 𝒵₁ ⊓ 𝒜₁ := mem_inf.2 ⟨ht, htA⟩
  rw [h.hZ₁A] at h1
  apply sq_ne_one_of_orderOf h htZ
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) h1 with rfl | rfl
  · exact one_pow 2
  · exact b₁_sq

theorem A₁_comm_F₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {a f : G}
    (ha : a ∈ 𝒜₁) (hf : f ∈ F₁) : a * f = f * a := by
  rw [← h.hZF₁] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  exact congrArg Subtype.val (mem_center_iff.1 hc ⟨f, hf⟩).symm

theorem sq_A₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {a : G} (ha : a ∈ 𝒜₁) :
    a ^ 2 = 1 := by
  have := (ptA_facts he hb h.hnd φ).2.1
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha

theorem sq_mul_A₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {a y : G}
    (ha : a ∈ 𝒜₁) (hy : y ∈ F₁) : (a * y) ^ 2 = y ^ 2 := by
  have h1 := A₁_comm_F₁ h ha hy
  have h2 := sq_A₁ h ha
  rw [sq] at h2
  calc (a * y) ^ 2 = a * (y * a) * y := by rw [sq]; group
    _ = (a * a) * (y * y) := by rw [← h1]; group
    _ = y ^ 2 := by rw [h2, one_mul, sq]

theorem F₁_eq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) (ht : t ∈ 𝒵₁)
    (htZ : zpowers t = 𝒵₁) : F₁ = 𝒜₁ ⊔ closure {z, t} := by
  have hzS : z ∈ ({z, t} : Set G) := Set.mem_insert z {t}
  have htS : t ∈ ({z, t} : Set G) := Set.mem_insert_of_mem z (Set.mem_singleton t)
  have hle : 𝒜₁ ⊔ closure ({z, t} : Set G) ≤ F₁ := by
    refine sup_le (A₁F₁ h) ((closure_le F₁).2 ?_)
    intro x hx
    rcases hx with rfl | hx
    · exact zF₁ h
    · rw [Set.mem_singleton_iff.1 hx]
      exact t_mem_F₁ h ht
  have hE : C₁ ⊓ F₁ ≤ 𝒜₁ ⊔ closure ({z, t} : Set G) := by
    rw [h.hE₁, ← htZ]
    exact sup_le_sup_left (zpowers_le.2 (subset_closure htS)) _
  have hzX : z ∈ 𝒜₁ ⊔ closure ({z, t} : Set G) := mem_sup_right (subset_closure hzS)
  have h64 : 64 ∣ Nat.card (𝒜₁ ⊔ closure ({z, t} : Set G) : Subgroup G) := by
    rw [← h.hE₁card]
    exact Subgroup.card_dvd_of_le hE
  have h128 : Nat.card (𝒜₁ ⊔ closure ({z, t} : Set G) : Subgroup G) ∣ 128 := by
    rw [← h.hF₁card]
    exact Subgroup.card_dvd_of_le hle
  have hne : Nat.card (𝒜₁ ⊔ closure ({z, t} : Set G) : Subgroup G) ≠ 64 := fun h64' => by
    have heq : C₁ ⊓ F₁ = 𝒜₁ ⊔ closure ({z, t} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hE (by rw [h64', h.hE₁card])
    rw [← heq] at hzX
    exact z_not_mem_C₁' h (mem_inf.1 hzX).1
  have hX128 : Nat.card (𝒜₁ ⊔ closure ({z, t} : Set G) : Subgroup G) = 128 := by
    obtain ⟨m, hm⟩ := h64
    rw [hm] at h128 hne ⊢
    have h2 : 64 * m ∣ 64 * 2 := h128
    have hm2 : m ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    have : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
    interval_cases m <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hX128, h.hF₁card])).symm

theorem z_conj_t [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) : z * t * z⁻¹ = t⁻¹ := by
  have htF := t_mem_F₁ h ht
  have hγ : z⁻¹ * (t⁻¹ * z * t) ∈ zpowers 𝐛₁ := (h.hγF₁ t (h.hFD₁ htF)).2 htF
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) hγ with h1 | h1
  · exfalso
    have hzt : t * z = z * t := by
      have h2 : t⁻¹ * z * t = z := by
        calc t⁻¹ * z * t = z * (z⁻¹ * (t⁻¹ * z * t)) := by group
          _ = z := by rw [h1, mul_one]
      calc t * z = t * (t⁻¹ * z * t) := by rw [h2]
        _ = z * t := by group
    apply t_not_mem_A₁ h ht htZ
    have hcen : 𝒜₁ ⊔ closure ({z, t} : Set G) ≤ centralizer ({t} : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_singleton_iff.2 (A₁_comm_F₁ h ha htF))
        ((closure_le _).2 ?_)
      intro x hx
      rcases hx with rfl | hx
      · exact mem_centralizer_singleton_iff.2 hzt.symm
      · rw [Set.mem_singleton_iff.1 hx]
        exact mem_centralizer_singleton_iff.2 rfl
    rw [← h.hZF₁]
    refine ⟨⟨t, htF⟩, mem_center_iff.2 fun f => Subtype.ext ?_, rfl⟩
    have hf : (f : G) ∈ centralizer ({t} : Set G) := hcen (by rw [← F₁_eq h ht htZ]; exact f.2)
    exact mem_centralizer_singleton_iff.1 hf
  · have h2 : z⁻¹ * t⁻¹ * z = t := by
      calc z⁻¹ * t⁻¹ * z = z⁻¹ * (t⁻¹ * z * t) * t⁻¹ := by group
        _ = t ^ 2 * t⁻¹ := by rw [h1, t_sq h ht htZ]
        _ = t := by group
    calc z * t * z⁻¹ = z⁻¹ * t * z := by rw [z_inv hz]
      _ = (z⁻¹ * t⁻¹ * z)⁻¹ := by group
      _ = t⁻¹ := by rw [h2]

theorem zt_sq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) : (z * t) ^ 2 = 1 := by
  calc (z * t) ^ 2 = (z * t * z⁻¹) * t := by rw [sq, z_inv hz]; group
    _ = 1 := by rw [z_conj_t h ht htZ, inv_mul_cancel]

theorem mem_E₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) {x : G} (hx : x ∈ C₁ ⊓ F₁) :
    ∃ a ∈ 𝒜₁, x = a ∨ x = a * t := by
  rw [h.hE₁, ← htZ] at hx
  have hT : zpowers t ≤ centralizer (𝒜₁ : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => A₁_comm_F₁ h ha (t_mem_F₁ h ht))
  obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_of_le_centralizer hT).1 hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hs
  have htb : t ^ (2 : ℤ) = 𝐛₁ := by
    rw [zpow_ofNat]
    exact t_sq h ht htZ
  have hn : t ^ n = 𝐛₁ ^ (n / 2) * t ^ (n % 2) := by
    rw [← htb, ← _root_.zpow_mul, ← _root_.zpow_add, Int.mul_ediv_add_emod]
  have hbA : 𝐛₁ ^ (n / 2) ∈ 𝒜₁ := zpow_mem (I₁A₁ (mem_zpowers _)) _
  refine ⟨a * 𝐛₁ ^ (n / 2), mul_mem ha hbA, ?_⟩
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [hn, h0, zpow_zero, mul_one]
  · right
    rw [hn, h1, zpow_one, mul_assoc]

theorem elem_cases [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) {x : G} (hxF : x ∈ F₁) (hx2 : x ^ 2 = 1) :
    x ∈ 𝒜₁ ∨ (∃ a ∈ 𝒜₁, x = z * a) ∨ (∃ a ∈ 𝒜₁, x = z * (a * t)) := by
  rcases mem_D₁ h (h.hFD₁ hxF) with hxC | ⟨c, hc, rfl⟩
  · obtain ⟨a, ha, rfl | rfl⟩ := mem_E₁ h ht htZ (mem_inf.2 ⟨hxC, hxF⟩)
    · exact Or.inl ha
    · exfalso
      rw [sq_mul_A₁ h ha (t_mem_F₁ h ht), t_sq h ht htZ] at hx2
      exact b₁_ne_one hx2
  · have hcF : c ∈ F₁ := by
      have h1 := mul_mem (inv_mem (zF₁ h)) hxF
      rwa [inv_mul_cancel_left] at h1
    obtain ⟨a, ha, hca | hca⟩ := mem_E₁ h ht htZ (mem_inf.2 ⟨hc, hcF⟩)
    · exact Or.inr (Or.inl ⟨a, ha, by rw [hca]⟩)
    · exact Or.inr (Or.inr ⟨a, ha, by rw [hca]⟩)

include hzC in
theorem z_comm_A₁ {a : G} (ha : a ∈ 𝒜₁) : z * a = a * z :=
  (mul_comm_z hzC (pullSub_le φ _ ha)).symm

theorem card_B₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : Nat.card ℬ₁ = 64 :=
  (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.2.1

theorem card_A₁' (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) : Nat.card 𝒜₁ = 32 :=
  (ptA_facts he hb h.hnd φ).2.2.1

theorem zt_not_mem_A₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) : z * t ∉ 𝒜₁ := fun hA => by
  have h1 := mul_mem (A₁C₁' h hA) (inv_mem (t_mem_C₁ ht))
  rw [mul_inv_cancel_right] at h1
  exact z_not_mem_C₁' h h1

theorem card_A₁_zt [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) : Nat.card (𝒜₁ ⊔ zpowers (z * t) : Subgroup G) = 64 := by
  have hztF : z * t ∈ F₁ := mul_mem (zF₁ h) (t_mem_F₁ h ht)
  have hord : orderOf (z * t) = 2 := orderOf_eq_prime (zt_sq h ht htZ) fun h1 =>
    zt_not_mem_A₁ h ht (by rw [h1]; exact one_mem _)
  have hT : zpowers (z * t) ≤ centralizer (𝒜₁ : Set G) :=
    zpowers_le.2 (mem_centralizer_iff.2 fun a ha => A₁_comm_F₁ h ha hztF)
  have hinf : 𝒜₁ ⊓ zpowers (z * t) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxZ⟩ := mem_inf.1 hx
    rcases eq_one_or_eq_of_mem_zpowers hord hxZ with rfl | rfl
    · exact one_mem _
    · exact absurd hxA (zt_not_mem_A₁ h ht)
  rw [card_sup_eq_mul hT hinf, card_A₁' h, Nat.card_zpowers, hord]

theorem elem_eq [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) {X : Subgroup G} (hXF : X ≤ F₁)
    (hX : IsElementaryAbelian 2 X) (hXcard : Nat.card X = 64) :
    X = ℬ₁ ∨ X = 𝒜₁ ⊔ zpowers (z * t) := by
  have hX2 : ∀ x ∈ X, x ^ 2 = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  have hcases := fun x hx => elem_cases h ht htZ (hXF hx) (hX2 x hx)
  by_cases hzA : ∃ a ∈ 𝒜₁, z * a ∈ X
  · left
    obtain ⟨a₀, ha₀, hx₀⟩ := hzA
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [hXcard, card_B₁ h])
    rcases hcases y hy with hyA | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact mem_sup_left hyA
    · exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left ha)
    · exfalso
      have hm := hX2 _ (mul_mem hx₀ hy)
      have heq : z * a₀ * (z * (a * t)) = (a₀ * a) * t := by
        calc z * a₀ * (z * (a * t)) = a₀ * (z * z) * (a * t) := by
              rw [z_comm_A₁ (hzC := hzC) ha₀]; group
          _ = (a₀ * a) * t := by rw [← sq, ← hz, pow_orderOf_eq_one]; group
      rw [heq, sq_mul_A₁ h (mul_mem ha₀ ha) (t_mem_F₁ h ht), t_sq h ht htZ] at hm
      exact b₁_ne_one hm
  · right
    push Not at hzA
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => ?_) (by rw [hXcard, card_A₁_zt h ht htZ])
    rcases hcases y hy with hyA | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact mem_sup_left hyA
    · exact absurd hy (hzA a ha)
    · have heq : z * (a * t) = a * (z * t) := by
        rw [← mul_assoc, z_comm_A₁ (hzC := hzC) ha, mul_assoc]
      rw [heq]
      exact mul_mem (mem_sup_left ha) (mem_sup_right (mem_zpowers _))

theorem F₁_iso [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) :
    Nonempty (↥(𝒜₁ ⊔ closure {z, t} : Subgroup G) ≃*
      DihedralGroup 4 × Multiplicative (Fin 4 → ZMod 2)) := by
  have ht4 : t ^ 4 = 1 := by
    rw [← orderOf_t h htZ]
    exact pow_orderOf_eq_one t
  have hz2 : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  let δ := dihedralFourHom ht4 hz2 (z_conj_t h ht htZ)
  let α : Multiplicative (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))) →* G :=
    L.subtype.comp (φ.symm.toMonoidHom.comp ((ptHomV he hb).comp
      (AddMonoidHom.toMultiplicative (AddMonoidHom.inl _ (ZMod 2)))))
  have hα : ∀ w, α w = ((φ.symm (ptHomV he hb
      (Multiplicative.ofAdd (Multiplicative.toAdd w, 0))) : L) : G) := fun w => rfl
  have hαA : ∀ w, α w ∈ 𝒜₁ := fun w => (mem_ptA_iff he hb φ).2 ⟨_, (hα w).symm⟩
  have hαinj : Function.Injective α := by
    intro w w' hww'
    rw [hα, hα] at hww'
    have h1 := ptHomV_injective he hb (φ.symm.injective (Subtype.ext hww'))
    have h2 := congrArg (fun v => (Multiplicative.toAdd v).1) h1
    exact Multiplicative.toAdd.injective h2
  have hδF : ∀ d, δ d ∈ F₁ := by
    rintro (i | i)
    · exact pow_mem (t_mem_F₁ h ht) _
    · exact mul_mem (zF₁ h) (pow_mem (t_mem_F₁ h ht) _)
  have hcomm : ∀ d w, Commute (δ d) (α w) := fun d w =>
    (A₁_comm_F₁ h (hαA w) (hδF d)).symm
  let Ψ := MonoidHom.noncommCoprod δ α hcomm
  have hΨ : ∀ p, Ψ p = δ p.1 * α p.2 := fun p => rfl
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, w⟩ hdw
    rw [hΨ] at hdw
    have hδA : δ d ∈ 𝒜₁ := by
      rw [eq_inv_of_mul_eq_one_left hdw]
      exact inv_mem (hαA w)
    rcases d with i | i
    · change t ^ i.val ∈ 𝒜₁ at hδA
      change t ^ i.val * α w = 1 at hdw
      have hI : t ^ i.val ∈ zpowers 𝐛₁ := by
        rw [← h.hZ₁A]
        exact mem_inf.2 ⟨by rw [← htZ]; exact pow_mem (mem_zpowers t) _, hδA⟩
      rcases eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) hI with h1 | h1
      · have hi : i = 0 := by
          have h2 := orderOf_dvd_of_pow_eq_one h1
          rw [orderOf_t h htZ] at h2
          have h3 := ZMod.val_lt i
          have h4 : i.val = 0 := by omega
          exact (ZMod.val_eq_zero i).1 h4
        have hw : α w = 1 := by rw [h1, one_mul] at hdw; exact hdw
        have hw1 : w = 1 := hαinj (by rw [hw, map_one])
        rw [hi, hw1]
        rfl
      · exfalso
        have hw : α w = 𝐛₁ := by
          rw [h1] at hdw
          rw [eq_inv_of_mul_eq_one_right hdw, z_inv (orderOf_ptB₁ he hb φ hzC hz)]
        rw [hα, ptB₁, ptHom_pt] at hw
        have h2 := ptHomV_injective he hb (φ.symm.injective (Subtype.ext hw))
        have h3 := congrArg (fun v => (Multiplicative.toAdd v).2) h2
        exact zero_ne_one h3
    · exfalso
      change z * t ^ i.val ∈ 𝒜₁ at hδA
      have h1 := mul_mem (A₁C₁' h hδA) (inv_mem (pow_mem (t_mem_C₁ ht) i.val))
      rw [mul_inv_cancel_right] at h1
      exact z_not_mem_C₁' h h1
  have hrange : Ψ.range = F₁ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨⟨d, w⟩, rfl⟩
      rw [hΨ]
      exact mul_mem (hδF d) (A₁F₁ h (hαA w))
    · rw [h.hF₁card, ← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv, Nat.card_prod,
        DihedralGroup.nat_card]
      change 128 ≤ 2 * 4 * Nat.card (pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)))
      rw [card_pairOrth_eq he hb h.hnd]
  have hfin : FiniteDimensional (ZMod 2) V :=
    Module.finite_of_finrank_pos (by rw [h.hV]; norm_num)
  have h4 := finrank_pairOrth_eq he hb h.hnd
  let l : pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0)) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [h4, Module.finrank_fin_fun])
  exact ⟨(MulEquiv.subgroupCongr ((F₁_eq h ht htZ).symm.trans hrange.symm)).trans
    ((MonoidHom.ofInjective hΨinj).symm.trans
      (MulEquiv.prodCongr (MulEquiv.refl _) (AddEquiv.toMultiplicative l.toAddEquiv)))⟩

end PtF1

theorem PtBase.F₁_structure [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {t : G} (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) :
    F₁ = 𝒜₁ ⊔ closure {z, t} ∧
    Nonempty (↥(𝒜₁ ⊔ closure {z, t} : Subgroup G) ≃*
      DihedralGroup 4 × Multiplicative (Fin 4 → ZMod 2)) ∧
    ∀ X : Subgroup G, X ≤ F₁ → IsElementaryAbelian 2 X → Nat.card X = 64 →
      X = ℬ₁ ∨ X = 𝒜₁ ⊔ zpowers (z * t) :=
  ⟨PtF1.F₁_eq h ht htZ, PtF1.F₁_iso h ht htZ, fun _ hXF hX hXcard =>
    PtF1.elem_eq h ht htZ hXF hX hXcard⟩

namespace PtF1

theorem exists_gen [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    ∃ t ∈ 𝒵₁, zpowers t = 𝒵₁ := by
  obtain ⟨ψ⟩ := h.hZ₁iso
  have ht : (((ψ.symm (Multiplicative.ofAdd 1) : center C₁) : C₁) : G) ∈ 𝒵₁ :=
    ⟨_, (ψ.symm (Multiplicative.ofAdd 1)).2, rfl⟩
  refine ⟨_, ht, Subgroup.eq_of_le_of_card_ge (zpowers_le.2 ht) ?_⟩
  rw [card_Z₁ h, Nat.card_zpowers, Subgroup.orderOf_coe, Subgroup.orderOf_coe,
    MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

theorem mem_map_conj {g x : G} {H : Subgroup G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [mem_map_equiv, MulAut.conj_symm_apply]

theorem card_map_conj (g : G) (H : Subgroup G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective

theorem sq_B₁ (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) {y : G} (hy : y ∈ ℬ₁) :
    y ^ 2 = 1 := by
  have := (ptSub_facts he hb h.hnd φ hzC h.hinf hz).2.1
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) y hy

theorem conj_B₁_cases [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {t : G} (ht : t ∈ 𝒵₁) (htZ : zpowers t = 𝒵₁) {g : G} (hg : g ∈ normalizer (F₁ : Set G)) :
    Subgroup.map (MulAut.conj g).toMonoidHom ℬ₁ = ℬ₁ ∨
      Subgroup.map (MulAut.conj g).toMonoidHom ℬ₁ = 𝒜₁ ⊔ zpowers (z * t) := by
  refine elem_eq h ht htZ ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hg y).1 (h.hBF₁ hy)
  · refine elemAbelian_of_sq_eq_one ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow, sq_B₁ h hy, mul_one,
      mul_inv_cancel]
  · rw [card_map_conj, card_B₁ h]

theorem mem_N₁_iff [Finite G] {g : G} :
    g ∈ 𝒩₁ ↔ Subgroup.map (MulAut.conj g).toMonoidHom ℬ₁ = ℬ₁ := by
  constructor
  · intro hg
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hg y).1 hy
    · rw [card_map_conj]
  · intro hg
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    rw [← hg]
    exact ⟨y, hy, rfl⟩

theorem inv_mul_mem_N₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {g k : G} (hg : g ∈ normalizer (F₁ : Set G)) (hk : k ∈ normalizer (F₁ : Set G))
    (hgN : g ∉ 𝒩₁) (hkN : k ∉ 𝒩₁) : g⁻¹ * k ∈ 𝒩₁ := by
  obtain ⟨t, ht, htZ⟩ := exists_gen h
  have hg' := (conj_B₁_cases h ht htZ hg).resolve_left fun h1 => hgN (mem_N₁_iff.2 h1)
  have hk' := (conj_B₁_cases h ht htZ hk).resolve_left fun h1 => hkN (mem_N₁_iff.2 h1)
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  have h1 : k * y * k⁻¹ ∈ Subgroup.map (MulAut.conj g).toMonoidHom ℬ₁ := by
    rw [hg', ← hk']
    exact ⟨y, hy, rfl⟩
  have h2 := mem_map_conj.1 h1
  have h3 : g⁻¹ * k * y * (g⁻¹ * k)⁻¹ = g⁻¹ * (k * y * k⁻¹) * g := by group
  rw [h3]
  exact h2

theorem N₁_le_normalizer_F₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    𝒩₁ ≤ normalizer (F₁ : Set G) := fun n hn =>
  mem_normalizer_of_conj_mem fun f hf => h.hF₁n n hn f hf

theorem conj_mem_N₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁)
    {g n : G} (hg : g ∈ normalizer (F₁ : Set G)) (hn : n ∈ 𝒩₁) : g * n * g⁻¹ ∈ 𝒩₁ := by
  by_cases hgN : g ∈ 𝒩₁
  · exact mul_mem (mul_mem hgN hn) (inv_mem hgN)
  by_contra hb
  have hb' : g * n * g⁻¹ ∈ normalizer (F₁ : Set G) :=
    mul_mem (mul_mem hg (N₁_le_normalizer_F₁ h hn)) (inv_mem hg)
  have h1 := inv_mul_mem_N₁ h hg hb' hgN hb
  have h2 : g⁻¹ * (g * n * g⁻¹) = n * g⁻¹ := by group
  rw [h2] at h1
  have h3 := mul_mem (inv_mem hn) h1
  rw [inv_mul_cancel_left] at h3
  exact hgN (by simpa using inv_mem h3)

theorem normalizer_F₁_le [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    normalizer (F₁ : Set G) ≤ normalizer (D₁ : Set G) := by
  intro g hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 D₁ := IsPGroup.of_card (n := 11) (by rw [h.hD₁card]; norm_num)
  have hKN : D₁.map (MulAut.conj g).toMonoidHom ≤ 𝒩₁ := by
    rintro _ ⟨d, hd, rfl⟩
    exact conj_mem_N₁ h hg (h.hD₁N hd)
  have hKn : ∀ n ∈ 𝒩₁, ∀ k ∈ D₁.map (MulAut.conj g).toMonoidHom,
      n * k * n⁻¹ ∈ D₁.map (MulAut.conj g).toMonoidHom := by
    rintro n hn _ ⟨d, hd, rfl⟩
    have hn' : g⁻¹ * n * g⁻¹⁻¹ ∈ 𝒩₁ := conj_mem_N₁ h (inv_mem hg) hn
    rw [inv_inv] at hn'
    refine ⟨(g⁻¹ * n * g) * d * (g⁻¹ * n * g)⁻¹, h.hD₁n _ hn' d hd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hle := le_pCoreOf 2 hKN hKn (hp.map _)
  rw [← h.hD₁] at hle
  exact mem_normalizer_of_conj_mem fun d hd => hle ⟨d, hd, rfl⟩

theorem relIndex_le_two [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    (𝒩₁).relIndex (normalizer (F₁ : Set G)) ≤ 2 := by
  by_cases hK : ∃ g₀ ∈ normalizer (F₁ : Set G), g₀ ∉ 𝒩₁
  · obtain ⟨g₀, hg₀, hg₀N⟩ := hK
    rw [Subgroup.relIndex, Subgroup.index]
    let f : Bool → ↥(normalizer (F₁ : Set G)) ⧸ (𝒩₁).subgroupOf (normalizer (F₁ : Set G)) :=
      fun c => if c then QuotientGroup.mk ⟨g₀, hg₀⟩ else QuotientGroup.mk 1
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H k =>
        by_cases hk : (k : G) ∈ 𝒩₁
        · refine ⟨false, ?_⟩
          change (QuotientGroup.mk 1 : _ ⧸ (𝒩₁).subgroupOf (normalizer (F₁ : Set G))) =
            QuotientGroup.mk k
          refine QuotientGroup.eq.2 ?_
          rw [mem_subgroupOf, inv_one, one_mul]
          exact hk
        · refine ⟨true, ?_⟩
          change (QuotientGroup.mk ⟨g₀, hg₀⟩ : _ ⧸ (𝒩₁).subgroupOf (normalizer (F₁ : Set G))) =
            QuotientGroup.mk k
          refine QuotientGroup.eq.2 ?_
          rw [mem_subgroupOf]
          exact inv_mul_mem_N₁ h hg₀ k.2 hg₀N hk
    calc Nat.card (↥(normalizer (F₁ : Set G)) ⧸ (𝒩₁).subgroupOf (normalizer (F₁ : Set G)))
        ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
      _ = 2 := by simp
  · push Not at hK
    rw [Subgroup.relIndex_eq_one.2 hK]
    norm_num

end PtF1

theorem PtBase.normalizer_D₁ [Finite G] (h : PtBase he hb φ hzC hz D₂ C₂ E₂ ν₂ σ D₁ C₁ F₁ ν₁) :
    normalizer (D₁ : Set G) = normalizer (F₁ : Set G) ∧
    normalizer (D₁ : Set G) ≤ normalizer (C₁ : Set G) ∧ 𝒩₁ ≤ normalizer (D₁ : Set G) ∧
    (𝒩₁).relIndex (normalizer (D₁ : Set G)) ≤ 2 := by
  have hDF : normalizer (D₁ : Set G) = normalizer (F₁ : Set G) :=
    le_antisymm (PtF1.normalizer_le_of_characteristic h.characteristic_F₁ h.hFD₁)
      (PtF1.normalizer_F₁_le h)
  refine ⟨hDF, PtF1.normalizer_le_of_characteristic h.characteristic_C₁ h.hC₁D,
    fun n hn => mem_normalizer_of_conj_mem fun d hd => h.hD₁n n hn d hd, ?_⟩
  rw [hDF]
  exact PtF1.relIndex_le_two h

end Basic

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.EpsOne
