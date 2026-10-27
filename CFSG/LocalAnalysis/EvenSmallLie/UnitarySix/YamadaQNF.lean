module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQW
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQCount
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDD1Elem
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ
open scoped commutatorElement

theorem mX_e0 (k : Fin 4) (hk : (mX k).mulVec (Pi.single 0 1) = Pi.single 0 1) : k = 0 := by
  revert k; decide

variable {G : Type*} [Group G]

namespace Data

@[expose] def R₀ (d : Data G) : Subgroup G :=
  ((d.D₁ ⊓ centralizer ({d.e} : Set G)) ⊔ zpowers d.a₀) ⊔ zpowers d.t

end Data

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d)
include h

omit [Finite G] in
theorem X₁_le_L : d.X₁ ≤ d.L := fun _ hx => h.Λ_le_L (h.X₁_le_Λ hx)

theorem X₁_inf_D₄ (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {d₀ : G} (hd₀ : d₀ ∈ d.D₄)
    (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {x : G} (hx : x ∈ d.X₁) (hxD : x ∈ d.D₄) : x = 1 := by
  obtain ⟨k, rfl⟩ := h.exists_xs hx
  have h1 := h.conj_xs_kap hd₀ hB hV k (Pi.single 0 1)
  rw [h.D₄_comm hxD (h.kap_mem hd₀ _), mul_inv_cancel_right] at h1
  have hk := mX_e0 k (h.kap_injective hd₀ hB hV hθ h1).symm
  rw [hk]; rfl

theorem X₁_inf_D (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {d₀ : G} (hd₀ : d₀ ∈ d.D₄)
    (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) : d.X₁ ⊓ d.D = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hx, hxD⟩
  have hxH : x ∈ d.D ⊓ d.H := ⟨hxD, h.L_le_H (h.X₁_le_L hx)⟩
  rw [h.D_inf_H, h.mem_withT_iff h.A₄_le_L] at hxH
  rcases hxH with hxA | hxA
  · exact h.X₁_inf_D₄ hB hV hd₀ hθ hx (h.A₄_le_D₄ hxA)
  · exfalso
    apply h.t_not_mem_L
    have : d.t = x⁻¹ * (x * d.t) := by group
    rw [this]
    exact mul_mem (inv_mem (h.X₁_le_L hx)) (h.A₄_le_L hxA)

theorem card_Q₁ (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {d₀ : G} (hd₀ : d₀ ∈ d.D₄)
    (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) : Nat.card d.Q₁ = 2 ^ 11 := by
  have e := card_sup_mul_card_inf_of_normalizes h.X₁_le_normalizer_D
  rw [h.X₁_inf_D hB hV hd₀ hθ, Subgroup.card_bot, mul_one, h.card_X₁, h.card_D] at e
  rw [Data.Q₁, e]; norm_num

theorem conj_t_mem_A₄t {r : G} (hr : r ∈ normalizer ((d.withT d.A₄ : Subgroup G) : Set G)) :
    r * d.t * r⁻¹ ∈ (fun a => a * d.t) '' (d.A₄ : Set G) := by
  have h1 : r * d.t * r⁻¹ ∈ d.withT d.A₄ :=
    (mem_normalizer_iff.mp hr d.t).mp (t_mem_withT _)
  rw [h.mem_withT_iff h.A₄_le_L] at h1
  rcases h1 with h1 | h1
  · exfalso
    exact h.not_conj_mem_A₂ r⁻¹ (by simpa using h.A₄_le_A₂ h1)
  · exact ⟨_, h1, by simp only [mul_assoc, h.t_sq, mul_one]⟩

omit [Finite G] in
theorem card_A₄t : Nat.card ((fun a => a * d.t) '' (d.A₄ : Set G)) = 2 ^ 4 := by
  rw [Nat.card_image_of_injective (mul_left_injective d.t), Nat.card_coe_set_eq,
    ← h.card_A₄]
  rfl

theorem card_le_of_normalizer (R : Subgroup G)
    (hR : R ≤ normalizer ((d.withT d.A₄ : Subgroup G) : Set G)) :
    Nat.card R ≤ 2 ^ 4 * Nat.card (R ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
  have := card_le_card_mul_card_cent R d.t _ (fun r hr => h.conj_t_mem_A₄t (hR hr))
  rwa [h.card_A₄t] at this

section E₁

variable (hQ : HypQ d)
include hQ

omit [Finite G] in
theorem w₂₃₂_mem_L : d.w₂₃₂ ∈ d.L := h.K₁_le_L hQ.w₂₃₂_mem_K₁

omit [Finite G] in
theorem w₂₃₂_comm_t : d.w₂₃₂ * d.t = d.t * d.w₂₃₂ := h.comm_of_mem_L (h.w₂₃₂_mem_L hQ)

theorem w₂₃₂_mem_normalizer_D₁ : d.w₂₃₂ ∈ normalizer (d.D₁ : Set G) :=
  Hyp.XV_le_normalizer_D₁ (h.K₁_le_XV hQ.w₂₃₂_mem_K₁)

omit [Finite G] h hQ in
theorem mem_conjG {B : Subgroup G} {x : G} :
    x ∈ d.conjG B ↔ d.w₂₃₂⁻¹ * x * d.w₂₃₂ ∈ B := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro hx
    exact ⟨_, hx, by simp [mul_assoc]⟩

omit [Finite G] h hQ in
theorem card_conjG (B : Subgroup G) : Nat.card (d.conjG B) = Nat.card B :=
  Subgroup.card_map_of_injective (MulAut.conj d.w₂₃₂).injective

theorem t_mem_normalizer_conjG {B : Subgroup G} (htB : d.t ∈ normalizer (B : Set G)) :
    d.t ∈ normalizer (d.conjG B : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  rw [mem_conjG] at hx ⊢
  have hc : Commute d.w₂₃₂ d.t := h.w₂₃₂_comm_t hQ
  have e : d.w₂₃₂⁻¹ * (d.t * x * d.t⁻¹) * d.w₂₃₂ =
      d.t * (d.w₂₃₂⁻¹ * x * d.w₂₃₂) * d.t⁻¹ := by
    calc d.w₂₃₂⁻¹ * (d.t * x * d.t⁻¹) * d.w₂₃₂
        = (d.w₂₃₂⁻¹ * d.t) * x * (d.t⁻¹ * d.w₂₃₂) := by group
      _ = (d.t * d.w₂₃₂⁻¹) * x * (d.w₂₃₂ * d.t⁻¹) := by
          rw [hc.inv_left.eq, (hc.inv_right).eq]
      _ = d.t * (d.w₂₃₂⁻¹ * x * d.w₂₃₂) * d.t⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp htB _).mp hx

theorem conjG_V₂_inf_H {x : G} (hx : x ∈ d.conjG d.V₂) (hxH : x ∈ d.H) :
    x ∈ d.conjG d.Z₂S := by
  rw [mem_conjG] at hx ⊢
  rw [← h.V₂_inf_H]
  refine ⟨hx, ?_⟩
  have hgH : d.w₂₃₂ ∈ d.H := h.L_le_H (h.w₂₃₂_mem_L hQ)
  exact d.H.mul_mem (d.H.mul_mem (d.H.inv_mem hgH) hxH) hgH

theorem card_V₂_inf_conjG (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    Nat.card (d.V₂ ⊓ d.conjG d.V₂ : Subgroup G) ≤ 4 := by
  have h1 := card_le_sq_of_elem h.t_sq
    (mem_normalizer_inf h.t_mem_normalizer_V₂ (h.t_mem_normalizer_conjG hQ h.t_mem_normalizer_V₂))
    (fun x hx y hy => h.D₄_comm (h.V₂_le_D₄ hx.1) (h.V₂_le_D₄ hy.1))
    (fun x hx => h.D₄_sq hB hV (h.V₂_le_D₄ hx.1))
  have h2 : (d.V₂ ⊓ d.conjG d.V₂ ⊓ centralizer ({d.t} : Set G) : Subgroup G) ≤ zpowers d.z := by
    intro x ⟨⟨hx1, hx2⟩, hx3⟩
    refine hQ.Z₂S_inf ⟨?_, h.conjG_V₂_inf_H hQ hx2 hx3⟩
    rw [← h.V₂_inf_H]
    exact ⟨hx1, hx3⟩
  have h3 := Subgroup.card_le_of_le h2
  rw [h.card_zpowers_z] at h3
  calc Nat.card (d.V₂ ⊓ d.conjG d.V₂ : Subgroup G)
      ≤ Nat.card (d.V₂ ⊓ d.conjG d.V₂ ⊓ centralizer ({d.t} : Set G) : Subgroup G) ^ 2 := h1
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_left h3 2
    _ = 4 := by norm_num

omit hQ in
theorem V₂_le_cent_e : d.V₂ ≤ centralizer ({d.e} : Set G) :=
  h.V₂_le_D₄.trans (h.D₄_le_D.trans D_le_cent_e)

omit hQ in
theorem V₂_le_E₁ (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    d.V₂ ≤ d.D₁ ⊓ centralizer ({d.e} : Set G) :=
  le_inf (h.V₂_le_D₁ hB hV) h.V₂_le_cent_e

theorem conjG_V₂_le_E₁ (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    d.conjG d.V₂ ≤ d.D₁ ⊓ centralizer ({d.e} : Set G) := by
  rintro _ ⟨v, hv, rfl⟩
  have hvD := h.V₂_le_D₁ hB hV hv
  have hve := mem_centralizer_singleton_iff.mp (h.V₂_le_cent_e hv)
  have hge := hQ.w₂₃₂_comm_e
  refine ⟨(mem_normalizer_iff.mp (h.w₂₃₂_mem_normalizer_D₁ hQ) v).mp hvD,
    mem_centralizer_singleton_iff.mpr ?_⟩
  change d.w₂₃₂ * v * d.w₂₃₂⁻¹ * d.e = d.e * (d.w₂₃₂ * v * d.w₂₃₂⁻¹)
  have hge' : d.w₂₃₂⁻¹ * d.e = d.e * d.w₂₃₂⁻¹ := (Commute.inv_left hge).eq
  calc d.w₂₃₂ * v * d.w₂₃₂⁻¹ * d.e = d.w₂₃₂ * v * (d.w₂₃₂⁻¹ * d.e) := by group
    _ = d.w₂₃₂ * (v * d.e) * d.w₂₃₂⁻¹ := by rw [hge']; group
    _ = d.w₂₃₂ * (d.e * v) * d.w₂₃₂⁻¹ := by rw [hve]
    _ = (d.w₂₃₂ * d.e) * v * d.w₂₃₂⁻¹ := by group
    _ = d.e * (d.w₂₃₂ * v * d.w₂₃₂⁻¹) := by rw [hge]; group

omit hQ in
theorem D₁_le_normalizer_of (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {B : Subgroup G} (hVB : d.V₁ ≤ B) (hBD : B ≤ d.D₁) : d.D₁ ≤ normalizer (B : Set G) :=
  fun u hu => mem_normalizer_of_conj_mem fun b hb => by
    have e : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact mul_mem (hVB (h.D₁_comm_mod hB hC hV hu (hBD hb))) hb

theorem card_E₁ (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    2 ^ 10 ≤ Nat.card (d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) := by
  have hN : d.conjG d.V₂ ≤ normalizer (d.V₂ : Set G) := fun x hx =>
    h.D₁_le_normalizer_of hB hC hV d.V₁_le_V₂ (h.V₂_le_D₁ hB hV)
      (h.conjG_V₂_le_E₁ hQ hB hV hx).1
  have e := card_sup_mul_card_inf_of_normalizes hN
  rw [card_conjG, h.card_V₂, inf_comm] at e
  have hi := h.card_V₂_inf_conjG hQ hB hV
  have hsup : 2 ^ 10 ≤ Nat.card (d.conjG d.V₂ ⊔ d.V₂ : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card (d.conjG d.V₂ ⊔ d.V₂ : Subgroup G) *
        Nat.card (d.V₂ ⊓ d.conjG d.V₂ : Subgroup G) < 2 ^ 10 * 4 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hi (by norm_num)
    rw [e] at this
    norm_num at this
  exact hsup.trans (Subgroup.card_le_of_le
    (sup_le (h.conjG_V₂_le_E₁ hQ hB hV) (h.V₂_le_E₁ hB hV)))

end E₁

omit h in
theorem mem_normalizer_cent_of_comm {x e : G} (hx : x * e = e * x) :
    x ∈ normalizer (centralizer ({e} : Set G) : Set G) :=
  mem_normalizer_of_conj_mem fun n hn => by
    rw [mem_centralizer_singleton_iff] at hn ⊢
    have hx' : x⁻¹ * e = e * x⁻¹ := (Commute.inv_left hx).eq
    calc x * n * x⁻¹ * e = x * n * (x⁻¹ * e) := by group
      _ = x * (n * e) * x⁻¹ := by rw [hx']; group
      _ = x * (e * n) * x⁻¹ := by rw [hn]
      _ = (x * e) * n * x⁻¹ := by group
      _ = e * (x * n * x⁻¹) := by rw [hx]; group

theorem a₀_mem_normalizer_E₁ :
    d.a₀ ∈ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) := by
  have hz : d.a₀ ∈ centralizer ({d.z} : Set G) ⊓ d.H :=
    ⟨mem_centralizer_singleton_iff.mpr (h.A₄_comm h.a₀_mem h.z_mem_A₄),
      h.L_le_H (h.A₄_le_L h.a₀_mem)⟩
  exact mem_normalizer_inf (Hyp.XV_le_normalizer_D₁ (h.X_le_XV (CHz_le_X hz)))
    (mem_normalizer_cent_of_comm (mem_centralizer_iff.mp h.e_cent_A₄ _ h.a₀_mem))

theorem t_mem_normalizer_E₁ :
    d.t ∈ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) :=
  mem_normalizer_inf h.t_mem_normalizer_D₁ (mem_normalizer_cent_of_comm h.e_comm_t.symm)

theorem kap_single_zero {d₀ : G} (hd₀ : d₀ ∈ d.D₄) : h.kap hd₀ (Pi.single 0 1) = d.a₀ := by
  rw [h.kap_single]; simp [Data.basG, Data.xs]

section R₀

variable (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)

omit [Finite G] h in
theorem _root_.CFSG.EvenSmallLie.UnitarySix.YamadaD.Data.R₀_def :
    d.R₀ = ((d.D₁ ⊓ centralizer ({d.e} : Set G)) ⊔ zpowers d.a₀) ⊔ zpowers d.t := rfl

include hB hV

theorem mem_A₁_of_E₁ {x : G} (hx : x ∈ d.D₁ ⊓ centralizer ({d.e} : Set G)) (hxH : x ∈ d.H) :
    x ∈ d.A₁ := by
  rw [← h.D₁_inf_H hB hV]; exact ⟨hx.1, hxH⟩

omit [Finite G] hB hV in
theorem a₀_sq_mem_E₁ : d.a₀ * d.a₀ ∈ d.D₁ ⊓ centralizer ({d.e} : Set G) := by
  rw [h.A₄_sq h.a₀_mem]; exact one_mem _

theorem R₀_inf_H {x : G} (hx : x ∈ d.R₀) (hxH : x ∈ d.H) : x ∈ d.L ⊔ zpowers d.t := by
  have haN := h.a₀_mem_normalizer_E₁
  have haL : d.a₀ ∈ d.L := h.A₄_le_L h.a₀_mem
  have hE' : ∀ {y : G}, y ∈ (d.D₁ ⊓ centralizer ({d.e} : Set G)) ⊔ zpowers d.a₀ →
      y ∈ d.H → y ∈ d.L := fun {y} hy hyH => by
    rw [mem_sup_zpowers_of_normalizer haN (h.a₀_sq_mem_E₁)] at hy
    rcases hy with hy | hy
    · exact h.A₁_le_L (h.mem_A₁_of_E₁ hB hV hy hyH)
    · have h1 := h.mem_A₁_of_E₁ hB hV hy (mul_mem hyH (inv_mem (h.L_le_H haL)))
      have e : y = (y * d.a₀⁻¹) * d.a₀ := by group
      rw [e]; exact mul_mem (h.A₁_le_L h1) haL
  have hta : d.t * d.a₀ = d.a₀ * d.t := (h.comm_of_mem_L haL).symm
  have htN : d.t ∈ normalizer (((d.D₁ ⊓ centralizer ({d.e} : Set G)) ⊔ zpowers d.a₀ :
      Subgroup G) : Set G) :=
    mem_normalizer_sup h.t_mem_normalizer_E₁ (mem_normalizer_zpowers hta)
  rw [Data.R₀_def, mem_sup_zpowers_of_normalizer htN (by rw [h.t_sq]; exact one_mem _)] at hx
  rcases hx with hx | hx
  · exact mem_sup_left (hE' hx hxH)
  · have h1 := hE' hx (mul_mem hxH (inv_mem t_mem_H))
    have e : x = (x * d.t⁻¹) * d.t := by group
    rw [e]; exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers _))

omit [Finite G] hB hV in
theorem R₀_le_cent_e : d.R₀ ≤ centralizer ({d.e} : Set G) :=
  sup_le (sup_le inf_le_right (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp h.e_cent_A₄ _ h.a₀_mem))))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h.e_comm_t.symm))

theorem isPGroup_R₀ : IsPGroup 2 d.R₀ := by
  have hEp : IsPGroup 2 (d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) :=
    (h.isPGroup_U₁ hB hV).to_le (inf_le_left.trans (h.D₁_le_U₁ hB hV))
  have ha2 : IsPGroup 2 (zpowers d.a₀) :=
    (IsPGroup.of_card h.card_A₄).to_le (zpowers_le.mpr h.a₀_mem)
  have ht2 : IsPGroup 2 (zpowers d.t) :=
    (isPGroup_C₄.to_le D_le_C₄).to_le (zpowers_le.mpr h.t_mem_D)
  have hta : d.t * d.a₀ = d.a₀ * d.t := (h.comm_of_mem_L (h.A₄_le_L h.a₀_mem)).symm
  exact (hEp.to_sup_of_normal_left' ha2
    (zpowers_le.mpr h.a₀_mem_normalizer_E₁)).to_sup_of_normal_left' ht2
    (zpowers_le.mpr (mem_normalizer_sup h.t_mem_normalizer_E₁ (mem_normalizer_zpowers hta)))

theorem card_R₀ (hC : HypC d) (hQ : HypQ d) {d₀ : G} (hd₀ : d₀ ∈ d.D₄)
    (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) : 2 ^ 12 ≤ Nat.card d.R₀ := by
  set E := (d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) with hE
  have haN := h.a₀_mem_normalizer_E₁
  set E' := (E ⊔ zpowers d.a₀ : Subgroup G) with hE'
  have ha_not : d.a₀ ∉ E := by
    intro ha
    have h1 : d.a₀ ∈ d.Z₂S :=
      hB.A₁_inf_A₄ ⟨h.mem_A₁_of_E₁ hB hV ha (h.L_le_H (h.A₄_le_L h.a₀_mem)), h.a₀_mem⟩
    rw [← h.kap_single_zero hd₀, h.kap_mem_Z₂S_iff hd₀ hB hV hθ] at h1
    exact absurd h1.1 (by decide)
  have hEH : ∀ {y : G}, y ∈ E' → y ∈ d.H → y ∈ d.L := fun {y} hy hyH => by
    rw [hE', mem_sup_zpowers_of_normalizer haN h.a₀_sq_mem_E₁] at hy
    rcases hy with hy | hy
    · exact h.A₁_le_L (h.mem_A₁_of_E₁ hB hV hy hyH)
    · have h2 := h.mem_A₁_of_E₁ hB hV hy
        (mul_mem hyH (inv_mem (h.L_le_H (h.A₄_le_L h.a₀_mem))))
      have e : y = (y * d.a₀⁻¹) * d.a₀ := by group
      rw [e]; exact mul_mem (h.A₁_le_L h2) (h.A₄_le_L h.a₀_mem)
  have ht_not : d.t ∉ E' := fun ht => h.t_not_mem_L (hEH ht t_mem_H)
  have c1 := two_mul_card_le_card_sup ha_not
  have c2 := two_mul_card_le_card_sup ht_not
  have c3 := h.card_E₁ hQ hB hC hV
  rw [← hE] at c3
  calc 2 ^ 12 = 2 * (2 * 2 ^ 10) := by norm_num
    _ ≤ 2 * (2 * Nat.card E) := by gcongr
    _ ≤ 2 * Nat.card E' := by gcongr
    _ ≤ Nat.card d.R₀ := c2

end R₀

theorem not_sylow_Q₁ (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
    {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) :
    ∃ R : Subgroup G, R ≤ centralizer ({d.e} : Set G) ∧ IsPGroup 2 R ∧
      Nat.card d.Q₁ < Nat.card R := by
  refine ⟨d.R₀, h.R₀_le_cent_e, h.isPGroup_R₀ hB hV, ?_⟩
  rw [h.card_Q₁ hB hV hd₀ hθ]
  have := h.card_R₀ hB hV hC hQ hd₀ hθ
  omega

omit [Finite G] h in
theorem w₂₃₂_inv (hQ : HypQ d) : d.w₂₃₂⁻¹ = d.w₂₃₂ := inv_eq_of_mul_eq_one_right hQ.w₂₃₂_sq

theorem w₂₃₂_X₁ (hQ : HypQ d) {x : G} (hx : x ∈ d.X₁) : d.w₂₃₂ * x * d.w₂₃₂⁻¹ ∈ d.X₈ := by
  have hle : d.conjG d.X₈ ≤ d.X₁ := by
    rintro _ ⟨b, hb, rfl⟩; exact hQ.w₂₃₂_X₈ b hb
  have heq : d.conjG d.X₈ = d.X₁ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjG, h.card_X₈, h.card_X₁])
  rw [← heq, mem_conjG, w₂₃₂_inv hQ] at hx
  rw [w₂₃₂_inv hQ]
  exact hx

theorem fusion_Q₁ (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
    {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {y : G}
    (hy : y⁻¹ * d.t * y ∈ d.Q₁) : ∃ x ∈ d.X₁, ∃ c ∈ d.D₄, y⁻¹ * d.t * y = x * c * d.t := by
  obtain ⟨k, v, ε, he⟩ := h.exists_Q₁_coords hd₀ hB hV hθ hy
  cases ε
  · exfalso
    simp only [Bool.false_eq_true, ite_false, mul_one] at he
    have hs2 : (y⁻¹ * d.t * y) * (y⁻¹ * d.t * y) = 1 := by
      calc (y⁻¹ * d.t * y) * (y⁻¹ * d.t * y) = y⁻¹ * (d.t * d.t) * y := by group
        _ = 1 := by rw [h.t_sq]; group
    by_cases hk : k = 0
    · subst hk
      have hsD : y⁻¹ * d.t * y ∈ d.D₄ := by rw [he]; simpa [Data.xs] using h.kap_mem hd₀ v
      set P := d.D₂.map (MulAut.conj y).toMonoidHom with hP
      have hPH : P ≤ d.H := by
        rintro _ ⟨x, hx, rfl⟩
        have hc := h.D₂_comm hB hx (h.D₄_le_D₂ hsD)
        change y * x * y⁻¹ ∈ centralizer ({d.t} : Set G)
        rw [mem_centralizer_singleton_iff]
        calc y * x * y⁻¹ * d.t = y * (x * (y⁻¹ * d.t * y)) * y⁻¹ := by group
          _ = y * ((y⁻¹ * d.t * y) * x) * y⁻¹ := by rw [hc]
          _ = d.t * (y * x * y⁻¹) := by group
      have hP2 : IsPGroup 2 P := (h.C₂_pGroup.to_le inf_le_left).map _
      have hcard := h.card_le P hPH hP2
      rw [hP, Subgroup.card_map_of_injective (MulAut.conj y).injective, h.card_D₂ hB] at hcard
      norm_num at hcard
    · have hcomm : (mX k).mulVec v = v := by
        apply h.kap_injective hd₀ hB hV hθ
        rw [← h.conj_xs_kap hd₀ hB hV k]
        have hx2 : d.xs k * d.xs k = 1 := h.X₁_sq (h.xs_mem k)
        have hc2 := h.kap_mul_self hd₀ hB hV v
        rw [he] at hs2
        have hxi : (d.xs k)⁻¹ = d.xs k := inv_eq_of_mul_eq_one_right hx2
        calc d.xs k * h.kap hd₀ v * (d.xs k)⁻¹
            = (d.xs k * h.kap hd₀ v * (d.xs k * h.kap hd₀ v)) * (h.kap hd₀ v)⁻¹ := by
              rw [hxi]; group
          _ = h.kap hd₀ v := by rw [hs2, one_mul, h.kap_inv hd₀ hB hV]
      obtain ⟨w, rfl⟩ := fix_mX_eq_comm k hk v hcomm
      set a := h.kap hd₀ w with ha
      have hxa : y⁻¹ * d.t * y = a * d.xs k * a⁻¹ := by
        rw [he, h.kap_add hd₀ hB hV, ← h.conj_xs_kap hd₀ hB hV k, ← ha, h.kap_inv hd₀ hB hV, ← ha]
        have hx2 : d.xs k * d.xs k = 1 := h.X₁_sq (h.xs_mem k)
        have hxi : (d.xs k)⁻¹ = d.xs k := inv_eq_of_mul_eq_one_right hx2
        have hcomm' : a * (d.xs k * a * (d.xs k)⁻¹) = (d.xs k * a * (d.xs k)⁻¹) * a :=
          h.D₄_comm (h.kap_mem hd₀ w) (by rw [h.conj_xs_kap hd₀ hB hV]; exact h.kap_mem hd₀ _)
        calc d.xs k * (a * (d.xs k * a * (d.xs k)⁻¹))
            = d.xs k * ((d.xs k * a * (d.xs k)⁻¹) * a) := by rw [hcomm']
          _ = (d.xs k * d.xs k) * a * (d.xs k)⁻¹ * a := by group
          _ = a * d.xs k * a := by rw [hx2, one_mul, hxi]
      have hxconj : (y * a * d.w₂₃₂⁻¹)⁻¹ * d.t * (y * a * d.w₂₃₂⁻¹) =
          d.w₂₃₂ * d.xs k * d.w₂₃₂⁻¹ := by
        calc (y * a * d.w₂₃₂⁻¹)⁻¹ * d.t * (y * a * d.w₂₃₂⁻¹)
            = d.w₂₃₂ * (a⁻¹ * (y⁻¹ * d.t * y) * a) * d.w₂₃₂⁻¹ := by group
          _ = d.w₂₃₂ * d.xs k * d.w₂₃₂⁻¹ := by rw [hxa]; group
      apply h.not_conj_mem_A₂ (y * a * d.w₂₃₂⁻¹)
      rw [hxconj]
      exact h.A₄_le_A₂ (h.X₈_le_A₄ (h.w₂₃₂_X₁ hQ (h.xs_mem k)))
  · exact ⟨d.xs k, h.xs_mem k, h.kap hd₀ v, h.kap_mem hd₀ v, by simpa using he⟩

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
