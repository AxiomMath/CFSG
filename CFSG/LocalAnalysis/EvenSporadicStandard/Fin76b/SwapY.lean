module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Sylow3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_conj_inv_of_order_three_a5 (a : alternatingGroup (Fin 5)) (ha : orderOf a = 3) :
    ∃ g : alternatingGroup (Fin 5), g * a * g⁻¹ = a⁻¹ := by
  have key : ∀ a : alternatingGroup (Fin 5), a ^ 3 = 1 → a ≠ 1 →
      ∃ g : alternatingGroup (Fin 5), g * a * g⁻¹ = a⁻¹ := by
    set_option maxRecDepth 100000 in decide
  have h1 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have h2 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    omega
  exact key a h1 h2

theorem exists_mem_conj_inv_of_order_three {G : Type*} [Group G] {B : Subgroup G}
    (hB : Nonempty (↥B ≃* alternatingGroup (Fin 5))) {β : G} (hβB : β ∈ B)
    (hβ3 : orderOf β = 3) : ∃ b ∈ B, b * β * b⁻¹ = β⁻¹ := by
  obtain ⟨e⟩ := hB
  have h3 : orderOf (e ⟨β, hβB⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hβ3
  obtain ⟨g, hg⟩ := exists_conj_inv_of_order_three_a5 _ h3
  refine ⟨(e.symm g : G), (e.symm g).2, ?_⟩
  have := congrArg (fun a => ((e.symm a : B) : G)) hg
  simpa using this

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B : Subgroup G}

omit [Finite G] in
theorem W_le_normalizer (hW : WFacts L t E) :
    L ⊓ centralizer ({t} : Set G) ≤ normalizer (E : Set G) := by
  intro w hw
  have hwL : w ∈ L := hw.1
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 hw.2
  have hwt' : w⁻¹ * t = t * w⁻¹ := by
    calc w⁻¹ * t = w⁻¹ * (t * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * t) * w⁻¹ := by rw [hwt]
      _ = t * w⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact hW.normal w hwL hwt e he
  · intro he
    have := hW.normal w⁻¹ (L.inv_mem hwL) hwt' _ he
    simpa [mul_assoc] using this

theorem exists_swap_centralizing_beta (hconf : Rest6Config L z t T₀ E Q x β B) (hW : WFacts L t E) :
    ∃ y ∈ normalizer (E : Set G), y * β = β * y ∧ y * z * y⁻¹ = z * t ∧ y * t * y⁻¹ = t := by
  have hcfg := hconf.cfg
  have hxN : x ∈ normalizer (E : Set G) := hconf.norm x hconf.x_norm
  have hβB := hconf.beta_mem
  have hβL : β ∈ L := hconf.B_le hβB
  have hβt : β * t = t * β := mem_centralizer_singleton_iff.1 (hconf.B_cent hβB)
  have hβz : β * z = z * β := hcfg.z_comm_of_mem_A hβL
  have hβ3 := hconf.beta_order
  have hxz := hconf.x_z
  have hxt := hconf.x_t
  have ht2 := hcfg.t_sq
  have hxzt : x * (z * t) * x⁻¹ = z := by
    calc x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
      _ = (z * t) * t := by rw [hxz, hxt]
      _ = z * (t * t) := by group
      _ = z := by rw [ht2, mul_one]
  have hxz' : x⁻¹ * z * x = z * t := by
    calc x⁻¹ * z * x = x⁻¹ * (x * (z * t) * x⁻¹) * x := by rw [hxzt]
      _ = z * t := by group
  have hxt' : x⁻¹ * t * x = t := by
    calc x⁻¹ * t * x = x⁻¹ * (x * t * x⁻¹) * x := by rw [hxt]
      _ = t := by group
  have hβzt : β * (z * t) = (z * t) * β := by
    calc β * (z * t) = (β * z) * t := by group
      _ = (z * β) * t := by rw [hβz]
      _ = z * (β * t) := by group
      _ = z * (t * β) := by rw [hβt]
      _ = (z * t) * β := by group
  have hβ'z : x * β * x⁻¹ * z = z * (x * β * x⁻¹) := by
    calc x * β * x⁻¹ * z = x * (β * (x⁻¹ * z * x)) * x⁻¹ := by group
      _ = x * (β * (z * t)) * x⁻¹ := by rw [hxz']
      _ = x * ((z * t) * β) * x⁻¹ := by rw [hβzt]
      _ = (x * (z * t) * x⁻¹) * (x * β * x⁻¹) := by group
      _ = z * (x * β * x⁻¹) := by rw [hxzt]
  have hβ't : x * β * x⁻¹ * t = t * (x * β * x⁻¹) := by
    calc x * β * x⁻¹ * t = x * (β * (x⁻¹ * t * x)) * x⁻¹ := by group
      _ = x * (β * t) * x⁻¹ := by rw [hxt']
      _ = x * (t * β) * x⁻¹ := by rw [hβt]
      _ = (x * t * x⁻¹) * (x * β * x⁻¹) := by group
      _ = t * (x * β * x⁻¹) := by rw [hxt]
  have hβ'3 : orderOf (x * β * x⁻¹) = 3 := by
    have := MulEquiv.orderOf_eq (MulAut.conj x) β
    simpa [MulAut.conj_apply, hβ3] using this
  have hβ'L : x * β * x⁻¹ ∈ L := by
    have hv' : x * β * x⁻¹ ∈ L ⊔ zpowers z := by
      rw [← hcfg.cent_eq]
      exact mem_centralizer_singleton_iff.2 hβ'z
    obtain ⟨l, hl, c, hc, hvlc⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 hcfg.z_cent) hv'
    rcases mem_zpowers_sq_eq_one hcfg.z_sq hc with hc1 | hc1
    · rw [hvlc, hc1, mul_one]
      exact hl
    · exfalso
      rw [hc1] at hvlc
      have hlz : Commute l z := hcfg.z_comm_of_mem_A hl
      have h3 : (l * z) ^ 3 = 1 := by
        rw [← hvlc, ← hβ'3]
        exact pow_orderOf_eq_one _
      have hz3 : z ^ 3 = z := by
        calc z ^ 3 = z * z * z := by rw [pow_succ, pow_two]
          _ = z := by rw [hcfg.z_sq, one_mul]
      rw [hlz.mul_pow, hz3] at h3
      have hzL : z ∈ L := by
        rw [eq_inv_of_mul_eq_one_right h3]
        exact L.inv_mem (L.pow_mem hl 3)
      exact hcfg.z_not_mem_A hzL
  have hβ'W : x * β * x⁻¹ ∈ L ⊓ centralizer ({t} : Set G) :=
    ⟨hβ'L, mem_centralizer_singleton_iff.2 hβ't⟩
  have hβW : β ∈ L ⊓ centralizer ({t} : Set G) := ⟨hβL, hconf.B_cent hβB⟩
  have step : ∀ u ∈ L ⊓ centralizer ({t} : Set G), ∀ y : G, y ∈ normalizer (E : Set G) →
      y * z * y⁻¹ = z * t → y * t * y⁻¹ = t →
      u * y ∈ normalizer (E : Set G) ∧ u * y * z * (u * y)⁻¹ = z * t ∧
        u * y * t * (u * y)⁻¹ = t := by
    intro u hu y hyN hyz hyt
    have huz : u * z = z * u := hcfg.z_comm_of_mem_A hu.1
    have hut : u * t = t * u := mem_centralizer_singleton_iff.1 hu.2
    refine ⟨Subgroup.mul_mem _ (W_le_normalizer hW hu) hyN, ?_, ?_⟩
    · calc u * y * z * (u * y)⁻¹ = u * (y * z * y⁻¹) * u⁻¹ := by group
        _ = u * (z * t) * u⁻¹ := by rw [hyz]
        _ = (u * z * u⁻¹) * (u * t * u⁻¹) := by group
        _ = z * t := by
          rw [huz, hut]
          group
    · calc u * y * t * (u * y)⁻¹ = u * (y * t * y⁻¹) * u⁻¹ := by group
        _ = u * t * u⁻¹ := by rw [hyt]
        _ = t := by rw [hut]; group
  obtain ⟨w, hwW, hw⟩ := exists_conj_of_order_three (W := L ⊓ centralizer ({t} : Set G))
    hW.card_cent hβ'W hβW hβ'3 hβ3
  obtain ⟨hy₁N, hy₁z, hy₁t⟩ := step w hwW x hxN hxz hxt
  rcases hw with hw | hw
  · refine ⟨w * x, hy₁N, ?_, hy₁z, hy₁t⟩
    have : w * x * β * (w * x)⁻¹ = β := by
      calc w * x * β * (w * x)⁻¹ = w * (x * β * x⁻¹) * w⁻¹ := by group
        _ = β := hw
    exact mul_inv_eq_iff_eq_mul.1 this
  · obtain ⟨b₀, hb₀B, hb₀⟩ := exists_mem_conj_inv_of_order_three hconf.B_iso hβB hβ3
    have hb₀W : b₀ ∈ L ⊓ centralizer ({t} : Set G) := ⟨hconf.B_le hb₀B, hconf.B_cent hb₀B⟩
    obtain ⟨hy₂N, hy₂z, hy₂t⟩ := step b₀ hb₀W (w * x) hy₁N hy₁z hy₁t
    refine ⟨b₀ * (w * x), hy₂N, ?_, hy₂z, hy₂t⟩
    have : b₀ * (w * x) * β * (b₀ * (w * x))⁻¹ = β := by
      calc b₀ * (w * x) * β * (b₀ * (w * x))⁻¹
          = b₀ * (w * (x * β * x⁻¹) * w⁻¹) * b₀⁻¹ := by group
        _ = b₀ * β⁻¹ * b₀⁻¹ := by rw [hw]
        _ = (b₀ * β * b₀⁻¹)⁻¹ := by group
        _ = β := by rw [hb₀, inv_inv]
    exact mul_inv_eq_iff_eq_mul.1 this

end CFSG.EvenSporadicStandard.Fin76b
