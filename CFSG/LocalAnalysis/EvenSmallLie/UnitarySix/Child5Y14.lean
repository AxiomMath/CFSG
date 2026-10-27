module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y14E
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Set

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD YamadaN2

variable {G : Type} [Group G] [Finite G] {d : YamadaD.Data G}

theorem exists_D₂_surj_eq (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {a : G}
    (ha : a ∈ d.A₂) : ∃ x ∈ d.D₂, x * (d.t * x * d.t⁻¹) = a := by
  obtain ⟨c, hc, hca⟩ := h.C₂_conj a ha
  have ht' : d.t⁻¹ = d.t := h.t_inv
  rw [h.C₂_eq_D₂_t hB, mem_sup_zpowers_of_normalizer h.t_mem_normalizer_D₂
    (by rw [h.t_sq]; exact one_mem _)] at hc
  rcases hc with hc | hc
  · refine ⟨c, hc, ?_⟩
    have hcc : c⁻¹ = c := inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV hc)
    calc c * (d.t * c * d.t⁻¹) = c⁻¹ * d.t * c * d.t⁻¹ := by rw [hcc]; group
      _ = a * d.t * d.t⁻¹ := by rw [hca]
      _ = a := by group
  · set x := c * d.t⁻¹ with hx_def
    refine ⟨x, hc, ?_⟩
    have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV hc)
    have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h.A₂_sq a ha)
    have hcx : c = x * d.t := by rw [hx_def]; group
    have e1 : d.t⁻¹ * x⁻¹ * d.t * x = a := by
      have := hca
      rw [hcx] at this
      calc d.t⁻¹ * x⁻¹ * d.t * x = (x * d.t)⁻¹ * d.t * (x * d.t) * d.t⁻¹ := by group
        _ = a * d.t * d.t⁻¹ := by rw [this]
        _ = a := by group
    calc x * (d.t * x * d.t⁻¹) = x * (d.t * x * d.t) := by rw [ht']
      _ = x⁻¹ * d.t * x * d.t := by rw [hxx]; group
      _ = (d.t⁻¹ * x⁻¹ * d.t⁻¹ * x)⁻¹ := by group
      _ = (d.t⁻¹ * x⁻¹ * d.t * x)⁻¹ := by rw [ht']
      _ = a := by rw [e1, haa]

omit [Finite G] in
theorem theta_eq' (h : Hyp d) (x : G) : d.theta x = x⁻¹ * (d.t * x * d.t⁻¹) := by
  simp only [Data.theta]; rw [h.t_inv]; group

@[expose] def tD (d : YamadaD.Data G) (ht : d.t * d.t = 1)
    (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) : Subgroup G where
  carrier := {x | x ∈ d.D₁ ∧ d.theta x ∈ d.D₂}
  one_mem' := ⟨one_mem _, by simp only [Data.theta, inv_one, one_mul, mul_one, ht]; exact one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hx, hθx⟩ ⟨hy, hθy⟩
    refine ⟨mul_mem hx hy, ?_⟩
    rw [Hyp.theta_mul ht]
    have h1 : y⁻¹ * d.theta x * y⁻¹⁻¹ ∈ d.D₂ :=
      (mem_normalizer_iff.mp (hN (inv_mem hy)) _).mp hθx
    rw [inv_inv] at h1
    exact mul_mem h1 hθy
  inv_mem' := by
    rintro x ⟨hx, hθx⟩
    refine ⟨inv_mem hx, ?_⟩
    have h1 := Hyp.theta_mul ht x⁻¹ x
    rw [inv_mul_cancel] at h1
    have h0 : d.theta 1 = 1 := by simp only [Data.theta, inv_one, one_mul, mul_one, ht]
    rw [h0] at h1
    have e : d.theta x⁻¹ = x * (d.theta x)⁻¹ * x⁻¹ := by
      have h2 : x⁻¹ * d.theta x⁻¹ * x = (d.theta x)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      calc d.theta x⁻¹ = x * (x⁻¹ * d.theta x⁻¹ * x) * x⁻¹ := by group
        _ = x * (d.theta x)⁻¹ * x⁻¹ := by rw [h2]
    rw [e]
    exact (mem_normalizer_iff.mp (hN hx) _).mp (inv_mem hθx)

theorem exists_D₁_surj (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {a : G} (ha : a ∈ d.A₁) : ∃ x ∈ d.D₁, (x * (d.t * x * d.t⁻¹))⁻¹ * a ∈ d.D₂ := by
  obtain ⟨x, hx, hxa⟩ := exists_ι_range h hB hC hV ha
  refine ⟨x, hx, ?_⟩
  have hy : d.t * x * d.t⁻¹ ∈ d.D₁ := t_conj_mem_of_normalizer h.t_mem_normalizer_D₁ hx
  have hc := h.D₁_comm_mod hB hC hV (inv_mem hy) (inv_mem hx)
  have e : (x * (d.t * x * d.t⁻¹))⁻¹ * a =
      ((d.t * x * d.t⁻¹)⁻¹ * x⁻¹ * (d.t * x * d.t⁻¹)⁻¹⁻¹ * x⁻¹⁻¹) *
        ((d.t * x * d.t⁻¹ * x)⁻¹ * a) := by group
  rw [e]
  exact h.V₁_le_D₂ (mul_mem hc hxa)

theorem mem_D₂_of_kr₂ (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G}
    (hxc : ∀ y ∈ d.D₂, x * y * x⁻¹ = y) (hxt : x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₂) : x ∈ d.D₂ := by
  have ht' : d.t⁻¹ = d.t := h.t_inv
  have hcθ : x⁻¹ * (d.t * x * d.t⁻¹) = d.theta x := (theta_eq' h x).symm
  have hcc : (d.theta x)⁻¹ = d.theta x :=
    inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV (hcθ ▸ hxt))
  have hct : d.t * d.theta x * d.t = d.theta x := by rw [t_theta_t h, hcc]
  have hcA : d.theta x ∈ d.A₂ := by
    rw [← h.D₂_inf_H]
    refine mem_inf.mpr ⟨hcθ ▸ hxt, mem_centralizer_singleton_iff.mpr ?_⟩
    calc d.theta x * d.t = d.t⁻¹ * (d.t * d.theta x * d.t) := by group
      _ = d.t * d.theta x := by rw [hct, ht']
  obtain ⟨w, hw, hwc⟩ := exists_D₂_surj_eq h hB hV hcA
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV hw)
  have hθw : d.theta w = d.theta x := by
    rw [theta_eq' h, hww]
    exact hwc
  set x' := x * w⁻¹ with hx'_def
  have hx't : d.t * x' = x' * d.t := by
    have e1 : x⁻¹ * d.t * x * d.t = w⁻¹ * d.t * w * d.t := hθw.symm
    calc d.t * x' = x * (x⁻¹ * d.t * x * d.t) * d.t⁻¹ * w⁻¹ := by rw [hx'_def]; group
      _ = x * (w⁻¹ * d.t * w * d.t) * d.t⁻¹ * w⁻¹ := by rw [e1]
      _ = x' * d.t := by rw [hx'_def]; group
  have hx'c : ∀ y ∈ d.D₂, x' * y * x'⁻¹ = y := fun y hy => by
    have hwy : w⁻¹ * y * w⁻¹⁻¹ = y := by
      rw [inv_inv, h.D₂_comm hB (inv_mem hw) hy, inv_mul_cancel_right]
    calc x' * y * x'⁻¹ = x * (w⁻¹ * y * w⁻¹⁻¹) * x⁻¹ := by rw [hx'_def]; group
      _ = y := by rw [hwy, hxc y hy]
  have hx'H : x' ∈ d.H := mem_centralizer_singleton_iff.mpr hx't.symm
  have hx'CA : x' ∈ centralizer (d.A₂ : Set G) := mem_centralizer_iff.mpr fun a ha => by
    have h1 := hx'c a (h.A₂_le_D₂ ha)
    calc a * x' = x' * a * x'⁻¹ * x' := by rw [h1]
      _ = x' * a := by group
  have hx'N : x' ∈ normalizer (d.withT d.A₂ : Set G) := by
    refine YamadaD.mem_normalizer_sup (YamadaPar.mem_normalizer_of_conj_eq fun a ha => ?_)
      (YamadaPar.mem_normalizer_of_conj_eq fun y hy => ?_)
    · rw [← mem_centralizer_iff.mp hx'CA a ha, mul_inv_cancel_right]
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [(Commute.zpow_right (show Commute x' d.t from hx't.symm) k).eq, mul_inv_cancel_right]
  have hmem : x' ∈ d.withT d.A₂ := by
    rw [← h.C₂_inf_H]
    exact mem_inf.mpr ⟨h.C₂_max (mem_inf.mpr ⟨hx'N, hx'CA⟩), hx'H⟩
  rcases (h.mem_withT_iff h.A₂_le_L).mp hmem with hA | hAt
  · have e : x = x' * w := by rw [hx'_def]; group
    rw [e]
    exact mul_mem (h.A₂_le_D₂ hA) hw
  · exfalso
    have htc : ∀ y ∈ d.D₂, y * d.t = d.t * y := fun y hy => by
      have h1 : (x' * d.t) * y * (x' * d.t)⁻¹ = y := by
        rw [h.D₂_comm hB (h.A₂_le_D₂ hAt) hy, mul_inv_cancel_right]
      have h2 : x'⁻¹ * y * x' = y := by
        have := hx'c y hy
        calc x'⁻¹ * y * x' = x'⁻¹ * (x' * y * x'⁻¹) * x' := by rw [this]
          _ = y := by group
      have h3 : d.t * y * d.t⁻¹ = y := by
        calc d.t * y * d.t⁻¹ = x'⁻¹ * ((x' * d.t) * y * (x' * d.t)⁻¹) * x' := by group
          _ = y := by rw [h1, h2]
      calc y * d.t = d.t * y * d.t⁻¹ * d.t := by rw [h3]
        _ = d.t * y := by group
    have hle : d.D₂ ≤ d.A₂ := fun y hy => by
      rw [← h.D₂_inf_H]
      exact mem_inf.mpr ⟨hy, mem_centralizer_singleton_iff.mpr (htc y hy)⟩
    have := Subgroup.card_le_of_le hle
    rw [h.card_D₂ hB, h.card_A₂] at this
    norm_num at this

section Count

variable {θ : d.K₁ ≃* SU42b} {ιG₁ : (Fin 8 → ZMod 2) → G}

theorem card_tD_le (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG₁) (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) :
    Nat.card (tD d h.t_sq hN) ≤ 2 ^ 14 := by
  have := h.V₁_normal_AV
  set T := tD d h.t_sq hN
  have hs := elemSec h hB hC hV
  have hK : d.K₁ ≤ normalizer (d.D₁ : Set G) := h.K₁_le_XV.trans Hyp.XV_le_normalizer_D₁
  have hTU : ∀ x ∈ T, x ∈ d.U₁ := fun x hx => h.D₁_le_U₁ hB hV hx.1
  let φ : T →* (d.AV ⧸ d.V₁.subgroupOf d.AV) :=
    { toFun := fun x => d.cls (d.theta x)
      map_one' := cls_theta_one h
      map_mul' := fun x y => h.cls_theta_mul (hTU x x.2) (hTU y y.2) }
  have hker : Nat.card φ.ker ≤ 2 ^ 10 := by
    rw [← h.card_AV hV]
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : T) : G), ?_⟩) ?_
    · have h1 : d.cls (d.theta ((x : T) : G)) = 1 := x.2
      have hxD := ((x : T)).2.1
      rw [Hyp.cls_eq_one_iff (h.crossed_D₁ hB hV hxD)] at h1
      exact (h.theta_mem_V₁_iff hB hV hxD).mp h1
    · intro x y hxy
      have h1 : ((x : T) : G) = ((y : T) : G) := by
        have := congrArg (fun w : d.AV => (w : G)) hxy
        simpa using this
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card φ.range ≤ 16 := by
    have hsub : (φ.range : Set (d.AV ⧸ d.V₁.subgroupOf d.AV)) ⊆ (fun u => d.cls (ιG₁ u)) ''
        {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u} := by
      rintro _ ⟨x, rfl⟩
      have hx := (x : T).2
      have hθ := h.crossed_D₁ hB hV hx.1
      have hθC : d.theta x ∈ centE θ hs hK := by
        rw [centE_eq h hB hC hV hc]
        exact mem_inf.mpr ⟨theta_mem_D₁ h hx.1, hx.2⟩
      obtain ⟨u, hu, hux⟩ := exists_fix_of_cent h hC hV hc hθ
        (fun m hm => cls_conj_e_eq h hθ (hθC.2 m hm))
      exact ⟨u, hu, hux⟩
    calc Nat.card φ.range = (φ.range : Set (d.AV ⧸ d.V₁.subgroupOf d.AV)).ncard :=
          (Nat.card_coe_set_eq _)
      _ ≤ ((fun u => d.cls (ιG₁ u)) ''
          {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}.ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ ≤ 16 := ncard_fix_le
  calc Nat.card T = Nat.card φ.ker * Nat.card φ.range := card_eq_card_ker_mul_card_range φ
    _ ≤ 2 ^ 10 * 16 := Nat.mul_le_mul hker hrange
    _ = 2 ^ 14 := by norm_num

end Count

section E2

variable {θ : d.K₁ ≃* SU42b} {ιG₁ : (Fin 8 → ZMod 2) → G} {θ₂ : SL3 →* G}
  {ιG₂ : (Fin 9 → ZMod 2) → G}

omit [Finite G]
  in
theorem eProdG_mem_A₁ (hc₂ : Y14Coords d θ₂ ιG₂) (μ : ℕ) : eProdG θ₂ μ ∈ d.A₁ :=
  Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    exact hc₂.E_mem n (bitList_lt hn)

omit [Finite G]
  in
theorem eProdG_mem_K₂ (hc₂ : Y14Coords d θ₂ ιG₂) (μ : ℕ) : eProdG θ₂ μ ∈ d.K₂ := by
  rw [eProdG_eq, ← hc₂.K₂_eq]
  exact ⟨_, rfl⟩

theorem A₁_le_tD (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) : d.A₁ ≤ tD d h.t_sq hN := fun a ha => by
  refine ⟨h.A₁_le_D₁ hB hV ha, ?_⟩
  have hat : d.t * a = a * d.t := t_comm_of_mem_L h (h.A₁_le_L ha)
  have e : d.theta a = 1 := by
    simp only [Data.theta]
    rw [mul_assoc a⁻¹, hat, ← mul_assoc, inv_mul_cancel, one_mul, h.t_sq]
  rw [e]
  exact one_mem _

theorem inf_le_tD (h : Hyp d) (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) :
    d.D₁ ⊓ d.D₂ ≤ tD d h.t_sq hN := fun y hy => by
  refine ⟨(mem_inf.mp hy).1, ?_⟩
  rw [theta_eq' h]
  exact mul_mem (inv_mem (mem_inf.mp hy).2)
    (t_conj_mem_of_normalizer h.t_mem_normalizer_D₂ (mem_inf.mp hy).2)

theorem exists_eProdG_mul (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG₁) (hc₂ : Y14Coords d θ₂ ιG₂) (hK2A : d.K₂ ⊓ d.A₂ = ⊥)
    (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) {x : G} (hx : x ∈ tD d h.t_sq hN) :
    ∃ μ < 16, ∃ y ∈ d.D₁ ⊓ d.D₂, x = eProdG θ₂ μ * y := by
  set T := tD d h.t_sq hN
  let f : Fin 16 × (d.D₁ ⊓ d.D₂ : Subgroup G) → T := fun p =>
    ⟨eProdG θ₂ p.1 * p.2, mul_mem (A₁_le_tD h hB hV hN (eProdG_mem_A₁ hc₂ _))
      (inf_le_tD h hN p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨μ, y⟩ ⟨μ', y'⟩ hf
    have h1 : eProdG θ₂ μ * (y : G) = eProdG θ₂ μ' * y' := congrArg Subtype.val hf
    have h2 : (eProdG θ₂ μ')⁻¹ * eProdG θ₂ μ = (y' : G) * (y : G)⁻¹ :=
      calc (eProdG θ₂ μ')⁻¹ * eProdG θ₂ μ = (eProdG θ₂ μ')⁻¹ * (eProdG θ₂ μ * y) * (y : G)⁻¹ := by
            group
        _ = (eProdG θ₂ μ')⁻¹ * (eProdG θ₂ μ' * y') * (y : G)⁻¹ := by rw [h1]
        _ = (y' : G) * (y : G)⁻¹ := by group
    have hK : (eProdG θ₂ μ')⁻¹ * eProdG θ₂ μ ∈ d.K₂ :=
      mul_mem (inv_mem (eProdG_mem_K₂ hc₂ _)) (eProdG_mem_K₂ hc₂ _)
    have hD : (eProdG θ₂ μ')⁻¹ * eProdG θ₂ μ ∈ d.D₂ := by
      rw [h2]
      exact mul_mem (mem_inf.mp y'.2).2 (inv_mem (mem_inf.mp y.2).2)
    have hA : (eProdG θ₂ μ')⁻¹ * eProdG θ₂ μ ∈ d.A₂ := by
      rw [← h.D₂_inf_H]
      exact mem_inf.mpr ⟨hD, h.L_le_H (hB.K₂_le_L hK)⟩
    have hbot : (eProdG θ₂ μ')⁻¹ * eProdG θ₂ μ ∈ d.K₂ ⊓ d.A₂ := mem_inf.mpr ⟨hK, hA⟩
    rw [hK2A, mem_bot, inv_mul_eq_one] at hbot
    have hμ : (μ : ℕ) = μ' := eProdG_inj hc₂ μ.2 μ'.2 hbot.symm
    have hy : (y : G) = y' := by
      rw [← hbot] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Fin.ext hμ) (Subtype.ext hy)
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 16), Fintype.card_fin,
      h.card_D₁_inf_D₂ hB hV]
    exact (card_tD_le h hB hC hV hc hN).trans (by norm_num))
  obtain ⟨⟨μ, y⟩, hp⟩ := hbij.2 ⟨x, hx⟩
  exact ⟨μ, μ.2, y, y.2, (congrArg Subtype.val hp).symm⟩

theorem exists_D₁_fix (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG₁) (hc₂ : Y14Coords d θ₂ ιG₂) (hK2A : d.K₂ ⊓ d.A₂ = ⊥)
    (hN : d.D₁ ≤ normalizer (d.D₂ : Set G)) {x : G} (hx : x ∈ d.D₁)
    (hxt : x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₂) : ∃ μ < 16, x⁻¹ * eProdG θ₂ μ ∈ d.D₂ := by
  have hT : x ∈ tD d h.t_sq hN := ⟨hx, by rw [theta_eq' h]; exact hxt⟩
  obtain ⟨μ, hμ, y, hy, rfl⟩ := exists_eProdG_mul h hB hC hV hc hc₂ hK2A hN hT
  refine ⟨μ, hμ, ?_⟩
  rw [show (eProdG θ₂ μ * y)⁻¹ * eProdG θ₂ μ = y⁻¹ by group]
  exact inv_mem (mem_inf.mp hy).2

end E2

section Main

variable {θ : d.K₁ ≃* SU42b} {ιG₁ : (Fin 8 → ZMod 2) → G} {θ₂ : SL3 →* G}
  {ιG₂ : (Fin 9 → ZMod 2) → G}

theorem y14Hyp_of (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG₁) (hc₂ : Y14Coords d θ₂ ιG₂) (hK2A : d.K₂ ⊓ d.A₂ = ⊥)
    (hN : d.D₂ ≤ normalizer (d.D₁ : Set G) ∧ d.D₁ ≤ normalizer (d.D₂ : Set G)) :
    YamadaN2.Y14Hyp d.t d.D₁ d.V₁ d.D₂ d.A₂ d.K₂ θ₂ ιG₂ where
  t_sq := h.t_sq
  D₂_comm := fun x hx y hy => h.D₂_comm hB hx hy
  D₂_sq := fun x hx => h.D₂_sq hB hV hx
  card_D₂ := h.card_D₂ hB
  A₂_le := h.A₂_le_D₂
  A₂_t := fun a ha => t_comm_of_mem_L h (h.A₂_le_L ha)
  D₂_H := fun x hx hxt => by
    rw [← h.D₂_inf_H]
    exact mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr hxt.symm⟩
  t_D₂ := h.t_mem_normalizer_D₂
  K₂_eq := hc₂.K₂_eq
  K₂_t := fun k hk => t_comm_of_mem_L h (hB.K₂_le_L hk)
  K₂_norm := h.K₂_le_normalizer_D₂ hB
  ι_mem := hc₂.ι_mem
  ι_add := hc₂.ι_add
  ι_inj := hc₂.ι_inj
  K₂_ι := hc₂.K₂_ι
  ι_range := fun u => exists_D₂_surj_eq h hB hV (hc₂.ι_mem u)
  D₁_norm := hN.2
  D₂_norm := hN.1
  t_D₁ := h.t_mem_normalizer_D₁
  V₁_le₁ := h.V₁_le_D₁ hB hV
  V₁_le₂ := h.V₁_le_D₂
  card_V₁ := h.card_V₁.le
  V₁_central := (elemSec h hB hC hV).central
  D₁_comm_mod := fun x hx y hy => h.D₁_comm_mod hB hC hV hx hy
  D₁_sq_mod := fun x hx => h.D₁_sq_mod hB hC hV hx
  card_D₁D₂ := (h.card_D₁_inf_D₂ hB hV).le
  E_mem := fun m hm => h.A₁_le_D₁ hB hV (hc₂.E_mem m hm)
  ν_norm := fun j hj => (h.K₁_le_XV.trans Hyp.XV_le_normalizer_D₁) (hc₂.ν_mem j hj)
  D₁_fix := fun x hx hxt => exists_D₁_fix h hB hC hV hc hc₂ hK2A hN.2 hx hxt
  D₁_surj := fun m hm => exists_D₁_surj h hB hC hV (hc₂.E_mem m hm)
  Kr := fun x _ hxc hxt => mem_D₂_of_kr₂ h hB hV hxc hxt

end Main

end CFSG.EvenSmallLie.UnitarySix.Child5
