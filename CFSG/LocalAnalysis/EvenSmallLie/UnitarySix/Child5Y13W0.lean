module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13Cls
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13E

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD

variable {G : Type} [Group G] {d : YamadaD.Data G}
variable {θ : d.K₁ ≃* SU42b} {ιG : (Fin 8 → ZMod 2) → G}

@[expose] def centE (θ : d.K₁ ≃* SU42b) (hs : YamadaPar.ElemSec d.D₁ d.V₁)
    (hK : d.K₁ ≤ normalizer (d.D₁ : Set G)) : Subgroup G where
  carrier := {x | x ∈ d.D₁ ∧ ∀ m < 4, (((θ.symm (eSU m) : d.K₁) : G) * x *
    ((θ.symm (eSU m) : d.K₁) : G)⁻¹)⁻¹ * x ∈ d.V₁}
  one_mem' := ⟨one_mem _, fun m _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxe⟩ ⟨hy, hye⟩
    refine ⟨mul_mem hx hy, fun m hm => ?_⟩
    set e : G := ((θ.symm (eSU m) : d.K₁) : G)
    have heD := hK (θ.symm (eSU m)).2
    have hey : e * y * e⁻¹ ∈ d.D₁ := (mem_normalizer_iff.mp heD y).mp hy
    have hc := hs.central _ (hxe m hm) _ (inv_mem hey)
    have e1 : (e * (x * y) * e⁻¹)⁻¹ * (x * y) =
        ((e * x * e⁻¹)⁻¹ * x) * ((e * y * e⁻¹)⁻¹ * y) :=
      calc (e * (x * y) * e⁻¹)⁻¹ * (x * y)
          = (e * y * e⁻¹)⁻¹ * ((e * x * e⁻¹)⁻¹ * x) * y := by group
        _ = ((e * x * e⁻¹)⁻¹ * x) * (e * y * e⁻¹)⁻¹ * y := by rw [hc]
        _ = ((e * x * e⁻¹)⁻¹ * x) * ((e * y * e⁻¹)⁻¹ * y) := by group
    rw [e1]
    exact mul_mem (hxe m hm) (hye m hm)
  inv_mem' := by
    rintro x ⟨hx, hxe⟩
    refine ⟨inv_mem hx, fun m hm => ?_⟩
    set e : G := ((θ.symm (eSU m) : d.K₁) : G)
    have hc := hs.central _ (inv_mem (hxe m hm)) x hx
    have e1 : (e * x⁻¹ * e⁻¹)⁻¹ * x⁻¹ = x * ((e * x * e⁻¹)⁻¹ * x)⁻¹ * x⁻¹ := by group
    rw [e1, ← hc, mul_inv_cancel_right]
    exact inv_mem (hxe m hm)

section Count

variable [Finite G]

theorem cls_conj_e_eq (h : Hyp d) [(d.V₁.subgroupOf d.AV).Normal] {m : ℕ} {a : G}
    (ha : a ∈ d.AV) (hae : (((θ.symm (eSU m) : d.K₁) : G) * a *
      ((θ.symm (eSU m) : d.K₁) : G)⁻¹)⁻¹ * a ∈ d.V₁) :
    d.cls (((θ.symm (eSU m) : d.K₁) : G) * a * ((θ.symm (eSU m) : d.K₁) : G)⁻¹) = d.cls a := by
  have hX : ((θ.symm (eSU m) : d.K₁) : G) ∈ d.XV := h.K₁_le_XV (θ.symm (eSU m)).2
  have hg := (mem_normalizer_iff.mp (h.XV_le_normalizer_AV hX) a).mp ha
  exact (Hyp.cls_eq_iff hg ha).mpr hae

theorem card_centE_inf_AV_le (h : Hyp d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) (hs : YamadaPar.ElemSec d.D₁ d.V₁)
    (hK : d.K₁ ≤ normalizer (d.D₁ : Set G)) [(d.V₁.subgroupOf d.AV).Normal] :
    Nat.card (centE θ hs hK ⊓ d.AV : Subgroup G) ≤ 2 ^ 6 := by
  set C := centE θ hs hK ⊓ d.AV
  let ψ : C →* (d.AV ⧸ d.V₁.subgroupOf d.AV) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion (inf_le_right : C ≤ d.AV))
  have hψ : ∀ a : C, ψ a = d.cls (a : G) := fun a => (Hyp.cls_of_mem (mem_inf.mp a.2).2).symm
  have hker : Nat.card ψ.ker ≤ 4 := by
    rw [← h.card_V₁]
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : C) : G), ?_⟩) ?_
    · have h1 : ψ x = 1 := x.2
      rw [hψ] at h1
      exact (Hyp.cls_eq_one_iff (mem_inf.mp (x : C).2).2).mp h1
    · intro x y hxy
      have h1 : ((x : C) : G) = ((y : C) : G) := by
        have := congrArg (fun w : d.V₁ => (w : G)) hxy
        simpa using this
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card ψ.range ≤ 16 := by
    have hsub : (ψ.range : Set (d.AV ⧸ d.V₁.subgroupOf d.AV)) ⊆ (fun u => d.cls (ιG u)) ''
        {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u} := by
      rintro _ ⟨a, rfl⟩
      have haC := mem_inf.mp a.2
      obtain ⟨u, hu, hua⟩ := exists_fix_of_cent h hC hV hc haC.2
        (fun m hm => cls_conj_e_eq h haC.2 (haC.1.2 m hm))
      exact ⟨u, hu, by rw [hψ]; exact hua⟩
    calc Nat.card ψ.range = (ψ.range : Set (d.AV ⧸ d.V₁.subgroupOf d.AV)).ncard :=
          (Nat.card_coe_set_eq _)
      _ ≤ ((fun u => d.cls (ιG u)) ''
          {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}.ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ ≤ 16 := ncard_fix_le
  calc Nat.card C = Nat.card ψ.ker * Nat.card ψ.range := card_eq_card_ker_mul_card_range ψ
    _ ≤ 4 * 16 := Nat.mul_le_mul hker hrange
    _ = 2 ^ 6 := by norm_num

omit [Finite G]
  in
theorem theta_conj (h : Hyp d) {e x : G} (he : e ∈ d.L) :
    e * d.theta x * e⁻¹ = d.theta (e * x * e⁻¹) := by
  have het : e * d.t = d.t * e := h.comm_of_mem_L he
  have het' : e⁻¹ * d.t = d.t * e⁻¹ := by
    calc e⁻¹ * d.t = e⁻¹ * (d.t * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * d.t) * e⁻¹ := by rw [het]
      _ = d.t * e⁻¹ := by group
  simp only [Data.theta]
  calc e * (x⁻¹ * d.t * x * d.t) * e⁻¹ = e * x⁻¹ * d.t * x * (d.t * e⁻¹) := by group
    _ = e * x⁻¹ * d.t * x * (e⁻¹ * d.t) := by rw [het']
    _ = e * x⁻¹ * (d.t * x) * e⁻¹ * d.t := by group
    _ = e * x⁻¹ * (e⁻¹ * e) * (d.t * x) * e⁻¹ * d.t := by group
    _ = e * x⁻¹ * e⁻¹ * (e * d.t) * x * e⁻¹ * d.t := by group
    _ = e * x⁻¹ * e⁻¹ * (d.t * e) * x * e⁻¹ * d.t := by rw [het]
    _ = (e * x * e⁻¹)⁻¹ * d.t * (e * x * e⁻¹) * d.t := by group

omit [Finite G]
  in
theorem cls_theta_one (h : Hyp d) [(d.V₁.subgroupOf d.AV).Normal] : d.cls (d.theta 1) = 1 := by
  have : d.theta 1 = 1 := by simp [Data.theta, h.t_sq]
  rw [this, Hyp.cls_one]

theorem cls_theta_V₁ (h : Hyp d) [(d.V₁.subgroupOf d.AV).Normal] {v : G} (hv : v ∈ d.V₁) :
    d.cls (d.theta v) = 1 :=
  (Hyp.cls_eq_one_iff (mem_sup_right (zpowers_z_le_V₁ h (h.crossed_V₁ hv)))).mpr
    (zpowers_z_le_V₁ h (h.crossed_V₁ hv))

theorem card_centE_le (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) (hs : YamadaPar.ElemSec d.D₁ d.V₁)
    (hK : d.K₁ ≤ normalizer (d.D₁ : Set G)) [(d.V₁.subgroupOf d.AV).Normal] :
    Nat.card (centE θ hs hK) ≤ 2 ^ 10 := by
  set C := centE θ hs hK
  have hCU : ∀ x ∈ C, x ∈ d.U₁ := fun x hx => h.D₁_le_U₁ hB hV hx.1
  let φ : C →* (d.AV ⧸ d.V₁.subgroupOf d.AV) :=
    { toFun := fun x => d.cls (d.theta x)
      map_one' := cls_theta_one h
      map_mul' := fun x y => h.cls_theta_mul (hCU x x.2) (hCU y y.2) }
  have hker : Nat.card φ.ker ≤ 2 ^ 6 := by
    refine le_trans ?_ (card_centE_inf_AV_le h hC hV hc hs hK)
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : C) : G), ?_⟩) ?_
    · have h1 : d.cls (d.theta ((x : C) : G)) = 1 := x.2
      have hxD := ((x : C)).2.1
      rw [Hyp.cls_eq_one_iff (h.crossed_D₁ hB hV hxD)] at h1
      exact mem_inf.mpr ⟨(x : C).2, (h.theta_mem_V₁_iff hB hV hxD).mp h1⟩
    · intro x y hxy
      have h1 : ((x : C) : G) = ((y : C) : G) := by
        have := congrArg (fun w : (centE θ hs hK ⊓ d.AV : Subgroup G) => (w : G)) hxy
        simpa using this
      exact Subtype.ext (Subtype.ext h1)
  have hrange : Nat.card φ.range ≤ 16 := by
    have hsub : (φ.range : Set (d.AV ⧸ d.V₁.subgroupOf d.AV)) ⊆ (fun u => d.cls (ιG u)) ''
        {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u} := by
      rintro _ ⟨x, rfl⟩
      have hx := (x : C).2
      have hθ := h.crossed_D₁ hB hV hx.1
      obtain ⟨u, hu, hux⟩ := exists_fix_of_cent h hC hV hc hθ (fun m hm => by
        set e : G := ((θ.symm (eSU m) : d.K₁) : G)
        have heL : e ∈ d.L := h.K₁_le_L (θ.symm (eSU m)).2
        rw [theta_conj h heL]
        set v : G := (x : G)⁻¹ * (e * (x : G) * e⁻¹)
        have hv : v ∈ d.V₁ := by
          have := inv_mem (hx.2 m hm)
          rwa [_root_.mul_inv_rev, inv_inv] at this
        have e1 : e * (x : G) * e⁻¹ = x * v := by simp only [v]; group
        rw [e1, h.cls_theta_mul (hCU x x.2) (h.D₁_le_U₁ hB hV (h.V₁_le_D₁ hB hV hv)),
          cls_theta_V₁ h hv, mul_one])
      exact ⟨u, hu, hux⟩
    calc Nat.card φ.range = (φ.range : Set (d.AV ⧸ d.V₁.subgroupOf d.AV)).ncard :=
          (Nat.card_coe_set_eq _)
      _ ≤ ((fun u => d.cls (ιG u)) ''
          {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ {u : Fin 8 → ZMod 2 | ∀ m < 4, toMat 8 8 (eBits m) *ᵥ u = u}.ncard :=
          Set.ncard_image_le (Set.toFinite _)
      _ ≤ 16 := ncard_fix_le
  calc Nat.card C = Nat.card φ.ker * Nat.card φ.range := card_eq_card_ker_mul_card_range φ
    _ ≤ 2 ^ 6 * 16 := Nat.mul_le_mul hker hrange
    _ = 2 ^ 10 := by norm_num

theorem centE_eq (h : Hyp d) (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hc : Y13Coords d θ ιG) (hs : YamadaPar.ElemSec d.D₁ d.V₁)
    (hK : d.K₁ ≤ normalizer (d.D₁ : Set G)) : centE θ hs hK = d.D₁ ⊓ d.D₂ := by
  have := h.V₁_normal_AV
  symm
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ⟨(mem_inf.mp hx).1, fun m hm => ?_⟩) ?_
  · have he : ((θ.symm (eSU m) : d.K₁) : G) ∈ d.D₂ := h.A₂_le_D₂ (hc.E_mem m hm)
    rw [h.D₂_comm hB he (mem_inf.mp hx).2, mul_inv_cancel_right, inv_mul_cancel]
    exact one_mem _
  · rw [h.card_D₁_inf_D₂ hB hV]
    exact card_centE_le h hB hC hV hc hs hK

end Count

end CFSG.EvenSmallLie.UnitarySix.Child5
