module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDInter
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSettingC

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

@[expose] noncomputable def cls [(d.V₁.subgroupOf d.AV).Normal] (g : G) :
    d.AV ⧸ d.V₁.subgroupOf d.AV :=
  open Classical in if hg : g ∈ d.AV then QuotientGroup.mk ⟨g, hg⟩ else 1

end Data

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem AV_le_C₀ [Finite G] : d.AV ≤ d.C₀ := by
  rw [← h.C₀_inf_cent_V₁]; exact inf_le_left

theorem AV_le_U₁ [Finite G] : d.AV ≤ d.U₁ := h.AV_le_C₀.trans h.C₀_le_U₁

omit h in
theorem cls_of_mem [(d.V₁.subgroupOf d.AV).Normal] {g : G} (hg : g ∈ d.AV) :
    d.cls g = QuotientGroup.mk ⟨g, hg⟩ := by
  simp [Data.cls, hg]

omit h in
theorem cls_mul [(d.V₁.subgroupOf d.AV).Normal] {g g' : G} (hg : g ∈ d.AV) (hg' : g' ∈ d.AV) :
    d.cls (g * g') = d.cls g * d.cls g' := by
  rw [cls_of_mem hg, cls_of_mem hg', cls_of_mem (mul_mem hg hg'), ← QuotientGroup.mk_mul]
  rfl

omit h in
theorem cls_one [(d.V₁.subgroupOf d.AV).Normal] : d.cls 1 = 1 := by
  rw [cls_of_mem (one_mem _)]; rfl

omit h in
theorem cls_inv [(d.V₁.subgroupOf d.AV).Normal] {g : G} (hg : g ∈ d.AV) :
    d.cls g⁻¹ = (d.cls g)⁻¹ := by
  rw [cls_of_mem hg, cls_of_mem (inv_mem hg), ← QuotientGroup.mk_inv]
  rfl

omit h in
theorem cls_eq_iff [(d.V₁.subgroupOf d.AV).Normal] {g g' : G} (hg : g ∈ d.AV)
    (hg' : g' ∈ d.AV) : d.cls g = d.cls g' ↔ g⁻¹ * g' ∈ d.V₁ := by
  rw [cls_of_mem hg, cls_of_mem hg', QuotientGroup.eq, mem_subgroupOf]
  rfl

omit h in
theorem cls_eq_one_iff [(d.V₁.subgroupOf d.AV).Normal] {g : G} (hg : g ∈ d.AV) :
    d.cls g = 1 ↔ g ∈ d.V₁ := by
  rw [← cls_one, cls_eq_iff hg (one_mem _), mul_one]
  exact ⟨fun h1 => by simpa using inv_mem h1, inv_mem⟩

theorem cls_comm [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {g g' : G} (hg : g ∈ d.AV)
    (hg' : g' ∈ d.AV) : d.cls g * d.cls g' = d.cls g' * d.cls g := by
  rw [← cls_mul hg hg', ← cls_mul hg' hg, cls_eq_iff (mul_mem hg hg') (mul_mem hg' hg)]
  have h1 := (mem_inf.mp (h.AV_le_U₁ (inv_mem hg'))).2.2.2 g⁻¹ (inv_mem hg)
  rwa [show g'⁻¹ * g⁻¹ * g'⁻¹⁻¹ * g⁻¹⁻¹ = (g * g')⁻¹ * (g' * g) by group] at h1

theorem cls_conj [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {x g : G} (hx : x ∈ d.U₁)
    (hg : g ∈ d.AV) : d.cls (x * g * x⁻¹) = d.cls g := by
  have hxg : x * g * x⁻¹ ∈ d.AV :=
    (mem_normalizer_iff.mp (h.XV_le_normalizer_AV (mem_inf.mp hx).1) g).mp hg
  rw [cls_eq_iff hxg hg]
  have h1 := (mem_inf.mp hx).2.2.2 g hg
  have h2 := (mem_normalizer_iff''.mp (h.AV_le_normalizer_V₁ hg) _).mp (inv_mem h1)
  rwa [show g⁻¹ * (x * g * x⁻¹ * g⁻¹)⁻¹ * g = (x * g * x⁻¹)⁻¹ * g by group] at h2

theorem cls_conj_congr [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {k g g' : G}
    (hk : k ∈ d.XV) (hg : g ∈ d.AV) (hg' : g' ∈ d.AV) (e : d.cls g = d.cls g') :
    d.cls (k * g * k⁻¹) = d.cls (k * g' * k⁻¹) := by
  have hN := h.XV_le_normalizer_AV hk
  rw [cls_eq_iff ((mem_normalizer_iff.mp hN g).mp hg) ((mem_normalizer_iff.mp hN g').mp hg'),
    show (k * g * k⁻¹)⁻¹ * (k * g' * k⁻¹) = k * (g⁻¹ * g') * k⁻¹ by group]
  exact (mem_normalizer_iff.mp (mem_inf.mp hk).2 _).mp ((cls_eq_iff hg hg').mp e)

theorem cls_eq_iff_A₁ [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {a b : G} (ha : a ∈ d.A₁)
    (hb : b ∈ d.A₁) : d.cls a = d.cls b ↔ a⁻¹ * b ∈ zpowers d.z := by
  rw [cls_eq_iff (mem_sup_left ha) (mem_sup_left hb)]
  exact ⟨fun h1 => h.V₁_inf_H_le (mem_inf.mpr ⟨h1, h.L_le_H (h.A₁_le_L
    (mul_mem (inv_mem ha) hb))⟩), fun h1 => (zpowers_le.mpr h.z_mem_V₁) h1⟩

theorem exists_A₁_cls [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {g : G} (hg : g ∈ d.AV) :
    ∃ a ∈ d.A₁, d.cls a = d.cls g := by
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hg
  refine ⟨a, ha, (cls_eq_iff (mem_sup_left ha) hg).mpr ?_⟩
  rwa [inv_mul_cancel_left]

theorem cls_theta_mul [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {x y : G} (hx : x ∈ d.U₁)
    (hy : y ∈ d.U₁) : d.cls (d.theta (x * y)) = d.cls (d.theta x) * d.cls (d.theta y) := by
  have hθx := h.crossed_XV (mem_inf.mp hx).1
  have hθy := h.crossed_XV (mem_inf.mp hy).1
  rw [← cls_mul hθx hθy, eq_comm, cls_eq_iff (mul_mem hθx hθy)
    (h.crossed_XV (mem_inf.mp (mul_mem hx hy)).1)]
  exact h.theta_mul_mod hx hy

theorem cls_theta_inv [Finite G] [(d.V₁.subgroupOf d.AV).Normal] {x : G} (hx : x ∈ d.U₁) :
    d.cls (d.theta x⁻¹) = (d.cls (d.theta x))⁻¹ := by
  have e := h.cls_theta_mul hx (inv_mem hx)
  rw [mul_inv_cancel, h.theta_one, cls_one] at e
  exact (eq_inv_of_mul_eq_one_right e.symm)

variable (hB : HypB d)
include hB

theorem D₁_inf_C₀ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.D₁ ⊓ d.C₀ = d.AV := by
  rw [h.D₁_eq hB hV, ← h.C₀_inf_cent_V₁]
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · exact mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).1⟩
  · exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hx).2, h.C₀_le_U₁ (mem_inf.mp hx).1⟩,
      (mem_inf.mp hx).1⟩

theorem AV_le_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.AV ≤ d.D₁ := by
  rw [← h.D₁_inf_C₀ hB hV]; exact inf_le_left

theorem mem_AV_of_cls_theta [Finite G] [(d.V₁.subgroupOf d.AV).Normal]
    (hV : ∀ v ∈ d.V₁, v * v = 1) {x x' : G} (hx : x ∈ d.D₁) (hx' : x' ∈ d.D₁)
    (e : d.cls (d.theta x) = d.cls (d.theta x')) : x⁻¹ * x' ∈ d.AV := by
  have hU := h.D₁_le_U₁ hB hV
  have hθ : d.cls (d.theta (x⁻¹ * x')) = 1 := by
    rw [h.cls_theta_mul (inv_mem (hU hx)) (hU hx'), h.cls_theta_inv (hU hx), e, inv_mul_cancel]
  have hθV := (cls_eq_one_iff (h.crossed_XV (mem_inf.mp (hU (mul_mem (inv_mem hx) hx'))).1)).mp hθ
  rw [← h.D₁_inf_C₀ hB hV]
  exact mem_inf.mpr ⟨mul_mem (inv_mem hx) hx',
    h.mem_C₀_of_theta hB hV (hU (mul_mem (inv_mem hx) hx')) hθV⟩

theorem comm_mem_AV [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x y : G} (hx : x ∈ d.D₁)
    (hy : y ∈ d.D₁) : x * y * x⁻¹ * y⁻¹ ∈ d.AV := by
  have := h.V₁_normal_AV
  have hU := h.D₁_le_U₁ hB hV
  have hθ : d.cls (d.theta (x * y * x⁻¹ * y⁻¹)) = 1 := by
    rw [h.cls_theta_mul (mul_mem (mul_mem (hU hx) (hU hy)) (inv_mem (hU hx))) (inv_mem (hU hy)),
      h.cls_theta_mul (mul_mem (hU hx) (hU hy)) (inv_mem (hU hx)),
      h.cls_theta_mul (hU hx) (hU hy), h.cls_theta_inv (hU hx), h.cls_theta_inv (hU hy),
      h.cls_comm (h.crossed_D₁ hB hV hx) (h.crossed_D₁ hB hV hy)]
    group
  have hc : x * y * x⁻¹ * y⁻¹ ∈ d.D₁ := mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hθV := (cls_eq_one_iff (h.crossed_D₁ hB hV hc)).mp hθ
  rw [← h.D₁_inf_C₀ hB hV]
  exact mem_inf.mpr ⟨hc, h.mem_C₀_of_theta hB hV (hU hc) hθV⟩

theorem cls_comm_mul_left [Finite G] [(d.V₁.subgroupOf d.AV).Normal]
    (hV : ∀ v ∈ d.V₁, v * v = 1) {x x' y : G} (hx : x ∈ d.D₁) (hx' : x' ∈ d.D₁)
    (hy : y ∈ d.D₁) : d.cls (x * x' * y * (x * x')⁻¹ * y⁻¹) =
      d.cls (x * y * x⁻¹ * y⁻¹) * d.cls (x' * y * x'⁻¹ * y⁻¹) := by
  have h1 := h.comm_mem_AV hB hV hx' hy
  have h2 := h.comm_mem_AV hB hV hx hy
  rw [show x * x' * y * (x * x')⁻¹ * y⁻¹ =
      (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) by group,
    cls_mul ((mem_normalizer_iff.mp (h.XV_le_normalizer_AV (U₁_le_XV (h.D₁_le_U₁ hB hV hx)))
      _).mp h1) h2, h.cls_conj (h.D₁_le_U₁ hB hV hx) h1, h.cls_comm h1 h2]

theorem cls_comm_mul_right [Finite G] [(d.V₁.subgroupOf d.AV).Normal]
    (hV : ∀ v ∈ d.V₁, v * v = 1) {x y y' : G} (hx : x ∈ d.D₁) (hy : y ∈ d.D₁)
    (hy' : y' ∈ d.D₁) : d.cls (x * (y * y') * x⁻¹ * (y * y')⁻¹) =
      d.cls (x * y * x⁻¹ * y⁻¹) * d.cls (x * y' * x⁻¹ * y'⁻¹) := by
  have h1 := h.comm_mem_AV hB hV hx hy
  have h2 := h.comm_mem_AV hB hV hx hy'
  rw [show x * (y * y') * x⁻¹ * (y * y')⁻¹ =
      (x * y * x⁻¹ * y⁻¹) * (y * (x * y' * x⁻¹ * y'⁻¹) * y⁻¹) by group,
    cls_mul h1 ((mem_normalizer_iff.mp (h.XV_le_normalizer_AV (U₁_le_XV (h.D₁_le_U₁ hB hV hy)))
      _).mp h2), h.cls_conj (h.D₁_le_U₁ hB hV hy) h2]

theorem cls_comm_AV_left [Finite G] [(d.V₁.subgroupOf d.AV).Normal]
    (hV : ∀ v ∈ d.V₁, v * v = 1) {c y : G} (hc : c ∈ d.AV) (hy : y ∈ d.D₁) :
    d.cls (c * y * c⁻¹ * y⁻¹) = 1 := by
  have hyc : y * c⁻¹ * y⁻¹ ∈ d.AV :=
    (mem_normalizer_iff.mp (h.XV_le_normalizer_AV (U₁_le_XV (h.D₁_le_U₁ hB hV hy))) _).mp
      (inv_mem hc)
  rw [show c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) by group, cls_mul hc hyc,
    h.cls_conj (h.D₁_le_U₁ hB hV hy) (inv_mem hc), cls_inv hc, mul_inv_cancel]

theorem cls_comm_congr [Finite G] [(d.V₁.subgroupOf d.AV).Normal]
    (hV : ∀ v ∈ d.V₁, v * v = 1) {x x' y y' : G} (hx : x ∈ d.D₁) (hx' : x' ∈ d.D₁)
    (hy : y ∈ d.D₁) (hxx : x⁻¹ * x' ∈ d.AV) (hyy : y⁻¹ * y' ∈ d.AV) :
    d.cls (x' * y' * x'⁻¹ * y'⁻¹) = d.cls (x * y * x⁻¹ * y⁻¹) := by
  have hAD := h.AV_le_D₁ hB hV
  have e1 : x' = x * (x⁻¹ * x') := by group
  have e2 : y' = y * (y⁻¹ * y') := by group
  have hcomm2 : d.cls ((x⁻¹ * x') * y * (x⁻¹ * x')⁻¹ * y⁻¹) = 1 :=
    h.cls_comm_AV_left hB hV hxx hy
  have hcomm3 : d.cls (x' * (y⁻¹ * y') * x'⁻¹ * (y⁻¹ * y')⁻¹) = 1 := by
    have h3 := h.cls_comm_AV_left hB hV hyy hx'
    have hm := h.comm_mem_AV hB hV (hAD hyy) hx'
    rw [show x' * (y⁻¹ * y') * x'⁻¹ * (y⁻¹ * y')⁻¹ =
      ((y⁻¹ * y') * x' * (y⁻¹ * y')⁻¹ * x'⁻¹)⁻¹ by group, cls_inv hm, h3, inv_one]
  rw [e2, h.cls_comm_mul_right hB hV hx' hy (hAD hyy), hcomm3, mul_one, e1,
    h.cls_comm_mul_left hB hV hx (hAD hxx) hy, hcomm2, mul_one]

theorem D₁_comm_mod [Finite G] (hY : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) {x y : G}
    (hx : x ∈ d.D₁) (hy : y ∈ d.D₁) : x * y * x⁻¹ * y⁻¹ ∈ d.V₁ := by
  have := h.V₁_normal_AV
  have hAD := h.AV_le_D₁ hB hV
  have hF : ∀ a ∈ d.A₁, ∃ x ∈ d.D₁, d.cls (d.theta x) = d.cls a := fun a ha => by
    obtain ⟨x, hx, hax⟩ := h.exists_D₁_theta hB hV ha
    exact ⟨x, hx, ((cls_eq_iff (mem_sup_left ha) (h.crossed_D₁ hB hV hx)).mpr hax).symm⟩
  choose! F hFD hFθ using hF
  have hP : ∀ g ∈ d.AV, ∃ a ∈ d.A₁, d.cls a = d.cls g := fun g hg => h.exists_A₁_cls hg
  choose! P hPA hPc using hP
  have hγ : ∀ {a b : G}, a ∈ d.A₁ → b ∈ d.A₁ → F a * F b * (F a)⁻¹ * (F b)⁻¹ ∈ d.AV :=
    fun ha hb => h.comm_mem_AV hB hV (hFD _ ha) (hFD _ hb)
  set β : G → G → G := fun a b => P (F a * F b * (F a)⁻¹ * (F b)⁻¹) with hβ
  have hβA : ∀ {a b : G}, a ∈ d.A₁ → b ∈ d.A₁ → β a b ∈ d.A₁ := fun ha hb => hPA _ (hγ ha hb)
  have hβc : ∀ {a b : G}, a ∈ d.A₁ → b ∈ d.A₁ →
      d.cls (β a b) = d.cls (F a * F b * (F a)⁻¹ * (F b)⁻¹) := fun ha hb => hPc _ (hγ ha hb)
  have hFmul : ∀ {a a' : G}, a ∈ d.A₁ → a' ∈ d.A₁ → (F a * F a')⁻¹ * F (a * a') ∈ d.AV := by
    intro a a' ha ha'
    refine h.mem_AV_of_cls_theta hB hV (mul_mem (hFD _ ha) (hFD _ ha')) (hFD _ (mul_mem ha ha')) ?_
    rw [h.cls_theta_mul (h.D₁_le_U₁ hB hV (hFD _ ha)) (h.D₁_le_U₁ hB hV (hFD _ ha')), hFθ _ ha,
      hFθ _ ha', hFθ _ (mul_mem ha ha'), cls_mul (mem_sup_left ha) (mem_sup_left ha')]
  have hK : ∀ {k : G}, k ∈ d.K₁ → k ∈ d.XV := fun hk => h.K₁_le_XV hk
  have hKA : ∀ {k a : G}, k ∈ d.K₁ → a ∈ d.A₁ → k * a * k⁻¹ ∈ d.A₁ := fun hk ha =>
    (mem_normalizer_iff.mp (h.CHz_le (mem_inf.mpr ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩))
      _).mp ha
  have hKD : ∀ {k x : G}, k ∈ d.K₁ → x ∈ d.D₁ → k * x * k⁻¹ ∈ d.D₁ := fun hk hx =>
    (mem_normalizer_iff.mp (XV_le_normalizer_D₁ (hK hk)) _).mp hx
  have hFconj : ∀ {k a : G}, k ∈ d.K₁ → a ∈ d.A₁ →
      (k * F a * k⁻¹)⁻¹ * F (k * a * k⁻¹) ∈ d.AV := by
    intro k a hk ha
    refine h.mem_AV_of_cls_theta hB hV (hKD hk (hFD _ ha)) (hFD _ (hKA hk ha)) ?_
    rw [hFθ _ (hKA hk ha), Data.theta, show (k * F a * k⁻¹)⁻¹ * d.t * (k * F a * k⁻¹) * d.t =
      d.theta (k * F a * k⁻¹) from rfl, Data.theta, crossed_conj (h.comm_of_mem_L (h.K₁_le_L hk))]
    exact h.cls_conj_congr (hK hk) (h.crossed_D₁ hB hV (hFD _ ha)) (mem_sup_left ha) (hFθ _ ha)
  have hFz : F d.z ∈ d.AV := by
    have hθz : d.cls (d.theta (F d.z)) = 1 := by
      rw [hFθ _ h.z_mem_A₁, cls_eq_one_iff (mem_sup_left h.z_mem_A₁)]
      exact h.z_mem_V₁
    rw [← h.D₁_inf_C₀ hB hV]
    exact mem_inf.mpr ⟨hFD _ h.z_mem_A₁, h.mem_C₀_of_theta hB hV
      (h.D₁_le_U₁ hB hV (hFD _ h.z_mem_A₁))
      ((cls_eq_one_iff (h.crossed_D₁ hB hV (hFD _ h.z_mem_A₁))).mp hθz)⟩
  have hzz : ∀ {g : G}, g ∈ d.A₁ → d.cls g = 1 → g ∈ zpowers d.z := fun hg e => by
    have := (h.cls_eq_iff_A₁ hg (one_mem _)).mp (e.trans cls_one.symm)
    simpa using inv_mem this
  have hzero := hY.hom_wedge_A₁ β (fun a ha b hb => hβA ha hb)
    (fun a ha a' ha' b hb => by
      rw [← h.cls_eq_iff_A₁ (mul_mem (hβA ha hb) (hβA ha' hb)) (hβA (mul_mem ha ha') hb),
        cls_mul (mem_sup_left (hβA ha hb)) (mem_sup_left (hβA ha' hb)), hβc ha hb, hβc ha' hb,
        hβc (mul_mem ha ha') hb, ← h.cls_comm_mul_left hB hV (hFD _ ha) (hFD _ ha') (hFD _ hb)]
      exact (h.cls_comm_congr hB hV (mul_mem (hFD _ ha) (hFD _ ha')) (hFD _ (mul_mem ha ha'))
        (hFD _ hb) (hFmul ha ha') (by rw [inv_mul_cancel]; exact one_mem _)).symm)
    (fun a ha b hb b' hb' => by
      rw [← h.cls_eq_iff_A₁ (mul_mem (hβA ha hb) (hβA ha hb')) (hβA ha (mul_mem hb hb')),
        cls_mul (mem_sup_left (hβA ha hb)) (mem_sup_left (hβA ha hb')), hβc ha hb, hβc ha hb',
        hβc ha (mul_mem hb hb'), ← h.cls_comm_mul_right hB hV (hFD _ ha) (hFD _ hb) (hFD _ hb')]
      exact (h.cls_comm_congr hB hV (hFD _ ha) (hFD _ ha) (mul_mem (hFD _ hb) (hFD _ hb'))
        (by rw [inv_mul_cancel]; exact one_mem _) (hFmul hb hb')).symm)
    (fun a ha => hzz (hβA ha ha) (by
      rw [hβc ha ha, show F a * F a * (F a)⁻¹ * (F a)⁻¹ = 1 by group, cls_one]))
    (fun b hb => hzz (hβA h.z_mem_A₁ hb) (by
      rw [hβc h.z_mem_A₁ hb]; exact h.cls_comm_AV_left hB hV hFz (hFD _ hb)))
    (fun k hk a ha b hb => by
      rw [← h.cls_eq_iff_A₁ (hKA hk (hβA ha hb)) (hβA (hKA hk ha) (hKA hk hb)),
        h.cls_conj_congr (hK hk) (mem_sup_left (hβA ha hb)) (hγ ha hb) (hβc ha hb),
        hβc (hKA hk ha) (hKA hk hb),
        show k * (F a * F b * (F a)⁻¹ * (F b)⁻¹) * k⁻¹ = (k * F a * k⁻¹) * (k * F b * k⁻¹) *
          (k * F a * k⁻¹)⁻¹ * (k * F b * k⁻¹)⁻¹ by group]
      exact (h.cls_comm_congr hB hV (hKD hk (hFD _ ha)) (hFD _ (hKA hk ha)) (hKD hk (hFD _ hb))
        (hFconj hk ha) (hFconj hk hb)).symm)
  have hθx := h.crossed_D₁ hB hV hx
  have hθy := h.crossed_D₁ hB hV hy
  have hxa : x⁻¹ * F (P (d.theta x)) ∈ d.AV := h.mem_AV_of_cls_theta hB hV hx
    (hFD _ (hPA _ hθx)) (by rw [hFθ _ (hPA _ hθx), hPc _ hθx])
  have hyb : y⁻¹ * F (P (d.theta y)) ∈ d.AV := h.mem_AV_of_cls_theta hB hV hy
    (hFD _ (hPA _ hθy)) (by rw [hFθ _ (hPA _ hθy), hPc _ hθy])
  have e := h.cls_comm_congr hB hV hx (hFD _ (hPA _ hθx)) hy hxa hyb
  rw [← hβc (hPA _ hθx) (hPA _ hθy)] at e
  have hβ1 : d.cls (β (P (d.theta x)) (P (d.theta y))) = 1 := by
    rw [cls_eq_one_iff (mem_sup_left (hβA (hPA _ hθx) (hPA _ hθy)))]
    exact (zpowers_le.mpr h.z_mem_V₁) (hzero _ (hPA _ hθx) _ (hPA _ hθy))
  rw [hβ1] at e
  exact (cls_eq_one_iff (h.comm_mem_AV hB hV hx hy)).mp e.symm

theorem eq_D₁_of_inv [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {T : Subgroup G}
    (hTD : T ≤ d.D₁) (hAT : d.AV ≤ T) (hVT : d.V₂ ≤ T) (hKT : d.K₁ ≤ normalizer (T : Set G)) :
    T = d.D₁ := by
  have := h.V₁_normal_AV
  have hU := h.D₁_le_U₁ hB hV
  let B : Subgroup G :=
    { carrier := {a | a ∈ d.A₁ ∧ ∃ x ∈ T, d.cls (d.theta x) = d.cls a}
      one_mem' := ⟨one_mem _, 1, one_mem _, by rw [h.theta_one]⟩
      mul_mem' := by
        rintro a b ⟨ha, x, hx, hax⟩ ⟨hb, y, hy, hby⟩
        refine ⟨mul_mem ha hb, x * y, mul_mem hx hy, ?_⟩
        rw [h.cls_theta_mul (hU (hTD hx)) (hU (hTD hy)), hax, hby,
          cls_mul (mem_sup_left ha) (mem_sup_left hb)]
      inv_mem' := by
        rintro a ⟨ha, x, hx, hax⟩
        refine ⟨inv_mem ha, x⁻¹, inv_mem hx, ?_⟩
        rw [h.cls_theta_inv (hU (hTD hx)), hax, cls_inv (mem_sup_left ha)] }
  have hBA : B ≤ d.A₁ := fun _ hb => hb.1
  have hzB : zpowers d.z ≤ B := by
    rw [zpowers_le]
    refine ⟨h.z_mem_A₁, 1, one_mem _, ?_⟩
    rw [h.theta_one, cls_one, eq_comm, cls_eq_one_iff (mem_sup_left h.z_mem_A₁)]
    exact h.z_mem_V₁
  have hKB : d.K₁ ≤ normalizer (B : Set G) := by
    intro k hk
    have hkX := h.K₁_le_XV hk
    have hkA : k ∈ normalizer (d.A₁ : Set G) :=
      h.CHz_le (mem_inf.mpr ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩)
    apply mem_normalizer_of_conj_mem
    rintro a ⟨ha, x, hx, hax⟩
    refine ⟨(mem_normalizer_iff.mp hkA a).mp ha, k * x * k⁻¹,
      (mem_normalizer_iff.mp (hKT hk) x).mp hx, ?_⟩
    rw [Data.theta, show (k * x * k⁻¹)⁻¹ * d.t * (k * x * k⁻¹) * d.t =
      d.theta (k * x * k⁻¹) from rfl, Data.theta, crossed_conj (h.comm_of_mem_L (h.K₁_le_L hk))]
    exact h.cls_conj_congr hkX (h.crossed_D₁ hB hV (hTD hx)) (mem_sup_left ha) hax
  obtain ⟨b₀, hb₀, -, hb₀z⟩ := h.exists_b₀
  obtain ⟨y, hy, hyt⟩ := h.exists_V₂_conj (mem_sup_left hb₀ : b₀ ∈ d.Z₂S)
  have hb₀B : b₀ ∈ B := ⟨h.X₈_le_A₁ hb₀, y, hVT hy, by rw [Data.theta, hyt]⟩
  have hBeq : B = d.A₁ := by
    rcases hB.A₁_irred B hzB hBA hKB with hb | hb
    · exact absurd (hb ▸ hb₀B) hb₀z
    · exact hb
  refine le_antisymm hTD fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := h.exists_A₁_cls (h.crossed_D₁ hB hV hx)
  obtain ⟨-, x', hx', hx'a⟩ := (hBeq ▸ ha : a ∈ B)
  have e : x = x' * (x'⁻¹ * x) := by group
  rw [e]
  exact mul_mem hx' (hAT (h.mem_AV_of_cls_theta hB hV (hTD hx') hx (hx'a.trans hax)))

theorem D₁_sq_mod [Finite G] (hY : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G}
    (hx : x ∈ d.D₁) : x * x ∈ d.V₁ := by
  let T : Subgroup G :=
    { carrier := {x | x ∈ d.D₁ ∧ x * x ∈ d.V₁}
      one_mem' := ⟨one_mem _, by rw [one_mul]; exact one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [show a * b * (a * b) = (a * a) * (a⁻¹ * b * a⁻¹⁻¹ * b⁻¹) * (b * b) by group]
        exact mul_mem (mul_mem ha2 (h.D₁_comm_mod hB hY hV (inv_mem ha) hb)) hb2
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [← mul_inv_rev]
        exact inv_mem ha2 }
  have hAT : d.AV ≤ T := by
    intro g hg
    refine ⟨h.AV_le_D₁ hB hV hg, ?_⟩
    obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hg
    have hav : v * a = a * v := (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha).symm
    rw [show a * v * (a * v) = a * (v * a) * v by group, hav,
      show a * (a * v) * v = (a * a) * (v * v) by group]
    exact mul_mem ((zpowers_le.mpr h.z_mem_V₁) (hY.A₁_sq a ha)) (mul_mem hv hv)
  have hVT : d.V₂ ≤ T := fun y hy =>
    ⟨h.V₂_le_D₁ hB hV hy, by rw [h.D₄_sq hB hV (h.V₂_le_D₄ hy)]; exact one_mem _⟩
  have hKT : d.K₁ ≤ normalizer (T : Set G) := by
    intro k hk
    apply mem_normalizer_of_conj_mem
    rintro y ⟨hy, hy2⟩
    refine ⟨(mem_normalizer_iff.mp (XV_le_normalizer_D₁ (h.K₁_le_XV hk)) y).mp hy, ?_⟩
    rw [show k * y * k⁻¹ * (k * y * k⁻¹) = k * (y * y) * k⁻¹ by group]
    exact (mem_normalizer_iff.mp (mem_inf.mp (h.K₁_le_XV hk)).2 _).mp hy2
  have hTD : T ≤ d.D₁ := fun y hy => by
    obtain ⟨hy1, -⟩ := hy
    exact hy1
  have hT := h.eq_D₁_of_inv hB hV hTD hAT hVT hKT
  have hxT : x ∈ T := hT ▸ hx
  obtain ⟨-, hx2⟩ := hxT
  exact hx2

omit hB in
theorem mem_V₁_of_AV_cent [Finite G] {g : G} (hg : g ∈ d.AV)
    (hgc : g ∈ centralizer (d.A₁ : Set G)) : g ∈ d.V₁ := by
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hg
  have hac : a ∈ centralizer (d.A₁ : Set G) := by
    have := mul_mem hgc (inv_mem (h.V₁_le_cent_A₁ hv))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem ((zpowers_le.mpr h.z_mem_V₁) (h.center_A₁ (mem_inf.mpr ⟨ha, hac⟩))) hv

theorem center_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) :
    d.D₁ ⊓ centralizer (d.D₁ : Set G) = d.V₁ := by
  have hAD : d.A₁ ≤ d.D₁ := h.A₁_le_D₁ hB hV
  refine le_antisymm (fun c hc => ?_) (le_inf (h.V₁_le_D₁ hB hV) fun v hv =>
    mem_centralizer_iff.mpr fun x hx => ?_)
  · obtain ⟨hcD, hcC⟩ := mem_inf.mp hc
    have htc : d.t * c * d.t ∈ d.D₁ ⊓ centralizer (d.D₁ : Set G) := by
      have htN := mem_normalizer_inf (h.t_mem_normalizer_D₁)
        (mem_normalizer_of_conj_mem (fun n hn => conj_mem_centralizer h.t_mem_normalizer_D₁ hn) :
          d.t ∈ normalizer (centralizer (d.D₁ : Set G) : Set G))
      have := (mem_normalizer_iff.mp htN c).mp hc
      rwa [h.t_inv] at this
    have hθ : d.theta c ∈ d.D₁ ⊓ centralizer (d.D₁ : Set G) := by
      rw [Data.theta, show c⁻¹ * d.t * c * d.t = c⁻¹ * (d.t * c * d.t) by group]
      exact mul_mem (inv_mem hc) htc
    have hθV : d.theta c ∈ d.V₁ := h.mem_V₁_of_AV_cent (h.crossed_D₁ hB hV hcD)
      (centralizer_le hAD (mem_inf.mp hθ).2)
    have hcAV : c ∈ d.AV := by
      rw [← h.D₁_inf_C₀ hB hV]
      exact mem_inf.mpr ⟨hcD, h.mem_C₀_of_theta hB hV (h.D₁_le_U₁ hB hV hcD) hθV⟩
    exact h.mem_V₁_of_AV_cent hcAV (centralizer_le hAD hcC)
  · rw [h.D₁_eq hB hV] at hx
    exact (mem_centralizer_iff.mp (mem_inf.mp hx).1 v hv).symm

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
