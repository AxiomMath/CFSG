module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDX1V2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDOmega
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSettingB

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

namespace Data

variable (d : Data G)

abbrev AV : Subgroup G := d.A₁ ⊔ d.V₁

abbrev U₁ : Subgroup G := d.XV ⊓ actTriv d.AV d.V₁

@[expose] def theta (x : G) : G := x⁻¹ * d.t * x * d.t

end Data

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem z_cent_C₀ [Finite G] : d.z ∈ centralizer (d.C₀ : Set G) := by
  rw [h.C₀_eq]
  refine mem_centralizer_sup h.z_cent_A₁ (mem_centralizer_sup ?_ ?_)
  · exact mem_centralizer_iff.mpr fun v hv => h.V₁_comm hv h.z_mem_V₁
  · rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact ((Commute.zpow_left (show Commute d.t d.z from h.z_comm_t.symm) k))

theorem XV_cent_z [Finite G] {x : G} (hx : x ∈ d.XV) : x * d.z = d.z * x := by
  obtain ⟨hxC, hxV⟩ := mem_inf.mp hx
  have h1 : x * d.z * x⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp hxV d.z).mp h.z_mem_V₁
  have h2 : x * d.z * x⁻¹ ∈ centralizer (d.C₀ : Set G) := conj_mem_centralizer hxC h.z_cent_C₀
  have h3 : x * d.z * x⁻¹ ∈ d.H := by
    change x * d.z * x⁻¹ ∈ centralizer ({d.t} : Set G)
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp h2 d.t h.t_mem_C₀).symm
  rcases h.mem_zpowers_z_iff.mp (h.V₁_inf_H_le (mem_inf.mpr ⟨h1, h3⟩)) with e | e
  · exfalso
    apply h.z_ne_one
    calc d.z = x⁻¹ * (x * d.z * x⁻¹) * x := by group
      _ = 1 := by rw [e]; group
  · calc x * d.z = x * d.z * x⁻¹ * x := by group
      _ = d.z * x := by rw [e]

theorem mem_X_of_crossed [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G} (hx : x ∈ d.XV)
    (hw : x * d.t * x⁻¹ * d.t⁻¹ ∈ d.V₁) : x ∈ normalizer (d.ZR : Set G) := by
  set w := x * d.t * x⁻¹ * d.t⁻¹ with hwdef
  have hxt : x * d.t * x⁻¹ = w * d.t := by rw [hwdef]; group
  have hwz : w ∈ zpowers d.z := by
    by_contra hwz
    have hc := h.crossed_V₁_eq_z hw hwz
    have hsq : (w * d.t) * (w * d.t) = 1 := by
      rw [← hxt, show x * d.t * x⁻¹ * (x * d.t * x⁻¹) = x * (d.t * d.t) * x⁻¹ by group, h.t_sq]
      group
    have e : w⁻¹ * d.t * w * d.t = 1 := by
      have e1 : d.t * w * d.t = w⁻¹ := by
        calc d.t * w * d.t = w⁻¹ * ((w * d.t) * (w * d.t)) := by group
          _ = w⁻¹ := by rw [hsq, mul_one]
      calc w⁻¹ * d.t * w * d.t = w⁻¹ * (d.t * w * d.t) := by group
        _ = w⁻¹ * w⁻¹ := by rw [e1]
        _ = (w * w)⁻¹ := by group
        _ = 1 := by rw [hV w hw, inv_one]
    exact h.z_ne_one (hc ▸ e)
  refine mem_X_of (h.XV_cent_z hx) ?_
  rw [hxt]
  exact mul_mem (mem_sup_left hwz) (mem_sup_right (mem_zpowers _))

theorem crossed_XV [Finite G] {x : G} (hx : x ∈ d.XV) : d.theta x ∈ d.AV := by
  obtain ⟨hxC, hxV⟩ := mem_inf.mp hx
  have h1 : x⁻¹ * d.t * x ∈ d.C₀ := (mem_normalizer_iff''.mp hxC d.t).mp h.t_mem_C₀
  have h2 : x⁻¹ * d.t * x ∉ centralizer (d.V₁ : Set G) := by
    intro hc
    apply h.t_not_cent_V₁
    have := conj_mem_centralizer hxV hc
    rwa [show x * (x⁻¹ * d.t * x) * x⁻¹ = d.t by group] at this
  obtain ⟨a, ha, w, hw, e⟩ := h.exists_of_mem_C₀ h1 h2
  rw [Data.theta, e, mul_assoc _ d.t d.t, h.t_sq, mul_one]
  exact mul_mem (mem_sup_left ha) (mem_sup_right hw)

theorem C₀_inf_cent_V₁ [Finite G] : d.C₀ ⊓ centralizer (d.V₁ : Set G) = d.AV := by
  have hAC : d.A₁ ≤ d.C₀ := by rw [h.C₀_eq]; exact le_sup_left
  have hVC : d.V₁ ≤ d.C₀ := by rw [h.C₀_eq]; exact le_sup_right.trans' le_sup_left
  refine le_antisymm (fun y hy => ?_) (sup_le (le_inf hAC fun a ha =>
    mem_centralizer_iff.mpr fun v hv => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha).symm)
    (le_inf hVC fun v hv => mem_centralizer_iff.mpr fun w hw => h.V₁_comm hw hv))
  obtain ⟨hyC, hyV⟩ := mem_inf.mp hy
  have h1 : y * d.t ∈ d.C₀ := mul_mem hyC h.t_mem_C₀
  have h2 : y * d.t ∉ centralizer (d.V₁ : Set G) := fun hc => h.t_not_cent_V₁ (by
    have := mul_mem (inv_mem hyV) hc
    rwa [inv_mul_cancel_left] at this)
  obtain ⟨a, ha, w, hw, e⟩ := h.exists_of_mem_C₀ h1 h2
  have : y = a * w := mul_right_cancel e
  rw [this]
  exact mul_mem (mem_sup_left ha) (mem_sup_right hw)

theorem XV_le_normalizer_AV [Finite G] : d.XV ≤ normalizer (d.AV : Set G) := by
  intro x hx
  obtain ⟨hxC, hxV⟩ := mem_inf.mp hx
  apply mem_normalizer_of_conj_mem
  intro g hg
  rw [← h.C₀_inf_cent_V₁] at hg ⊢
  obtain ⟨hgC, hgV⟩ := mem_inf.mp hg
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hxC g).mp hgC, conj_mem_centralizer hxV hgV⟩

theorem mem_actTriv_of [Finite G] {y : G} (hyC : y ∈ normalizer (d.AV : Set G))
    (hyN : y ∈ normalizer (d.V₁ : Set G)) (hA : ∀ a ∈ d.A₁, y * a * y⁻¹ * a⁻¹ ∈ d.V₁) :
    y ∈ actTriv d.AV d.V₁ := by
  refine ⟨hyC, hyN, fun c hc => ?_⟩
  let T : Subgroup G :=
    { carrier := {g | g ∈ normalizer (d.V₁ : Set G) ∧ y * g * y⁻¹ * g⁻¹ ∈ d.V₁}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
            (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha' ((mem_normalizer_iff.mp ha _).mp hb')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := (mem_normalizer_iff.mp (inv_mem ha) _).mp (inv_mem ha')
        simpa using this }
  have hAT : d.A₁ ≤ T := fun a ha => ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr
    fun v hv => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha).symm), hA a ha⟩
  have hVT : d.V₁ ≤ T := fun v hv => ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr
    fun w hw => h.V₁_comm hw hv), by
      have := mul_mem ((mem_normalizer_iff.mp hyN v).mp hv) (inv_mem hv)
      simpa [mul_assoc] using this⟩
  exact (sup_le hAT hVT hc).2

theorem C₀_le_U₁ [Finite G] : d.C₀ ≤ d.U₁ := by
  intro c hc
  have hcX := h.C₀_le_XV hc
  refine mem_inf.mpr ⟨hcX, h.mem_actTriv_of (h.XV_le_normalizer_AV hcX) (mem_inf.mp hcX).2
    fun a ha => ?_⟩
  rw [h.C₀_eq] at hc
  obtain ⟨b, hb, e, he, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha e he => (mem_centralizer_iff.mp (h.E₈_le_cent_A₁ he) a ha)) hc
  have hea : e * a = a * e := (mem_centralizer_iff.mp (h.E₈_le_cent_A₁ he) a ha).symm
  have e1 : b * e * a * (b * e)⁻¹ * a⁻¹ = b * a * b⁻¹ * a⁻¹ := by
    calc b * e * a * (b * e)⁻¹ * a⁻¹ = b * (e * a) * e⁻¹ * b⁻¹ * a⁻¹ := by group
      _ = b * (a * e) * e⁻¹ * b⁻¹ * a⁻¹ := by rw [hea]
      _ = b * a * b⁻¹ * a⁻¹ := by group
  rw [e1]
  exact (zpowers_le.mpr h.z_mem_V₁) (h.A₁_comm b hb a ha)

theorem V₂_le_U₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.V₂ ≤ d.U₁ := by
  intro y hy
  have hyX := h.V₂_le_XV hy
  have hyN := (mem_inf.mp hyX).2
  refine mem_inf.mpr ⟨hyX, h.mem_actTriv_of (h.XV_le_normalizer_AV hyX) hyN fun a ha => ?_⟩
  let T : Subgroup G :=
    { carrier := {g | g ∈ normalizer (d.V₁ : Set G) ∧ y * g * y⁻¹ * g⁻¹ ∈ d.V₁}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
            (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem ha' ((mem_normalizer_iff.mp ha _).mp hb')
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := (mem_normalizer_iff.mp (inv_mem ha) _).mp (inv_mem ha')
        simpa using this }
  have hX₁T : d.X₁ ≤ T := fun x hx => ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr
    fun v hv => (mem_centralizer_iff.mp (V₁_le_cent_X₁ hv) x hx).symm), by
      have := inv_mem (h.comm_X₁_V₂ hV hx hy)
      rwa [show (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ by group] at this⟩
  have hA₃T : d.A₃ ≤ T := fun b hb => ⟨centralizer_le_normalizer _ (mem_centralizer_iff.mpr
    fun v hv => (mem_centralizer_iff.mp (h.V₁_le_cent_A₃ hv) b hb).symm), by
      rw [← mem_centralizer_iff.mp (h.D_le_cent_A₃ (h.D₄_le_D (h.V₂_le_D₄ hy))) b hb]
      simp⟩
  exact (h.A₁_le.trans (sup_le hX₁T hA₃T) ha).2

theorem AV_le_normalizer_V₁ [Finite G] : d.AV ≤ normalizer (d.V₁ : Set G) :=
  sup_le (fun a ha => centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hv =>
    (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha).symm))
    (fun _ hv => centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ hw => h.V₁_comm hw hv))

theorem V₁_normal_AV [Finite G] : (d.V₁.subgroupOf d.AV).Normal :=
  (normal_subgroupOf_iff le_sup_right).mpr fun v _ hv hk =>
    (mem_normalizer_iff.mp (h.AV_le_normalizer_V₁ hk) v).mp hv

omit h in
theorem theta_mul (ht : d.t * d.t = 1) (x y : G) :
    d.theta (x * y) = y⁻¹ * d.theta x * y * d.theta y := by
  simp only [Data.theta]
  calc (x * y)⁻¹ * d.t * (x * y) * d.t = y⁻¹ * x⁻¹ * d.t * x * (d.t * d.t) * y * d.t := by
        rw [ht]; group
    _ = y⁻¹ * (x⁻¹ * d.t * x * d.t) * y * (y⁻¹ * d.t * y * d.t) := by group

theorem theta_one : d.theta 1 = 1 := by
  simp only [Data.theta, inv_one, one_mul, mul_one, h.t_sq]

theorem theta_mul_mod [Finite G] {x y : G} (hx : x ∈ d.U₁) (hy : y ∈ d.U₁) :
    (d.theta x * d.theta y)⁻¹ * d.theta (x * y) ∈ d.V₁ := by
  have hθx := h.crossed_XV (mem_inf.mp hx).1
  have hθy := h.crossed_XV (mem_inf.mp hy).1
  have hyi : y⁻¹ ∈ actTriv d.AV d.V₁ := inv_mem (mem_inf.mp hy).2
  have hu := hyi.2.2 _ hθx
  rw [inv_inv] at hu
  rw [theta_mul h.t_sq]
  have e : (d.theta x * d.theta y)⁻¹ * (y⁻¹ * d.theta x * y * d.theta y) =
      (d.theta x * d.theta y)⁻¹ * (y⁻¹ * d.theta x * y * (d.theta x)⁻¹) *
        (d.theta x * d.theta y) := by group
  rw [e]
  have := (mem_normalizer_iff''.mp (h.AV_le_normalizer_V₁ (mul_mem hθx hθy)) _).mp hu
  exact this

@[expose] def thetaHom [Finite G] (Y : Subgroup G) (hY : Y ≤ d.U₁)
    [(d.V₁.subgroupOf d.AV).Normal] : Y →* d.AV ⧸ d.V₁.subgroupOf d.AV where
  toFun y := QuotientGroup.mk ⟨d.theta y, h.crossed_XV (mem_inf.mp (hY y.2)).1⟩
  map_one' := by
    have : (⟨d.theta 1, h.crossed_XV (one_mem _)⟩ : d.AV) = 1 := Subtype.ext h.theta_one
    simp only [OneMemClass.coe_one]
    rw [this, QuotientGroup.mk_one]
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq, mem_subgroupOf]
    exact h.theta_mul_mod (hY x.2) (hY y.2)

theorem mem_ker_thetaHom [Finite G] {Y : Subgroup G} (hY : Y ≤ d.U₁)
    [(d.V₁.subgroupOf d.AV).Normal] (y : Y) :
    y ∈ (h.thetaHom Y hY).ker ↔ d.theta y ∈ d.V₁ := by
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk _ : d.AV ⧸ d.V₁.subgroupOf d.AV) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem thetaHom_eq_iff [Finite G] {Y : Subgroup G} (hY : Y ≤ d.U₁)
    [(d.V₁.subgroupOf d.AV).Normal] (y : Y) (g : d.AV) :
    h.thetaHom Y hY y = QuotientGroup.mk g ↔ (g : G)⁻¹ * d.theta y ∈ d.V₁ := by
  change (QuotientGroup.mk _ : d.AV ⧸ d.V₁.subgroupOf d.AV) = QuotientGroup.mk g ↔ _
  rw [eq_comm, QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem theta_mem_V₁_of_C₀ [Finite G] {c : G} (hc : c ∈ d.C₀) : d.theta c ∈ d.V₁ := by
  rcases h.conj_t_C₀ hc with e | e <;> rw [Data.theta, e]
  · rw [h.t_sq]; exact one_mem _
  · rw [mul_assoc, h.t_sq, mul_one]; exact h.z_mem_V₁

omit h in
theorem U₁_le_XV : d.U₁ ≤ d.XV := inf_le_left

variable (hB : HypB d)
include hB

theorem mem_C₀_of_mem_U₁_X [Finite G] {x : G} (hx : x ∈ d.U₁)
    (hxN : x ∈ normalizer (d.ZR : Set G)) : x ∈ d.C₀ := by
  obtain ⟨v, hv, hxv⟩ := h.X_factor hxN
  have hVC : d.V₁ ≤ d.C₀ := by rw [h.C₀_eq]; exact le_sup_right.trans' le_sup_left
  have hnU : x * v⁻¹ ∈ d.U₁ := mul_mem hx (h.C₀_le_U₁ (hVC (inv_mem hv)))
  have hnA := h.CHz_le hxv
  have hmod : ∀ a ∈ d.A₁, (x * v⁻¹) * a * (x * v⁻¹)⁻¹ * a⁻¹ ∈ zpowers d.z := by
    intro a ha
    have h1 := (mem_inf.mp hnU).2.2.2 a (mem_sup_left ha)
    have h2 : (x * v⁻¹) * a * (x * v⁻¹)⁻¹ * a⁻¹ ∈ d.A₁ :=
      mul_mem ((mem_normalizer_iff.mp hnA a).mp ha) (inv_mem ha)
    exact h.V₁_inf_H_le (mem_inf.mpr ⟨h1, h.L_le_H (h.A₁_le_L h2)⟩)
  have hn := hB.CH_A₁_mod _ (mem_inf.mp hxv).2 hnA hmod
  have hnC : x * v⁻¹ ∈ d.C₀ := by
    have : x * v⁻¹ ∈ d.C₀ ⊓ d.H := by rw [h.C₀_inf_H]; exact hn
    exact (mem_inf.mp this).1
  have e : x = (x * v⁻¹) * v := by group
  rw [e]
  exact mul_mem hnC (hVC hv)

theorem mem_C₀_of_theta [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G} (hx : x ∈ d.U₁)
    (hθ : d.theta x ∈ d.V₁) : x ∈ d.C₀ := by
  have hxi : x⁻¹ ∈ d.XV := inv_mem (mem_inf.mp hx).1
  have hw : x⁻¹ * d.t * x⁻¹⁻¹ * d.t⁻¹ ∈ d.V₁ := by
    rw [inv_inv, h.t_inv]
    exact hθ
  have hN := h.mem_X_of_crossed hV hxi hw
  exact h.mem_C₀_of_mem_U₁_X hB hx (by simpa using inv_mem hN)

omit hB in
theorem conj_mem_U₁ [Finite G] {k x : G} (hk : k ∈ d.XV) (hx : x ∈ d.U₁) :
    k * x * k⁻¹ ∈ d.U₁ :=
  mem_inf.mpr ⟨mul_mem (mul_mem hk (mem_inf.mp hx).1) (inv_mem hk),
    conj_mem_actTriv (h.XV_le_normalizer_AV hk) (mem_inf.mp hk).2 (mem_inf.mp hx).2⟩

theorem exists_U₁_theta [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {a : G} (ha : a ∈ d.A₁) :
    ∃ x ∈ d.U₁, a⁻¹ * d.theta x ∈ d.V₁ := by
  have hcomm : ∀ {b w : G}, b ∈ d.A₁ → w ∈ d.V₁ → w * b = b * w := fun hb hw =>
    (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) _ hb).symm
  let B : Subgroup G :=
    { carrier := {b | b ∈ d.A₁ ∧ ∃ x ∈ d.U₁, b⁻¹ * d.theta x ∈ d.V₁}
      one_mem' := ⟨one_mem _, 1, one_mem _, by rw [h.theta_one]; simp⟩
      mul_mem' := by
        rintro b c ⟨hb, x, hx, hbx⟩ ⟨hc, y, hy, hcy⟩
        refine ⟨mul_mem hb hc, x * y, mul_mem hx hy, ?_⟩
        have hm := h.theta_mul_mod hx hy
        set p := b⁻¹ * d.theta x
        set q := c⁻¹ * d.theta y
        have e : (b * c)⁻¹ * d.theta (x * y) =
            c⁻¹ * p * c * q * ((d.theta x * d.theta y)⁻¹ * d.theta (x * y)) := by
          simp only [p, q]; group
        rw [e, show c⁻¹ * p * c = p by
          calc c⁻¹ * p * c = c⁻¹ * (p * c) := by group
            _ = c⁻¹ * (c * p) := by rw [hcomm hc hbx]
            _ = p := by group]
        exact mul_mem (mul_mem hbx hcy) hm
      inv_mem' := by
        rintro b ⟨hb, x, hx, hbx⟩
        refine ⟨inv_mem hb, x⁻¹, inv_mem hx, ?_⟩
        have hm := h.theta_mul_mod hx (inv_mem hx)
        rw [mul_inv_cancel, h.theta_one, mul_one] at hm
        have hm' := inv_mem hm
        rw [inv_inv] at hm'
        set p := b⁻¹ * d.theta x
        have e : b⁻¹⁻¹ * d.theta x⁻¹ = b * p⁻¹ * b⁻¹ * (d.theta x * d.theta x⁻¹) := by
          simp only [p]; group
        rw [e, show b * p⁻¹ * b⁻¹ = p⁻¹ by
          calc b * p⁻¹ * b⁻¹ = (p⁻¹ * b) * b⁻¹ := by rw [hcomm hb (inv_mem hbx)]
            _ = p⁻¹ := by group]
        exact mul_mem (inv_mem hbx) hm' }
  have hBA : B ≤ d.A₁ := fun _ hb => hb.1
  have hzB : zpowers d.z ≤ B := by
    rw [zpowers_le]
    exact ⟨h.z_mem_A₁, 1, one_mem _, by rw [h.theta_one, mul_one]; exact inv_mem h.z_mem_V₁⟩
  have hKB : d.K₁ ≤ normalizer (B : Set G) := by
    intro k hk
    have hkX := h.K₁_le_XV hk
    have hkA : k ∈ normalizer (d.A₁ : Set G) :=
      h.CHz_le (mem_inf.mpr ⟨h.K₁_cent_z hk, h.L_le_H (h.K₁_le_L hk)⟩)
    apply mem_normalizer_of_conj_mem
    rintro b ⟨hb, x, hx, hbx⟩
    refine ⟨(mem_normalizer_iff.mp hkA b).mp hb, k * x * k⁻¹, h.conj_mem_U₁ hkX hx, ?_⟩
    have e : d.theta (k * x * k⁻¹) = k * d.theta x * k⁻¹ :=
      crossed_conj (h.comm_of_mem_L (h.K₁_le_L hk))
    rw [e, show (k * b * k⁻¹)⁻¹ * (k * d.theta x * k⁻¹) = k * (b⁻¹ * d.theta x) * k⁻¹ by group]
    exact (mem_normalizer_iff.mp (mem_inf.mp hkX).2 _).mp hbx
  obtain ⟨b₀, hb₀, -, hb₀z⟩ := h.exists_b₀
  obtain ⟨y, hy, hyt⟩ := h.exists_V₂_conj (mem_sup_left hb₀ : b₀ ∈ d.Z₂S)
  have hb₀B : b₀ ∈ B := ⟨h.X₈_le_A₁ hb₀, y, h.V₂_le_U₁ hV hy, by
    rw [Data.theta, hyt, inv_mul_cancel]; exact one_mem _⟩
  rcases hB.A₁_irred B hzB hBA hKB with hb | hb
  · exact absurd (hb ▸ hb₀B) hb₀z
  · exact (hb ▸ ha : a ∈ B).2

omit hB in
theorem exists_V₁_not_mem_z [Finite G] : ∃ v ∈ d.V₁, v ∉ zpowers d.z := by
  obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
  refine ⟨v, hv, fun hvz => h.z_ne_one ?_⟩
  have hc : v * d.t = d.t * v := by
    rcases h.mem_zpowers_z_iff.mp hvz with rfl | rfl
    · simp
    · exact h.z_comm_t
  have : v⁻¹ * d.t * v = d.t := by rw [mul_assoc, ← hc]; group
  rw [this] at hvt
  calc d.z = d.z * d.t * d.t⁻¹ := by group
    _ = 1 := by rw [← hvt]; group

omit hB in
theorem card_AV [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : Nat.card d.AV = 2 ^ 10 := by
  obtain ⟨v₀, hv₀, hv₀z⟩ := h.exists_V₁_not_mem_z
  have hv₀A : v₀ ∉ d.A₁ := fun hA => hv₀z (h.V₁_inf_H_le (mem_inf.mpr
    ⟨hv₀, h.L_le_H (h.A₁_le_L hA)⟩))
  have heq : d.AV = d.A₁ ⊔ zpowers v₀ := by
    refine le_antisymm (sup_le le_sup_left fun w hw => ?_)
      (sup_le le_sup_left (zpowers_le.mpr (mem_sup_right hv₀)))
    by_cases hwz : w ∈ zpowers d.z
    · exact mem_sup_left ((zpowers_le.mpr h.z_mem_A₁) hwz)
    · have h1 := h.mul_inv_mem_zpowers_z hv₀ hw hv₀z hwz
      have e : w = (w * v₀⁻¹) * v₀ := by group
      rw [e]
      exact mul_mem (mem_sup_left ((zpowers_le.mpr h.z_mem_A₁) h1)) (mem_sup_right (mem_zpowers _))
  rw [heq, card_sup_zpowers (hV v₀ hv₀) (fun a ha =>
    mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv₀) a ha) hv₀A, h.card_A₁]
  norm_num

omit hB in
theorem card_quot [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) [(d.V₁.subgroupOf d.AV).Normal] :
    Nat.card (d.AV ⧸ d.V₁.subgroupOf d.AV) = 2 ^ 8 := by
  have h1 := (d.V₁.subgroupOf d.AV).card_eq_card_quotient_mul_card_subgroup
  rw [h.card_AV hV, Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : d.V₁ ≤ d.AV)).toEquiv,
    h.card_V₁] at h1
  omega

theorem card_of_onto [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {Y : Subgroup G} (hY : Y ≤ d.U₁)
    (honto : ∀ a ∈ d.A₁, ∃ y ∈ Y, a⁻¹ * d.theta y ∈ d.V₁) :
    Nat.card Y = Nat.card (Y ⊓ d.C₀ : Subgroup G) * 2 ^ 8 := by
  have := h.V₁_normal_AV
  have hrange : (h.thetaHom Y hY).range = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, w, hw, hgaw⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) g.2
    obtain ⟨y, hy, hay⟩ := honto a ha
    refine ⟨⟨y, hy⟩, (h.thetaHom_eq_iff hY ⟨y, hy⟩ g).mpr ?_⟩
    rw [← hgaw, show (a * w)⁻¹ * d.theta y = w⁻¹ * (a⁻¹ * d.theta y) by group]
    exact mul_mem (inv_mem hw) hay
  have hker : (h.thetaHom Y hY).ker = (Y ⊓ d.C₀).subgroupOf Y := by
    ext y
    rw [h.mem_ker_thetaHom hY, mem_subgroupOf, mem_inf]
    exact ⟨fun hθ => ⟨y.2, h.mem_C₀_of_theta hB hV (hY y.2) hθ⟩,
      fun hc => h.theta_mem_V₁_of_C₀ hc.2⟩
  rw [card_eq_card_ker_mul_card_range (h.thetaHom Y hY), hrange, hker, card_top,
    h.card_quot hV, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]

theorem card_U₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : Nat.card d.U₁ = 2 ^ 19 := by
  rw [h.card_of_onto hB hV le_rfl fun a ha => h.exists_U₁_theta hB hV ha,
    inf_eq_right.mpr h.C₀_le_U₁, h.card_C₀]
  norm_num

theorem isPGroup_U₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : IsPGroup 2 d.U₁ :=
  IsPGroup.of_card (h.card_U₁ hB hV)

omit hB in
theorem XV_le_normalizer_U₁ [Finite G] : d.XV ≤ normalizer (d.U₁ : Set G) := fun _ hk =>
  mem_normalizer_of_conj_mem fun _ hx => h.conj_mem_U₁ hk hx

omit h hB in
theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB' : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB' ⊢
  intro g
  simp only [mem_inf, hA g, hB' g]

theorem oTwo_XV [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : oTwo d.XV = d.U₁ := by
  have hUle : d.U₁ ≤ oTwo d.XV := le_oTwo U₁_le_XV h.XV_le_normalizer_U₁ (h.isPGroup_U₁ hB hV)
  refine le_antisymm (fun x hx => ?_) hUle
  have hxX : x ∈ d.XV := oTwo_le _ hx
  obtain ⟨a, ha, w, hw, haw⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) (h.crossed_XV hxX)
  obtain ⟨u, hu, hau⟩ := h.exists_U₁_theta hB hV ha
  set y := x * u⁻¹ with hydef
  have hyX : y ∈ d.XV := mul_mem hxX (inv_mem (U₁_le_XV hu))
  have hθy : d.theta y ∈ d.V₁ := by
    have e1 : d.theta x = u⁻¹ * d.theta y * u * d.theta u := by
      rw [← theta_mul h.t_sq, hydef, inv_mul_cancel_right]
    have e2 : d.theta y = u * (d.theta x * (d.theta u)⁻¹) * u⁻¹ := by
      rw [e1]; group
    set p := a⁻¹ * d.theta u with hpdef
    have hθu : d.theta u = a * p := by rw [hpdef]; group
    have hwp : w * p⁻¹ ∈ d.V₁ := mul_mem hw (inv_mem hau)
    have hc : a * (w * p⁻¹) = (w * p⁻¹) * a := mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hwp) a ha
    have e3 : d.theta x * (d.theta u)⁻¹ = w * p⁻¹ := by
      rw [← haw, hθu]
      calc a * w * (a * p)⁻¹ = a * (w * p⁻¹) * a⁻¹ := by group
        _ = (w * p⁻¹) * a * a⁻¹ := by rw [hc]
        _ = w * p⁻¹ := by group
    rw [e2, e3]
    exact (mem_normalizer_iff.mp (mem_inf.mp (U₁_le_XV hu)).2 _).mp hwp
  have hyN : y ∈ normalizer (d.ZR : Set G) := by
    have hw' : y⁻¹ * d.t * y⁻¹⁻¹ * d.t⁻¹ ∈ d.V₁ := by rw [inv_inv, h.t_inv]; exact hθy
    simpa using inv_mem (h.mem_X_of_crossed hV (inv_mem hyX) hw')
  have hyO : y ∈ oTwo d.XV := mul_mem hx (inv_mem (hUle hu))
  have hyC : y ∈ d.C₀ := by
    refine le_oTwo (P := oTwo d.XV ⊓ normalizer (d.ZR : Set G)) inf_le_right ?_
      ((isPGroup_oTwo _).to_le inf_le_left) (mem_inf.mpr ⟨hyO, hyN⟩)
    intro n hn
    exact mem_normalizer_inf (le_normalizer_oTwo _ (h.X_le_XV hn))
      (le_normalizer hn)
  have e : x = y * u := by rw [hydef]; group
  rw [e]
  exact mul_mem (h.C₀_le_U₁ hyC) hu

theorem D₁_eq [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) :
    d.D₁ = centralizer (d.V₁ : Set G) ⊓ d.U₁ := by
  rw [Data.D₁, ← h.oTwo_XV hB hV]

theorem D₁_le_U₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.D₁ ≤ d.U₁ := by
  rw [h.D₁_eq hB hV]; exact inf_le_right

omit hB in
theorem mul_t_cent_V₁ [Finite G] {x : G} (hx : x ∈ d.XV) (hxV : x ∉ centralizer (d.V₁ : Set G)) :
    x * d.t ∈ centralizer (d.V₁ : Set G) := by
  have hxN := (mem_inf.mp hx).2
  have hxz := h.XV_cent_z hx
  have hxz' : x * d.z * x⁻¹ = d.z := by rw [hxz]; group
  have hz1 : ∀ {w : G}, w ∈ zpowers d.z → x * w = w * x := by
    intro w hw
    rcases h.mem_zpowers_z_iff.mp hw with rfl | rfl
    · simp
    · exact hxz
  have hzt : ∀ {w : G}, w ∈ zpowers d.z → w * d.t = d.t * w := by
    intro w hw
    rcases h.mem_zpowers_z_iff.mp hw with rfl | rfl
    · simp
    · exact h.z_comm_t
  obtain ⟨w', hw', hxw'⟩ : ∃ w' ∈ d.V₁, x * w' * x⁻¹ ≠ w' := by
    by_contra hne
    push Not at hne
    exact hxV (mem_centralizer_iff.mpr fun w hw => by
      calc w * x = x * w * x⁻¹ * x := by rw [hne w hw]
        _ = x * w := by group)
  have hw'z : w' ∉ zpowers d.z := fun hz => hxw' (by rw [hz1 hz, mul_inv_cancel_right])
  have hxw'V : x * w' * x⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp hxN w').mp hw'
  have hxw'z : x * w' * x⁻¹ ∉ zpowers d.z := by
    intro hz
    apply hw'z
    rcases h.mem_zpowers_z_iff.mp hz with e | e
    · have : w' = 1 := by
        calc w' = x⁻¹ * (x * w' * x⁻¹) * x := by group
          _ = 1 := by rw [e]; group
      rw [this]; exact one_mem _
    · have : w' = d.z := by
        calc w' = x⁻¹ * (x * w' * x⁻¹) * x := by group
          _ = x⁻¹ * (d.z * x) := by rw [e]; group
          _ = d.z := by rw [← hxz]; group
      rw [this]; exact mem_zpowers _
  have hmove : x * w' * x⁻¹ = w' * d.z := by
    have h1 := h.mul_inv_mem_zpowers_z hw' hxw'V hw'z hxw'z
    rcases h.mem_zpowers_z_iff.mp h1 with e | e
    · exact absurd (mul_inv_eq_one.mp e) hxw'
    · calc x * w' * x⁻¹ = (x * w' * x⁻¹ * w'⁻¹) * w' := by group
        _ = w' * d.z := by rw [e]; exact h.V₁_comm h.z_mem_V₁ hw'
  rw [mem_centralizer_iff]
  intro w hw
  by_cases hwz : w ∈ zpowers d.z
  · calc w * (x * d.t) = (w * x) * d.t := by group
      _ = (x * w) * d.t := by rw [hz1 hwz]
      _ = x * (w * d.t) := by group
      _ = x * (d.t * w) := by rw [hzt hwz]
      _ = x * d.t * w := by group
  ·
    have htw : d.t * w * d.t⁻¹ = w * d.z := by
      have := h.crossed_V₁_eq_z hw hwz
      rw [h.t_inv]
      calc d.t * w * d.t = w * (w⁻¹ * d.t * w * d.t) := by group
        _ = w * d.z := by rw [this]
    have hxw : x * w * x⁻¹ = w * d.z := by
      rcases h.mem_zpowers_z_iff.mp (h.mul_inv_mem_zpowers_z hw' hw hw'z hwz) with e | e
      · rw [mul_inv_eq_one.mp e, hmove]
      · have hw'' : w = d.z * w' := by
          calc w = (w * w'⁻¹) * w' := by group
            _ = d.z * w' := by rw [e]
        rw [hw'']
        calc x * (d.z * w') * x⁻¹ = (x * d.z * x⁻¹) * (x * w' * x⁻¹) := by group
          _ = d.z * (w' * d.z) := by rw [hmove, hxz']
          _ = d.z * w' * d.z := by group
    have e : x * d.t * w * (x * d.t)⁻¹ = w := by
      calc x * d.t * w * (x * d.t)⁻¹ = x * (d.t * w * d.t⁻¹) * x⁻¹ := by group
        _ = x * w * x⁻¹ * (x * d.z * x⁻¹) := by rw [htw]; group
        _ = w * d.z * d.z := by rw [hxw, hxz']
        _ = w := by rw [mul_assoc, h.z_sq, mul_one]
    calc w * (x * d.t) = x * d.t * w * (x * d.t)⁻¹ * (x * d.t) := by rw [e]
      _ = x * d.t * w := by group

theorem exists_D₁_theta [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {a : G} (ha : a ∈ d.A₁) :
    ∃ x ∈ d.D₁, a⁻¹ * d.theta x ∈ d.V₁ := by
  obtain ⟨x, hx, hax⟩ := h.exists_U₁_theta hB hV ha
  rw [h.D₁_eq hB hV]
  by_cases hxV : x ∈ centralizer (d.V₁ : Set G)
  · exact ⟨x, mem_inf.mpr ⟨hxV, hx⟩, hax⟩
  · have htU : d.t ∈ d.U₁ := h.C₀_le_U₁ h.t_mem_C₀
    refine ⟨x * d.t, mem_inf.mpr ⟨h.mul_t_cent_V₁ (U₁_le_XV hx) hxV, mul_mem hx htU⟩, ?_⟩
    have hθt : d.theta d.t = 1 := by simp [Data.theta, h.t_sq]
    rw [theta_mul h.t_sq, hθt, mul_one, h.t_inv]
    have hu := (mem_inf.mp htU).2.2.2 _ (h.crossed_XV (U₁_le_XV hx))
    rw [h.t_inv] at hu
    have e : a⁻¹ * (d.t * d.theta x * d.t) =
        (a⁻¹ * (d.t * d.theta x * d.t * (d.theta x)⁻¹) * a) * (a⁻¹ * d.theta x) := by group
    rw [e]
    exact mul_mem ((mem_normalizer_iff''.mp (h.AV_le_normalizer_V₁ (mem_sup_left ha)) _).mp hu)
      hax

theorem card_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : Nat.card d.D₁ = 2 ^ 18 := by
  rw [h.card_of_onto hB hV (h.D₁_le_U₁ hB hV) fun a ha => h.exists_D₁_theta hB hV ha]
  have e : d.D₁ ⊓ d.C₀ = d.AV := by
    rw [h.D₁_eq hB hV, ← h.C₀_inf_cent_V₁]
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · exact mem_inf.mpr ⟨(mem_inf.mp hx).2, (mem_inf.mp (mem_inf.mp hx).1).1⟩
    · exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hx).2, h.C₀_le_U₁ (mem_inf.mp hx).1⟩,
        (mem_inf.mp hx).1⟩
  rw [e, h.card_AV hV]
  norm_num

theorem D₁_inf_H [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.D₁ ⊓ d.H = d.A₁ := by
  have hAC : d.A₁ ≤ d.C₀ := by rw [h.C₀_eq]; exact le_sup_left
  refine le_antisymm (fun x hx => ?_) (le_inf ?_ (h.A₁_le_L.trans h.L_le_H))
  · obtain ⟨hxD, hxH⟩ := mem_inf.mp hx
    rw [h.D₁_eq hB hV] at hxD
    obtain ⟨hxV, hxU⟩ := mem_inf.mp hxD
    have hθ : d.theta x = 1 := by
      rw [Data.theta, mul_assoc x⁻¹, ← mem_centralizer_singleton_iff.mp hxH]
      simp [h.t_sq]
    have hxC := h.mem_C₀_of_theta hB hV hxU (hθ ▸ one_mem _)
    have : x ∈ d.C₀ ⊓ d.H := mem_inf.mpr ⟨hxC, hxH⟩
    rw [h.C₀_inf_H] at this
    rcases (h.mem_withT_iff h.A₁_le_L).mp this with hxA | hxA
    · exact hxA
    · exfalso
      apply h.t_not_cent_V₁
      have haV : x * d.t ∈ centralizer (d.V₁ : Set G) := mem_centralizer_iff.mpr fun v hv =>
        (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) _ hxA).symm
      have := mul_mem (inv_mem hxV) haV
      rwa [inv_mul_cancel_left] at this
  · rw [h.D₁_eq hB hV]
    exact le_inf (fun a ha => mem_centralizer_iff.mpr fun v hv =>
      (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) a ha).symm) (hAC.trans h.C₀_le_U₁)

theorem V₂_le_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.V₂ ≤ d.D₁ := by
  rw [h.D₁_eq hB hV]
  exact le_inf (fun y hy => mem_centralizer_iff.mpr fun v hv =>
    h.D₄_comm (V₁_le_D₄ hv) (h.V₂_le_D₄ hy)) (h.V₂_le_U₁ hV)

theorem V₁_le_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.V₁ ≤ d.D₁ :=
  (le_sup_right : d.V₁ ≤ d.V₂).trans (h.V₂_le_D₁ hB hV)

theorem A₁_le_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) : d.A₁ ≤ d.D₁ := by
  rw [← h.D₁_inf_H hB hV]; exact inf_le_left

theorem crossed_D₁ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G} (hx : x ∈ d.D₁) :
    d.theta x ∈ d.AV :=
  h.crossed_XV (U₁_le_XV (h.D₁_le_U₁ hB hV hx))

omit h hB in
theorem XV_le_normalizer_D₁ [Finite G] : d.XV ≤ normalizer (d.D₁ : Set G) := by
  intro x hx
  exact mem_normalizer_inf (mem_normalizer_of_conj_mem fun _ hn =>
    conj_mem_centralizer (mem_inf.mp hx).2 hn) (le_normalizer_oTwo _ hx)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
