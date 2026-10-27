module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQMain

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ
open scoped commutatorElement

set_option maxRecDepth 10000 in
theorem augZ_comm_mX' (k : Fin 4) (v : Fin 8 → ZMod 2) : augZ (v + (mX k).mulVec v) := by
  revert k v; decide

variable {G : Type*} [Group G]

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d)
include h

theorem A₃_le_cent_D₄ : d.A₃ ≤ centralizer (d.D₄ : Set G) := fun a ha =>
  mem_centralizer_iff.mpr fun _ hx =>
    ((mem_centralizer_iff.mp (h.D_le_cent_A₃ (h.D₄_le_D hx))) a ha).symm

theorem A₃_le_XV : d.A₃ ≤ d.XV := fun _ ha =>
  h.X_le_XV (CHz_le_X ⟨mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp (h.A₃_le_cent_A₄ ha)) _ h.z_mem_A₄).symm,
    h.L_le_H (h.A₃_le_L ha)⟩)

theorem A₃_le_normalizer_D₁ : d.A₃ ≤ normalizer (d.D₁ : Set G) :=
  fun _ ha => Hyp.XV_le_normalizer_D₁ (h.A₃_le_XV ha)

omit [Finite G] in
theorem A₃_comm_t {a : G} (ha : a ∈ d.A₃) : a * d.t = d.t * a := h.comm_of_mem_L (h.A₃_le_L ha)

omit [Finite G] h in
theorem theta_conj_of_comm {a y : G} (ha : a * d.t = d.t * a) :
    d.theta (a * y * a⁻¹) = a * d.theta y * a⁻¹ := by
  have hc : Commute a d.t := ha
  simp only [Data.theta]
  calc (a * y * a⁻¹)⁻¹ * d.t * (a * y * a⁻¹) * d.t
      = a * y⁻¹ * (a⁻¹ * d.t) * a * y * (a⁻¹ * d.t) := by group
    _ = a * y⁻¹ * (d.t * a⁻¹) * a * y * (d.t * a⁻¹) := by rw [hc.inv_left.eq]
    _ = a * (y⁻¹ * d.t * y * d.t) * a⁻¹ := by group

theorem A₃_conj_mem_actTriv {a y : G} (ha : a ∈ d.A₃) (hy : y ∈ LemmaQ.actTriv d.D₄ d.V₂) :
    a * y * a⁻¹ ∈ LemmaQ.actTriv d.D₄ d.V₂ := by
  have hc := h.A₃_le_cent_D₄ ha
  have hcV : a ∈ centralizer (d.V₂ : Set G) := mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_iff.mp hc) x (h.V₂_le_D₄ hx)
  exact LemmaQ.conj_mem_actTriv (centralizer_le_normalizer _ hc)
    (centralizer_le_normalizer _ hcV) hy

section PartA

variable (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
  (h4 : Hyp416 d)

include hB hV in
theorem X₁_le_actTriv : d.X₁ ≤ LemmaQ.actTriv d.D₄ d.V₂ := by
  obtain ⟨d₀, hd₀, hθ⟩ := h.exists_d₀
  intro x hx
  refine ⟨h.X₁_le_normalizer_D₄ hx, h.X₁_le_normalizer_V₂ hV hx, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := h.exists_xs hx
  obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hy
  rw [h.conj_xs_kap hd₀ hB hV k, h.kap_inv hd₀ hB hV, ← h.kap_add hd₀ hB hV,
    h.kap_mem_V₂_iff hd₀ hB hV hθ, add_comm]
  exact augZ_comm_mX' k v

include hB hV h4 in
theorem A₁_le_actTriv : d.A₁ ≤ LemmaQ.actTriv d.D₄ d.V₂ := by
  refine h4.A₁_le_conj.trans ((closure_le _).mpr ?_)
  rintro _ ⟨a, ha, x, hx, rfl⟩
  exact h.A₃_conj_mem_actTriv ha (h.X₁_le_actTriv hB hV hx)

theorem V₁_le_actTriv : d.V₁ ≤ LemmaQ.actTriv d.D₄ d.V₂ := fun v hv =>
  ⟨Subgroup.le_normalizer (V₁_le_D₄ hv),
    LemmaQ.mem_normalizer_of_le_comm h.D₄_comm' h.V₂_le_D₄ (V₁_le_D₄ hv), fun y hy => by
      rw [h.D₄_comm (V₁_le_D₄ hv) hy, mul_inv_cancel_right, mul_inv_cancel]; exact one_mem _⟩

include hB hC hV in
theorem E₁_le_actTriv
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ LemmaQ.actTriv d.D₄ d.V₂ := fun u hu =>
  ⟨hLQ.1 hu, h.E₁_le_normalizer_V₂ hB hC hV hu, fun y hy => by
    have := hLQ.2.2 (commutator_mem_commutator hy hu)
    rw [← inv_mem_iff, commutatorElement_def] at this
    simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem A₃_conj_X₁_mem_A₁ (h4 : Hyp416 d) {a x : G} (ha : a ∈ d.A₃) (hx : x ∈ d.X₁) :
    a * x * a⁻¹ ∈ d.A₁ :=
  (mem_normalizer_iff.mp (h.CHz_le ⟨mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp (h.A₃_le_cent_A₄ ha)) _ h.z_mem_A₄).symm,
    h.L_le_H (h.A₃_le_L ha)⟩) x).mp (h4.X₁_le_A₁ hx)

include hB hC hV hQ h4 in
theorem D₁_le_actTriv
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    d.D₁ ≤ LemmaQ.actTriv d.D₄ d.V₂ := by
  have := h.V₁_normal_AV
  set M := (d.D₁ ⊓ LemmaQ.actTriv d.D₄ d.V₂ : Subgroup G) with hM
  have hEM : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ M :=
    le_inf inf_le_left (h.E₁_le_actTriv hB hC hV hLQ)
  have hAVM : d.AV ≤ M := sup_le (le_inf (h.A₁_le_D₁ hB hV) (h.A₁_le_actTriv hB hV h4))
    (le_inf (h.V₁_le_D₁ hB hV) h.V₁_le_actTriv)
  have hMU : ∀ {w : G}, w ∈ M → w ∈ d.U₁ := fun hw => h.D₁_le_U₁ hB hV hw.1
  let T : Subgroup G :=
    { carrier := {g | g ∈ d.AV ∧ ∃ w ∈ M, d.cls (d.theta w) = d.cls g}
      mul_mem' := by
        rintro g g' ⟨hg, w, hw, hwg⟩ ⟨hg', w', hw', hwg'⟩
        exact ⟨mul_mem hg hg', w * w', mul_mem hw hw', by
          rw [h.cls_theta_mul (hMU hw) (hMU hw'), hwg, hwg', cls_mul hg hg']⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, by rw [h.theta_one]⟩
      inv_mem' := by
        rintro g ⟨hg, w, hw, hwg⟩
        exact ⟨inv_mem hg, w⁻¹, inv_mem hw, by
          rw [h.cls_theta_inv (hMU hw), hwg, cls_inv hg]⟩ }
  have hT : d.AV ≤ T := by
    refine sup_le (h4.A₁_le_conj.trans ((closure_le _).mpr ?_)) ?_
    · rintro _ ⟨a, ha, x, hx, rfl⟩
      obtain ⟨y, hy, hθy⟩ := h.exists_conjG_V₂_theta hQ hx
      have hyM : y ∈ M := hEM (h.conjG_V₂_le_E₁ hQ hB hV hy)
      have haM : a ∈ normalizer (M : Set G) := mem_normalizer_inf (h.A₃_le_normalizer_D₁ ha)
        (mem_normalizer_of_conj_mem fun z hz => h.A₃_conj_mem_actTriv ha hz)
      refine ⟨mem_sup_left (h.A₃_conj_X₁_mem_A₁ h4 ha hx), a * y * a⁻¹,
        (mem_normalizer_iff.mp haM y).mp hyM, ?_⟩
      rw [theta_conj_of_comm (h.A₃_comm_t ha), hθy]
    · intro v hv
      exact ⟨mem_sup_right hv, 1, one_mem _, by
        rw [h.theta_one, cls_one, (cls_eq_one_iff (mem_sup_right hv)).mpr hv]⟩
  intro u hu
  obtain ⟨-, w, hw, hwu⟩ := hT (h.crossed_D₁ hB hV hu)
  have hD : u * w⁻¹ ∈ d.D₁ := mul_mem hu (inv_mem hw.1)
  have h1 : u * w⁻¹ ∈ d.AV := by
    rw [← h.theta_mem_V₁_iff hB hV hD, ← cls_eq_one_iff (h.crossed_D₁ hB hV hD),
      h.cls_theta_mul (h.D₁_le_U₁ hB hV hu) (hMU (inv_mem hw)), h.cls_theta_inv (hMU hw), hwu,
      mul_inv_cancel]
  have e : u = (u * w⁻¹) * w := by group
  rw [e]
  exact (mul_mem (hAVM h1) hw).2

include hB hC hV hQ h4 in
theorem D₄_le_normalizer_D₁
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    d.D₄ ≤ normalizer (d.D₁ : Set G) := by
  have hc : ⁅d.D₄, d.D₁⁆ ≤ d.V₂ := by
    rw [commutator_le]
    intro x hx u hu
    have := ((h.D₁_le_actTriv hB hC hV hQ h4 hLQ) hu).2.2 x hx
    rw [← inv_mem_iff] at this
    rw [commutatorElement_def]
    simpa [mul_assoc] using this
  exact LemmaQ.le_normalizer_of_commutator_le hc (h.V₂_le_D₁ hB hV)

theorem A₂_le_normalizer_D₁ : d.A₂ ≤ normalizer (d.D₁ : Set G) := fun a ha =>
  Hyp.XV_le_normalizer_D₁ (h.X_le_XV (CHz_le_X ⟨mem_centralizer_singleton_iff.mpr
    (h.A₂_comm a ha d.z h.z_mem_A₂), h.L_le_H (h.A₂_le_L ha)⟩))

include hB hC hV hQ h4 in
theorem D₂_le_normalizer_D₁
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    d.D₂ ≤ normalizer (d.D₁ : Set G) := by
  set N₂ := (d.D₂ ⊓ normalizer (d.D₁ : Set G) : Subgroup G) with hN₂
  have hYB : N₂ ≤ centralizer (d.A₂ : Set G) := fun y hy => h.C₂_le_cent hy.1.1
  have hY : ∀ y ∈ N₂, y⁻¹ * d.t * y * d.t ∈ d.A₂ := fun y hy => h.crossed_C₂ hy.1.1
  set f := crossedHom h.t_sq d.A₂ N₂ hYB hY with hf
  set R := f.range.map d.A₂.subtype with hR
  have hRA : R ≤ d.A₂ := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hA₄R : d.A₄ ≤ R := by
    intro a ha
    obtain ⟨y, hy, hyt⟩ := h.exists_D₄_conj ha
    have hyN : y ∈ N₂ := ⟨h.D₄_le_D₂ hy, h.D₄_le_normalizer_D₁ hB hC hV hQ h4 hLQ hy⟩
    refine ⟨f ⟨y, hyN⟩, ⟨⟨y, hyN⟩, rfl⟩, ?_⟩
    change y⁻¹ * d.t * y * d.t = a
    rw [hyt, mul_assoc, h.t_sq, mul_one]
  have hKR : d.K₁ ⊓ d.K₂ ≤ normalizer (R : Set G) := by
    intro k ⟨hk₁, hk₂⟩
    have hkt : k * d.t = d.t * k := h.comm_of_mem_L (h.K₁_le_L hk₁)
    have hkD₁ : k ∈ normalizer (d.D₁ : Set G) := Hyp.XV_le_normalizer_D₁ (h.K₁_le_XV hk₁)
    apply mem_normalizer_of_conj_mem
    rintro _ ⟨x, ⟨n, rfl⟩, rfl⟩
    have hn2 := mem_inf.mp n.2
    have hn : k * (n : G) * k⁻¹ ∈ N₂ :=
      mem_inf.mpr ⟨(mem_normalizer_iff.mp (h.K₂_le_normalizer_D₂ hB hk₂) n).mp hn2.1,
        (normalizer (d.D₁ : Set G)).mul_mem ((normalizer (d.D₁ : Set G)).mul_mem hkD₁ hn2.2)
          ((normalizer (d.D₁ : Set G)).inv_mem hkD₁)⟩
    refine ⟨f ⟨_, hn⟩, ⟨⟨_, hn⟩, rfl⟩, ?_⟩
    change (k * (n : G) * k⁻¹)⁻¹ * d.t * (k * n * k⁻¹) * d.t =
      k * ((n : G)⁻¹ * d.t * n * d.t) * k⁻¹
    exact theta_conj_of_comm hkt
  have hReq : R = d.A₂ := h4.A₂_closure R hA₄R hRA hKR
  have hcard := card_eq_of_crossed h.t_sq hYB hY
  have h1 : Nat.card f.range = 2 ^ 9 := by
    have e1 : Nat.card R = Nat.card f.range :=
      Subgroup.card_map_of_injective d.A₂.subtype_injective
    rw [← e1, hReq, h.card_A₂]
  have hA₂N : d.A₂ ≤ N₂ := le_inf h.A₂_le_D₂ h.A₂_le_normalizer_D₁
  have h2 : 2 ^ 9 ≤ Nat.card (N₂ ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
    rw [← h.card_A₂]
    exact Subgroup.card_le_of_le (le_inf hA₂N fun x hx => h.L_le_H (h.A₂_le_L hx))
  have h3 : Nat.card d.D₂ ≤ Nat.card N₂ := by
    rw [h.card_D₂ hB, hcard, h1]
    calc 2 ^ 18 = 2 ^ 9 * 2 ^ 9 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_right _ h2
  have heq : N₂ = d.D₂ := Subgroup.eq_of_le_of_card_ge inf_le_left h3
  rw [← heq]
  exact inf_le_right

theorem AV_cent_le_D₂ (h4 : Hyp416 d) {x : G} (hx : x ∈ d.AV)
    (hc : x ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G)) : x ∈ d.D₂ := by
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hx
  have hva : v ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun y hy => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) y hy.1)
  have hac : a ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) := by
    have : a = (a * v) * v⁻¹ := by group
    rw [this]; exact mul_mem hc (inv_mem hva)
  exact mul_mem (h.A₂_le_D₂ (h4.CA₁A₂ ⟨ha, hac⟩)) (h.V₁_le_D₂ hv)

include hB hV h4 in
theorem D₁_cent_le_D₂ {u : G} (hu : u ∈ d.D₁)
    (hc : u ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G)) : u ∈ d.D₂ := by
  have := h.V₁_normal_AV
  have hθu := h.crossed_D₁ hB hV hu
  have hθc : d.theta u ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) := by
    have ht : d.t ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun y hy => (h.comm_of_mem_L (h.A₁_le_L hy.1))
    simp only [Data.theta]
    exact mul_mem (mul_mem (mul_mem (inv_mem hc) ht) hc) ht
  obtain ⟨a, ha, v, hv, hav⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hw) a ha)) hθu
  have hva : v ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun y hy => (mem_centralizer_iff.mp (h.V₁_le_cent_A₁ hv) y hy.1)
  have hac' : a ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) := by
    have : a = d.theta u * v⁻¹ := by rw [← hav]; group
    rw [this]
    exact Subgroup.mul_mem _ hθc (Subgroup.inv_mem _ hva)
  have hac : a ∈ d.A₁ ⊓ d.A₂ := ⟨ha, h4.CA₁A₂ ⟨ha, hac'⟩⟩
  have hcomm : ∀ x ∈ d.Z₂S, ∀ y ∈ d.conjW d.Z₂S, x * y = y * x := fun x hx y hy =>
    h.A₂_comm x (h.A₄_le_A₂ (h.Z₂S_le_A₄ hx)) y (by
      obtain ⟨y', hy', rfl⟩ := mem_conjW.mp hy
      exact (mem_normalizer_iff.mp (hB.K₂_le_normalizer hB.w₂_mem_K₂) y').mp
        (h.A₄_le_A₂ (h.Z₂S_le_A₄ hy')))
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm (hB.A₁_inf_A₂ hac)
  · obtain ⟨y₁, hy₁, hθ₁⟩ := h.exists_V₂_conj hb₁
    obtain ⟨b₂', hb₂', rfl⟩ := mem_conjW.mp hb₂
    obtain ⟨y₂', hy₂', hθ₂⟩ := h.exists_V₂_conj hb₂'
    set y₂ := d.w₂ * y₂' * d.w₂⁻¹ with hy₂
    have hy₂D : y₂ ∈ d.D₁ ⊓ d.D₂ :=
      ⟨h.conjW_V₂_le_D₁ hB hV (mem_conjW.mpr ⟨y₂', hy₂', rfl⟩),
        h.conjW_V₂_le_D₂ hB (mem_conjW.mpr ⟨y₂', hy₂', rfl⟩)⟩
    have hy₁D : y₁ ∈ d.D₁ ⊓ d.D₂ := ⟨h.V₂_le_D₁ hB hV hy₁, h.V₂_le_D₂ hy₁⟩
    have hθy₂ : d.theta y₂ = d.w₂ * b₂' * d.w₂⁻¹ := by
      rw [hy₂, theta_conj_of_comm (h.comm_of_mem_L (hB.K₂_le_L hB.w₂_mem_K₂))]
      change d.w₂ * (y₂'⁻¹ * d.t * y₂' * d.t) * d.w₂⁻¹ = _
      rw [hθ₂]
    set w := y₁ * y₂ with hw
    have hwD : w ∈ d.D₁ ⊓ d.D₂ := mul_mem hy₁D hy₂D
    have hU : ∀ {z : G}, z ∈ d.D₁ → z ∈ d.U₁ := fun hz => h.D₁_le_U₁ hB hV hz
    have hb₁A : b₁ ∈ d.AV := mem_sup_left (h.Z₂S_le_A₁ hb₁)
    have hb₂A : d.w₂ * b₂' * d.w₂⁻¹ ∈ d.AV := by
      have hmem : d.w₂ * b₂' * d.w₂⁻¹ ∈ d.A₁ :=
        (mem_normalizer_iff.mp (h.X_le_normalizer_A₁ (h.K₁_le_X hB.w₂_mem_K₁)) b₂').mp
          (h.Z₂S_le_A₁ hb₂')
      exact mem_sup_left hmem
    have c1 : d.cls (d.theta u) = d.cls b₁ * d.cls (d.w₂ * b₂' * d.w₂⁻¹) := by
      rw [← hav, cls_mul (mem_sup_left ha) (mem_sup_right hv),
        (cls_eq_one_iff (mem_sup_right hv)).mpr hv, mul_one, cls_mul hb₁A hb₂A]
    have c2 : d.cls (d.theta w) = d.cls b₁ * d.cls (d.w₂ * b₂' * d.w₂⁻¹) := by
      rw [hw, h.cls_theta_mul (hU hy₁D.1) (hU hy₂D.1), hθy₂]
      simp only [Data.theta] at hθ₁ ⊢
      rw [hθ₁]
    have hD : u * w⁻¹ ∈ d.D₁ := mul_mem hu (inv_mem hwD.1)
    have huw : u * w⁻¹ ∈ d.AV := by
      rw [← h.theta_mem_V₁_iff hB hV hD, ← cls_eq_one_iff (h.crossed_D₁ hB hV hD),
        h.cls_theta_mul (hU hu) (hU (inv_mem hwD.1)), h.cls_theta_inv (hU hwD.1), c1, c2,
        mul_inv_cancel]
    have hwc : w ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) :=
      mem_centralizer_iff.mpr fun y hy => h.D₂_comm hB (h.A₂_le_D₂ hy.2) hwD.2
    have h1 := h.AV_cent_le_D₂ h4 huw (mul_mem hc (inv_mem hwc))
    have e : u = (u * w⁻¹) * w := by group
    rw [e]
    exact mul_mem h1 hwD.2

include hB hC hV in
theorem D₁_le_normalizer_inf : d.D₁ ≤ normalizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) :=
  h.D₁_le_normalizer_of hB hC hV (le_inf (h.V₁_le_D₁ hB hV) h.V₁_le_D₂) inf_le_left

include hB hC hV hQ h4 in
theorem D₁_le_normalizer_D₂
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    d.D₁ ≤ normalizer (d.D₂ : Set G) := by
  have hD₂ := h.D₂_le_normalizer_D₁ hB hC hV hQ h4 hLQ
  intro x hx
  apply mem_normalizer_of_conj_mem
  intro y hy
  have hc1 : x * y * x⁻¹ * y⁻¹ ∈ d.D₁ := by
    have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [this]
    exact mul_mem hx ((mem_normalizer_iff.mp (hD₂ hy) x⁻¹).mp (inv_mem hx))
  have hyc : y ∈ centralizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun z hz => h.D₂_comm hB hz.2 hy
  have hxyc : x * y * x⁻¹ ∈ centralizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) :=
    conj_mem_centralizer (h.D₁_le_normalizer_inf hB hC hV hx) hyc
  have hcc : x * y * x⁻¹ * y⁻¹ ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) := by
    have h1 := Subgroup.mul_mem _ hxyc (Subgroup.inv_mem _ hyc)
    exact mem_centralizer_iff.mpr fun z hz => (mem_centralizer_iff.mp h1) z
      ⟨h.A₁_le_D₁ hB hV hz.1, h.A₂_le_D₂ hz.2⟩
  have hcD := h.D₁_cent_le_D₂ hB hV h4 hc1 hcc
  have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
  rw [e]
  exact mul_mem hcD hy

include hB in
theorem exists_D₂_theta {c : G} (hc : c ∈ d.A₂) : ∃ y ∈ d.D₂, d.theta y = c := by
  obtain ⟨x, hx, hxt⟩ := h.C₂_conj c hc
  have hct : c * d.t = d.t * c := h.comm_of_mem_L (h.A₂_le_L hc)
  rw [h.C₂_eq_D₂_t hB, mem_sup_zpowers_of_normalizer h.t_mem_normalizer_D₂
    (by rw [h.t_sq]; exact one_mem _), h.t_inv] at hx
  rcases hx with hx | hx
  · exact ⟨x, hx, by rw [Data.theta, hxt, mul_assoc, h.t_sq, mul_one]⟩
  · refine ⟨x * d.t, hx, ?_⟩
    simp only [Data.theta]
    calc (x * d.t)⁻¹ * d.t * (x * d.t) * d.t = d.t⁻¹ * (x⁻¹ * d.t * x) * (d.t * d.t) := by group
      _ = c := by rw [hxt, h.t_sq, mul_one, h.t_inv, ← mul_assoc, ← hct, mul_assoc, h.t_sq,
          mul_one]

omit [Finite G] in
theorem theta_mul_D₂ {x y : G} (hx : x ∈ d.D₂) (hy : y ∈ d.D₂) :
    d.theta (x * y) = d.theta x * d.theta y := by
  rw [theta_mul h.t_sq]
  have h1 : d.theta x * y = y * d.theta x :=
    mem_centralizer_iff.mp (h.C₂_le_cent hy.1) _ (h.crossed_C₂ hx.1)
  rw [mul_assoc y⁻¹, h1]; group

omit [Finite G] in
theorem theta_comm_D₂ {a y : G} (ha : a * d.t = d.t * a) (haD : a ∈ normalizer (d.D₂ : Set G))
    (hy : y ∈ d.D₂) : d.theta ⁅a, y⁆ = ⁅a, d.theta y⁆ := by
  have hay : a * y * a⁻¹ ∈ d.D₂ := (mem_normalizer_iff.mp haD y).mp hy
  rw [commutatorElement_def, commutatorElement_def, h.theta_mul_D₂ hay (inv_mem hy),
    theta_conj_of_comm ha]
  congr 1
  have h1 := h.theta_mul_D₂ hy (inv_mem hy)
  rw [mul_inv_cancel, h.theta_one] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)

include hB hC hV hQ h4 in
theorem comm_sup_le_inf
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    ⁅d.D₁ ⊔ d.D₂, d.D₁ ⊔ d.D₂⁆ ≤ d.D₁ ⊓ d.D₂ := by
  have hD₂₁ := h.D₂_le_normalizer_D₁ hB hC hV hQ h4 hLQ
  have hD₁₂ := h.D₁_le_normalizer_D₂ hB hC hV hQ h4 hLQ
  have hN : ∀ s ∈ (d.D₁ : Set G) ∪ d.D₂, s ∈ normalizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) := by
    rintro s (hs | hs)
    · exact h.D₁_le_normalizer_inf hB hC hV hs
    · exact LemmaQ.mem_normalizer_of_le_comm (fun a ha b hb => h.D₂_comm hB ha hb) inf_le_right hs
  have h12 : ∀ x ∈ d.D₁, ∀ y ∈ d.D₂, ⁅x, y⁆ ∈ d.D₁ ⊓ d.D₂ := fun x hx y hy => by
    rw [commutatorElement_def]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact d.D₁.mul_mem hx ((mem_normalizer_iff.mp (hD₂₁ hy) x⁻¹).mp (d.D₁.inv_mem hx))
    · exact d.D₂.mul_mem ((mem_normalizer_iff.mp (hD₁₂ hx) y).mp hy) (d.D₂.inv_mem hy)
  rw [sup_eq_closure]
  refine commutator_closure_le hN hN ?_
  rintro m (hm | hm) s (hs | hs)
  · have := h.D₁_comm_mod hB hC hV hm hs
    rw [commutatorElement_def]
    exact Subgroup.mem_inf.mpr ⟨h.V₁_le_D₁ hB hV this, h.V₁_le_D₂ this⟩
  · exact h12 m hm s hs
  · rw [← commutatorElement_inv]; exact Subgroup.inv_mem _ (h12 s hs m hm)
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.D₂_comm hB hm hs)]
    exact Subgroup.one_mem _

include hB hC hV hQ h4 in
theorem comm_sup_eq_inf
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    ⁅d.D₁ ⊔ d.D₂, d.D₁ ⊔ d.D₂⁆ = d.D₁ ⊓ d.D₂ := by
  refine le_antisymm (h.comm_sup_le_inf hB hC hV hQ h4 hLQ) ?_
  have hD₁₂ := h.D₁_le_normalizer_D₂ hB hC hV hQ h4 hLQ
  set K := ⁅d.A₁, d.D₂⁆ with hK
  have hKle : K ≤ ⁅d.D₁ ⊔ d.D₂, d.D₁ ⊔ d.D₂⁆ :=
    commutator_mono ((h.A₁_le_D₁ hB hV).trans le_sup_left) le_sup_right
  have hKinf : K ≤ d.D₁ ⊓ d.D₂ := hKle.trans (h.comm_sup_le_inf hB hC hV hQ h4 hLQ)
  have hKD₂ : K ≤ d.D₂ := hKinf.trans inf_le_right
  have hYB : K ≤ centralizer (d.A₂ : Set G) := fun y hy => h.C₂_le_cent (hKD₂ hy).1
  have hY : ∀ y ∈ K, y⁻¹ * d.t * y * d.t ∈ d.A₂ := fun y hy => h.crossed_C₂ (hKD₂ hy).1
  have hcard := card_eq_of_crossed h.t_sq hYB hY
  set f := crossedHom h.t_sq d.A₂ K hYB hY with hf
  have hker : 2 ^ 5 ≤ Nat.card (K ⊓ centralizer ({d.t} : Set G) : Subgroup G) := by
    rw [← h4.card_A₁A₂]
    refine Subgroup.card_le_of_le (le_inf (h4.A₁A₂_le_comm.trans
      (commutator_mono le_rfl h.A₂_le_D₂)) fun x hx => ?_)
    exact h.L_le_H (h.A₂_le_L hx.2)
  have himg : 2 ^ 5 ≤ Nat.card f.range := by
    rw [← h4.card_A₁A₂]
    have hle : d.A₁ ⊓ d.A₂ ≤ f.range.map d.A₂.subtype := by
      refine h4.A₁A₂_le_comm.trans ?_
      rw [commutator_le]
      intro a ha c hc
      obtain ⟨y, hy, hθy⟩ := h.exists_D₂_theta hB hc
      have hat : a * d.t = d.t * a := h.comm_of_mem_L (h.A₁_le_L ha)
      have haN : a ∈ normalizer (d.D₂ : Set G) := hD₁₂ (h.A₁_le_D₁ hB hV ha)
      have hk : ⁅a, y⁆ ∈ K := commutator_mem_commutator ha hy
      refine ⟨f ⟨_, hk⟩, ⟨⟨_, hk⟩, rfl⟩, ?_⟩
      change ⁅a, y⁆⁻¹ * d.t * ⁅a, y⁆ * d.t = ⁅a, c⁆
      have := h.theta_comm_D₂ hat haN hy
      simp only [Data.theta] at this
      rw [this]
      simp only [Data.theta] at hθy
      rw [hθy]
    calc Nat.card (d.A₁ ⊓ d.A₂ : Subgroup G) ≤ Nat.card (f.range.map d.A₂.subtype) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card f.range := Subgroup.card_map_of_injective d.A₂.subtype_injective
  have hK10 : 2 ^ 10 ≤ Nat.card K := by
    rw [hcard]
    calc 2 ^ 10 = 2 ^ 5 * 2 ^ 5 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hker himg
  have heq : K = d.D₁ ⊓ d.D₂ :=
    Subgroup.eq_of_le_of_card_ge hKinf (by rw [h.card_D₁_inf_D₂ hB hV]; exact hK10)
  rw [← heq]
  exact hKle

include hB hC hV hQ h4 in
theorem sup_inf_cent_eq_D₂
    (hLQ : d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂) :
    (d.D₁ ⊔ d.D₂) ⊓ centralizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) = d.D₂ := by
  have hD₂₁ := h.D₂_le_normalizer_D₁ hB hC hV hQ h4 hLQ
  refine le_antisymm (fun x hx' => ?_) (le_inf le_sup_right fun y hy =>
    mem_centralizer_iff.mpr fun z hz => h.D₂_comm hB hz.2 hy)
  obtain ⟨hx, hc⟩ := mem_inf.mp hx'
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hD₂₁] at hx
  obtain ⟨u, hu, y, hy, rfl⟩ := hx
  have hyc : y ∈ centralizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) :=
    mem_centralizer_iff.mpr fun z hz => h.D₂_comm hB hz.2 hy
  have huc : u ∈ centralizer ((d.A₁ ⊓ d.A₂ : Subgroup G) : Set G) := by
    have h1 : u ∈ centralizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) := by
      have : u = (u * y) * y⁻¹ := by group
      rw [this]; exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hyc)
    exact mem_centralizer_iff.mpr fun z hz => (mem_centralizer_iff.mp h1) z
      ⟨h.A₁_le_D₁ hB hV hz.1, h.A₂_le_D₂ hz.2⟩
  exact mul_mem (h.D₁_cent_le_D₂ hB hV h4 hu huc) hy

end PartA

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
