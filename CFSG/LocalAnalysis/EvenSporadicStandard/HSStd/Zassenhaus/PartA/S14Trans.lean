module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Cent

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath

namespace S14Cfg

variable {G : Type} [Group G] [Finite G] {t : G} (c : S14Cfg G t)

include c

theorem tut : t * c.u * t = c.u := by
  calc t * c.u * t = (c.u * t) * t := by rw [c.t_comm_u]
    _ = c.u := by rw [mul_assoc, c.t_sq, mul_one]

theorem tu₁t : t * c.u₁ * t = c.u * c.u₁ := by
  have := c.u₁_conj
  rwa [c.t_inv] at this

theorem u₁_ne_u : c.u₁ ≠ c.u := by
  intro h
  have := c.tu₁t
  rw [h, c.tut, c.u_sq] at this
  exact c.u_ne_one this

theorem u₁_mem_P : c.u₁ ∈ c.P := c.u₁_mem.1.1

theorem conj_u₁_cases {p : G} (hp : p ∈ c.P) :
    p * c.u₁ * p⁻¹ = c.u₁ ∨ p * c.u₁ * p⁻¹ = c.u * c.u₁ := by
  let p' : ↥c.P := ⟨p, hp⟩
  let u₁' : ↥c.P := ⟨c.u₁, c.u₁_mem_P⟩
  have hker : u₁' ∈ c.pair.rho.ker := by
    rw [c.pair.ker_rho, mem_subgroupOf]
    exact ⟨c.u₁_mem.1.2, c.u₁_mem.2⟩
  have hk2 := (c.pair.rho.normal_ker).conj_mem u₁' hker p'
  rw [c.pair.ker_rho, mem_subgroupOf] at hk2
  have hpu : p * c.u = c.u * p := mem_centralizer_singleton_iff.1 hp
  have hpuc : p * c.u * p⁻¹ = c.u := by rw [hpu]; group
  have hpuc' : p⁻¹ * c.u * p = c.u := by
    calc p⁻¹ * c.u * p = p⁻¹ * (c.u * p) := mul_assoc _ _ _
      _ = p⁻¹ * (p * c.u) := by rw [hpu]
      _ = c.u := inv_mul_cancel_left _ _
  have hw : p * c.u₁ * p⁻¹ ∈ centralizer ({c.u} : Set G) ⊓ centralizer (c.L₁ : Set G) ⊓
      centralizer ((conjSub t c.L₁ : Subgroup G) : Set G) := by
    refine ⟨⟨?_, hk2.1⟩, hk2.2⟩
    apply mem_centralizer_singleton_iff.2
    calc p * c.u₁ * p⁻¹ * c.u = p * c.u₁ * (p⁻¹ * c.u * p) * p⁻¹ := by group
      _ = p * c.u₁ * c.u * p⁻¹ := by rw [hpuc']
      _ = p * (c.u₁ * c.u) * p⁻¹ := by group
      _ = p * (c.u * c.u₁) * p⁻¹ := by rw [c.u₁_mul_u]
      _ = (p * c.u) * c.u₁ * p⁻¹ := by group
      _ = (c.u * p) * c.u₁ * p⁻¹ := by rw [hpu]
      _ = c.u * (p * c.u₁ * p⁻¹) := by group
  rw [c.F_eq] at hw
  have hcm : Cm (zpowers c.u) (zpowers c.u₁) := cm_zpowers_zpowers c.u₁_mul_u.symm
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_cm hcm).1 hw
  rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u_sq ha with rfl | rfl <;>
    rcases eq_one_or_eq_of_mem_zpowers_of_mul_self c.u₁_sq hb with rfl | rfl
  · exfalso
    rw [one_mul] at hab
    apply c.u₁_ne_one
    have : c.u₁ = p⁻¹ * (p * c.u₁ * p⁻¹) * p := by group
    rw [this, hab]; group
  · left
    rw [one_mul] at hab
    exact hab
  · exfalso
    rw [mul_one] at hab
    apply c.u₁_ne_u
    have : c.u₁ = p⁻¹ * (p * c.u₁ * p⁻¹) * p := by group
    rw [this, hab]
    exact hpuc'
  · right
    exact hab

theorem diag_comm_u₁ {p : G} (hp : p ∈ c.P) :
    (p * (t * p * t)) * c.u₁ * (p * (t * p * t))⁻¹ = c.u₁ := by
  have hpu : p * c.u = c.u * p := mem_centralizer_singleton_iff.1 hp
  have hpuc : p * c.u * p⁻¹ = c.u := by rw [hpu]; group
  have hq : (t * p * t)⁻¹ = t * p⁻¹ * t := by
    simp only [mul_inv_rev, c.t_inv, mul_assoc]
  have key : ∀ w : G, p * c.u₁ * p⁻¹ = w →
      (t * p * t) * c.u₁ * (t * p * t)⁻¹ = c.u * (t * w * t) := by
    intro w hw
    have e2 : p * (c.u * c.u₁) * p⁻¹ = c.u * w := by
      rw [← hw]
      calc p * (c.u * c.u₁) * p⁻¹ = (p * c.u * p⁻¹) * (p * c.u₁ * p⁻¹) := by group
        _ = c.u * (p * c.u₁ * p⁻¹) := by rw [hpuc]
    rw [hq]
    calc t * p * t * c.u₁ * (t * p⁻¹ * t)
        = t * (p * (t * c.u₁ * t) * p⁻¹) * t := by group
      _ = t * (p * (c.u * c.u₁) * p⁻¹) * t := by rw [c.tu₁t]
      _ = t * (c.u * w) * t := by rw [e2]
      _ = (t * c.u * t) * (t * w * t) := c.pair.t_mul_mul_t c.u w
      _ = c.u * (t * w * t) := by rw [c.tut]
  have hg : (p * (t * p * t))⁻¹ = (t * p * t)⁻¹ * p⁻¹ := mul_inv_rev _ _
  rw [hg]
  have e : p * (t * p * t) * c.u₁ * ((t * p * t)⁻¹ * p⁻¹) =
      p * ((t * p * t) * c.u₁ * (t * p * t)⁻¹) * p⁻¹ := by group
  rw [e]
  have e0 : c.u * (c.u * c.u₁) = c.u₁ := by rw [← mul_assoc, c.u_sq, one_mul]
  rcases c.conj_u₁_cases hp with hw | hw
  · rw [key _ hw, c.tu₁t, e0]
    exact hw
  · rw [key _ hw, c.pair.t_mul_mul_t c.u c.u₁, c.tut, c.tu₁t]
    have e1 : c.u * (c.u * (c.u * c.u₁)) = c.u * c.u₁ := by
      rw [← mul_assoc c.u c.u, c.u_sq, one_mul]
    rw [e1]
    calc p * (c.u * c.u₁) * p⁻¹ = (p * c.u * p⁻¹) * (p * c.u₁ * p⁻¹) := by group
      _ = c.u * (c.u * c.u₁) := by rw [hpuc, hw]
      _ = c.u₁ := e0

structure NormZ (g : G) : Prop where
  fwd : ∀ z ∈ c.Zc, g * z * g⁻¹ ∈ c.Zc
  bwd : ∀ z ∈ c.Zc, g⁻¹ * z * g ∈ c.Zc

omit c in
theorem NormZ.inv {g : G} {c : S14Cfg G t} (h : c.NormZ g) : c.NormZ g⁻¹ :=
  ⟨fun z hz => by simpa using h.bwd z hz, fun z hz => by simpa using h.fwd z hz⟩

theorem conj_mem_Jc {g : G} (h : c.NormZ g) {j : G} (hj : j ∈ c.Jc) : g * j * g⁻¹ ∈ c.Jc := by
  rw [mem_centralizer_iff]
  intro z hz
  have h1 := mem_centralizer_iff.1 hj (g⁻¹ * z * g) (h.bwd z hz)
  calc z * (g * j * g⁻¹) = g * ((g⁻¹ * z * g) * j) * g⁻¹ := by group
    _ = g * (j * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
    _ = g * j * g⁻¹ * z := by group

@[expose] def Jaut {g : G} (h : c.NormZ g) : ↥c.Jc ≃* ↥c.Jc where
  toFun j := ⟨g * j * g⁻¹, c.conj_mem_Jc h j.2⟩
  invFun j := ⟨g⁻¹ * j * g, by simpa using c.conj_mem_Jc h.inv j.2⟩
  left_inv j := by apply Subtype.ext; simp [mul_assoc]
  right_inv j := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

theorem map_Jaut {g : G} (h : c.NormZ g) :
    (c.Zc.subgroupOf c.Jc).map (c.Jaut h).toMonoidHom = c.Zc.subgroupOf c.Jc := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact h.fwd _ hj
  · intro hy
    refine ⟨(c.Jaut h).symm y, ?_, (c.Jaut h).apply_symm_apply y⟩
    exact h.bwd _ hy

@[expose] def Yaut {g : G} (h : c.NormZ g) : c.Yq ≃* c.Yq :=
  QuotientGroup.congr (c.Zc.subgroupOf c.Jc) (c.Zc.subgroupOf c.Jc) (c.Jaut h) (c.map_Jaut h)

theorem Yaut_mkY {g : G} (h : c.NormZ g) (j : ↥c.Jc) : c.Yaut h (c.mkY j) = c.mkY (c.Jaut h j) :=
  rfl

theorem Zc_conj_mem {g : G} (hX : ∀ a ∈ c.X, g * a * g⁻¹ ∈ c.X) (hu : g * c.u₁ * g⁻¹ = c.u₁) :
    ∀ z ∈ c.Zc, g * z * g⁻¹ ∈ c.Zc := by
  intro z hz
  obtain ⟨a, ha, w, hw, rfl⟩ := c.mem_Zc_iff.1 hz
  obtain ⟨k, hk⟩ := hw
  have hk' : w = c.u₁ ^ k := hk.symm
  subst hk'
  have hk2 : g * c.u₁ ^ k * g⁻¹ = c.u₁ ^ k := by rw [← conj_zpow, hu]
  have e : g * (a * c.u₁ ^ k) * g⁻¹ = (g * a * g⁻¹) * c.u₁ ^ k := by
    calc g * (a * c.u₁ ^ k) * g⁻¹ = (g * a * g⁻¹) * (g * c.u₁ ^ k * g⁻¹) := by group
      _ = (g * a * g⁻¹) * c.u₁ ^ k := by rw [hk2]
  rw [e]
  exact mul_mem (mem_sup_left (hX a ha)) (mem_sup_right (zpow_mem (mem_zpowers _) _))

theorem exists_conj_normalizing (hA : AutFacts ↥c.L₁) {b : G} (hb : b ∈ c.Xt) (hb1 : b ≠ 1) :
    ∃ g : G, c.NormZ g ∧ g * c.xt * g⁻¹ = b := by
  obtain ⟨b₀, hb₀, rfl⟩ := c.exists_conj_of_mem_Xt hb
  have hb01 : b₀ ≠ 1 := by
    rintro rfl
    apply hb1
    simp
  have hb03 := c.orderOf_eq_three_of_mem_X hb₀ hb01
  obtain ⟨β, hβ⟩ := hA.1 ⟨c.x, c.x_mem⟩ ⟨b₀, c.X_le_L₁ hb₀⟩
    (by rw [orderOf_mk_subgroup c.x_mem]; exact c.x_ord)
    (by rw [orderOf_mk_subgroup (c.X_le_L₁ hb₀)]; exact hb03)
  obtain ⟨p₁, hp₁⟩ := c.exists_pair_rho_eq β 1
  let tP : ↥c.P := ⟨t, c.t_mem_P⟩
  let p₂ : ↥c.P := tP * p₁ * tP
  have hρt : c.pair.rho tP = tau := c.pair.rho_t
  have hp₂ : c.pair.rho p₂ = base 1 β := by
    rw [map_mul, map_mul, hρt, hp₁, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
  let g : ↥c.P := p₁ * p₂
  have hg : c.pair.rho g = base β β := by
    rw [map_mul, hp₁, hp₂, base_mul_base, mul_one, one_mul]
  have hgG : (g : G) = (p₁ : G) * (t * (p₁ : G) * t) := rfl
  have hn : (g : G) ∈ normalizer (c.L₁ : Set G) := by
    rw [mem_normalizer_iff_map_eq, ← c.pair.rho_mem_baseSubgroup_iff g, hg,
      mem_baseSubgroup_iff, swapChar_base]
  have hr := c.pair.rho_of_normalizes g hn
  rw [hg, base_injective] at hr
  have h1 : (g : G) * c.x * (g : G)⁻¹ = b₀ := by
    have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.1
    simp only [hβ, conjAutOf_apply] at this
    exact this.symm
  have h2 : (t * (g : G) * t) * c.x * (t * (g : G) * t)⁻¹ = b₀ := by
    have := congrArg (fun f : MulAut ↥c.L₁ => ((f ⟨c.x, c.x_mem⟩ : ↥c.L₁) : G)) hr.2
    simp only [hβ, conjAutOf_apply] at this
    exact this.symm
  have hgu₁ : (g : G) * c.u₁ * (g : G)⁻¹ = c.u₁ := by
    rw [hgG]
    exact c.diag_comm_u₁ p₁.2
  have hXinv : ∀ a ∈ c.X, (g : G)⁻¹ * a * (g : G) ∈ c.X := by
    intro a ha
    have hL : (g : G)⁻¹ * a * (g : G) ∈ c.L₁ := by
      have := (mem_normalizer_iff.1 (inv_mem hn) a).1 (c.X_le_L₁ ha)
      simpa using this
    have hcomm : (g : G)⁻¹ * a * (g : G) * c.x = c.x * ((g : G)⁻¹ * a * (g : G)) := by
      have hab := c.X_comm a ha b₀ hb₀
      have hx : c.x = (g : G)⁻¹ * b₀ * (g : G) := by
        rw [← h1]; group
      calc (g : G)⁻¹ * a * (g : G) * c.x = (g : G)⁻¹ * (a * b₀) * (g : G) := by
            rw [hx]; group
        _ = (g : G)⁻¹ * (b₀ * a) * (g : G) := by rw [hab]
        _ = c.x * ((g : G)⁻¹ * a * (g : G)) := by rw [hx]; group
    have hcube : ((g : G)⁻¹ * a * (g : G)) ^ 3 = 1 := by
      have := c.X_cube a ha
      have e : ((g : G)⁻¹ * a * (g : G)) ^ 3 = (g : G)⁻¹ * a ^ 3 * (g : G) := by
        have := conj_pow (a := (g : G)⁻¹) (b := a) (i := 3)
        simpa using this
      rw [e, this]; group
    by_cases h1' : (g : G)⁻¹ * a * (g : G) = 1
    · rw [h1']; exact one_mem _
    · exact c.X_three _ ⟨hL, mem_centralizer_singleton_iff.2 hcomm⟩
        (orderOf_eq_prime hcube h1')
  have hle : conjSub (g : G)⁻¹ c.X ≤ c.X := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := mem_conjSub.1 hy
    rw [inv_inv]
    exact hXinv a ha
  have heq : conjSub (g : G)⁻¹ c.X = c.X :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)⁻¹).injective])
  have hXfwd : ∀ a ∈ c.X, (g : G) * a * (g : G)⁻¹ ∈ c.X := by
    intro a ha
    rw [← heq] at ha
    obtain ⟨a', ha', rfl⟩ := mem_conjSub.1 ha
    have : (g : G) * ((g : G)⁻¹ * a' * (g : G)⁻¹⁻¹) * (g : G)⁻¹ = a' := by group
    rw [this]
    exact ha'
  have hXbwd : ∀ a ∈ c.X, (g : G)⁻¹ * a * (g : G)⁻¹⁻¹ ∈ c.X := by
    intro a ha
    simpa using hXinv a ha
  have hu' : (g : G)⁻¹ * c.u₁ * (g : G)⁻¹⁻¹ = c.u₁ := by
    rw [inv_inv]
    have e : c.u₁ = (g : G)⁻¹ * ((g : G) * c.u₁ * (g : G)⁻¹) * (g : G) := by group
    rw [hgu₁] at e
    exact e.symm
  refine ⟨(g : G), ⟨c.Zc_conj_mem hXfwd hgu₁, fun z hz => ?_⟩, ?_⟩
  · simpa using c.Zc_conj_mem hXbwd hu' z hz
  · have htg : t * (t * (g : G) * t) = (g : G) * t := by
      calc t * (t * (g : G) * t) = (t * t) * (g : G) * t := by group
        _ = (g : G) * t := by rw [c.t_sq, one_mul]
    calc (g : G) * (t * c.x * t⁻¹) * (g : G)⁻¹
        = ((g : G) * t) * c.x * ((g : G) * t)⁻¹ := by group
      _ = (t * (t * (g : G) * t)) * c.x * (t * (t * (g : G) * t))⁻¹ := by rw [htg]
      _ = t * ((t * (g : G) * t) * c.x * (t * (g : G) * t)⁻¹) * t⁻¹ := by group
      _ = t * b₀ * t⁻¹ := by rw [h2]

theorem Xt_comm {a b : G} (ha : a ∈ c.Xt) (hb : b ∈ c.Xt) : a * b = b * a := by
  obtain ⟨a₀, ha₀, rfl⟩ := c.exists_conj_of_mem_Xt ha
  obtain ⟨b₀, hb₀, rfl⟩ := c.exists_conj_of_mem_Xt hb
  calc t * a₀ * t⁻¹ * (t * b₀ * t⁻¹) = t * (a₀ * b₀) * t⁻¹ := by group
    _ = t * (b₀ * a₀) * t⁻¹ := by rw [c.X_comm a₀ ha₀ b₀ hb₀]
    _ = _ := by group

@[expose] def Pbar : Subgroup c.Yq := (c.Xt.subgroupOf c.Jc).map c.mkY

theorem mem_Pbar_iff {y : c.Yq} :
    y ∈ c.Pbar ↔ ∃ b ∈ c.Xt, ∃ hb : b ∈ c.Jc, c.mkY ⟨b, hb⟩ = y := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, g.2, rfl⟩
  · rintro ⟨b, hb, hbJ, rfl⟩
    exact ⟨⟨b, hbJ⟩, hb, rfl⟩

theorem Pbar_comm : ∀ a ∈ c.Pbar, ∀ b ∈ c.Pbar, a * b = b * a := by
  intro a ha b hb
  obtain ⟨a₀, ha₀, haJ, rfl⟩ := c.mem_Pbar_iff.1 ha
  obtain ⟨b₀, hb₀, hbJ, rfl⟩ := c.mem_Pbar_iff.1 hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (c.Xt_comm ha₀ hb₀)

theorem Pbar_cube : ∀ a ∈ c.Pbar, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨a₀, ha₀, haJ, rfl⟩ := c.mem_Pbar_iff.1 ha
  rw [← map_pow, ← map_one c.mkY]
  congr 1
  exact Subtype.ext (c.Xt_cube ha₀)

theorem card_Pbar : Nat.card c.Pbar = 9 := by
  let φ : ↥(c.Xt.subgroupOf c.Jc) →* c.Yq := c.mkY.comp (c.Xt.subgroupOf c.Jc).subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, hg⟩ h
    have h1 : c.mkY g = 1 := h
    have h2 := (c.mkY_eq_one_iff g).1 h1
    rw [Subgroup.mem_subgroupOf] at hg
    exact Subtype.ext (Subtype.ext (c.eq_one_of_mem_Zc_Xt h2 hg))
  have hr : φ.range = c.Pbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [← hr, ← h]
  exact (Nat.card_congr (subgroupOfEquivOfLe c.Xt_le_J).toEquiv).trans c.card_Xt

theorem centralizer_equiv_of_mem_Pbar (hA : AutFacts ↥c.L₁) {y : c.Yq}
    (hy : y ∈ c.Pbar) (hy1 : y ≠ 1) :
    Nonempty (↥(centralizer ({y} : Set c.Yq)) ≃*
      Multiplicative (ZMod 3) × Equiv.Perm (Fin 5)) := by
  obtain ⟨b, hb, hbJ, rfl⟩ := c.mem_Pbar_iff.1 hy
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hy1 (map_one c.mkY)
  obtain ⟨g, hN, hg⟩ := c.exists_conj_normalizing hA hb hb1
  have e : c.mkY ⟨b, hbJ⟩ = c.Yaut hN c.xbar := by
    rw [xbar, Yaut_mkY]
    congr 1
    exact Subtype.ext hg.symm
  rw [e]
  obtain ⟨e1⟩ := centralizer_equiv_of_equiv (c.Yaut hN) c.xbar
  obtain ⟨e2⟩ := c.centralizer_xbar_equiv hA
  exact ⟨e1.trans e2⟩

theorem eq_bot_of_normal (hA : AutFacts ↥c.L₁) (A : Subgroup c.Yq)
    (hA' : A.Normal) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : A = ⊥ := by
  refine eq_bot_of_normal_of_commute c.Pbar c.Pbar_comm c.Pbar_cube c.card_Pbar ?_ A hA' hAab
  intro a ha ha1 Q hQ hQn hQab
  obtain ⟨e⟩ := c.centralizer_equiv_of_mem_Pbar hA ha ha1
  exact le_zpowers_of_centralizer_equiv ha1 (c.Pbar_cube a ha) e Q hQ hQn hQab

end S14Cfg

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
