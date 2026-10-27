module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Seven
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Defs
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalD1

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaS₄ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₄ d t ⊓ centralizer (yamadaV₁ d t : Set G)

@[expose] noncomputable def yamadaL₄ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₄ d t ⊓ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G)

@[expose] noncomputable def yamadaM₄ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₄ d t ⊓ centralizer (yamadaY₂ d t : Set G)

@[expose] noncomputable def yamadaD₄ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₄ d t ⊓ yamadaD₅ d t

end Defs

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem exists_mem_J₀_x₃ :
    ∃ j ∈ d.J₀, ∃ ν : d.Γ, ν ≠ 1 ∧ ∀ a, j * d.x₃ a * j⁻¹ = d.x₃ (ν * a) := by
  obtain ⟨j, hj, hj1⟩ : ∃ j ∈ d.J₀, j ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : d.J₀ = ⊥ := eq_bot_iff.2 fun j hj => (mem_bot).2 (hcon j hj)
    have hc := d.yamada_three_five_four.2
    rw [hbot, Subgroup.card_bot] at hc
    have := d.two_le_q
    nlinarith
  have hj' := hj
  rw [d.J₀_eq_map] at hj'
  obtain ⟨m, -, hm⟩ := hj'
  refine ⟨j, hj, (m : d.Γ), fun hν => hj1 ?_, fun a => ?_⟩
  · rw [← hm, show m = 1 from Units.ext hν, map_one]
  · rw [← hm, MonoidHom.comp_apply, MonoidHom.inr_apply, d.torus_x₃]
    simp

theorem exists_commutatorElement_eq_x₃ {j : X} {ν : d.Γ} (hν : ν ≠ 1)
    (hj : ∀ a, j * d.x₃ a * j⁻¹ = d.x₃ (ν * a)) (b : d.Γ) :
    ∃ a, j * d.x₃ a * j⁻¹ * (d.x₃ a)⁻¹ = d.x₃ b := by
  have hν1 : ν + 1 ≠ 0 := fun h4 =>
    hν ((eq_neg_of_add_eq_zero_left h4).trans (CharTwo.neg_eq 1))
  refine ⟨(ν + 1)⁻¹ * b, ?_⟩
  rw [hj, d.x₃_inv, ← d.x₃_add]
  congr 1
  calc ν * ((ν + 1)⁻¹ * b) + (ν + 1)⁻¹ * b = (ν + 1) * (ν + 1)⁻¹ * b := by ring
    _ = b := by rw [mul_inv_cancel₀ hν1, one_mul]

end TrialityD4Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Generic

omit [Finite G] in
theorem commutatorElement_mem_centralizer_C8 {K : Subgroup G} {j x : G}
    (hj : j ∈ centralizer (K : Set G)) (hx : x ∈ normalizer (K : Set G)) :
    j * x * j⁻¹ * x⁻¹ ∈ centralizer (K : Set G) := by
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : x⁻¹ * y * x ∈ K := by
    have := (mem_normalizer_iff.1 (inv_mem hx) y).1 hy
    rwa [inv_inv] at this
  have h1 : y * j = j * y := mem_centralizer_iff.1 hj y hy
  have h2 : (x⁻¹ * y * x) * j = j * (x⁻¹ * y * x) := mem_centralizer_iff.1 hj _ hy'
  have h3 : (x⁻¹ * y * x) * j⁻¹ = j⁻¹ * (x⁻¹ * y * x) := by
    calc (x⁻¹ * y * x) * j⁻¹ = j⁻¹ * (j * (x⁻¹ * y * x)) * j⁻¹ := by group
      _ = j⁻¹ * ((x⁻¹ * y * x) * j) * j⁻¹ := by rw [h2]
      _ = j⁻¹ * (x⁻¹ * y * x) := by group
  calc y * (j * x * j⁻¹ * x⁻¹) = (y * j) * x * j⁻¹ * x⁻¹ := by group
    _ = (j * y) * x * j⁻¹ * x⁻¹ := by rw [h1]
    _ = j * x * ((x⁻¹ * y * x) * j⁻¹) * x⁻¹ := by group
    _ = j * x * (j⁻¹ * (x⁻¹ * y * x)) * x⁻¹ := by rw [h3]
    _ = j * x * j⁻¹ * x⁻¹ * y := by group

theorem mem_normalizer_centralizer_C8 {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) : g ∈ normalizer (centralizer (K : Set G) : Set G) := by
  refine mem_normalizer_fintype fun c hc => ?_
  rw [SetLike.mem_coe, mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ K := by
    have := (mem_normalizer_iff.1 (inv_mem hg) y).1 hy
    rwa [inv_inv] at this
  have := hc _ hy'
  calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * y := by group

omit [Finite G] in
theorem commutator_sup_le_C8 {N K : Subgroup G} (hK : K ≤ normalizer (N : Set G))
    (hKK : ⁅K, K⁆ ≤ N) : ⁅N ⊔ K, N ⊔ K⁆ ≤ N := by
  rw [commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left N K hK, Set.mem_mul] at hx hy
  obtain ⟨n, hn, k, hk, rfl⟩ := hx
  obtain ⟨n', hn', k', hk', rfl⟩ := hy
  have h1 : k * n' * k⁻¹ ∈ N := (mem_normalizer_iff.1 (hK hk) n').1 hn'
  have h2 : k * k' * k⁻¹ * k'⁻¹ ∈ N := hKK (commutator_mem_commutator hk hk')
  have h3 : k' * n⁻¹ * k'⁻¹ ∈ N := (mem_normalizer_iff.1 (hK hk') _).1 (inv_mem hn)
  rw [commutatorElement_def, show n * k * (n' * k') * (n * k)⁻¹ * (n' * k')⁻¹ =
    n * (k * n' * k⁻¹) * (k * k' * k⁻¹ * k'⁻¹) * (k' * n⁻¹ * k'⁻¹) * n'⁻¹ by group]
  exact mul_mem (mul_mem (mul_mem (mul_mem hn h1) h2) h3) (inv_mem hn')

omit [Finite G] in
theorem normalizer_le_normalizer_commutator_C8 (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  have hmap : (⁅(⊤ : Subgroup H), ⊤⁆ : Subgroup H).map H.subtype = ⁅H, H⁆ := by
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rw [← hmap]
  exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

end Generic

section Main

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hNH : NormalizerHyp d t)
  (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
  (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t)
  (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
  (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype)
  (h593 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t)
  (h5101 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype = yamadaY₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t)
  (h5102 : CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t)
  (h59e : yamadaY₂ d t = jZeroLayer d ⊓ yamadaL₂ d t)
  (h520 : yamadaC₅ d t = yamadaD₅ d t ⊔ zpowers t ∧ t ∉ yamadaD₅ d t ∧
    yamadaD₅ d t = yamadaD₃ d t ⊔ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ∧
    yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
      yamadaD₁ d t ∧
    yamadaL₃ d t = yamadaM₃ d t ⊔ zpowers t ∧ t ∉ yamadaM₃ d t ∧
    yamadaR₃ d t = yamadaS₃ d t ⊔ zpowers t ∧ t ∉ yamadaS₃ d t)
  (h5221 : ((yamadaF₃ d t ⊔ zpowers t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
    ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
    ⁅yamadaR₃ d t, yamadaR₃ d t⁆ = yamadaF₂ d t)

include h h562 h592 in
theorem yamadaY₁_inf_centralizer_C8 :
    yamadaY₁ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype := by
  have hYc := mul_comm_of_isMulCommutative_D4 h592.2.2.1
  have hVN : yamadaV₁ d t ≤ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_fintype fun y hy => by
      rw [SetLike.mem_coe, hYc v (le_sup_left (a := yamadaV₁ d t) hv) y (Y_le_yamadaY₂ d h592 hy),
        mul_inv_cancel_right]
      exact hy
  refine le_antisymm (fun x hx => ?_)
    (le_inf le_sup_left ((map_subtype_le _).trans h.L_le_centralizer))
  obtain ⟨hxY, hxC⟩ := mem_inf.1 hx
  rw [show yamadaY₁ d t = d.Y.map L.subtype ⊔ yamadaV₁ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hVN, Set.mem_mul] at hxY
  obtain ⟨y, hy, v, hv, rfl⟩ := hxY
  have hyC : y ∈ centralizer ({t} : Set G) := h.L_le_centralizer (map_subtype_le _ hy)
  have hvC : v ∈ centralizer ({t} : Set G) := by
    have := mul_mem (inv_mem hyC) hxC
    rwa [inv_mul_cancel_left] at this
  have hvV : v ∈ d.V.map L.subtype := by
    rw [← h562.2.2.1]
    exact mem_inf.2 ⟨hv, hvC⟩
  exact mul_mem hy (map_mono d.V_le_Y hvV)

include h h561 h562 h592 h593 in
theorem yamadaF₁_le_centralizer_yamadaY₁ :
    yamadaF₁ d t ≤ centralizer (yamadaY₁ d t : Set G) := by
  have hYc := mul_comm_of_isMulCommutative_D4 h592.2.2.1
  have hV₁Y₂ : yamadaV₁ d t ≤ yamadaY₂ d t := le_sup_left
  have hYY₂ : d.Y.map L.subtype ≤ yamadaY₂ d t := Y_le_yamadaY₂ d h592
  rw [h.yamadaF₁_eq_sup d h561 h562]
  refine sup_le ?_ ?_
  · refine le_centralizer_iff.1 (sup_le ?_ ?_)
    · rintro _ ⟨y, hy, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      exact congrArg Subtype.val
        (mem_centralizer_iff.1 (d.M_le_centralizer_Y (d.F_le_M ha)) y hy).symm
    · intro v hv
      rw [mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      exact mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨a, d.F_le_S ha, rfl⟩ hv
  · intro v hv
    rw [mem_centralizer_iff]
    intro y hy
    refine hYc y ?_ v (hV₁Y₂ hv)
    exact sup_le hYY₂ hV₁Y₂ hy

include h hNH h561 h562 h591 h592 h593 in
theorem crossed_mem_yamadaF₁ {x : G} (hx : x ∈ yamadaR₄ d t) :
    t * x * t * x⁻¹ ∈ yamadaF₁ d t := by
  obtain ⟨w, hw, e⟩ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.1.1 x hx
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, h.t_mul_t, one_mul]
  exact hw

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₄_le_normalizer_Y :
    yamadaR₄ d t ≤ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := fun x hx => by
  have hx5 : x ∈ yamadaR₅ d t := (mem_inf.1 hx).1
  have hxY₁ := h.yamadaR₅_le_normalizer_yamadaY₁ d hNH h561 h562 h591 h592 h593 hx5
  have hκ := h.crossed_mem_yamadaF₁ d hNH h561 h562 h591 h592 h593 hx
  have hFY := h.yamadaF₁_le_centralizer_yamadaY₁ d h561 h562 h592 h593
  refine mem_normalizer_fintype fun y hy => ?_
  have hyt : y * t = t * y := mem_centralizer_singleton_iff.1 (h.L_le_centralizer
    (map_subtype_le _ hy))
  have h1 : x * y * x⁻¹ ∈ yamadaY₁ d t :=
    (mem_normalizer_iff.1 hxY₁ y).1 (le_sup_left (a := d.Y.map L.subtype) hy)
  have hcomm : (t * x * t * x⁻¹) * (x * y * x⁻¹) = (x * y * x⁻¹) * (t * x * t * x⁻¹) :=
    (mem_centralizer_iff.1 (hFY hκ) _ h1).symm
  have h2 : (x * y * x⁻¹) * t = t * (x * y * x⁻¹) := by
    have e1 : (x * y * x⁻¹) * (x * t * x⁻¹) = (x * t * x⁻¹) * (x * y * x⁻¹) := by
      rw [show x * y * x⁻¹ * (x * t * x⁻¹) = x * (y * t) * x⁻¹ by group, hyt]
      group
    have e2 : x * t * x⁻¹ = t * (t * x * t * x⁻¹) := by
      rw [show t * (t * x * t * x⁻¹) = (t * t) * x * t * x⁻¹ by group, h.t_mul_t, one_mul]
    rw [e2] at e1
    have e3 : (x * y * x⁻¹) * t * (t * x * t * x⁻¹) = t * (x * y * x⁻¹) * (t * x * t * x⁻¹) := by
      calc (x * y * x⁻¹) * t * (t * x * t * x⁻¹)
          = (x * y * x⁻¹) * (t * (t * x * t * x⁻¹)) := by group
        _ = t * (t * x * t * x⁻¹) * (x * y * x⁻¹) := e1
        _ = t * ((t * x * t * x⁻¹) * (x * y * x⁻¹)) := by group
        _ = t * ((x * y * x⁻¹) * (t * x * t * x⁻¹)) := by rw [hcomm]
        _ = t * (x * y * x⁻¹) * (t * x * t * x⁻¹) := by group
    exact mul_right_cancel e3
  rw [SetLike.mem_coe, ← h.yamadaY₁_inf_centralizer_C8 d h562 h592]
  exact mem_inf.2 ⟨h1, mem_centralizer_singleton_iff.2 h2⟩

include h hNH h561 h562 h591 h592 h593 in
theorem crossed_mul_mem_yamadaW₁ {x y : G} (hx : x ∈ yamadaR₅ d t)
    (hy : t * y * t * y⁻¹ ∈ yamadaF₁ d t) :
    ∃ w ∈ yamadaW₁ d t, t * (x * y) * t * (x * y)⁻¹ =
      (t * x * t * x⁻¹) * (t * y * t * y⁻¹) * w := by
  rw [crossed_mul_D4 h.t_mul_t x y]
  generalize t * y * t * y⁻¹ = b at hy ⊢
  have hc := h.commutatorElement_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 (inv_mem hy) hx
  rw [inv_inv] at hc
  exact ⟨b⁻¹ * x * b * x⁻¹, hc, by group⟩

include h hNH h561 h562 h591 h592 h593 in
theorem crossed_inv_mem_yamadaW₁ {x : G} (hx : x ∈ yamadaR₅ d t)
    (hκ : t * x * t * x⁻¹ ∈ yamadaF₁ d t) :
    ∃ w ∈ yamadaW₁ d t, t * x⁻¹ * t * x⁻¹⁻¹ = (t * x * t * x⁻¹)⁻¹ * w := by
  rw [crossed_inv_D4 h.t_mul_t x]
  generalize t * x * t * x⁻¹ = b at hκ ⊢
  have hc := h.commutatorElement_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 hκ (inv_mem hx)
  exact ⟨b * x⁻¹ * b⁻¹ * x⁻¹⁻¹, hc, by group⟩

include h hNH h561 h562 h591 h592 h593 in
theorem mem_yamadaR₃_iff_of_mem_yamadaR₄ {x : G} (hx : x ∈ yamadaR₄ d t) :
    x ∈ yamadaR₃ d t ↔ t * x * t * x⁻¹ ∈ yamadaW₁ d t :=
  (h.mem_inf_normalizer_iff d hNH h561 h562 (yamadaW₁_le_yamadaD₁ d)
    (h.yamadaR₅_le_normalizer_yamadaW₁ d hNH h561 h562 h591 h592 h593) (x := x)).trans
    ⟨fun h1 => h1.2, fun h1 => ⟨(mem_inf.1 hx).1, h1⟩⟩

omit [Finite G] in
include h59e in
theorem yamadaY₂_le_centralizer_J₀ :
    yamadaY₂ d t ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  rw [h59e]
  exact inf_le_left.trans (map_subtype_le _)

include h h561 h562 h59e in
theorem J₀_map_le_normalizer_yamadaR₄ :
    d.J₀.map L.subtype ≤ normalizer (yamadaR₄ d t : Set G) := by
  intro j hj
  have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (h.J₀_map_le_centralizer d hj)
  have hjR₅ : j ∈ normalizer (yamadaR₅ d t : Set G) := Common.mem_normalizer_sup
    (le_normalizer_yamadaC₅ d t (h.J₀_map_le_normalizer_yamadaC₁ d hj))
    (J₀_map_le_normalizer_S d hj)
  have hjV₁ : j ∈ normalizer (yamadaV₁ d t : Set G) := by
    refine mem_normalizer_fintype fun v hv => ?_
    have hvJ := yamadaY₂_le_centralizer_J₀ d h59e (le_sup_left (a := yamadaV₁ d t) hv)
    rw [SetLike.mem_coe, mem_centralizer_iff.1 hvJ j hj, mul_inv_cancel_right]
    exact hv
  have hjF₁ : j ∈ normalizer (yamadaF₁ d t : Set G) := by
    rw [h.yamadaF₁_eq_sup d h561 h562]
    exact Common.mem_normalizer_sup
      (map_le_normalizer_map (d.J₀_le_J.trans d.J_le_normalizer_F) hj) hjV₁
  exact Common.mem_normalizer_inf hjR₅
    (le_normalizer (Common.mem_normalizer_sup hjF₁ (mem_normalizer_zpowers_of_comm_D4 hjt)))

include h hNH h561 h562 h591 h592 h593 h59e in
theorem exists_mem_yamadaR₃_mul_commutator {x : G} (hx : x ∈ yamadaR₄ d t) :
    ∃ j ∈ d.J₀.map L.subtype, ∃ x' ∈ yamadaR₄ d t,
      x * (j * x' * j⁻¹ * x'⁻¹)⁻¹ ∈ yamadaR₃ d t := by
  have hF₁ := h.yamadaF₁_eq_sup d h561 h562
  have hR₄5 : ∀ {y : G}, y ∈ yamadaR₄ d t → y ∈ yamadaR₅ d t := fun hy => (mem_inf.1 hy).1
  have hR₅W₁ := h.yamadaR₅_le_normalizer_yamadaW₁ d hNH h561 h562 h591 h592 h593
  have hκF := fun {y : G} (hy : y ∈ yamadaR₄ d t) =>
    h.crossed_mem_yamadaF₁ d hNH h561 h562 h591 h592 h593 hy
  obtain ⟨j₀, hj₀, ν, hν, hjx⟩ := d.exists_mem_J₀_x₃
  have hjJ : (j₀ : G) ∈ d.J₀.map L.subtype := ⟨j₀, hj₀, rfl⟩
  have hjt : (j₀ : G) * t = t * j₀ :=
    mem_centralizer_singleton_iff.1 (h.J₀_map_le_centralizer d hjJ)
  have hjt' : (j₀ : G)⁻¹ * t * j₀ = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  have hVF : yamadaV₁ d t ≤ normalizer ((d.F.map L.subtype : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_fintype fun a ha => by
      obtain ⟨a', ha', rfl⟩ := ha
      rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨a', d.F_le_S ha', rfl⟩ hv,
        mul_inv_cancel_right]
      exact ⟨a', ha', rfl⟩
  have hκx := hκF hx
  rw [hF₁, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hVF, Set.mem_mul] at hκx
  obtain ⟨_, ⟨f₀, hf₀, rfl⟩, v, hv, hfv⟩ := hκx
  obtain ⟨b, n, hn, rfl⟩ := d.mem_F_iff.1 hf₀
  obtain ⟨a, ha⟩ := d.exists_commutatorElement_eq_x₃ hν hjx b
  have ha' : (j₀ : G) * (d.x₃ a : G) * (j₀ : G)⁻¹ * ((d.x₃ a : L) : G)⁻¹ = (d.x₃ b : G) :=
    congrArg Subtype.val ha
  have hx₃a : ((d.x₃ a : L) : G) ∈ yamadaF₁ d t := by
    rw [hF₁]
    exact mem_sup_left ⟨_, d.x₃_mem_F a, rfl⟩
  obtain ⟨x', hx', v', hv', e'⟩ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.1.2 _ hx₃a
  have hκx' : t * x' * t * x'⁻¹ = (d.x₃ a : G) * v' := by
    rw [show t * x' * t * x'⁻¹ = t * (x' * t * x'⁻¹) by group, e', ← mul_assoc, ← mul_assoc,
      h.t_mul_t, one_mul]
  have hjv' : (j₀ : G) * v' * (j₀ : G)⁻¹ = v' := by
    have hvJ := yamadaY₂_le_centralizer_J₀ d h59e (le_sup_left (a := yamadaV₁ d t) hv')
    rw [mem_centralizer_iff.1 hvJ _ hjJ, mul_inv_cancel_right]
  refine ⟨j₀, hjJ, x', hx', ?_⟩
  have hjx'R₄ : (j₀ : G) * x' * (j₀ : G)⁻¹ ∈ yamadaR₄ d t :=
    (mem_normalizer_iff.1 (h.J₀_map_le_normalizer_yamadaR₄ d h561 h562 h59e hjJ) x').1 hx'
  have hcR₄ : (j₀ : G) * x' * (j₀ : G)⁻¹ * x'⁻¹ ∈ yamadaR₄ d t := mul_mem hjx'R₄ (inv_mem hx')
  have hκj : t * ((j₀ : G) * x' * (j₀ : G)⁻¹) * t * ((j₀ : G) * x' * (j₀ : G)⁻¹)⁻¹ =
      (j₀ : G) * (t * x' * t * x'⁻¹) * (j₀ : G)⁻¹ := by
    calc t * ((j₀ : G) * x' * (j₀ : G)⁻¹) * t * ((j₀ : G) * x' * (j₀ : G)⁻¹)⁻¹ =
          t * j₀ * x' * ((j₀ : G)⁻¹ * t * j₀) * x'⁻¹ * (j₀ : G)⁻¹ := by group
      _ = j₀ * t * x' * t * x'⁻¹ * (j₀ : G)⁻¹ := by rw [hjt', ← hjt]
      _ = (j₀ : G) * (t * x' * t * x'⁻¹) * (j₀ : G)⁻¹ := by group
  obtain ⟨w₁, hw₁, e₁⟩ := h.crossed_mul_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593
    (hR₄5 hjx'R₄) (hκF (inv_mem hx'))
  obtain ⟨w₂, hw₂, e₂⟩ := h.crossed_inv_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593
    (hR₄5 hx') (hκF hx')
  have hκc : t * ((j₀ : G) * x' * (j₀ : G)⁻¹ * x'⁻¹) * t *
      ((j₀ : G) * x' * (j₀ : G)⁻¹ * x'⁻¹)⁻¹ = (d.x₃ b : G) * (w₂ * w₁) := by
    rw [e₁, hκj, e₂, hκx', ← ha']
    calc (j₀ : G) * ((d.x₃ a : G) * v') * (j₀ : G)⁻¹ * (((d.x₃ a : G) * v')⁻¹ * w₂) * w₁ =
          (j₀ : G) * (d.x₃ a : G) * (j₀ : G)⁻¹ * ((d.x₃ a : L) : G)⁻¹ *
            ((d.x₃ a : G) * ((j₀ : G) * v' * (j₀ : G)⁻¹) * v'⁻¹ * ((d.x₃ a : L) : G)⁻¹) *
            (w₂ * w₁) := by group
      _ = (j₀ : G) * (d.x₃ a : G) * (j₀ : G)⁻¹ * ((d.x₃ a : L) : G)⁻¹ * (w₂ * w₁) := by
          rw [hjv', mul_inv_cancel_right, mul_inv_cancel, mul_one]
  generalize hcdef : (j₀ : G) * x' * (j₀ : G)⁻¹ * x'⁻¹ = c at hcR₄ hκc ⊢
  obtain ⟨w₃, hw₃, e₃⟩ := h.crossed_mul_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593
    (hR₄5 hx) (hκF (inv_mem hcR₄))
  obtain ⟨w₄, hw₄, e₄⟩ := h.crossed_inv_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593
    (hR₄5 hcR₄) (hκF hcR₄)
  refine (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593
    (mul_mem hx (inv_mem hcR₄))).2 ?_
  rw [e₃, e₄, hκc, ← hfv]
  have hnW : ((n : L) : G) ∈ yamadaW₁ d t := mem_sup_left ⟨n, hn, rfl⟩
  have hvW : v ∈ yamadaW₁ d t := mem_sup_right hv
  have hbN : ((d.x₃ b : L) : G) ∈ normalizer (yamadaW₁ d t : Set G) :=
    hR₅W₁ (mem_sup_right ⟨_, d.F_le_S (d.x₃_mem_F b), rfl⟩)
  have hin : ((n : L) : G) * v * (w₂ * w₁)⁻¹ ∈ yamadaW₁ d t :=
    mul_mem (mul_mem hnW hvW) (inv_mem (mul_mem hw₂ hw₁))
  have hconj := (mem_normalizer_iff.1 hbN _).1 hin
  have := mul_mem hconj (mul_mem hw₄ hw₃)
  rwa [show (d.x₃ b : G) * (((n : L) : G) * v * (w₂ * w₁)⁻¹) * ((d.x₃ b : L) : G)⁻¹ * (w₄ * w₃) =
    L.subtype (d.x₃ b * n) * v * (((d.x₃ b : G) * (w₂ * w₁))⁻¹ * w₄) * w₃ by
      rw [map_mul, Subgroup.coe_subtype]; group] at this

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₄_le_normalizer_yamadaL₄ :
    yamadaR₄ d t ≤ normalizer (yamadaL₄ d t : Set G) := fun _ hg =>
  Common.mem_normalizer_inf (le_normalizer hg)
    (mem_normalizer_centralizer_C8 (h.yamadaR₄_le_normalizer_Y d hNH h561 h562 h591 h592 h593 hg))

include h hNH h561 h562 h591 h592 h593 h59e in
theorem commutatorElement_mem_yamadaL₄ {j x : G} (hj : j ∈ d.J₀.map L.subtype)
    (hx : x ∈ yamadaR₄ d t) : j * x * j⁻¹ * x⁻¹ ∈ yamadaL₄ d t :=
  mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 (h.J₀_map_le_normalizer_yamadaR₄ d h561 h562 h59e hj)
    x).1 hx) (inv_mem hx), commutatorElement_mem_centralizer_C8 (J₀_map_le_centralizer_Y d hj)
      (h.yamadaR₄_le_normalizer_Y d hNH h561 h562 h591 h592 h593 hx)⟩

include h hNH h561 h562 h591 h592 h593 h59e in
theorem yamadaR₄_eq_sup : yamadaR₄ d t = yamadaR₃ d t ⊔ yamadaL₄ d t := by
  refine le_antisymm (fun x hx => ?_)
    (sup_le (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.1.1 inf_le_left)
  obtain ⟨j, hj, x', hx', hr⟩ := h.exists_mem_yamadaR₃_mul_commutator d hNH h561 h562 h591 h592
    h593 h59e hx
  have := mul_mem (mem_sup_left hr : _ ∈ yamadaR₃ d t ⊔ yamadaL₄ d t)
    (mem_sup_right (h.commutatorElement_mem_yamadaL₄ d hNH h561 h562 h591 h592 h593 h59e hj hx'))
  rwa [inv_mul_cancel_right] at this

include h h592 h520 in
theorem yamadaL₃_le_centralizer_Y :
    yamadaL₃ d t ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
  rw [h520.2.2.2.2.1]
  refine sup_le (fun x hx => centralizer_le (Y_le_yamadaY₂ d h592) (mem_inf.1 hx).2)
    ((zpowers_le).2 (mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hy))))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₃_le_yamadaR₃ : yamadaL₃ d t ≤ yamadaR₃ d t := by
  rw [(h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2]
  exact le_sup_left

include h in
theorem S_le_normalizer_yamadaL₃ :
    d.S.map L.subtype ≤ normalizer (yamadaL₃ d t : Set G) := fun _ hs =>
  LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_normalizer_yamadaL₂ d t
    (h.centralizer_inf_normalizer_Y_le d ⟨h.S_le_centralizer d hs,
      map_le_normalizer_map d.S_le_normalizer_Y hs⟩))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h520 in
theorem yamadaR₃_inf_yamadaL₄ : yamadaR₃ d t ⊓ yamadaL₄ d t = yamadaL₃ d t := by
  have hR₃eq := (h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2
  have hL₃Y := h.yamadaL₃_le_centralizer_Y d h592 h520
  have hL₃R₃ := h.yamadaL₃_le_yamadaR₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hR₃R₄ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.1.1
  refine le_antisymm (fun x hx => ?_) (le_inf hL₃R₃ (le_inf (hL₃R₃.trans hR₃R₄) hL₃Y))
  obtain ⟨hxR₃, hxL₄⟩ := mem_inf.1 hx
  have hxC := (mem_inf.1 hxL₄).2
  rw [hR₃eq, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    (h.S_le_normalizer_yamadaL₃ d), Set.mem_mul] at hxR₃
  obtain ⟨l, hl, s, hs, rfl⟩ := hxR₃
  have hsC : s ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    have := mul_mem (inv_mem (hL₃Y hl)) hxC
    rwa [inv_mul_cancel_left] at this
  obtain ⟨s', hs', rfl⟩ := hs
  have hs'M : s' ∈ d.M := by
    rw [← d.S_inf_centralizer_Y]
    refine mem_inf.2 ⟨hs', mem_centralizer_iff.2 fun y hy => ?_⟩
    exact Subtype.ext (mem_centralizer_iff.1 hsC (y : G) ⟨y, hy, rfl⟩)
  exact mul_mem hl (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
    ((le_sup_left.trans (h.tM_le_yamadaL₂ d)) ⟨s', hs'M, rfl⟩))

include h hNH h561 h562 h591 h592 h593 h5221 in
theorem yamadaR₄_le_normalizer_yamadaY₂ :
    yamadaR₄ d t ≤ normalizer (yamadaY₂ d t : Set G) := by
  intro x hx
  have h1 := normalizer_le_normalizer_commutator_C8 (yamadaR₃ d t)
    ((h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.1.2 hx)
  rw [h5221.2.2] at h1
  rw [← yamadaF₂_inf_centralizer d h592]
  exact Common.mem_normalizer_inf h1 (mem_normalizer_centralizer_C8 h1)

include h hNH h561 h562 h591 h592 h593 in
theorem t_mem_yamadaR₄ : t ∈ yamadaR₄ d t := by
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  exact h514.2.2.2.2.1.1 (h514.2.2.2.1.1 ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)
    (h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t)))))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 in
theorem yamadaL₄_eq_sup : yamadaL₄ d t = yamadaM₄ d t ⊔ zpowers t ∧ t ∉ yamadaM₄ d t := by
  have htR₄ := h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593
  have htY : t ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hy))
  have hR₄Y₂ := h.yamadaR₄_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5221
  have hL₃R₄ : yamadaL₃ d t ≤ yamadaR₄ d t :=
    (h.yamadaL₃_le_yamadaR₃ d hNH h561 h562 h591 h592 h593 h5101 h5102).trans
      (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.1.1
  have hM₃M₄ : yamadaM₃ d t ≤ yamadaM₄ d t := fun m hm =>
    mem_inf.2 ⟨hL₃R₄ (mem_inf.1 hm).1, (mem_inf.1 hm).2⟩
  refine ⟨le_antisymm (fun x hx => ?_) (sup_le (inf_le_inf_left _
    (centralizer_le (Y_le_yamadaY₂ d h592))) ((zpowers_le).2 (mem_inf.2 ⟨htR₄, htY⟩))),
    fun ht => t_not_mem_centralizer_yamadaY₂ d h592 (mem_inf.1 ht).2⟩
  obtain ⟨hxR₄, -⟩ := mem_inf.1 hx
  obtain ⟨j, hj, x', hx', hr⟩ := h.exists_mem_yamadaR₃_mul_commutator d hNH h561 h562 h591 h592
    h593 h59e hxR₄
  have hcL₄ := h.commutatorElement_mem_yamadaL₄ d hNH h561 h562 h591 h592 h593 h59e hj hx'
  have hjY₂ : j ∈ centralizer (yamadaY₂ d t : Set G) := le_centralizer_iff.1
    (yamadaY₂_le_centralizer_J₀ d h59e) hj
  have hcM₄ : j * x' * j⁻¹ * x'⁻¹ ∈ yamadaM₄ d t :=
    mem_inf.2 ⟨(mem_inf.1 hcL₄).1, commutatorElement_mem_centralizer_C8 hjY₂ (hR₄Y₂ hx')⟩
  have hrL₃ : x * (j * x' * j⁻¹ * x'⁻¹)⁻¹ ∈ yamadaL₃ d t := by
    rw [← h.yamadaR₃_inf_yamadaL₄ d hNH h561 h562 h591 h592 h593 h5101 h5102 h520]
    exact mem_inf.2 ⟨hr, mul_mem hx (inv_mem hcL₄)⟩
  rw [h520.2.2.2.2.1] at hrL₃
  have := mul_mem (sup_le_sup_right hM₃M₄ _ hrL₃)
    (mem_sup_left hcM₄ : j * x' * j⁻¹ * x'⁻¹ ∈ yamadaM₄ d t ⊔ zpowers t)
  rwa [inv_mul_cancel_right] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 in
theorem yamada_5_24_2 :
    yamadaR₄ d t = yamadaL₄ d t ⊔ yamadaR₃ d t ∧ yamadaL₄ d t ⊓ yamadaR₃ d t = yamadaL₃ d t ∧
      yamadaR₄ d t ≤ normalizer (yamadaL₄ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaR₃ d t : Set G) :=
  ⟨(h.yamadaR₄_eq_sup d hNH h561 h562 h591 h592 h593 h59e).trans (sup_comm _ _),
    (inf_comm _ _).trans (h.yamadaR₃_inf_yamadaL₄ d hNH h561 h562 h591 h592 h593 h5101 h5102 h520),
    h.yamadaR₄_le_normalizer_yamadaL₄ d hNH h561 h562 h591 h592 h593,
    (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.2.1.2⟩

include h h592 in
theorem t_not_mem_centralizer_yamadaV₁_C8 : t ∉ centralizer (yamadaV₁ d t : Set G) := by
  intro ht
  apply t_not_mem_centralizer_yamadaY₂ d h592
  have hvt : ((d.v : L) : G) * t = t * ((d.v : L) : G) :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.v).2)
  have hvt' : ((d.v : L) : G)⁻¹ * t = t * ((d.v : L) : G)⁻¹ := by
    calc ((d.v : L) : G)⁻¹ * t = ((d.v : L) : G)⁻¹ * (t * ((d.v : L) : G)) *
          ((d.v : L) : G)⁻¹ := by group
      _ = ((d.v : L) : G)⁻¹ * (((d.v : L) : G) * t) * ((d.v : L) : G)⁻¹ := by rw [hvt]
      _ = t * ((d.v : L) : G)⁻¹ := by group
  have hY₂ : yamadaY₂ d t ≤ centralizer ({t} : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht a ha)) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hat : a * t = t * a := mem_centralizer_iff.1 ht a ha
    show ((d.v : L) : G) * a * ((d.v : L) : G)⁻¹ * t = t * (((d.v : L) : G) * a * ((d.v : L) : G)⁻¹)
    rw [mul_assoc _ _ t, hvt', ← mul_assoc, mul_assoc _ a, hat, ← mul_assoc, hvt]
    group
  exact mem_centralizer_iff.2 fun a ha => mem_centralizer_singleton_iff.1 (hY₂ ha)

include h hNH h561 h562 h591 h592 h593 in
theorem commutator_yamadaR₄_le_yamadaR₃ : ⁅yamadaR₄ d t, yamadaR₄ d t⁆ ≤ yamadaR₃ d t := by
  have hR₄5 : ∀ {y : G}, y ∈ yamadaR₄ d t → y ∈ yamadaR₅ d t := fun hy => (mem_inf.1 hy).1
  have hκF := fun {y : G} (hy : y ∈ yamadaR₄ d t) =>
    h.crossed_mem_yamadaF₁ d hNH h561 h562 h591 h592 h593 hy
  have hR₅W₁ := h.yamadaR₅_le_normalizer_yamadaW₁ d hNH h561 h562 h591 h592 h593
  have hD₁C₁ : yamadaD₁ d t ≤ yamadaC₁ d t := by
    rw [h561.1]
    exact le_sup_left
  have hF₁R₅ : yamadaF₁ d t ≤ yamadaR₅ d t :=
    ((yamadaF₁_le_yamadaD₁ d).trans (hD₁C₁.trans (yamadaC₁_le_yamadaC₅ d t))).trans le_sup_left
  rw [commutator_le]
  intro x hx y hy
  have hxy : x * y ∈ yamadaR₄ d t := mul_mem hx hy
  have hxyx : x * y * x⁻¹ ∈ yamadaR₄ d t := mul_mem hxy (inv_mem hx)
  refine (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593
    (mul_mem hxyx (inv_mem hy))).2 ?_
  obtain ⟨w₁, hw₁, e₁⟩ := h.crossed_mul_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 (hR₄5 hx)
    (hκF hy)
  obtain ⟨w₂, hw₂, e₂⟩ := h.crossed_mul_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 (hR₄5 hxy)
    (hκF (inv_mem hx))
  obtain ⟨w₃, hw₃, e₃⟩ := h.crossed_inv_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 (hR₄5 hx)
    (hκF hx)
  obtain ⟨w₄, hw₄, e₄⟩ := h.crossed_mul_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 (hR₄5 hxyx)
    (hκF (inv_mem hy))
  obtain ⟨w₅, hw₅, e₅⟩ := h.crossed_inv_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 (hR₄5 hy)
    (hκF hy)
  rw [e₄, e₂, e₁, e₃, e₅]
  have ha := hκF hx
  have hb := hκF hy
  generalize t * x * t * x⁻¹ = a at ha ⊢
  generalize t * y * t * y⁻¹ = b at hb ⊢
  have hab := h.commutatorElement_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 ha (hF₁R₅ hb)
  have hbaN : b * a ∈ normalizer (yamadaW₁ d t : Set G) :=
    hR₅W₁ (mul_mem (hF₁R₅ hb) (hF₁R₅ ha))
  have hbN : b ∈ normalizer (yamadaW₁ d t : Set G) := hR₅W₁ (hF₁R₅ hb)
  have h1 := (mem_normalizer_iff.1 hbaN w₁).1 hw₁
  have h2 := (mem_normalizer_iff.1 hbN (w₃ * w₂)).1 (mul_mem hw₃ hw₂)
  have := mul_mem (mul_mem (mul_mem hab h1) h2) (mul_mem hw₅ hw₄)
  rwa [show a * b * a⁻¹ * b⁻¹ * (b * a * w₁ * (b * a)⁻¹) * (b * (w₃ * w₂) * b⁻¹) * (w₅ * w₄) =
    a * b * w₁ * (a⁻¹ * w₃) * w₂ * (b⁻¹ * w₅) * w₄ by group] at this

include h hNH h561 h562 h591 h592 h593 h59e h5221 in
theorem commutator_yamadaR₄_le_yamadaL₄ : ⁅yamadaR₄ d t, yamadaR₄ d t⁆ ≤ yamadaL₄ d t := by
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have hYc := mul_comm_of_isMulCommutative_D4 h592.2.2.1
  have hF₂C : yamadaF₂ d t ≤ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    refine sup_le ?_ fun a ha => mem_centralizer_iff.2 fun y hy =>
      hYc y (Y_le_yamadaY₂ d h592 hy) a ha
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val
      (mem_centralizer_iff.1 (d.M_le_centralizer_Y (d.F_le_M ha)) y hy)
  have hF₂R₄ : yamadaF₂ d t ≤ yamadaR₄ d t := by
    have hF₂M₂ : yamadaF₂ d t ≤ yamadaM₂ d t := sup_le_sup_right (map_mono d.F_le_M) _
    have hM₂L₂ : yamadaM₂ d t ≤ yamadaL₂ d t := by
      rw [h591.1]
      exact le_sup_left
    exact ((hF₂M₂.trans hM₂L₂).trans (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)).trans
      (h514.2.2.2.1.1.trans h514.2.2.2.2.1.1)
  rw [h.yamadaR₄_eq_sup d hNH h561 h562 h591 h592 h593 h59e, sup_comm]
  refine commutator_sup_le_C8 (fun x hx => h.yamadaR₄_le_normalizer_yamadaL₄ d hNH h561 h562 h591
    h592 h593 (h514.2.2.2.2.1.1 hx)) ?_
  rw [h5221.2.2]
  exact le_inf hF₂R₄ hF₂C

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 in
theorem commutator_yamadaR₄_le_yamadaL₃ : ⁅yamadaR₄ d t, yamadaR₄ d t⁆ ≤ yamadaL₃ d t := by
  rw [← h.yamadaR₃_inf_yamadaL₄ d hNH h561 h562 h591 h592 h593 h5101 h5102 h520]
  exact le_inf (h.commutator_yamadaR₄_le_yamadaR₃ d hNH h561 h562 h591 h592 h593)
    (h.commutator_yamadaR₄_le_yamadaL₄ d hNH h561 h562 h591 h592 h593 h59e h5221)

include h h561 h593 h520 in
theorem commutator_yamadaR₅_le_yamadaD₅ : ⁅yamadaR₅ d t, yamadaR₅ d t⁆ ≤ yamadaD₅ d t := by
  have hR₅ : yamadaR₅ d t = yamadaD₅ d t ⊔ (d.S.map L.subtype ⊔ zpowers t) := by
    rw [show yamadaR₅ d t = yamadaC₅ d t ⊔ d.S.map L.subtype from rfl, h520.1, sup_assoc,
      sup_comm (zpowers t)]
  have hSC₅ : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G) :=
    (h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t)
  have htC₅ : t ∈ normalizer (yamadaC₅ d t : Set G) :=
    le_normalizer (yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d))
  have htV₁ : t ∈ normalizer (centralizer (yamadaV₁ d t : Set G) : Set G) :=
    mem_normalizer_centralizer_C8
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d))
  have hKN : d.S.map L.subtype ⊔ zpowers t ≤ normalizer (yamadaD₅ d t : Set G) :=
    sup_le (fun s hs => Common.mem_normalizer_inf (hSC₅ hs)
      (mem_normalizer_centralizer_C8 (S_le_normalizer_yamadaV₁ d h593 hs)))
      ((zpowers_le).2 (Common.mem_normalizer_inf htC₅ htV₁))
  have hD₁C₁ : yamadaD₁ d t ≤ yamadaC₁ d t := by
    rw [h561.1]
    exact le_sup_left
  have hDD₅ : d.D.map L.subtype ≤ yamadaD₅ d t := le_inf
    (((D_le_yamadaD₁ d t).trans hD₁C₁).trans (yamadaC₁_le_yamadaC₅ d t))
    fun δ hδ => mem_centralizer_iff.2 fun v hv =>
      (mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 (map_mono d.D_le_S hδ) hv).symm
  have htS : zpowers t ≤ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    (zpowers_le).2 (h.t_mem_normalizer_map d.S)
  have hKK : ⁅d.S.map L.subtype ⊔ zpowers t, d.S.map L.subtype ⊔ zpowers t⁆ ≤
      yamadaD₅ d t := by
    rw [commutator_le]
    intro x hx y hy
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ htS, Set.mem_mul] at hx hy
    obtain ⟨s, hs, τ, hτ, rfl⟩ := hx
    obtain ⟨s', hs', τ', hτ', rfl⟩ := hy
    have hτs' : τ * s' = s' * τ := (h.commute_zpowers_of_mem_L (map_subtype_le _ hs') hτ).symm
    have hτ's : τ' * s⁻¹ * τ'⁻¹ = s⁻¹ := by
      rw [← h.commute_zpowers_of_mem_L (inv_mem (map_subtype_le _ hs)) hτ', mul_inv_cancel_right]
    have hττ' : τ * τ' * τ⁻¹ = τ' := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
      obtain ⟨k', rfl⟩ := mem_zpowers_iff.1 hτ'
      rw [zpow_mul_comm, mul_inv_cancel_right]
    have e : ⁅s * τ, s' * τ'⁆ = ⁅s, s'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc s * τ * (s' * τ') * (s * τ)⁻¹ * (s' * τ')⁻¹ =
            s * (τ * s') * τ' * τ⁻¹ * s⁻¹ * τ'⁻¹ * s'⁻¹ := by group
        _ = s * (s' * τ) * τ' * τ⁻¹ * s⁻¹ * τ'⁻¹ * s'⁻¹ := by rw [hτs']
        _ = s * s' * (τ * τ' * τ⁻¹) * s⁻¹ * τ'⁻¹ * s'⁻¹ := by group
        _ = s * s' * (τ' * s⁻¹ * τ'⁻¹) * s'⁻¹ := by rw [hττ']; group
        _ = s * s' * s⁻¹ * s'⁻¹ := by rw [hτ's]
    rw [e]
    obtain ⟨a, ha, rfl⟩ := hs
    obtain ⟨b, hb, rfl⟩ := hs'
    exact hDD₅ ⟨⁅a, b⁆, d.F_le_D (d.commutator_S_S (commutator_mem_commutator ha hb)),
      map_commutatorElement _ _ _⟩
  rw [hR₅]
  exact commutator_sup_le_C8 hKN hKK

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h520 in
theorem yamadaL₃_inf_yamadaD₅_le : yamadaL₃ d t ⊓ yamadaD₅ d t ≤ yamadaF₃ d t := by
  intro x hx
  obtain ⟨hxL₃, hxD₅⟩ := mem_inf.1 hx
  obtain ⟨hxC₅, hxV₁⟩ := mem_inf.1 hxD₅
  have htL₃ : t ∈ yamadaL₃ d t := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101
    h5102 (h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t)))
  have htM₃ : t ∈ normalizer (yamadaM₃ d t : Set G) := Common.mem_normalizer_inf
    (le_normalizer htL₃) (mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))
  have hxM₃ : x ∈ yamadaM₃ d t := by
    have h1 := hxL₃
    rw [h520.2.2.2.2.1] at h1
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htM₃).1 h1 with h2 | ⟨m, hm, rfl⟩
    · exact h2
    · exfalso
      have hmV₁ : m ∈ centralizer (yamadaV₁ d t : Set G) :=
        centralizer_le (le_sup_left (a := yamadaV₁ d t)) (mem_inf.1 hm).2
      have := mul_mem (inv_mem hmV₁) hxV₁
      rw [inv_mul_cancel_left] at this
      exact h.t_not_mem_centralizer_yamadaV₁_C8 d h592 this
  exact mem_inf.2 ⟨hxM₃, mem_inf.2 ⟨mem_inf.2 ⟨h.yamadaL₃_le_yamadaR₃ d hNH h561 h562 h591 h592
    h593 h5101 h5102 hxL₃, hxV₁⟩, hxC₅⟩⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 in
theorem commutator_yamadaR₄_le_yamadaF₃ : ⁅yamadaR₄ d t, yamadaR₄ d t⁆ ≤ yamadaF₃ d t := by
  have hR₄5 : yamadaR₄ d t ≤ yamadaR₅ d t := inf_le_left
  exact (le_inf (h.commutator_yamadaR₄_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221) ((commutator_mono hR₄5 hR₄5).trans (h.commutator_yamadaR₅_le_yamadaD₅ d h561 h593
      h520))).trans
    (h.yamadaL₃_inf_yamadaD₅_le d hNH h561 h562 h591 h592 h593 h5101 h5102 h520)

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaL₂_inf_yamadaF₃_le : yamadaL₂ d t ⊓ yamadaF₃ d t ≤ yamadaF₂ d t := by
  have h512 := h.yamada_5_12 d hNH h561 h562 h591 h592 h593
  intro x hx
  obtain ⟨hxL₂, hxF₃⟩ := mem_inf.1 hx
  have hxV₁ : x ∈ centralizer (yamadaV₁ d t : Set G) :=
    (mem_inf.1 (mem_inf.1 (mem_inf.1 hxF₃).2).1).2
  have hxC₅ : x ∈ yamadaC₅ d t := (mem_inf.1 (mem_inf.1 hxF₃).2).2
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    Common.mem_normalizer_sup (h.t_mem_normalizer_map d.M) (h.t_mem_normalizer_yamadaY₂ d)
  have hM₂C := (h.yamadaM₂_eq_inf_centralizer d h591 h592).le
  rw [h591.1] at hxL₂
  have hxM₂ : x ∈ yamadaM₂ d t := by
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htM₂).1 hxL₂ with h1 | ⟨m, hm, rfl⟩
    · exact h1
    · exfalso
      have hmV₁ : m ∈ centralizer (yamadaV₁ d t : Set G) :=
        centralizer_le (le_sup_left (a := yamadaV₁ d t)) (mem_inf.1 (hM₂C hm)).2
      have := mul_mem (inv_mem hmV₁) hxV₁
      rw [inv_mul_cancel_left] at this
      exact h.t_not_mem_centralizer_yamadaV₁_C8 d h592 this
  have hY₂M : yamadaY₂ d t ≤ normalizer ((d.M.map L.subtype : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_fintype fun m hm => by
      rw [SetLike.mem_coe, ← commute_of_mem_M_of_mem_yamadaY₂ d h592 hm hy, mul_inv_cancel_right]
      exact hm
  rw [show yamadaM₂ d t = d.M.map L.subtype ⊔ yamadaY₂ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hY₂M, Set.mem_mul] at hxM₂
  obtain ⟨m, hm, y, hy, rfl⟩ := hxM₂
  have hmC₅ : m ∈ yamadaC₅ d t := by
    have := mul_mem hxC₅ (inv_mem (h512.2.2.1 hy))
    rwa [mul_inv_cancel_right] at this
  have hmD : m ∈ d.D.map L.subtype := by
    have h1 : m ∈ yamadaC₅ d t ⊓ centralizer ({t} : Set G) :=
      mem_inf.2 ⟨hmC₅, h.L_le_centralizer (map_subtype_le _ hm)⟩
    rw [h512.1.2.2.2] at h1
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h1 with h2 | h2
    · exact h2
    · exfalso
      have := mul_mem (map_subtype_le _ h2) (inv_mem (map_subtype_le _ hm))
      rw [mul_inv_cancel_right] at this
      exact h.t_not_mem_L this
  obtain ⟨m', hm', rfl⟩ := hm
  have hm'D : m' ∈ d.D := (mem_map_iff_mem L.subtype_injective).1 hmD
  exact mul_mem (mem_sup_left ⟨m', d.M_inf_D_le_F ⟨hm', hm'D⟩, rfl⟩) (mem_sup_right hy)

include h h562 h593 in
theorem yamadaW₁_inf_le : yamadaW₁ d t ⊓ L ≤ d.W.map L.subtype := by
  intro x hx
  obtain ⟨hxW₁, hxL⟩ := mem_inf.1 hx
  have hVW : yamadaV₁ d t ≤ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) :=
    fun v hv => mem_normalizer_fintype fun w hw => by
      obtain ⟨w', hw', rfl⟩ := hw
      rw [SetLike.mem_coe, ← mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨w', d.W_le_S hw', rfl⟩ hv,
        mul_inv_cancel_right]
      exact ⟨w', hw', rfl⟩
  rw [show yamadaW₁ d t = d.W.map L.subtype ⊔ yamadaV₁ d t from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hVW, Set.mem_mul] at hxW₁
  obtain ⟨w, hw, v, hv, rfl⟩ := hxW₁
  have hvL : v ∈ L := by
    have := mul_mem (inv_mem (map_subtype_le _ hw)) hxL
    rwa [inv_mul_cancel_left] at this
  have hvV : v ∈ d.V.map L.subtype := by
    rw [← h562.2.2.1]
    exact mem_inf.2 ⟨hv, h.L_le_centralizer hvL⟩
  exact mul_mem hw (map_mono (d.V_le_Y.trans d.Y_le_W) hvV)

include h hNH h561 h562 h591 h592 h593 in
theorem exists_mem_yamadaR₄_not_mem_yamadaR₃ : ∃ x ∈ yamadaR₄ d t, x ∉ yamadaR₃ d t := by
  have hx₃ : ((d.x₃ 1 : L) : G) ∈ yamadaF₁ d t := by
    rw [h.yamadaF₁_eq_sup d h561 h562]
    exact mem_sup_left ⟨_, d.x₃_mem_F 1, rfl⟩
  obtain ⟨x, hx, v, hv, e⟩ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.1.2 _ hx₃
  refine ⟨x, hx, fun hxR₃ => ?_⟩
  have hκ := (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593 hx).1 hxR₃
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
    h.t_mul_t, one_mul] at hκ
  have h1 : ((d.x₃ 1 : L) : G) ∈ yamadaW₁ d t := by
    have := mul_mem hκ (inv_mem (mem_sup_right hv : v ∈ yamadaW₁ d t))
    rwa [mul_inv_cancel_right] at this
  have h2 := h.yamadaW₁_inf_le d h562 h593 (mem_inf.2 ⟨h1, (d.x₃ 1).2⟩)
  rw [show ((d.x₃ 1 : L) : G) = L.subtype (d.x₃ 1) from rfl,
    mem_map_iff_mem L.subtype_injective] at h2
  exact one_ne_zero (d.x₃_mem_W_iff.1 h2)

include h h561 h562 in
theorem J_map_le_normalizer_yamadaR₄ :
    d.J.map L.subtype ≤ normalizer (yamadaR₄ d t : Set G) := by
  rintro _ ⟨j, hj, rfl⟩
  have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
  have hjV : (j : G) ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    map_le_normalizer_map d.J_le_normalizer_V ⟨j, hj, rfl⟩
  have hjC₁ : (j : G) ∈ normalizer (yamadaC₁ d t : Set G) :=
    le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d ⟨h.L_le_centralizer j.2, hjV⟩)
  have hjR₅ : (j : G) ∈ normalizer (yamadaR₅ d t : Set G) :=
    Common.mem_normalizer_sup (le_normalizer_yamadaC₅ d t hjC₁)
      (map_le_normalizer_map d.J_le_normalizer_S ⟨j, hj, rfl⟩)
  have hjV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t
    (h561.2.2 ⟨j, d.J_le_normalizer_V hj, rfl⟩)
  have hjF₁ : (j : G) ∈ normalizer (yamadaF₁ d t : Set G) := by
    rw [h.yamadaF₁_eq_sup d h561 h562]
    exact Common.mem_normalizer_sup (map_le_normalizer_map d.J_le_normalizer_F ⟨j, hj, rfl⟩) hjV₁
  exact Common.mem_normalizer_inf hjR₅
    (le_normalizer (Common.mem_normalizer_sup hjF₁ (mem_normalizer_zpowers_of_comm_D4 hjt)))

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 in
theorem yamadaF₃_le_commutator_yamadaR₄ : yamadaF₃ d t ≤ ⁅yamadaR₄ d t, yamadaR₄ d t⁆ := by
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have hR₃R₄ := h514.2.2.2.2.1.1
  have hPF₃ := h.commutator_yamadaR₄_le_yamadaF₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221
  have hPL₃ := h.commutator_yamadaR₄_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221
  have hF₂P : yamadaF₂ d t ≤ ⁅yamadaR₄ d t, yamadaR₄ d t⁆ := by
    rw [← h5221.2.2]
    exact commutator_mono hR₃R₄ hR₃R₄
  have hF₃L₃ : yamadaF₃ d t ≤ yamadaL₃ d t := fun x hx => (mem_inf.1 (mem_inf.1 hx).1).1
  have hL₃V := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₂F₃ := h.yamadaL₂_inf_yamadaF₃_le d hNH h561 h562 h591 h592 h593
  have hY : ∀ z ∈ yamadaF₃ d t, t * z * t * z⁻¹ ∈ d.Y.map L.subtype →
      z ∈ ⁅yamadaR₄ d t, yamadaR₄ d t⁆ := fun z hz hκ =>
    hF₂P (hL₂F₃ (mem_inf.2 ⟨yamadaL₃_inf_le d t (mem_inf.2 ⟨hF₃L₃ hz,
      (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 (hL₃V (hF₃L₃ hz))).1 hκ⟩),
      hz⟩))
  obtain ⟨r₀, hr₀, hκr₀⟩ : ∃ r ∈ ⁅yamadaR₄ d t, yamadaR₄ d t⁆,
      t * r * t * r⁻¹ ∉ d.Y.map L.subtype := by
    by_contra hcon
    push Not at hcon
    have hPR₂ : ⁅yamadaR₄ d t, yamadaR₄ d t⁆ ≤ yamadaR₂ d t := fun r hr =>
      (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) (yamadaL₃_inf_le d t (mem_inf.2 ⟨hPL₃ hr,
        (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 (hL₃V (hPL₃ hr))).1
          (hcon r hr)⟩))
    have hR₄N : yamadaR₄ d t ≤ normalizer (yamadaR₂ d t : Set G) := fun x hx =>
      mem_normalizer_fintype fun y hy => by
        have hyR₄ : y ∈ yamadaR₄ d t := hR₃R₄ (h514.2.2.2.1.1 hy)
        have := mul_mem (hPR₂ (commutator_mem_commutator hx hyR₄)) hy
        rwa [commutatorElement_def, inv_mul_cancel_right] at this
    obtain ⟨x, hx, hxR₃⟩ := h.exists_mem_yamadaR₄_not_mem_yamadaR₃ d hNH h561 h562 h591 h592 h593
    apply hxR₃
    refine (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593 hx).2 ?_
    exact mem_sup_left (h.crossed_mem_W d h562 h592
      (mem_inf.1 (normalizer_yamadaR₂_le d h592 h5101 h5102 (hR₄N hx))).1)
  obtain ⟨w₀, hw₀, hw₀e⟩ := h.crossed_mem_W d h562 h592 (hL₃V (hPL₃ hr₀))
  obtain ⟨a₀, n₀, hn₀, rfl⟩ := d.mem_W_iff.1 hw₀
  have ha₀ : d.x₄ a₀ ≠ 1 := fun e => hκr₀ (by
    rw [← hw₀e, e, one_mul]
    exact ⟨n₀, hn₀, rfl⟩)
  intro z hz
  obtain ⟨wz, hwz, hwze⟩ := h.crossed_mem_W d h562 h592 (hL₃V (hF₃L₃ hz))
  obtain ⟨b, n, hn, rfl⟩ := d.mem_W_iff.1 hwz
  by_cases hb : d.x₄ b = 1
  · refine hY z hz ?_
    rw [← hwze, hb, one_mul]
    exact ⟨n, hn, rfl⟩
  obtain ⟨j, ⟨hj, hjx⟩, -⟩ := (d.yamada_three_five_five.2.2.1).2 _ (d.x₄_mem_U₄ a₀) ha₀ _
    (d.x₄_mem_U₄ b) hb
  have hjJ : j ∈ d.J := (inf_le_left : d.J₂ ≤ d.J) hj
  have hjP : (j : G) ∈ normalizer ((⁅yamadaR₄ d t, yamadaR₄ d t⁆ : Subgroup G) : Set G) :=
    normalizer_le_normalizer_commutator_C8 _
      (h.J_map_le_normalizer_yamadaR₄ d h561 h562 ⟨j, hjJ, rfl⟩)
  have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
  have hjt' : (j : G)⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
  have hrP : (j : G) * r₀ * (j : G)⁻¹ ∈ ⁅yamadaR₄ d t, yamadaR₄ d t⁆ :=
    (mem_normalizer_iff.1 hjP r₀).1 hr₀
  have hκr : t * ((j : G) * r₀ * (j : G)⁻¹) * t * ((j : G) * r₀ * (j : G)⁻¹)⁻¹ =
      (j : G) * (t * r₀ * t * r₀⁻¹) * (j : G)⁻¹ := by
    calc t * ((j : G) * r₀ * (j : G)⁻¹) * t * ((j : G) * r₀ * (j : G)⁻¹)⁻¹ =
          t * j * r₀ * ((j : G)⁻¹ * t * j) * r₀⁻¹ * (j : G)⁻¹ := by group
      _ = j * t * r₀ * t * r₀⁻¹ * (j : G)⁻¹ := by rw [hjt', ← hjt]
      _ = (j : G) * (t * r₀ * t * r₀⁻¹) * (j : G)⁻¹ := by group
  have hjn₀ : (j : G) * (n₀ : G) * (j : G)⁻¹ ∈ d.Y.map L.subtype :=
    ⟨j * n₀ * j⁻¹, (mem_normalizer_iff.1 (d.J_le_normalizer_Y hjJ) n₀).1 hn₀, rfl⟩
  have hjx' : (j : G) * (d.x₄ a₀ : G) * (j : G)⁻¹ = (d.x₄ b : G) := congrArg Subtype.val hjx
  have e : t * ((j : G) * r₀ * (j : G)⁻¹) * t * ((j : G) * r₀ * (j : G)⁻¹)⁻¹ =
      t * z * t * z⁻¹ * ((n : G)⁻¹ * ((j : G) * n₀ * (j : G)⁻¹)) := by
    rw [hκr, ← hw₀e, ← hwze]
    calc (j : G) * L.subtype (d.x₄ a₀ * n₀) * (j : G)⁻¹ =
          ((j : G) * (d.x₄ a₀ : G) * (j : G)⁻¹) * ((j : G) * (n₀ : G) * (j : G)⁻¹) := by
          rw [map_mul, Subgroup.coe_subtype]
          group
      _ = (d.x₄ b : G) * ((j : G) * (n₀ : G) * (j : G)⁻¹) := by rw [hjx']
      _ = L.subtype (d.x₄ b * n) * ((n : G)⁻¹ * ((j : G) * n₀ * (j : G)⁻¹)) := by
          rw [map_mul, Subgroup.coe_subtype]
          group
  have hc := h.inv_mul_mem_normalizer_tY d hNH h561 h562 h591 h592 h593 h5101 h5102
    (hL₃V (hPL₃ hrP)) (hL₃V (hF₃L₃ hz)) (mul_mem (inv_mem ⟨n, hn, rfl⟩) hjn₀) e
  have hcF₂ : ((j : G) * r₀ * (j : G)⁻¹)⁻¹ * z ∈ yamadaF₂ d t :=
    hL₂F₃ (mem_inf.2 ⟨yamadaL₃_inf_le d t (mem_inf.2 ⟨mul_mem (inv_mem (hPL₃ hrP)) (hF₃L₃ hz),
      hc⟩), mul_mem (inv_mem (hPF₃ hrP)) hz⟩)
  have := mul_mem hrP (hF₂P hcF₂)
  rwa [mul_inv_cancel_left] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 in
theorem yamada_5_24 :
    (yamadaL₄ d t = yamadaM₄ d t ⊔ zpowers t ∧ t ∉ yamadaM₄ d t) ∧
    (yamadaR₄ d t = yamadaL₄ d t ⊔ yamadaR₃ d t ∧ yamadaL₄ d t ⊓ yamadaR₃ d t = yamadaL₃ d t ∧
      yamadaR₄ d t ≤ normalizer (yamadaL₄ d t : Set G) ∧
      yamadaR₄ d t ≤ normalizer (yamadaR₃ d t : Set G)) ∧
    ⁅yamadaR₄ d t, yamadaR₄ d t⁆ = yamadaF₃ d t :=
  ⟨h.yamadaL₄_eq_sup d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221,
    h.yamada_5_24_2 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520,
    le_antisymm (h.commutator_yamadaR₄_le_yamadaF₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
      h520 h5221) (h.yamadaF₃_le_commutator_yamadaR₄ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
      h520 h5221)⟩

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
