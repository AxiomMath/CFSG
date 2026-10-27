module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S1A

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

noncomputable def Data.secHomXC₀ {G : Type} [Group G] (d : Data G)
    (hle : d.XC₀ ≤ normalizer (d.D₀ : Set G)) : d.XC₀ →* MulAut (innSub d.D₀) :=
  (secHom d.D₀).comp (Subgroup.inclusion hle)

@[expose] def Data.XY {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.XC₀ ⊓ normalizer (d.Y : Set G)

@[expose] def Data.OmY {G : Type} [Group G] (d : Data G) : Set (Set G) :=
  {S | ∃ x ∈ d.XY, S = (x * d.t * x⁻¹) • (d.Y : Set G)}

namespace Data

variable {G : Type} [Group G] (d : Data G)

theorem conj_mem_OmY {x : G} (hx : x ∈ d.XY) {S : Set G} (hS : S ∈ d.OmY) :
    (fun g => x * g * x⁻¹) '' S ∈ d.OmY := by
  obtain ⟨y, hy, rfl⟩ := hS
  refine ⟨x * y, mul_mem hx hy, ?_⟩
  rw [conj_image_smul_coset (Subgroup.mem_inf.1 hx).2]
  congr 1
  group

@[expose] def omegaConjY (x : d.XY) : Equiv.Perm d.OmY where
  toFun S := ⟨(fun g => (x : G) * g * (x : G)⁻¹) '' S, d.conj_mem_OmY x.2 S.2⟩
  invFun S := ⟨(fun g => (x : G)⁻¹ * g * (x : G)⁻¹⁻¹) '' S, d.conj_mem_OmY (inv_mem x.2) S.2⟩
  left_inv S := Subtype.ext (by simp [Set.image_image, mul_assoc])
  right_inv S := Subtype.ext (by simp [Set.image_image, mul_assoc])

@[expose] def omegaPermY : d.XY →* Equiv.Perm d.OmY where
  toFun := d.omegaConjY
  map_one' := Equiv.ext fun S => Subtype.ext (by simp [omegaConjY])
  map_mul' x y := Equiv.ext fun S => Subtype.ext (by
    simp [omegaConjY, Set.image_image, mul_assoc])

theorem omegaPermY_apply (x : d.XY) (S : d.OmY) :
    ((d.omegaPermY x S : d.OmY) : Set G) = (fun g => (x : G) * g * (x : G)⁻¹) '' S := rfl

end Data

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem mem_Y_iff_D₀ (z : G) : z ∈ d.Y ↔ z ∈ d.D₀ ∧ ∀ q ∈ d.D₀, z * q = q * z :=
  ⟨fun hz => ⟨Y_le_D₀ hz, fun q hq => Y_comm_D₀ hz hq⟩, fun ⟨hz, hc⟩ =>
    ⟨mem_centralizer_iff.2 fun q hq => (hc q hq).symm, hz⟩⟩

theorem card_D₀_eq_mul (h : d.Hyp) : Nat.card d.D₀ = 16 * Nat.card d.Y := by
  rw [h.card_D₀, h.sec4_6.2.2.2.2.1]
  norm_num

omit [Finite G] in
theorem commutator_mem_F {a b : G} (ha : a ∈ d.A₂) (hb : b ∈ d.A₂) :
    a * b * a⁻¹ * b⁻¹ ∈ d.F := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  exact ⟨⁅α, β⁆, commutator_mem_Fsub hα hβ, by rw [map_commutatorElement, commutatorElement_def]⟩

omit [Finite G] in
theorem mul_self_mem_F {a : G} (ha : a ∈ d.A₂) : a * a ∈ d.F := by
  obtain ⟨α, hα, rfl⟩ := ha
  exact ⟨α * α, mul_self_mem_Fsub hα, map_mul _ _ _⟩

theorem comm_D₀ (h : d.Hyp) {p q : G} (hp : p ∈ d.D₀) (hq : q ∈ d.D₀) :
    p * q * p⁻¹ * q⁻¹ ∈ d.Y := by
  rw [h.D₀_eq] at hp hq
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 hp
  obtain ⟨b, hb, e', he', rfl⟩ := (h.mem_A₂E₂_iff).1 hq
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have he'Y : e' ∈ d.Y := h.Y_eq_E₂ ▸ he'
  rw [← commutatorElement_def, commutatorElement_mul_mul_eq (Y_comm_D₀ heY (h.A₂_le_D₀ hb))
    (h.Y_comm heY he'Y) (Y_comm_D₀ he'Y (h.A₂_le_D₀ ha)), commutatorElement_def]
  exact h.F_le_Y (commutator_mem_F ha hb)

theorem sq_D₀ (h : d.Hyp) {p : G} (hp : p ∈ d.D₀) : p * p ∈ d.Y := by
  rw [h.D₀_eq] at hp
  obtain ⟨a, ha, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 hp
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have hea : e * a = a * e := Y_comm_D₀ heY (h.A₂_le_D₀ ha)
  rw [show a * e * (a * e) = (a * a) * (e * e) by
    rw [show a * e * (a * e) = a * (e * a) * e by group, hea]
    group, h.Y_sq heY, mul_one]
  exact h.F_le_Y (mul_self_mem_F ha)

theorem crossed_t_mem_Y (h : d.Hyp) {a : G} (ha : a ∈ d.D₀) : a⁻¹ * (d.t * a * d.t) ∈ d.Y := by
  rw [h.D₀_eq] at ha
  obtain ⟨a₁, ha₁, e, he, rfl⟩ := (h.mem_A₂E₂_iff).1 ha
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have hta : d.t * a₁ = a₁ * d.t := (h.t_comm_of_mem_L (d.pull_le_L _ ha₁)).symm
  have : (a₁ * e)⁻¹ * (d.t * (a₁ * e) * d.t) = e⁻¹ * (d.t * e * d.t) := by
    calc (a₁ * e)⁻¹ * (d.t * (a₁ * e) * d.t) = e⁻¹ * (a₁⁻¹ * (d.t * a₁) * e * d.t) := by group
      _ = e⁻¹ * (a₁⁻¹ * (a₁ * d.t) * e * d.t) := by rw [hta]
      _ = e⁻¹ * (d.t * e * d.t) := by group
  rw [this]
  exact mul_mem (inv_mem heY) (h.t_conj_mem_Y heY)

theorem conj_mem_Y_of_mem_C₀ (h : d.Hyp) {c a : G} (hc : c ∈ d.C₀) (ha : a ∈ d.D₀) :
    a⁻¹ * c * a * c⁻¹ ∈ d.Y := by
  rcases (h.mem_C₀_iff).1 hc with hcD | hcD
  · have := h.comm_D₀ (inv_mem ha) hcD
    rwa [inv_inv] at this
  · obtain ⟨δ, hδ, rfl⟩ : ∃ δ, δ ∈ d.D₀ ∧ c = δ * d.t :=
      ⟨c * d.t, hcD, by rw [mul_assoc, h.t_mul_t, mul_one]⟩
    obtain ⟨y', hy'Y, hy'⟩ : ∃ y' ∈ d.Y, d.t * a * d.t = a * y' :=
      ⟨_, h.crossed_t_mem_Y ha, by group⟩
    have hy'δ : y' * δ⁻¹ = δ⁻¹ * y' := Y_comm_D₀ hy'Y (inv_mem hδ)
    have e1 : a⁻¹ * (δ * d.t) * a * (δ * d.t)⁻¹ = (a⁻¹ * δ * a * δ⁻¹) * y' := by
      calc a⁻¹ * (δ * d.t) * a * (δ * d.t)⁻¹ = a⁻¹ * δ * (d.t * a * d.t) * δ⁻¹ := by
            rw [mul_inv_rev, h.t_inv]
            group
        _ = a⁻¹ * δ * (a * y') * δ⁻¹ := by rw [hy']
        _ = (a⁻¹ * δ * a * δ⁻¹) * (δ * (y' * δ⁻¹)) := by group
        _ = (a⁻¹ * δ * a * δ⁻¹) * (δ * (δ⁻¹ * y')) := by rw [hy'δ]
        _ = (a⁻¹ * δ * a * δ⁻¹) * y' := by group
    rw [e1]
    have := h.comm_D₀ (inv_mem ha) hδ
    rw [inv_inv] at this
    exact mul_mem this hy'Y

theorem C₀_le_UD₀ (h : d.Hyp) : d.C₀ ≤ d.UD₀ := fun c hc =>
  mem_UD₀_iff.2 ⟨d.C₀.le_normalizer hc, fun a ha => ⟨h.conj_mem_Y_of_mem_C₀ hc ha, by
    have := h.conj_mem_Y_of_mem_C₀ (inv_mem hc) ha
    rwa [inv_inv] at this⟩⟩

theorem Y_le_UD₀ (h : d.Hyp) : d.Y ≤ d.UD₀ := fun y hy =>
  h.C₀_le_UD₀ (h.Y_le_C₀ hy)

theorem conj_mem_UD₀ (h : d.Hyp) {g u : G} (hg : g ∈ d.XC₀) (hu : u ∈ d.UD₀) :
    g * u * g⁻¹ ∈ d.UD₀ := by
  have hgD : g ∈ normalizer (d.D₀ : Set G) := h.normalizer_C₀_le_normalizer_D₀ hg
  have hgY : ∀ y ∈ d.Y, g * y * g⁻¹ ∈ d.Y := fun y hy => h.conj_mem_Y_of_mem_XC₀ hg hy
  have ha' : ∀ a ∈ d.D₀, g⁻¹ * a * g ∈ d.D₀ := fun a ha => by
    have := (mem_normalizer_iff.1 (inv_mem hgD) a).1 ha
    rwa [inv_inv] at this
  refine mem_UD₀_iff.2 ⟨mul_mem (mul_mem hg (UD₀_le_XC₀ hu)) (inv_mem hg), fun a ha => ⟨?_, ?_⟩⟩
  · have h2 := hgY _ ((mem_UD₀_iff.1 hu).2 _ (ha' a ha)).1
    rwa [show g * ((g⁻¹ * a * g)⁻¹ * u * (g⁻¹ * a * g) * u⁻¹) * g⁻¹ =
      a⁻¹ * (g * u * g⁻¹) * a * (g * u * g⁻¹)⁻¹ by group] at h2
  · have h2 := hgY _ ((mem_UD₀_iff.1 hu).2 _ (ha' a ha)).2
    rwa [show g * ((g⁻¹ * a * g)⁻¹ * u⁻¹ * (g⁻¹ * a * g) * u) * g⁻¹ =
      a⁻¹ * (g * u * g⁻¹)⁻¹ * a * (g * u * g⁻¹) by group] at h2

theorem crossed_mul_mem_UD₀ (h : d.Hyp) {u₁ u₂ : G} (hu₁ : u₁ ∈ d.UD₀) (hu₂ : u₂ ∈ d.XC₀) :
    ∃ w ∈ d.Y, u₁ * u₂ * d.t * (u₁ * u₂)⁻¹ * d.t =
      (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) * w := by
  have hp := h.crossed_mem_D₀ hu₂
  have hq := h.crossed_mem_D₀ (UD₀_le_XC₀ hu₁)
  obtain ⟨c, hc, hce⟩ : ∃ c ∈ d.Y, u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹ =
      c * (u₂ * d.t * u₂⁻¹ * d.t) := by
    refine ⟨u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹ * (u₂ * d.t * u₂⁻¹ * d.t)⁻¹, ?_, by group⟩
    have := inv_mem ((mem_UD₀_iff.1 hu₁).2 (u₂ * d.t * u₂⁻¹ * d.t)⁻¹ (inv_mem hp)).1
    rwa [show ((u₂ * d.t * u₂⁻¹ * d.t)⁻¹⁻¹ * u₁ * (u₂ * d.t * u₂⁻¹ * d.t)⁻¹ * u₁⁻¹)⁻¹ =
      u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹ * (u₂ * d.t * u₂⁻¹ * d.t)⁻¹ by group] at this
  refine ⟨c, hc, ?_⟩
  have hcomm : c * (u₂ * d.t * u₂⁻¹ * d.t) = (u₂ * d.t * u₂⁻¹ * d.t) * c := Y_comm_D₀ hc hp
  have hcq : c * (u₁ * d.t * u₁⁻¹ * d.t) = (u₁ * d.t * u₁⁻¹ * d.t) * c := Y_comm_D₀ hc hq
  calc u₁ * u₂ * d.t * (u₁ * u₂)⁻¹ * d.t =
      (u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹) * (u₁ * d.t * u₁⁻¹ * d.t) := by
        rw [show (u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹) * (u₁ * d.t * u₁⁻¹ * d.t) =
          u₁ * u₂ * d.t * u₂⁻¹ * (d.t * d.t) * u₁⁻¹ * d.t by group, h.t_mul_t]
        group
    _ = c * (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) := by rw [hce]
    _ = (u₂ * d.t * u₂⁻¹ * d.t) * c * (u₁ * d.t * u₁⁻¹ * d.t) := by rw [hcomm]
    _ = (u₂ * d.t * u₂⁻¹ * d.t) * (c * (u₁ * d.t * u₁⁻¹ * d.t)) := by group
    _ = (u₂ * d.t * u₂⁻¹ * d.t) * ((u₁ * d.t * u₁⁻¹ * d.t) * c) := by rw [hcq]
    _ = (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) * c := by group

theorem mem_ker_secHomXC₀_iff (h : d.Hyp) (hle : d.XC₀ ≤ normalizer (d.D₀ : Set G))
    (x : d.XC₀) : x ∈ (d.secHomXC₀ hle).ker ↔ (x : G) ∈ d.UD₀ := by
  rw [MonoidHom.mem_ker]
  change secHom d.D₀ (Subgroup.inclusion hle x) = 1 ↔ _
  rw [secHom_eq_one_iff]
  change (∀ p ∈ d.D₀, ∀ q ∈ d.D₀, ((x : G) * p * (x : G)⁻¹ * p⁻¹) * q =
    q * ((x : G) * p * (x : G)⁻¹ * p⁻¹)) ↔ _
  constructor
  · intro hc
    have hcY : ∀ p ∈ d.D₀, (x : G) * p * (x : G)⁻¹ * p⁻¹ ∈ d.Y := fun p hp => by
      refine (mem_Y_iff_D₀ _).2 ⟨?_, fun q hq => hc p hp q hq⟩
      exact mul_mem ((mem_normalizer_iff.1 (hle x.2) p).1 hp) (inv_mem hp)
    refine mem_UD₀_iff.2 ⟨x.2, fun a ha => ⟨?_, ?_⟩⟩
    · have := inv_mem (hcY a⁻¹ (inv_mem ha))
      rwa [show ((x : G) * a⁻¹ * (x : G)⁻¹ * a⁻¹⁻¹)⁻¹ = a⁻¹ * (x : G) * a * (x : G)⁻¹ by
        group] at this
    · have := h.conj_mem_Y_of_mem_XC₀ (inv_mem x.2) (hcY a⁻¹ (inv_mem ha))
      rwa [show (x : G)⁻¹ * ((x : G) * a⁻¹ * (x : G)⁻¹ * a⁻¹⁻¹) * (x : G)⁻¹⁻¹ =
        a⁻¹ * (x : G)⁻¹ * a * (x : G) by group] at this
  · intro hx p hp q hq
    have := inv_mem ((mem_UD₀_iff.1 hx).2 p⁻¹ (inv_mem hp)).1
    rw [show ((p⁻¹)⁻¹ * (x : G) * p⁻¹ * (x : G)⁻¹)⁻¹ = (x : G) * p * (x : G)⁻¹ * p⁻¹ by
      group] at this
    exact Y_comm_D₀ this hq

theorem relIndex_UD₀_dvd (h : d.Hyp) : d.UD₀.relIndex d.XC₀ ∣ 20160 := by
  have hle : d.XC₀ ≤ normalizer (d.D₀ : Set G) := h.normalizer_C₀_le_normalizer_D₀
  have hker : (d.secHomXC₀ hle).ker = d.UD₀.subgroupOf d.XC₀ := by
    ext x
    rw [h.mem_ker_secHomXC₀_iff hle, mem_subgroupOf]
  obtain ⟨hinn_comm, hinn_sq⟩ := innSub_comm_sq d.D₀ mem_Y_iff_D₀
    (fun p hp q hq => h.comm_D₀ hp hq) (fun p hp => h.sq_D₀ hp)
  have hAut := card_mulAut_of_elemAb_sixteen hinn_comm hinn_sq
    (card_innSub d.D₀ mem_Y_iff_D₀ h.card_D₀_eq_mul)
  change (d.UD₀.subgroupOf d.XC₀).index ∣ 20160
  rw [← hker, Subgroup.index_ker, ← hAut]
  exact Subgroup.card_subgroup_dvd_card _

theorem mem_C₀_of_mem_UD₀_of_crossed_mem (h : d.Hyp) {u : G} (hu : u ∈ d.UD₀)
    (hθ : u * d.t * u⁻¹ * d.t ∈ d.Y) : u ∈ d.C₀ := by
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.Y
    h.NHA₂_le_normalizer_Y
  obtain ⟨n, hn, y, hy, rfl⟩ : u ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) : Set G) *
      (d.Y : Set G) := by
    rw [← hset]
    exact h.mem_NHA₂Y_of_crossed_mem (UD₀_le_XC₀ hu) hθ
  have hnU : n ∈ d.UD₀ := by
    have := mul_mem hu (inv_mem (h.Y_le_UD₀ hy))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨hnA, hnH⟩ := Subgroup.mem_inf.1 hn
  have hnN : n ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) := by
    have : n ∈ normalizer ((d.withT d.A₂ : Subgroup G) : Set G) ⊓ d.H := by
      rw [h.normalizer_inf_H_eq]
      exact hn
    exact this.1
  have hnX₀ : n ∈ X₀ d := by
    refine ⟨⟨n, hnN⟩, ?_, rfl⟩
    change secHom (d.withT d.A₂) ⟨n, hnN⟩ = 1
    rw [secHom_eq_one_iff]
    intro p hp q hq
    obtain ⟨a, ha, c, hc, rfl⟩ := h.exists_eq_mul_of_mem_withT_A₂ hp
    have hcn : n * c * n⁻¹ = c := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.1 hnH) k).eq
    have hm : n * (a * c) * n⁻¹ * (a * c)⁻¹ = (n * a * n⁻¹) * a⁻¹ := by
      rw [show n * (a * c) * n⁻¹ * (a * c)⁻¹ = (n * a * n⁻¹) * (n * c * n⁻¹) * c⁻¹ * a⁻¹ by
        group, hcn]
      group
    have hY : (n * a * n⁻¹) * a⁻¹ ∈ d.Y := by
      have := inv_mem ((mem_UD₀_iff.1 hnU).2 a⁻¹ (inv_mem (h.A₂_le_D₀ ha))).1
      rwa [show ((a⁻¹)⁻¹ * n * a⁻¹ * n⁻¹)⁻¹ = (n * a * n⁻¹) * a⁻¹ by group] at this
    have hF : (n * a * n⁻¹) * a⁻¹ ∈ d.F := by
      rw [← h.A₂_inf_Y]
      exact Subgroup.mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hnA a).1 ha) (inv_mem ha), hY⟩
    change (n * (a * c) * n⁻¹ * (a * c)⁻¹) * q = q * (n * (a * c) * n⁻¹ * (a * c)⁻¹)
    rw [hm]
    exact ((h.mem_center_A₂t_iff).2 (mem_sup_left hF)).2 q hq
  have hnP : n ∈ d.withT d.A₂ := by
    rw [← h.X₀_inf_H_eq]
    exact Subgroup.mem_inf.2 ⟨hnX₀, hnH⟩
  exact mul_mem ((sup_le h.A₂_le_C₀ (zpowers_le.2 h.t_mem_C₀) : d.withT d.A₂ ≤ d.C₀) hnP)
    (h.Y_le_C₀ hy)

theorem t_conj_mem_Y_iff (h : d.Hyp) {y : G} : d.t * y * d.t ∈ d.Y ↔ y ∈ d.Y :=
  ⟨fun hy => by
    have := h.t_conj_mem_Y hy
    rwa [show d.t * (d.t * y * d.t) * d.t = (d.t * d.t) * y * (d.t * d.t) by group, h.t_mul_t,
      one_mul, mul_one] at this, fun hy => h.t_conj_mem_Y hy⟩

theorem coset_mem_Y_iff (h : d.Hyp) (a u : G) :
    (a * d.t)⁻¹ * (u * d.t * u⁻¹) ∈ d.Y ↔ a⁻¹ * (u * d.t * u⁻¹ * d.t) ∈ d.Y := by
  have e : (a * d.t)⁻¹ * (u * d.t * u⁻¹) = d.t * (a⁻¹ * (u * d.t * u⁻¹ * d.t)) * d.t := by
    rw [show d.t * (a⁻¹ * (u * d.t * u⁻¹ * d.t)) * d.t =
      d.t * a⁻¹ * (u * d.t * u⁻¹) * (d.t * d.t) by group, h.t_mul_t, mul_one, mul_inv_rev,
      h.t_inv]
  rw [e]
  exact h.t_conj_mem_Y_iff

theorem relIndex_normalizer_withT_Y (h : d.Hyp) {K : Subgroup G} (hK : K ≤ d.XC₀)
    (htrans : ∀ c : Fin 2 → F4, ∃ x ∈ K, (d.ι (nfA₂ c) * d.t)⁻¹ * (x * d.t * x⁻¹) ∈ d.Y) :
    (normalizer ((d.withT d.Y : Subgroup G) : Set G)).relIndex K = 16 := by
  have hKXY : K ≤ d.XY := le_inf hK (hK.trans h.XC₀_le_normalizer_Y)
  let φ : K →* Equiv.Perm d.OmY := d.omegaPermY.comp (Subgroup.inclusion hKXY)
  let : MulAction K d.OmY := MulAction.compHom _ φ
  have hsmul : ∀ (u : K) (S : d.OmY), ((u • S : d.OmY) : Set G) =
      (fun g => (u : G) * g * (u : G)⁻¹) '' (S : Set G) := by
    intro u S
    rw [MulAction.compHom_smul_def, Equiv.Perm.smul_def, MonoidHom.comp_apply,
      Data.omegaPermY_apply, Subgroup.coe_inclusion]
  have htY : d.t • (d.Y : Set G) ∈ d.OmY := ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩
  have hstab : MulAction.stabilizer K (⟨_, htY⟩ : d.OmY) =
      (normalizer ((d.withT d.Y : Subgroup G) : Set G)).subgroupOf K := by
    ext u
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, h.mem_normalizer_withT_Y_iff (hK u.2),
      Subtype.ext_iff, hsmul]
    change (fun g => (u : G) * g * (u : G)⁻¹) '' (d.t • (d.Y : Set G)) = d.t • (d.Y : Set G) ↔ _
    rw [conj_image_smul_coset (h.XC₀_le_normalizer_Y (hK u.2)), leftCoset_eq_iff,
      show ((u : G) * d.t * (u : G)⁻¹)⁻¹ * d.t = (u : G) * d.t * (u : G)⁻¹ * d.t by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, h.t_inv]
        group]
  have hmem : ∀ c : Fin 2 → F4, (d.ι (nfA₂ c) * d.t) • (d.Y : Set G) ∈ d.OmY := fun c => by
    obtain ⟨x, hxK, hx⟩ := htrans c
    exact ⟨x, hKXY hxK, (leftCoset_eq_iff d.Y).2 hx⟩
  let f : (Fin 2 → F4) → d.OmY := fun c => ⟨_, hmem c⟩
  have hf : Function.Injective f := fun c c' e => by
    have e1 := (leftCoset_eq_iff d.Y).1 (congrArg Subtype.val e)
    have e2 : (d.ι (nfA₂ c))⁻¹ * d.ι (nfA₂ c') ∈ d.Y := by
      have := h.t_conj_mem_Y e1
      rwa [show d.t * ((d.ι (nfA₂ c) * d.t)⁻¹ * (d.ι (nfA₂ c') * d.t)) * d.t =
        (d.ι (nfA₂ c))⁻¹ * d.ι (nfA₂ c') * (d.t * d.t) by group, h.t_mul_t, mul_one] at this
    have e3 : d.ι ((nfA₂ c)⁻¹ * nfA₂ c') ∈ d.F := by
      rw [← h.A₂_inf_Y]
      refine Subgroup.mem_inf.2 ⟨⟨_, mul_mem (inv_mem (nfA₂_mem c)) (nfA₂_mem c'), rfl⟩, ?_⟩
      rw [map_mul, map_inv]
      exact e2
    have e4 := (inv_mul_mem_Fsub_iff_a₂Coord (nfA₂_mem c) (nfA₂_mem c')).1
      (d.ι_mem_pull_iff.1 e3)
    rwa [a₂Coord_nfA₂, a₂Coord_nfA₂] at e4
  have horb : MulAction.orbit K (⟨_, htY⟩ : d.OmY) = Set.range f := by
    ext S
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨a, ha, e, he, hθ⟩ := (h.mem_A₂E₂_iff).1 (h.D₀_eq ▸ h.crossed_mem_D₀ (hK u.2))
      have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
      obtain ⟨α, hα, rfl⟩ := ha
      refine ⟨a₂Coord (mat α), Subtype.ext ?_⟩
      change (d.ι (nfA₂ (a₂Coord (mat α))) * d.t) • (d.Y : Set G) =
        ((u • (⟨_, htY⟩ : d.OmY) : d.OmY) : Set G)
      rw [hsmul]
      change _ = (fun g => (u : G) * g * (u : G)⁻¹) '' (d.t • (d.Y : Set G))
      rw [conj_image_smul_coset (h.XC₀_le_normalizer_Y (hK u.2)), leftCoset_eq_iff,
        h.coset_mem_Y_iff, hθ]
      have hF : (nfA₂ (a₂Coord (mat α)))⁻¹ * α ∈ Fsub :=
        (inv_mul_mem_Fsub_iff_a₂Coord (nfA₂_mem _) hα).2 (by rw [a₂Coord_nfA₂])
      rw [show (d.ι (nfA₂ (a₂Coord (mat α))))⁻¹ * (d.ι α * e) =
        d.ι ((nfA₂ (a₂Coord (mat α)))⁻¹ * α) * e by rw [map_mul, map_inv, mul_assoc]]
      exact mul_mem (h.F_le_Y ⟨_, hF, rfl⟩) heY
    · rintro ⟨c, rfl⟩
      obtain ⟨x, hxK, hx⟩ := htrans c
      refine ⟨⟨x, hxK⟩, Subtype.ext ?_⟩
      rw [hsmul]
      change (fun g => x * g * x⁻¹) '' (d.t • (d.Y : Set G)) =
        (d.ι (nfA₂ c) * d.t) • (d.Y : Set G)
      rw [conj_image_smul_coset (h.XC₀_le_normalizer_Y (hK hxK)), eq_comm, leftCoset_eq_iff]
      exact hx
  have hidx := MulAction.index_stabilizer (G := K) (⟨_, htY⟩ : d.OmY)
  rw [horb, Set.ncard_range_of_injective hf, hstab] at hidx
  change ((normalizer ((d.withT d.Y : Subgroup G) : Set G)).subgroupOf K).index = 16
  rw [hidx, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, F4.card]
  norm_num

theorem Y_inf_NHA₂ (h : d.Hyp) :
    d.Y ⊓ (normalizer (d.A₂ : Set G) ⊓ d.H) = d.F := by
  refine le_antisymm (fun x hx => ?_) (le_inf h.F_le_Y fun f hf =>
    Subgroup.mem_inf.2 ⟨(d.A₂).le_normalizer (d.F_le_A₂ hf), h.L_le_H (d.pull_le_L _ hf)⟩)
  obtain ⟨hxY, hxN⟩ := Subgroup.mem_inf.1 hx
  exact (h.mem_F_iff_Y x).2 ⟨hxY, mem_centralizer_singleton_iff.1 hxN.2⟩

theorem card_XC₀ (h : d.Hyp) :
    Nat.card d.XC₀ = 256 * Nat.card (normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) := by
  have hTY : normalizer ((d.withT d.Y : Subgroup G) : Set G) =
      (normalizer (d.A₂ : Set G) ⊓ d.H) ⊔ d.Y := h.sec4_7
  have hTX : normalizer ((d.withT d.Y : Subgroup G) : Set G) ≤ d.XC₀ := by
    rw [hTY]
    exact h.NHA₂Y_le_XC₀
  have h16 := h.relIndex_normalizer_withT_Y (K := d.XC₀) le_rfl
    (fun c => h.exists_mem_XC₀_conj_t ⟨_, nfA₂_mem c, rfl⟩)
  have e1 := Subgroup.relIndex_mul_card (normalizer ((d.withT d.Y : Subgroup G) : Set G)) d.XC₀
  rw [inf_of_le_left hTX, h16] at e1
  have e2 := card_sup_mul_card_inf_of_le_normalizer d.Y
    (normalizer (d.A₂ : Set G) ⊓ d.H) h.NHA₂_le_normalizer_Y
  rw [h.Y_inf_NHA₂, sup_comm, ← hTY, h.sec4_6.2.2.2.2.1, d.card_F] at e2
  generalize Nat.card (normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) = N at e2 ⊢
  generalize Nat.card (normalizer ((d.withT d.Y : Subgroup G) : Set G)) = T at e1 e2
  generalize Nat.card d.XC₀ = X at e1 ⊢
  norm_num at e1 e2
  omega

theorem ker_secHomXC₀_eq (h : d.Hyp) (hle : d.XC₀ ≤ normalizer (d.D₀ : Set G)) :
    (d.secHomXC₀ hle).ker = d.UD₀.subgroupOf d.XC₀ := by
  ext x
  rw [h.mem_ker_secHomXC₀_iff hle, mem_subgroupOf]

theorem exists_mem_UD₀_crossed_not_mem_Y (h : d.Hyp) :
    ∃ u ∈ d.UD₀, u * d.t * u⁻¹ * d.t ∉ d.Y := by
  by_contra hno
  push Not at hno
  have hUC : d.UD₀ = d.C₀ := le_antisymm
    (fun u hu => h.mem_C₀_of_mem_UD₀_of_crossed_mem hu (hno u hu)) h.C₀_le_UD₀
  have hle : d.XC₀ ≤ normalizer (d.D₀ : Set G) := h.normalizer_C₀_le_normalizer_D₀
  have hdvd := h.relIndex_UD₀_dvd
  have e1 := Subgroup.relIndex_mul_card d.UD₀ d.XC₀
  have hcU : Nat.card d.UD₀ = 2 ^ 13 := by
    rw [hUC]
    exact h.card_C₀
  rw [inf_of_le_left UD₀_le_XC₀, hcU] at e1
  have hX := h.card_XC₀
  obtain ⟨m, hm⟩ := h.dvd_card_normalizer_inf_H
  rw [h.normalizer_inf_H_eq] at hm
  have hr : d.UD₀.relIndex d.XC₀ = 2880 * m := by
    generalize d.UD₀.relIndex d.XC₀ = r at e1 ⊢
    generalize Nat.card d.XC₀ = X at e1 hX
    generalize Nat.card (normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) = N at hX hm
    norm_num at e1 hX hm
    omega
  have hm7 : m ∣ 7 := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hr] at hk
    exact ⟨k, by nlinarith⟩
  have hm1 : m = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).1 hm7 with h1 | h7
    · exact h1
    · exfalso
      refine h.not_seven_dvd_card_H (Dvd.dvd.trans ?_ (Subgroup.card_dvd_of_le
        (inf_le_right : normalizer (d.A₂ : Set G) ⊓ d.H ≤ d.H)))
      rw [hm, h7]
      exact Dvd.intro_left _ rfl
  rw [hm1, mul_one] at hr
  obtain ⟨hinn_comm, hinn_sq⟩ := innSub_comm_sq d.D₀ mem_Y_iff_D₀
    (fun p hp q hq => h.comm_D₀ hp hq) (fun p hp => h.sq_D₀ hp)
  have hcard := card_innSub d.D₀ mem_Y_iff_D₀ h.card_D₀_eq_mul
  have hAut := card_mulAut_of_elemAb_sixteen hinn_comm hinn_sq hcard
  have : IsSimpleGroup (MulAut (innSub d.D₀)) :=
    isSimpleGroup_mulAut_of_elemAb_sixteen hinn_comm hinn_sq hcard
  have hker : (d.secHomXC₀ hle).ker.index = 2880 := by
    rw [h.ker_secHomXC₀_eq hle]
    exact hr
  have hrange : Nat.card (d.secHomXC₀ hle).range = 2880 := by
    rw [← hker, Subgroup.index_ker]
  have hidx := Subgroup.card_mul_index (d.secHomXC₀ hle).range
  rw [hrange, hAut] at hidx
  have h7 : (d.secHomXC₀ hle).range.index = 7 := by omega
  have htop := eq_top_of_index_le_seven hAut h7.le
  rw [htop, index_top] at h7
  exact absurd h7 (by norm_num)

theorem exists_mem_UD₀_conj_t (h : d.Hyp) {a : G} (ha : a ∈ d.A₂) :
    ∃ u ∈ d.UD₀, (a * d.t)⁻¹ * (u * d.t * u⁻¹) ∈ d.Y := by
  let T : Set SU52 := {α | α ∈ A₂sub ∧ ∃ u ∈ d.UD₀,
    (d.ι α)⁻¹ * (u * d.t * u⁻¹ * d.t) ∈ d.Y}
  have h1 : (1 : SU52) ∈ T := ⟨one_mem _, 1, one_mem _, by simp [h.t_mul_t]⟩
  have hF : ∀ f ∈ Fsub, f ∈ T := fun f hf => ⟨Fsub_le_A₂sub hf, 1, one_mem _, by
    simpa [h.t_mul_t] using inv_mem (h.F_le_Y (⟨f, hf, rfl⟩ : d.ι f ∈ d.F))⟩
  have hmul : ∀ α ∈ T, ∀ β ∈ T, α * β ∈ T := by
    rintro α ⟨hα, u₁, hu₁, h₁⟩ β ⟨hβ, u₂, hu₂, h₂⟩
    obtain ⟨w, hw, e⟩ := h.crossed_mul_mem_UD₀ hu₂ (UD₀_le_XC₀ hu₁)
    refine ⟨mul_mem hα hβ, u₂ * u₁, mul_mem hu₂ hu₁, ?_⟩
    have hβD : d.ι β ∈ d.D₀ := h.A₂_le_D₀ ⟨β, hβ, rfl⟩
    have hc : (d.ι β)⁻¹ * (((d.ι α)⁻¹ * (u₁ * d.t * u₁⁻¹ * d.t)) * d.ι β) =
        (d.ι α)⁻¹ * (u₁ * d.t * u₁⁻¹ * d.t) := by
      rw [Y_comm_D₀ h₁ hβD]
      group
    rw [e, map_mul, show (d.ι α * d.ι β)⁻¹ * ((u₁ * d.t * u₁⁻¹ * d.t) * (u₂ * d.t * u₂⁻¹ * d.t) * w) =
      ((d.ι β)⁻¹ * (((d.ι α)⁻¹ * (u₁ * d.t * u₁⁻¹ * d.t)) * d.ι β)) *
        ((d.ι β)⁻¹ * (u₂ * d.t * u₂⁻¹ * d.t)) * w by group, hc]
    exact mul_mem (mul_mem h₁ h₂) hw
  have hK : ∀ n ∈ K₂sub, ∀ α ∈ T, n * α * n⁻¹ ∈ T := by
    rintro n hn α ⟨hα, u, hu, hθ⟩
    have hmN : d.ι n ∈ normalizer (d.A₂ : Set G) ⊓ d.H :=
      ⟨ι_mem_normalizer_pull (K₂sub_le_normalizer_A₂sub hn), h.L_le_H (d.ι_mem n)⟩
    have hmX : d.ι n ∈ d.XC₀ := h.NHA₂_le_XC₀ hmN
    refine ⟨(mem_normalizer_iff.1 (K₂sub_le_normalizer_A₂sub hn) α).1 hα,
      d.ι n * u * (d.ι n)⁻¹, h.conj_mem_UD₀ hmX hu, ?_⟩
    rw [crossed_conj_of_mem_H (d := d) hmN.2, map_mul, map_mul, map_inv,
      show (d.ι n * d.ι α * (d.ι n)⁻¹)⁻¹ * (d.ι n * (u * d.t * u⁻¹ * d.t) * (d.ι n)⁻¹) =
        d.ι n * ((d.ι α)⁻¹ * (u * d.t * u⁻¹ * d.t)) * (d.ι n)⁻¹ by group]
    exact (mem_normalizer_iff.1 (h.NHA₂_le_normalizer_Y hmN) _).1 hθ
  obtain ⟨u₀, hu₀, hθ₀⟩ := h.exists_mem_UD₀_crossed_not_mem_Y
  obtain ⟨a₀, ha₀, y₀, hy₀, e₀⟩ := (h.mem_A₂E₂_iff).1
    (h.D₀_eq ▸ h.crossed_mem_D₀ (UD₀_le_XC₀ hu₀))
  have hy₀Y : y₀ ∈ d.Y := h.Y_eq_E₂ ▸ hy₀
  have ha₀F : a₀ ∉ d.F := fun hF => hθ₀ (by rw [e₀]; exact mul_mem (h.F_le_Y hF) hy₀Y)
  obtain ⟨α₀, hα₀, rfl⟩ := ha₀
  have hα₀T : α₀ ∈ T := ⟨hα₀, u₀, hu₀, by rw [e₀, inv_mul_cancel_left]; exact hy₀Y⟩
  obtain ⟨α, hα, rfl⟩ := ha
  have hαT : α ∈ T := by
    by_cases hαF : α ∈ Fsub
    · exact hF α hαF
    obtain ⟨n, hn, hnF⟩ := exists_K₂sub_conj_mem hα₀ (fun hF => ha₀F ⟨α₀, hF, rfl⟩) hα hαF
    have hβ := hK n hn α₀ hα₀T
    have hf : (n * α₀ * n⁻¹)⁻¹ * α ∈ Fsub := by
      have := inv_mem hnF
      rwa [show (α⁻¹ * (n * α₀ * n⁻¹))⁻¹ = (n * α₀ * n⁻¹)⁻¹ * α by group] at this
    have := hmul _ hβ _ (hF _ hf)
    rwa [mul_inv_cancel_left] at this
  obtain ⟨-, u, hu, hθ⟩ := hαT
  exact ⟨u, hu, (h.coset_mem_Y_iff _ u).2 hθ⟩

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
