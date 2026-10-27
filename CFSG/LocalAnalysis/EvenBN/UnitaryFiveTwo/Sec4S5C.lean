module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S5B

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

@[expose] def Data.P₀ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  ((normalizer (d.R₃ : Set G) ⊓ centralizer (d.W : Set G)) ⊓ cenMod d.V₃ d.S₃) ⊓
    normalizer (d.Y : Set G)

theorem Data.mem_P₀ {G : Type} [Group G] {d : Data G} {x : G} :
    x ∈ d.P₀ ↔ x ∈ normalizer (d.R₃ : Set G) ∧ x ∈ centralizer (d.W : Set G) ∧
      x ∈ cenMod d.V₃ d.S₃ ∧ x ∈ normalizer (d.Y : Set G) := by
  simp only [Data.P₀, Subgroup.mem_inf, and_assoc]

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_R_of_comm_mod_commutator_S (h : d.Hyp) {n : G} (hnS : n ∈ normalizer (d.S : Set G))
    (hnH : n ∈ d.H) (hc : ∀ s ∈ d.S, n * s * n⁻¹ * s⁻¹ ∈ ⁅d.S, d.S⁆) : n ∈ d.R := by
  set φ : MulAut SU52 := h.act ⟨n, hnH⟩ with hφ
  have hφι : ∀ g, d.ι (φ g) = n * d.ι g * n⁻¹ := fun g => h.ι_act_apply ⟨n, hnH⟩ g
  have hφS : ∀ g ∈ Ssub, φ g ∈ Ssub := fun g hg => by
    have : d.ι (φ g) ∈ d.S := by
      rw [hφι]
      exact (mem_normalizer_iff.1 hnS _).1 ⟨g, hg, rfl⟩
    exact d.ι_mem_pull_iff.1 this
  have hφtriv : ∀ g ∈ Ssub, g⁻¹ * φ g ∈ ⁅Ssub, Ssub⁆ := fun g hg => by
    have hg' : d.ι g ∈ d.S := ⟨g, hg, rfl⟩
    have h1 := (mem_normalizer_iff.1 (le_normalizer_commutator_left' d.S d.S (inv_mem hg')) _).1
      (hc _ hg')
    have h2 : d.ι (g⁻¹ * φ g) ∈ ⁅d.S, d.S⁆ := by
      rw [map_mul, map_inv, hφι]
      rw [show (d.ι g)⁻¹ * (n * d.ι g * n⁻¹) =
        (d.ι g)⁻¹ * (n * d.ι g * n⁻¹ * (d.ι g)⁻¹) * (d.ι g)⁻¹⁻¹ by group]
      exact h1
    rw [← pull_commutator_Ssub (d := d)] at h2
    exact d.ι_mem_pull_iff.1 h2
  obtain ⟨s₀, hs₀ | hs₀⟩ := exists_eq_conj_or_eq_conj_mul_fld φ
  · have hs₀N : s₀ ∈ normalizer (Ssub : Set SU52) := mem_normalizer_fintype fun x hx => by
      have := hφS x hx
      rwa [hs₀, MulAut.conj_apply] at this
    have hs₀S : s₀ ∈ Ssub := mem_Ssub_of_conj_mem_commutator hs₀N fun x hx => by
      have := hφtriv x hx
      rwa [hs₀, MulAut.conj_apply] at this
    have hx1 : h.act ⟨(d.ι s₀)⁻¹ * n, mul_mem (inv_mem (h.L_le_H (d.ι_mem s₀))) hnH⟩ = 1 := by
      refine MulEquiv.ext fun g => d.ι_injective ?_
      show d.ι (h.act _ g) = d.ι g
      rw [h.ι_act_apply]
      have e1 : n * d.ι g * n⁻¹ = d.ι s₀ * d.ι g * (d.ι s₀)⁻¹ := by
        rw [← hφι g, hs₀, MulAut.conj_apply]
        simp only [map_mul, map_inv]
      change (d.ι s₀)⁻¹ * n * d.ι g * ((d.ι s₀)⁻¹ * n)⁻¹ = d.ι g
      calc (d.ι s₀)⁻¹ * n * d.ι g * ((d.ι s₀)⁻¹ * n)⁻¹ =
          (d.ι s₀)⁻¹ * (n * d.ι g * n⁻¹) * d.ι s₀ := by group
        _ = d.ι g := by rw [e1]; group
    have hC := (h.act_eq_one_iff _).1 hx1
    have hC' : (d.ι s₀)⁻¹ * n ∈ centralizer (d.L : Set G) ⊓ d.H :=
      Subgroup.mem_inf.2 ⟨hC, mul_mem (inv_mem (h.L_le_H (d.ι_mem s₀))) hnH⟩
    rw [h.centralizer_inf_H_eq] at hC'
    have e : n = d.ι s₀ * ((d.ι s₀)⁻¹ * n) := by group
    rw [e]
    exact mul_mem (mem_sup_left (⟨s₀, hs₀S, rfl⟩ : d.ι s₀ ∈ d.S)) (mem_sup_right hC')
  · exfalso
    refine not_conj_fld_trivial_mod_commutator (s := s₀) (fun x hx => ?_) fun x hx => ?_
    · have := hφS x hx
      rwa [hs₀, MulAut.mul_apply, MulAut.conj_apply] at this
    · have := hφtriv x hx
      rwa [hs₀, MulAut.mul_apply, MulAut.conj_apply] at this

theorem S₃_le_P₀ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.S₃ ≤ d.P₀ := fun x hx =>
  Data.mem_P₀.2 ⟨d.R₃.le_normalizer (S₃_le_R₃ hx), S₃_le_centralizer_W hx,
    ⟨h.S₃_le_normalizer_V₃ hx, fun m hm => h.commutator_mem_V₃_of_mem_S₃ hK hx hm⟩,
    h.S₃_le_normalizer_Y hx⟩

theorem D₂_le_P₀ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.D₂ ≤ d.P₀ := fun x hx =>
  Data.mem_P₀.2 ⟨h.D₂_le_normalizer_R₃ hx, h.D₂_le_centralizer_W hx, h.D₂_le_cenMod_V₃_S₃ hK hx,
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' hx hy).symm⟩

theorem D₁_le_P₀ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) : d.D₁ ≤ d.P₀ := fun x hx =>
  Data.mem_P₀.2 ⟨h.D₁_le_normalizer_R₃ hKY hx, (Subgroup.mem_inf.1 hx).2,
    h.D₁_le_cenMod_V₃_S₃ hK hKY hx, h.D₁_le_normalizer_Y hKY hx⟩

theorem t_conj_mem_S₃ (h : d.Hyp) {k : G} (hk : k ∈ d.S₃) : d.t * k * d.t ∈ d.S₃ := by
  have hk' : k ∈ (d.S ⊔ d.Y) ⊔ d.D₃ := by rwa [h.S₃_eq] at hk
  have := (mem_normalizer_iff.1 h.t_mem_normalizer_SYD₃ k).1 hk'
  rw [h.t_inv, ← h.S₃_eq] at this
  exact this

theorem theta_mem_S₃ (h : d.Hyp) {x : G} (hx : x ∈ d.P₀) : x * d.t * x⁻¹ * d.t ∈ d.S₃ := by
  obtain ⟨hxR, hxC, -, -⟩ := Data.mem_P₀.1 hx
  have htR : d.t ∈ d.R₃ := h.R_le_R₃ (mem_sup_right (mem_zpowers _))
  have hy : x * d.t * x⁻¹ ∈ d.R₃ := (mem_normalizer_iff.1 hxR _).1 htR
  rw [h.R₃_eq_S₃_sup] at hy
  rcases (mem_sup_zpowers_iff h.t_mul_t fun k hk => h.t_conj_mem_S₃ hk).1 hy with h1 | h1
  · exfalso
    apply h.t_not_mem_centralizer_W
    refine mem_centralizer_iff.2 fun w hw => ?_
    have h2 := mem_centralizer_iff.1 (S₃_le_centralizer_W h1) w hw
    have h3 := mem_centralizer_iff.1 hxC w hw
    have hxw : x * w * x⁻¹ = w := by rw [← h3, mul_inv_cancel_right]
    have e : x * (w * d.t) * x⁻¹ = x * (d.t * w) * x⁻¹ := by
      calc x * (w * d.t) * x⁻¹ = (x * w * x⁻¹) * (x * d.t * x⁻¹) := by group
        _ = w * (x * d.t * x⁻¹) := by rw [hxw]
        _ = (x * d.t * x⁻¹) * w := h2
        _ = (x * d.t * x⁻¹) * (x * w * x⁻¹) := by rw [hxw]
        _ = x * (d.t * w) * x⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e)
  · exact h1

theorem theta_mul_mem_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {x y : G} (hx : x ∈ d.P₀) (hy : y ∈ d.P₀) :
    ((x * d.t * x⁻¹ * d.t) * (y * d.t * y⁻¹ * d.t))⁻¹ * (x * y * d.t * (x * y)⁻¹ * d.t) ∈ d.V₃ := by
  have ha := h.theta_mem_S₃ hx
  have hb := h.theta_mem_S₃ hy
  obtain ⟨-, -, ⟨hxN, hxc⟩, -⟩ := Data.mem_P₀.1 hx
  have hc₁ : x * (y * d.t * y⁻¹ * d.t) * x⁻¹ * (y * d.t * y⁻¹ * d.t)⁻¹ ∈ d.V₃ := hxc _ hb
  rw [h.crossed_mul_eq x y]
  have e : ((x * d.t * x⁻¹ * d.t) * (y * d.t * y⁻¹ * d.t))⁻¹ *
      (x * (y * d.t * y⁻¹ * d.t) * x⁻¹ * (x * d.t * x⁻¹ * d.t)) =
      (((x * d.t * x⁻¹ * d.t) * (y * d.t * y⁻¹ * d.t))⁻¹ *
        (x * (y * d.t * y⁻¹ * d.t) * x⁻¹ * (y * d.t * y⁻¹ * d.t)⁻¹) *
        ((x * d.t * x⁻¹ * d.t) * (y * d.t * y⁻¹ * d.t))⁻¹⁻¹) *
      ((y * d.t * y⁻¹ * d.t)⁻¹ * (x * d.t * x⁻¹ * d.t)⁻¹ * (y * d.t * y⁻¹ * d.t) *
        (x * d.t * x⁻¹ * d.t)) := by group
  rw [e]
  refine mul_mem (h.conj_mem_V₃ (inv_mem (mul_mem ha hb)) hc₁) ?_
  have := h.commutator_mem_V₃_of_mem_S₃ hK (inv_mem hb) (inv_mem ha)
  rwa [inv_inv, inv_inv] at this

theorem theta_mem_V₃_of_mem_S₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {s : G} (hs : s ∈ d.S₃) :
    s * d.t * s⁻¹ * d.t ∈ d.V₃ := by
  have hset := coe_mul_of_left_le_normalizer_right d.S d.V₃ fun g hg => h.S_le_normalizer_V₃ hg
  rw [h.S₃_eq_S_sup_V₃ hK] at hs
  obtain ⟨s₀, hs₀, v, hv, rfl⟩ : s ∈ (d.S : Set G) * (d.V₃ : Set G) := by
    rw [← hset]
    exact hs
  have hH : s₀ ∈ d.H := h.R_le_H (mem_sup_left hs₀)
  rw [crossed_mul_of_mem_H hH]
  exact h.conj_mem_V₃ (h.S_le_S₃ hs₀) (h.commutator_S_sup_W_le_V₃ (h.crossed_V₃_mem hK hv))

theorem mem_S₃_of_theta_mem_V₃ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x : G} (hx : x ∈ d.P₀)
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.V₃) : x ∈ d.S₃ := by
  obtain ⟨-, hxC, ⟨hxN, hxc⟩, -⟩ := Data.mem_P₀.1 hx
  have hxT : x ∈ normalizer ((d.V₃ ⊔ zpowers d.t : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun y hy => ?_
    have hle : d.V₃ ⊔ zpowers d.t ≤ (d.V₃ ⊔ zpowers d.t).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun v hv => ?_) (zpowers_le.2 ?_)
      · exact mem_sup_left ((mem_normalizer_iff.1 hxN v).1 hv)
      · change x * d.t * x⁻¹ ∈ d.V₃ ⊔ zpowers d.t
        rw [show x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t) * d.t by
          rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
        exact mul_mem (mem_sup_left hθ) (mem_sup_right (mem_zpowers _))
    exact hle hy
  rw [h.normalizer_withT_V₃ hK] at hxT
  have hNV : normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.V₃ : Set G) := fun n hn =>
    h.mem_normalizer_V₃ (h.NHS_le_normalizer_S₃ hn) (h.NHS_le_normalizer_Y hn)
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.S : Set G) ⊓ d.H) d.V₃ hNV
  obtain ⟨n, hn, v, hv, hnv⟩ : x ∈ ((normalizer (d.S : Set G) ⊓ d.H : Subgroup G) : Set G) *
      (d.V₃ : Set G) := by
    rw [← hset]
    exact hxT
  have hxnv : x = n * v := hnv.symm
  have hnS : n ∈ normalizer (d.S : Set G) := (Subgroup.mem_inf.1 hn).1
  have hnH : n ∈ d.H := (Subgroup.mem_inf.1 hn).2
  have hn_x : n = x * v⁻¹ := by rw [hxnv]; group
  have hc : ∀ s ∈ d.S, n * s * n⁻¹ * s⁻¹ ∈ ⁅d.S, d.S⁆ := fun s hs => by
    have hs₃ := h.S_le_S₃ hs
    have z1 : s⁻¹ * v⁻¹ * s * v ∈ d.V₃ := by
      have := h.conj_mem_V₃ (inv_mem hs₃) (inv_mem hv)
      rw [inv_inv] at this
      exact mul_mem this hv
    have hV : n * s * n⁻¹ * s⁻¹ ∈ d.V₃ := by
      have e : n * s * n⁻¹ * s⁻¹ = (x * s * x⁻¹ * s⁻¹) *
          (s * (x * (s⁻¹ * v⁻¹ * s * v) * x⁻¹) * s⁻¹) := by rw [hn_x]; group
      rw [e]
      exact mul_mem (hxc s hs₃) (h.conj_mem_V₃ hs₃ ((mem_normalizer_iff.1 hxN _).1 z1))
    have hS : n * s * n⁻¹ * s⁻¹ ∈ d.S := mul_mem ((mem_normalizer_iff.1 hnS s).1 hs) (inv_mem hs)
    have : n * s * n⁻¹ * s⁻¹ ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨hS, hV⟩
    rwa [h.S_inf_V₃] at this
  have hnR : n ∈ d.S ⊔ zpowers d.t := h.mem_R_of_comm_mod_commutator_S hnS hnH hc
  have hnC : n ∈ centralizer (d.W : Set G) := by
    have := mul_mem hxC (inv_mem (V₃_le_centralizer_W hv))
    rwa [← hn_x] at this
  have htS : ∀ k ∈ d.S, d.t * k * d.t ∈ d.S := fun k hk => by
    have hkt : k * d.t = d.t * k :=
      mem_centralizer_singleton_iff.1 (h.R_le_H (mem_sup_left hk))
    rw [← hkt, mul_assoc, h.t_mul_t, mul_one]
    exact hk
  have hnS' : n ∈ d.S := by
    rcases (mem_sup_zpowers_iff h.t_mul_t htS).1 hnR with h1 | h1
    · exact h1
    · exfalso
      apply h.t_not_mem_centralizer_W
      have := mul_mem (inv_mem hnC) (S_le_centralizer_W h1)
      rwa [inv_mul_cancel_left] at this
  rw [h.S₃_eq_S_sup_V₃ hK, hxnv]
  exact mul_mem (mem_sup_left hnS') (mem_sup_right hv)

theorem S₃_le_D₁_sup_D₂ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.S₃ ≤ d.D₁ ⊔ d.D₂ := by
  rw [h.S₃_eq_S_sup_V₃ hK, S_eq_A₁_sup_A₂]
  exact sup_le (sup_le (h.A₁_le_D₁.trans le_sup_left) (h.A₂_le_D₂'.trans le_sup_right))
    ((h.V₃_le_D₂ hK).trans le_sup_right)

theorem P₀_eq_and_card (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    (hKY : ∀ m ∈ d.M, m ∈ normalizer (d.Y : Set G)) :
    d.P₀ = d.D₁ ⊔ d.D₂ ∧ Nat.card d.P₀ = 2 ^ 20 ∧
      ∀ x ∈ d.P₀, ∀ y ∈ d.P₀, x * y * x⁻¹ * y⁻¹ ∈ d.S₃ := by
  haveI : (d.V₃.subgroupOf d.S₃).Normal :=
    (Subgroup.normal_subgroupOf_iff V₃_le_S₃).2 fun v g hv hg => h.conj_mem_V₃ hg hv
  let ψ : d.P₀ →* d.S₃ ⧸ d.V₃.subgroupOf d.S₃ :=
    MonoidHom.mk' (fun x => QuotientGroup.mk
      ⟨(x : G) * d.t * (x : G)⁻¹ * d.t, h.theta_mem_S₃ x.2⟩) (fun x y => by
      rw [← QuotientGroup.mk_mul]
      refine Eq.symm (QuotientGroup.eq.2 ?_)
      rw [Subgroup.mem_subgroupOf]
      exact h.theta_mul_mem_V₃ hK x.2 y.2)
  have hker : ∀ x : d.P₀, ψ x = 1 ↔ (x : G) * d.t * (x : G)⁻¹ * d.t ∈ d.V₃ := fun x => by
    show QuotientGroup.mk _ = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hmk : ∀ (g g' : G) (hg : g ∈ d.S₃) (hg' : g' ∈ d.S₃), g⁻¹ * g' ∈ d.V₃ →
      (QuotientGroup.mk (⟨g, hg⟩ : ↥d.S₃) : d.S₃ ⧸ d.V₃.subgroupOf d.S₃) =
        QuotientGroup.mk ⟨g', hg'⟩ := fun g g' hg hg' hv =>
    QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hv)
  have hsurj : ∀ g : ↥d.S₃, ∃ π : d.P₀, (π : G) ∈ d.D₁ ⊔ d.D₂ ∧
      ψ π = QuotientGroup.mk g := by
    rintro ⟨g, hg⟩
    have hset₁ := coe_mul_of_left_le_normalizer_right d.S d.V₃ fun g hg =>
      h.S_le_normalizer_V₃ hg
    have hA₁N : d.A₁ ≤ normalizer (d.A₂ : Set G) := fun a ha =>
      normalizer_S_le_normalizer_A₂ (d.S.le_normalizer (d.A₁_le_S ha))
    have hset₂ := coe_mul_of_left_le_normalizer_right d.A₁ d.A₂ hA₁N
    have hg' : g ∈ d.S ⊔ d.V₃ := by rwa [h.S₃_eq_S_sup_V₃ hK] at hg
    obtain ⟨s, hs, v, hv, hsv⟩ : g ∈ (d.S : Set G) * (d.V₃ : Set G) := by
      rw [← hset₁]
      exact hg'
    have hs' : s ∈ d.A₁ ⊔ d.A₂ := by rwa [S_eq_A₁_sup_A₂] at hs
    obtain ⟨a₁, ha₁, a₂, ha₂, ha₁₂⟩ : s ∈ (d.A₁ : Set G) * (d.A₂ : Set G) := by
      rw [← hset₂]
      exact hs'
    obtain ⟨u, hu, w, hw, huw⟩ := h.sec4_11_2.2.1 a₁ ha₁
    obtain ⟨u', hu', y, hy, hu'y⟩ := h.sec4_15_2.2.1 a₂ (h.A₂_le_D₀ ha₂)
    have h₁ : ψ ⟨u, h.D₁_le_P₀ hK hKY hu⟩ =
        QuotientGroup.mk ⟨a₁, h.S_le_S₃ (d.A₁_le_S ha₁)⟩ := by
      show QuotientGroup.mk _ = _
      refine hmk _ _ _ _ ?_
      rw [huw, mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem (h.W_le_V₃ hw)
    have h₂ : ψ ⟨u', h.D₂_le_P₀ hK hu'⟩ =
        QuotientGroup.mk ⟨a₂, h.S_le_S₃ (d.A₂_le_S ha₂)⟩ := by
      show QuotientGroup.mk _ = _
      refine hmk _ _ _ _ ?_
      rw [hu'y, mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem (h.Y_le_V₃ hy)
    refine ⟨⟨u, h.D₁_le_P₀ hK hKY hu⟩ * ⟨u', h.D₂_le_P₀ hK hu'⟩,
      mul_mem (mem_sup_left hu) (mem_sup_right hu'), ?_⟩
    rw [map_mul, h₁, h₂, ← QuotientGroup.mk_mul]
    refine hmk _ _ _ _ ?_
    change (a₁ * a₂)⁻¹ * g ∈ d.V₃
    have hsv' : s * v = g := hsv
    have ha₁₂' : a₁ * a₂ = s := ha₁₂
    rw [← hsv', ← ha₁₂', inv_mul_cancel_left]
    exact hv
  have hS₃P : d.S₃ ≤ d.P₀ := h.S₃_le_P₀ hK
  have hPi : d.D₁ ⊔ d.D₂ ≤ d.P₀ := sup_le (h.D₁_le_P₀ hK hKY) (h.D₂_le_P₀ hK)
  have hS₃Pi : d.S₃ ≤ d.D₁ ⊔ d.D₂ := h.S₃_le_D₁_sup_D₂ hK
  have hP : d.P₀ = d.D₁ ⊔ d.D₂ := by
    refine le_antisymm (fun x hx => ?_) hPi
    obtain ⟨π, hπPi, hπ⟩ := hsurj ⟨x * d.t * x⁻¹ * d.t, h.theta_mem_S₃ hx⟩
    have hψx : ψ ⟨x, hx⟩ = QuotientGroup.mk ⟨x * d.t * x⁻¹ * d.t, h.theta_mem_S₃ hx⟩ := rfl
    have h1 : ψ (π⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hπ, ← hψx, inv_mul_cancel]
    have h2 := (hker _).1 h1
    have h3 : ((π : G))⁻¹ * x ∈ d.S₃ := h.mem_S₃_of_theta_mem_V₃ hK (π⁻¹ * ⟨x, hx⟩).2 h2
    have h4 := hS₃Pi h3
    have e : x = (π : G) * ((π : G)⁻¹ * x) := by group
    rw [e]
    exact mul_mem hπPi h4
  have hQ : ∀ q q' : d.S₃ ⧸ d.V₃.subgroupOf d.S₃, q * q' * q⁻¹ * q'⁻¹ = 1 := by
    intro q q'
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective q'
    have hm : (QuotientGroup.mk (g * g' * g⁻¹ * g'⁻¹) : d.S₃ ⧸ d.V₃.subgroupOf d.S₃) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h.commutator_mem_V₃_of_mem_S₃ hK g.2 g'.2
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using hm
  have hcomm : ∀ x ∈ d.P₀, ∀ y ∈ d.P₀, x * y * x⁻¹ * y⁻¹ ∈ d.S₃ := fun x hx y hy => by
    have h1 : ψ (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hQ _ _
    exact h.mem_S₃_of_theta_mem_V₃ hK
      (mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) ((hker _).1 h1)
  refine ⟨hP, ?_, hcomm⟩
  have hkerS : ψ.ker = d.S₃.subgroupOf d.P₀ := by
    ext x
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    exact ⟨h.mem_S₃_of_theta_mem_V₃ hK x.2, h.theta_mem_V₃_of_mem_S₃ hK⟩
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨π, -, hπ⟩ := hsurj g
    exact ⟨π, hπ⟩
  have e1 := card_eq_card_ker_mul_card_range ψ
  rw [hkerS, hrange, Subgroup.card_top] at e1
  have e2 : Nat.card (d.S₃.subgroupOf d.P₀) = 2 ^ 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₃P).toEquiv, h.card_S₃]
  have e3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.V₃.subgroupOf d.S₃)
  have e4 : Nat.card (d.V₃.subgroupOf d.S₃) = 2 ^ 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe V₃_le_S₃).toEquiv, h.card_V₃ hK]
  have e5 : Nat.card d.S₃ = 2 ^ 16 := h.card_S₃
  rw [e5, e4] at e3
  rw [e1, e2]
  omega

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
