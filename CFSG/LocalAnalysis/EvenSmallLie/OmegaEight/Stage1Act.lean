module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Setup
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Perm

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

namespace RadicalData

variable {ε : Eps} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hR : RadicalData ε L U Q P a ψ p)

@[expose] noncomputable def linHom : normalizer (Q : Set G) →* Equiv.Perm V6 where
  toFun g :=
    { toFun := lin ψ g
      invFun := lin ψ (g : G)⁻¹
      left_inv := hR.lin_inv' g.2
      right_inv := hR.lin_inv g.2 }
  map_one' := Equiv.ext hR.lin_one
  map_mul' g h := Equiv.ext (hR.lin_mul g.2 h.2)

theorem linHom_mem_linGroup (g : normalizer (Q : Set G)) : hR.linHom g ∈ linGroup :=
  fun v w => hR.lin_add g.2 v w

end RadicalData

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
include hS

theorem conj_mem_Zset {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    {v : V6} (hv : v ∈ Zset t Q ψ) : ∃ w ∈ Zset t Q ψ, g * (t * ψ v) * g⁻¹ = t * ψ w := by
  obtain ⟨h, hh, hht⟩ := hv
  obtain ⟨w, hw⟩ := hS.conj_t_eq (mul_mem hg hh)
  refine ⟨w, ⟨g * h, mul_mem hg hh, hw⟩, ?_⟩
  rw [← hht, ← hw]
  group

theorem normalizer_E_le (hsum : ∀ w, ∃ v ∈ Zset t Q ψ, ∃ v' ∈ Zset t Q ψ, v + v' = w) :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G) := by
  have hprod : ∀ v v', ψ (v + v') = t * ψ v * (t * ψ v') := by
    intro v v'
    rw [hS.rad.ψ_add, mul_assoc t, ← mul_assoc (ψ v), hS.commute_ψ v, ← mul_assoc,
      ← mul_assoc, hS.shape.mul_self, one_mul]
  have key : ∀ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), ∀ x ∈ Q,
      g * x * g⁻¹ ∈ Q := by
    intro g hg x hx
    obtain ⟨w, rfl⟩ := hS.rad.mem_ψ x hx
    obtain ⟨v, hv, v', hv', rfl⟩ := hsum w
    obtain ⟨u, -, hu⟩ := hS.conj_mem_Zset hg hv
    obtain ⟨u', -, hu'⟩ := hS.conj_mem_Zset hg hv'
    have : g * ψ (v + v') * g⁻¹ = ψ (u + u') := by
      rw [hprod, hprod, ← hu, ← hu']
      group
    rw [this]
    exact hS.rad.ψ_mem _
  intro g hg
  refine mem_normalizer_iff.2 fun x => ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end Setup

@[expose] noncomputable def affF (t : G) (ψ : V6 → G) (g : G) (v : V6) : V6 :=
  coord ψ (t * (g * (t * ψ v) * g⁻¹))

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
  (hNQ : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) ≤ normalizer (Q : Set G))
include hS hNQ

theorem t_affF {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    t * ψ (affF t ψ g v) = g * (t * ψ v) * g⁻¹ := by
  have hmem : t * (g * (t * ψ v) * g⁻¹) ∈ Q := by
    obtain ⟨w, hw⟩ := hS.conj_t_eq hg
    have h1 : t * (g * (t * ψ v) * g⁻¹) = ψ w * (g * ψ v * g⁻¹) :=
      calc t * (g * (t * ψ v) * g⁻¹) = t * (g * t * g⁻¹) * (g * ψ v * g⁻¹) := by group
        _ = t * (t * ψ w) * (g * ψ v * g⁻¹) := by rw [hw]
        _ = (t * t) * ψ w * (g * ψ v * g⁻¹) := by group
        _ = ψ w * (g * ψ v * g⁻¹) := by rw [hS.shape.mul_self, one_mul]
    rw [h1]
    exact mul_mem (hS.rad.ψ_mem w) (hS.rad.conj_mem_Q (hNQ hg) v)
  rw [affF, hS.rad.ψ_coord hmem, ← mul_assoc, hS.shape.mul_self, one_mul]

theorem affF_eq_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v w : V6) : affF t ψ g v = w ↔ g * (t * ψ v) * g⁻¹ = t * ψ w := by
  rw [← hS.t_affF hNQ hg]
  constructor
  · rintro rfl; rfl
  · intro h; exact hS.rad.ψ_inj (mul_left_cancel h)

theorem affF_mul {g h : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (hh : h ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    affF t ψ (g * h) v = affF t ψ g (affF t ψ h v) := by
  rw [hS.affF_eq_iff hNQ (mul_mem hg hh), hS.t_affF hNQ hg, hS.t_affF hNQ hh]
  group

theorem affF_one (v : V6) : affF t ψ 1 v = v := by
  rw [hS.affF_eq_iff hNQ (one_mem _)]
  group

theorem affF_eq_add {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v = affF t ψ g 0 + lin ψ g v := by
  rw [hS.affF_eq_iff hNQ hg]
  calc g * (t * ψ v) * g⁻¹ = (g * (t * ψ 0) * g⁻¹) * (g * ψ v * g⁻¹) := by
        rw [hS.rad.ψ_zero]; group
    _ = t * ψ (affF t ψ g 0) * ψ (lin ψ g v) := by
        rw [hS.t_affF hNQ hg, hS.rad.ψ_lin (hNQ hg)]
    _ = t * ψ (affF t ψ g 0 + lin ψ g v) := by rw [hS.rad.ψ_add, mul_assoc]

@[expose] noncomputable def affHom :
    normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →* Equiv.Perm V6 where
  toFun g :=
    { toFun := affF t ψ g
      invFun := affF t ψ (g : G)⁻¹
      left_inv := fun v => by
        rw [← hS.affF_mul hNQ (inv_mem g.2) g.2, inv_mul_cancel, hS.affF_one hNQ]
      right_inv := fun v => by
        rw [← hS.affF_mul hNQ g.2 (inv_mem g.2), mul_inv_cancel, hS.affF_one hNQ] }
  map_one' := Equiv.ext (hS.affF_one hNQ)
  map_mul' g h := Equiv.ext (hS.affF_mul hNQ g.2 h.2)

theorem affHom_apply (g : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) (v : V6) :
    hS.affHom hNQ g v = affF t ψ g v := rfl

theorem affF_mem_Zset_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v ∈ Zset t Q ψ ↔ v ∈ Zset t Q ψ := by
  constructor
  · rintro ⟨h, hh, hht⟩
    refine ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_⟩
    have : g * (t * ψ v) * g⁻¹ = h * t * h⁻¹ := by rw [hht, hS.t_affF hNQ hg]
    calc g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g := by group
      _ = g⁻¹ * (g * (t * ψ v) * g⁻¹) * g := by rw [this]
      _ = t * ψ v := by group
  · rintro ⟨h, hh, hht⟩
    refine ⟨g * h, mul_mem hg hh, ?_⟩
    calc g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
      _ = g * (t * ψ v) * g⁻¹ := by rw [hht]
      _ = t * ψ (affF t ψ g v) := (hS.t_affF hNQ hg v).symm

theorem affF_eq_self_iff {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    (∀ v, affF t ψ g v = v) ↔ g ∈ (Q ⊔ zpowers t : Subgroup G) := by
  constructor
  · intro h
    have hc : ∀ v, g * (t * ψ v) * g⁻¹ = t * ψ v := fun v => (hS.affF_eq_iff hNQ hg v v).1 (h v)
    have ht : g * t * g⁻¹ = t := by simpa [hS.rad.ψ_zero] using hc 0
    have hq : ∀ v, g * ψ v * g⁻¹ = ψ v := by
      intro v
      have h1 := hc v
      have h2 : g * (t * ψ v) * g⁻¹ = (g * t * g⁻¹) * (g * ψ v * g⁻¹) := by group
      rw [h2, ht] at h1
      exact mul_left_cancel h1
    rw [← hS.centralizer_E]
    refine mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hy
    · calc ψ v * g = g * ψ v * g⁻¹ * g := by rw [hq]
        _ = g * ψ v := by group
    · calc t * ψ v * g = g * (t * ψ v) * g⁻¹ * g := by rw [hc]
        _ = g * (t * ψ v) := by group
  · intro hgE v
    rw [hS.affF_eq_iff hNQ hg]
    have hc : (t * ψ v) * g = g * (t * ψ v) := hS.E_comm (mul_mem (t_mem_sup (X := Q))
      (mem_sup_left (hS.rad.ψ_mem v))) hgE
    rw [← hc, mul_inv_cancel_right]

theorem card_range_affHom [Finite G] :
    Nat.card (Q ⊔ zpowers t : Subgroup G) * Nat.card (hS.affHom hNQ).range =
      Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) := by
  have hker : Nat.card (hS.affHom hNQ).ker = Nat.card (Q ⊔ zpowers t : Subgroup G) := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g.1.1, ?_⟩) ⟨fun g h e => ?_, fun x => ?_⟩)
    · exact (hS.affF_eq_self_iff hNQ g.1.2).1 fun v => by
        have := congrArg (fun σ : Equiv.Perm V6 => σ v) (MonoidHom.mem_ker.1 g.2)
        simpa [hS.affHom_apply hNQ] using this
    · simp only [Subtype.mk.injEq] at e
      exact Subtype.ext (Subtype.ext e)
    · have hxN : (x : G) ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
        le_normalizer x.2
      refine ⟨⟨⟨x, hxN⟩, MonoidHom.mem_ker.2 (Equiv.ext fun v => ?_)⟩, rfl⟩
      rw [hS.affHom_apply hNQ]
      exact (hS.affF_eq_self_iff hNQ hxN).2 x.2 v
  rw [← hker, ← Subgroup.index_ker, Subgroup.card_mul_index]

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
