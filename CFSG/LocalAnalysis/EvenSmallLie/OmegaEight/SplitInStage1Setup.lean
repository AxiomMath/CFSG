module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInInputs

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitIn

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type} [Group G]

structure ShapeX (t : G) (L Q K : Subgroup G) : Prop where
  orderOf_eq : orderOf t = 2
  not_mem : t ∉ L
  le_centralizer : L ≤ centralizer ({t} : Set G)
  not_mem_closure_odd : t ∉ closure {g : G | g * t = t * g ∧ Odd (orderOf g)}
  not_square : ∀ h : G, h * h ≠ t
  normalizer_eq : centralizer ({t} : Set G) ⊓ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) =
    K ⊔ zpowers t
  centralizer_eq : centralizer ({t} : Set G) ⊓ centralizer (Q : Set G) = Q ⊔ zpowers t

section ShapeXLemmas

variable {t : G} {L Q K : Subgroup G}

namespace ShapeX

variable (hA : ShapeX t L Q K)
include hA

theorem mul_self : t * t = 1 := by
  rw [← pow_two, ← hA.orderOf_eq, pow_orderOf_eq_one]

theorem inv_eq : t⁻¹ = t := inv_eq_of_mul_eq_one_right hA.mul_self

theorem commute_of_mem {l : G} (hl : l ∈ L) : l * t = t * l :=
  mem_centralizer_singleton_iff.1 (hA.le_centralizer hl)

theorem mem_zpowers_iff {z : G} : z ∈ zpowers t ↔ z = 1 ∨ z = t := by
  constructor
  · rintro ⟨k, rfl⟩
    change t ^ k = 1 ∨ t ^ k = t
    rw [← zpow_mod_orderOf, hA.orderOf_eq]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [Nat.cast_ofNat, h]
    · exact Or.inl (zpow_zero t)
    · exact Or.inr (zpow_one t)
  · rintro (h | h) <;> rw [h]
    · exact one_mem _
    · exact mem_zpowers t

theorem conj_not_mem (hodd : InvolutionsInOddPart L) (g : G) : g * t * g⁻¹ ∉ L := by
  intro hu
  set u : L := ⟨g * t * g⁻¹, hu⟩ with hudef
  have hu2 : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hA.orderOf_eq]
  have hle : closure {y : L | y * u = u * y ∧ Odd (orderOf y)} ≤
      (closure {x : G | x * t = t * x ∧ Odd (orderOf x)}).comap
        (((MulAut.conj g⁻¹).toMonoidHom).comp L.subtype) := by
    rw [closure_le]
    rintro y ⟨hyu, hyo⟩
    have hyu' : (y : G) * (g * t * g⁻¹) = g * t * g⁻¹ * y := congrArg Subtype.val hyu
    refine subset_closure ⟨?_, ?_⟩
    · change g⁻¹ * y * g⁻¹⁻¹ * t = t * (g⁻¹ * y * g⁻¹⁻¹)
      rw [inv_inv]
      calc g⁻¹ * y * g * t = g⁻¹ * ((y : G) * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * t * g⁻¹ * y) * g := by rw [hyu']
        _ = t * (g⁻¹ * y * g) := by group
    · change Odd (orderOf (MulAut.conj g⁻¹ (y : G)))
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
      exact hyo
  have h := hle (hodd u hu2)
  rw [mem_comap, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, hudef,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
  apply hA.not_mem_closure_odd
  convert h using 1
  group

theorem commute_sup {X : Subgroup G} (hXL : X ≤ L) : ∀ u ∈ X, ∀ c ∈ zpowers t, u * c = c * u := by
  intro u hu c hc
  rcases hA.mem_zpowers_iff.1 hc with rfl | rfl
  · rw [mul_one, one_mul]
  · exact hA.commute_of_mem (hXL hu)

theorem mem_sup_iff {X : Subgroup G} (hXL : X ≤ L) {x : G} :
    x ∈ X ⊔ zpowers t ↔ ∃ u ∈ X, x = u ∨ x = u * t := by
  constructor
  · intro hx
    obtain ⟨u, hu, z, hz, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (hA.commute_sup hXL) hx
    rcases hA.mem_zpowers_iff.1 hz with rfl | rfl
    · exact ⟨u, hu, Or.inl (mul_one u)⟩
    · exact ⟨u, hu, Or.inr rfl⟩
  · rintro ⟨u, hu, rfl | rfl⟩
    · exact mem_sup_left hu
    · exact mul_mem (mem_sup_left hu) (mem_sup_right (mem_zpowers t))

theorem relIndex_sup {X : Subgroup G} (hXL : X ≤ L) : X.relIndex (X ⊔ zpowers t) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨t, t_mem_sup, fun b hb => ?_⟩
  obtain ⟨u, hu, rfl | rfl⟩ := (hA.mem_sup_iff hXL).1 hb
  · refine Or.inr ⟨hu, fun h => hA.not_mem (hXL (by simpa using X.mul_mem (X.inv_mem hu) h))⟩
  · rw [mul_assoc, hA.mul_self, mul_one]
    refine Or.inl ⟨hu, fun h => hA.not_mem (hXL (by simpa using X.mul_mem (X.inv_mem hu) h))⟩

theorem card_sup [Finite G] {X : Subgroup G} (hXL : X ≤ L) :
    Nat.card (X ⊔ zpowers t : Subgroup G) = 2 * Nat.card X := by
  rw [← Subgroup.relIndex_mul_card (H := X) (K := X ⊔ zpowers t), hA.relIndex_sup hXL,
    inf_of_le_left le_sup_left]

end ShapeX

end ShapeXLemmas

structure SetupX (ε : Eps) (t : G) (L H₀ U Q P : Subgroup G) (a : G) (ψ : V6 → G)
    (p u : Fin 6 → G) (x₀ : G) : Prop where
  shape : ShapeX t L Q (P ⊔ zpowers x₀)
  rad : RadicalData ε L U Q P a ψ p
  inputs : Inputs ε t L H₀ U Q P a ψ p u x₀
  normalizes_L : centralizer ({t} : Set G) ≤ normalizer (L : Set G)

theorem SetupX.of_inputs {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
    {p u : Fin 6 → G} {x₀ : G} (hK : Stage0.StepK t L) (hI : Inputs ε t L H₀ U Q P a ψ p u x₀) :
    SetupX ε t L H₀ U Q P a ψ p u x₀ where
  shape :=
    { orderOf_eq := hK.orderOf_eq
      not_mem := hK.not_mem
      le_centralizer := hK.le_centralizer
      not_mem_closure_odd := hI.setting.shape.not_mem_closure_odd
      not_square := Stage0.not_square_of_shapeSplit hI.setting.shape
      normalizer_eq := hI.normalizer_E hK
      centralizer_eq := le_antisymm hI.setting.data.centralizer_Q (sup_le
        (fun _ hq => ⟨hK.le_centralizer (hI.setting.rad.Q_le_L hq),
          mem_centralizer_iff.2 fun _ hy => hI.setting.rad.Q_comm hy hq⟩)
        (zpowers_le.2 ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_iff.2 fun _ hy =>
          hK.commute_of_mem (hI.setting.rad.Q_le_L hy)⟩)) }
  rad := hI.setting.rad
  inputs := hI
  normalizes_L := hK.le_normalizer

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
include hS

theorem commute_ψ (v : V6) : ψ v * t = t * ψ v :=
  hS.shape.commute_of_mem (hS.rad.Q_le_L (hS.rad.ψ_mem v))

theorem mem_E_iff {x : G} : x ∈ Q ⊔ zpowers t ↔ ∃ v, x = ψ v ∨ x = t * ψ v := by
  rw [hS.shape.mem_sup_iff hS.rad.Q_le_L]
  constructor
  · rintro ⟨q, hq, h | h⟩ <;> obtain ⟨v, rfl⟩ := hS.rad.mem_ψ q hq
    · exact ⟨v, Or.inl h⟩
    · exact ⟨v, Or.inr (h.trans (hS.commute_ψ v))⟩
  · rintro ⟨v, h | h⟩
    · exact ⟨ψ v, hS.rad.ψ_mem v, Or.inl h⟩
    · exact ⟨ψ v, hS.rad.ψ_mem v, Or.inr (h.trans (hS.commute_ψ v).symm)⟩

theorem E_comm {x y : G} (hx : x ∈ Q ⊔ zpowers t) (hy : y ∈ Q ⊔ zpowers t) : x * y = y * x :=
  sup_comm_of (fun x hx y hy => hS.rad.Q_comm hx hy) (fun x hx y hy => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]) (hS.shape.commute_sup hS.rad.Q_le_L) hx hy

theorem centralizer_E :
    centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) = Q ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_centralizer_iff.2 fun y hy =>
    hS.E_comm hy hx)
  rw [← hS.shape.centralizer_eq]
  exact ⟨centralizer_le (Set.singleton_subset_iff.2 (t_mem_sup (X := Q))) hx,
    centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx⟩

theorem K_le_normalizer_E :
    P ⊔ zpowers x₀ ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
  intro x hx
  have : x ∈ P ⊔ zpowers x₀ ⊔ zpowers t := mem_sup_left hx
  rw [← hS.shape.normalizer_eq] at this
  exact this.2

theorem K_le_centralizer : P ⊔ zpowers x₀ ≤ centralizer ({t} : Set G) := by
  intro x hx
  have : x ∈ P ⊔ zpowers x₀ ⊔ zpowers t := mem_sup_left hx
  rw [← hS.shape.normalizer_eq] at this
  exact this.1

theorem P_le_normalizer_E : P ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  le_sup_left.trans hS.K_le_normalizer_E

theorem x₀_mem_normalizer_E : x₀ ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  hS.K_le_normalizer_E (mem_sup_right (mem_zpowers x₀))

theorem x₀_mem_normalizer_Q : x₀ ∈ normalizer (Q : Set G) := hS.inputs.x₀_mem_normalizer

theorem K_le_normalizer_Q : P ⊔ zpowers x₀ ≤ normalizer (Q : Set G) :=
  sup_le hS.rad.P_le_normalizer (zpowers_le.2 hS.x₀_mem_normalizer_Q)

theorem K_le_H₀ : P ⊔ zpowers x₀ ≤ H₀ :=
  sup_le (hS.rad.P_le_L.trans hS.inputs.setting.shape.L_le) (zpowers_le.2 hS.inputs.outer.mem)

theorem x₀_conj_mem_P {y : G} (hy : y ∈ P) : x₀ * y * x₀⁻¹ ∈ P := by
  have hxL : x₀ ∈ normalizer (L : Set G) :=
    hS.normalizes_L (hS.inputs.setting.shape.le_centralizer hS.inputs.outer.mem)
  rw [hS.rad.P_eq] at hy ⊢
  obtain ⟨hyL, hyQ⟩ := Subgroup.mem_inf.1 hy
  have h2 : x₀ * y * x₀⁻¹ ∈ normalizer (Q : Set G) :=
    mul_mem (mul_mem hS.x₀_mem_normalizer_Q hyQ) (inv_mem hS.x₀_mem_normalizer_Q)
  exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hxL y).1 hyL, h2⟩

theorem card_K : Nat.card (P ⊔ zpowers x₀ : Subgroup G) = 2 * Nat.card P :=
  Stage0.card_sup_zpowers hS.inputs.outer.sq (fun _ hy => hS.x₀_conj_mem_P hy)
    (fun h => hS.inputs.outer.not_mem (hS.rad.P_le_L h))

theorem card_E [Finite G] : Nat.card (Q ⊔ zpowers t : Subgroup G) = 128 := by
  rw [hS.shape.card_sup hS.rad.Q_le_L, hS.rad.card_Q]

theorem commute_of_mem_P {x : G} (hx : x ∈ P) : x * t = t * x :=
  hS.shape.commute_of_mem (hS.rad.P_le_L hx)

theorem conj_t_eq {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ v, g * t * g⁻¹ = t * ψ v := by
  obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 ((mem_normalizer_iff.1 hg t).1 t_mem_sup)
  · exact absurd (h ▸ hS.rad.Q_le_L (hS.rad.ψ_mem v)) (hS.shape.conj_not_mem hS.rad.odd g)
  · exact ⟨v, h⟩

theorem card_normalizer_E [Finite G] :
    Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) =
      Nat.card (Zset t Q ψ) * (2 * Nat.card (P ⊔ zpowers x₀ : Subgroup G)) := by
  have e : Zset t Q ψ ≃ {y : G // ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G),
      g * t * g⁻¹ = y} :=
    Equiv.ofBijective (fun v => ⟨t * ψ v, v.2⟩) ⟨fun v w h => Subtype.ext (hS.rad.ψ_inj
      (mul_left_cancel (congrArg Subtype.val h))), fun y => by
        obtain ⟨g, hg, hgy⟩ := y.2
        obtain ⟨v, hv⟩ := hS.conj_t_eq hg
        exact ⟨⟨v, g, hg, hv⟩, Subtype.ext (hv.symm.trans hgy)⟩⟩
  have h := card_conj_orbit_mul (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) t
  rw [← Nat.card_congr e, inf_comm, hS.shape.normalizer_eq,
    hS.inputs.setting.shape.card_sup hS.K_le_H₀] at h
  exact h.symm

end SetupX

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
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

end SetupX

namespace SetupX

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p u : Fin 6 → G}
  {x₀ : G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
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

theorem affF_eq_add {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    (v : V6) : affF t ψ g v = affF t ψ g 0 + lin ψ g v := by
  rw [hS.affF_eq_iff hNQ hg]
  calc g * (t * ψ v) * g⁻¹ = (g * (t * ψ 0) * g⁻¹) * (g * ψ v * g⁻¹) := by
        rw [hS.rad.ψ_zero]; group
    _ = t * ψ (affF t ψ g 0) * ψ (lin ψ g v) := by
        rw [hS.t_affF hNQ hg, hS.rad.ψ_lin (hNQ hg)]
    _ = t * ψ (affF t ψ g 0 + lin ψ g v) := by rw [hS.rad.ψ_add, mul_assoc]

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

end SetupX

end CFSG.EvenSmallLie.OmegaEight.SplitIn
