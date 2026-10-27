module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Sylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coord

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup

variable {G : Type*} [Group G]

theorem sup_comm_of {A B : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x y : G}
    (hx : x ∈ A ⊔ B) (hy : y ∈ A ⊔ B) : x * y = y * x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB hx
  obtain ⟨a', ha', b', hb', rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hAB hy
  calc a * b * (a' * b') = a * (b * a') * b' := by group
    _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
    _ = (a * a') * (b * b') := by group
    _ = (a' * a) * (b' * b) := by rw [hA a ha a' ha', hB b hb b' hb']
    _ = a' * (a * b') * b := by group
    _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
    _ = a' * b' * (a * b) := by group

structure Setup (ε : Eps) (t : G) (L U Q P : Subgroup G) (a : G) (ψ : V6 → G) (p : Fin 6 → G) :
    Prop where
  shape : ShapeAB t L U Q P
  rad : RadicalData ε L U Q P a ψ p

@[expose] def Zset (t : G) (Q : Subgroup G) (ψ : V6 → G) : Set V6 :=
  {v | ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G), g * t * g⁻¹ = t * ψ v}

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
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

theorem E_mul_self {x : G} (hx : x ∈ Q ⊔ zpowers t) : x * x = 1 := by
  obtain ⟨v, rfl | rfl⟩ := hS.mem_E_iff.1 hx
  · exact hS.rad.ψ_mul_self v
  · calc t * ψ v * (t * ψ v) = t * (ψ v * t) * ψ v := by group
      _ = t * (t * ψ v) * ψ v := by rw [hS.commute_ψ v]
      _ = (t * t) * (ψ v * ψ v) := by group
      _ = 1 := by rw [hS.shape.mul_self, hS.rad.ψ_mul_self, one_mul]

theorem centralizer_E :
    centralizer ((Q ⊔ zpowers t : Subgroup G) : Set G) = Q ⊔ zpowers t := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => mem_centralizer_iff.2 fun y hy =>
    hS.E_comm hy hx)
  rw [← hS.shape.centralizer_eq]
  exact ⟨centralizer_le (Set.singleton_subset_iff.2 (t_mem_sup (X := Q))) hx,
    centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hx⟩

theorem P_le_normalizer_E : P ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
  intro x hx
  have : x ∈ P ⊔ zpowers t := mem_sup_left hx
  rw [← hS.shape.normalizer_eq] at this
  exact this.2

theorem commute_of_mem_P {x : G} (hx : x ∈ P) : x * t = t * x :=
  hS.shape.commute_of_mem (hS.rad.P_le_L hx)

theorem conj_t_eq {g : G} (hg : g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ v, g * t * g⁻¹ = t * ψ v := by
  obtain ⟨v, h | h⟩ := hS.mem_E_iff.1 ((mem_normalizer_iff.1 hg t).1 t_mem_sup)
  · exact absurd (h ▸ hS.rad.Q_le_L (hS.rad.ψ_mem v)) (hS.shape.conj_not_mem hS.rad.odd g)
  · exact ⟨v, h⟩

theorem zero_mem_Zset : (0 : V6) ∈ Zset t Q ψ :=
  ⟨1, one_mem _, by rw [hS.rad.ψ_zero]; group⟩

theorem lin_mem_Zset {x : G} (hx : x ∈ P) {v : V6} (hv : v ∈ Zset t Q ψ) :
    lin ψ x v ∈ Zset t Q ψ := by
  obtain ⟨g, hg, hgt⟩ := hv
  refine ⟨x * g, mul_mem (hS.P_le_normalizer_E hx) hg, ?_⟩
  have hxt : x * t * x⁻¹ = t := by rw [hS.commute_of_mem_P hx, mul_inv_cancel_right]
  rw [hS.rad.ψ_lin (hS.rad.P_le_normalizer hx)]
  calc x * g * t * (x * g)⁻¹ = x * (g * t * g⁻¹) * x⁻¹ := by group
    _ = x * t * x⁻¹ * (x * ψ v * x⁻¹) := by rw [hgt]; group
    _ = t * (x * ψ v * x⁻¹) := by rw [hxt]

theorem card_normalizer_E [Finite G] :
    Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) =
      Nat.card (Zset t Q ψ) * (2 * Nat.card P) := by
  have e : Zset t Q ψ ≃ {y : G // ∃ g ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G),
      g * t * g⁻¹ = y} :=
    Equiv.ofBijective (fun v => ⟨t * ψ v, v.2⟩) ⟨fun v w h => Subtype.ext (hS.rad.ψ_inj
      (mul_left_cancel (congrArg Subtype.val h))), fun y => by
        obtain ⟨g, hg, hgy⟩ := y.2
        obtain ⟨v, hv⟩ := hS.conj_t_eq hg
        exact ⟨⟨v, g, hg, hv⟩, Subtype.ext (hv.symm.trans hgy)⟩⟩
  have h := card_conj_orbit_mul (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) t
  rw [← Nat.card_congr e, inf_comm, hS.shape.normalizer_eq, hS.shape.card_sup hS.rad.P_le_L] at h
  exact h.symm

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
