module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Kit

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem map_centralizer_conj_class' {G : Type*} [Group G] {P : Subgroup G} {X k : G}
    (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2) :
    (Subgroup.centralizer ({X} : Set G) ⊓ P).map (MulAut.conj k).toMonoidHom =
      Subgroup.centralizer ({k * X ^ e * k⁻¹} : Set G) ⊓ P := by
  have hXe : (X ^ e) ^ e = X := by
    rcases he with rfl | rfl
    · simp
    · calc (X ^ 2) ^ 2 = X ^ 3 * X := by group
        _ = X := by rw [hX3, one_mul]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, ⟨hzc, hzP⟩, rfl⟩
    have hz : z * X ^ e = X ^ e * z := (Commute.pow_right (show Commute z X from hzc) e).eq
    refine ⟨?_, P.mul_mem (P.mul_mem hk hzP) (P.inv_mem hk)⟩
    calc k * z * k⁻¹ * (k * X ^ e * k⁻¹) = k * (z * X ^ e) * k⁻¹ := by group
      _ = k * (X ^ e * z) * k⁻¹ := by rw [hz]
      _ = k * X ^ e * k⁻¹ * (k * z * k⁻¹) := by group
  · rintro ⟨hyc, hyP⟩
    refine ⟨k⁻¹ * y * k, ⟨?_, P.mul_mem (P.mul_mem (P.inv_mem hk) hyP) hk⟩, by group⟩
    have h1 : k⁻¹ * y * k * X ^ e = X ^ e * (k⁻¹ * y * k) := by
      calc k⁻¹ * y * k * X ^ e = k⁻¹ * (y * (k * X ^ e * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * X ^ e * k⁻¹) * y) * k := by rw [hyc]
        _ = X ^ e * (k⁻¹ * y * k) := by group
    have h2 : (Commute (k⁻¹ * y * k) (X ^ e)) := h1
    have h3 := Commute.pow_right h2 e
    rw [hXe] at h3
    exact h3.eq

theorem card_centralizer_conj_class' {G : Type*} [Group G] {P : Subgroup G} {X k : G}
    (hX3 : X ^ 3 = 1) (hk : k ∈ P) {e : ℕ} (he : e = 1 ∨ e = 2) :
    Nat.card ↥(Subgroup.centralizer ({k * X ^ e * k⁻¹} : Set G) ⊓ P) =
      Nat.card ↥(Subgroup.centralizer ({X} : Set G) ⊓ P) := by
  rw [← map_centralizer_conj_class' hX3 hk he,
    Subgroup.card_map_of_injective (MulAut.conj k).injective]

theorem sporL3DownInner_of_fusion {s : TauCeti.SporadicName} {G : Type} [Group G] [Finite G]
    (P : Subgroup G) (hM : Nonempty (↥P ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hord : NoL3Eq (Nat.card ↥P)) (cs : G → Prop)
    (hcs : ∀ c, cs c → c ^ 3 = 1 ∧
      Nat.card ↥(Subgroup.centralizer ({c} : Set G) ⊓ P) < 20160)
    (hfus : ∀ x ∈ P, orderOf x = 3 →
      ∃ k ∈ P, ∃ c, cs c ∧ ∃ e, (e = 1 ∨ e = 2) ∧ x = k * c ^ e * k⁻¹) :
    SporL3DownInner s := by
  refine sporL3DownInner_of_model ↥P hM hord ?_
  intro x hx
  have hx3 : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨k, hk, c, hc, e, he, hxe⟩ := hfus x x.2 hx3
  obtain ⟨hc3, hcard⟩ := hcs c hc
  have hmapc := map_centralizer_subtype P x
  have hcc' : Nat.card (Subgroup.centralizer ({x} : Set ↥P)) =
      Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P) := by
    rw [← hmapc, Subgroup.card_map_of_injective P.subtype_injective]
  rw [hcc', hxe, card_centralizer_conj_class' hc3 hk he]
  exact hcard

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
