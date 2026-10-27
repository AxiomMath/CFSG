module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open scoped commutatorElement

private theorem commutatorElement_center_mul_left {X : Type} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (x y : X) : ⁅z * x, y⁆ = ⁅x, y⁆ := by
  have hzy : Commute z y := (Subgroup.mem_center_iff.mp hz y).symm
  have hzc : Commute z ⁅x, y⁆ := (Subgroup.mem_center_iff.mp hz ⁅x, y⁆).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hzy.commutator_eq, mul_one, hzc.mul_inv_cancel]

private theorem commutatorElement_center_mul_right {X : Type} [Group X] {z : X}
    (hz : z ∈ Subgroup.center X) (x y : X) : ⁅x, z * y⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_center_mul_left hz, commutatorElement_inv]

private theorem map_commutatorElement_eq_of_center {X : Type} [Group X] (θ : X →* X)
    {z₁ z₂ x₁ x₂ : X} (hz₁ : z₁ ∈ Subgroup.center X) (hz₂ : z₂ ∈ Subgroup.center X)
    (h₁ : θ x₁ = z₁ * x₁) (h₂ : θ x₂ = z₂ * x₂) : θ ⁅x₁, x₂⁆ = ⁅x₁, x₂⁆ := by
  rw [map_commutatorElement, h₁, h₂, commutatorElement_center_mul_left hz₁,
    commutatorElement_center_mul_right hz₂]

theorem normal_solvable_of_fixed {G X : Type} [Group G] [Group X] (ρ : X →* G) (θ : X →* X)
    (τ : G →* G) (hτρ : ∀ x, τ (ρ x) = ρ (θ x)) (hker : ρ.ker ≤ Subgroup.center X)
    (S : Subgroup X) (hS : ∀ x, x ∈ S ↔ θ x = x) (hSperf : Group.IsPerfect ↥S)
    (C₄ : Subgroup G) (hC₄ : ρ.range ≤ C₄) [hN : (ρ.range.subgroupOf C₄).Normal]
    (hsolv : Group.IsSolvable (↥C₄ ⧸ ρ.range.subgroupOf C₄))
    (C' : Subgroup G) (hC' : ∀ g, g ∈ C' ↔ g ∈ C₄ ∧ τ g = g) :
    S.map ρ ≤ C' ∧ ∃ _ : ((S.map ρ).subgroupOf C').Normal,
      Group.IsSolvable (↥C' ⧸ (S.map ρ).subgroupOf C') := by
  have hC'₄ : C' ≤ C₄ := fun c hc => ((hC' c).1 hc).1
  have hQC' : S.map ρ ≤ C' := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hC' _).2 ⟨hC₄ (ρ.mem_range.2 ⟨x, rfl⟩), by rw [hτρ, (hS x).1 hx]⟩
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Subgroup G, ∀ g, g ∈ C₁ ↔ g ∈ C' ∧ g ∈ ρ.range :=
    ⟨C' ⊓ ρ.range, fun g => Subgroup.mem_inf⟩
  have hQC₁ : S.map ρ ≤ C₁ := fun q hq => (hC₁ q).2 ⟨hQC' hq, Subgroup.map_le_range ρ S hq⟩
  have hlift : ∀ c ∈ C₁, ∃ x : X, ρ x = c ∧ θ x * x⁻¹ ∈ ρ.ker := by
    intro c hc
    obtain ⟨hcC', x, rfl⟩ := (hC₁ c).1 hc
    refine ⟨x, rfl, ?_⟩
    have h1 : τ (ρ x) = ρ x := ((hC' _).1 hcC').2
    rw [hτρ] at h1
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  have hcomm : ⁅C₁, C₁⁆ = S.map ρ := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.commutator_le]
      intro c₁ hc₁ c₂ hc₂
      obtain ⟨x₁, rfl, hx₁⟩ := hlift c₁ hc₁
      obtain ⟨x₂, rfl, hx₂⟩ := hlift c₂ hc₂
      refine ⟨⁅x₁, x₂⁆, (hS _).2 ?_, map_commutatorElement ρ x₁ x₂⟩
      exact map_commutatorElement_eq_of_center θ (hker hx₁) (hker hx₂)
        (inv_mul_cancel_right _ _).symm (inv_mul_cancel_right _ _).symm
    · calc S.map ρ = (⁅S, S⁆).map ρ := by rw [Subgroup.commutator_eq_self]
        _ = ⁅S.map ρ, S.map ρ⁆ := Subgroup.map_commutator S S ρ
        _ ≤ ⁅C₁, C₁⁆ := Subgroup.commutator_mono hQC₁ hQC₁
  have hconj₁ : ∀ c ∈ C', ∀ y ∈ C₁, c * y * c⁻¹ ∈ C₁ := by
    intro c hc y hy
    obtain ⟨hyC', hyR⟩ := (hC₁ y).1 hy
    refine (hC₁ _).2 ⟨C'.mul_mem (C'.mul_mem hc hyC') (C'.inv_mem hc), ?_⟩
    exact Subgroup.mem_subgroupOf.1
      (hN.conj_mem ⟨y, hC₄ hyR⟩ (Subgroup.mem_subgroupOf.2 hyR) ⟨c, hC'₄ hc⟩)
  have hconj : ∀ c ∈ C', ∀ q ∈ S.map ρ, c * q * c⁻¹ ∈ S.map ρ := by
    intro c hc q hq
    rw [← hcomm] at hq ⊢
    have hle : ⁅C₁, C₁⁆.map (MulAut.conj c).toMonoidHom ≤ ⁅C₁, C₁⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_ <;>
        rintro _ ⟨y, hy, rfl⟩ <;> exact hconj₁ c hc y hy
    exact hle ⟨q, hq, rfl⟩
  have hnorm : ((S.map ρ).subgroupOf C').Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (hconj g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  refine ⟨hQC', hnorm, ?_⟩
  obtain ⟨g, hg⟩ : ∃ g : (↥C' ⧸ (S.map ρ).subgroupOf C') →* (↥C₄ ⧸ ρ.range.subgroupOf C₄),
      ∀ h : ↥C', g (QuotientGroup.mk h) = QuotientGroup.mk (Subgroup.inclusion hC'₄ h) :=
    ⟨QuotientGroup.map _ _ (Subgroup.inclusion hC'₄) (fun n hn => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact Subgroup.map_le_range ρ S (Subgroup.mem_subgroupOf.1 hn)), fun h => rfl⟩
  obtain ⟨A, hAmem⟩ : ∃ A : Subgroup (↥C' ⧸ (S.map ρ).subgroupOf C'),
      ∀ y, y ∈ A ↔ ∃ h : ↥C', (h : G) ∈ C₁ ∧ QuotientGroup.mk h = y :=
    ⟨(C₁.subgroupOf C').map (QuotientGroup.mk' _), fun y => Iff.rfl⟩
  have hAsolv : Group.IsSolvable ↥A := by
    refine Group.isSolvable_of_comm ?_
    rintro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
    obtain ⟨a, ha, rfl⟩ := (hAmem _).1 hy₁
    obtain ⟨b, hb, rfl⟩ := (hAmem _).1 hy₂
    have hab : (⁅a, b⁆ : ↥C') ∈ (S.map ρ).subgroupOf C' := by
      rw [Subgroup.mem_subgroupOf, ← hcomm]
      exact Subgroup.commutator_mem_commutator ha hb
    have h1 : ⁅(QuotientGroup.mk a : ↥C' ⧸ (S.map ρ).subgroupOf C'), QuotientGroup.mk b⁆ = 1 :=
      (map_commutatorElement (QuotientGroup.mk' ((S.map ρ).subgroupOf C')) a b).symm.trans
        ((QuotientGroup.eq_one_iff _).2 hab)
    refine Subtype.ext ?_
    show (QuotientGroup.mk a : ↥C' ⧸ (S.map ρ).subgroupOf C') * QuotientGroup.mk b =
      QuotientGroup.mk b * QuotientGroup.mk a
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  refine Group.isSolvable_of_ker_le_range A.subtype g ?_
  intro y hy
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [MonoidHom.mem_ker, hg, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_inclusion] at hy
  exact ⟨⟨QuotientGroup.mk h, (hAmem _).2 ⟨h, (hC₁ _).2 ⟨h.2, hy⟩, rfl⟩⟩, rfl⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
