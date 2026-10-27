module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510R
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSymplecticSmallCritical

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5g_q8_sq (a w : QuaternionGroup 2) : a ^ 2 * w = w * a ^ 2 := by
  revert a w
  decide +kernel

variable {G : Type} [Group G]

theorem sec5g_sq_commute {K : Subgroup G} (e : ↥K ≃* QuaternionGroup 2) {a w : G}
    (ha : a ∈ K) (hw : w ∈ K) : Commute (a ^ 2) w := by
  have h := sec5g_q8_sq (e ⟨a, ha⟩) (e ⟨w, hw⟩)
  have h' : (⟨a, ha⟩ : ↥K) ^ 2 * ⟨w, hw⟩ = ⟨w, hw⟩ * (⟨a, ha⟩ : ↥K) ^ 2 :=
    e.injective (by simpa only [map_mul, map_pow] using h)
  exact (by simpa using congrArg Subtype.val h' : a ^ 2 * w = w * a ^ 2)

theorem sec5g_Q_sq {L : Subgroup G} {z : G} {Q₁ Q₂ : Subgroup G} (hQ : Sec510Q G L z Q₁ Q₂)
    {x : G} (hx : x ∈ Q₁ ⊔ Q₂) : x ^ 2 ∈ zpowers z := by
  obtain ⟨e₁⟩ := hQ.iso₁
  obtain ⟨e₂⟩ := hQ.iso₂
  have hc : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a := by
    intro a ha b hb
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQ.comm
    exact (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm
  rw [← hQ.center]
  refine sec5_mem_centerIn_iff.mpr ⟨pow_mem hx 2, fun y hy => ?_⟩
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hc hx
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hc hy
  have hcomm : Commute a₁ a₂ := hc a₁ ha₁ a₂ ha₂
  rw [hcomm.mul_pow]
  have h1 : Commute (a₁ ^ 2) w₁ := sec5g_sq_commute e₁ ha₁ hw₁
  have h2 : Commute (a₁ ^ 2) w₂ := hc _ (pow_mem ha₁ 2) _ hw₂
  have h3 : Commute (a₂ ^ 2) w₁ := (hc _ hw₁ _ (pow_mem ha₂ 2)).symm
  have h4 : Commute (a₂ ^ 2) w₂ := sec5g_sq_commute e₂ ha₂ hw₂
  exact (Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4)).eq

variable [Finite G]

theorem sec5g_Q_extraspecial {L : Subgroup G} {z : G} {Q₁ Q₂ : Subgroup G}
    (hQ : Sec510Q G L z Q₁ Q₂) (hz : orderOf z = 2) : IsExtraspecialPGroup 2 ↥(Q₁ ⊔ Q₂) := by
  have hzQ : z ∈ Q₁ ⊔ Q₂ := (sec5_mem_centerIn_iff.mp (hQ.center ▸ mem_zpowers z)).1
  have hzc : ∀ y ∈ Q₁ ⊔ Q₂, z * y = y * z :=
    (sec5_mem_centerIn_iff.mp (hQ.center ▸ mem_zpowers z)).2
  have hcen : ∀ x ∈ Q₁ ⊔ Q₂, (∀ y ∈ Q₁ ⊔ Q₂, x * y = y * x) → x ∈ zpowers z := fun x hx h =>
    hQ.center ▸ sec5_mem_centerIn_iff.mpr ⟨hx, h⟩
  have hzmem : ∀ k : ℤ, ∀ x : ↥(Q₁ ⊔ Q₂), z ^ k = (x : G) →
      x ∈ zpowers (⟨z, hzQ⟩ : ↥(Q₁ ⊔ Q₂)) := fun k x hk =>
    mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  refine CFSG.LocalAnalysis.GorensteinLyons.SymplecticSmallCritical.isExtraspecialPGroup_of_sq_mem
    (z := (⟨z, hzQ⟩ : ↥(Q₁ ⊔ Q₂))) (IsPGroup.of_card (n := 5) (by rw [hQ.card]; norm_num))
    (by rw [Subgroup.orderOf_mk]; exact hz)
    (mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm) (fun x => ?_) (fun x hx => ?_) ?_
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (sec5g_Q_sq hQ x.2)
    exact hzmem k _ hk
  · obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
      (hcen x x.2 fun y hy => (congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)).symm)
    exact hzmem k _ hk
  · by_contra hcon
    push Not at hcon
    have hle : (Q₁ ⊔ Q₂) ≤ zpowers z := fun x hx =>
      hcen x hx fun y hy => congrArg Subtype.val (hcon ⟨x, hx⟩ ⟨y, hy⟩)
    have := Subgroup.card_le_of_le hle
    rw [hQ.card, Nat.card_zpowers, hz] at this
    omega

end CFSG.OddStandard.SmallF3.Omega
