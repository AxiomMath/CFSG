module

public import CFSG.CGT.PushingUpLit.CGT6E.Emb55Orth

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin CFSG.CGT.PushingUpLit.CGT6
open scoped commutatorElement

structure Emb55Data (V : Type) [CommGroup V] (G T Y H Q : Subgroup (MulAut V)) : Prop where
  sec : Sec5Hyp V G T Y
  hG : H ≤ G
  yH : Y ≤ H
  tN : ∀ t ∈ T, ∀ h : MulAut V, h ∈ H ↔ t * h * t⁻¹ ∈ H
  gen : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → Y ≤ N → H ≤ N
  QH : Q ≤ H
  Qnorm : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q
  Q3 : IsPGroup 3 ↥Q
  Qmax : ∀ N : Subgroup (MulAut V), N ≤ H → (∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) →
    IsPGroup 3 ↥N → N ≤ Q
  Qcent : ∀ h ∈ H, (∀ q ∈ Q, h * q = q * h) → h ∈ Q

namespace Emb55Data

variable {V : Type} [CommGroup V] {G T Y H Q : Subgroup (MulAut V)}
  (d : Emb55Data V G T Y H Q)
include d

theorem Y3 : IsPGroup 3 ↥Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.of_card (n := 1) (by rw [d.sec.ycard]; simp)

theorem QG : Q ≤ G := d.QH.trans d.hG

theorem Y_le_normalizer : Y ≤ Subgroup.normalizer (Q : Set (MulAut V)) := fun y hy =>
  Subgroup.mem_normalizer_iff.mpr fun q =>
    ⟨fun hq => d.Qnorm y (d.yH hy) q hq, fun hq => by
      have h1 := d.Qnorm y⁻¹ (d.yH (Y.inv_mem hy)) _ hq
      have e : y⁻¹ * (y * q * y⁻¹) * y⁻¹⁻¹ = q := by group
      rwa [e] at h1⟩

theorem sup_Y_Q_three : IsPGroup 3 ↥(Y ⊔ Q) :=
  d.Y3.to_sup_of_normal_right' d.Q3 d.Y_le_normalizer

theorem conj_sup_three {a : MulAut V} (ha : a ∈ Q) : IsPGroup 3 ↥(Y ⊔ conjSub a Y) := by
  refine d.sup_Y_Q_three.to_le (sup_le le_sup_left ?_)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_conjSub.mp hx
  have h1 : y * a⁻¹ * y⁻¹ ∈ Q := d.Qnorm y (d.yH hy) a⁻¹ (Q.inv_mem ha)
  have h2 : a * (y * a⁻¹ * y⁻¹) ∈ Q := Q.mul_mem ha h1
  have e : a * y * a⁻¹ = (a * (y * a⁻¹ * y⁻¹)) * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hy)

theorem inf_eq_one {y : MulAut V} (hy : y ∈ Y) (hy1 : y ≠ 1) (hyQ : y ∉ Q) {x : MulAut V}
    (hxY : x ∈ Y) (hxQ : x ∈ Q) : x = 1 := by
  by_contra hx1
  have : Subgroup.zpowers x = Y := d.sec.zpowers_eq hxY hx1
  apply hyQ
  rw [← this] at hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact Q.zpow_mem hxQ k

end Emb55Data

end CFSG.CGT.PushingUpLit.CGT6E
