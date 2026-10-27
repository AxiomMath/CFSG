module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.Open Subgroup
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

lemma conj_apply' (c y : Γ) :
    (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := rfl

lemma mem_conjSub {X : Subgroup Γ} {c x : Γ} :
    x ∈ conjSub c X ↔ ∃ y ∈ X, c * y * c⁻¹ = x := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [conj_apply']⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [conj_apply']⟩

lemma isElemAbelian_conjSub {p : ℕ} {X : Subgroup Γ} (hX : IsElemAbelian p X) (c : Γ) :
    IsElemAbelian p (conjSub c X) := by
  constructor
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨y, hy, hay⟩ := mem_conjSub.mp a.2
    obtain ⟨z, hz, hbz⟩ := mem_conjSub.mp b.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hay, ← hbz]
    calc c * y * c⁻¹ * (c * z * c⁻¹) = c * (y * z) * c⁻¹ := by group
      _ = c * (z * y) * c⁻¹ := by rw [hX.comm hy hz]
      _ = c * z * c⁻¹ * (c * y * c⁻¹) := by group
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_conjSub.mp hx
    rw [← hxy]
    show ((MulAut.conj c) y) ^ p = 1
    rw [← map_pow (MulAut.conj c) y p, hX.2 y hy, map_one]

lemma zpowers_eq_one_or_self {z x : Γ} (h1 : z ≠ 1) (h2 : z * z = 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact h2
  have horder : orderOf z = 2 := orderOf_eq_prime hz2 h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk' : z ^ (k % 2 : ℤ) = x := by
    rw [← hk, ← zpow_mod_orderOf z k, horder]
    congr 1
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1'
  · left; rw [← hk', h0, zpow_zero]
  · right; rw [← hk', h1', zpow_one]

lemma conjSub_inv_conjSub (c : Γ) (X : Subgroup Γ) :
    conjSub c⁻¹ (conjSub c X) = X := by
  rw [conjSub, conjSub, Subgroup.map_map]
  have h : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom
      = MonoidHom.id Γ := by
    ext x
    simp [conj_apply', mul_assoc]
  rw [h, Subgroup.map_id]

lemma conjSub_conjSub_inv (c : Γ) (X : Subgroup Γ) :
    conjSub c (conjSub c⁻¹ X) = X := by
  simpa only [inv_inv] using conjSub_inv_conjSub c⁻¹ X


end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
