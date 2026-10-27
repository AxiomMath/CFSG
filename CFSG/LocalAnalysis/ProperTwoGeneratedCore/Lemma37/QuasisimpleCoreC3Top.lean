module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Sylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x : G}

structure CaseC3Top (T Q P₁ S : Subgroup G) (e u y x : G) : Prop extends CaseC3 T Q P₁ e u y where
  le_top : T ≤ S
  isPGroup_top : IsPGroup 2 S
  top_le_normalizer : S ≤ Subgroup.normalizer (T : Set G)
  max : CaseC3.MaxInNormalizer T u
  mem_top : x ∈ S
  not_mem_bot : x ∉ T
  swap_right : ∀ p ∈ P₁, x * p * x⁻¹ ∈ Q
  swap_left : ∀ q ∈ Q, x * q * x⁻¹ ∈ P₁
  mul_mem : ∀ s ∈ S, s ∉ T → s * x ∈ T

namespace CaseC3

variable [Finite G]

theorem exists_caseC3Top (h : CaseC3 T Q P₁ e u y) (Z : Subgroup G) [Z.Normal]
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) (hmax : MaxInNormalizer T u) (hS : IsPGroup 2 S)
    (hTS : T ≤ S) (hne : T ≠ S) : ∃ x, CaseC3Top T Q P₁ S e u y x := by
  obtain ⟨x, hxS, hxT, hSN, hxP, hxQ, hmul⟩ := h.exists_two_group_structure Z hZ hmax hS hTS hne
  exact ⟨x, h, hTS, hS, hSN, hmax, hxS, hxT, hxP, hxQ, hmul⟩

end CaseC3

namespace CaseC3Top

variable (hs : CaseC3Top T Q P₁ S e u y x)
include hs

theorem mem_normalizer : x ∈ Subgroup.normalizer (T : Set G) :=
  hs.top_le_normalizer hs.mem_top

theorem mul_self_mem : x * x ∈ T := hs.mul_mem x hs.mem_top hs.not_mem_bot

theorem mul_inv_mem {s : G} (hsS : s ∈ S) (hsT : s ∉ T) : s * x⁻¹ ∈ T := by
  rw [show s * x⁻¹ = s * x * (x * x)⁻¹ by group]
  exact T.mul_mem (hs.mul_mem s hsS hsT) (T.inv_mem hs.mul_self_mem)

theorem swap [Finite G] {s : G} (hsS : s ∈ S) (hsT : s ∉ T) :
    (∀ p ∈ P₁, s * p * s⁻¹ ∈ Q) ∧ (∀ q ∈ Q, s * q * s⁻¹ ∈ P₁) :=
  hs.toCaseC3.conj_swap hs.max (hs.top_le_normalizer hsS) hsT
    (CaseC3.exists_pow_eq_one_of_mem hs.isPGroup_top hsS)

theorem conj_mem_sup [Finite G] {w : G} (hw : w ∈ Q ⊔ P₁) : x * w * x⁻¹ ∈ Q ⊔ P₁ :=
  hs.partC.conj_mem_sup_of_mem_normalizer hs.quaternion_right.some hs.mem_normalizer hw

theorem mul_conj_mem_sup [Finite G] {t : G} (ht : t ∈ T) : t * (x * t * x⁻¹) ∈ Q ⊔ P₁ := by
  have hc := hs.partC
  by_cases htW : t ∈ Q ⊔ P₁
  · exact (Q ⊔ P₁).mul_mem htW (hs.conj_mem_sup htW)
  · have hxt : x * t * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hs.mem_normalizer t).mp ht
    have hxtW : x * t * x⁻¹ ∉ Q ⊔ P₁ := fun h' => htW (by
      have := hs.partC.conj_mem_sup_of_mem_normalizer hs.quaternion_right.some
        (Subgroup.inv_mem _ hs.mem_normalizer) h'
      simpa [mul_assoc] using this)
    have := hc.inv_mul_mem t⁻¹ (T.inv_mem ht) _ hxt (fun h' => htW (by
      simpa using (Q ⊔ P₁).inv_mem h')) hxtW
    rwa [inv_inv] at this

theorem mul_self_mem_mul [Finite G] {s : G} (hsS : s ∈ S) (hsT : s ∉ T) :
    s * s * (x * x)⁻¹ ∈ Q ⊔ P₁ := by
  have ht := hs.mul_inv_mem hsS hsT
  have h1 := hs.mul_conj_mem_sup ht
  rw [show s * x⁻¹ * (x * (s * x⁻¹) * x⁻¹) = s * s * (x * x)⁻¹ by group] at h1
  exact h1

end CaseC3Top

namespace CaseC3

variable (Z : Subgroup G) [Z.Normal]

theorem mk_conj_eq_of_not_mem (h : CaseC3 T Q P₁ e u y) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    {c w : G} (hcT : c ∈ T) (hcW : c ∉ Q ⊔ P₁) (hw : w ∈ Q ⊔ P₁) :
    ((c * w * c⁻¹ : G) : G ⧸ Z) = ((y * w * y⁻¹ : G) : G ⧸ Z) := by
  have hc := h.partC
  obtain ⟨φ⟩ := h.quaternion_right
  have hw₁ : c⁻¹ * y ∈ Q ⊔ P₁ := hc.inv_mul_mem c hcT y h.mem hcW h.not_mem
  have hcomm := hc.mul_comm_of_mem_map_sup Z φ hZ (Subgroup.mem_map_of_mem _ hw₁)
    (Subgroup.mem_map_of_mem _ hw)
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hcomm ⊢
  rw [show (y : G ⧸ Z) = (c : G ⧸ Z) * ((c : G ⧸ Z)⁻¹ * (y : G ⧸ Z)) by group]
  rw [show (c : G ⧸ Z) * ((c : G ⧸ Z)⁻¹ * (y : G ⧸ Z)) * (w : G ⧸ Z) *
      ((c : G ⧸ Z) * ((c : G ⧸ Z)⁻¹ * (y : G ⧸ Z)))⁻¹ =
      (c : G ⧸ Z) * (((c : G ⧸ Z)⁻¹ * (y : G ⧸ Z)) * (w : G ⧸ Z)) *
        ((c : G ⧸ Z)⁻¹ * (y : G ⧸ Z))⁻¹ * (c : G ⧸ Z)⁻¹ by group, hcomm]
  group

end CaseC3

namespace CaseC3Top

variable [Finite G] (Z : Subgroup G) [Z.Normal]

theorem mk_conj_mem (hs : CaseC3Top T Q P₁ S e u y x) {w : G} (hw : w ∈ Q ⊔ P₁) :
    ((x * w * x⁻¹ : G) : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) :=
  Subgroup.mem_map_of_mem _ (hs.conj_mem_sup hw)

omit [Finite G] in
theorem mk_conj_self (hs : CaseC3Top T Q P₁ S e u y x) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    {v : G} (hvfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) :
    ((x * u * x⁻¹ : G) : G ⧸ Z) = (v : G ⧸ Z) := by
  have hc := hs.partC
  have hxuQ := hs.swap_right u hc.self_mem
  have hy' : x⁻¹ * y * x ∈ T := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs.mem_normalizer) y).mp hs.mem
    simpa using this
  have hfix : y * (x * u * x⁻¹) * y⁻¹ = x * u * x⁻¹ ∨
      y * (x * u * x⁻¹) * y⁻¹ = x * u * x⁻¹ * e := by
    have hconj : y * (x * u * x⁻¹) * y⁻¹ =
        x * ((x⁻¹ * y * x) * u * (x⁻¹ * y * x)⁻¹) * x⁻¹ := by group
    rcases hs.toCaseC3.conj_self_of_mem hy' with h1 | h1 <;> rw [hconj, h1]
    · exact Or.inl rfl
    · right
      rw [show x * (u * e) * x⁻¹ = x * u * (e * x⁻¹) by group, ← hc.commute_centralElt x⁻¹,
        ← mul_assoc]
  have he1 : ((e : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff e).mpr ((hZ e).mpr (Or.inr rfl))
  have hne := hc.self_ne
  rcases hvfix _ hxuQ hfix with h1 | h1 | h1 | h1
  · exfalso
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hne.1 h1
  · exfalso
    rw [← hc.conj_centralElt x] at h1
    exact hne.2 (mul_left_cancel (mul_right_cancel h1))
  · rw [h1]
  · rw [h1, QuotientGroup.mk_mul, he1, mul_one]

theorem mk_conj_conj_comm (hs : CaseC3Top T Q P₁ S e u y x) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    {w : G} (hw : w ∈ Q ⊔ P₁) :
    ((x * (y * w * y⁻¹) * x⁻¹ : G) : G ⧸ Z) = ((y * (x * w * x⁻¹) * y⁻¹ : G) : G ⧸ Z) := by
  have hxyT : x * y * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hs.mem_normalizer y).mp hs.mem
  have hxyW : x * y * x⁻¹ ∉ Q ⊔ P₁ := fun h' => hs.not_mem (by
    have := hs.partC.conj_mem_sup_of_mem_normalizer hs.quaternion_right.some
      (Subgroup.inv_mem _ hs.mem_normalizer) h'
    simpa [mul_assoc] using this)
  have := hs.toCaseC3.mk_conj_eq_of_not_mem Z hZ hxyT hxyW (hs.conj_mem_sup hw)
  rw [← this]
  congr 1
  group

end CaseC3Top

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
