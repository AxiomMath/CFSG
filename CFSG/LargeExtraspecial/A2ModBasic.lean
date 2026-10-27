module

public import CFSG.LargeExtraspecial.DW2AOutInput
public import CFSG.LargeExtraspecial.Types

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open TauCeti.QuadraticMap (orthogonalGroup)

@[expose] def RootClass (X : Type) [Group X] (D : Set X) : Prop :=
  DW.IsTransClass34 D ∧ (∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) ∧ Subgroup.center X = ⊥ ∧
    ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥

@[expose] def A2Action {X : Type} [Group X] (D : Set X) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (Q : QuadraticForm (ZMod 2) V) (ρ : X →* (V ≃ₗ[ZMod 2] V)) : Prop :=
  (QuadraticMap.polarBilin Q).Nondegenerate ∧ Function.Injective ρ ∧
    (∀ x v, Q (ρ x v) = Q v) ∧ ∀ d ∈ D, IsTypeA Q (ρ d) 2

namespace RootClass

variable {X : Type} [Group X] {D : Set X}

theorem closure_eq_top (h : RootClass X D) : Subgroup.closure D = ⊤ :=
  h.1.1

theorem nonempty (h : RootClass X D) : D.Nonempty :=
  let ⟨d₀, hd₀, _⟩ := h.1.2.1
  ⟨d₀, hd₀⟩

theorem ne_one (h : RootClass X D) {d : X} (hd : d ∈ D) : d ≠ 1 :=
  (h.1.2.2.1 d hd).1

theorem mul_self (h : RootClass X D) {d : X} (hd : d ∈ D) : d * d = 1 :=
  (h.1.2.2.1 d hd).2

end RootClass

namespace A2Action

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem nondegenerate (h : A2Action D Q ρ) : Q.polarBilin.Nondegenerate :=
  h.1

theorem injective (h : A2Action D Q ρ) : Function.Injective ρ :=
  h.2.1

theorem map_apply (h : A2Action D Q ρ) (x : X) (v : V) : Q (ρ x v) = Q v :=
  h.2.2.1 x v

theorem mem_orthogonalGroup (h : A2Action D Q ρ) (x : X) : ρ x ∈ orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (h.2.2.1 x)

theorem isTypeA (h : A2Action D Q ρ) {d : X} (hd : d ∈ D) : IsTypeA Q (ρ d) 2 :=
  h.2.2.2 d hd

theorem ne_one (h : A2Action D Q ρ) {d : X} (hd : d ∈ D) : d ≠ 1 := fun h1 =>
  (h.isTypeA hd).2.1 (by rw [h1, map_one])

theorem mul_self (h : A2Action D Q ρ) {d : X} (hd : d ∈ D) : d * d = 1 :=
  h.injective (by rw [map_mul, map_one]; exact (h.isTypeA hd).2.2.1)

theorem mono (h : A2Action D Q ρ) {D' : Set X} (hD' : D' ⊆ D) : A2Action D' Q ρ :=
  ⟨h.1, h.2.1, h.2.2.1, fun d hd => h.2.2.2 d (hD' hd)⟩

end A2Action

section CommSpace

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem commSpace_eq_bot_iff {g : V ≃ₗ[K] V} : commSpace g = ⊥ ↔ g = 1 := by
  constructor
  · intro h
    ext v
    have hv : g v - v ∈ commSpace g := sub_mem_commSpace g v
    rw [h, Submodule.mem_bot, sub_eq_zero] at hv
    rw [hv, LinearEquiv.coe_one, id]
  · rintro rfl
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
    rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]

theorem commSpace_inv_eq (g : V ≃ₗ[K] V) : commSpace g⁻¹ = commSpace g := by
  have key : ∀ h : V ≃ₗ[K] V, commSpace h⁻¹ ≤ commSpace h := by
    intro h y hy
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    have hv : h (h⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
    have e : h⁻¹ v - v = -(h (h⁻¹ v) - h⁻¹ v) := by
      rw [hv]
      abel
    rw [e]
    exact neg_mem (sub_mem_commSpace h _)
  refine le_antisymm (key g) ?_
  have h2 := key g⁻¹
  rwa [inv_inv] at h2

theorem commSpace_mul_le_sup (g h : V ≃ₗ[K] V) :
    commSpace (g * h) ≤ commSpace g ⊔ commSpace h := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  have e : (g * h) v - v = (g (h v) - h v) + (h v - v) := by
    rw [LinearEquiv.mul_apply]
    abel
  rw [e]
  exact Submodule.add_mem_sup (sub_mem_commSpace g _) (sub_mem_commSpace h v)

theorem finrank_biSup_le_sum [FiniteDimensional K V] {ι : Type*} (s : Finset ι)
    (W : ι → Submodule K V) :
    finrank K ↥(⨆ i ∈ s, W i) ≤ ∑ i ∈ s, finrank K (W i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iSup_insert, Finset.sum_insert ha]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

end CommSpace

section CommSpaceOf

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {X : Type*} [Group X]

@[expose] def commSpaceOf (ρ : X →* (V ≃ₗ[K] V)) (H : Subgroup X) : Submodule K V :=
  ⨆ h ∈ H, commSpace (ρ h)

variable (ρ : X →* (V ≃ₗ[K] V))

theorem commSpace_le_commSpaceOf {H : Subgroup X} {h : X} (hh : h ∈ H) :
    commSpace (ρ h) ≤ commSpaceOf ρ H :=
  le_iSup₂ (f := fun h (_ : h ∈ H) => commSpace (ρ h)) h hh

theorem commSpaceOf_le_iff {H : Subgroup X} {W : Submodule K V} :
    commSpaceOf ρ H ≤ W ↔ ∀ h ∈ H, commSpace (ρ h) ≤ W :=
  iSup₂_le_iff

theorem commSpaceOf_mono {H₁ H₂ : Subgroup X} (h : H₁ ≤ H₂) :
    commSpaceOf ρ H₁ ≤ commSpaceOf ρ H₂ :=
  (commSpaceOf_le_iff ρ).mpr fun _ hx => commSpace_le_commSpaceOf ρ (h hx)

theorem commSpaceOf_bot : commSpaceOf ρ ⊥ = ⊥ := by
  refine eq_bot_iff.mpr ((commSpaceOf_le_iff ρ).mpr fun x hx => ?_)
  rw [Subgroup.mem_bot] at hx
  rw [hx, map_one, commSpace_eq_bot_iff.mpr rfl]

theorem commSpaceOf_closure (S : Set X) :
    commSpaceOf ρ (Subgroup.closure S) = ⨆ s ∈ S, commSpace (ρ s) := by
  refine le_antisymm ((commSpaceOf_le_iff ρ).mpr fun x hx => ?_)
    (iSup₂_le fun s hs => commSpace_le_commSpaceOf ρ (Subgroup.subset_closure hs))
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact le_iSup₂ (f := fun s (_ : s ∈ S) => commSpace (ρ s)) s hs
  | one => rw [map_one, commSpace_eq_bot_iff.mpr rfl]; exact bot_le
  | mul x y _ _ hx hy => rw [map_mul]; exact (commSpace_mul_le_sup _ _).trans (sup_le hx hy)
  | inv x _ hx => rw [map_inv, commSpace_inv_eq]; exact hx

theorem commSpaceOf_sup (H₁ H₂ : Subgroup X) :
    commSpaceOf ρ (H₁ ⊔ H₂) = commSpaceOf ρ H₁ ⊔ commSpaceOf ρ H₂ := by
  have e : H₁ ⊔ H₂ = Subgroup.closure ((H₁ : Set X) ∪ H₂) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [e, commSpaceOf_closure, iSup_union]
  rfl

theorem commSpaceOf_zpowers (g : X) : commSpaceOf ρ (Subgroup.zpowers g) = commSpace (ρ g) := by
  rw [Subgroup.zpowers_eq_closure, commSpaceOf_closure, iSup_singleton]

theorem commSpaceOf_sup_zpowers (H : Subgroup X) (g : X) :
    commSpaceOf ρ (H ⊔ Subgroup.zpowers g) = commSpaceOf ρ H ⊔ commSpace (ρ g) := by
  rw [commSpaceOf_sup, commSpaceOf_zpowers]

theorem apply_mem_commSpaceOf {H : Subgroup X} {g : X} (hg : g ∈ H) {v : V}
    (hv : v ∈ commSpaceOf ρ H) : ρ g v ∈ commSpaceOf ρ H := by
  have e : ρ g v = (ρ g v - v) + v := by abel
  rw [e]
  exact add_mem (commSpace_le_commSpaceOf ρ hg (sub_mem_commSpace _ _)) hv

theorem commSpaceOf_top_eq_top
    (hirr : ∀ W : Submodule K V, (∀ x, ∀ w ∈ W, ρ x w ∈ W) → W = ⊥ ∨ W = ⊤) {x : X}
    (hx : ρ x ≠ 1) : commSpaceOf ρ ⊤ = ⊤ := by
  rcases hirr (commSpaceOf ρ ⊤)
      (fun y _ hw => apply_mem_commSpaceOf ρ (Subgroup.mem_top y) hw) with h | h
  · refine absurd ?_ hx
    rw [← commSpace_eq_bot_iff, eq_bot_iff, ← h]
    exact commSpace_le_commSpaceOf ρ (Subgroup.mem_top x)
  · exact h

section Finrank

variable [FiniteDimensional K V]

theorem finrank_commSpaceOf_closure_le (S : Finset X) :
    finrank K (commSpaceOf ρ (Subgroup.closure (S : Set X))) ≤
      ∑ s ∈ S, finrank K (commSpace (ρ s)) := by
  rw [commSpaceOf_closure]
  exact finrank_biSup_le_sum S _

theorem finrank_commSpaceOf_sup_zpowers_le (H : Subgroup X) {g : X}
    (hg : finrank K (commSpace (ρ g)) ≤ 2) (hmeet : commSpace (ρ g) ⊓ commSpaceOf ρ H ≠ ⊥) :
    finrank K (commSpaceOf ρ (H ⊔ Subgroup.zpowers g)) ≤ finrank K (commSpaceOf ρ H) + 1 := by
  rw [commSpaceOf_sup_zpowers]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (commSpaceOf ρ H) (commSpace (ρ g))
  have h2 : 1 ≤ finrank K ↥(commSpaceOf ρ H ⊓ commSpace (ρ g)) :=
    Submodule.one_le_finrank_iff.mpr (by rwa [inf_comm])
  omega

end Finrank

end CommSpaceOf

end CFSG.LargeExtraspecial.A2Mod
