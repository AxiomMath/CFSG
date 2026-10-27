module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Tools
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.QuasithinUnique.Setup.Family


section SubQuot

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def IsInvRep (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E) : Prop :=
  ∀ g, ∀ x ∈ D, ρ g x ∈ D

theorem IsInvRep.map_eq {ρ : G →* (E ≃ₗ[ZMod 2] E)} {D : Submodule (ZMod 2) E}
    (hD : IsInvRep ρ D) (g : G) : D.map (ρ g : E →ₗ[ZMod 2] E) = D := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact hD g y hy
  · refine ⟨ρ g⁻¹ x, hD g⁻¹ x hx, ?_⟩
    change ρ g (ρ g⁻¹ x) = x
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

@[expose] noncomputable def subRep (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E)
    (hD : IsInvRep ρ D) : G →* (D ≃ₗ[ZMod 2] D) where
  toFun g := (ρ g).ofSubmodules D D (hD.map_eq g)
  map_one' := LinearEquiv.ext fun x => Subtype.ext (by
    simp only [LinearEquiv.ofSubmodules_apply, map_one]
    rfl)
  map_mul' g h := LinearEquiv.ext fun x => Subtype.ext (by
    simp only [LinearEquiv.ofSubmodules_apply, map_mul, LinearEquiv.mul_apply])

theorem subRep_apply (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E) (hD : IsInvRep ρ D)
    (g : G) (x : D) : ((subRep ρ D hD g x : D) : E) = ρ g x := rfl

@[expose] noncomputable def quotRep (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E)
    (hD : IsInvRep ρ D) : G →* ((E ⧸ D) ≃ₗ[ZMod 2] (E ⧸ D)) where
  toFun g := Submodule.Quotient.equiv D D (ρ g) (hD.map_eq g)
  map_one' := LinearEquiv.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective D x
    simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    simp
  map_mul' g h := LinearEquiv.ext fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective D x
    simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.mul_apply]
    simp

theorem quotRep_mk (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E) (hD : IsInvRep ρ D)
    (g : G) (x : E) : quotRep ρ D hD g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) :=
  rfl

@[expose] def fixedSub (ρ : G →* (E ≃ₗ[ZMod 2] E)) (A : Subgroup G) : Submodule (ZMod 2) E where
  carrier := {x | ∀ a ∈ A, ρ a x = x}
  add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := fun c x hx a ha => by rw [map_smul, hx a ha]

theorem mem_fixedSub {ρ : G →* (E ≃ₗ[ZMod 2] E)} {A : Subgroup G} {x : E} :
    x ∈ fixedSub ρ A ↔ ∀ a ∈ A, ρ a x = x := Iff.rfl

theorem natCard_fixedSub_le [Finite E] (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E)
    (hD : IsInvRep ρ D) (A : Subgroup G) :
    Nat.card (fixedSub ρ A) ≤
      Nat.card (fixedSub (subRep ρ D hD) A) * Nat.card (fixedSub (quotRep ρ D hD) A) := by
  have : Finite (E ⧸ D) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective D)
  let φ : fixedSub ρ A →ₗ[ZMod 2] fixedSub (quotRep ρ D hD) A :=
    ((D.mkQ).comp (fixedSub ρ A).subtype).codRestrict (fixedSub (quotRep ρ D hD) A)
      (fun x a ha => by
        show quotRep ρ D hD a (Submodule.Quotient.mk (x : E)) = Submodule.Quotient.mk (x : E)
        rw [quotRep_mk, x.2 a ha])
  have h := AddSubgroup.card_ker_mul_card_range φ.toAddMonoidHom
  have hker : Nat.card φ.toAddMonoidHom.ker ≤ Nat.card (fixedSub (subRep ρ D hD) A) := by
    have hmem : ∀ x : φ.toAddMonoidHom.ker, (x.1 : E) ∈ D := fun x => by
      have h0 : φ x.1 = 0 := x.2
      have h1 : ((φ x.1 : fixedSub (quotRep ρ D hD) A) : E ⧸ D) = 0 := by rw [h0]; rfl
      exact (Submodule.Quotient.mk_eq_zero D).1 h1
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨(x.1 : E), hmem x⟩, fun a ha => Subtype.ext (x.1.2 a ha)⟩ :
        fixedSub (subRep ρ D hD) A)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fixedSub (subRep ρ D hD) A => ((z : D) : E)) hxy
  have hrange : Nat.card φ.toAddMonoidHom.range ≤ Nat.card (fixedSub (quotRep ρ D hD) A) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  calc Nat.card (fixedSub ρ A) = Nat.card φ.toAddMonoidHom.ker * Nat.card φ.toAddMonoidHom.range :=
        h.symm
    _ ≤ _ := Nat.mul_le_mul hker hrange

theorem exists_minimal_invRep [Finite E] [Nontrivial E] (ρ : G →* (E ≃ₗ[ZMod 2] E)) :
    ∃ D : Submodule (ZMod 2) E, D ≠ ⊥ ∧ IsInvRep ρ D ∧
      ∀ N : Submodule (ZMod 2) E, N ≤ D → N ≠ ⊥ → IsInvRep ρ N → N = D := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ D : Submodule (ZMod 2) E, D ≠ ⊥ ∧ IsInvRep ρ D ∧ Nat.card D = n
  have hbot : (⊤ : Submodule (ZMod 2) E) ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    intro h
    apply hx
    have : x ∈ (⊥ : Submodule (ZMod 2) E) := h ▸ Submodule.mem_top
    simpa using this
  have hex : ∃ n, P n := ⟨_, ⊤, hbot, fun g x _ => Submodule.mem_top, rfl⟩
  obtain ⟨D, hD0, hDinv, hDcard⟩ := Nat.find_spec hex
  refine ⟨D, hD0, hDinv, fun N hND hN0 hNinv => ?_⟩
  have hle : Nat.find hex ≤ Nat.card N := Nat.find_min' hex ⟨N, hN0, hNinv, rfl⟩
  refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hND ?_)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card D ≤ Nat.card N
  rw [hDcard]
  exact hle

theorem isIrrRep_subRep_of_minimal (ρ : G →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E)
    (hD0 : D ≠ ⊥) (hD : IsInvRep ρ D)
    (hmin : ∀ N : Submodule (ZMod 2) E, N ≤ D → N ≠ ⊥ → IsInvRep ρ N → N = D) :
    IsIrrRep (subRep ρ D hD) := by
  have : Nontrivial D := (Submodule.nontrivial_iff_ne_bot).2 hD0
  refine isIrrRep_of this fun N hN => ?_
  by_cases hN0 : N = ⊥
  · exact Or.inl hN0
  · right
    have hinv : IsInvRep ρ (N.map D.subtype) := by
      rintro g _ ⟨n, hn, rfl⟩
      exact ⟨subRep ρ D hD g n, hN g n hn, rfl⟩
    have hne : N.map D.subtype ≠ ⊥ := by
      obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff N).1 hN0
      exact (Submodule.ne_bot_iff _).2 ⟨(n : E), ⟨n, hn, rfl⟩, fun h => hn0 (Subtype.ext h)⟩
    have hDeq : N.map D.subtype = D := hmin _ (by
      rintro _ ⟨n, -, rfl⟩
      exact n.2) hne hinv
    rw [eq_top_iff]
    intro x _
    have hx : (x : E) ∈ N.map D.subtype := by rw [hDeq]; exact x.2
    obtain ⟨n, hn, hnx⟩ := hx
    have : n = x := Subtype.ext hnx
    rw [← this]
    exact hn

theorem rep_trivial_of_sub_quot {S : Type*} [Group S] (hS : Group.IsPerfect S)
    (ρ : S →* (E ≃ₗ[ZMod 2] E)) (D : Submodule (ZMod 2) E)
    (h1 : ∀ g, ∀ x ∈ D, ρ g x = x) (h2 : ∀ g x, ρ g x - x ∈ D) : ∀ g x, ρ g x = x := by
  have hcomm : ∀ g h : S, ρ g * ρ h = ρ h * ρ g := by
    intro g h
    refine LinearEquiv.ext fun x => ?_
    have e1 := h1 g _ (h2 h x)
    have e2 := h1 h _ (h2 g x)
    rw [map_sub] at e1 e2
    change ρ g (ρ h x) = ρ h (ρ g x)
    rw [sub_eq_iff_eq_add.1 e1, sub_eq_iff_eq_add.1 e2]
    abel
  have hle : commutator S ≤ ρ.ker := by
    show ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ ≤ ρ.ker
    refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm g h
  have hker : ρ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.isPerfect_def.mp hS]
    exact hle
  intro g x
  have hg : g ∈ ρ.ker := by rw [hker]; exact Subgroup.mem_top g
  rw [MonoidHom.mem_ker] at hg
  rw [hg]
  rfl

end SubQuot

end CFSG.QuasithinUnique.Setup.Family
