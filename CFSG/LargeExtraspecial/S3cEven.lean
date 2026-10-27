module

public import CFSG.LargeExtraspecial.S3cD
public import CFSG.LargeExtraspecial.S3cRad
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

namespace IsAltTrilin

variable {K : Type*} [AddCommGroup K] [Module (ZMod 2) K] {T : K → K → K → ZMod 2}
  (h : IsAltTrilin T)
include h

@[expose] def contractRad (ψ : K) : Submodule (ZMod 2) K where
  carrier := {φ | ∀ χ, T φ ψ χ = 0}
  add_mem' {φ φ'} hφ hφ' χ := by
    rw [h.add_left, hφ χ, hφ' χ, add_zero]
  zero_mem' χ := by
    have e := h.add_left 0 0 ψ χ
    rw [add_zero] at e
    exact left_eq_add.mp e
  smul_mem' c φ hφ χ := by
    rw [map_smul_of_map_add_zmod2 (f := fun φ => T φ ψ χ) (fun φ φ' => h.add_left φ φ' ψ χ),
      hφ χ, mul_zero]

theorem mem_contractRad {ψ φ : K} : φ ∈ h.contractRad ψ ↔ ∀ χ, T φ ψ χ = 0 := Iff.rfl

end IsAltTrilin

namespace TransvectionConfig

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
  {a : V} {W : Submodule (ZMod 2) V} {L : Subgroup (V ≃ₗ[ZMod 2] V)}
  (C : TransvectionConfig q a W L)
include C

@[expose] noncomputable def psi {p : V} (hp : polar q a p = 0) : C.K :=
  C.formK (q.polarBilin p ∘ₗ W.subtype) (C.formOf_a hp)

theorem theta_psi {v : V} (hv : polar q a v = 1) {p : V} (hp : polar q a p = 0) (φ χ : C.K) :
    C.theta v φ (C.psi hp) χ =
      χ (Submodule.Quotient.mk ⟨C.sOf φ p - p, C.perp _ (C.sOf_mem φ) p hp⟩) := by
  have hw : p - (C.sOf (C.psi hp) v - v) ∈ W := C.sub_sOf_formOf_mem hv hp
  set w₀ := p - (C.sOf (C.psi hp) v - v) with hw₀
  have e1 : C.sOf (C.psi hp) v - v = p - w₀ := by
    rw [hw₀]
    abel
  have e3 : C.sOf φ w₀ = w₀ + φ (Submodule.Quotient.mk ⟨w₀, hw⟩) • a := C.sOf_apply φ ⟨w₀, hw⟩
  have e2 : C.sOf φ (p - w₀) - (p - w₀) =
      (C.sOf φ p - p) - φ (Submodule.Quotient.mk ⟨w₀, hw⟩) • a := by
    rw [map_sub, e3]
    abel
  have e4 := C.polar_sOf_sub hv χ ⟨C.sOf φ p - p, C.perp _ (C.sOf_mem φ) p hp⟩
  rw [theta_def, e1, e2, polar_sub_right, polar_smul_right, polar_comm q _ a,
    C.polar_a_sub (C.sOf_mem χ) v, smul_zero, sub_zero]
  exact e4

@[expose] noncomputable def fixK (p : V) : Submodule (ZMod 2) C.K where
  carrier := {φ | C.sOf φ p = p}
  add_mem' {φ φ'} hφ hφ' := by
    change C.sOf (φ + φ') p = p
    rw [C.sOf_add, LinearEquiv.mul_apply]
    rw [show C.sOf φ' p = p from hφ']
    exact hφ
  zero_mem' := by
    change C.sOf 0 p = p
    rw [C.sOf_zero]
    rfl
  smul_mem' c φ hφ := by
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · change C.sOf (0 • φ) p = p
      rw [zero_smul, C.sOf_zero]
      rfl
    · rwa [one_smul]

theorem mem_fixK {p : V} {φ : C.K} : φ ∈ C.fixK p ↔ C.sOf φ p = p := Iff.rfl

theorem finrank_contractRad_le [FiniteDimensional (ZMod 2) V] {v : V} (hv : polar q a v = 1)
    {p : V} (hp : polar q a p = 0) :
    finrank (ZMod 2) ((C.isAltTrilin_theta v).contractRad (C.psi hp)) ≤
      finrank (ZMod 2) (C.fixK p) + 1 := by
  have hT := C.isAltTrilin_theta v
  have hR : ∀ φ ∈ hT.contractRad (C.psi hp), C.sOf φ p = p ∨ C.sOf φ p = p + a := by
    intro φ hφ
    have hmem := C.mem_span_of_forall_K (C.perp _ (C.sOf_mem φ) p hp) fun χ => by
      rw [← C.theta_psi hv hp φ χ]
      exact (hT.mem_contractRad).mp hφ χ
    rcases mem_span_singleton_iff.mp hmem with h0 | h1
    · exact Or.inl (sub_eq_zero.mp h0)
    · exact Or.inr (sub_eq_iff_eq_add'.mp h1)
  by_cases hle : hT.contractRad (C.psi hp) ≤ C.fixK p
  · exact (Submodule.finrank_mono hle).trans (Nat.le_succ _)
  obtain ⟨φ₁, hφ₁R, hφ₁⟩ : ∃ φ₁ ∈ hT.contractRad (C.psi hp), φ₁ ∉ C.fixK p := by
    by_contra hcon
    push Not at hcon
    exact hle hcon
  have hφ₁a : C.sOf φ₁ p = p + a := (hR φ₁ hφ₁R).resolve_left hφ₁
  have hle' : hT.contractRad (C.psi hp) ≤ C.fixK p ⊔ (ZMod 2) ∙ φ₁ := by
    intro φ hφ
    rcases hR φ hφ with h0 | h1
    · exact Submodule.mem_sup_left h0
    · have hsum : φ + φ₁ ∈ C.fixK p := by
        rw [C.mem_fixK, C.sOf_add, LinearEquiv.mul_apply, hφ₁a, map_add, h1, C.fix _ (C.sOf_mem φ),
          add_assoc, vec_add_self, add_zero]
      have : φ = (φ + φ₁) - φ₁ := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hsum)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self φ₁))
  calc finrank (ZMod 2) (hT.contractRad (C.psi hp)) ≤
        finrank (ZMod 2) ↥(C.fixK p ⊔ (ZMod 2) ∙ φ₁) := Submodule.finrank_mono hle'
    _ ≤ finrank (ZMod 2) (C.fixK p) + finrank (ZMod 2) ↥((ZMod 2) ∙ φ₁) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ finrank (ZMod 2) (C.fixK p) + 1 := by
        have := finrank_span_le_card (R := ZMod 2) ({φ₁} : Set C.K)
        simp only [Set.toFinset_singleton, Finset.card_singleton] at this
        omega

end TransvectionConfig

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem eq_one_or_eq_of_card_Dbar_eq_two {g : G} (hD2 : Nat.card (S.Dbar g) = 2) {x : S.O}
    (hxD : x ∈ S.Dbar g) (hx1 : x ≠ 1) :
    ∀ s ∈ S.Lbar g, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) →
      s = 1 ∨ s = x := by
  classical
  intro s hs hsN
  by_contra h
  push Not at h
  let f : Fin 3 → S.Dbar g := ![⟨1, one_mem _⟩, ⟨x, hxD⟩, ⟨s, hs, hsN⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢
    all_goals first
      | exact hx1 hij'.symm
      | exact hx1 hij'
      | exact h.1 hij'.symm
      | exact h.1 hij'
      | exact h.2 hij'.symm
      | exact h.2 hij'
  have := Nat.card_le_card_of_injective f hf
  simp at this
  omega

end Setting

end CFSG.LargeExtraspecial
