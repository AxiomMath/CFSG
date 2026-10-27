module

public import CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors
public import CFSG.LocalAnalysis.RankThreeUC.ModuleRanks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LinearAlgebra.CoprimeActions.CoprimeTwoGroupFixedSpaceControl

theorem fixes {H : Type*} [Group H] [Finite H]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (σ : Representation (ZMod 2) H V)
    (U B : Subgroup H) (hU : IsPGroup 2 U) (hB : Odd (Nat.card B))
    (hBU : B ≤ Subgroup.normalizer (U : Set H))
    (h : ∀ b ∈ B, ∀ v ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σ U, σ b v = v) :
    ∀ b ∈ B, ∀ v ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σ ⁅U, B⁆, σ b v = v := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  have mem_fix : ∀ (E : Subgroup H) (v : V),
      v ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σ E ↔ ∀ e ∈ E, σ e v = v := by
    intro E v
    simp [CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule, Representation.mem_invariants]
  set K : Subgroup H := ⁅U, B⁆ with hKdef
  have hUK : U ≤ Subgroup.normalizer K := Subgroup.normalizer_commutator_ge_left U B
  have hconj : ∀ g ∈ U, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg k hk =>
    (Subgroup.mem_normalizer_iff.mp (hUK hg) k).mp hk
  set W : Submodule (ZMod 2) V := CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σ K with hWdef
  have hWinv : ∀ u ∈ U, ∀ w ∈ W, σ u w ∈ W := by
    intro u hu w hw
    rw [hWdef, mem_fix] at hw ⊢
    intro k hk
    have h1 : u⁻¹ * k * u⁻¹⁻¹ ∈ K := hconj u⁻¹ (inv_mem hu) k hk
    rw [inv_inv] at h1
    have : σ k (σ u w) = σ u (σ (u⁻¹ * k * u) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 1
      group
    rw [this, hw _ h1]
  have hub : ∀ u ∈ U, ∀ b ∈ B, ∀ w ∈ W, σ (u * b) w = σ b (σ u w) := by
    intro u hu b hb w hw
    have hk0 : u⁻¹ * b⁻¹ * u * b ∈ K := by
      rw [hKdef]
      have hc := Subgroup.commutator_mem_commutator (inv_mem hu) (inv_mem hb)
      rwa [commutatorElement_def, inv_inv, inv_inv] at hc
    have hk0' : σ (u⁻¹ * b⁻¹ * u * b) w = w := by
      rw [hWdef, mem_fix] at hw
      exact hw _ hk0
    have hid : u * b = b * (u * (u⁻¹ * b⁻¹ * u * b)) := by group
    rw [hid, map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, hk0']
  set M : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) {x | ∃ b ∈ B, ∃ w ∈ W, x = σ b w - w} with hMdef
  have hgen : ∀ b ∈ B, ∀ w ∈ W, σ b w - w ∈ M := fun b hb w hw =>
    Submodule.subset_span ⟨b, hb, w, hw, rfl⟩
  have hMinv : ∀ u ∈ U, ∀ x ∈ M, σ u x ∈ M := by
    intro u hu x hx
    have hle : M ≤ M.comap (σ u) := by
      rw [hMdef]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, hb, w, hw, rfl⟩
      show σ u (σ b w - w) ∈ M
      rw [map_sub, ← Module.End.mul_apply, ← map_mul, hub u hu b hb w hw]
      exact hgen b hb (σ u w) (hWinv u hu w hw)
    exact hle hx
  let P : V →ₗ[ZMod 2] V := ∑ c : B, (σ (c : H) : V →ₗ[ZMod 2] V)
  have hP : ∀ x, P x = ∑ c : B, σ (c : H) x := by
    intro x
    simp [P, LinearMap.sum_apply]
  have hMker : M ≤ LinearMap.ker P := by
    rw [hMdef]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, w, hw, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hP]
    simp only [map_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    refine Fintype.sum_equiv (Equiv.mulRight (⟨b, hb⟩ : B)) _ _ (fun c => ?_)
    simp [map_mul, Module.End.mul_apply]
  have hodd : ((Nat.card B : ℕ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hB
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [hk]
    push_cast
    rw [h2]
    simp
  have hPfix : ∀ v ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σ U, P v = v := by
    intro v hv
    rw [hP, Finset.sum_congr rfl (fun (c : B) _ => h (c : H) c.2 v hv), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul (ZMod 2), hodd, one_smul]
  have hMbot : M = ⊥ := by
    by_contra hne
    obtain ⟨v, hvM, hv0, hvfix⟩ :=
      CFSG.LinearAlgebra.CoprimeActions.BinaryFixedVectors.exists_fixed hU (σ.comp U.subtype) M
        (fun g => by intro x hx; exact hMinv g g.2 x hx) hne
    have hvU : v ∈ CFSG.LocalAnalysis.RankThreeUC.fixedSubmodule σ U :=
      (mem_fix U v).mpr (fun e he => hvfix ⟨e, he⟩)
    have h1 : P v = v := hPfix v hvU
    have h2 : P v = 0 := hMker hvM
    exact hv0 (h1.symm.trans h2)
  intro b hb v hv
  have h1 : σ b v - v ∈ M := hgen b hb v hv
  rw [hMbot, Submodule.mem_bot, sub_eq_zero] at h1
  exact h1

end CFSG.LinearAlgebra.CoprimeActions.CoprimeTwoGroupFixedSpaceControl

end
