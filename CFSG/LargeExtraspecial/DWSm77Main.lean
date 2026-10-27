module

public import CFSG.LargeExtraspecial.DWSm77Small

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith

namespace Sm77

namespace Decomp

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (D : Decomp S)

include D in
theorem eq_z_of_mem_QG [IsSimpleGroup G] (hn : 4 ≤ S.width) {g : G}
    (hxQ : g * S.z * g⁻¹ ∈ S.QG) : g * S.z * g⁻¹ = S.z := by
  by_contra hxz
  have hA : ∀ h : G, h * S.z * h⁻¹ ∈ D.A → h * S.z * h⁻¹ = S.z := fun h hh => by
    by_contra hne
    exact D.false_of_mem_A hn hh hne
  have hB : ∀ h : G, h * S.z * h⁻¹ ∈ D.B → h * S.z * h⁻¹ = S.z := fun h hh => by
    by_contra hne
    exact D.swap.false_of_mem_A hn hh hne
  have hdim := D.finrank_add
  by_cases hA8 : 8 < Nat.card D.A
  · exact hxz (hA g (D.mem_A_of_mem_QG hB hA8 hxQ))
  · have hdA : finrank (ZMod 2) (S.clSub D.A) ≤ 2 := by
      by_contra h
      push Not at h
      apply hA8
      rw [D.card_A]
      calc 8 < 2 * 2 ^ 3 := by norm_num
        _ ≤ 2 * 2 ^ finrank (ZMod 2) (S.clSub D.A) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) h)
    have hB8 : 8 < Nat.card D.B := by
      rw [D.card_B]
      calc 8 < 2 * 2 ^ 3 := by norm_num
        _ ≤ 2 * 2 ^ finrank (ZMod 2) (S.clSub D.B) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact hxz (hB g (D.swap.mem_A_of_mem_QG hA hB8 hxQ))

end Decomp

section Submodule

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem orthogonal_invariant {W : Submodule (ZMod 2) S.Qt}
    (hinv : ∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) (m : S.M) {v : S.Qt}
    (hv : v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin W) :
    (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro w hw
  have hw' := hv _ (hinv m⁻¹ w hw)
  have e : w = (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ m⁻¹ : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
    rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← map_mul, mul_inv_cancel, map_one]
    rfl
  change polarBilin S.q w _ = 0
  change polarBilin S.q _ v = 0 at hw'
  rw [polarBilin_apply_apply] at hw' ⊢
  rw [e, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2]
  exact hw'

theorem sup_orthogonal_eq_top {W : Submodule (ZMod 2) S.Qt}
    (hnd : W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊥) :
    W ⊔ LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W
    (LinearMap.BilinForm.orthogonal S.q.polarBilin W)
  have h2 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  have h3 := Submodule.finrank_le W
  rw [hnd, finrank_bot, add_zero] at h1
  omega

@[expose] noncomputable def ofSubmodule (W : Submodule (ZMod 2) S.Qt)
    (hinv : ∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hnd : W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊥) (h0 : W ≠ ⊥)
    (htop : W ≠ ⊤) : Decomp S where
  A := S.clPre W
  B := S.clPre (LinearMap.BilinForm.orthogonal S.q.polarBilin W)
  A_le := S.clPre_le_QG W
  B_le := S.clPre_le_QG _
  conj_A := fun m hm a ha =>
    ⟨S.conj_mem_QG hm ha.1, by rw [← S.ρ_cl ⟨m, hm⟩ ha.1]; exact hinv ⟨m, hm⟩ _ ha.2⟩
  conj_B := fun m hm b hb =>
    ⟨S.conj_mem_QG hm hb.1, by
      rw [← S.ρ_cl ⟨m, hm⟩ hb.1]
      exact orthogonal_invariant S hinv ⟨m, hm⟩ hb.2⟩
  comm := fun a ha b hb => by
    rw [← S.polar_cl_eq_zero_iff ha.1 hb.1]
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hb.2) _ ha.2
    rwa [polarBilin_apply_apply] at this
  mul := fun x hx => by
    have hmem : S.cl x ∈ W ⊔ LinearMap.BilinForm.orthogonal S.q.polarBilin W := by
      rw [sup_orthogonal_eq_top S hnd]
      exact Submodule.mem_top
    obtain ⟨w, hw, w', hw', hww'⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨a, ha, rfl⟩ := S.exists_cl w
    obtain ⟨b, hb, rfl⟩ := S.exists_cl w'
    rw [← S.cl_mul ha hb] at hww'
    rcases (S.cl_eq_cl_iff (S.QG.mul_mem ha hb) hx).mp hww' with e | e
    · exact ⟨a, ⟨ha, hw⟩, b, ⟨hb, hw'⟩, e⟩
    · refine ⟨a, ⟨ha, hw⟩, b * S.z, ⟨S.QG.mul_mem hb S.z_mem_QG, ?_⟩, by rw [e, mul_assoc]⟩
      rw [S.cl_mul_z hb]
      exact hw'
  inter := fun x ha hb => by
    have h : S.cl x ∈ W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W := ⟨ha.2, hb.2⟩
    rw [hnd, Submodule.mem_bot] at h
    exact (S.cl_eq_zero_iff ha.1).mp h
  z_mem_A := S.z_mem_clPre W
  z_mem_B := S.z_mem_clPre _
  ne_A := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    obtain ⟨a, ha, rfl⟩ := S.exists_cl w
    refine ⟨a, ⟨ha, hw⟩, fun h => hw0 ?_, fun h => hw0 ?_⟩
    · rw [h, S.cl_one]
    · rw [h, S.cl_z]
  ne_B := by
    have hne : LinearMap.BilinForm.orthogonal S.q.polarBilin W ≠ ⊥ := by
      intro h
      apply htop
      rw [← LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl W,
        h, LinearMap.BilinForm.orthogonal_bot]
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨b, hb, rfl⟩ := S.exists_cl w
    refine ⟨b, ⟨hb, hw⟩, fun h => hw0 ?_, fun h => hw0 ?_⟩
    · rw [h, S.cl_one]
    · rw [h, S.cl_z]

end Submodule

end Sm77

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)

theorem not_decomposable_of_submodule_of_four_le (hn : 4 ≤ S.width)
    (W : Submodule (ZMod 2) S.Qt)
    (hinv : ∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W)
    (hnd : W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊥) (h0 : W ≠ ⊥)
    (htop : W ≠ ⊤) {g : G} (hgQ : g * S.z * g⁻¹ ∈ S.QG) : g * S.z * g⁻¹ = S.z :=
  (Sm77.ofSubmodule S W hinv hnd h0 htop).eq_z_of_mem_QG hn hgQ

@[expose] def NondegWeaklyClosed (S : Setting G) : Prop :=
  ∀ W : Submodule (ZMod 2) S.Qt,
    (∀ m : S.M, ∀ v ∈ W, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) →
    W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊥ → W ≠ ⊥ → W ≠ ⊤ →
    ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z

theorem nondegWeaklyClosed_of_four_le (hn : 4 ≤ S.width) : NondegWeaklyClosed S :=
  fun W hinv hnd h0 htop g hgQ =>
    not_decomposable_of_submodule_of_four_le S hn W hinv hnd h0 htop hgQ

end CFSG.LargeExtraspecial.DW
