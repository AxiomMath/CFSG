module

public import CFSG.LargeExtraspecial.S13TwoA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem span_pair_eq {u : S.Qt} (hu : u ∈ Fbar S g K) (hu0 : u ≠ 0) {k : S.O} (hk : k ∈ K)
    (hk1 : k ≠ 1) :
    Submodule.span (ZMod 2) (Set.range ![u, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u]) = Fbar S g K := by
  have hku0 : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u ≠ 0 := fun h =>
    hu0 (by simpa using congrArg (k : S.Qt ≃ₗ[ZMod 2] S.Qt).symm h)
  have hne : u ≠ (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u := fun h =>
    hu0 (fix_eq_zero Y.card_K Y.fpf hk hk1 _ h.symm)
  have hle : Submodule.span (ZMod 2) (Set.range ![u, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u]) ≤
      Fbar S g K := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact Hyp13.K_apply_mem_Fbar hk hu
  have h2 := finrank_span_eq_card (linearIndependent_pair_zmod2 hu0 hku0 hne)
  simp only [Fintype.card_fin] at h2
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [Y.finrank_Fbar, h2])

theorem fix_Fbar_of_fix {u : S.Qt} (hu : u ∈ Fbar S g K) (hu0 : u ≠ 0) {x : S.O}
    (hxK : ∀ k ∈ K, k * x = x * k) (hxu : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) :
    ∀ v ∈ Fbar S g K, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  rw [← Y.span_pair_eq hu hu0 hk hk1]
  intro v hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    fin_cases i
    · exact hxu
    · show (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = _
      rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ← hxK k hk, Subgroup.coe_mul,
        LinearEquiv.mul_apply, hxu]
      rfl
  | zero => exact map_zero _
  | add v w _ _ hv hw => rw [map_add, hv, hw]
  | smul c v _ hv => rw [map_smul, hv]

end Hyp13

section Index

variable (Y : Hyp13 S g K) (Y₁ : Hyp13 S g₁ K)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
include Y Y₁ hperp

theorem card_Ebar_eq_mul {u₀ : S.Qt} (hu₀ : u₀ ∈ Fbar S g₁ K) (hu₀0 : u₀ ≠ 0)
    {Λ : Submodule (ZMod 2) S.Qt}
    (hΛ : ∀ e ∈ Ebar S g K, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ - u₀ ∈ Λ) :
    ∃ r : ℕ, r ∣ Nat.card Λ ∧ Nat.card (Ebar S g K) =
      r * Nat.card (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) : Subgroup S.O) := by
  have hu₀D : u₀ ∈ (Fbar S g K ⊔ Fbar S g₁ K : Submodule (ZMod 2) S.Qt) :=
    Submodule.mem_sup_right hu₀
  have hF : ∀ e ∈ Ebar S g K, ∀ e' ∈ Ebar S g K,
      (e : S.Qt ≃ₗ[ZMod 2] S.Qt) ((e' : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ - u₀) =
        (e' : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ - u₀ := fun e he e' he' =>
    Ebar_apply_sub_mem_Fbar_of_perp Y hperp he' hu₀D e he
  let φ : Ebar S g K →* Multiplicative Λ :=
    { toFun := fun e => Multiplicative.ofAdd ⟨(e : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ - u₀, hΛ e e.2⟩
      map_one' := by
        apply Multiplicative.toAdd.injective
        ext
        simp
      map_mul' := fun e e' => by
        apply Multiplicative.toAdd.injective
        ext
        simp only [toAdd_ofAdd, toAdd_mul, Submodule.coe_add, Subgroup.coe_mul,
          LinearEquiv.mul_apply]
        have h1 := hF e e.2 e' e'.2
        rw [map_sub] at h1
        rw [← sub_add_sub_cancel ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) ((e' : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀))
          ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀) u₀, h1, add_comm] }
  have hker : ∀ e : Ebar S g K, e ∈ φ.ker ↔
      (e : S.O) ∈ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) := by
    intro e
    rw [MonoidHom.mem_ker]
    constructor
    · intro he
      have he' : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) u₀ = u₀ := by
        have := congrArg (fun x => ((Multiplicative.toAdd x : Λ) : S.Qt)) he
        simpa [φ, sub_eq_zero] using this
      have hfix := Y₁.fix_Fbar_of_fix hu₀ hu₀0 (fun k hk => ((mem_Ebar).mp e.2).2 k hk) he'
      intro w hw
      obtain ⟨f, hf, f₁, hf₁, rfl⟩ := Submodule.mem_sup.mp hw
      rw [map_add, hf (e : S.O) e.2, hfix f₁ hf₁]
    · intro he
      apply Multiplicative.toAdd.injective
      ext
      simp [φ, he u₀ hu₀D]
  have h1 := Subgroup.card_ker_mul_card_range φ
  have h2 : Nat.card φ.ker = Nat.card (Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) :
      Subgroup S.O) := by
    have heq : φ.ker = (ptStab S (Fbar S g K ⊔ Fbar S g₁ K)).subgroupOf (Ebar S g K) := by
      ext e
      rw [hker, mem_subgroupOf]
    rw [heq, ← Subgroup.inf_subgroupOf_left, Nat.card_congr (subgroupOfEquivOfLe
      (inf_le_left : Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) ≤ Ebar S g K)).toEquiv]
  refine ⟨Nat.card φ.range, ?_, ?_⟩
  · have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_congr Multiplicative.toAdd] at this
  · rw [← h1, h2, mul_comm]

end Index

end CFSG.LargeExtraspecial.S13
