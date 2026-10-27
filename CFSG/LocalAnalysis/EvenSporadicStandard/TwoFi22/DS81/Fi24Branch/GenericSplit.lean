module

public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

theorem split_of_complete {G : Type*} [Group G] {J K O : Subgroup G} (hKJ : K ≤ J) (hOK : O ≤ K)
    (hKn : ∀ j ∈ J, ∀ k ∈ K, j * k * j⁻¹ ∈ K) (hOn : ∀ j ∈ J, ∀ o ∈ O, j * o * j⁻¹ ∈ O)
    {X : Type*} [Group X] (π : ↥K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = O.subgroupOf K) (hcenter : Subgroup.center X = ⊥)
    (hcomplete : ∀ φ : MulAut X, ∃ a : X, φ = MulAut.conj a) :
    (∀ j ∈ J, ∃ k ∈ K, ∀ k' ∈ K, (k⁻¹ * j) * k' * (k⁻¹ * j)⁻¹ * k'⁻¹ ∈ O) ∧
    (∀ k ∈ K, (∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ O) → k ∈ O) := by
  constructor
  ·
    intro j hj
    have hjinv : j⁻¹ ∈ J := J.inv_mem hj
    let cj : ↥K →* ↥K := MonoidHom.mk'
      (fun k : ↥K => ⟨j * (k : G) * j⁻¹, hKn j hj (k : G) k.2⟩)
      (fun a b => by ext; simp only [Subgroup.coe_mul]; group)
    let cjInv : ↥K →* ↥K := MonoidHom.mk'
      (fun k : ↥K => ⟨j⁻¹ * (k : G) * j, by simpa using hKn j⁻¹ hjinv (k : G) k.2⟩)
      (fun a b => by ext; simp only [Subgroup.coe_mul]; group)
    have hcj_apply : ∀ k : ↥K, ((cj k : ↥K) : G) = j * (k : G) * j⁻¹ := fun _ => rfl
    have hcjInv_apply : ∀ k : ↥K, ((cjInv k : ↥K) : G) = j⁻¹ * (k : G) * j := fun _ => rfl
    have hβker : π.ker ≤ (π.comp cj).ker := by
      intro k hk
      have hkO : (k : G) ∈ O := by
        rw [hker, Subgroup.mem_subgroupOf] at hk
        exact hk
      rw [MonoidHom.mem_ker]
      have hconjO : j * (k : G) * j⁻¹ ∈ O := hOn j hj (k : G) hkO
      have hmem : cj k ∈ O.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        rwa [hcj_apply k]
      have hker' : cj k ∈ π.ker := by rwa [hker]
      simpa only [MonoidHom.comp_apply] using MonoidHom.mem_ker.mp hker'
    have hβinvker : π.ker ≤ (π.comp cjInv).ker := by
      intro k hk
      have hkO : (k : G) ∈ O := by
        rw [hker, Subgroup.mem_subgroupOf] at hk
        exact hk
      rw [MonoidHom.mem_ker]
      have hconjO : j⁻¹ * (k : G) * j ∈ O := by
        simpa using hOn j⁻¹ hjinv (k : G) hkO
      have hmem : cjInv k ∈ O.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        rwa [hcjInv_apply k]
      have hker' : cjInv k ∈ π.ker := by rwa [hker]
      simpa only [MonoidHom.comp_apply] using MonoidHom.mem_ker.mp hker'
    let α : X →* X :=
      π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨π.comp cj, hβker⟩
    let αinv : X →* X :=
      π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨π.comp cjInv, hβinvker⟩
    have hα : ∀ k : ↥K, α (π k) = π (cj k) := by
      intro k
      change (π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨π.comp cj, hβker⟩) (π k) = π (cj k)
      rw [MonoidHom.liftOfRightInverse_comp_apply]
      rfl
    have hαinv : ∀ k : ↥K, αinv (π k) = π (cjInv k) := by
      intro k
      change (π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨π.comp cjInv, hβinvker⟩) (π k) = π (cjInv k)
      rw [MonoidHom.liftOfRightInverse_comp_apply]
      rfl
    have hcj_cjInv : ∀ k : ↥K, cj (cjInv k) = k := by
      intro k
      apply Subtype.ext
      rw [hcj_apply, hcjInv_apply]
      group
    have hcjInv_cj : ∀ k : ↥K, cjInv (cj k) = k := by
      intro k
      apply Subtype.ext
      rw [hcjInv_apply, hcj_apply]
      group
    have hααinv : Function.RightInverse αinv α := by
      intro x
      obtain ⟨k, rfl⟩ := hπ x
      rw [hαinv k, hα (cjInv k), hcj_cjInv k]
    have hαinvα : Function.LeftInverse αinv α := by
      intro x
      obtain ⟨k, rfl⟩ := hπ x
      rw [hα k, hαinv (cj k), hcjInv_cj k]
    let e : X ≃ X :=
      { toFun := α, invFun := αinv, left_inv := hαinvα, right_inv := hααinv }
    let αaut : MulAut X := MulEquiv.mk' e (fun x y => map_mul α x y)
    have hαaut : ∀ k : ↥K, αaut (π k) = π (cj k) := fun k => hα k
    obtain ⟨a, ha⟩ := hcomplete αaut
    obtain ⟨k₀, hk₀⟩ := hπ a
    have hkey : ∀ k' : ↥K, π (cj k') = π (k₀ * k' * k₀⁻¹) := by
      intro k'
      calc π (cj k') = αaut (π k') := (hαaut k').symm
        _ = (MulAut.conj a) (π k') := by rw [ha]
        _ = a * π k' * a⁻¹ := by rw [MulAut.conj_apply]
        _ = π k₀ * π k' * (π k₀)⁻¹ := by rw [← hk₀]
        _ = π (k₀ * k' * k₀⁻¹) := by rw [map_mul, map_mul, map_inv]
    refine ⟨(k₀ : G), k₀.2, ?_⟩
    intro k'G hk'G
    set k' : ↥K := ⟨k'G, hk'G⟩ with hk'def
    have hk'val : (k' : G) = k'G := rfl
    have hdO : (((k₀)⁻¹ * cj k' * k₀ * k'⁻¹ : ↥K) : G) ∈ O := by
      have hdker : (k₀⁻¹ * cj k' * k₀ * k'⁻¹ : ↥K) ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv, hkey k']
        group
      rwa [hker, Subgroup.mem_subgroupOf] at hdker
    have hgoal : ((k₀ : G)⁻¹ * j) * k'G * ((k₀ : G)⁻¹ * j)⁻¹ * k'G⁻¹
        = (((k₀)⁻¹ * cj k' * k₀ * k'⁻¹ : ↥K) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcj_apply k', hk'val]
      group
    rw [hgoal]
    exact hdO
  ·
    intro k hk hcomm
    have hz : π ⟨k, hk⟩ ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k', rfl⟩ := hπ g
      have hmem : (⟨k, hk⟩ * k' * ⟨k, hk⟩⁻¹ * k'⁻¹ : ↥K) ∈ π.ker := by
        rw [hker, Subgroup.mem_subgroupOf]
        simpa using hcomm k' k'.2
      have h1 : π ⟨k, hk⟩ * π k' * (π ⟨k, hk⟩)⁻¹ * (π k')⁻¹ = 1 := by
        simpa using MonoidHom.mem_ker.mp hmem
      have h3 : π ⟨k, hk⟩ * π k' * (π ⟨k, hk⟩)⁻¹ = π k' := mul_inv_eq_one.mp h1
      have h2 : π ⟨k, hk⟩ * π k' = π k' * π ⟨k, hk⟩ := by
        calc π ⟨k, hk⟩ * π k' = (π ⟨k, hk⟩ * π k' * (π ⟨k, hk⟩)⁻¹) * π ⟨k, hk⟩ := by group
          _ = π k' * π ⟨k, hk⟩ := by rw [h3]
      exact h2.symm
    have hz1 : π ⟨k, hk⟩ = 1 := by
      have hmemc := hz
      rw [hcenter] at hmemc
      exact Subgroup.mem_bot.mp hmemc
    have hmemker : (⟨k, hk⟩ : ↥K) ∈ π.ker := MonoidHom.mem_ker.mpr hz1
    rw [hker, Subgroup.mem_subgroupOf] at hmemker
    exact hmemker

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
