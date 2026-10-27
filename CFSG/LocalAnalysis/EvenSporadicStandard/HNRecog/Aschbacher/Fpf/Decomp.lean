module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Split

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private def tau (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) : A5 × A5 →* Module.End (ZMod 2) V :=
  (Units.coeHom (Module.End (ZMod 2) V)).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.toMonoidHom.comp σ)

private lemma tau_apply_fun (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (g : A5 × A5) (u : V) :
    tau σ g u = σ g u := rfl

private lemma a0_pow_five : a₀ ^ 5 = 1 := by
  have := pow_orderOf_eq_one a₀
  rwa [orderOf_a₀] at this

private lemma a0_ne_one : a₀ ≠ 1 := by
  intro h
  have : orderOf a₀ = 1 := by rw [h]; exact orderOf_one
  rw [orderOf_a₀] at this
  omega

private lemma a0_inv_eq_pow_four : a₀ ^ 4 = a₀⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, a0_pow_five]

private lemma n0_mul_a0 : n₀ * a₀ = a₀ ^ 4 * n₀ := by
  rw [a0_inv_eq_pow_four]
  calc n₀ * a₀ = n₀ * a₀ * n₀⁻¹ * n₀ := by group
    _ = a₀⁻¹ * n₀ := by rw [n₀_mul_a₀_mul_inv]

private lemma mem_ker_sub_one (f : Module.End (ZMod 2) V) (u : V) :
    u ∈ LinearMap.ker (f - 1) ↔ f u = u := by
  rw [LinearMap.mem_ker]
  rw [show (f - 1) u = f u - u from rfl, sub_eq_zero]

theorem exists_decomposition (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (hσ : Function.Injective σ)
    (h8 : finrank (ZMod 2) V = 8)
    (hne : (∃ u : V, u ≠ 0 ∧ σ (a₀, 1) u = u) ∨ (∃ u : V, u ≠ 0 ∧ σ (1, a₀) u = u)) :
    ∃ VA W : Submodule (ZMod 2) V, IsCompl VA W ∧ finrank (ZMod 2) VA = 4 ∧
      finrank (ZMod 2) W = 4 ∧
      (∀ g : A5 × A5, ∀ u ∈ VA, σ g u ∈ VA) ∧ (∀ g : A5 × A5, ∀ u ∈ W, σ g u ∈ W) ∧
      (∀ y : A5, ∀ u ∈ VA, σ (1, y) u = u) ∧ (∀ x : A5, ∀ u ∈ W, σ (x, 1) u = u) := by
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let α : Module.End (ZMod 2) V := tau σ (a₀, 1)
  let β : Module.End (ZMod 2) V := tau σ (1, a₀)
  let ν₁ : Module.End (ZMod 2) V := tau σ (n₀, 1)
  let ν₂ : Module.End (ZMod 2) V := tau σ (1, n₀)
  have hα5 : α ^ 5 = 1 := by
    show tau σ (a₀, 1) ^ 5 = 1
    rw [← map_pow]
    have hp : ((a₀, 1) : A5 × A5) ^ 5 = 1 := by ext <;> simp [a0_pow_five]
    rw [hp, map_one]
  have hβ5 : β ^ 5 = 1 := by
    show tau σ (1, a₀) ^ 5 = 1
    rw [← map_pow]
    have hp : ((1, a₀) : A5 × A5) ^ 5 = 1 := by ext <;> simp [a0_pow_five]
    rw [hp, map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have hfun : ∀ v : V, σ (a₀, 1) v = v := by
      intro v
      have h' := congrArg (fun f : Module.End (ZMod 2) V => f v) h
      simpa [α, tau_apply_fun] using h'
    have heq : σ (a₀, 1) = σ (1 : A5 × A5) := by
      ext v
      simpa using hfun v
    have hprod := hσ heq
    have : a₀ = 1 := by simpa using congrArg Prod.fst hprod
    exact a0_ne_one this
  have hβ1 : β ≠ 1 := by
    intro h
    have hfun : ∀ v : V, σ (1, a₀) v = v := by
      intro v
      have h' := congrArg (fun f : Module.End (ZMod 2) V => f v) h
      simpa [β, tau_apply_fun] using h'
    have heq : σ (1, a₀) = σ (1 : A5 × A5) := by
      ext v
      simpa using hfun v
    have hprod := hσ heq
    have : a₀ = 1 := by simpa using congrArg Prod.snd hprod
    exact a0_ne_one this
  have hαβ : α * β = β * α := by
    show tau σ (a₀, 1) * tau σ (1, a₀) = tau σ (1, a₀) * tau σ (a₀, 1)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by ext <;> simp [mul_comm])
  have hν₂α : ν₂ * α = α * ν₂ := by
    show tau σ (1, n₀) * tau σ (a₀, 1) = tau σ (a₀, 1) * tau σ (1, n₀)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by ext <;> simp)
  have hν₁β : ν₁ * β = β * ν₁ := by
    show tau σ (n₀, 1) * tau σ (1, a₀) = tau σ (1, a₀) * tau σ (n₀, 1)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by ext <;> simp)
  have hν₂β : ν₂ * β = β ^ 4 * ν₂ := by
    show tau σ (1, n₀) * tau σ (1, a₀) = tau σ (1, a₀) ^ 4 * tau σ (1, n₀)
    rw [← map_mul, ← map_pow, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by
      rw [show ((1, a₀) : A5 × A5) ^ 4 = ((1 : A5) ^ 4, a₀ ^ 4) from rfl]
      ext <;> simp [n0_mul_a0])
  have hν₁α : ν₁ * α = α ^ 4 * ν₁ := by
    show tau σ (n₀, 1) * tau σ (a₀, 1) = tau σ (a₀, 1) ^ 4 * tau σ (n₀, 1)
    rw [← map_mul, ← map_pow, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by
      rw [show ((a₀, 1) : A5 × A5) ^ 4 = (a₀ ^ 4, (1 : A5) ^ 4) from rfl]
      ext <;> simp [n0_mul_a0])
  have hν₁inj : Function.Injective ν₁ := by
    intro a b hab
    exact (σ (n₀, 1)).injective (by simpa [ν₁, tau_apply_fun] using hab)
  have hν₂inj : Function.Injective ν₂ := by
    intro a b hab
    exact (σ (1, n₀)).injective (by simpa [ν₂, tau_apply_fun] using hab)
  have hkerα_of : (∃ u : V, u ≠ 0 ∧ σ (a₀, 1) u = u) → LinearMap.ker (α - 1) ≠ ⊥ := by
    rintro ⟨u, hu0, hu⟩
    have hαu : α u = u := (tau_apply_fun σ (a₀, 1) u).trans hu
    intro hbot
    have hmem : u ∈ LinearMap.ker (α - 1) := (mem_ker_sub_one α u).mpr hαu
    rw [hbot] at hmem
    exact hu0 ((Submodule.mem_bot (ZMod 2)).mp hmem)
  have hkerβ_of : (∃ u : V, u ≠ 0 ∧ σ (1, a₀) u = u) → LinearMap.ker (β - 1) ≠ ⊥ := by
    rintro ⟨u, hu0, hu⟩
    have hβu : β u = u := (tau_apply_fun σ (1, a₀) u).trans hu
    intro hbot
    have hmem : u ∈ LinearMap.ker (β - 1) := (mem_ker_sub_one β u).mpr hβu
    rw [hbot] at hmem
    exact hu0 ((Submodule.mem_bot (ZMod 2)).mp hmem)
  have decompα : LinearMap.ker (α - 1) ≠ ⊥ →
      LinearMap.range (α - 1) = LinearMap.ker (β - 1) ∧
      finrank (ZMod 2) (LinearMap.range (α - 1)) = 4 ∧
      LinearMap.range (β - 1) = LinearMap.ker (α - 1) ∧
      finrank (ZMod 2) (LinearMap.range (β - 1)) = 4 := by
    intro hkerα
    have hA := range_eq_ker_of_ker_ne_bot α β ν₂ hα5 hβ5 hαβ.symm hν₂α hν₂β hν₂inj h8 hα1 hβ1 hkerα
    have hkerβ : LinearMap.ker (β - 1) ≠ ⊥ := by
      rw [← hA.1]
      intro hbot
      have : finrank (ZMod 2) (LinearMap.range (α - 1)) = 0 := by rw [hbot, finrank_bot]
      omega
    have hB := range_eq_ker_of_ker_ne_bot β α ν₁ hβ5 hα5 hαβ hν₁β hν₁α hν₁inj h8 hβ1 hα1 hkerβ
    exact ⟨hA.1, hA.2, hB.1, hB.2⟩
  have decompβ : LinearMap.ker (β - 1) ≠ ⊥ →
      LinearMap.range (α - 1) = LinearMap.ker (β - 1) ∧
      finrank (ZMod 2) (LinearMap.range (α - 1)) = 4 ∧
      LinearMap.range (β - 1) = LinearMap.ker (α - 1) ∧
      finrank (ZMod 2) (LinearMap.range (β - 1)) = 4 := by
    intro hkerβ
    have hB := range_eq_ker_of_ker_ne_bot β α ν₁ hβ5 hα5 hαβ hν₁β hν₁α hν₁inj h8 hβ1 hα1 hkerβ
    have hkerα : LinearMap.ker (α - 1) ≠ ⊥ := by
      rw [← hB.1]
      intro hbot
      have : finrank (ZMod 2) (LinearMap.range (β - 1)) = 0 := by rw [hbot, finrank_bot]
      omega
    exact decompα hkerα
  have hfacts : LinearMap.range (α - 1) = LinearMap.ker (β - 1) ∧
      finrank (ZMod 2) (LinearMap.range (α - 1)) = 4 ∧
      LinearMap.range (β - 1) = LinearMap.ker (α - 1) ∧
      finrank (ZMod 2) (LinearMap.range (β - 1)) = 4 := by
    rcases hne with h | h
    · exact decompα (hkerα_of h)
    · exact decompβ (hkerβ_of h)
  obtain ⟨hVAker, hVAfin, hWker, hWfin⟩ := hfacts
  have hβ_comm : ∀ x : A5, tau σ (x, 1) * β = β * tau σ (x, 1) := by
    intro x
    show tau σ (x, 1) * tau σ (1, a₀) = tau σ (1, a₀) * tau σ (x, 1)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by ext <;> simp)
  have hα_comm : ∀ y : A5, tau σ (1, y) * α = α * tau σ (1, y) := by
    intro y
    show tau σ (1, y) * tau σ (a₀, 1) = tau σ (a₀, 1) * tau σ (1, y)
    rw [← map_mul, ← map_mul]
    exact congrArg (fun g : A5 × A5 => tau σ g) (by ext <;> simp)
  have hVA_range_inv : ∀ y : A5, ∀ u ∈ LinearMap.range (α - 1),
      tau σ (1, y) u ∈ LinearMap.range (α - 1) := by
    intro y u hu
    obtain ⟨v, rfl⟩ := hu
    refine ⟨tau σ (1, y) v, ?_⟩
    have key : tau σ (1, y) ((α - 1) v) = (α - 1) (tau σ (1, y) v) := by
      rw [show (α - 1) v = α v - v from rfl, map_sub]
      rw [show (α - 1) (tau σ (1, y) v) = α (tau σ (1, y) v) - tau σ (1, y) v from rfl]
      have hcomm : tau σ (1, y) (α v) = α (tau σ (1, y) v) := by
        have := LinearMap.congr_fun (hα_comm y) v
        simpa only [Module.End.mul_apply] using this
      rw [hcomm]
    exact key.symm
  have hVA_ker_inv : ∀ x : A5, ∀ u ∈ LinearMap.ker (β - 1),
      tau σ (x, 1) u ∈ LinearMap.ker (β - 1) := by
    intro x u hu
    have hu' : β u = u := (mem_ker_sub_one β u).mp hu
    exact (mem_ker_sub_one β (tau σ (x, 1) u)).mpr (by
      have hcomm : tau σ (x, 1) (β u) = β (tau σ (x, 1) u) := by
        have := LinearMap.congr_fun (hβ_comm x) u
        simpa only [Module.End.mul_apply] using this
      rw [← hcomm, hu'])
  have hVA_inv : ∀ g : A5 × A5, ∀ u ∈ LinearMap.range (α - 1),
      σ g u ∈ LinearMap.range (α - 1) := by
    intro g u hu
    obtain ⟨x, y⟩ := g
    have htau : tau σ (x, y) u ∈ LinearMap.range (α - 1) := by
      rw [show ((x, y) : A5 × A5) = (x, 1) * (1, y) from by ext <;> simp,
        map_mul, Module.End.mul_apply]
      rw [hVAker]
      exact hVA_ker_inv x _ (by rw [← hVAker]; exact hVA_range_inv y u hu)
    simpa [tau_apply_fun] using htau
  have hW_range_inv : ∀ x : A5, ∀ u ∈ LinearMap.range (β - 1),
      tau σ (x, 1) u ∈ LinearMap.range (β - 1) := by
    intro x u hu
    obtain ⟨v, rfl⟩ := hu
    refine ⟨tau σ (x, 1) v, ?_⟩
    have key : tau σ (x, 1) ((β - 1) v) = (β - 1) (tau σ (x, 1) v) := by
      rw [show (β - 1) v = β v - v from rfl, map_sub]
      rw [show (β - 1) (tau σ (x, 1) v) = β (tau σ (x, 1) v) - tau σ (x, 1) v from rfl]
      have hcomm : tau σ (x, 1) (β v) = β (tau σ (x, 1) v) := by
        have := LinearMap.congr_fun (hβ_comm x) v
        simpa only [Module.End.mul_apply] using this
      rw [hcomm]
    exact key.symm
  have hW_ker_inv : ∀ y : A5, ∀ u ∈ LinearMap.ker (α - 1),
      tau σ (1, y) u ∈ LinearMap.ker (α - 1) := by
    intro y u hu
    have hu' : α u = u := (mem_ker_sub_one α u).mp hu
    exact (mem_ker_sub_one α (tau σ (1, y) u)).mpr (by
      have hcomm : tau σ (1, y) (α u) = α (tau σ (1, y) u) := by
        have := LinearMap.congr_fun (hα_comm y) u
        simpa only [Module.End.mul_apply] using this
      rw [← hcomm, hu'])
  have hW_inv : ∀ g : A5 × A5, ∀ u ∈ LinearMap.range (β - 1),
      σ g u ∈ LinearMap.range (β - 1) := by
    intro g u hu
    obtain ⟨x, y⟩ := g
    have htau : tau σ (x, y) u ∈ LinearMap.range (β - 1) := by
      rw [show ((x, y) : A5 × A5) = (x, 1) * (1, y) from by ext <;> simp,
        map_mul, Module.End.mul_apply]
      exact hW_range_inv x _ (by rw [hWker]; exact hW_ker_inv y u (by rw [← hWker]; exact hu))
    simpa [tau_apply_fun] using htau
  let N : Subgroup A5 :=
    { carrier := {y | ∀ u ∈ LinearMap.range (α - 1), tau σ (1, y) u = u}
      one_mem' := by
        intro u _
        show tau σ (1 : A5 × A5) u = u
        simp
      mul_mem' := by
        intro y z hy hz u hu
        have h1 : tau σ (1, y * z) = tau σ (1, y) * tau σ (1, z) := by
          rw [show ((1, y * z) : A5 × A5) = (1, y) * (1, z) from by ext <;> simp, map_mul]
        rw [h1, Module.End.mul_apply, hz u hu, hy u hu]
      inv_mem' := by
        intro y hy u hu
        have hcomp : tau σ (1, y⁻¹) * tau σ (1, y) = 1 := by
          rw [← map_mul]
          rw [show ((1, y⁻¹) : A5 × A5) * (1, y) = 1 from by ext <;> simp, map_one]
        have h' := LinearMap.congr_fun hcomp u
        rw [Module.End.mul_apply, Module.End.one_apply, hy u hu] at h'
        exact h' }
  have hNnormal : N.Normal :=
    { conj_mem := by
        intro y hy z u hu
        have hz1 : tau σ (1, z⁻¹) u ∈ LinearMap.range (α - 1) := hVA_range_inv z⁻¹ u hu
        have hy' : tau σ (1, y) (tau σ (1, z⁻¹) u) = tau σ (1, z⁻¹) u := hy _ hz1
        have h1 : tau σ (1, z * y * z⁻¹) = tau σ (1, z) * tau σ (1, y) * tau σ (1, z⁻¹) := by
          rw [show ((1, z * y * z⁻¹) : A5 × A5) = (1, z) * (1, y) * (1, z⁻¹) from by
            ext <;> simp, map_mul, map_mul]
        rw [h1, Module.End.mul_apply, Module.End.mul_apply, hy']
        rw [← Module.End.mul_apply]
        have hzz : tau σ (1, z) * tau σ (1, z⁻¹) = 1 := by
          rw [← map_mul]
          rw [show ((1, z) : A5 × A5) * (1, z⁻¹) = 1 from by ext <;> simp, map_one]
        rw [hzz, Module.End.one_apply] }
  have ha0_mem_N : a₀ ∈ N := by
    intro u hu
    have hu' : u ∈ LinearMap.ker (β - 1) := by rw [← hVAker]; exact hu
    have hβu : β u = u := (mem_ker_sub_one β u).mp hu'
    simpa [β] using hβu
  have hNne : N ≠ ⊥ := by
    intro hbot
    have : a₀ ∈ (⊥ : Subgroup A5) := by rw [← hbot]; exact ha0_mem_N
    exact a0_ne_one ((Subgroup.mem_bot).mp this)
  haveI : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  haveI : N.Normal := hNnormal
  have hNtop : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact absurd h hNne
    · exact h
  have hB_triv : ∀ y : A5, ∀ u ∈ LinearMap.range (α - 1), σ (1, y) u = u := by
    intro y u hu
    have hy : y ∈ N := by rw [hNtop]; exact Subgroup.mem_top y
    simpa [tau_apply_fun] using hy u hu
  let M : Subgroup A5 :=
    { carrier := {x | ∀ u ∈ LinearMap.range (β - 1), tau σ (x, 1) u = u}
      one_mem' := by
        intro u _
        show tau σ (1 : A5 × A5) u = u
        simp
      mul_mem' := by
        intro x z hx hz u hu
        have h1 : tau σ (x * z, 1) = tau σ (x, 1) * tau σ (z, 1) := by
          rw [show ((x * z, 1) : A5 × A5) = (x, 1) * (z, 1) from by ext <;> simp, map_mul]
        rw [h1, Module.End.mul_apply, hz u hu, hx u hu]
      inv_mem' := by
        intro x hx u hu
        have hcomp : tau σ (x⁻¹, 1) * tau σ (x, 1) = 1 := by
          rw [← map_mul]
          rw [show ((x⁻¹, 1) : A5 × A5) * (x, 1) = 1 from by ext <;> simp, map_one]
        have h' := LinearMap.congr_fun hcomp u
        rw [Module.End.mul_apply, Module.End.one_apply, hx u hu] at h'
        exact h' }
  have hMnormal : M.Normal :=
    { conj_mem := by
        intro x hx z u hu
        have hz1 : tau σ (z⁻¹, 1) u ∈ LinearMap.range (β - 1) := hW_range_inv z⁻¹ u hu
        have hx' : tau σ (x, 1) (tau σ (z⁻¹, 1) u) = tau σ (z⁻¹, 1) u := hx _ hz1
        have h1 : tau σ (z * x * z⁻¹, 1) = tau σ (z, 1) * tau σ (x, 1) * tau σ (z⁻¹, 1) := by
          rw [show ((z * x * z⁻¹, 1) : A5 × A5) = (z, 1) * (x, 1) * (z⁻¹, 1) from by
            ext <;> simp, map_mul, map_mul]
        rw [h1, Module.End.mul_apply, Module.End.mul_apply, hx']
        rw [← Module.End.mul_apply]
        have hzz : tau σ (z, 1) * tau σ (z⁻¹, 1) = 1 := by
          rw [← map_mul]
          rw [show ((z, 1) : A5 × A5) * (z⁻¹, 1) = 1 from by ext <;> simp, map_one]
        rw [hzz, Module.End.one_apply] }
  have ha0_mem_M : a₀ ∈ M := by
    intro u hu
    have hu' : u ∈ LinearMap.ker (α - 1) := by rw [← hWker]; exact hu
    have hαu : α u = u := (mem_ker_sub_one α u).mp hu'
    simpa [α] using hαu
  have hMne : M ≠ ⊥ := by
    intro hbot
    have : a₀ ∈ (⊥ : Subgroup A5) := by rw [← hbot]; exact ha0_mem_M
    exact a0_ne_one ((Subgroup.mem_bot).mp this)
  haveI : M.Normal := hMnormal
  have hMtop : M = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
    · exact absurd h hMne
    · exact h
  have hA_triv : ∀ x : A5, ∀ u ∈ LinearMap.range (β - 1), σ (x, 1) u = u := by
    intro x u hu
    have hx : x ∈ M := by rw [hMtop]; exact Subgroup.mem_top x
    simpa [tau_apply_fun] using hx u hu
  have hdisj : Disjoint (LinearMap.range (α - 1)) (LinearMap.range (β - 1)) := by
    rw [hWker]
    exact disjoint_comm.mpr (disjoint_ker_range α hα5)
  have hcompl : IsCompl (LinearMap.range (α - 1)) (LinearMap.range (β - 1)) := by
    apply (Submodule.isCompl_iff_disjoint _ _ ?_).mpr hdisj
    rw [h8, hVAfin, hWfin]
  exact ⟨LinearMap.range (α - 1), LinearMap.range (β - 1), hcompl, hVAfin, hWfin,
    hVA_inv, hW_inv, hB_triv, hA_triv⟩

end CFSG.EvenSporadicStandard.HNRecog.Fpf
