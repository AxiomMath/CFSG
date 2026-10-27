module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Core
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.Coordinator

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag CFSG.StandardType.RecipeExcLang

section

theorem twistedE6DiagCase_unfolded :
    ∀ (ℓ f : ℕ), ℓ.Prime → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ (σ : K ≃+* K), (∀ c, σ c = c ^ ℓ ^ f) → 3 ∣ ℓ ^ f + 1 →
    ∀ (g : twistedE6RootGroup K σ)
      (u : (a : Fin TwistTag.E6.foldedTag.rank) → (orbitField TwistTag.E6 K σ.toRingHom a)ˣ)
      (β : MulAut (twistedE6RootGroup K σ)),
    β = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u → β ^ 3 = 1 →
    β ∉ twistedE6Inn K σ → 27 ∣ Nat.card (fixedSubgroup β) := by
  intro ℓ f hℓ hf K _ _ hK σ hσ h3 g u β hβ hβ3 _
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  let Fr : Ω →+* Ω := iterateFrobenius Ω ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ..
  have hσ' : ∀ c, σ.toRingHom c = c ^ ℓ ^ f := hσ
  obtain ⟨hfin, hCR, hCnorm, hCidx, -⟩ := cgrp_facts hf K hK σ.toRingHom hσ' h3 Ω Fr hFr
  have hcomm : (algebraMap K Ω).comp σ.toRingHom = Fr.comp (algebraMap K Ω) :=
    RingHom.ext fun c => by
      change algebraMap K Ω (σ c) = Fr (algebraMap K Ω c)
      rw [hσ, hFr, map_pow]
  set b := compatDiag TwistTag.E6 σ.toRingHom u with hb
  have hbc : IsCompatE6 σ.toRingHom b := fun i => compatDiag_perm u i
  have hdR := baseChangeGL_rootDiagUnit_mem_twistedFixed (L := Ω) hcomm hbc
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) with hι
  have hι : Function.Injective ι := baseChangeGL_injective _
  set x : ModGL TwistTag.E6.tag Ω := ι g.1 * ι (rootDiagUnit TwistTag.E6.tag b) with hxdef
  have hxR : x ∈ Rgrp Ω Fr :=
    mul_mem (hCR (Subgroup.mem_map.2 ⟨g.1, g.2, rfl⟩)) hdR
  have hβx : ∀ c : twistedE6RootGroup K σ,
      ι (β c).1 = x * ι c.1 * x⁻¹ := by
    intro c
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_compatDiagAutHom, ← hb, hxdef]
    simp only [map_mul, map_inv]
    group
  have hpow : ∀ n : ℕ, ∀ c : twistedE6RootGroup K σ,
      ι ((β ^ n) c).1 = x ^ n * ι c.1 * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
      intro c
      rw [pow_succ, MulAut.mul_apply, ih (β c), hβx c]
      group
  have := hCnorm
  have hx3C : x ^ 3 ∈ Cgrp K σ.toRingHom Ω := by
    have h := Subgroup.pow_index_mem ((Cgrp K σ.toRingHom Ω).subgroupOf (Rgrp Ω Fr))
      (⟨x, hxR⟩ : Rgrp Ω Fr)
    have hidx : ((Cgrp K σ.toRingHom Ω).subgroupOf (Rgrp Ω Fr)).index = 3 := hCidx
    rw [hidx] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hx3 : x ^ 3 = 1 := by
    obtain ⟨z, hz, hzx⟩ : ∃ z : ModGL TwistTag.E6.tag K,
        z ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom ∧ ι z = x ^ 3 := hx3C
    have hcent : (⟨z, hz⟩ : twistedE6RootGroup K σ) ∈
        Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      apply hι
      have h := hpow 3 c
      rw [hβ3, MulAut.one_apply] at h
      change ι (c.1 * z) = ι (z * c.1)
      rw [map_mul, map_mul, hzx]
      calc ι c.1 * x ^ 3 = x ^ 3 * ι c.1 * (x ^ 3)⁻¹ * x ^ 3 := by rw [← h]
        _ = x ^ 3 * ι c.1 := by group
    rw [center_graphFixedRootGroup_eq_bot σ.surjective, Subgroup.mem_bot] at hcent
    have hz1 : z = 1 := congrArg Subtype.val hcent
    rw [← hzx, hz1]
    exact map_one ι
  have key := core hf K hK σ.toRingHom hσ' h3 Ω Fr hFr hxR hx3
  have hcard : Nat.card (fixedSubgroup β) =
      Nat.card ↥(Subgroup.centralizer {x} ⊓ Cgrp K σ.toRingHom Ω) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c => ⟨ι c.1.1, ?_, Subgroup.mem_map.2 ⟨c.1.1, c.1.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · have h : β c.1 = c.1 := c.2
      have h2 := hβx c.1
      rw [h] at h2
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc ι c.1.1 * x = x * ι c.1.1 * x⁻¹ * x := by rw [← h2]
        _ = x * ι c.1.1 := by group
    · intro c c' h
      apply Subtype.ext
      apply Subtype.ext
      exact hι (congrArg Subtype.val h)
    · rintro ⟨y, hyc, hyC⟩
      obtain ⟨c0, hc0, rfl⟩ := hyC
      have hc := Subgroup.mem_centralizer_singleton_iff.1 hyc
      refine ⟨⟨⟨c0, hc0⟩, ?_⟩, rfl⟩
      change β ⟨c0, hc0⟩ = ⟨c0, hc0⟩
      apply Subtype.ext
      apply hι
      rw [hβx]
      exact mul_inv_eq_iff_eq_mul.2 hc.symm
  rw [hcard]
  exact key

theorem twentySeven_dvd_fixedSubgroup_twistedE6RootGroup {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ3 : β ^ 3 = 1) (hβ : β ∉ twistedE6Inn K σ) :
    27 ∣ Nat.card (fixedSubgroup β) :=
  twentySeven_dvd_fixedSubgroup_twistedE6RootGroup_of_diag' hℓ hf K hK σ hσ β hβ3 hβ
    fun g u h3 hgu => twistedE6DiagCase_unfolded ℓ f hℓ hf K hK σ hσ h3 g u β hgu hβ3 hβ

end

end CFSG.HardMathSupport.Lang.Coordinator
