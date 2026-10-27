module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false

section Divisible

variable (L : Type) [Field L] [IsAlgClosed L]

theorem units_zpow_surjective {n : ℤ} (hn : n ≠ 0) : Function.Surjective (fun u : Lˣ => u ^ n) := by
  intro u
  have hnat : 0 < n.natAbs := Int.natAbs_pos.2 hn
  rcases lt_or_gt_of_ne hn with h | h
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((u⁻¹ : Lˣ) : L) hnat
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hnat.ne'] at hz
      exact Units.ne_zero _ hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    have e : n = -(n.natAbs : ℤ) := by omega
    show (Units.mk0 z hz0) ^ n = u
    rw [e, zpow_neg, zpow_natCast]
    have : (Units.mk0 z hz0) ^ n.natAbs = u⁻¹ := Units.ext (by simpa using hz)
    rw [this, inv_inv]
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((u : Lˣ) : L) hnat
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hnat.ne'] at hz
      exact Units.ne_zero _ hz.symm
    refine ⟨Units.mk0 z hz0, ?_⟩
    have e : n = (n.natAbs : ℤ) := by omega
    show (Units.mk0 z hz0) ^ n = u
    rw [e, zpow_natCast]
    exact Units.ext (by simpa using hz)

@[instance_reducible] def divisibleByUnits : DivisibleBy (Additive Lˣ) ℤ :=
  divisibleByOfSMulRightSurj (A := Additive Lˣ) (α := ℤ) fun {n} hn a => by
    obtain ⟨u, hu⟩ := units_zpow_surjective L hn (Additive.toMul a)
    exact ⟨Additive.ofMul u, by
      show n • Additive.ofMul u = a
      rw [← ofMul_zpow]
      exact congrArg Additive.ofMul hu⟩

end Divisible

section Lemma

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]

@[expose] def charHom (a : Fin τ.rank → Lˣ) : (Fin τ.rank → ℤ) →+ Additive Lˣ where
  toFun v := Additive.ofMul (rootChar a v)
  map_zero' := by rw [rootChar_zero]; rfl
  map_add' u v := by rw [rootChar_add]; rfl

@[expose] def coQ (τ : Tag) (J₂ : Finset ℕ) : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ) where
  toFun v j := if j.val ∈ J₂ then ∑ l, τ.cartan j l * v l else 0
  map_zero' := by funext j; simp
  map_add' u v := by
    funext j
    by_cases hj : j.val ∈ J₂
    · simp only [hj, if_true, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · simp [hj]

theorem coQ_apply (J₂ : Finset ℕ) (v : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    coQ τ J₂ v j = if j.val ∈ J₂ then ∑ l, τ.cartan j l * v l else 0 := rfl


theorem rootDiagUnit_mem_rootSpan_of_chars {k : ℕ} (J₂ : Finset ℕ) (δ₀ : Fin τ.rank → ℤ)
    (δ : Fin k → Fin τ.rank → ℤ)
    (hlat : ∀ v : Fin τ.rank → ℤ,
      (∀ j : Fin τ.rank, j.val ∈ J₂ → ∑ l, τ.cartan j l * v l = 0) →
        ∃ (c₀ : ℤ) (co : Fin k → ℤ), v = c₀ • δ₀ + ∑ m, co m • δ m)
    (a : Fin τ.rank → Lˣ) (h₀ : rootChar a δ₀ = 1) (hδ : ∀ m, rootChar a (δ m) = 1) :
    rootDiagUnit τ a ∈ rootSpan τ L (parabolicRoots τ {i : Fin τ.rank | i.val ∈ J₂}) := by
  haveI := divisibleByUnits L
  have hker : (coQ τ J₂).ker ≤ (charHom a).ker := by
    intro v hv
    have hQ : ∀ j : Fin τ.rank, j.val ∈ J₂ → ∑ l, τ.cartan j l * v l = 0 := by
      intro j hj
      have := congrFun (AddMonoidHom.mem_ker.1 hv) j
      simpa [coQ_apply, hj] using this
    obtain ⟨c₀, co, rfl⟩ := hlat v hQ
    rw [AddMonoidHom.mem_ker, map_add, map_zsmul, map_sum]
    have h0 : charHom a δ₀ = 0 := by
      show Additive.ofMul (rootChar a δ₀) = 0
      rw [h₀]; rfl
    have hm : ∀ m, charHom a (δ m) = 0 := fun m => by
      show Additive.ofMul (rootChar a (δ m)) = 0
      rw [hδ m]; rfl
    simp only [map_zsmul, h0, hm, smul_zero, Finset.sum_const_zero, add_zero]
  obtain ⟨H, hH⟩ := (Module.Baer.of_divisible (Additive Lˣ)).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift (coQ τ J₂)) (QuotientAddGroup.kerLift_injective _)
    (QuotientAddGroup.lift (coQ τ J₂).ker (charHom a) hker)
  have hHQ : ∀ v, H (coQ τ J₂ v) = charHom a v := fun v => by
    have := congrArg (fun f : _ →+ Additive Lˣ => f (QuotientAddGroup.mk v)) hH
    simpa using this
  set c : Fin τ.rank → Lˣ := fun j =>
    if j.val ∈ J₂ then Additive.toMul (H (Pi.single j 1)) else 1 with hc
  have ha : a = fun l => ∏ j, c j ^ τ.cartan j l := by
    funext l
    have h1 := hHQ (Pi.single l 1)
    have h2 : coQ τ J₂ (Pi.single l 1) =
        ∑ j, (if j.val ∈ J₂ then τ.cartan j l else 0) • (Pi.single j 1 : Fin τ.rank → ℤ) := by
      funext j
      have e1 : ∑ l', τ.cartan j l' * (Pi.single l 1 : Fin τ.rank → ℤ) l' = τ.cartan j l := by
        simp [Pi.single_apply]
      have e2 : (∑ j', (if j'.val ∈ J₂ then τ.cartan j' l else 0) •
          (Pi.single j' 1 : Fin τ.rank → ℤ)) j = if j.val ∈ J₂ then τ.cartan j l else 0 := by
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single j]
        · simp
        · intro j' _ hj'
          simp [Ne.symm hj']
        · intro h
          exact absurd (Finset.mem_univ j) h
      rw [e2, coQ_apply, e1]
    rw [h2, map_sum] at h1
    have h3 : charHom a (Pi.single l 1) = Additive.ofMul (a l) := by
      show Additive.ofMul (rootChar a (Pi.single l 1)) = _
      simp [rootChar, Pi.single_apply]
    rw [h3] at h1
    have h4 := congrArg Additive.toMul h1
    rw [toMul_ofMul, toMul_sum] at h4
    rw [← h4]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_zsmul, toMul_zsmul]
    by_cases hj : j.val ∈ J₂
    · simp [hc, hj]
    · simp [hc, hj]
  have hdiag : rootDiagUnit τ a =
      ((List.finRange τ.rank).map fun j => torusElt τ L j (c j)).prod := by
    rw [list_prod_torusElt_eq_rootDiagUnit]
    exact congrArg (rootDiagUnit τ) ha
  rw [hdiag]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
  by_cases hj : j.val ∈ J₂
  · rw [← subsystemGroup_eq_rootSpan]
    have hjA : j ∈ {i : Fin τ.rank | i.val ∈ J₂} := hj
    show torusElt τ L j (c j) ∈ subsystemGroup τ L {i : Fin τ.rank | i.val ∈ J₂}
    rw [torusElt]
    exact mul_mem (weylElt_mem_subsystemGroup hjA _) (weylElt_mem_subsystemGroup hjA _)
  · have : c j = 1 := by simp [hc, hj]
    rw [this, torusElt_one]
    exact one_mem _

end Lemma

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.CentralAux
