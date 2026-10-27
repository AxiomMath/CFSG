module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDet
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.AGLEmbedding.ToralCensus

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.LinearGroups

section Invariant

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {x : LinearMap.GeneralLinearGroup K V} {W : Submodule K V}

theorem aeval_mem_of_forall_mem (hW : ∀ w ∈ W, (x : Module.End K V) w ∈ W) (p : K[X]) {w : V}
    (hw : w ∈ W) : aeval (x : Module.End K V) p w ∈ W := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using W.add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    refine W.smul_mem c ?_
    induction n with
    | zero => simpa using hw
    | succ n ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih

theorem coe_smul_mem (hW : ∀ w ∈ W, (x : Module.End K V) w ∈ W) (a : K[X]) (e : AdjoinRoot a)
    {v : primaryComponent (x : Module.End K V) a} (hv : (v : V) ∈ W) :
    ((e • v : primaryComponent (x : Module.End K V) a) : V) ∈ W := by
  induction e using AdjoinRoot.induction_on with
  | ih p => rw [coe_mk_smul_primaryComponent]; exact aeval_mem_of_forall_mem hW p hv

variable {ℓ f : ℕ} [Finite K] (hK : UnitaryFieldData ℓ f K) [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} (H : UnitaryPrimaryData hK.bar B x)
include H

theorem inf_primaryComponent_eq_bot_of_selfDual (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W)
    (hWx : ∀ w ∈ W, (x : Module.End K V) w ∈ W) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hself : dualPoly hK.bar a = a) :
    W ⊓ primaryComponent (x : Module.End K V) a = ⊥ := by
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  have hE := unitaryFieldData_adjoinRoot hK (a := a)
  have hsymm := selfDualForm_isSymm hK H ha hself
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwW, hwa⟩ := Submodule.mem_inf.mp hw
  rw [Submodule.mem_bot]
  by_contra hw0
  set w' : primaryComponent (x : Module.End K V) a := ⟨w, hwa⟩
  have hHt : ∀ v u : primaryComponent (x : Module.End K V) a, (v : V) ∈ W → (u : V) ∈ W →
      selfDualForm hK H ha hself v u = 0 := by
    intro v u hv hu
    rw [selfDualForm_apply, selfDualVal_eq_iff]
    intro b
    rw [zero_mul, map_zero]
    exact (hWt _ hv _ (coe_smul_mem hWx a b hu)).symm
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
  obtain ⟨u, hwu, huu⟩ := (hermitian_hyperbolic_splitting hE hsymm
    (selfDualForm_separatingLeft hK H ha hself) hw'0 (hHt w' w' hwW hwW)).1
  obtain ⟨c, hc, hc0⟩ := hE.exists_mem_traceZero_ne_zero
  have hγ := (hermitian_unitary_transvection hE hsymm huu).2.1 c hc
  set γ := hermTransvectionGL (selfDualForm hK H ha hself) huu c
  set g := (selfDualFactorEquiv hK H ha hself).symm ⟨γ, sesqSpecialUnitaryGroup_le _ hγ⟩
  have hg1 : (selfDualFactorEquiv hK H ha hself g :
      sesqUnitaryGroup (selfDualForm hK H ha hself)) = ⟨γ, sesqSpecialUnitaryGroup_le _ hγ⟩ :=
    MulEquiv.apply_symm_apply _ _
  have hdet := det_eq_one_of_selfDual hK H ha hself g (by rw [hg1]; exact hγ)
  have hgU := mem_unitaryCentralizer.mp g.2.1
  have hgw := hC g (mem_sesqSpecialUnitaryGroup.mpr ⟨hgU.1, hdet⟩) hgU.2 w hwW
  have hgw' : ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w =
      ((w' + (c * selfDualForm hK H ha hself u w') • u :
        primaryComponent (x : Module.End K V) a) : V) := by
    rw [← blockApply_selfDualFactorEquiv hK H ha hself g w hwa, hg1]
    change (((hermTransvection (selfDualForm hK H ha hself) u c) w' :
      primaryComponent (x : Module.End K V) a) : V) = _
    rw [hermTransvection_apply]
  rw [hgw'] at hgw
  have h1 : (((c * selfDualForm hK H ha hself u w') • u :
      primaryComponent (x : Module.End K V) a) : V) ∈ W := by
    have := W.sub_mem hgw hwW
    rwa [Submodule.coe_add, add_sub_cancel_left] at this
  have hHuw : selfDualForm hK H ha hself u w' = 1 := by
    rw [← hsymm.eq w' u, hwu, map_one]
  have hcu : c * selfDualForm hK H ha hself u w' ≠ 0 := by rw [hHuw, mul_one]; exact hc0
  have h2 : (u : V) ∈ W := by
    have := coe_smul_mem hWx a (c * selfDualForm hK H ha hself u w')⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcu, one_smul] at this
  have := hHt w' u hwW h2
  rw [hwu] at this
  exact one_ne_zero this

omit [Finite K] in
theorem primaryComponent_le_of_ne_dualPoly
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W)
    (hWx : ∀ w ∈ W, (x : Module.End K V) w ∈ W) {a : K[X]}
    (ha : a ∈ primaryFactors (x : Module.End K V)) (hne : a ≠ dualPoly hK.bar a)
    (hWa : W ⊓ primaryComponent (x : Module.End K V) a ≠ ⊥) :
    primaryComponent (x : Module.End K V) a ≤ W := by
  have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWa
  obtain ⟨hwW, hwa⟩ := Submodule.mem_inf.mp hw
  set w' : primaryComponent (x : Module.End K V) a := ⟨w, hwa⟩
  have hw'0 : w' ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (AdjoinRoot a) (primaryComponent (x : Module.End K V) a),
      φ w' = 1 := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual (AdjoinRoot a) (primaryComponent (x : Module.End K V) a),
        ψ w' ≠ 0 := by
      by_contra! hz
      exact hw'0 ((Module.forall_dual_apply_eq_zero_iff (AdjoinRoot a) w').mp hz)
    exact ⟨(ψ w')⁻¹ • ψ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hψ]⟩
  intro v hv
  set v' : primaryComponent (x : Module.End K V) a := ⟨v, hv⟩
  set v₀ := v' - φ v' • w' with hv₀
  have hφv₀ : φ v₀ = 0 := by rw [hv₀, map_sub, map_smul, hφ, smul_eq_mul, mul_one, sub_self]
  set γ : blockGL (x : Module.End K V) a :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hφv₀)
  set g := (pairedFactorEquiv H ha hne).symm γ
  have hg1 : pairedFactorEquiv H ha hne g = γ := MulEquiv.apply_symm_apply _ _
  have hdet := det_eq_one_of_paired hK H ha hne g (by
    rw [hg1]
    change LinearMap.det (LinearMap.transvection φ v₀) = 1
    rw [LinearMap.transvection.det, hφv₀, add_zero])
  have hgU := mem_unitaryCentralizer.mp g.2.1
  have hgw := hC g (mem_sesqSpecialUnitaryGroup.mpr ⟨hgU.1, hdet⟩) hgU.2 w hwW
  have hgw' : ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w =
      ((w' + v₀ : primaryComponent (x : Module.End K V) a) : V) := by
    rw [← blockApply_pairedFactorEquiv H ha hne g w hwa, hg1]
    change ((LinearMap.transvection φ v₀ w' : primaryComponent (x : Module.End K V) a) : V) = _
    rw [LinearMap.transvection.apply, hφ, one_smul]
  rw [hgw'] at hgw
  have h1 : (v₀ : V) ∈ W := by
    have := W.sub_mem hgw hwW
    rwa [Submodule.coe_add, add_sub_cancel_left] at this
  have h2 := coe_smul_mem hWx a (φ v') (v := w') hwW
  have hv' : v = (v₀ : V) + ((φ v' • w' : primaryComponent (x : Module.End K V) a) : V) := by
    rw [hv₀, Submodule.coe_sub, sub_add_cancel]
  rw [hv']
  exact W.add_mem h1 h2

theorem eq_iSup_primaryComponent_of_forall_commute
    (hdet : LinearMap.det (x : Module.End K V) = 1) (hWt : ∀ v ∈ W, ∀ w ∈ W, B v w = 0)
    (hC : ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ sesqSpecialUnitaryGroup B →
      Commute (g : Module.End K V) (x : Module.End K V) → ∀ w ∈ W, (g : Module.End K V) w ∈ W) :
    W = ⨆ (a ∈ primaryFactors (x : Module.End K V))
      (_ : primaryComponent (x : Module.End K V) a ≤ W),
        primaryComponent (x : Module.End K V) a := by
  have hWx : ∀ w ∈ W, (x : Module.End K V) w ∈ W :=
    hC x (mem_sesqSpecialUnitaryGroup.mpr ⟨H.isom, hdet⟩) (Commute.refl _)
  have hdich : ∀ a ∈ primaryFactors (x : Module.End K V),
      W ⊓ primaryComponent (x : Module.End K V) a = ⊥ ∨
        primaryComponent (x : Module.End K V) a ≤ W := by
    intro a ha
    by_cases hself : dualPoly hK.bar a = a
    · exact Or.inl (inf_primaryComponent_eq_bot_of_selfDual hK H hWt hC hWx ha hself)
    · by_cases hbot : W ⊓ primaryComponent (x : Module.End K V) a = ⊥
      · exact Or.inl hbot
      · exact Or.inr (primaryComponent_le_of_ne_dualPoly hK H hC hWx ha (Ne.symm hself) hbot)
  apply le_antisymm
  · intro w hw
    classical
    have hsum : ∑ a ∈ primaryFactors (x : Module.End K V),
        primaryProjection (x : Module.End K V) a w = w := by
      have := congrArg (fun T : Module.End K V => T w) (sum_primaryProjection H.squarefree)
      simpa only [LinearMap.sum_apply, Module.End.one_apply] using this
    rw [← hsum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have hpa := primaryProjection_mem H.squarefree ha w
    have hpW : primaryProjection (x : Module.End K V) a w ∈ W :=
      aeval_mem_of_forall_mem hWx _ hw
    rcases hdich a ha with hbot | hle
    · have hmem : primaryProjection (x : Module.End K V) a w ∈
          W ⊓ primaryComponent (x : Module.End K V) a := Submodule.mem_inf.mpr ⟨hpW, hpa⟩
      rw [hbot, Submodule.mem_bot] at hmem
      rw [hmem]
      exact Submodule.zero_mem _
    · have h3 : primaryComponent (x : Module.End K V) a ≤
          ⨆ (_ : primaryComponent (x : Module.End K V) a ≤ W),
            primaryComponent (x : Module.End K V) a :=
        le_iSup (fun _ : primaryComponent (x : Module.End K V) a ≤ W =>
          primaryComponent (x : Module.End K V) a) hle
      have h4 : primaryComponent (x : Module.End K V) a ≤
          ⨆ (b ∈ primaryFactors (x : Module.End K V))
            (_ : primaryComponent (x : Module.End K V) b ≤ W),
            primaryComponent (x : Module.End K V) b :=
        le_iSup₂_of_le (f := fun b _ => ⨆ (_ : primaryComponent (x : Module.End K V) b ≤ W),
          primaryComponent (x : Module.End K V) b) a ha h3
      exact h4 hpa
  · exact iSup₂_le fun a _ => iSup_le fun hle => hle

end Invariant

end CFSG.AGLEmbedding.ToralCensus
