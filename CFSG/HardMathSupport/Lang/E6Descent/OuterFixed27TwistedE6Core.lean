module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Group
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Order
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Arith
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27TwistedE6Normalizer

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction.E6Pilot (numTwistedE6)

namespace TwistedDiag


@[expose] def Rgrp (Ω : Type) [Field Ω] (Fr : Ω →+* Ω) : Subgroup (ModGL Tag.E6 Ω) :=
  twistedFixedGroup TwistTag.E6 Ω Fr

@[expose] def Cgrp (K : Type) [Field K] (σ : K →+* K) (Ω : Type) [Field Ω] [Algebra K Ω] :
    Subgroup (ModGL Tag.E6 Ω) :=
  (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω))

variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)

theorem mem_Rgrp {g : ModGL Tag.E6 Ω} :
    g ∈ Rgrp Ω Fr ↔ g ∈ adjointGroup Tag.E6 Ω ∧ twistE6 Ω Fr g = g := Iff.rfl

theorem mem_thetaFixed_iff_conj {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = n0 Ω) (x : ModGL Tag.E6 Ω) :
    x ∈ thetaFixed Fr ↔ g * x * g⁻¹ ∈ Rgrp Ω Fr := by
  rw [mem_thetaFixed, mem_Rgrp, theta_apply, ← hgn]
  have hG : x ∈ adjointGroup Tag.E6 Ω ↔ g * x * g⁻¹ ∈ adjointGroup Tag.E6 Ω := by
    constructor
    · intro hx
      exact mul_mem (mul_mem hg hx) (inv_mem hg)
    · intro hx
      have := mul_mem (mul_mem (inv_mem hg) hx) hg
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  rw [hG, map_mul, map_mul, map_inv]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    calc twistE6 Ω Fr g * twistE6 Ω Fr x * (twistE6 Ω Fr g)⁻¹ =
        g * (g⁻¹ * twistE6 Ω Fr g * twistE6 Ω Fr x * (g⁻¹ * twistE6 Ω Fr g)⁻¹) * g⁻¹ := by
          group
      _ = g * x * g⁻¹ := by rw [h]
  · intro h
    calc g⁻¹ * twistE6 Ω Fr g * twistE6 Ω Fr x * (g⁻¹ * twistE6 Ω Fr g)⁻¹ =
        g⁻¹ * (twistE6 Ω Fr g * twistE6 Ω Fr x * (twistE6 Ω Fr g)⁻¹) * g := by group
      _ = x := by rw [h]; group

theorem mapsRootLines_rootDiagUnit' (a : Fin Tag.E6.rank → Ωˣ) :
    MapsRootLines (rootDiagUnit Tag.E6 a : (Module.End Ω (RootModule Tag.E6 Ω))ˣ) 1 := by
  intro α hα
  refine ⟨rootChar a α, ?_⟩
  rw [one_smul]
  exact rootDiag_rootVec a hα

theorem mapsRootLines_of_mem_Dgrp' {y : ModGL Tag.E6 Ω} (hy : y ∈ DiagTorus.Dgrp Ω) :
    MapsRootLines (y : (Module.End Ω (RootModule Tag.E6 Ω))ˣ) 1 := by
  obtain ⟨a, rfl⟩ := hy
  exact mapsRootLines_rootDiagUnit' a

theorem weyl_pow_three_eq_one' {y : ModGL Tag.E6 Ω} {w : WeylGroup Tag.E6}
    (hy : MapsRootLines (y : (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w) (hy3 : y ^ 3 = 1) :
    w ^ 3 = 1 := by
  have h := (hy.mul hy).mul hy
  rw [← pow_three', hy3, ← pow_three'] at h
  exact MapsRootLines.unique h mapsRootLines_one |>.trans (by rfl)

theorem weyl_eq_one_of_mem_Dgrp' {y : ModGL Tag.E6 Ω} {w : WeylGroup Tag.E6}
    (hy : y ∈ DiagTorus.Dgrp Ω)
    (hyw : MapsRootLines (y : (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w) : w = 1 :=
  MapsRootLines.unique hyw (mapsRootLines_of_mem_Dgrp' hy)

theorem cgrp_facts {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (h3 : 3 ∣ ℓ ^ f + 1) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f) :
    Finite (Rgrp Ω Fr) ∧ Cgrp K σ Ω ≤ Rgrp Ω Fr ∧
      ((Cgrp K σ Ω).subgroupOf (Rgrp Ω Fr)).Normal ∧
      (Cgrp K σ Ω).relIndex (Rgrp Ω Fr) = 3 ∧
      Nat.card (Rgrp Ω Fr) = numTwistedE6 (ℓ ^ f) := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨-, hle, hnormal, -⟩ :=
    exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf K hK σ hσ Ω Fr hFr
  obtain ⟨hfin, -, -, -, -, hRcard, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ hσ Ω Fr hFr
  have hCR : Cgrp K σ Ω ≤ Rgrp Ω Fr := hle
  have : Finite (Rgrp Ω Fr) := hfin
  have : Finite (Cgrp K σ Ω) :=
    Finite.of_injective (Subgroup.inclusion hCR) (Subgroup.inclusion_injective hCR)
  have hRnum : Nat.card (Rgrp Ω Fr) = numTwistedE6 (ℓ ^ f) := hRcard
  have hC3 : Nat.card (Cgrp K σ Ω) * 3 = Nat.card (Rgrp Ω Fr) := by
    have h := CFSG.HardMathSupport.Lang.Coordinator.card_graphFixedRootGroup_E6_mul_gcd hℓ hf hK hσ
    rw [Nat.gcd_eq_left h3] at h
    rw [hRnum, ← h]
    exact congrArg (· * 3) (Subgroup.card_map_of_injective (baseChangeGL_injective _))
  refine ⟨hfin, hCR, hnormal, ?_, hRnum⟩
  have h := Subgroup.relIndex_mul_card (Cgrp K σ Ω) (Rgrp Ω Fr)
  rw [inf_of_le_left hCR, ← hC3] at h
  have h' : (Cgrp K σ Ω).relIndex (Rgrp Ω Fr) * Nat.card (Cgrp K σ Ω) =
      3 * Nat.card (Cgrp K σ Ω) := by rw [h, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h'

theorem core {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ f)
    (h3 : 3 ∣ ℓ ^ f + 1) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω ℓ]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ ℓ ^ f)
    {x : ModGL Tag.E6 Ω} (hxR : x ∈ Rgrp Ω Fr) (hx3 : x ^ 3 = 1) :
    27 ∣ Nat.card ↥(Subgroup.centralizer {x} ⊓ Cgrp K σ Ω) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨hfin, hCR, hC, hCidx3, hRnum⟩ := cgrp_facts hf K hK σ hσ h3 Ω Fr hFr
  have : Finite (Rgrp Ω Fr) := hfin
  have hCidx : (Cgrp K σ Ω).relIndex (Rgrp Ω Fr) ≤ 3 := hCidx3.le
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have h30 : (3 : Ω) ≠ 0 := three_ne_zero_of_dvd_card_add_one hf h3
  have hq0 : ((ℓ ^ f : ℕ) : Ω) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero Ω ℓ, zero_pow (by omega)]
  obtain ⟨g, hg, hgn⟩ := exists_inv_mul_twistE6_eq hf hFr
    (canonicalRep_mem_adjointGroup (coxeterSystem Tag.E6) Ω twE6W0)
  let N : Subgroup (ModGL Tag.E6 Ω) :=
    (monomialSubgroup Tag.E6 Ω ⊓ thetaFixed Fr).map (MulAut.conj g).toMonoidHom
  have hNR : N ≤ Rgrp Ω Fr := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mem_thetaFixed_iff_conj Fr hg hgn m).1 hm.2
  have hNcard : Nat.card N = (ℓ ^ f + 1) ^ 6 * 51840 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      card_monomial_thetaFixed Fr hFr hq0]
  have hN : ¬ 3 ∣ N.relIndex (Rgrp Ω Fr) := by
    refine three_not_dvd_of_mul_eq_twisted (ℓ ^ f) _ hq2 h3 ?_
    have h := Subgroup.relIndex_mul_card N (Rgrp Ω Fr)
    rw [inf_of_le_left hNR, hNcard, hRnum] at h
    exact h
  refine twentySeven_dvd_of_fixed_group (Rgrp Ω Fr) N (Cgrp K σ Ω) hNR hCR hC hCidx hN ?_ hxR hx3
  rintro _ ⟨m, ⟨hmM, hmθ⟩, rfl⟩ hy3
  have hm3 : m ^ 3 = 1 := by
    apply (MulAut.conj g).injective
    rw [map_pow, map_one]
    exact hy3
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hmM
  have hmaps : MapsRootLines ((k * canonicalRep (coxeterSystem Tag.E6) Ω w : ModGL Tag.E6 Ω) :
      (Module.End Ω (RootModule Tag.E6 Ω))ˣ) w := by
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hw3 : w ^ 3 = 1 := weyl_pow_three_eq_one' hmaps hm3
  obtain ⟨F, hFθ, hFD, hF3, hFy, hF27, hF81⟩ := exists_fixed_group Fr hFr h3 h30 hw3
  refine ⟨F.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨f, hf', rfl⟩
    exact (mem_thetaFixed_iff_conj Fr hg hgn f).1 (hFθ hf')
  · rintro _ ⟨f, hf', rfl⟩
    rw [← map_pow, hF3 f hf', map_one]
  · rintro _ ⟨f, hf', rfl⟩
    have h := hFy f hf' k (DiagTorus.torusGroup_le_Dgrp hk)
    change (MulAut.conj g) f * (MulAut.conj g) (k * canonicalRep (coxeterSystem Tag.E6) Ω w) =
      (MulAut.conj g) (k * canonicalRep (coxeterSystem Tag.E6) Ω w) * (MulAut.conj g) f
    rw [← map_mul, ← map_mul, h]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hF27
  · rintro ⟨f, hf', hfe⟩
    have hfk : f = k * canonicalRep (coxeterSystem Tag.E6) Ω w := (MulAut.conj g).injective hfe
    have hmD : k * canonicalRep (coxeterSystem Tag.E6) Ω w ∈ DiagTorus.Dgrp Ω := hfk ▸ hFD hf'
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hF81 (weyl_eq_one_of_mem_Dgrp' hmD hmaps)

end TwistedDiag

end CFSG.HardMathSupport.Lang.E6Descent
