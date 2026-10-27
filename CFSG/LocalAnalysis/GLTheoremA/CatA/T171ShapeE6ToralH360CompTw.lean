module

import Mathlib.Tactic.Group
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralH360Comp
public import CFSG.Adapters.TauCetiExceptional.TwistedTransfer
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Lang.E6Descent CFSG.GroupActions
open scoped Pointwise


theorem nonempty_twE6ToralLangComp (n : ℕ) (K : Type) [Field K] [Finite K] (hn : 1 ≤ n)
    (hKcard : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (wd wb : ↥(RecipeExcLang.twInndiagGroup K σ)) (hwd3 : wd ^ 3 = 1) (hwd1 : wd ≠ 1)
    (hwb3 : wb ^ 3 = 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (g : ModGL Tag.E6 (AlgebraicClosure K))
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hn0 : g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
      TwistedDiag.n0 (AlgebraicClosure K))
    (htorus : ∀ w ∈ ({wd, wb} : Set ↥(RecipeExcLang.twInndiagGroup K σ)),
      g⁻¹ * ((NoOffTwE6Three.twInndiagEquivRgrp hn hKcard σ hσ Fr hFr w :
          ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
            ModGL Tag.E6 (AlgebraicClosure K)) * g ∈
        torusGroup Tag.E6 (AlgebraicClosure K))
    (Kc : Subgroup (TwE6Delta.RecipeR K n))
    (hKc : CFSG.Assembly.IsComponentOf Kc
      (fixedSubgroup (TwE6Transport.recipeConj σ ε wd)))
    (hnorm : ∀ x ∈ Kc, TwE6Transport.recipeConj σ ε wb x ∈ Kc) :
    ∃ (S : LangSetup Tag.E6 (AlgebraicClosure K) 5)
      (a : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ)
      (D : T171ToralLangComp n K S a (TwE6Delta.RecipeR K n)
        (TwE6Transport.recipeConj σ ε wb).toMonoidHom Kc hnorm),
      S.D.q = 2 ^ n ∧ rootDiagUnit Tag.E6 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
      rootDiagUnit Tag.E6 a ^ 3 = 1 ∧ rootDiagUnit Tag.E6 a ≠ 1 ∧
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (wd : ModGL TwistTag.E6.tag K) =
        S.D.g0 * rootDiagUnit Tag.E6 a * S.D.g0⁻¹ := by
  classical
  let L := AlgebraicClosure K
  let bc : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 L :=
    baseChangeGL (τ := Tag.E6) (algebraMap K L)
  haveI hcharK : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hKcard, pow_mul])
  haveI hcharL : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap K L).injective 2
  have hn0' : TwistedDiag.n0 L = canonicalRep (coxeterSystem Tag.E6) L twE6W0 := rfl
  have hgLang : twistE6 L Fr g = g * canonicalRep (coxeterSystem Tag.E6) L twE6W0 := by
    have h := hn0
    rw [show TwistedDiag.n0 L = canonicalRep (coxeterSystem Tag.E6) L twE6W0 from rfl] at h
    calc twistE6 L Fr g = g * (g⁻¹ * twistE6 L Fr g) := by group
      _ = g * canonicalRep (coxeterSystem Tag.E6) L twE6W0 := by rw [h]
  let D : LangDatum Tag.E6 L :=
    LangDatum.ofTwist TwistTag.E6 Fr (2 ^ n) hFr twE6W0 hg hgLang
  have hDq : D.q = 2 ^ n := rfl
  have hDΦ : D.Φ = twistE6 L Fr := rfl
  have hfin : Finite D.model :=
    finite_model_twistedE6 Nat.prime_two hn hKcard hσ hFr D hDΦ
  have hΓ : D.Γ = ((twistedE6RootGroup K σ).map (bc)).map
      (MulAut.conj D.g0⁻¹).toMonoidHom :=
    Γ_eq_map_twistedE6RootGroup Nat.prime_two hn hKcard hσ hFr D hDΦ
  obtain ⟨-, -, hder, -⟩ :=
    twisted_E6_full_rational_fixed_group_order Nat.prime_two hn K hKcard σ.toRingHom hσ L Fr hFr
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved Tag.E6 L D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : L) = 0 := by
    constructor
    · rw [hDq]
      exact Nat.prime_two.isPrimePow.pow (by omega)
    · rw [hDq]
      exact (CharP.cast_eq_zero_iff L 2 (2 ^ n)).2 (dvd_pow_self 2 (by omega))
  have hpq : ¬ 5 ∣ D.q := by
    rw [hDq]
    intro h5
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h5) (by norm_num)
  let S : LangSetup Tag.E6 L 5 :=
    D.toSetup 5 ρ hρ Nat.prime_five (Or.inl (by norm_num)) hqpow hpq hfin
  have hg0 : S.D.g0 = g := rfl
  let uWd : ModGL Tag.E6 L := bc (wd : ModGL TwistTag.E6.tag K)
  let uWb : ModGL Tag.E6 L := bc (wb : ModGL TwistTag.E6.tag K)
  let ud : ↥(TwistedDiag.Rgrp L Fr) :=
    NoOffTwE6Three.twInndiagEquivRgrp hn hKcard σ hσ Fr hFr wd
  let ub : ↥(TwistedDiag.Rgrp L Fr) :=
    NoOffTwE6Three.twInndiagEquivRgrp hn hKcard σ hσ Fr hFr wb
  have hud_coe : (ud : ModGL Tag.E6 L) = uWd :=
    NoOffTwE6Three.twInndiagEquivRgrp_apply hn hKcard σ hσ Fr hFr wd
  have hub_coe : (ub : ModGL Tag.E6 L) = uWb :=
    NoOffTwE6Three.twInndiagEquivRgrp_apply hn hKcard σ hσ Fr hFr wb
  have huWd_coe : uWd = bc (wd : ModGL TwistTag.E6.tag K) := rfl
  have huWb_coe : uWb = bc (wb : ModGL TwistTag.E6.tag K) := rfl
  have hudF : twistE6 L Fr (ud : ModGL Tag.E6 L) = (ud : ModGL Tag.E6 L) :=
    ((TwistedDiag.mem_Rgrp Fr).1 ud.2).2
  have hubF : twistE6 L Fr (ub : ModGL Tag.E6 L) = (ub : ModGL Tag.E6 L) :=
    ((TwistedDiag.mem_Rgrp Fr).1 ub.2).2
  have huWdF : twistE6 L Fr uWd = uWd := by
    rw [← hud_coe]
    exact hudF
  have huWbF : twistE6 L Fr uWb = uWb := by
    rw [← hub_coe]
    exact hubF
  have hzdH : g⁻¹ * uWd * g ∈ torusGroup Tag.E6 L := by
    have h := htorus wd (by simp)
    change g⁻¹ * (ud : ModGL Tag.E6 L) * g ∈ torusGroup Tag.E6 L at h
    rwa [hud_coe] at h
  have hzdF : TwistedDiag.n0 L * twistE6 L Fr (g⁻¹ * uWd * g) *
      (TwistedDiag.n0 L)⁻¹ = g⁻¹ * uWd * g := by
    rw [map_mul, map_mul, map_inv, huWdF, hgLang]
    rw [show TwistedDiag.n0 L = canonicalRep (coxeterSystem Tag.E6) L twE6W0 from rfl]
    group
  have hzd : g⁻¹ * uWd * g ∈ S.D.torus :=
    mem_twistedTorusOf.2 ⟨hzdH, hzdF⟩
  obtain ⟨a, ha⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hzd).1
  have hT : rootDiagUnit Tag.E6 a ∈ S.D.torus := ha ▸ hzd
  have hwd : uWd = g * rootDiagUnit Tag.E6 a * g⁻¹ := by
    rw [← ha]
    group
  have hwd3' : (wd : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
    simpa using congrArg (fun x : ↥(RecipeExcLang.twInndiagGroup K σ) =>
      (x : ModGL TwistTag.E6.tag K)) hwd3
  have hu3 : uWd ^ 3 = 1 := by
    have h := congrArg (fun x : ModGL TwistTag.E6.tag K =>
      bc x) hwd3'
    have h' : (bc (wd : ModGL TwistTag.E6.tag K) :
        ModGL Tag.E6 L) ^ 3 = 1 := by
      simpa [map_pow] using h
    simpa [huWd_coe] using h'
  have hz3 : (g⁻¹ * uWd * g) ^ 3 = 1 := by
    have hc : (g⁻¹ * uWd * g) ^ 3 = g⁻¹ * uWd ^ 3 * g := by
      rw [show g⁻¹ * uWd * g = g⁻¹ * uWd * (g⁻¹)⁻¹ by rw [inv_inv]]
      exact conj_pow
    rw [hc, hu3, mul_one, inv_mul_cancel]
  have hap : ∀ j, a j ^ 3 = 1 := by
    have h1 : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 1 := by
      have hmap : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
        (rootDiagUnitHom Tag.E6 L).map_pow a 3
      rw [hmap, ← ha, hz3, rootDiagUnit_one]
    exact fun j => congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h1) j
  have h1 : rootDiagUnit Tag.E6 a ≠ 1 := by
    intro hz1
    have hu1 : uWd = 1 := by
      rw [hwd, hz1]
      group
    apply hwd1
    have hbc : bc (wd : ModGL TwistTag.E6.tag K) = 1 := by
      rw [← huWd_coe]
      exact hu1
    have hbc_inj : Function.Injective bc :=
      baseChangeGL_injective (τ := Tag.E6) (algebraMap K L)
    exact Subtype.ext (hbc_inj (by rw [hbc]; simp))
  have hpow : rootDiagUnit Tag.E6 a ^ 3 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  have hzbH : g⁻¹ * uWb * g ∈ torusGroup Tag.E6 L := by
    have h := htorus wb (by simp)
    change g⁻¹ * (ub : ModGL Tag.E6 L) * g ∈ torusGroup Tag.E6 L at h
    rwa [hub_coe] at h
  have hzbF : TwistedDiag.n0 L * twistE6 L Fr (g⁻¹ * uWb * g) *
      (TwistedDiag.n0 L)⁻¹ = g⁻¹ * uWb * g := by
    rw [map_mul, map_mul, map_inv, huWbF, hgLang]
    rw [show TwistedDiag.n0 L = canonicalRep (coxeterSystem Tag.E6) L twE6W0 from rfl]
    group
  have hzb : g⁻¹ * uWb * g ∈ S.D.torus :=
    mem_twistedTorusOf.2 ⟨hzbH, hzbF⟩
  let y : ModGL Tag.E6 L := g⁻¹ * uWb * g
  have hy : y ∈ S.D.torus := hzb
  have hy_eq : y = g⁻¹ * uWb * g := rfl
  have hyZ : y ∈ torusGroup Tag.E6 L ⊔
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_left (mem_twistedTorusOf.1 hy).1
  have hyF : S.D.step y = y := by
    simpa [LangDatum.step, MulAut.conj_apply] using (mem_twistedTorusOf.1 hy).2
  let C := ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
  let eR : C ≃* ↥((twistedE6RootGroup K σ).map (bc)) :=
    (CFSG.TauCetiBridge.Twisted.rootGroupEquivDerived (t := TwistTag.E6) (L := L) (Fr := Fr)
      Nat.prime_two hn hKcard hσ hFr).trans (MulEquiv.subgroupCongr hder)
  have eR_coe : ∀ c : C,
      ((eR c : ↥((twistedE6RootGroup K σ).map (bc))) :
        ModGL Tag.E6 L) = bc (c : ModGL TwistTag.E6.tag K) := by
    intro c
    rfl
  let ι₀ : C →* ModGL Tag.E6 L :=
    ((twistedE6RootGroup K σ).map (bc)).subtype.comp eR.toMonoidHom
  let ιLang : C →* ModGL Tag.E6 L := (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp ι₀
  have hιLang_inj : Function.Injective ιLang :=
    (MulAut.conj S.D.g0⁻¹).injective.comp
      ((Subgroup.subtype_injective _).comp eR.injective)
  have hι₀_range : ι₀.range =
      ((twistedE6RootGroup K σ).map (bc)) := by
    have h : ι₀ = ((twistedE6RootGroup K σ).map (bc)).subtype.comp
        eR.toMonoidHom := rfl
    rw [h, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eR.surjective,
      ← MonoidHom.range_eq_map]
    exact Subgroup.range_subtype _
  have hιLang_range : ιLang.range = S.Γ := by
    change ιLang.range = D.Γ
    rw [show ιLang = (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp ι₀ from rfl,
      MonoidHom.range_comp, hι₀_range]
    exact hΓ.symm
  have hβd : ∀ c : C,
      ιLang (RecipeExcLang.twConj K σ wd c) =
        rootDiagUnit Tag.E6 a * ιLang c * (rootDiagUnit Tag.E6 a)⁻¹ := by
    intro c
    have hb : ι₀ (RecipeExcLang.twConj K σ wd c) =
        (ud : ModGL Tag.E6 L) * bc (c : ModGL TwistTag.E6.tag K) *
          (ud : ModGL Tag.E6 L)⁻¹ := by
      change ((eR (RecipeExcLang.twConj K σ wd c) :
        ↥((twistedE6RootGroup K σ).map (bc))) : ModGL Tag.E6 L) = _
      rw [eR_coe, RecipeExcLang.coe_twConj, map_mul, map_mul, map_inv, hud_coe]
    change S.D.g0⁻¹ * ι₀ (RecipeExcLang.twConj K σ wd c) * S.D.g0 =
      rootDiagUnit Tag.E6 a * (S.D.g0⁻¹ * bc
        (c : ModGL TwistTag.E6.tag K) * S.D.g0) * (rootDiagUnit Tag.E6 a)⁻¹
    rw [hg0, hb, hud_coe, hwd]
    group
  have hβb : ∀ c : C,
      ιLang (RecipeExcLang.twConj K σ wb c) = y * ιLang c * y⁻¹ := by
    intro c
    have hb : ι₀ (RecipeExcLang.twConj K σ wb c) =
        (ub : ModGL Tag.E6 L) * bc (c : ModGL TwistTag.E6.tag K) *
          (ub : ModGL Tag.E6 L)⁻¹ := by
      change ((eR (RecipeExcLang.twConj K σ wb c) :
        ↥((twistedE6RootGroup K σ).map (bc))) : ModGL Tag.E6 L) = _
      rw [eR_coe, RecipeExcLang.coe_twConj, map_mul, map_mul, map_inv, hub_coe]
    change S.D.g0⁻¹ * ι₀ (RecipeExcLang.twConj K σ wb c) * S.D.g0 =
      y * (S.D.g0⁻¹ * bc (c : ModGL TwistTag.E6.tag K) * S.D.g0) * y⁻¹
    rw [hg0, hb, hub_coe, show y = g⁻¹ * uWb * g from rfl]
    group
  have h3L : (3 : L) ≠ 0 := by
    intro h0
    have h23 : 2 ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h0
    omega
  have hTame := langSetup_hTame_of_prime S Nat.prime_three h3L (fun h => by cases h) hT hap h1
  let ρR : C ≃* TwE6Delta.RecipeR K n := ε
  let βd : MulAut C := RecipeExcLang.twConj K σ wd
  let βb : MulAut C := RecipeExcLang.twConj K σ wb
  have he_d : ∀ c : C, ρR (βd c) = TwE6Transport.recipeConj σ ε wd (ρR c) := by
    intro c
    rw [TwE6Transport.recipeConj_apply]
    rw [show ε.symm (ε c) = c from ε.symm_apply_apply c]
  have he_b : ∀ c : C, ρR (βb c) = TwE6Transport.recipeConj σ ε wb (ρR c) := by
    intro c
    rw [TwE6Transport.recipeConj_apply]
    rw [show ε.symm (ε c) = c from ε.symm_apply_apply c]
  have hρRrange : Kc ≤ ρR.toMonoidHom.range := by
    rintro x -
    exact ⟨ρR.symm x, ρR.apply_symm_apply x⟩
  have hKsub : CFSG.Assembly.IsComponentOf (Kc.comap ρR.toMonoidHom) (fixedSubgroup βd) :=
    CFSG.ComponentClassification.GSThmB.Catalog7L4EU.HarrisN36.isComponentOf_comap_of_intertwine
      ρR.toMonoidHom ρR.injective he_d hKc hρRrange
  have hKsub' : CFSG.Open.IsComponentOf (Kc.comap ρR.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup βd) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hKsub
  obtain ⟨Dc⟩ := nonempty_toralLangComp
    (φ := (TwE6Transport.recipeConj σ ε wb).toMonoidHom) (hnorm := hnorm) S a ιLang
    hιLang_inj hιLang_range βd hβd hT hap h1 hTame (ρR := ρR) βb hβb he_b hKsub' hy hyZ hyF
  exact ⟨S, a, Dc, rfl, hT, hap, hpow, h1, hwd⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
