module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralDefs
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1RankSix
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent

private theorem three_not_dvd_sq_two_pow_of_dvd_add_one {n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) :
    ¬ 3 ∣ (2 ^ n) ^ 2 := by
  intro h
  have h2 : 3 ∣ 2 ^ n := Nat.prime_three.dvd_of_dvd_pow h
  have h1 : 3 ∣ (2 ^ n + 1) - 2 ^ n := Nat.dvd_sub h3 h2
  rw [Nat.add_sub_cancel_left] at h1
  exact Nat.prime_three.not_dvd_one h1

theorem isAlgebraic_of_ringEquiv_algebraMap {k K Ω : Type*} [Field k] [Field K] [Field Ω]
    [Algebra K Ω] [Algebra k Ω] (τ : k ≃+* K)
    (halg : ∀ x, algebraMap k Ω x = algebraMap K Ω (τ x))
    (h : Algebra.IsAlgebraic K Ω) : Algebra.IsAlgebraic k Ω := by
  refine Algebra.IsAlgebraic.mk fun ω => ?_
  obtain ⟨p, hp, hp0⟩ := h.isAlgebraic ω
  refine ⟨p.map τ.symm.toRingHom, ?_, ?_⟩
  · rw [Polynomial.map_ne_zero_iff τ.symm.injective]
    exact hp
  · rw [Polynomial.aeval_def] at hp0 ⊢
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap k Ω).comp τ.symm.toRingHom = algebraMap K Ω := by
      ext x
      change (algebraMap k Ω) (τ.symm x) = (algebraMap K Ω) x
      rw [halg (τ.symm x), RingEquiv.apply_symm_apply]
    rw [hcomp]
    exact hp0


theorem twE6BigToralExit_of (h : TwE6W0TorusExit) : TwE6BigToralExit := by
  intro G _ _ L J A d b n K _ _ hn hK h3 hS θ E hE3 hEcard hEI hEd hEb
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact three_not_dvd_sq_two_pow_of_dvd_add_one h3
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  let Ω := AlgebraicClosure K
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let Φ : ↥(TwistedDiag.Rgrp Ω Fr) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr
  have hΦinj : Function.Injective Φ :=
    NoOffTwE6Three.rgrpConjAut_injective hn hK σ hσ Fr hFr
  have hΦrange : Φ.range = (RecipeExcLang.twConj K σ).range :=
    NoOffTwE6Three.rgrpConjAut_range hn hK σ hσ Fr hFr
  let Ψ : ↥(TwistedDiag.Rgrp Ω Fr) →* MulAut (TwE6Delta.RecipeR K n) :=
    (MulAut.congr ε).toMonoidHom.comp Φ
  have hΨinj : Function.Injective Ψ := (MulAut.congr ε).injective.comp hΦinj
  have hΨrange : Ψ.range = (TwE6Transport.recipeConj σ ε).range := by
    change ((MulAut.congr ε).toMonoidHom.comp Φ).range =
      (TwE6Transport.recipeConj σ ε).range
    rw [MonoidHom.range_comp, hΦrange]
    exact (MonoidHom.range_comp (MulAut.congr ε).toMonoidHom
      (RecipeExcLang.twConj K σ)).symm
  have hErange : E ≤ Ψ.range := by
    intro φ hφ
    rw [hΨrange]
    exact (hε φ).2 (hEI φ hφ)
  let EZ : Subgroup ↥(TwistedDiag.Rgrp Ω Fr) := E.comap Ψ
  have hEZel : IsElemAbelian 3 EZ := hE3.comap hΨinj
  have hEZcard : Nat.card EZ = Nat.card E := by
    have hmap : EZ.map Ψ = E := Subgroup.map_comap_eq_self hErange
    calc Nat.card EZ = Nat.card (EZ.map Ψ) := (Subgroup.card_map_of_injective hΨinj).symm
      _ = Nat.card E := by rw [hmap]
  let Ē : Subgroup (ModGL Tag.E6 Ω) := EZ.map (TwistedDiag.Rgrp Ω Fr).subtype
  have hĒR : Ē ≤ TwistedDiag.Rgrp Ω Fr := Subgroup.map_subtype_le _
  have hĒadj : Ē ≤ adjointGroup Tag.E6 Ω := fun x hx =>
    (TwistedDiag.mem_Rgrp Fr).1 (hĒR hx) |>.1
  have hĒel : IsElemAbelian 3 Ē := hEZel.map _
  have hĒcard : Nat.card Ē = Nat.card E := by
    calc Nat.card Ē = Nat.card EZ :=
          Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      _ = Nat.card E := hEZcard
  obtain ⟨g, hg, hgT⟩ :=
    ExcFramesHalf.bigElemAbelianToralBar_E6_three K h3K Ē hĒadj
      (fun x hx y hy => hĒel.comm hx hy)
      (fun x hx => hĒel.2 x hx) (by
        change 3 ^ (Tag.E6.rank - 1) ≤ Nat.card Ē
        rw [hĒcard]
        exact hEcard)
  obtain ⟨φd, hφdE, hφdInd⟩ := hEd
  obtain ⟨φb, hφbE, hφbInd⟩ := hEb
  have hφdI : φd ∈ TwE6Delta.RecipeI K n := hEI φd hφdE
  have hφbI : φb ∈ TwE6Delta.RecipeI K n := hEI φb hφbE
  obtain ⟨wd, hwd⟩ := (hε φd).2 hφdI
  obtain ⟨wb, hwb⟩ := (hε φb).2 hφbI
  let yd : ↥(TwistedDiag.Rgrp Ω Fr) :=
    NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr wd
  let yb : ↥(TwistedDiag.Rgrp Ω Fr) :=
    NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr wb
  have hΨyd : Ψ yd = φd := by
    change (MulAut.congr ε) (NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr
      (NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr wd)) = φd
    rw [NoOffTwE6Three.rgrpConjAut_apply_baseChange]
    exact hwd
  have hΨyb : Ψ yb = φb := by
    change (MulAut.congr ε) (NoOffTwE6Three.rgrpConjAut hn hK σ hσ Fr hFr
      (NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr wb)) = φb
    rw [NoOffTwE6Three.rgrpConjAut_apply_baseChange]
    exact hwb
  have hydE : yd ∈ EZ := Subgroup.mem_comap.2 (by rw [hΨyd]; exact hφdE)
  have hybE : yb ∈ EZ := Subgroup.mem_comap.2 (by rw [hΨyb]; exact hφbE)
  have hxdĒ : ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ∈ Ē :=
    Subgroup.mem_map.2 ⟨yd, hydE, rfl⟩
  have hxbĒ : ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ∈ Ē :=
    Subgroup.mem_map.2 ⟨yb, hybE, rfl⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥Ē := Nat.finite_of_card_ne_zero (by
    rw [hĒcard]
    exact (lt_of_lt_of_le (by norm_num) hEcard).ne')
  let H : Subgroup (ModGL Tag.E6 Ω) :=
    Subgroup.zpowers ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ⊔
      Subgroup.zpowers ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω)
  have hHdef : H = Subgroup.zpowers ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ⊔
      Subgroup.zpowers ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) := rfl
  have hHle : H ≤ Ē := sup_le (Subgroup.zpowers_le.2 hxdĒ) (Subgroup.zpowers_le.2 hxbĒ)
  have hHcard : Nat.card H ∣ 3 ^ 2 := by
    have hyd3 : ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ^ 3 = 1 :=
      hĒel.2 _ hxdĒ
    have hyb3 : ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ^ 3 = 1 :=
      hĒel.2 _ hxbĒ
    by_cases hyd1 : ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) = 1
    · rw [hHdef, hyd1, Subgroup.zpowers_one_eq_bot, bot_sup_eq, Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one hyb3).trans (by norm_num : 3 ∣ 3 ^ 2)
    by_cases hyb1 : ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) = 1
    · rw [hHdef, hyb1, Subgroup.zpowers_one_eq_bot, sup_bot_eq, Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one hyd3).trans (by norm_num : 3 ∣ 3 ^ 2)
    by_cases hmem : ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ∈
        Subgroup.zpowers ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω)
    · rw [hHdef, sup_eq_left.2 (Subgroup.zpowers_le.2 hmem), Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one hyd3).trans (by norm_num : 3 ∣ 3 ^ 2)
    · have hydord : orderOf ((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) = 3 :=
        orderOf_eq_prime hyd3 hyd1
      have hybord : orderOf ((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) = 3 :=
        orderOf_eq_prime hyb3 hyb1
      let xd' : ↥Ē := ⟨((yd : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω), hxdĒ⟩
      let xb' : ↥Ē := ⟨((yb : ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω), hxbĒ⟩
      have hxdord' : orderOf xd' = 3 := by
        rw [Subgroup.orderOf_mk]
        exact hydord
      have hxbord' : orderOf xb' = 3 := by
        rw [Subgroup.orderOf_mk]
        exact hybord
      have hmem' : xb' ∉ Subgroup.zpowers xd' := by
        intro h
        apply hmem
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
        exact Subgroup.mem_zpowers_iff.2 ⟨m, by
          have := congrArg Subtype.val hm
          simpa using this⟩
      have htop : IsElemAbelian 3 (⊤ : Subgroup ↥Ē) := by
        rw [← Subgroup.subgroupOf_self]
        exact hĒel.subgroupOf Ē
      have h9 := (CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_mem_isElemAbelian
        (p := 3) htop (Subgroup.mem_top xd') (Subgroup.mem_top xb')
        hxdord' hxbord' hmem').2
      have hmap : (Subgroup.zpowers xd' ⊔ Subgroup.zpowers xb').map Ē.subtype = H := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, hHdef]
        rfl
      rw [← hmap, Subgroup.card_map_of_injective (Subtype.val_injective), h9]
  have hHdvd : Nat.card H ∣ 3 ^ 4 := hHcard.trans (by norm_num : 3 ^ 2 ∣ 3 ^ 4)
  have hĒp : IsPGroup 3 Ē := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hĒel.2 (x : ModGL Tag.E6 Ω) x.2)⟩
  obtain ⟨k, hk⟩ := hĒp.exists_card_eq
  have hk4 : 4 ≤ k := by
    have h5 : 5 ≤ k := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp
      rw [← hk, hĒcard]
      exact hEcard
    omega
  have hĒdvd : 3 ^ 4 ∣ Nat.card Ē := by
    rw [hk]
    exact Nat.pow_dvd_pow 3 hk4
  obtain ⟨X, hXcard, hHX, hXĒ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    Nat.prime_three hHdvd hĒdvd hHle
  have hX3 : IsElemAbelian 3 X := hĒel.mono hXĒ
  have hXcard' : Nat.card X = 3 ^ 4 := hXcard
  have hXR : X ≤ TwistedDiag.Rgrp Ω Fr := hXĒ.trans hĒR
  have hXt : NoOffTwE6Three.IsToralE6 Ω X :=
    ⟨g, hg, fun x hx => hgT x (hXĒ hx)⟩
  let k := GaloisField 2 (2 * n)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype k := Fintype.ofFinite k
  have hcardk : Fintype.card k = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  let τ : k ≃+* K := FiniteField.ringEquivOfCardEq hcardk
  letI : Algebra k Ω := ((algebraMap K Ω).comp τ.toRingHom).toAlgebra
  haveI : IsAlgClosure k Ω :=
    ⟨IsAlgClosure.isAlgClosed K,
      isAlgebraic_of_ringEquiv_algebraMap τ (fun x => rfl) (AlgebraicClosure.isAlgebraic K)⟩
  have h30 : (3 : Ω) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root h30
  obtain ⟨g', hg'G, hg'F, hg'X⟩ :=
    CFSG.StandardType.TwE6LemmaK.ggTwE6ThreeToralTypeMinusOneInput (f := n) (by omega) h3 Ω Fr hFr
      hζ hζo hXR hX3 hXcard' hXt
  refine h G L J A d b n K hn hK h3 hS σ hσ ε θ wd wb
    (by rw [hwd]; exact hφdInd) (by rw [hwb]; exact hφbInd) Fr hFr g' hg'G hg'F ?_
  intro w hw
  have hxX : ((NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr w :
      ↥(TwistedDiag.Rgrp Ω Fr)) : ModGL Tag.E6 Ω) ∈ X := by
    rcases hw with rfl | rfl
    · exact hHX (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · exact hHX (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  obtain ⟨v, hv⟩ := hg'X _ hxX
  rw [hv]
  have : g'⁻¹ * (g' * rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) * g'⁻¹) * g' =
      rootDiagUnit Tag.E6 (TableBExc.E6Three.zetaVec ζ hζ v) := by group
  rw [this]
  exact rootDiagUnit_mem_torusGroup _

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
