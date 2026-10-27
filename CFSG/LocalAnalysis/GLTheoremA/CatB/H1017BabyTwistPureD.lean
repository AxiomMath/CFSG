module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDLin
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
public import CFSG.Monster.B.GSide.TwoDNativeOrderFinal
public import CFSG.Monster.B.CTIB.FourClasses
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.B.TwoA.Sp8.Normalizer
public import CFSG.Monster.B.TwoA.Sp8.Orth8Plus
public import CFSG.Monster.B.TwoA.Sp8.QuadForm
public import CFSG.Monster.B.TwoA.Sp8.GenActionImage
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.B.Pinned.Primes.SeedGL
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS Subgroup
open CFSG.Monster.B.TwoA (Shat Dfull)
open CFSG.Monster.B.TwoA.Sp8 (V8 b0 Xgrp Lgrp rhoXSp rhoXSp_surjective ker_rhoXSp natCard_Lgrp
  Lgrp_le_Xgrp P4p_le_Xgrp nondegenerate_b0 b0_isAlt)
open CFSG.Monster.B.GSide (t2DS orderOf_t2DS natCard_centralizer_t2DS centralizer_t2DS_eq
  mem_P4pS)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (phiB t3)

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid


attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent in
theorem babyNoPureFourAt_two
    : BabyNoPureFourAt 2 := by
  intro t ht D hDt hD hDcard
  by_contra! hpure
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨ε⟩ : Nonempty (Shat ≃* NativeSporadic.B) :=
    ⟨CFSG.Monster.B.CTIB.sEquiv.symm.trans CFSG.Monster.B.CTIB.iotaEquiv.symm⟩
  have h2D : BabyInv 2 (ε t2DS) := by
    refine ⟨?_, ?_⟩
    · rw [MulEquiv.orderOf_eq]
      exact orderOf_t2DS
    · rw [← Nat.card_congr (CFSG.Monster.B.CTIB.centralizerEquiv ε t2DS).toEquiv,
        natCard_centralizer_t2DS]
      rfl
  obtain ⟨g, hg⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 2 t _ ht h2D)
  have hX : ∀ d ∈ D, ((ε.symm (g * d * g⁻¹) : Shat) : Dfull) ∈ Xgrp := by
    intro d hd
    have hc : d * t = t * d := (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 (hDt hd)
    have h : ε.symm (g * d * g⁻¹) ∈ centralizer ({t2DS} : Set Shat) := by
      rw [mem_centralizer_singleton_iff]
      apply ε.injective
      rw [map_mul ε, map_mul ε, MulEquiv.apply_symm_apply, ← hg]
      calc g * d * g⁻¹ * (g * t * g⁻¹) = g * (d * t) * g⁻¹ := by group
        _ = g * (t * d) * g⁻¹ := by rw [hc]
        _ = g * t * g⁻¹ * (g * d * g⁻¹) := by group
    rw [centralizer_t2DS_eq, mem_P4pS] at h
    exact P4p_le_Xgrp h
  let φ : D →* Xgrp :=
    { toFun := fun d => ⟨((ε.symm (g * d * g⁻¹) : Shat) : Dfull), hX d d.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun d₁ d₂ => Subtype.ext (by
        show ((ε.symm (g * (d₁ * d₂ : NativeSporadic.B) * g⁻¹) : Shat) : Dfull) =
          ((ε.symm (g * d₁ * g⁻¹) * ε.symm (g * d₂ * g⁻¹) : Shat) : Dfull)
        rw [← map_mul, show g * (d₁ * d₂ : NativeSporadic.B) * g⁻¹ =
          g * d₁ * g⁻¹ * (g * d₂ * g⁻¹) by group]) }
  have hφ : ∀ d : D, ((φ d : Xgrp) : Dfull) = ((ε.symm (g * d * g⁻¹) : Shat) : Dfull) :=
    fun _ => rfl
  have hE3 : ∀ e : D, e ^ 3 = 1 := fun e => Subtype.ext (by simpa using hD.2 e e.2)
  let ρ : D →* Module.End (ZMod 2) V8 :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((TauCeti.BilinForm.isometryGroup b0).subtype.comp (rhoXSp.comp φ))
  have hρ' : ∀ e : D, ∀ v, ρ e v = (rhoXSp (φ e) : V8 ≃ₗ[ZMod 2] V8) v := fun _ _ => rfl
  have hcardker : Nat.card rhoXSp.ker = 2 ^ 25 := by
    rw [ker_rhoXSp, Nat.card_congr (subgroupOfEquivOfLe Lgrp_le_Xgrp).toEquiv, natCard_Lgrp]
  have hρ : ∀ e : D, (∀ v, ρ e v = v) → e = 1 := by
    intro e he
    have h1 : φ e ∈ rhoXSp.ker :=
      MonoidHom.mem_ker.2 (Subtype.ext (LinearEquiv.ext fun v => (hρ' e v).symm.trans (he v)))
    have h2 : orderOf (φ e) ∣ 2 ^ 25 := hcardker ▸ Subgroup.orderOf_dvd_natCard _ h1
    have h3 : orderOf (φ e) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hE3 e, map_one])
    have h4 : orderOf (φ e) ∣ Nat.gcd 3 (2 ^ 25) := Nat.dvd_gcd h3 h2
    rw [show Nat.gcd 3 (2 ^ 25) = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h4
    have h5 := congrArg (fun x : Xgrp => (x : Dfull)) h4
    simp only [hφ, OneMemClass.coe_one] at h5
    have h6 : g * (e : NativeSporadic.B) * g⁻¹ = 1 := by
      simpa using congrArg ε (Subtype.ext h5 : ε.symm (g * e * g⁻¹) = 1)
    refine Subtype.ext ?_
    simpa using h6
  have hiso : ∀ (e : D) (u v : V8), b0 (ρ e u) (ρ e v) = b0 u v := fun e u v =>
    TauCeti.BilinForm.mem_isometryGroup_iff.1 (rhoXSp (φ e)).2 u v
  haveI := hD.1
  obtain ⟨a, ha, T, hT, hT7, hTc⟩ :=
    letI : CommGroup D := { (inferInstance : Group D) with mul_comm := fun a b => mul_comm' a b }
    PureD.exists_commute_isometry_orderOf_seven (V := V8) (E := D) b0 hE3 nondegenerate_b0
      b0_isAlt ρ hρ hiso hDcard
  obtain ⟨y, hy⟩ := rhoXSp_surjective (⟨T, hT⟩ : TauCeti.BilinForm.isometryGroup b0)
  have hTc' : ∀ v, T ((rhoXSp (φ a) : V8 ≃ₗ[ZMod 2] V8) v) =
      (rhoXSp (φ a) : V8 ≃ₗ[ZMod 2] V8) (T v) := hTc
  have hk : rhoXSp y * rhoXSp (φ a) = rhoXSp (φ a) * rhoXSp y := by
    rw [hy]
    exact Subtype.ext (LinearEquiv.ext hTc')
  have h3 : IsPGroup 3 (zpowers (φ a)) := by
    have hpow : φ a ^ 3 = 1 := by rw [← map_pow, hE3 a, map_one]
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (show orderOf (φ a) ∣ 3 ^ 1 from orderOf_dvd_of_pow_eq_one hpow)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨n, hn, hcomm⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_mem_ker_mul_commute
    Nat.prime_three rhoXSp (by rw [hcardker]; norm_num) h3 hk
  have h7 : 7 ∣ orderOf (y * n) := by
    have h := orderOf_map_dvd rhoXSp (y * n)
    rw [map_mul, (MonoidHom.mem_ker).1 hn, mul_one, hy, Subgroup.orderOf_mk, hT7] at h
    exact h
  have ha1 : (a : NativeSporadic.B) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨c, hc⟩ := isConj_iff.1 (hpure a a.2 ha1)
  let κ : Xgrp →* NativeSporadic.B :=
    ((MulAut.conj (c * g⁻¹)).toMonoidHom.comp ε.toMonoidHom).comp
      (Subgroup.inclusion CFSG.Monster.B.TwoA.Sp8.Xgrp_le_Shat)
  have hκ : Function.Injective κ :=
    ((MulAut.conj (c * g⁻¹)).injective.comp ε.injective).comp (Subgroup.inclusion_injective _)
  have hκa : κ (φ a) = phiB (t3 1) := by
    show (MulAut.conj (c * g⁻¹)) (ε (ε.symm (g * a * g⁻¹))) = _
    rw [MulEquiv.apply_symm_apply, MulAut.conj_apply, ← hc]
    group
  have hmem : κ (y * n) ∈ centralizer ({phiB (t3 1)} : Set NativeSporadic.B) := by
    rw [mem_centralizer_singleton_iff (G := NativeSporadic.B), ← hκa, ← map_mul, ← map_mul,
      hcomm]
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  rw [orderOf_injective κ hκ] at hdvd
  exact CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.bThreeB_seven_free
    (h7.trans hdvd)

end CFSG.LocalAnalysis.GLTheoremA.H1017
