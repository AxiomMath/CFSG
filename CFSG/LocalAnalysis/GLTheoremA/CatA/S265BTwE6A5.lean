module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24LineLang
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BTwE6A5Aux
import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaUpgrade

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Seitz CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TwE6RootAs

section Fixed


private theorem fixedPoints_zpowers_conj_eq {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (h : twistedE6InndiagGL K σ) :
    fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) =
      (Subgroup.centralizer
        ({(h : ModGL TwistTag.E6.tag K)} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
        (twistedE6RootGroup K σ) := by
  rw [← fixSubgroup_eq_fixedPoints]
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h1 : twistedE6InndiagConj K σ h x = x := hx
    have h2 := congrArg Subtype.val h1
    rw [twistedE6InndiagConj_apply] at h2
    calc (x : ModGL TwistTag.E6.tag K) * h
        = ((h : ModGL TwistTag.E6.tag K) * x * (h : ModGL TwistTag.E6.tag K)⁻¹) * h := by
          rw [h2]
      _ = h * x := by group
  · intro hx
    show twistedE6InndiagConj K σ h x = x
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply, ← hx]
    simp

end Fixed

section Main


theorem center_eq_bot_and_involution_mem_of_dim36 {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} (hK : Nat.card K = 4) (hσ : ∀ c, σ c = c ^ 2) {h : twistedE6InndiagGL K σ}
    (hh3 : h ^ 3 = 1) (hh1 : h ≠ 1) (hdim : twE6MatFixDim K σ h = 36)
    {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))) :
    Subgroup.center ↥J = ⊥ ∧
      ∀ v ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)), v * v = 1 → v ∈ J := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by rw [hchar]; decide
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ 2 hK3 hσ (by rw [hK]; norm_num) le_rfl h hh1 hh3
  have hq2 : D.S.D.q = 2 := D.hSq.trans D.hqe.symm
  have h30 : (kernelRoots (rootCharHom D.a)).ncard = 30 := by
    have := D.hker
    omega
  obtain ⟨γ, ζ, hγ, hζ3, hζ1, hDa⟩ := exists_corootTuple_of_ncard_thirty D.hL3 D.hap h30
  obtain ⟨t, ht, Fr, hFr, hΦ0⟩ := D.hS
  obtain rfl : t = .E6 := by
    cases t
    · rfl
    · exact absurd ht (by decide)
  have hΦ : D.S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr :=
    MonoidHom.ext fun g => (hΦ0 g).trans rfl
  obtain ⟨v, hv⟩ := D.S.D.n_weyl
  have hlang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr D.S.D.g0 =
      D.S.D.g0 * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) v :=
    (congrArg (fun f => f D.S.D.g0) hΦ).symm.trans
      (D.S.D.lang.trans (congrArg (fun n => D.S.D.g0 * n) hv))
  have hg0 : D.S.D.g0 * rootDiagUnit Tag.E6 D.a * D.S.D.g0⁻¹ =
      baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
        (h : ModGL TwistTag.E6.tag K) := D.hg0
  have hcor : D.S.D.g0⁻¹ * baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K))
      (h : ModGL TwistTag.E6.tag K) * D.S.D.g0 = rootDiagUnit Tag.E6 D.a := by
    rw [← hg0]
    group
  rw [hDa] at hcor
  obtain ⟨X, D', hfix, hXc, hXodd, hXD, hDq, hDz, -, -, -⟩ :=
    twE6CorootCoreGen_of_upgrade twE6EnnolaUpgrade_holds twE6CorootCore_holds K σ 2
      (by rw [hK]; norm_num) hσ hchar 3 Nat.prime_three (by norm_num) Fr
      (fun c => by rw [hFr c, hq2]) v D.S.D.g0 D.S.D.g0_mem hlang
      (h : ModGL TwistTag.E6.tag K) h.2 γ hγ ζ hζ3 hζ1 hcor
  have hfp : fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) = X ⊔ D' := by
    rw [fixedPoints_zpowers_conj_eq, hfix]
  rw [hfp] at hJ ⊢
  exact center_eq_bot_and_mem_of_isComponentOf_sup hXc hXodd hXD hDq hDz hJ

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
