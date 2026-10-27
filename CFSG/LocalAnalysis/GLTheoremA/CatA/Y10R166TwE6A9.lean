module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwE6
public import CFSG.Quasithin.Background.A3FactsNumber
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwE6A4
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag

namespace TwE6A

theorem exists_prime_dvd_two_pow_add_one {n : ℕ} (hn : 2 ≤ n) :
    ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ q ∣ 2 ^ n + 1 ∧ (q ≠ 3 ∨ 9 ∣ 2 ^ n + 1) := by
  by_cases h3 : n = 3
  · subst h3
    exact ⟨3, Nat.prime_three, by norm_num, by norm_num, Or.inr (by norm_num)⟩
  · obtain ⟨r, hr, hrdvd, hr3⟩ :=
      CFSG.Quasithin.A3Facts.exists_prime_dvd_two_pow_add_one hn h3
    have hr2 : r ≠ 2 := by
      intro hr2
      rw [hr2] at hrdvd
      have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      have h2 : 2 ∣ (2 ^ n + 1) - 2 ^ n := Nat.dvd_sub hrdvd h1
      rw [show 2 ^ n + 1 - 2 ^ n = 1 by omega] at h2
      exact Nat.Prime.not_dvd_one Nat.prime_two h2
    exact ⟨r, hr, hr2, hrdvd, Or.inl hr3⟩

end TwE6A

section RootOfUnity


namespace TwE6A

theorem exists_rootOfUnity_kernelComponent (F : Type) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 2 ≤ n) :
    ∃ (q : ℕ) (ζ : (AlgebraicClosure F)ˣ)
      (i : KernelComponent (rootCharHom (twE6omega1Tuple ζ))),
      q.Prime ∧ q ≠ 2 ∧ q ∣ 2 ^ n + 1 ∧ (q ≠ 3 ∨ 9 ∣ 2 ^ n + 1) ∧ ζ ^ q = 1 ∧ ζ ≠ 1 := by
  classical
  obtain ⟨q, hq, hq2, hqdvd, hq3⟩ := TwE6A.exists_prime_dvd_two_pow_add_one hn
  haveI : Fact q.Prime := ⟨hq⟩
  have hF2 : Nat.card F = 2 ^ (2 * n) := by
    rw [hF, mul_comm 2 n, pow_mul]
  have hqunits : q ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF2]
    refine hqdvd.trans ?_
    rw [CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one n]
    exact dvd_mul_left _ _
  obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) q hqunits
  have hζ₀q : ζ₀ ^ q = 1 := by rw [← hζ₀]; exact pow_orderOf_eq_one ζ₀
  have hζ₀1 : ζ₀ ≠ 1 := by
    intro h1
    have h1' : orderOf ζ₀ = 1 := by rw [h1]; exact orderOf_one
    rw [hζ₀] at h1'
    exact hq.ne_one h1'
  let ζ : (AlgebraicClosure F)ˣ := Units.map (algebraMap F (AlgebraicClosure F)).toMonoidHom ζ₀
  have hζq : ζ ^ q = 1 := by
    rw [← map_pow, hζ₀q, map_one]
  have hζ1 : ζ ≠ 1 := by
    intro h1
    have h2 : (algebraMap F (AlgebraicClosure F)) (ζ₀ : F) = 1 := by
      have := congrArg Units.val h1
      simpa [ζ] using this
    have h3 : (ζ₀ : F) = 1 := (algebraMap F (AlgebraicClosure F)).injective (by simpa using h2)
    exact hζ₀1 (Units.ext h3)
  have hmem : (Pi.single (1 : Fin Tag.E6.rank) 1) ∈
      kernelRoots (rootCharHom (twE6omega1Tuple ζ)) := by
    rw [kernelRoots_omega1 hq hζq hζ1]
    refine ⟨isRoot_single Tag.E6 1, ?_⟩
    rw [Pi.single_eq_of_ne (show (0 : Fin Tag.E6.rank) ≠ 1 by decide)]
  exact ⟨q, ζ, ⟦⟨_, hmem⟩⟧, hq, hq2, hqdvd, hq3, hζq, hζ1⟩

end TwE6A

end RootOfUnity

section Model


theorem exists_mulEquiv_twE6C_of_isLabel {X : Type} [Group X] [Finite X] {lab : GLALabel}
    (hX : HasLabel X (fun l => l = lab)) (ht : lab.tag = .twE6) (hn : 2 ≤ lab.n)
    (hZ : Subgroup.center X = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (σ : F ≃+* F),
      Nat.card F = (2 ^ lab.n) ^ 2 ∧ (∀ c, σ c = c ^ (2 ^ lab.n)) ∧
      Nonempty (X ≃* ↥⁅thetaFixed (iterateFrobenius (AlgebraicClosure F) 2 lab.n),
        thetaFixed (iterateFrobenius (AlgebraicClosure F) 2 lab.n)⁆) := by
  classical
  obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨e1⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_twistedE6RootGroup_of_isLabel hX ht hZ
  letI : Field F := hField
  letI : Finite F := hFin
  haveI : Fintype F := Fintype.ofFinite F
  have hcard2 : Nat.card F = 2 ^ (lab.n * 2) := by
    rw [hcard, pow_mul]
  have hcardF : Fintype.card F = 2 ^ (lab.n * 2) := by
    rw [← Nat.card_eq_fintype_card, hcard2]
  have hcharF : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := lab.n * 2) hcardF
  letI : CharP F 2 := hcharF
  let Ω := AlgebraicClosure F
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 lab.n
  have hFr : ∀ c, Fr c = c ^ (2 ^ lab.n) := fun c => iterateFrobenius_def 2 lab.n c
  refine ⟨F, hField, hFin, hcharF, σ, hcard, hσ, ?_⟩
  have eBC : ↥(twistedE6RootGroup F σ) ≃* ↥(Cgrp F σ.toRingHom Ω) :=
    Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 F σ.toRingHom)
      (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap F Ω)) (baseChangeGL_injective _)
  have e2 : ↥(Cgrp F σ.toRingHom Ω) ≃* ↥⁅thetaFixed Fr, thetaFixed Fr⁆ :=
    (twE6C_equiv_cgrp (ℓ := 2) (f := lab.n) (K := F) (σ := σ.toRingHom) (Ω := Ω)
      (Fr := Fr) Nat.prime_two (by omega) hcard hσ hFr).some.symm
  exact ⟨e1.trans (eBC.trans e2)⟩

end Model

end CFSG.LocalAnalysis.GLTheoremA.Y10F

end
