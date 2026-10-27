module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieConj
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

structure Pkg (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (x : Y) : Type 1 where
  K : Type
  [instField : Field K]
  [instFinite : Finite K]
  P' : Type
  [instGroup : Group P']
  eP : (↥L ⧸ center ↥L) ≃* P'
  M : MatModel 5 K P'
  hAut : AutHyps (thetaP L eP) M
  hout : thetaP L eP x ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner P'
  a : ℕ
  ha : 1 ≤ a
  hGL : (Nat.card M.𝔾).factorization 5 = 5 * a + 1
  hker : (Nat.card M.c.ker).factorization 5 = a
  e : C5 →* Kˣ
  he : Function.Injective e
  hmon : ∀ m : M5, monEmb e 5 m ∈ M.𝔾
  F : GL (Fin 5) K
  hF : F ∈ M.𝔾
  hFconj : F * monEmb e 5 (monS sig5) * F⁻¹ = (monEmb e 5 (mT ddv))⁻¹

attribute [instance] Pkg.instField Pkg.instFinite Pkg.instGroup

theorem five_ne_zero_of_dvd {K : Type} [Field K] [Finite K] (hpK : 5 ∣ Nat.card K - 1) :
    (5 : K) ≠ 0 := by
  intro h
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K ℓ
  have hdvd : ℓ ∣ 5 := (CharP.cast_eq_zero_iff K ℓ 5).mp (by exact_mod_cast h)
  have hℓ5 : ℓ = 5 := (Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_five).mp hdvd
  subst hℓ5
  have h1 : 5 ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self 5 m.ne_zero
  have h2 : 5 ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hpK
  have h3 : Nat.card K - (Nat.card K - 1) = 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  rw [h3] at h2
  exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
