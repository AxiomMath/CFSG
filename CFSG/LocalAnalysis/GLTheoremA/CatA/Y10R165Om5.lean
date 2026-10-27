module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
public import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.GF2n.Stroth80 QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

namespace OmEngine

theorem not_isPlusType_of_fixedPointFree_odd [Finite F] [CharP F 2]
    {W : Type} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    {Q : QuadraticForm F W} (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F W = 4) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : Nat.card F = 2 ^ n) (hm0 : 3 ≤ CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n)
    {x : W ≃ₗ[F] W} (hx : OddOrderIsometry Q p x) (hfree : ∀ v, x v = v → v = 0) :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
  intro hplus
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxne : x ≠ 1 := by
    intro h
    have hzero : ∀ v : W, v = 0 := fun v => hfree v (by rw [h]; rfl)
    have : Module.finrank F W = 0 := by
      rw [Module.finrank_zero_iff]
      exact ⟨fun a b => by rw [hzero a, hzero b]⟩
    omega
  have hxord : orderOf x = p := orderOf_eq_prime hx.pow_eq_one hxne
  have hker : LinearMap.ker ((x : W →ₗ[F] W) - 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hfree v (sub_eq_zero.mp hv)
  have hrange : Module.finrank F (LinearMap.range ((x : W →ₗ[F] W) - 1)) = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker ((x : W →ₗ[F] W) - 1)
    rw [hker, finrank_bot, add_zero, hdim] at h
    omega
  have hdvd : orderOf ((Nat.card F : ℕ) : ZMod p) ∣ 4 := by
    have h := CFSG.RankThree.GF2n.Stroth80.orderOf_card_dvd_finrank_range
      (K := F) (V := W) (g := x) hp hp2 hxord
    rwa [hrange] at h
  have hordq : orderOf ((Nat.card F : ℕ) : ZMod p) =
      CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n := by
    rw [CFSG.LocalAnalysis.GLTheoremA.rk2Ord, hn]
    push_cast
    rfl
  have hm04 : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ∣ 4 := by
    rwa [← hordq]
  have hm0le : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≤ 4 :=
    Nat.le_of_dvd (by norm_num) hm04
  have hm0eq : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n = 4 := by
    have hmne : CFSG.LocalAnalysis.GLTheoremA.rk2Ord p n ≠ 3 := by
      intro h
      rw [h] at hm04
      norm_num at hm04
    omega
  have hord4 : orderOf ((Nat.card F : ℕ) : ZMod p) = 4 := by
    rw [hordq, hm0eq]
  have hq4 : ((Nat.card F : ℕ) : ZMod p) ^ 4 = 1 := by
    rw [← hord4]
    exact pow_orderOf_eq_one _
  have hq2ne : ((Nat.card F : ℕ) : ZMod p) ^ 2 ≠ 1 := by
    intro h2
    have hd : orderOf ((Nat.card F : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hord4] at hd
    omega
  have hsum : ((Nat.card F : ℕ) : ZMod p) ^ 2 + 1 = 0 := by
    have h0 : (((Nat.card F : ℕ) : ZMod p) ^ 2 - 1) *
        (((Nat.card F : ℕ) : ZMod p) ^ 2 + 1) = 0 := by
      have heq : (((Nat.card F : ℕ) : ZMod p) ^ 2 - 1) *
          (((Nat.card F : ℕ) : ZMod p) ^ 2 + 1) =
          ((Nat.card F : ℕ) : ZMod p) ^ 4 - 1 := by ring
      rw [heq, hq4]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hq2ne
    · exact h
  have hq2p1_nat : p ∣ Nat.card F ^ 2 + 1 := by
    have hcast : (((Nat.card F ^ 2 + 1 : ℕ)) : ZMod p) = 0 := by
      push_cast
      exact hsum
    exact (ZMod.natCast_eq_zero_iff _ p).mp hcast
  have hq2p1 : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + 1 := by
    obtain ⟨k, hk⟩ := hq2p1_nat
    exact ⟨k, by exact_mod_cast hk⟩
  let O := TauCeti.QuadraticMap.orthogonalGroup Q
  have hpdvdO : p ∣ Nat.card O := by
    have h1 : orderOf (⟨x, hx.mem⟩ : ↥O) ∣ Nat.card ↥O := orderOf_dvd_natCard _
    have h2 : orderOf (⟨x, hx.mem⟩ : ↥O) = p := by
      rw [Subgroup.orderOf_mk]
      exact hxord
    rwa [h2] at h1
  have hpdvdOZ : (p : ℤ) ∣ (Nat.card O : ℤ) := by exact_mod_cast hpdvdO
  have hcard := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (K := F) (V := W) (Q := Q) hQ (m := 1) (by omega)
    (Or.inl ⟨rfl, hplus⟩)
  have hprod : (∏ i ∈ Finset.Icc 1 1, ((((Nat.card F : ℤ)) ^ 2) ^ i - 1)) =
      (Nat.card F : ℤ) ^ 2 - 1 := by
    simp
  rw [hprod, show (1 * 2 : ℕ) = 2 by norm_num] at hcard
  have hpdvd_expr : (p : ℤ) ∣ 2 * (Nat.card F : ℤ) ^ 2 *
      ((Nat.card F : ℤ) ^ 2 - 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    rw [← hcard]
    exact hpdvdOZ
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2' : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h2n : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2n)
  have hq : ¬ (p : ℤ) ∣ (Nat.card F : ℤ) := by
    intro h
    have hq2 : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 := dvd_pow h (by norm_num)
    have h1 : (p : ℤ) ∣ 1 := by
      have := dvd_sub hq2p1 hq2
      simpa using this
    exact hpZ.not_dvd_one h1
  have hq2 : ¬ (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 := by
    intro h
    exact hq (hpZ.dvd_of_dvd_pow h)
  have hq2m1 : ¬ (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 - 1 := by
    intro h
    have h2d : (p : ℤ) ∣ 2 := by
      have := dvd_sub hq2p1 h
      simpa using this
    exact h2' h2d
  have hmain : ¬ (p : ℤ) ∣ 2 * (Nat.card F : ℤ) ^ 2 *
      ((Nat.card F : ℤ) ^ 2 - 1) * ((Nat.card F : ℤ) ^ 2 - 1) := by
    intro h
    have h2q : ¬ (p : ℤ) ∣ 2 * (Nat.card F : ℤ) ^ 2 := fun hh =>
      (hpZ.dvd_mul.mp hh).elim h2' hq2
    have hmid : ¬ (p : ℤ) ∣ (2 * (Nat.card F : ℤ) ^ 2) *
        ((Nat.card F : ℤ) ^ 2 - 1) := fun hh =>
      (hpZ.dvd_mul.mp hh).elim h2q hq2m1
    exact (hpZ.dvd_mul.mp h).elim hmid hq2m1
  exact hmain hpdvd_expr

theorem isQuasisimple_supportedFixedDerived_of_four [Finite F] [CharP F 2]
    [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (h4 : Module.finrank F ↥(fixedSpace x) = 4)
    (hns : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Q.comp (fixedSpace x).subtype)) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) := by
  have h3 : 3 ≤ Module.finrank F ↥(fixedSpace x) := by omega
  have hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype) := by
    rintro (⟨h, -⟩ | ⟨⟨h, hsplit⟩, -⟩)
    · omega
    · obtain ⟨S, hS, hSQ⟩ := hsplit
      exact hns ⟨S, by omega, hSQ⟩
  have hns' : ¬ (Module.finrank F ↥(fixedSpace x) = 4 ∧
      ∃ S : Submodule F ↥(fixedSpace x), Module.finrank F S = 2 ∧
        ∀ y ∈ S, (Q.comp (fixedSpace x).subtype) y = 0) := by
    rintro ⟨-, S, hS, hSQ⟩
    exact hns ⟨S, by omega, hSQ⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hx).symm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (CFSG.RankThree.PartOne.orthDerivedEquivCommutator _)
      (orthogonal_regular_space_derived_quasisimple _
        hx.polarBilin_fixed_nondegenerate h3 hnexc hns'))

end OmEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F
