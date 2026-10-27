module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.GroupTheory.CoprimeNormalizerSup
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.UBSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.SeitzReduction.TwistedE6Pilot

theorem exists_subfield_twE6 {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra k F), Nat.card k = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card hn hF
  exact ⟨CFSG.LieType.Steinberg.fixedSubfield F 2 n, inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield (p := 2) (f := n) hF⟩

theorem twE6MaxA5_eq_foldedSetA : twE6MaxA5 = foldedSetA := rfl

section Certificates


theorem le_su6Levi_of_isPGroup {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k] [Field K]
    [Algebra k K] [Finite K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ f - 1) {E : Subgroup (ModGL TwistTag.E6.tag K)}
    (hE : E ≤ parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ)
    (hEp : IsPGroup p E) : E ≤ su6Levi σ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  obtain ⟨-, hsup, -, hcomm, -, -, -⟩ := su6Levi_facts hf hk hK hσ
  have hcent : thetaTorus (algebraMap k K) ≤
      Subgroup.centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) :=
    fun t ht => Subgroup.mem_centralizer_iff.2 fun l hl => hcomm l hl t ht
  have hnorm : thetaTorus (algebraMap k K) ≤
      Subgroup.normalizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hkunits : Nat.card kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hk]
  have hdvdT : Nat.card (thetaTorus (algebraMap k K)) ∣ Nat.card kˣ :=
    Subgroup.card_range_dvd
      ((thetaTorusHom K).comp (Units.map (algebraMap k K).toMonoidHom))
  have hcop : ¬ p ∣ Nat.card (thetaTorus (algebraMap k K)) := by
    intro h
    exact hpq (hkunits ▸ h.trans hdvdT)
  refine CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card hp hnorm hEp ?_ hcop
  intro e he
  rw [hsup]
  exact hE he

theorem le_su6Levi_of_isQuasisimple {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k] [Field K]
    [Algebra k K] [Finite K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {E : Subgroup (ModGL TwistTag.E6.tag K)}
    (hE : E ≤ parabolicLevi TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ)
    (hq : CFSG.IsQuasisimple ↥E) : E ≤ su6Levi σ := by
  obtain ⟨hperf, -, -⟩ := hq
  obtain ⟨-, hsup, -, hcomm, -, -, -⟩ := su6Levi_facts hf hk hK hσ
  let T : Subgroup (ModGL TwistTag.E6.tag K) := thetaTorus (algebraMap k K)
  have hTcomm : IsMulCommutative ↥T :=
    Subgroup.range_isMulCommutative
      ((thetaTorusHom K).comp (Units.map (algebraMap k K).toMonoidHom))
  letI : IsMulCommutative ↥T := hTcomm
  have hP : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hperf
  have hPle : E ≤ su6Levi σ ⊔ T := by
    intro e he
    rw [hsup]
    exact hE he
  exact CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.le_of_perfect_of_le_sup_normalizing
    (su6Levi σ) T E (fun t ht l hl => by
      rw [← hcomm l hl t ht, mul_inv_cancel_right]
      exact hl) hP hPle

theorem exists_pow_eq_one_centralizer_su6Levi {f : ℕ} (hf : 1 ≤ f) {k K : Type} [Field k]
    [Field K] [Algebra k K] [Finite K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ f + 1) :
    ∃ y : ModGL TwistTag.E6.tag K, y ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
      y ∈ Subgroup.centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) ∧ y ^ p = 1 ∧
      y ∉ su6Levi σ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨X, hXJ, hXcyc, hXcard⟩ := exists_nonsplit_le_thetaRankOneGroup hf hk hK
  obtain ⟨-, hdisj, hXcent, hXC0⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hXcard hXcyc
  have hdvd : p ∣ Nat.card X := by
    rw [hXcard]
    exact hpq
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hord : orderOf (x : ModGL TwistTag.E6.tag K) = p := by
    rw [Subgroup.orderOf_coe x, hxord]
  refine ⟨(x : ModGL TwistTag.E6.tag K), hXC0 x.2, hXcent x.2, ?_, ?_⟩
  · exact hord ▸ pow_orderOf_eq_one _
  · intro hxL
    have hx1 : (x : ModGL TwistTag.E6.tag K) = 1 :=
      (Subgroup.disjoint_def.1 hdisj) x.2 hxL
    have : orderOf (x : ModGL TwistTag.E6.tag K) = 1 := by
      rw [hx1]
      exact orderOf_one
    rw [hord] at this
    exact hp.ne_one this

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
