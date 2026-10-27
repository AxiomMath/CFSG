module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Inner
public import CFSG.HardMathSupport.Dickson.I271.ChevPBal
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterStep

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance

section Elements

variable {X : Type} [Group X] [Finite X]

theorem lift_data_of_inner {p : ℕ} {K : Subgroup X} {a k : X} (hap : a ^ p = 1)
    (haC : a ∉ Subgroup.centralizer (K : Set X)) (hk : k ∈ K)
    (hc : k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    (⟨k, hk⟩ : ↥K) ∉ Subgroup.center ↥K ∧ (⟨k, hk⟩ : ↥K) ^ p ∈ Subgroup.center ↥K := by
  refine ⟨?_, ?_⟩
  · intro hz
    apply haC
    have hk1 : k ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)
    have : a = k * (k⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ hk1 hc
  · have hcomm : Commute k (k⁻¹ * a) := Subgroup.mem_centralizer_iff.1 hc k hk
    have h1 : k ^ p * (k⁻¹ * a) ^ p = 1 := by
      rw [← hcomm.mul_pow]
      have : k * (k⁻¹ * a) = a := by group
      rw [this, hap]
    have h2 : k ^ p ∈ Subgroup.centralizer (K : Set X) := by
      have : k ^ p = ((k⁻¹ * a) ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc p)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 g g.2)

end Elements

section Step

variable {X : Type} [Group X] [Finite X]

theorem strong_of_constrained {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName}
    (hOut : SporadicOuterLeTwo) (hH : I271Hyp p K B) (hN : I271Norm p K B)
    (hS : I271SporType K name)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    (hcon : ∀ k : ↥K, k ∉ Subgroup.center ↥K → k ^ p ∈ Subgroup.center ↥K →
      PConstrainedShape p (Subgroup.centralizer ({k} : Set ↥K))) :
    IsStronglyBalancedIn p B K := by
  have hp := hH.prime
  have hp2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hO : GLAPPrimeCore p ↥K = ⊥ := i271h_primeCore_eq_bot hH.core hH.comp
  have hdvd : p ∣ Nat.card K := i116e_dvd_card hp hH.core hH.comp
  have hBel : IsElemAbelian p B := hH.scp.2.1
  obtain ⟨hBN, h2⟩ := hN
  have hSC : IsSCp p (K ⊔ B) B :=
    ⟨le_sup_right, hBel, fun E _ hEel hBE => hH.scp.2.2 E le_top hEel hBE⟩
  obtain ⟨A, hAB, hAnc, hAf⟩ := exists_faithful_noncyclic hp hBel hBN h2
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAB.trans hBN
  have hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := fun a ha =>
    exists_inner_of_spor hp hp2 hOut hq hS hBN hBel (hAB ha)
  have hloc' : IsCompLocallyBalanced p 1 A K :=
    isCompLocallyBalanced_of_inner_loc hp hq hO hloc hAN hin
  have hno : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J := by
    intro a ha ha1 J hJ
    obtain ⟨k, hk, hc⟩ := hin a ha
    obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hBel.2 a (hAB ha))
      (not_mem_centralizer_of_faithful hAf ha ha1) hk hc
    exact not_glaPComponent_of_constrained hp hq hk hc (hcon ⟨k, hk⟩ hkZ hkp) hJ
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon'
    push Not at hcon'
    apply hAnc
    haveI : Subsingleton ↥A :=
      ⟨fun x y => Subtype.ext ((hcon' x x.2).trans (hcon' y y.2).symm)⟩
    exact isCyclic_of_subsingleton
  exact engine_full ⟨hp, hp2, hq, hdvd, hBN, hBel, hSC, hAB, hAnc, hloc',
    fun a ha ha1 J hJ => (hno a ha ha1 J hJ).elim⟩
    ⟨a₀, ha₀A, ha₀1, fun w _ _ _ J hJ => (hno a₀ ha₀A ha₀1 J hJ).elim⟩

end Step

end CFSG.HardMathSupport.Dickson.I271
