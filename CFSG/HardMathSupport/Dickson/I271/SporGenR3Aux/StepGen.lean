module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Inner
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Leaf

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.Yardstones.Md0ec50421ce4

section StepGen

variable {X : Type} [Group X] [Finite X]

theorem strong_of_dichotomy_rk {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hH : CompHyp p K B) (hN : I271Norm p K B)
    (hS : I271SporType K name)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : ∀ (a k : X) (hk : k ∈ K), a ∈ B → k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) →
      a ∉ Subgroup.centralizer (K : Set X) →
        (∀ J : Subgroup X, ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
          ∃ J₀ : Subgroup X, J₀ ≤ K ∧
            (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
              J = J₀) ∧ Good (PSimple p (J₀.subgroupOf K)) ∧ Rk (PQuot p (J₀.subgroupOf K))) :
    IsStronglyBalancedIn p B K := by
  have hp := hH.prime
  have hp2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := hH.quasi
  have hO : GLAPPrimeCore p ↥K = ⊥ := hH.primeCore
  have hdvd : p ∣ Nat.card K := hH.dvd
  have hBel : IsElemAbelian p B := hH.elem
  obtain ⟨hBN, h2⟩ := hN
  have hSC : IsSCp p (K ⊔ B) B := hH.sc
  obtain ⟨A, hAB, hAnc, hAf⟩ := exists_faithful_noncyclic hp hBel hBN h2
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAB.trans hBN
  have hin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := fun a ha =>
    exists_inner_of_spor hp hp2 hOut hq hS hBN hBel (hAB ha)
  have hloc' : IsCompLocallyBalanced p 1 A K :=
    isCompLocallyBalanced_of_inner_loc hp hq hO hloc hAN hin
  have hdich : ∀ a ∈ A, a ≠ 1 →
      (∀ J : Subgroup X, ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
        ∃ J₀ : Subgroup X, J₀ ≤ K ∧
          (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
            J = J₀) ∧ Good (PSimple p (J₀.subgroupOf K)) ∧ Rk (PQuot p (J₀.subgroupOf K)) := by
    intro a ha ha1
    obtain ⟨k, hk, hc⟩ := hin a ha
    exact hD a k hk (hAB ha) hc (not_mem_centralizer_of_faithful hAf ha ha1)
  have hcomp : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J := by
    intro a ha ha1 J hJ
    rcases hdich a ha ha1 with hno | ⟨J₀, hJ₀K, huniq, hgood, hrk⟩
    · exact (hno J hJ).elim
    · have huniq' : ∀ I J : Subgroup X,
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I →
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → I = J :=
        fun I J hI hJ => (huniq I hI).trans (huniq J hJ).symm
      have hBN' : B ≤ Subgroup.normalizer (J : Set X) :=
        le_normalizer_of_unique hBN hBel (hAB ha) huniq' hJ
      refine ⟨hBN', ?_⟩
      set C := Subgroup.centralizer ({a} : Set X) with hC
      have hBC : B ≤ C := fun b hb =>
        Subgroup.mem_centralizer_singleton_iff.2
          (CFSG.Open.IsElemAbelian.comm hBel (hAB ha) hb).symm
      have hJK : J ≤ K := hJ.1.trans inf_le_left
      have hJC : J ≤ C := hJ.1.trans inf_le_right
      have hJcomp : GLAPComponent p C J := glaPComponent_centralizer hp hH.comp.2.1 hJ
      have hsn : IsSubnormal J C := hJcomp.2.1
      obtain ⟨hcoreC, hcompC, hSCC, hBNC⟩ := recursionData hp hJcomp hBC hBN' hH.scp
      have hJeq : J = J₀ := huniq J hJ
      have hgoodJ : Good (PSimple p (J.subgroupOf K)) := by
        rw [hJeq]
        exact hgood
      have hrkJ : Rk (PQuot p (J.subgroupOf K)) := by
        rw [hJeq]
        exact hrk
      let pS : PSimple p (J.subgroupOf K) ≃*
          (↥(barX p C J) ⧸ Subgroup.center ↥(barX p C J)) :=
        (pSimpleEquiv p (Subgroup.subgroupOfEquivOfLe hJK)).trans (pSimpleBarEquiv hp hJC hsn)
      let fQ : PQuot p (J.subgroupOf K) ≃* ↥(barX p C J) :=
        (pQuotEquiv p (Subgroup.subgroupOfEquivOfLe hJK)).trans (quotEquivBarX hp hJC hsn)
      have hbal := hIH (↥C ⧸ GLAPPrimeCore p ↥C) (barX p C J) (barX p C B)
        ⟨hp, hp2, hcoreC, hcompC, hSCC, hBNC⟩ (hGood _ _ pS hgoodJ) (hRk _ _ fQ hrkJ)
      exact stronglyLocallyOneBalanced_of_bar hp hsn hBN' hbal
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon'
    push Not at hcon'
    apply hAnc
    haveI : Subsingleton ↥A :=
      ⟨fun x y => Subtype.ext ((hcon' x x.2).trans (hcon' y y.2).symm)⟩
    exact isCyclic_of_subsingleton
  have hc : ∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
      (∀ b ∈ B, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X) := by
    refine ⟨a₀, ha₀A, ha₀1, fun w hw _ hwB J hJ => ?_⟩
    rcases hdich a₀ ha₀A ha₀1 with hno | ⟨J₀, hJ₀K, huniq, hgood, hrk⟩
    · exact (hno J hJ).elim
    · have huniq' : ∀ I J : Subgroup X,
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a₀} : Set X)) I →
          GLAPComponent p (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J → I = J :=
        fun I J hI hJ => (huniq I hI).trans (huniq J hJ).symm
      have hwC := mem_normalizer_inf_centralizer_of_comm hw (hwB a₀ (hAB ha₀A))
      have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ w
      rw [(mem_normalizer_iff_gLBConj_eq).1 hwC] at h1
      exact (mem_normalizer_iff_gLBConj_eq).2 (huniq' _ J h1 hJ)
  exact engine_full ⟨hp, hp2, hq, hdvd, hBN, hBel, hSC, hAB, hAnc, hloc', hcomp⟩ hc

theorem strong_of_dichotomy {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName}
    {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hOut : SporadicOuterLeTwo) (hH : CompHyp p K B) (hN : I271Norm p K B)
    (hS : I271SporType K name)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → IsStronglyBalancedIn p B' J)
    (hD : ∀ (a k : X) (hk : k ∈ K), a ∈ B → k⁻¹ * a ∈ Subgroup.centralizer (K : Set X) →
      a ∉ Subgroup.centralizer (K : Set X) →
        (∀ J : Subgroup X, ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) ∨
          ∃ J₀ : Subgroup X, J₀ ≤ K ∧
            (∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
              J = J₀) ∧ Good (PSimple p (J₀.subgroupOf K))) :
    IsStronglyBalancedIn p B K :=
  strong_of_dichotomy_rk (Rk := fun _ _ => True) hGood (fun _ _ _ _ _ h => h) hOut hH hN hS hloc
    (fun Y _ _ J B' h hG _ => hIH Y J B' h hG)
    (fun a k hk haB hc haC => (hD a k hk haB hc haC).imp_right
      fun ⟨J₀, h1, h2, h3⟩ => ⟨J₀, h1, h2, h3, trivial⟩)

end StepGen

end CFSG.HardMathSupport.Dickson.I271
