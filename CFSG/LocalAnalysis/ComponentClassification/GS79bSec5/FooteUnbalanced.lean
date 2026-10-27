module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximalU
import CFSG.LocalAnalysis.ComponentClassification.GrSLitReach39
import CFSG.LocalAnalysis.ComponentClassification.GrSLitReduction
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitThmBReach
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitWeakMaximalDef
import CFSG.LocalAnalysis.ComponentClassification.HSFLitWeakMaximal

public section

namespace CFSG.ComponentClassification.GSFM

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

theorem false_of_footeMaximal_small_of_footeUnbalanced
    (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput) (hHSF : HarrisSolomonFritzInput)
    (hCI : ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {x : X} {y : X} {L : Subgroup X} (hx : orderOf x = 2)
    (hLx : L ≤ centralizer ({x} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))))
    (hL : GSMaximalComponent L) (hT : GSUnbalancingTriple x y L) (hLF : FooteLit.FooteMaximal L)
    (htype : Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) : False := by
  rcases hFU X hnonab hK hz hU x y L hT hLF htype with
    hlie | hrank | ⟨⟨e9⟩, -⟩ | ⟨⟨e10⟩, -⟩ | ⟨⟨e11⟩, -⟩ | ⟨⟨eJ⟩, -⟩
  · exact hU (uOutcome_of_oddLieType hlie)
  · obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(coreActionKernel L)) := inferInstance
    rcases sylow_cyclic_or_quaternion_of_pRank_eq_one hrank P with hcyc | ⟨r, hr, ⟨eP⟩⟩
    · have hall : ∀ Q : Sylow 2 ↥(coreActionKernel L),
          IsCyclic (Q : Subgroup ↥(coreActionKernel L)) :=
        fun Q => (MulEquiv.isCyclic (Sylow.equiv P Q)).mp hcyc
      rcases htype with ⟨⟨e7⟩⟩ | hpsl
      · have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
          alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
        have hs : IsSimpleGroup (L ⧸ pPrimeCore 2 L) := e7.isSimpleGroup
        obtain ⟨S⟩ : Nonempty (Sylow 2 (L ⧸ pPrimeCore 2 L)) := inferInstance
        have hS8 : Nat.card (S : Subgroup (L ⧸ pPrimeCore 2 L)) = 8 :=
          card_sylow_two_of_card_eq_2520
            (by rw [Nat.card_congr e7.toEquiv, card_alternating_seven]) S
        rcases hHSF X hnonab x hx L hLx hLc hs (pRank_two_of_mulEquiv_alternating_seven e7)
            ⟨S, hS8⟩ hall with hlie | ⟨⟨e6⟩, -⟩
        · exact hU (uOutcome_of_oddLieType hlie)
        · have h67 := Nat.card_congr (e6.symm.trans e7).toEquiv
          rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h67
          norm_num [Nat.factorial] at h67
      · exact hH X hnonab hK hz hU ⟨x, L, hx, hLx, hLc, hL, hpsl, hall⟩
    · exact false_of_quaternion_kernel hCI hnonab hz hU hx hLx hLc
        (GrSLit.two_le_pRank_of_small_type hLx hLc htype) hrank P hr eP
  · have h9 := mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e9 hz
    norm_num at h9
  · have h10 := mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e10 hz
    norm_num at h10
  · exact hU (uOutcome_of_mulEquiv_alternating_eleven e11)
  · exact false_of_mulEquiv_j2 eJ hz
theorem he_or_l34_of_reach_bound_of_footeUnbalanced
    (hTB : ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hB : GrSLit.TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a x : X} {J : Subgroup X}
    (hJ : GSMaximalUnbalancingTriple a x J)
    (hbound : ∀ (c v : X) (K : Subgroup X), GSUnbalancingTriple c v K →
      GrSLit.GSWeakReach J K → (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index) :
    Nonempty (J ⧸ pPrimeCore 2 J ≃* Blueprint.NativeSporadic.He) ∨
      (Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL 3 2 2 ∧
        GrSLit.GSWeakMaximalComponent J) := by
  have ha : orderOf a = 2 := hJ.1.1
  have hJa : J ≤ centralizer ({a} : Set X) := hJ.1.2.2.2.1
  have hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))) := hJ.1.2.2.2.2.1
  rcases hTB X hnonab hK hz hU a x J hJ.1 with ⟨n, hodd, hn, he⟩ | hsmall | hbig
  · exact absurd ⟨a, J, n, ha, hodd, hn, hJa, hJc, he⟩ (hSA X hnonab hK hz hU)
  · exfalso
    rcases hB X hnonab hK hz hU a x J hJ hbound (hsmall.imp id Or.inl) with
      ⟨-, b, L, ρ, e, hb, hLb, hL, hρ, hρ2, he, hLie, hbK, hP⟩ | ⟨hiso, hcentral⟩
    · refine (hH X hnonab hK hz hU) ⟨b, L, hb, hLb, hL,
        gsMaximalComponent_of_cyclic_kernel hb hLb hL hP,
        ⟨ρ, 2 * e, hρ, hρ2, by omega, ?_, hLie⟩, isCyclic_sylow_of_eq_zpowers hbK hP⟩
      have h3 : 3 ≤ ρ := by have := hρ.two_le; omega
      calc 5 ≤ 3 ^ 2 := by norm_num
        _ ≤ ρ ^ 2 := Nat.pow_le_pow_left h3 2
        _ ≤ ρ ^ (2 * e) := Nat.pow_le_pow_right hρ.pos (by omega)
    · exact false_of_footeMaximal_small_of_footeUnbalanced hH hFU hHSF hCI hnonab hK hz hU ha hJa hJc
        (gsMaximalComponent_of_B2 ha hJa hJc hiso hcentral) hJ.1
        (GrSLit.footeMaximal_of_B2 ha hJa hJc hiso hcentral) hsmall
  · rcases hbig with hHe | h34
    · exact Or.inl hHe
    · refine Or.inr ⟨h34, ?_⟩
      rcases hB X hnonab hK hz hU a x J hJ hbound (Or.inr (Or.inr h34)) with
        ⟨⟨p, f, -, hp2, -, hpsl⟩, -⟩ | ⟨hiso, hcentral⟩
      · exact (GrSLit.false_of_psl34_of_psl_two h34 hp2 hpsl).elim
      · exact GrSLit.gsWeakMaximalComponent_of_B2 ha hJa hJc hiso hcentral

end CFSG.ComponentClassification.GSFM

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem gsRestrictedType_of_gsUnbalancingTriple_of_footeUnbalanced (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hS : SchreierFor Blueprint.Catalog)
    (hB : TheoremBReachInput) (hH : HarrisInput) (hFU : FooteLit.FooteMaximalUnbalancedInput)
    (hHSF : HarrisSolomonFritzInput) (hCI : ClassicalInvolutionInput) (hHe : HeldFixedInput)
    (hL34 : L34FixedInput) (hA7 : A7FixedInput) (hL2 : L2FixedInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a₀ x₀ : X} {J₀ : Subgroup X}
    (hU₀ : GSUnbalancingTriple a₀ x₀ J₀) : GSRestrictedType J₀ := by
  obtain ⟨a, x, J, hmax, hR, hbound⟩ :=
    exists_maximal_unbalancing_triple_weakReach_of_simple hTB hSA hS hnonab hK hz hU hU₀
  have hJ : GSRestrictedType J := by
    rcases GSFM.he_or_l34_of_reach_bound_of_footeUnbalanced hTB hSA hB hH hFU hHSF hCI hnonab hK hz hU hmax
        hbound with
      hHe | ⟨h34, -⟩
    · obtain ⟨e⟩ := hHe
      exact Or.inl (nonempty_fusionZStar_equiv_held e)
    · exact Or.inr (Or.inl h34)
  exact gsRestrictedType_of_gsWeakReach hS hK
    (fun z hz' => GSLit.not_mem_center_of_orderOf_eq_two hnonab hz') hHe hL34 hA7 hL2 hR hJ

end CFSG.ComponentClassification.GrSLit
