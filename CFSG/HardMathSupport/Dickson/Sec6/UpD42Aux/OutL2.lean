module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.OutLinear

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.RankTwoClassical (statedProjEquiv)

theorem upD42Chev2Out_l2_holds : UpD42Chev2Out
    (fun d => match d with | .A r _ => r = 1 | _ => False) := by
  intro S _ _ _ _ ⟨d, hv⟩ hF hc ⟨e⟩ α _ h
  cases d with
  | A r q =>
    obtain rfl : r = 1 := hF
    have hp2 : q.p = 2 := hc
    exfalso
    have hm := CFSG.Models.lieModel_A 1 q hv e
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ :=
      hm.2.resolve_right (fun h => absurd h.1 (by norm_num))
    haveI : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv S eK.toEquiv
    have hP := h.congr eK
    obtain ⟨hβ3, hβ1, I, hI, hID⟩ := id hP
    let β := MulAut.congr eK α
    rcases l2Aut3Classification_holds K β hβ3 with h1 | hsol | ⟨σ, φ, γ, hφ, hβ⟩
    · exact hβ1 h1
    · exact hP.not_solvable_fixed hsol
    · obtain ⟨F₀, _, _, hcard, ⟨ψ0⟩⟩ :=
        l2FieldFixed_holds K β hβ3 hβ1 σ φ γ hφ hβ
      by_cases h4 : 4 ≤ Nat.card F₀
      · obtain ⟨hQ₀, hZ₀⟩ := l2fld_isQuasisimple_psl2 h4
        have hCq : CFSG.Open.IsQuasisimple ↥(fixSub β) :=
          isQuasisimple_open_of_mulEquiv ψ0 hQ₀
        have hI' : GLAPComponent 3 (fixSub β) I := hI
        have hIC : I = fixSub β := eq_of_isSubnormal_of_quasisimple hCq hI'.2.1
          (glaPComponent_perfect hI') (Lemma510Ns.glaPComponent_ne_bot hI')
        subst hIC
        have hZC : Subgroup.center ↥(fixSub β) = ⊥ :=
          CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns.center_eq_bot_of_mulEquiv'
            ψ0 hZ₀
        have hOC : GLAPPrimeCore 3 ↥(fixSub β) = ⊥ :=
          glaPPrimeCore_eq_bot_of_quasisimple hCq
            (fun z hz => by rw [hZC, Subgroup.mem_bot] at hz; rw [hz, one_pow])
            (by rw [Nat.card_congr ψ0.toEquiv]; exact l2fld_three_dvd_card_psl2)
        have hD : IsCatalogLieIso (StatedProj (StatedSL 2 F₀)) IsD42Index :=
          IsCatalogLieIso.of_mulEquiv (((barEquivOfCore hOC).symm).trans ψ0) hID
        have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, hp2]
        obtain ⟨g, hg⟩ : ∃ g : ℕ, Nat.card F₀ = 2 ^ g := by
          have hdvd : Nat.card F₀ ∣ 2 ^ q.exponent := by
            rw [← hK2, hcard]
            exact dvd_pow_self _ (by norm_num)
          obtain ⟨g, -, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
          exact ⟨g, hg⟩
        have hg1 : 1 ≤ g := by
          rcases Nat.eq_zero_or_pos g with h0 | h0
          · rw [h0] at hg
            omega
          · exact h0
        exact not_isD42Type_projectiveSL le_rfl hg1 hg (fun _ => h4)
          (IsCatalogLieIso.of_mulEquiv (statedProjEquiv 2 F₀) hD)
      · haveI : Group.IsSolvable (StatedProj (StatedSL 2 F₀)) :=
          l2fld_isSolvable_psl2_of_card_le_three (F := F₀) (by omega)
        exact hP.not_solvable_fixed
          (Group.isSolvable_of_isSolvable_injective (f := ψ0.toMonoidHom) ψ0.injective)
  | _ => exact hF.elim

theorem upD42Chev2Out_linear_holds : UpD42Chev2Out
    (fun d => match d with | .A _ _ => True | _ => False) := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc he α hout h
  cases d with
  | A r q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    by_cases h1 : r = 1
    · exact upD42Chev2Out_l2_holds S hs hnab ⟨.A r q, hv⟩ h1 hc he α hout h
    · exact upD42Chev2Out_linear_rank_ge_two_holds S hs hnab ⟨.A r q, hv⟩
        (by omega) hc he α hout h
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
