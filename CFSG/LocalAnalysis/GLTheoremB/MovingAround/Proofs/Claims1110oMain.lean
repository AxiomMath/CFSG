module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110o
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110oIdx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110oInner
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110oKac
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped MatrixGroups

section TwistedE6Card


theorem card_lieModel_twistedE6_ne_d4n {G : Type} [Group G] {p f : ℕ}
    (h : LieModel G .twistedE6 0 p f) : Nat.card G ≠ 174182400 := by
  have hadm := LieModel.admissible h
  have hp : p.Prime := hadm.1
  have hf : 0 < f := hadm.2.1
  rcases h with ⟨ht, -⟩ | ⟨-, -, hmod⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · simp [classicalTags] at ht
  · obtain ⟨-, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hmod
    let q : TauCeti.PrimePower := ⟨p, f, hp, hf⟩
    have hv := TauCeti.LieTypeIndex.valid_twistedE6 q
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv K
      (by rw [hK, TauCeti.PrimePower.card_def]) σ
      (fun x => by rw [hσ, TauCeti.PrimePower.card_def])
    exact card_ne_of_mulEquiv_lie ⟨.twistedE6 q, hv⟩ (e.trans b) (fun q' hq' => by cases hq')
  · simp [reeTitsTags] at ht
  · exact absurd ht (by decide)

end TwistedE6Card

section TypeA


theorem e8TwoFive_typeA_card_ne {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hap : ∀ j, a j ^ 5 = 1)
    (h1 : rootDiagUnit Tag.E8 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400 := by
  obtain ⟨ν, f, hν, -, -, hmodel | hmodel⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.RationalModel.rationalComponent_typeA_model
      (τ := Tag.E8) (S := S) (p := 5) Nat.prime_five hT hap h1 i hA hqs
  · exact card_statedClassicalModel_PSL_ne_d4n hmodel
  · rw [show ν = (ν - 1) + 1 by omega] at hmodel
    exact card_statedClassicalModel_PSU_ne_d4n hmodel

end TypeA

section Inner


theorem e8TwoFive_inner_card_ne {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
    (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hbig : 26 ≤ (componentRoots (rootCharHom a) i).ncard) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400 := by
  have hk : twistKind S.ρ (rootCharHom a) i = .inner := by
    unfold twistKind
    rw [if_pos hinner]
  exact inner_big_card_ne_of_kind S hT i hk (Or.inr (Or.inr (Or.inr rfl))) hbig

end Inner

section OuterD


theorem e8TwoFive_outerD_card_ne {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hap : ∀ j, a j ^ 5 = 1)
    (h1 : rootDiagUnit Tag.E8 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400 := by
  obtain ⟨m, e, -, hlie⟩ :=
    lieModel_rationalComponent_of_twoD_highG Nat.prime_five S hT hap h1 i h5 hn hout
      (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega))
      trivial
  exact card_lieModel_POmegaMinus_ne_d4n hlie

end OuterD

section OuterE


theorem e8TwoFive_outerE_card_ne {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.E8 L p₀) {a : Fin Tag.E8.rank → Lˣ}
    (hT : rootDiagUnit Tag.E8 a ∈ S.D.torus) (hap : ∀ j, a j ^ 5 = 1)
    (h1 : rootDiagUnit Tag.E8 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 174182400 := by
  have h5L : ((5 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_five
      (ringChar_ne_of_pow_eq_one Nat.prime_five hap h1)
  have hTp : rootDiagUnit Tag.E8 a ^ 5 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨f, hf, -, hlie⟩ :=
    lieModel_rationalComponent_of_outer_E8 S Nat.prime_five h5L hT hTp i h6 hn hout
  exact card_lieModel_twistedE6_ne_d4n hlie

end OuterE

section Main


theorem e8TwoFiveRatNotD4_holds : E8TwoFiveRatNotD4 := by
  intro L hL hLac p₀ S hFr hq2 a hT hap h1 i hqs
  classical
  obtain ⟨r, e, hr, hchar, he, hqre⟩ := S.exists_char_pow
  have hr2 : r = 2 := by
    have hpow : r ^ e = 2 := by rw [← hqre, hq2]
    have hdvd : r ∣ 2 := hpow ▸ dvd_pow_self r (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 hdvd
  haveI : CharP L 2 := hr2 ▸ hchar
  have h5L : ((5 : ℕ) : L) ≠ 0 :=
    natCast_ne_zero_of_ringChar_ne Nat.prime_five
      (ringChar_ne_of_pow_eq_one Nat.prime_five hap h1)
  have hTp : rootDiagUnit Tag.E8 a ^ 5 = 1 := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact e8TwoFive_typeA_card_ne S hT hap h1 i hA hqs
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S
        Nat.prime_five h5L hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD | hE
    · exact (hA hA').elim
    ·
      have hr5 : 5 ≤ compRank (componentRoots (rootCharHom a) i) := by
        rcases Nat.lt_or_ge (compRank (componentRoots (rootCharHom a) i)) 5 with hlt | hge
        · exfalso
          have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
          exact not_d4Shape_of_five S h5L hTp i
            ⟨hr4, by rw [hD.2, hr4]⟩
        · exact hge
      have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hD.2, Nat.mul_assoc]
        have h4 : 4 ≤ compRank (componentRoots (rootCharHom a) i) - 1 := by omega
        have h20 : 20 ≤ compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) - 1) :=
          le_trans (by norm_num : 20 ≤ 5 * 4) (Nat.mul_le_mul hr5 h4)
        omega
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact e8TwoFive_inner_card_ne S hT i hinner h26
      · exact e8TwoFive_outerD_card_ne S hT hap h1 i hr5 hD.2 hinner
    ·
      have hr8 : compRank (componentRoots (rootCharHom a) i) ≤ 8 := by
        have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
        rwa [show Tag.E8.rank = 8 from rfl] at hle
      have h26 : 26 ≤ (componentRoots (rootCharHom a) i).ncard := by
        rw [hE.2]
        have hc : compRank (componentRoots (rootCharHom a) i) = 6 ∨
            compRank (componentRoots (rootCharHom a) i) = 7 ∨
            compRank (componentRoots (rootCharHom a) i) = 8 := by omega
        rcases hc with h6 | h7 | h8
        · rw [h6]
          norm_num [eRootCount]
        · rw [h7]
          norm_num [eRootCount]
        · rw [h8]
          norm_num [eRootCount]
      by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · exact e8TwoFive_inner_card_ne S hT i hinner h26
      · exact e8TwoFive_outerE_card_ne S hT hap h1 i hE.1 hE.2 hinner

theorem e8TwoNoD4Comp_holds : Claims1110n.E8TwoNoD4Comp :=
  e8TwoNoD4Comp_of_rat e8TwoFiveRatNotD4_holds

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110o
