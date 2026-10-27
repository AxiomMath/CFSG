module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisG2Sylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCenter
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.PartOne.OutStructure (Inn OutPNice)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)

theorem heisG2_model
    {X : Type} [Group X] (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hq : q.p = 2) (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    ChevalleyExceptionalModel X .G2 2 q.exponent := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq e
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have h : ChevalleyExceptionalModel X .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, by
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.PrimePower.card_def] using hrange⟩, hmodel⟩
  rwa [hq] at h

theorem heisG2_outPNice
    {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {f : ℕ}
    (h : ChevalleyExceptionalModel X .G2 2 f) : OutPNice p X := by
  obtain ⟨⟨-, hf1, -, h3⟩, hm⟩ := h
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f = 1 := by omega
    subst this
    norm_num at h3
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf2 K hK
  have hcard := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard.1]; omega)
  have := hcard.2
  exact CFSG.RankThree.PartOne.OutStructure.OutPNice.of_mulEquiv e
    (CFSG.RankThree.PartOne.OutStructure.outPNice_of_hom_cyclic hp Θ hker)

theorem heisG2_noHeisAut_of_model
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hrk : ∀ A : Subgroup X, IsMulCommutative A → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ 3)
    {f : ℕ} (hmodel : ChevalleyExceptionalModel X .G2 2 f) : NoHeisAut p X := by
  have hp2 : p ≠ 2 := by omega
  have hadm : StatedLieAdmissible .G2 0 2 f := hmodel.1
  have hf : 1 ≤ f := hadm.2.1
  have hCyc : OutPCyc p X := outPCyc_of_outPNice (heisG2_outPNice hp hmodel)
  obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  have hfield : (∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) → ∃ f₀ : ℕ, f = p * f₀ := by
    rintro ⟨α, hαin, hαp⟩
    have hlie : LieModel X .G2 0 2 f :=
      Or.inr (Or.inl ⟨rfl, by simp [chevalleyExceptionalTags], hmodel⟩)
    have hdiv : ¬ p ∣ lieOrderDivisor .G2 0 (2 ^ f) := by
      intro h
      have h1 : p ∣ 1 := by simpa [lieOrderDivisor] using h
      exact hp.ne_one (Nat.dvd_one.1 h1)
    rcases CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 X 0 2 f
        hadm hlie (by decide) p hp hp2 hdiv (fun h => absurd h.1 (by decide)) α hαp hαin with
      ⟨f₀, hf₀, -⟩ | ⟨h, -⟩
    · exact ⟨f₀, hf₀⟩
    · exact absurd h (by decide)
  exact noHeisAut_of_abelian_sylow hp hp5 hZ hCyc hrk (heisG2_sylow_data hp hp5 hK hf eK hfield)

theorem heisCoreOn_g2_of_oddCenterRest
    (hZ : OddCenterRest) : HeisCoreOn IdxG2 := by
  intro L _ _ hperf hodd hrk hsimple d hd e p hp hp5
  left
  haveI := hperf
  haveI := hsimple
  obtain ⟨d, hv⟩ := d
  cases d
  case G2 q =>
    have hq2 : q.p = 2 := hd
    have hZp : ¬ p ∣ Nat.card (Subgroup.center L) :=
      heis_not_dvd_center_rest hZ ⟨hperf.commutator_eq_top, hsimple⟩ hodd
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩)))) hp hp5
    exact heisG2_noHeisAut_of_model hp hp5 (heis_conj_injective L)
      (fun A hA hAp => heis_rank_quotient hrk hp (by omega) hZp A hA hAp)
      (heisG2_model q hv hq2 e)
  all_goals exact hd.elim

theorem heisCoreOn_g2
    (hGA : CFSG.Open.GriessAllModelsStatement) : HeisCoreOn IdxG2 :=
  heisCoreOn_g2_of_oddCenterRest (oddCenterRest_of_griess hGA)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
