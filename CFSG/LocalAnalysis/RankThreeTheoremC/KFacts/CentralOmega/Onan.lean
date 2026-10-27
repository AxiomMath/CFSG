module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Onan
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaRowONan
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Bridge.ONSurj
public import CFSG.LocalAnalysis.GL83PartI.I_6_10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega

theorem not_forall_commute_onan
    {L : Type} [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hc : Nat.card (Subgroup.center L) = 3)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic .ONan).Group) (S : Sylow 3 L) :
    ¬ ∀ a ∈ (S : Subgroup L), ∀ b ∈ (S : Subgroup L), a ^ 3 = 1 → b ^ 3 = 1 →
      a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : Subgroup.center L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hc
    exact absurd hc (by norm_num)
  have hZp : IsPGroup 3 (Subgroup.center L) := IsPGroup.of_card (n := 1) (by rw [hc, pow_one])
  have hZc : IsCyclic (Subgroup.center L) := isCyclic_of_prime_card hc
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have e' : L ⧸ Subgroup.center L ≃* Blueprint.NativeSporadic.ON := e.trans b.symm
  have h1 := pow_three_eq_one_of_abelianSylowDatum (X := Blueprint.NativeSporadic.ON) hq hne hZp
    hZc e'
  have hexp : ∀ t ∈ (S : Subgroup L), t ^ 3 = 1 := h1 CFSG.AGLEmbedding.abelianSylowDatum_ON_three S
  intro hall
  exact GL83.not_isMulCommutative_sylow_of_perfect hq.1 (by rw [hc]) S
    ⟨⟨fun x y => Subtype.ext (hall x x.2 y y.2 (hexp x x.2) (hexp y y.2))⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.CentralOmega
