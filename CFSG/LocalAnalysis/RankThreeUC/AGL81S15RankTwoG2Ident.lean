module

public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeGN

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.Explicit
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem exists_mulEquiv_cayleyGroup_of_component_G2
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (hodd : Odd (Nat.card (Subgroup.center L)))
    {f : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hQexp : Q.exponent = f)
    {hv : (TauCeti.LieTypeIndex.G2 Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.G2 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group) :
    2 ≤ f ∧ Nonempty (L ≃* ↥(cayleyGroup (GaloisField 2 f))) := by
  classical
  have hq3 : 3 ≤ Q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hQcard : Q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hQ, hQexp]
  have hf : 2 ≤ f := by
    by_contra hlt
    have hle : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 Q hv hQ (GaloisField 2 f)
    (hK.trans hQcard.symm)
  let e1 : L ⧸ Subgroup.center L ≃* AdjointQuotient .G2 (GaloisField 2 f) := e.trans b.symm
  have hZA : Subgroup.center ↥(adjointGroup .G2 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  let eC : AdjointQuotient .G2 (GaloisField 2 f) ≃* ↥(adjointGroup .G2 (GaloisField 2 f)) :=
    (QuotientGroup.quotientMulEquivOfEq hZA).trans QuotientGroup.quotientBot
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL.1
  let ψ : L →* ↥(adjointGroup .G2 (GaloisField 2 f)) :=
    (e1.trans eC).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψker : ψ.ker = Subgroup.center L :=
    (CFSG.SectionRank.ker_mulEquiv_comp _ _).trans (QuotientGroup.ker_mk' _)
  have hψ : Function.Surjective ψ :=
    (e1.trans eC).surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ, hσ, -, -⟩ := CFSG.SectionRank.g2_even_central_odd_extension_splitting hψ
    hψker.le (by rw [hψker]; exact hodd)
  have hZ : Subgroup.center L = ⊥ := by
    rw [← hψker]
    exact CFSG.SectionRank.ker_eq_bot_of_section_of_perfect ψ hψker.le σ hσ
  obtain ⟨c⟩ := CFSG.Quasithin.B42G2Id.nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hf
  exact ⟨hf, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
    (e1.trans c.symm)⟩⟩

theorem exists_mulEquiv_cayleyGroup_of_gn_component_G2
    {X : Type} [Group X] [Finite X] {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hL : CFSG.Open.IsComponentOf Ls ⊤)
    (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower) (hd : d.1 = .G2 Q) (hQ : Q.p = 2)
    (hLd : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    2 ≤ Q.exponent ∧ Nonempty (↥Ls ≃* ↥(cayleyGroup (GaloisField 2 Q.exponent))) := by
  obtain ⟨eL⟩ := hLd
  rcases d with ⟨d, hv⟩
  have hd' : d = TauCeti.LieTypeIndex.G2 Q := hd
  subst hd'
  have hodd : Odd (Nat.card (Subgroup.center ↥Ls)) :=
    Nat.not_even_iff_odd.mp fun h =>
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.not_two_dvd_card_center hX hL
        (even_iff_two_dvd.mp h)
  exact exists_mulEquiv_cayleyGroup_of_component_G2 hL.2.2 hodd hQ rfl eL

end CFSG.LocalAnalysis.RankThreeUC.S15

end
