module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanJStarA9Inner
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanJStarA9Lie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanJStarA9Spor
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Target
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.ON

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint

theorem kFactJStarElimA3p_three (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    : KFactJStarElimA3p 3 (3 ^ 4) := by
  intro L _ _ ⟨eL⟩ L₀ _ _ hs hlist hdata
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hT, hTc, -⟩ := stmtA3pTarget_nine L ⟨eL⟩
  have : IsSimpleGroup L := hT.simple
  have hLcard : Nat.card L = 181440 :=
    (Nat.card_congr eL.toEquiv).trans nat_card_alternatingGroup_three_mul_three
  have hcat := isCatalogGroup_of_list (p := 3) (by norm_num) hlist
  obtain ⟨hdvd, hp⟩ := hdata.orderTest_of_schreier hT.nonabelian (fun hn => hSch L₀ hs hn hcat)
  rw [hLcard] at hdvd
  have h5 : ¬ 3 ^ 5 ∣ Nat.card L₀ := fun h5 => by
    have := Nat.le_of_dvd (by norm_num) (hp 5 h5)
    omega
  have h4 : 3 ^ 4 ∣ Nat.card L₀ := (by norm_num : 3 ^ 4 ∣ 181440).trans hdvd
  have hL₀nc : ∃ a b : L₀, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_two ((by norm_num : 2 ^ 2 ∣ 181440).trans hdvd)
  have hZ := center_bot_of_simple_nonab hL₀nc
  have hOut := hSch L₀ hs hL₀nc hcat
  rcases hlist with ⟨d, hd, he⟩ | he | ⟨s, hs', he⟩
  · obtain ⟨e'⟩ := he
    have hprof := lieListProfile hRee (by norm_num) hd e'
    rcases lie_nine_survivors hprof h5 hdvd with hN | ⟨-, hSp⟩
    · exact (not_jStarElimDataOf_of_card_eight_mul hN hLcard hT.toBase.isPerfect.commutator_eq_top
        hZ hOut hdata).elim
    · exact (not_jStarElimDataOf_spFourEight hSp e' hT hTc hZ h4 hdata).elim
  · obtain ⟨e'⟩ := he
    exact ⟨e'.trans eL.symm⟩
  · obtain ⟨e'⟩ := he
    obtain ⟨rfl, hN⟩ := three_spor_order_nine hbr hMcard hs' e' h5 hdvd
    obtain ⟨f⟩ := hbr .ONan
    exact (not_jStarElimDataOf_of_elemAbelian_sylow (f.trans e'.symm)
      CFSG.SectionRank.ON_elementary_three_rank_four (m := 5689080320) (by rw [hN]; norm_num)
      (by norm_num) eL hTc hZ hdata).elim

end CFSG.AGLEmbedding
