module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimSporOrders
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeReeF4

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.Sporadic

theorem five_lie_order {d : TauCeti.ValidLieTypeIndex} (hd : P1ThreeLieList 5 d)
    {L₀ : Type} [Group L₀] [Finite L₀] (e : L₀ ≃* CatGroup d) (h6 : ¬ 5 ^ 6 ∣ Nat.card L₀) :
    IsReeFFourFiveIndex d ∨ ¬ 331 ∣ Nat.card L₀ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_congr e.toEquiv] at h6 ⊢
  rcases hd with ⟨n, hn⟩ | hU | hR | hS | hC
  ·
    have hn0 : n ≠ 0 := by obtain ⟨q, -, -, hqn⟩ := hn; exact hqn ▸ q.exponent_pos.ne'
    have hN := card_catGroup_linTwo (p := 5) (by norm_num) hn0 hn
    rw [hN] at h6 ⊢
    have hn6 : n < 6 := by
      by_contra hn6
      exact h6 ((pow_dvd_pow 5 (by omega)).trans (Dvd.intro _ rfl))
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    refine Or.inr ?_
    interval_cases n <;> decide
  ·
    have h3 := pow_dvd_card_catGroup_unitary hU
    obtain ⟨q, hqp, hq⟩ := hU
    have hfe : d.1.fieldExponent = q.exponent := by rw [hq]; simp
    have hN := card_catGroup_twistedA hq
    rw [hfe] at h3
    have ha : q.exponent < 2 := by
      by_contra ha
      exact h6 ((pow_dvd_pow 5 (by omega)).trans h3)
    have ha1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [hN, hqp, ha1]
    exact Or.inr (by decide)
  · exact absurd hR.1 (by norm_num)
  ·
    obtain ⟨q, ⟨hqp, hqe, h⟩ | ⟨hp, -⟩⟩ := hS
    · rw [card_catGroup_B2 h, hqp, hqe]
      exact Or.inr (by decide)
    · omega
  · rcases hC with ⟨hp, -⟩ | ⟨hp, -⟩ | ⟨-, h⟩
    · omega
    · omega
    · exact Or.inl h

theorem eq_of_isReeFFourFiveIndex {d d' : TauCeti.ValidLieTypeIndex} (h : IsReeFFourFiveIndex d)
    (h' : IsReeFFourFiveIndex d') : d = d' :=
  Subtype.ext (h.trans h'.symm)

theorem kFactJStarElimReeF4_of (hSch : KFactCatalogSchreier)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    : KFactJStarElimReeF4 := by
  rintro d hd L _ _ ⟨eL⟩ L₀ _ _ hs hlist hdata
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hLcard : Nat.card L = ordTwistedF4 (2 ^ (2 * 2 + 1)) := by
    rw [Nat.card_congr eL.toEquiv]
    exact card_catGroup_reeF4 hd
  have : IsSimpleGroup (CatGroup d) := isSimpleGroup_of_catGroup_reeF4 hd
  have : IsSimpleGroup L := eL.isSimpleGroup
  have h331 : 331 ∣ Nat.card L := by
    rw [hLcard]
    decide
  have hLnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_two (by rw [hLcard]; decide)
  have hcat := isCatalogGroup_of_list (p := 5) (by norm_num) hlist
  obtain ⟨hdvd, hp⟩ := hdata.orderTest_of_schreier hLnc (fun hn => hSch L₀ hs hn hcat)
  have h331' : 331 ∣ Nat.card L₀ := h331.trans hdvd
  have h6 : ¬ 5 ^ 6 ∣ Nat.card L₀ := fun h => by
    have := Nat.le_of_dvd (by positivity) (hp 6 h)
    omega
  rcases hlist with ⟨d', hd', he'⟩ | he' | ⟨s, hs', he'⟩
  · obtain ⟨e'⟩ := he'
    rcases five_lie_order hd' e' h6 with hsp | h2
    · have hdd : d' = d := eq_of_isReeFFourFiveIndex hsp hd
      subst hdd
      exact ⟨e'.trans eL.symm⟩
    · exact absurd h331' h2
  · obtain ⟨e'⟩ := he'
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup_three_mul_five] at h331'
    exact absurd h331' (by decide)
  · obtain ⟨e'⟩ := he'
    exact absurd h331' (five_spor_order hbr hMcard hs' e')

end CFSG.AGLEmbedding
