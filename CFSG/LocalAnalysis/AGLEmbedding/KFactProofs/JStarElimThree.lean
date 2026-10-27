module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimSporOrders
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
public import CFSG.LocalAnalysis.AGLEmbedding.J3Facts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.Sporadic.J3

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.Sporadic

theorem three_lie_order (hRee : KFactReeOrder)
    {d : TauCeti.ValidLieTypeIndex} (hd : P1ThreeLieList 3 d)
    {L₀ : Type} [Group L₀] [Finite L₀] (e : L₀ ≃* CatGroup d) (h6 : ¬ 3 ^ 6 ∣ Nat.card L₀) :
    IsSpFourEightIndex d ∨ (¬ 50232960 ∣ Nat.card L₀ ∧ ¬ 1056706560 ∣ Nat.card L₀) := by
  have : Finite (CatGroup d) := Finite.of_equiv L₀ e.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_congr e.toEquiv] at h6 ⊢
  rcases hd with ⟨n, hn⟩ | hU | hR | hS | hC
  ·
    have hn0 : n ≠ 0 := by obtain ⟨q, -, -, hqn⟩ := hn; exact hqn ▸ q.exponent_pos.ne'
    have hN := card_catGroup_linTwo (p := 3) (by norm_num) hn0 hn
    rw [hN] at h6 ⊢
    have hn6 : n < 6 := by
      by_contra hn6
      exact h6 ((pow_dvd_pow 3 (by omega)).trans (Dvd.intro _ rfl))
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
      exact h6 ((pow_dvd_pow 3 (by omega)).trans h3)
    have ha1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [hN, hqp, ha1] at h6 ⊢
    exact Or.inr ((by decide : 3 ^ 6 ∣ ordTwistedA 2 (3 ^ 1) ∨ _).resolve_left h6)
  ·
    exfalso
    have hn3 := hR.three_le_fieldExponent
    have hN := hRee (CatGroup d) d hR ⟨MulEquiv.refl _⟩
    refine h6 ?_
    rw [hN]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)
  ·
    obtain ⟨q, ⟨hqp, hqe, h⟩ | ⟨-, hqp, hqe, h⟩⟩ := hS
    · have hN := card_catGroup_B2 h
      rw [hN, hqp, hqe] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordBC 2 (3 ^ 1) ∨ _).resolve_left h6)
    · have hN := card_catGroup_twistedA h
      rw [hN, hqp, hqe] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordTwistedA 3 (2 ^ 1) ∨ _).resolve_left h6)
  ·
    rcases hC with ⟨-, q, hq, hq1, h | h | h | h | h | h | h | h⟩ |
        ⟨-, q, hq, hq3, h | h | h | h⟩ | ⟨hp, -⟩
    · have hN := card_catGroup_B_even (by norm_num) hq h
      rw [hN, hq1] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordBC 3 (2 ^ 1) ∨ _).resolve_left h6)
    · have hN := card_catGroup_B_even (by norm_num) hq h
      rw [hN, hq1] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordBC 4 (2 ^ 1) ∨ _).resolve_left h6)
    · have hN := card_catGroup_twistedA h
      rw [hN, hq, hq1] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordTwistedA 4 (2 ^ 1) ∨ _).resolve_left h6)
    · have hN := card_catGroup_twistedA h
      rw [hN, hq, hq1] at h6
      exact absurd (by decide) h6
    · have hN := card_catGroup_D_even hq h
      rw [hN, hq1] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordD 4 (2 ^ 1) ∨ _).resolve_left h6)
    · have hN := card_catGroup_F4_even hq h
      rw [hN, hq1] at h6
      exact absurd (by decide) h6
    · have hN := card_catGroup_E6_even hq h
      rw [hN, hq1] at h6
      exact absurd (by decide) h6
    · have hN := card_catGroup_trialityD4_even hq h
      rw [hN, hq1] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordTrialityD4 (2 ^ 1) ∨ _).resolve_left h6)
    · exact Or.inl ⟨q, hq, hq3, h⟩
    · have hN := card_catGroup_G2_even hq h
      rw [hN, hq3] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordG2 (2 ^ 3) ∨ _).resolve_left h6)
    · have hN := card_catGroup_trialityD4_even hq h
      rw [hN, hq3] at h6
      exact absurd (by decide) h6
    · have hN := card_catGroup_twistedA h
      rw [hN, hq, hq3] at h6 ⊢
      exact Or.inr ((by decide : 3 ^ 6 ∣ ordTwistedA 2 (2 ^ 3) ∨ _).resolve_left h6)
    · omega

theorem eq_of_isSpFourEightIndex {d d' : TauCeti.ValidLieTypeIndex} (h : IsSpFourEightIndex d)
    (h' : IsSpFourEightIndex d') : d = d' := by
  obtain ⟨q, hq, hqe, hd⟩ := h
  obtain ⟨q', hq', hqe', hd'⟩ := h'
  have hqq : q = q' := by
    obtain ⟨p1, e1, h1, h2⟩ := q
    obtain ⟨p2, e2, h3, h4⟩ := q'
    simp only at hq hq' hqe hqe'
    subst hq hq' hqe hqe'
    rfl
  subst hqq
  exact Subtype.ext (hd.trans hd'.symm)

theorem isSimpleGroup_of_catGroup_B2 {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (h : d.1 = .B 2 q) {L : Type} [Group L] (e : L ≃* CatGroup d) : IsSimpleGroup L := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B 2 q := h
  exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 2 q.p
    q.exponent (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)

theorem not_three_pow_six_dvd {N : ℕ} (h : ∀ k : ℕ, 3 ^ k ∣ N → 3 ^ k ∣ 3 ^ 5) :
    ¬ 3 ^ 6 ∣ N := fun h6 => by
  have := Nat.le_of_dvd (by positivity) (h 6 h6)
  omega

theorem kFactJStarElimSp48_of (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    : KFactJStarElimSp48 := by
  rintro d hd L _ _ ⟨eL⟩ L₀ _ _ hs hlist hdata
  obtain ⟨q, hq, hq3, hdq⟩ := hd
  have hLcard : Nat.card L = 1056706560 := by
    rw [Nat.card_congr eL.toEquiv, card_catGroup_B2 hdq, hq, hq3]
    decide
  have : IsSimpleGroup L := isSimpleGroup_of_catGroup_B2 hdq eL
  have hLnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_two (by rw [hLcard]; decide)
  have hcat := isCatalogGroup_of_list (p := 3) (by norm_num) hlist
  obtain ⟨hdvd, hp⟩ := hdata.orderTest_of_schreier hLnc (fun hn => hSch L₀ hs hn hcat)
  rw [hLcard] at hdvd
  have h6 := not_three_pow_six_dvd hp
  rcases hlist with ⟨d', hd', he'⟩ | he' | ⟨s, hs', he'⟩
  · obtain ⟨e'⟩ := he'
    rcases three_lie_order hRee hd' e' h6 with hsp | ⟨-, h2⟩
    · have hdd : d' = d := eq_of_isSpFourEightIndex hsp ⟨q, hq, hq3, hdq⟩
      subst hdd
      exact ⟨e'.trans eL.symm⟩
    · exact absurd hdvd h2
  · obtain ⟨e'⟩ := he'
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup_three_mul_three] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e'⟩ := he'
    rcases three_spor_order hbr hMcard hs' e' with ⟨-, hN⟩ | h3 | ⟨-, h2⟩
    · rw [hN] at hdvd
      exact absurd hdvd (by decide)
    · exact absurd h3 h6
    · exact absurd hdvd h2

theorem kFactJStarElimJ3_of (hSch : KFactCatalogSchreier) (hRee : KFactReeOrder)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    : KFactJStarElimJ3 := by
  rintro L _ _ ⟨eL⟩ L₀ _ _ hs hlist hdata
  obtain ⟨fJ⟩ := hbr .J3
  have e3 : L ≃* NativeSporadic.Carrier .J3 := eL.trans fJ.symm
  have : IsSimpleGroup (NativeSporadic.Carrier .J3) := J3.isSimpleGroup_J3
  have : IsSimpleGroup L := e3.isSimpleGroup
  have hLcard : Nat.card L = 50232960 := (Nat.card_congr e3.toEquiv).trans J3.card_J3
  have hLnc : ∃ a b : L, a * b ≠ b * a :=
    nonabelian_of_simple_of_sq_dvd Nat.prime_two (by rw [hLcard]; decide)
  have hcat := isCatalogGroup_of_list (p := 3) (by norm_num) hlist
  obtain ⟨hdvd, hp⟩ := hdata.orderTest_of_schreier hLnc (fun hn => hSch L₀ hs hn hcat)
  rw [hLcard] at hdvd
  have h6 := not_three_pow_six_dvd hp
  rcases hlist with ⟨d', hd', he'⟩ | he' | ⟨s, hs', he'⟩
  · obtain ⟨e'⟩ := he'
    rcases three_lie_order hRee hd' e' h6 with hsp | ⟨h1, -⟩
    · obtain ⟨q, hq, hq3, hdq⟩ := hsp
      rw [Nat.card_congr e'.toEquiv, card_catGroup_B2 hdq, hq, hq3] at hdvd
      exact absurd hdvd (by decide)
    · exact absurd hdvd h1
  · obtain ⟨e'⟩ := he'
    rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup_three_mul_three] at hdvd
    exact absurd hdvd (by decide)
  · obtain ⟨e'⟩ := he'
    rcases three_spor_order hbr hMcard hs' e' with ⟨rfl, -⟩ | h3 | ⟨h1, -⟩
    · exact ⟨e'.trans eL.symm⟩
    · exact absurd h3 h6
    · exact absurd hdvd h1

end CFSG.AGLEmbedding
