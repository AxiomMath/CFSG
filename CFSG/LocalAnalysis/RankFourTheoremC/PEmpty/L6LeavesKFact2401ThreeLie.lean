module

public import CFSG.Assembly.InCatalogConverse
public import CFSG.LieType.SeitzGeneration.ConsumerEx
public import CFSG.LieType.SeitzGeneration.InnerExHolds
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.ExceptionalRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401

theorem exists_not_comm_of_two_le_pRank {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K)
    {r : ℕ} (hr : r.Prime) (h : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup K)) :
    ∃ a b : K, a * b ≠ b * a := by
  by_contra hcomm
  have hcomm' : ∀ a b : K, a * b = b * a := fun a b => by
    by_contra h
    exact hcomm ⟨a, b, h⟩
  letI : CommGroup K := { ‹Group K› with mul_comm := hcomm' }
  have hprime : (Nat.card K).Prime := CommGroup.is_simple_iff_prime_card.mp hK
  obtain ⟨E, -, -, hc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt (⊤ : Subgroup K)
  have h1 : r ^ 2 ∣ r ^ CFSG.Open.pRank r (⊤ : Subgroup K) := pow_dvd_pow r h
  rw [← hc] at h1
  have h2 : r ^ 2 ∣ Nat.card K := h1.trans (Subgroup.card_subgroup_dvd_card E)
  have h3 : r ∣ Nat.card K := (dvd_pow_self r two_ne_zero).trans h2
  have h4 : r = Nat.card K := (Nat.prime_dvd_prime_iff_eq hr hprime).mp h3
  rw [← h4] at h2
  have h5 : r ^ 2 ≤ r := Nat.le_of_dvd hr.pos h2
  nlinarith [hr.two_le]

theorem not_isRankOneLieIndex_of_rankTwoOdd {dd : TauCeti.LieTypeIndex}
    (hd : IsRankTwoOddIndex dd) : ¬ CFSG.AGLEmbedding.IsRankOneLieIndex dd := by
  rintro (⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨m, rfl⟩) <;> simp [IsRankTwoOddIndex] at hd

theorem not_isLinThreeFourIndex_of_rankTwoOdd {d : TauCeti.ValidLieTypeIndex}
    (hd : IsRankTwoOddIndex d.1) : ¬ CFSG.AGLEmbedding.IsLinThreeFourIndex d := by
  rintro ⟨q, -, -, h⟩
  rw [h] at hd
  simp [IsRankTwoOddIndex] at hd

theorem not_isCyclic_of_two_le_pRank {L : Type} [Group L] [Finite L]
    (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)) (T : Sylow 3 L) :
    ¬ IsCyclic (T : Subgroup L) := by
  intro hc
  have h1 := CFSG.AGLEmbedding.pRank_le_one_of_isCyclic_sylow Nat.prime_three T hc
  omega

theorem rankTwoOdd_cases (dd : TauCeti.LieTypeIndex) (hd : IsRankTwoOddIndex dd) :
    (∃ q : TauCeti.PrimePower, dd = .A 3 q ∧ q.p ≠ 2) ∨
      (∃ q : TauCeti.PrimePower, dd = .twistedA 3 q ∧ q.p ≠ 2) ∨
      (∃ q : TauCeti.PrimePower, dd = .B 2 q ∧ q.p ≠ 2) ∨
      (∃ q : TauCeti.PrimePower, dd = .G2 q ∧ q.p ≠ 2) := by
  rcases dd with ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | ⟨n, q⟩ | q | q | q |
    q | q | q | q | m | m | m | _
  · by_cases hn : n = 3
    · subst hn
      exact Or.inl ⟨q, rfl, hd⟩
    · exfalso
      simp [IsRankTwoOddIndex, hn] at hd
  · by_cases hn : n = 3
    · subst hn
      exact Or.inr (Or.inl ⟨q, rfl, hd⟩)
    · exfalso
      simp [IsRankTwoOddIndex, hn] at hd
  · by_cases hn : n = 2
    · subst hn
      exact Or.inr (Or.inr (Or.inl ⟨q, rfl, hd⟩))
    · exfalso
      simp [IsRankTwoOddIndex, hn] at hd
  all_goals first
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl, hd⟩))
    | (exfalso; simp [IsRankTwoOddIndex] at hd)

theorem two_le_pRank_three_of_A3 {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 3 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 3 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  rcases (CFSG.Models.lieModel_A 3 q hv e).2 with hC | ⟨h0, -⟩
  · obtain ⟨-, K, _, _, -, ⟨e'⟩⟩ := id hC
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
    exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psl (by norm_num)
  · omega

theorem two_le_pRank_three_of_B2 {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  rcases CFSG.Models.lieModel_B 2 q hv e with hL | hL
  · rcases hL.2 with hC | ⟨h0, -⟩
    · obtain ⟨-, K, _, _, -, ⟨e'⟩⟩ := id hC
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e']
      exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp (by norm_num)
    · omega
  · exact absurd hL.1.2.2.1 (by norm_num)

theorem two_le_pRank_three_of_twistedA3 {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩)
    (hq3 : q.p ≠ 3) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩
      = q.p := TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  rcases (CFSG.Models.lieModel_twistedA 3 q hv e).2 with hC | ⟨h0, -⟩
  · exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four (by norm_num)
      (by rw [hc]; exact hq3) hC
  · omega

theorem exists_prime_two_le_pRank_of_twistedA3 {G : Type} [Group G] [Finite G]
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid) (hq2 : q.p ≠ 2)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩) :
    ∃ r : ℕ, r.Prime ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩
      = q.p := TauCeti.LieTypeIndex.characteristic_twistedA 3 q
  rcases (CFSG.Models.lieModel_twistedA 3 q hv e).2 with hC | ⟨h0, -⟩
  · obtain ⟨hpr, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by rw [hc]; exact hq2) hC
    refine ⟨_, hpr, ?_⟩
    rcases hr with ⟨h1, -⟩ | ⟨-, ⟨hn3, -⟩ | h4⟩ | ⟨h1, -⟩ | h4 <;>
      first | omega | exact absurd h1 (by decide)
  · omega

theorem two_le_pRank_three_of_G2
    {G : Type} [Group G] [Finite G] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (e : G ≃* TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.G2 q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
  CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_of_untwistedBridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 (Or.inl rfl) e

theorem glbCore_three_eq_top_of_facts
    {L : Type} [Group L] [Finite L]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsRankTwoOddIndex d.1)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) (hs : IsSimpleGroup L)
    (hnab : ∃ a b : L, a * b ≠ b * a)
    (hcyc : 3 ≠ d.1.characteristic → ∀ T' : Sylow 3 L, ¬ IsCyclic (T' : Subgroup L))
    (T : Sylow 3 L) : CFSG.Open.GLBCore 3 1 (T : Subgroup L) = ⊤ := by
  by_cases h3c : 3 = d.1.characteristic
  · exact CFSG.AGLEmbedding.charPGen L hs hnab d ⟨e⟩ 3 Nat.prime_three (by norm_num) h3c
      (not_isRankOneLieIndex_of_rankTwoOdd hd) T
  · exact CFSG.LieType.SeitzGeneration.offCharGen_of_seitzEx
      CFSG.LieType.SeitzGeneration.kFactSeitzRankTwoInnerEx_holds L hs hnab d ⟨e⟩ 3
      Nat.prime_three (by norm_num) h3c T (hcyc h3c T)
      (fun h => not_isLinThreeFourIndex_of_rankTwoOdd hd h.2) (fun h => absurd h.1 (by norm_num))

theorem glbCore_three_eq_top_of_rankTwoOdd
    (L : Type) [Group L] [Finite L]
    (d : TauCeti.ValidLieTypeIndex) (hd : IsRankTwoOddIndex d.1)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) (T : Sylow 3 L) :
    CFSG.Open.GLBCore 3 1 (T : Subgroup L) = ⊤ := by
  obtain ⟨dd, hv⟩ := d
  have hs : IsSimpleGroup L :=
    e.isSimpleGroup_congr.mpr (CFSG.Assembly.lie_finite_simple ⟨dd, hv⟩).2
  rcases rankTwoOdd_cases dd hd with ⟨q, rfl, -⟩ | ⟨q, rfl, hq2⟩ | ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩
  · have h3 := two_le_pRank_three_of_A3 hv e
    exact glbCore_three_eq_top_of_facts ⟨_, hv⟩ hd e hs
      (exists_not_comm_of_two_le_pRank hs Nat.prime_three h3)
      (fun _ T' => not_isCyclic_of_two_le_pRank h3 T') T
  · obtain ⟨r, hr, h2⟩ := exists_prime_two_le_pRank_of_twistedA3 hv hq2 e
    refine glbCore_three_eq_top_of_facts ⟨_, hv⟩ hd e hs
      (exists_not_comm_of_two_le_pRank hs hr h2) ?_ T
    intro h3c T'
    have hq3 : q.p ≠ 3 := fun h => h3c (by simp [h, TauCeti.LieTypeIndex.characteristic_twistedA])
    exact not_isCyclic_of_two_le_pRank (two_le_pRank_three_of_twistedA3 hv e hq3) T'
  · have h3 := two_le_pRank_three_of_B2 hv e
    exact glbCore_three_eq_top_of_facts ⟨_, hv⟩ hd e hs
      (exists_not_comm_of_two_le_pRank hs Nat.prime_three h3)
      (fun _ T' => not_isCyclic_of_two_le_pRank h3 T') T
  · have h3 := two_le_pRank_three_of_G2 hv e
    exact glbCore_three_eq_top_of_facts ⟨_, hv⟩ hd e hs
      (exists_not_comm_of_two_le_pRank hs Nat.prime_three h3)
      (fun _ T' => not_isCyclic_of_two_le_pRank h3 T') T

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401

end
