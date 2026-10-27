module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LieType.Simplicity.Classical
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5AtlasProved
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.Adapters.StatedClassicalUnitaryOrders
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21a

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dSimpleProof

theorem exists_noncomm_of_four_dvd {S : Type} [Group S] [IsSimpleGroup S]
    (h4 : 4 ∣ Nat.card S) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  haveI : IsMulCommutative S := ⟨⟨h⟩⟩
  have hp : (Nat.card S).Prime := Group.is_simple_iff_prime_card.1 inferInstance
  rcases hp.eq_one_or_self_of_dvd 4 h4 with h1 | h1
  · omega
  · rw [← h1] at hp
    exact absurd hp (by norm_num)

theorem four_dvd_two_pow_pow {f k : ℕ} (hf : 1 ≤ f) (hk : 2 ≤ k) : 4 ∣ (2 ^ f) ^ k := by
  rw [← pow_mul]
  exact (pow_dvd_pow 2 (by nlinarith) : 2 ^ 2 ∣ 2 ^ (f * k))

open CFSG.Open CFSG.Timmesfeld.ClassicalOrders in
theorem four_dvd_ordA_three {f : ℕ} (hf : 1 ≤ f) : 4 ∣ ordA 3 (2 ^ f) := by
  unfold ordA
  have hg : Nat.gcd (3 + 1) (2 ^ f - 1) = 1 := by
    have := gcd_four_eq_one (odd_two_pow_pow_sub_one hf (n := 1) le_rfl)
    simpa using this
  rw [hg, Nat.div_one]
  exact Dvd.dvd.mul_right (four_dvd_two_pow_pow hf (by norm_num)) _

open CFSG.Open CFSG.Timmesfeld.ClassicalOrders in
theorem four_dvd_ordTwistedA_three {f : ℕ} (hf : 1 ≤ f) : 4 ∣ ordTwistedA 3 (2 ^ f) := by
  unfold ordTwistedA
  have hg : Nat.gcd (3 + 1) (2 ^ f + 1) = 1 := by
    have := gcd_four_eq_one (odd_two_pow_pow_add_one hf (n := 1) le_rfl)
    simpa using this
  rw [hg, Nat.div_one]
  exact Dvd.dvd.mul_right (four_dvd_two_pow_pow hf (by norm_num)) _

open CFSG.Open CFSG.Timmesfeld.ClassicalOrders in
theorem four_dvd_ordBC_two {f : ℕ} (hf : 1 ≤ f) : 4 ∣ ordBC 2 (2 ^ f) := by
  unfold ordBC
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have h2 : Nat.Coprime 2 (2 ^ f - 1) :=
      Nat.coprime_two_left.mpr (by simpa using odd_two_pow_pow_sub_one hf (n := 1) le_rfl)
    exact h2
  rw [hg, Nat.div_one]
  exact Dvd.dvd.mul_right (four_dvd_two_pow_pow hf (by norm_num)) _

open CFSG.Open in
theorem four_dvd_ordTwistedA_four_four : 4 ∣ ordTwistedA 4 4 := by
  unfold ordTwistedA
  decide

theorem four_dvd_card_alt {n : ℕ} (hn : n = 6 ∨ n = 8) :
    4 ∣ Nat.card (alternatingGroup (Fin n)) := by
  rcases hn with rfl | rfl
  · rw [K21aProof.card_alt6]; norm_num
  · rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]

end K21dSimpleProof

section G2


open CFSG.Open K21dSimpleProof in
theorem simple_G2 {S : Type} [Group S] [Finite S] {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.G2 Q).Valid) (hQ : Q.p = 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.G2 Q, hv⟩) :
    IsSimpleGroup S ∧ 4 ∣ Nat.card S := by
  have hq3 : 3 ≤ Q.card :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨p, f, hp, hf⟩ := Q
  dsimp only at hQ
  subst hQ
  haveI : Fact (Nat.Prime 2) := ⟨hp⟩
  let F := GaloisField 2 f
  have hF : Nat.card F = (⟨2, f, hp, hf⟩ : TauCeti.PrimePower).card := by
    rw [GaloisField.card _ _ hf.ne', TauCeti.PrimePower.card_def]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2
    (⟨2, f, hp, hf⟩ : TauCeti.PrimePower) hv rfl F hF
  have hmod : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 2 f :=
    ⟨⟨hp, hf, rfl, by simpa [TauCeti.PrimePower.card_def] using hq3⟩, F, inferInstance,
      inferInstance, by simpa [TauCeti.PrimePower.card_def] using hF, ⟨e.trans b.symm⟩⟩
  refine ⟨(CFSG.LieType.Simplicity.fam_g2_simplicity S 2 f hmod).2, ?_⟩
  have hc := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hmod
  simp only at hc
  rw [hc]
  unfold ordG2
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (four_dvd_two_pow_pow hf (by norm_num)) _) _

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.ClassicalOrders K21dSimpleProof in
theorem k21dSimple_holds : K21dSimple := by
  intro S _ _ hS
  have fin : 4 ∣ Nat.card S → IsSimpleGroup S → IsSimpleGroup S ∧ ∃ a b : S, a * b ≠ b * a :=
    fun h4 hs => ⟨hs, @exists_noncomm_of_four_dvd S _ hs h4⟩
  rcases hS with ⟨d, Q, hcase, ⟨e⟩⟩ | hL5 | hU3 | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨d1, hv⟩ := d
    simp only at hcase
    have hf : 1 ≤ Q.exponent := Q.exponent_pos
    rcases hcase with ⟨hQ, hd⟩ | ⟨hQ4, hd⟩
    · rcases hd with rfl | rfl | rfl | rfl
      ·
        obtain ⟨hs, h4⟩ := simple_G2 hv hQ e
        exact fin h4 hs
      ·
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 Q hv e
        rw [hQ] at hm
        have h4 : 4 ∣ Nat.card S := by
          rw [(card_statedClassicalModel_two hm).2.2.1 rfl]
          exact four_dvd_ordBC_two hf
        exact fin h4 (CFSG.LieType.Simplicity.fam_classical_converse S ⟨_, _, _, _, hm⟩).2.2
      ·
        have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        rw [hQ] at hm
        have h4 : 4 ∣ Nat.card S := by
          have hc := (card_statedClassicalModel_two hm).1 rfl
          simp only [Nat.add_sub_cancel] at hc
          rw [hc]
          exact four_dvd_ordA_three hf
        exact fin h4 (CFSG.LieType.Simplicity.fam_classical_converse S ⟨_, _, _, _, hm⟩).2.2
      ·
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e
        rw [hQ] at hm
        have h4 : 4 ∣ Nat.card S := by
          have hc := (card_statedClassicalModel_two hm).2.1 rfl
          simp only [Nat.add_sub_cancel] at hc
          rw [hc]
          exact four_dvd_ordTwistedA_three hf
        exact fin h4 (CFSG.LieType.Simplicity.fam_classical_converse S ⟨_, _, _, _, hm⟩).2.2
    ·
      subst hd
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 Q hv e
      have hpe : Q.p ^ Q.exponent = 4 := by rw [← TauCeti.PrimePower.card_def, hQ4]
      have hp2 : Q.p = 2 := by
        have hdvd : Q.p ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = Q.p ^ Q.exponent by rw [hpe]; norm_num]
          exact dvd_pow_self _ Q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq Q.prime_p Nat.prime_two).1
          (Q.prime_p.dvd_of_dvd_pow hdvd)
      have he2 : Q.exponent = 2 := by
        rw [hp2] at hpe
        exact Nat.pow_right_injective (le_refl 2) (by rw [hpe]; norm_num : 2 ^ Q.exponent = 2 ^ 2)
      rw [hp2, he2] at hm
      have h4 : 4 ∣ Nat.card S := by
        have hc := (card_statedClassicalModel_two hm).2.1 rfl
        simp only [Nat.add_sub_cancel] at hc
        rw [hc]
        exact four_dvd_ordTwistedA_four_four
      exact fin h4 (CFSG.LieType.Simplicity.fam_classical_converse S ⟨_, _, _, _, hm⟩).2.2
  ·
    obtain ⟨e⟩ := CFSG.AGLEmbeddingD2.McLaughlin.nonempty_equiv_G52_of_isL5Two hL5
    haveI : IsSimpleGroup (CFSG.GroupTheory.GL52.G52) := CFSG.GroupTheory.GL52.isSimpleGroup_G52
    have h4 : 4 ∣ Nat.card S := by
      rw [Nat.card_congr e.toEquiv, CFSG.GroupTheory.GL52.card_G52]
      norm_num
    exact fin h4 e.isSimpleGroup
  ·
    obtain ⟨⟨d1, hv⟩, ⟨q, hq3, hd⟩, ⟨e⟩⟩ := hU3
    simp only at hd
    subst hd
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).mp (ksm_card_eq hq3)
    rw [hp3, he1] at hm
    have h4 : 4 ∣ Nat.card S := by
      rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hm]
      norm_num
    exact fin h4 (CFSG.LieType.Simplicity.fam_classical_converse S ⟨_, _, _, _, hm⟩).2.2
  ·
    haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rcases hn with rfl | rfl <;> simp)
    have h4 : 4 ∣ Nat.card S := by
      rw [Nat.card_congr e.toEquiv]
      exact four_dvd_card_alt hn
    exact fin h4 e.isSimpleGroup

end G2

end CFSG.LocalAnalysis.RankThreeUC.S15
