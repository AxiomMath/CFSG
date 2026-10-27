module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62AltRank
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem nonempty_sl2_equiv_psl {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) : Nonempty (SL(2, F) ≃* PSL(2, GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hc := CFSG.CGT.PushingUpLit.CGT6.sl2_center_eq_bot F
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 n hn hF) (Fin 2))⟩

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem pRank_top_le (c : Ctx M B H S K z) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (Kbar K)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  rw [CFSG.SectionRank.pRank_quotient_eq _ hN]
  have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) K.subtype K.subtype_injective
    (⊤ : Subgroup ↥K)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2.trans c.comp.rank_one.le

theorem card_le_three (c : Ctx M B H S K z) {X : Type*} [Group X] [Finite X] (e : Kbar K ≃* X)
    (E : Subgroup X) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  have h2 := c.pRank_top_le
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hE)
  have hk1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 3 := by norm_num

theorem false_of_alt (c : Ctx M B H S K z) {n : ℕ} (hn : 6 ≤ n)
    (e : Kbar K ≃* alternatingGroup (Fin n)) : False := by
  have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.l62_two_le_pRank_alternating n hn
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  have := c.pRank_top_le
  omega

theorem false_of_card_lt (c : Ctx M B H S K z) {X : Type*} [Group X] [Finite X] (e : Kbar K ≃* X)
    (h : Nat.card X < 60) : False := by
  have hX : Group.IsSolvable X := CFSG.GroupTheory.groups_order_below_sixty_solvable h
  have hK : Group.IsSolvable (Kbar K) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have := c.isSimpleGroup
  obtain ⟨a, b, hab⟩ := c.exists_ne_comm
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hK a b)

theorem isChevTwo (c : Ctx M B H S K z) : IsChevTwo (Kbar K) := by
  rcases c.chevAlt with h | ⟨n, ⟨e⟩⟩
  · exact h
  · rcases Nat.lt_or_ge n 5 with hn | hn
    · exfalso
      refine c.false_of_card_lt e ?_
      calc Nat.card (alternatingGroup (Fin n)) ≤ Nat.card (Equiv.Perm (Fin n)) :=
            Subgroup.card_le_card_group _
        _ = n.factorial := by rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
        _ ≤ (4).factorial := Nat.factorial_le (by omega)
        _ < 60 := by decide
    · rcases Nat.eq_or_lt_of_le hn with h5 | h6
      · subst h5
        exact Or.inr (Or.inl ⟨5, Or.inl rfl, ⟨e⟩⟩)
      · exact (c.false_of_alt h6 e).elim

theorem bender_of_sl2 (c : Ctx M B H S K z) {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (e : Kbar K ≃* SL(2, F)) : fusionIsBenderGroup (Kbar K) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · exfalso
    refine c.false_of_card_lt e ?_
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
    interval_cases n <;> norm_num
  · obtain ⟨e'⟩ := nonempty_sl2_equiv_psl (by omega) hF
    exact Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩

theorem bender_of_alt5 (c : Ctx M B H S K z) (e : Kbar K ≃* alternatingGroup (Fin 5)) :
    fusionIsBenderGroup (Kbar K) := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcard : Nat.card SL(2, GaloisField 2 2) = 60 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  obtain ⟨e5⟩ := CFSG.Quasithin.A5Model.sl2_four_equiv_alt5 (GaloisField 2 2) hK hcard
  exact c.bender_of_sl2 (F := GaloisField 2 2) (n := 2) (by rw [hK]; norm_num) (e.trans e5.symm)

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
