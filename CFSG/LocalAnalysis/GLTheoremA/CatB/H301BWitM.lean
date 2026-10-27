module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi22
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.Sporadic.Schreier.Co1SplitLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.H1017 CFSG.Monster.Existence

private theorem attained_of_quot {G : Type} [Group G] [Finite G] {z : G} {X : Type} [Group X]
    (e : ↥(cent z) ⧸ CFSG.pCore 2 ↥(cent z) ≃* X)
    (hO : Nat.card (CFSG.pCore 2 ↥(cent z)) = 2 ^ 25) (hz : orderOf z = 2) {p r : ℕ}
    [Fact p.Prime] (hp : ¬ p ∣ 2 ^ 25)
    (hQ : ∃ Q : Subgroup X, IsElemAbelian p Q ∧ Nat.card Q = p ^ r) :
    ∃ E T : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨Q, hQe, hQc⟩ := hQ
  let f : X →* ↥(cent z) ⧸ CFSG.pCore 2 ↥(cent z) := e.symm.toMonoidHom
  obtain ⟨S, hS, -, hSc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift
    (CFSG.pCore 2 (cent z)) (by rw [hO]; exact hp) (CFSG.SectionRank.isElemAbelian_map hQe f)
  refine ⟨S.map (cent z).subtype, Subgroup.zpowers z, isElemAbelian_map_subtype hS, ?_,
    Subgroup.zpowers_ne_bot.2 fun h1 => by simp [h1] at hz,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one]), ?_⟩
  · rw [Subgroup.card_map_of_injective (cent z).subtype_injective, hSc,
      Subgroup.card_map_of_injective (f := f) e.symm.injective, hQc]
  · rintro _ ⟨g, -, rfl⟩
    have hg : Commute z (g : G) := (Subgroup.mem_centralizer_singleton_iff.1 g.2).symm
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hg.zpow_left n).eq

open CFSG.Sporadic.Co1Schreier in
private theorem exists_three_six_Co1 :
    ∃ Q : Subgroup CFSG.Blueprint.NativeSporadic.Co1, IsElemAbelian 3 Q ∧ Nat.card Q = 3 ^ 6 := by
  have hle : ElemThree.E ≤ GA := E_le_A.trans A_le_GA
  have hE : IsElemAbelian 3 (ElemThree.E.subgroupOf GA) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact (E_comm _ (Subgroup.mem_subgroupOf.1 x.2) _ (Subgroup.mem_subgroupOf.1 y.2)).eq
    · exact E_pow_three _ (Subgroup.mem_subgroupOf.1 hx)
  have e : ↥GA ≃* CFSG.Blueprint.NativeSporadic.Co1 := CFSG.Sporadic.Co1Block.co1MatEquiv.symm
  refine ⟨(ElemThree.E.subgroupOf GA).map (e : ↥GA →* CFSG.Blueprint.NativeSporadic.Co1),
    CFSG.SectionRank.isElemAbelian_map hE _, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_E]

private theorem exists_five_three_Co1
    [Finite CFSG.Blueprint.NativeSporadic.Co1] :
    ∃ Q : Subgroup CFSG.Blueprint.NativeSporadic.Co1, IsElemAbelian 5 Q ∧ Nat.card Q = 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1) :=
    ‹Finite CFSG.Blueprint.NativeSporadic.Co1›
  have h3 := CFSG.AGLEmbeddingD2.three_le_pRank_Co1_five
  obtain ⟨E₀, -, hE₀, hc₀⟩ := CFSG.SectionRank.exists_pRank (p := 5) (by norm_num)
    (⊤ : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Co1))
  obtain ⟨F, -, hF, hFc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hE₀
    (n := 3) (by rw [hc₀]; exact pow_dvd_pow 5 h3)
  exact ⟨F, hF, hFc⟩

section Monster


private theorem attained_M {p r : ℕ} [Fact p.Prime] (hp : ¬ p ∣ 2 ^ 25)
    (hQ : ∀ [Finite CFSG.Blueprint.NativeSporadic.Co1],
      ∃ Q : Subgroup CFSG.Blueprint.NativeSporadic.Co1, IsElemAbelian p Q ∧ Nat.card Q = p ^ r) :
    TwoRankAttained p .M r := by
  intro K _ _ hK
  obtain ⟨i, hi, ⟨e⟩⟩ := hK
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ : Nonempty (↥CFSG.Monster.Generated.Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  let φ : ↥CFSG.Monster.Generated.Gmat ≃* K := b.trans e.symm
  haveI : Finite ↥CFSG.Monster.Generated.Gmat := Finite.of_equiv K φ.symm.toEquiv
  have hZ := isTwoBCentralizer_Gmat xGmat (IsConj.refl _)
  obtain ⟨c⟩ := hZ.2.2.2.1
  haveI : Finite CFSG.Blueprint.NativeSporadic.Co1 :=
    Finite.of_surjective _ (c.surjective.comp (QuotientGroup.mk'_surjective _))
  exact attained_of_mulEquiv (by exact φ)
    (attained_of_quot (X := CFSG.Blueprint.NativeSporadic.Co1) (by exact c) hZ.2.1 orderOf_xGmat
      hp hQ)

theorem witM3_holds : TwoRankAttained 3 .M 6 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  attained_M (by norm_num) exists_three_six_Co1

section Five


theorem witM5_holds : TwoRankAttained 5 .M 3 :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  attained_M (by norm_num) exists_five_three_Co1

end Five

end Monster

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
