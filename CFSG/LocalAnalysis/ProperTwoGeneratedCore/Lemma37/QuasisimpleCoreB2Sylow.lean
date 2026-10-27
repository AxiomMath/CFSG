module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Covers
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneAlt
public import CFSG.Walter.Bender1970
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreSetting

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

theorem card_sylow_psl2Model_two (U : Sylow 2 (CFSG.Theory.Comparator.PSL2Model 2)) :
    Nat.card (U : Subgroup (CFSG.Theory.Comparator.PSL2Model 2)) = 4 := by
  have hU := ((bender_psl2_borel_full 2 le_rfl) U).2.2.2.2
  rw [hU]
  norm_num

theorem card_sylow_szModel_one {K : Type} [Group K] [Finite K]
    (e : K ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) (U : Sylow 2 K) : Nat.card (U : Subgroup K) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : CFSG.Theory.Comparator.SzModel 1 = Sz 1 := by
    simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, Sz, SzGenerators]
  let e' : K ≃* Sz 1 := e.trans (MulEquiv.subgroupCongr hmodel)
  have : Finite (Sz 1) := Finite.of_equiv _ e'.toEquiv
  obtain ⟨V⟩ : Nonempty (Sylow 2 (Sz 1)) := inferInstance
  have hV := ((bender_suzuki_borel_full 1 le_rfl) V).2.2.2.2
  rw [card_sylow_eq_of_mulEquiv e' U V, hV]
  norm_num

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

theorem Setting.exists_mul_ne_mul_centralQuotient (h : Setting J Q B) :
    ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
  have := h.simple
  by_contra hall
  push Not at hall
  have hZ : Subgroup.center J = ⊤ := by
    rw [eq_top_iff, ← h.perfect.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def, ← commute_mk_iff]
    exact hall _ _
  obtain ⟨g, hg⟩ := exists_ne (1 : J ⧸ Subgroup.center J)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  exact hg ((QuotientGroup.eq_one_iff x).mpr (hZ ▸ Subgroup.mem_top x))

theorem PartC.false_of_caseB2_of_sylow
    (h : Setting J Q B) {T R P : Subgroup J}
    (hc : PartC T R P (centralElt J) u) (hT : T ≤ R ⊔ P)
    (hφ : Nonempty (P ≃* QuaternionGroup 2)) (S : Sylow 2 J) (hS : (S : Subgroup J) = T) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨φ⟩ := hφ
  have hZ : ∀ x, x ∈ Subgroup.center J ↔ x = 1 ∨ x = centralElt J := fun _ => h.mem_center_iff
  set S' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hS' : (S' : Subgroup (J ⧸ Subgroup.center J)) =
      T.map (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [Sylow.coe_mapSurjective, hS]
  have hcard : Nat.card (S' : Subgroup (J ⧸ Subgroup.center J)) = 16 := by
    rw [hS']
    exact hc.card_map_of_caseB2 _ hT φ hZ
  have hcomm : ∀ a ∈ (S' : Subgroup (J ⧸ Subgroup.center J)),
      ∀ b ∈ (S' : Subgroup (J ⧸ Subgroup.center J)), a * b = b * a := by
    rw [hS']
    exact fun a ha b hb => hc.comm_map_of_caseB2 _ hT φ hZ ha hb
  have hsq : ∀ a ∈ (S' : Subgroup (J ⧸ Subgroup.center J)), a ^ 2 = 1 := by
    rw [hS']
    exact fun a ha => by rw [pow_two]; exact hc.mul_self_map_of_caseB2 _ hT φ hZ ha
  have hcommS : IsMulCommutative (S' : Subgroup (J ⧸ Subgroup.center J)) :=
    ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  have hab : CFSG.Walter.HasAbelianSylowTwo (J ⧸ Subgroup.center J) :=
    CFSG.Walter.hasAbelianSylowTwo_of_sylow S' hcommS
  have hnonab := h.exists_mul_ne_mul_centralQuotient
  have hrank : 3 ≤ CFSG.Open.twoRank (J ⧸ Subgroup.center J) := by
    have h4 : 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (J ⧸ Subgroup.center J)) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top ⟨hcommS, hsq⟩ (by rw [hcard]; norm_num)
    exact le_trans (by norm_num) h4
  have hSC := CFSG.Walter.simpleCaseHyp_of_benderHyp CFSG.Walter.benderHyp
  rcases CFSG.Walter.benderHyp _ h.simple hnonab hab hrank
      (fun K _ => CFSG.Walter.isAStar_of_hasAbelianSylowTwo hSC (hab.subgroup K)) with
    hJR | ⟨M, hM⟩
  · have h8 := (hJR.sylow_two_of_nonabelian hnonab S').2
    omega
  · have hB := CFSG.BenderSuzuki.bender_suzuki M hM
    rcases bender_cover_quotient h.perfect.commutator_eq_top h.center_card hB with he | he
    · obtain ⟨e⟩ := he
      have : Finite (CFSG.Theory.Comparator.PSL2Model 2) := Finite.of_equiv _ e.toEquiv
      obtain ⟨U⟩ : Nonempty (Sylow 2 (CFSG.Theory.Comparator.PSL2Model 2)) := inferInstance
      have h4 := card_sylow_eq_of_mulEquiv e S' U
      rw [card_sylow_psl2Model_two U, hcard] at h4
      omega
    · obtain ⟨e⟩ := he
      have h64 := card_sylow_szModel_one e S'
      omega

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
