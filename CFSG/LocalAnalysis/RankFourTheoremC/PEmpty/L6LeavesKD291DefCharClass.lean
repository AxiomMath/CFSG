module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharSL
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharSp
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open Subgroup CFSG.Open TauCeti CFSG.Assembly.LowTwoRank

@[expose] def InUni : Prop :=
  ∀ (p n f : ℕ), p.Prime → 5 ≤ p → 4 ≤ n → ∀ (G : Type) [Group G] [Finite G],
    StatedClassicalModel G .PSU n p f → RankThreeCent p G

@[expose] def InOmegaOdd : Prop :=
  ∀ (p n f : ℕ), p.Prime → 5 ≤ p → 3 ≤ n → ∀ (G : Type) [Group G] [Finite G],
    StatedClassicalModel G .POmegaOdd n p f → RankThreeCent p G

@[expose] def InOmegaPlus : Prop :=
  ∀ (p n f : ℕ), p.Prime → 5 ≤ p → 4 ≤ n → ∀ (G : Type) [Group G] [Finite G],
    StatedClassicalModel G .POmegaPlus n p f → RankThreeCent p G

@[expose] def InOmegaMinus : Prop :=
  ∀ (p n f : ℕ), p.Prime → 5 ≤ p → 4 ≤ n → ∀ (G : Type) [Group G] [Finite G],
    StatedClassicalModel G .POmegaMinus n p f → RankThreeCent p G

section Reduction

variable {p : ℕ} [hp : Fact p.Prime] {L : Type} [Group L] [Finite L]

theorem false_of_rankThreeCent (h : RankThreeCent p L) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) : False := by
  have := h y hyo
  omega

theorem kd291DC_A (hp5 : 5 ≤ p) (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (hqp : q.p = p) (e : L ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) : False := by
  have hxp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  subst hqp
  rcases (show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega) with rfl | rfl | hr3
  · obtain ⟨eP⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := q.p)
      (n := q.exponent) (d := ⟨.A 1 q, hv⟩) ⟨q, rfl, rfl, rfl⟩
    have e' : L ≃* CFSG.AGLEmbedding.PSL2GF q.p q.exponent := e.trans eP
    by_cases hn3 : 3 ≤ q.exponent
    · have := three_le_pRank_centralizer_of_psl2GF q.exponent_pos e' h3 hxp
      omega
    · have hle : CFSG.Open.pRank q.p (⊤ : Subgroup L) ≤ q.exponent := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt e']
        obtain ⟨T⟩ : Nonempty (Sylow q.p (CFSG.AGLEmbedding.PSL2GF q.p q.exponent)) :=
          inferInstance
        exact pRank_top_le_of_sylow_card T
          (CFSG.AGLEmbedding.psl2GF_sylow q.p q.exponent q.exponent_pos T).2
      omega
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨eK⟩⟩ := hm
    have := three_le_pRank_centralizer_of_statedSL_three_of_three_le q.exponent_pos hK eK h3 hxp
    omega
  · exact false_of_rankThreeCent (rankThreeCent_psl (n := r + 1) (by omega) hm) hyo hyc

theorem kd291DC_twistedA (hp5 : 5 ≤ p) (hUni : InUni) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hqp : q.p = p)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) : False := by
  have hxp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  subst hqp
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · obtain ⟨-, K, hKf, hKfin, hK, ⟨eK⟩⟩ := hm
    have hp2 : q.p ≠ 2 := by omega
    have := three_le_pRank_centralizer_of_statedSU_three_of_three_le hp2 q.exponent_pos
      (by rw [hK, ← pow_mul, mul_comm, pow_mul]) eK h3 hxp
    omega
  · exact false_of_rankThreeCent (hUni q.p (r + 1) q.exponent q.prime_p hp5 (by omega) L hm) hyo hyc

theorem statedClassicalModel_B2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) :
    StatedClassicalModel L .PSp 2 q.p q.exponent := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hq : q.card = q.p ^ q.exponent := PrimePower.card_def q
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) = q.p ^ q.exponent :=
    CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_B 2 q)
      (LieTypeIndex.fieldExponent_B 2 q)
  refine ⟨⟨q.prime_p, q.exponent_pos, le_rfl, ?_⟩, _, inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
    ⟨e.trans (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)⟩⟩
  intro h
  simp only [Prod.mk.injEq] at h
  exact hr.2 ⟨rfl, by omega⟩

theorem statedClassicalModel_Bodd (r : ℕ) (hr3 : 3 ≤ r) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hq2 : q.p ≠ 2)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    StatedClassicalModel L .POmegaOdd r q.p q.exponent := by
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) = q.p ^ q.exponent :=
    CFSG.Models.card_fixedField_of (LieTypeIndex.characteristic_B r q)
      (LieTypeIndex.fieldExponent_B r q)
  exact ⟨⟨q.prime_p, q.exponent_pos, hr3, hq2⟩, _, inferInstance,
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _, hK,
    ⟨e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv
      hq2 hr3)⟩⟩

theorem kd291DC_B (hp5 : 5 ≤ p) (hOdd : InOmegaOdd) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.B r q).Valid) (hqp : q.p = p)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup L) = 3 ∧
      (StatedClassicalModel L .PSp 2 p 1 ∨ CFSG.Blueprint.ChevalleyExceptionalModel L .G2 p 1) := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  subst hqp
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · have hm := statedClassicalModel_B2 q hv e
    by_cases hf : q.exponent = 1
    · rw [hf] at hm
      exact ⟨le_antisymm (pRank_le_three_psp_two_prime hm) (by omega), Or.inl hm⟩
    · exact (false_of_rankThreeCent (rankThreeCent_psp_two (f := q.exponent)
        (by have := q.exponent_pos; omega) hm h3) hyo hyc).elim
  · have hq2 : q.p ≠ 2 := by omega
    have hm := statedClassicalModel_Bodd r hr3 q hv hq2 e
    exact (false_of_rankThreeCent (hOdd q.p r q.exponent q.prime_p hp5 hr3 L hm) hyo hyc).elim

theorem kd291DC_C (hp5 : 5 ≤ p) (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid)
    (hqp : q.p = p) (e : L ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) : False := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm := CFSG.Models.LieModel.statedClassicalModel (CFSG.Models.lieModel_C r q hv e)
    (by simp [CFSG.Blueprint.classicalTags])
  subst hqp
  exact false_of_rankThreeCent (rankThreeCent_psp (by omega) hm) hyo hyc

theorem kd291DC_D (hp5 : 5 ≤ p) (hPlus : InOmegaPlus) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (hqp : q.p = p)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) : False := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm := CFSG.Models.LieModel.statedClassicalModel (CFSG.Models.lieModel_D r q hv e)
    (by simp [CFSG.Blueprint.classicalTags])
  subst hqp
  exact false_of_rankThreeCent (hPlus q.p r q.exponent q.prime_p hp5 hr L hm) hyo hyc

theorem kd291DC_twistedD (hp5 : 5 ≤ p) (hMinus : InOmegaMinus) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedD r q).Valid) (hqp : q.p = p)
    (e : L ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) {y : L} (hyo : orderOf y = p)
    (hyc : CFSG.Open.pRank p (centralizer ({y} : Set L)) ≤ 2) : False := by
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hm := CFSG.Models.LieModel.statedClassicalModel (CFSG.Models.lieModel_twistedD r q hv e)
    (by simp [CFSG.Blueprint.classicalTags])
  subst hqp
  exact false_of_rankThreeCent (hMinus q.p r q.exponent q.prime_p hp5 hr L hm) hyo hyc

end Reduction

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
