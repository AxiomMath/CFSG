module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Small
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.FieldAutLTwo
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.FieldAutLThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.Quasithin.Background.A318PL3Inst
import CFSG.RankThree.PartTwo.Sec12.Hering129KYb

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.RankThreeTheoremC.L28

section Certified


theorem fixedData_of_catalog
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1) (α : MulAut S) (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) :
    (∃ M : ℕ, (∀ T : Subgroup S, (∀ t ∈ T, α t = t) → Nat.card T ∣ M) ∧
      3 * M ∣ Nat.card S) ∧
      ∃ x₀ y₀ : S, α x₀ = x₀ ∧ α y₀ = y₀ ∧ x₀ ^ 3 = 1 ∧ x₀ ≠ 1 ∧ y₀ * x₀ * y₀⁻¹ = x₀⁻¹ := by
  obtain ⟨i, he⟩ := hcat
  rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple S hS hnab i
      he hr with ⟨⟨d1, hv⟩, hfam, ⟨e⟩⟩ | he | he
  · rcases hfam with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ <;> simp only at hd <;> subst hd
    ·
      obtain ⟨⟨hp, -⟩, F, _, _, hF, ⟨e'⟩⟩ := OutThree.statedClassicalModel_psl_of_typeA 1 q hv e
      have h3 : ¬ 3 ∣ Nat.card F := fun h => by
        have h' : 3 ∣ q.p ^ q.exponent := hF ▸ h
        exact hq ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h')).symm
      exact fixedData_of_mulEquiv_psl2
        (CFSG.RankThree.PartTwo.Sec12.Hering129KYb.three_ne_zero_of_not_dvd h3)
        (e'.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm)
        α hα hout
    ·
      obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := CFSG.Quasithin.A318P.projSL_of_statedClassicalModel_gen
        (OutThree.statedClassicalModel_psl_of_typeA 2 q hv e)
      refine fixedData_of_mulEquiv_projSL_anyChar ?_ e' α hα hout
      rwa [hK, ← TauCeti.PrimePower.card_def]
    ·
      have hm := OutThree.statedClassicalModel_psu_of_twistedA q hv e
      have : Fact q.p.Prime := ⟨hm.1.1⟩
      obtain ⟨e'⟩ := CFSG.Quasithin.A318P.projSU_of_statedClassicalModel_gen hm
      have hf : q.exponent ≠ 0 := by have := hm.1.2.1; omega
      exact fixedData_of_mulEquiv_projSU_of_ne_zero hf (by rwa [← TauCeti.PrimePower.card_def]) e'
        α hα hout
  ·
    obtain ⟨e⟩ := he
    obtain ⟨g, hg⟩ := OutThree.forall_inner_of_j1 e α
    exact (hout ⟨g, hg.symm⟩).elim
  ·
    obtain ⟨e⟩ := he
    obtain ⟨g, hg⟩ := OutThree.autThreePowInner_of_alt_five e α 1 fun x => by
      rw [pow_one, ← OutThree.mulAut_pow_apply, hα]
      rfl
    exact (hout ⟨g, MulEquiv.ext fun x => (hg x).symm⟩).elim

theorem exists_ne_of_sylow_of_catalog
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1) (α : MulAut S) (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) (P : Sylow 3 S) : ∃ y ∈ (P : Subgroup S), α y ≠ y := by
  obtain ⟨M, hM, h3M⟩ := (fixedData_of_catalog hS hnab hcat hr α hα hout).1
  exact exists_ne_of_sylow_of_card_dvd α hM h3M P

theorem exists_inverting_of_catalog
    {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (hcat : CFSG.Open.IsCatalogGroup S)
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1) (α : MulAut S) (hα : α ^ 3 = 1)
    (hout : ¬ IsInnerAut α) (x : S) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hxα : α x = x) :
    ∃ y : S, α y = y ∧ y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨x₀, y₀, hx₀, hy₀, hx₀3, hx₀1, hinv⟩ :=
    (fixedData_of_catalog hS hnab hcat hr α hα hout).2
  have hcyc : ∀ P : Sylow 3 S, IsCyclic P := fun P =>
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.isCyclic_of_pRank_le_one Nat.prime_three
      (by norm_num) P.isPGroup' (by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hr.le)
  obtain ⟨y, hy, hyx⟩ := exists_conj_eq_inv_of_isCyclic_sylow
    (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id S)) hcyc hx₀ hy₀ hx₀3 hx₀1 hinv hxα hx3 hx1
  exact ⟨y, hy, hyx⟩

end Certified

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
