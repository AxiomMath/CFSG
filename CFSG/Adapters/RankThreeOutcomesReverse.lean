module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Adapters.ClassicalCatalogReverse
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Models.PGL

public section

namespace CFSG.Assembly.RankThreeEven

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalModels
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)
open CFSG.RankThree.PartOne (projImage_statedSL_eq_projSL projImage_statedSU_eq_projSU
  projImage_statedSp_eq_projSp projImage_statedOmegaMinus_eq_projOmegaMinus)

theorem statedClassicalModel_of_projSL {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSL n p f) (e : G ≃* projSL n (GaloisField p f)) :
    StatedClassicalModel G .PSL n p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e

theorem statedClassicalModel_of_projSU {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSU n p f) (e : G ≃* projSU n p f) :
    StatedClassicalModel G .PSU n p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e

theorem statedClassicalModel_of_projSp {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSp n p f) (e : G ≃* projSp n (GaloisField p f)) :
    StatedClassicalModel G .PSp n p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm e

theorem statedClassicalModel_of_projOmegaPlus {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .POmegaPlus n p f) (e : G ≃* projOmegaPlus n (GaloisField p f)) :
    StatedClassicalModel G .POmegaPlus n p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projOmegaPlus hadm e

theorem statedClassicalModel_of_projOmegaMinus {G : Type} [Group G] {m p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .POmegaMinus (m + 1) p f) {b c : GaloisField p f}
    (hbc : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* projOmegaMinus m (GaloisField p f) b c) :
    StatedClassicalModel G .POmegaMinus (m + 1) p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projOmegaMinus hadm hbc e

theorem inCatalog_of_iModel (G : Type) [Group G] (h : IModel G) :
    CFSG.Assembly.InCatalog G := by
  obtain ⟨f, hf, ⟨⟨e⟩⟩ | ⟨b, c, hbc, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩⟩ := h
  · exact inCatalog_of_statedClassicalModel G .PSU 5 2 f
      (statedClassicalModel_of_projSU ⟨Nat.prime_two, hf, by norm_num, by simp⟩ e)
  · exact inCatalog_of_statedClassicalModel G .POmegaMinus 4 2 f
      (statedClassicalModel_of_projOmegaMinus (m := 3) ⟨Nat.prime_two, hf, le_rfl⟩ hbc e)
  · exact inCatalog_of_statedClassicalModel G .PSL 4 2 f
      (statedClassicalModel_of_projSL ⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSp 3 2 f
      (statedClassicalModel_of_projSp ⟨Nat.prime_two, hf, by norm_num, by simp⟩ e)

theorem inCatalog_of_iiClassical (G : Type) [Group G]
    (h : IIClassical G) : CFSG.Assembly.InCatalog G := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨b, c, hbc, ⟨e⟩⟩ | ⟨⟨e⟩⟩ |
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact inCatalog_of_statedClassicalModel G .PSU 5 2 1
      (statedClassicalModel_of_projSU ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSU 6 2 1
      (statedClassicalModel_of_projSU ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSL 6 2 1
      (statedClassicalModel_of_projSL ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSL 7 2 1
      (statedClassicalModel_of_projSL ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSp 4 2 1
      (statedClassicalModel_of_projSp ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .POmegaPlus 4 2 1
      (statedClassicalModel_of_projOmegaPlus ⟨Nat.prime_two, le_rfl, le_rfl⟩ e)
  · exact inCatalog_of_statedClassicalModel G .POmegaMinus 4 2 1
      (statedClassicalModel_of_projOmegaMinus (m := 3) ⟨Nat.prime_two, le_rfl, le_rfl⟩ hbc e)
  · exact inCatalog_of_statedClassicalModel G .PSL 4 2 2
      (statedClassicalModel_of_projSL ⟨Nat.prime_two, by norm_num, by norm_num, by decide,
        by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSp 3 2 2
      (statedClassicalModel_of_projSp ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩ e)
  · exact inCatalog_of_statedClassicalModel G .PSU 5 2 3
      (statedClassicalModel_of_projSU ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩ e)

theorem inCatalog_of_iModel_or_iiClassical (G : Type) [Group G]
    (h : IModel G ∨ IIClassical G) : CFSG.Assembly.InCatalog G :=
  h.elim (inCatalog_of_iModel G) (inCatalog_of_iiClassical G)

end CFSG.Assembly.RankThreeEven
