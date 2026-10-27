module

public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.Generic5
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Covers
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.GH74.Generic.Certificates
import CFSG.GH74.Bender.Suzuki

public section

namespace CFSG.GH74.KGroups

open CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem equiv_psl2_of_lieModel_even {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : LieModel S .PSL 2 2 f) : Nonempty (S ≃* CFSG.Theory.Comparator.PSL2Model f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact PSLN.psl_equiv_of_lieModel (F := GaloisField 2 f) 2 2 f (by omega)
    (GaloisField.card 2 f (by omega)) h

theorem equiv_psu3_of_lieModel_even {S : Type} [Group S] {f : ℕ} (hf : 2 ≤ f)
    (h : LieModel S .PSU 3 2 f) : Nonempty (S ≃* CFSG.Open.PSU3 2 f) := by
  rcases h with ⟨-, ⟨-, K, _, _, hK, ⟨e⟩⟩⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
    let e' : S ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
    exact ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

theorem noTwoCover_even (S : Type) [Group S]
    (h : LieModel S .PSL 2 2 3 ∨ LieModel S .PSL 2 2 4 ∨ LieModel S .PSU 3 2 2) :
    NoTwoCover S := by
  intro K _ _ hK hZ2 ⟨e⟩
  by_contra hZ
  obtain ⟨hperf0, hsimple, -⟩ := hK
  have hperf : commutator K = ⊤ := hperf0.commutator_eq_top
  have hJ := center_quotient_eq_bot hperf hsimple
  obtain ⟨C, _, _, φ, hφ, hker, hperfC, hcard, ⟨eC⟩⟩ := exists_double_cover hperf hZ2 hZ hJ
  have key : CFSG.BenderSuzuki.IsBenderGroup S ∧
      (Nat.card S = 504 ∨ Nat.card S = 4080 ∨ Nat.card S = 62400) := by
    rcases h with h | h | h
    · obtain ⟨e1⟩ := equiv_psl2_of_lieModel_even (f := 3) (by norm_num) h
      refine ⟨CFSG.BenderSuzuki.IsBenderGroup.isPSL2 3 (by norm_num) e1, Or.inl ?_⟩
      rw [Nat.card_congr e1.toEquiv, CFSG.Theory.Comparator.PSL2Model,
        CFSG.Walter.psl2_even_card (f := 3) (by norm_num)]
      norm_num
    · obtain ⟨e1⟩ := equiv_psl2_of_lieModel_even (f := 4) (by norm_num) h
      refine ⟨CFSG.BenderSuzuki.IsBenderGroup.isPSL2 4 (by norm_num) e1, Or.inr (Or.inl ?_)⟩
      rw [Nat.card_congr e1.toEquiv, CFSG.Theory.Comparator.PSL2Model,
        CFSG.Walter.psl2_even_card (f := 4) (by norm_num)]
      norm_num
    · obtain ⟨e1⟩ := equiv_psu3_of_lieModel_even (f := 2) (by norm_num) h
      have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
        simp only [CFSG.Theory.Comparator.PSU3Model, CFSG.Open.PSU3]
      refine ⟨CFSG.BenderSuzuki.IsBenderGroup.isPSU3 2 (by norm_num)
        (e1.trans (MulEquiv.subgroupCongr hmodel.symm)), Or.inr (Or.inr ?_)⟩
      rw [Nat.card_congr e1.toEquiv,
        CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3 (by norm_num)]
      norm_num
  obtain ⟨hB, hord⟩ := key
  have eS : C ⧸ Subgroup.center C ≃* S := eC.trans e
  have hBC : CFSG.BenderSuzuki.IsBenderGroup (C ⧸ Subgroup.center C) := by
    rcases hB with ⟨n, hn, e1⟩ | ⟨n, hn, e1⟩ | ⟨n, hn, e1⟩
    · exact .isPSL2 n hn (eS.trans e1)
    · exact .isSuzuki n hn (eS.trans e1)
    · exact .isPSU3 n hn (eS.trans e1)
  rcases CFSG.ProperTwoGeneratedCore.Lemma37.bender_cover_quotient hperfC hcard hBC with
    ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩
  · have h1 : Nat.card S = Nat.card (CFSG.Theory.Comparator.PSL2Model 2) :=
      Nat.card_congr (eS.symm.trans e1).toEquiv
    rw [CFSG.Theory.Comparator.PSL2Model, CFSG.Walter.psl2_even_card (f := 2) (by norm_num)] at h1
    norm_num at h1
    omega
  · have h1 : Nat.card S = Nat.card ↥(CFSG.Theory.Comparator.SzModel 1) :=
      Nat.card_congr (eS.symm.trans e1).toEquiv
    rw [CFSG.GH74.Bender.szModel_eq_sz,
      CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz] at h1
    norm_num at h1
    omega

end CFSG.GH74.KGroups
