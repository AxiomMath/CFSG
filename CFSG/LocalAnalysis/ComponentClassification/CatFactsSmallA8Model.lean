module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModelConj
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.GH74.KGroups.Checks
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8ModelInputs
public import Certificates.Certificate2007

public section

namespace CFSG.ComponentClassification.CatFactsSmall.A8

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup

local notation "P8" => Equiv.Perm (Fin 8)

theorem QS8_valid : QS8.check = true ∧ QS8.orderCertificate = 40320 :=
  Certificates.certificate2007.1

theorem QA8_valid : QA8.check = true ∧ QA8.orderCertificate = 20160 :=
  Certificates.certificate2007.2

theorem QS8_ok : ValidSchreier QS8 := QS8_valid.1

theorem QA8_ok : ValidSchreier QA8 := QA8_valid.1

theorem card_QS8 : Nat.card QS8.originalSubgroup = 40320 := by
  rw [card_group QS8 QS8_ok, QS8_valid.2]

theorem card_QA8 : Nat.card QA8.originalSubgroup = 20160 := by
  rw [card_group QA8 QA8_ok, QA8_valid.2]

theorem QS8_eq : QS8.originalSubgroup = ⊤ := by
  apply eq_top_of_card_eq
  rw [card_QS8, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_alt8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem QA8_eq : QA8.originalSubgroup = alternatingGroup (Fin 8) := by
  have hle : QA8.originalSubgroup ≤ alternatingGroup (Fin 8) := by
    rw [QA8, certificate_originalSubgroup, closure_le]
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [tab_eq]
      exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
    · rw [tab_eq]
      exact Equiv.Perm.mem_alternatingGroup.2 (by decide)
  exact eq_of_le_of_card_ge hle (by rw [card_QA8, card_alt8])

theorem exists_model {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 8)) :
    ∃ M : AutModel K P8, M.P = QA8.originalSubgroup ∧ M.A = QS8.originalSubgroup := by
  have hb := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
    (by norm_num)
  let Φ' : (⊤ : Subgroup P8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    topEquiv.trans (MulEquiv.ofBijective _ hb)
  let e' : K ≃* QA8.originalSubgroup := e.trans (MulEquiv.subgroupCongr QA8_eq.symm)
  let Φ'' : QS8.originalSubgroup ≃* MulAut QA8.originalSubgroup :=
    (MulEquiv.subgroupCongr QS8_eq).trans (Φ'.trans
      (MulAut.congr (MulEquiv.subgroupCongr QA8_eq.symm)))
  refine ⟨AutModel.ofRealization QA8.originalSubgroup QS8.originalSubgroup e' Φ'' ?_, rfl, rfl⟩
  intro σ x
  rfl

theorem s8_mem : s8 ∈ QS8.originalSubgroup := by
  rw [QS8_eq]
  exact mem_top _

end CFSG.ComponentClassification.CatFactsSmall.A8
