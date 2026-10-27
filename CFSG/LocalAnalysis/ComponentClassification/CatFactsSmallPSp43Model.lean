module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModelConj
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.GH74.Generic.Context
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.Fischer.Classification.PartIII.Beta.Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelInputs
public import Certificates.Certificate2012

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.GH74.Exceptional CFSG.Fischer.Classification.Beta CFSG.Assembly.LowTwoRank

local notation "P45" => Equiv.Perm (Fin 45)

theorem psi_injective : Function.Injective psi :=
  rho43_injective.comp psp43EquivU2.injective

theorem psi_s43_eq (i : Fin 45) : psi (s43 i) = tauPerm i :=
  Equiv.ext fun j => psi_s43 i j

theorem QP45_valid : QP45.check = true ∧ QP45.orderCertificate = 25920 :=
  Certificates.certificate2012.1

theorem QA45_valid : QA45.check = true ∧ QA45.orderCertificate = 51840 :=
  Certificates.certificate2012.2.1

theorem QP45_ok : ValidSchreier QP45 := QP45_valid.1

theorem QA45_ok : ValidSchreier QA45 := QA45_valid.1

theorem tau_sift : (List.finRange 45).all (fun j => QP45.sift (tauPerm j) 0) = true :=
  Certificates.certificate2012.2.2.1

theorem x45_facts : orderIs x45 2 = true ∧ orderIs y45 5 = true ∧
    pairInvB ws45 x45 y45 = true :=
  Certificates.certificate2012.2.2.2.1

theorem count_ok : NativeChecks.pairCountE QP45 2 5 ws45 = 51840 :=
  Certificates.certificate2012.2.2.2.2.1

theorem norm_ok : normCheck QP45 QA45.original.toList x45 y45 = true :=
  Certificates.certificate2012.2.2.2.2.2.1

theorem centA_ok : CFSG.KGroups.Native.centTrivA 45 (NativeChecks.enumA QA45)
    (NativeChecks.toA x45) (NativeChecks.toA y45) = true :=
  Certificates.certificate2012.2.2.2.2.2.2

theorem cent_ok : centTrivCheck (elemsT QA45) x45 y45 = true := by
  rw [NativeChecks.centTrivCheck_enumA]
  exact centA_ok

theorem QP45_closure : QP45.originalSubgroup = closure {x45, y45} := by
  rw [QP45, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem QA45_closure : QA45.originalSubgroup = closure {x45, y45, f45} := by
  rw [QA45, certificate_originalSubgroup]
  congr 1
  ext g
  simp [tab_eq]

theorem range_psi : psi.range = QP45.originalSubgroup := by
  have hY : psi.range = closure (Set.range tauPerm) := by
    rw [MonoidHom.range_eq_map, ← Y43_eq_top, MonoidHom.map_closure, ← Set.range_comp]
    congr 1
    ext g
    simp [psi_s43_eq]
  rw [hY]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_iff_sift QP45 QP45_ok]
    exact List.all_eq_true.1 tau_sift j (List.mem_finRange j)
  · rw [QP45_closure, closure_le]
    have hmem : ∀ i, tauPerm i ∈ closure (Set.range tauPerm) := fun i =>
      subset_closure ⟨i, rfl⟩
    rintro g (rfl | rfl)
    · exact hmem 0
    · exact mul_mem (mul_mem (mul_mem (hmem 31) (hmem 5)) (hmem 36)) (hmem 44)

@[expose] noncomputable def psp43EquivP : PSp43 ≃* QP45.originalSubgroup :=
  (MonoidHom.ofInjective psi_injective).trans (MulEquiv.subgroupCongr range_psi)

theorem equiv_of_lieModel {K : Type} [Group K] (h : Blueprint.LieModel K .PSp 2 3 1) :
    Nonempty (K ≃* QP45.originalSubgroup) := by
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data h
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 3) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
    rfl
  let φ : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hc
  let e₁ : StatedProj (StatedSp 2 F) ≃* PSp43 :=
    Adapters.RankTwoModelTransports.statedProjCongr (Adapters.RankTwoModelTransports.glCongr φ)
      (ClassicalInvolution.Upgrade.glCongr_statedSp φ 2)
      (Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨(e.trans e₁).trans psp43EquivP⟩

theorem exists_model {K : Type*} [Group K] (e : K ≃* QP45.originalSubgroup) :
    ∃ M : AutModel K P45, M.P = QP45.originalSubgroup ∧ M.A = QA45.originalSubgroup := by
  obtain ⟨h1, h2, h3⟩ := x45_facts
  exact autModel_exists QP45 QA45 QP45_ok QA45_ok x45 y45 QP45_closure 2 5 (by norm_num)
    (by norm_num) ws45 (by simp [ws45]) ((orderIs_iff _ (by norm_num)).1 h1)
    ((orderIs_iff _ (by norm_num)).1 h2) ((pairInvB_iff ws45 (by simp [ws45]) _ _).1 h3)
    (by rw [NativeChecks.pairCountB_eq_E, count_ok, QA45_valid.2]) norm_ok cent_ok e

end CFSG.ComponentClassification.CatFactsSmall.PSp43
