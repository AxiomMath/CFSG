module

public import CFSG.Fischer.Classification.PSU6
public import CFSG.Fischer.Classification.Unitary.Basic
public import CFSG.Fischer.T46Unitary
public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedSUFieldChange

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Blueprint.Fischer CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem card_K : Nat.card K = (2 ^ 1) ^ 2 := by
  show Nat.card (GaloisField 2 2) = _
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem SU_one_eq_statedSU : SU (1 : Matrix (Fin 6) (Fin 6) K) = StatedSU 6 (2 ^ 1) K := by
  rw [← localSU_eq_SU_one, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K 6]
  exact Unitary.SUm_eq 6

theorem center_statedSU_six :
    Subgroup.center (StatedSU 6 (2 ^ 1) K) =
      (StatedScalars (Fin 6) K).subgroupOf (StatedSU 6 (2 ^ 1) K) :=
  (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU card_K (by norm_num) (by decide))
    (CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 card_K 6 (by norm_num)
      (by decide))).2

noncomputable def psuOneEquivStatedProj :
    PSU (1 : Matrix (Fin 6) (Fin 6) K) ≃* StatedProj (StatedSU 6 (2 ^ 1) K) :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr SU_one_eq_statedSU) (by
    rw [← center_statedSU_six]
    exact Subgroup.map_center_eq (MulEquiv.subgroupCongr SU_one_eq_statedSU))

theorem lieModel_of_mulEquiv_PSU {Q : Type} [Group Q] {H : Matrix (Fin 6) (Fin 6) K}
    (hH : IsNondegenerateHermitian H) (e : Q ≃* PSU H) :
    CFSG.Blueprint.LieModel Q .PSU 6 2 1 := by
  obtain ⟨iso, -⟩ := CFSG.Fischer.exists_psu_equiv hH
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, K, inferInstance,
    inferInstance, card_K, ?_⟩
  exact ⟨(e.trans iso.symm).trans psuOneEquivStatedProj⟩

theorem card_PSU_one : Nat.card (PSU (1 : Matrix (Fin 6) (Fin 6) K)) = 9196830720 := by
  rw [← Nat.card_congr CFSG.Fischer.psuEquiv.toEquiv,
    Nat.card_congr CFSG.Fischer.suQuotEquiv.toEquiv, CFSG.Fischer.card_T46]

export CFSG.Open.StatedSUFieldChange (glEquiv glEquiv_coe statedSU_generator_iff map_statedSU
  glEquiv_scalar map_statedScalars statedSUEquiv statedSUEquiv_coe statedProjSUEquiv)

theorem card_statedProj_statedSU_six (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ 1) ^ 2) :
    Nat.card (StatedProj (StatedSU 6 (2 ^ 1) F)) = 9196830720 := by
  have := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card F = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, card_K]
  rw [Nat.card_congr (statedProjSUEquiv (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1)).toEquiv,
    ← Nat.card_congr psuOneEquivStatedProj.toEquiv, card_PSU_one]

theorem card_of_lieModel_PSU_six {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSU 6 2 1) :
    Nat.card Q = 9196830720 := by
  rcases h with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [Nat.card_congr e.toEquiv]
    exact card_statedProj_statedSU_six F hF
  all_goals exact absurd h0 (by norm_num)

end CFSG.Fischer.Classification.Recognition
