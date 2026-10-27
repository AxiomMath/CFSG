module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryOvergroup
import CFSG.GroupTheory.CenterSupNormalizer

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {q : ℕ}
  (hK : Nat.card K = q ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = q)

include hK hfix

theorem dvd_index_of_le_stabilizer_pinf {S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hS : S ≤ MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) :
    q ^ 3 + 1 ∣ S.index := by
  have : MulAction.IsMultiplyPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) 2 :=
    isMultiplyPretransitive_two J hJ q hK hfix
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have h := Subgroup.index_dvd_of_le hS
  rwa [MulAction.index_stabilizer_of_transitive, card_isoPoint J hJ q hK hfix] at h

theorem sup_eq_top_of_rootGroup_le_of_odd_index (hq : 2 < q) (hqo : Odd q)
    {S H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)} (hS : ¬ 2 ∣ S.index)
    (hH : rootGroup J hJ ≤ H) : S ⊔ H = ⊤ := by
  by_contra hne
  have hSH : S ⊔ H ≤
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) :=
    le_stabilizer_pinf_of_rootGroup_le J hJ hK hfix hq (hH.trans le_sup_right) hne
  have hdvd := dvd_index_of_le_stabilizer_pinf J hJ hK hfix (le_sup_left.trans hSH)
  exact hS ((even_iff_two_dvd.mp (Odd.add_one hqo.pow)).trans hdvd)

end Model

theorem exists_isMulCommutative_sylow_two_sup_normalizer_eq_top {L : Type} [Group L] [Finite L]
    {p f : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hst : CFSG.Open.StatedClassicalModel L .PSU 3 p f)
    {A : Subgroup L} (hA : IsPGroup p A) [IsMulCommutative A] (S : Sylow 2 L) :
    ∃ C : Subgroup L, IsMulCommutative C ∧ A ≤ C ∧
      (S : Subgroup L) ⊔ Subgroup.normalizer (C : Set L) = ⊤ := by
  obtain ⟨-, hf, hq2, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ := exists_equiv_psu hst
  obtain ⟨U, hAU⟩ := hA.exists_le_sylow
  obtain ⟨R, hR⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U R
  have hUmap : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hR
  let A' : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := A.map e'.toMonoidHom
  let C₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (rootGroup J hJ ⊓ Subgroup.centralizer (rootGroup J hJ : Set _)) ⊔ A'
  have hA'le : A' ≤ rootGroup J hJ := by
    change A.map e'.toMonoidHom ≤ rootGroup J hJ
    rw [← hUmap]
    exact Subgroup.map_mono hAU
  have hA'abel : IsMulCommutative A' := Subgroup.map_isMulCommutative (H := A) e'.toMonoidHom
  have hC₀abel : IsMulCommutative C₀ :=
    CFSG.GroupTheory.isMulCommutative_inf_centralizer_sup (U := rootGroup J hJ) (A := A') hA'le
  have hUcomm : ⁅rootGroup J hJ, rootGroup J hJ⁆ ≤
      Subgroup.centralizer (rootGroup J hJ : Set _) := by
    rw [commutator_rootGroup (p := p) (f := f) J hJ hK hfix]
    exact inf_le_right
  have hNs : rootGroup J hJ ≤ Subgroup.normalizer (C₀ : Set _) :=
    CFSG.GroupTheory.le_normalizer_inf_centralizer_sup (U := rootGroup J hJ) (A := A')
      hA'le hUcomm
  have hqo : Odd (p ^ f) := (Fact.out : p.Prime).odd_of_ne_two hp |>.pow
  have hS' : ¬ 2 ∣ ((S : Subgroup L).map e'.toMonoidHom).index := by
    simpa using S.not_dvd_index
  have hsup : ((S : Subgroup L).map e'.toMonoidHom) ⊔
      Subgroup.normalizer (C₀ : Set _) = ⊤ :=
    sup_eq_top_of_rootGroup_le_of_odd_index J hJ hK hfix hq2 hqo hS' hNs
  let C : Subgroup L := C₀.comap e'.toMonoidHom
  have hCmap : C.map e'.toMonoidHom = C₀ :=
    Subgroup.map_comap_eq_self_of_surjective (f := e'.toMonoidHom) e'.surjective C₀
  have hCabel : IsMulCommutative C :=
    Subgroup.comap_injective_isMulCommutative (H := C₀) (f := e'.toMonoidHom) e'.injective
  have hAC : A ≤ C :=
    Subgroup.map_le_iff_le_comap.mp (le_sup_right : A.map e'.toMonoidHom ≤ C₀)
  refine ⟨C, hCabel, hAC, ?_⟩
  apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
  rw [Subgroup.map_sup, Subgroup.map_equiv_normalizer_eq, hCmap,
    Subgroup.map_top_of_surjective e'.toMonoidHom e'.surjective]
  exact hsup

end CFSG.AGLEmbedding.UnitaryModel

end
