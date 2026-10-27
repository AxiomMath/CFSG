module

public import CFSG.ClassicalInvolution.Q3.Q3T6OpenStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenEBasic
public import CFSG.ClassicalInvolution.Q3.Q3T6MainFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section MuUse


theorem not_muIsoZ2_of_muIsoS3' {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
    (h3 : MuIsoS3 Ω W) : ¬ MuIsoZ2 Ω W := by
  rintro ⟨e2⟩
  obtain ⟨e3⟩ := h3
  have h := (Nat.card_congr e2.toEquiv).symm.trans (Nat.card_congr e3.toEquiv)
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_perm, Nat.card_fin] at h
  norm_num [Nat.factorial] at h

theorem c19_2Three_of (hS3 : MuS3OfShape3) (hZ2 : MuZ2OfShape3) : C19_2Three := by
  intro G _ _ _ Ω K hs he W hW
  have hP : Q3CL.PartIHypG Ω := Q3CL.partIHypG_of_modU hs.hyp hs.aEmpty
  by_cases h : ∃ J ∈ Ω, (omegaStarNbr Ω J).Nonempty
  · exact Or.inr (hS3 G Ω hP W hW he h)
  · refine Or.inl (hZ2 G Ω hP W hW ⟨K, hs.mem⟩ fun J hJ => ?_)
    exact Set.not_nonempty_iff_eq_empty.mp fun hne => h ⟨J, hJ, hne⟩

theorem notAllTypeTwoOfS3_of (hZ2 : MuZ2OfShape3) : NotAllTypeTwoOfS3 := by
  intro G _ _ _ Ω K S R z hstd W hW hS3 hA
  have ht := hstd.tight
  obtain rfl := hstd.eq_conjClass
  have hP : Q3CL.PartIHypG (CoreAssembly.conjClass K) :=
    Q3CL.partIHypG_of_modU hstd.stand.hyp hstd.stand.aEmpty
  refine not_muIsoZ2_of_muIsoS3' hS3
    (hZ2 G _ hP W hW ⟨K, CoreAssembly.mem_conjClass_self K⟩ fun J hJ => ?_)
  refine Set.eq_empty_of_forall_notMem ?_
  rintro J' ⟨hJ', hne, U, hU, hUJ', hUN⟩
  obtain ⟨w, hw⟩ := ht.exists_isUniqueInvolution_member hJ
  obtain ⟨u, hu⟩ := ht.exists_isUniqueInvolution_member hJ'
  obtain ⟨x, rfl⟩ := CoreAssembly.single_class K J hJ
  have hwx : x * z * x⁻¹ = w := (ht.isUniqueInvolution.conj x).eq hw
  have hUw : U ≤ Subgroup.centralizer ({w} : Set G) :=
    (ht.normalizer_eq_centralizer_member hJ hw) ▸ hUN
  obtain ⟨R', hR', hUR', -, hidx⟩ := hU
  have h8 := ht.natCard_rSet hR'
  have hcard : Nat.card R' = 2 * Nat.card U := by
    have h1 := Subgroup.relIndex_mul_card (H := U) (K := R')
    rw [inf_eq_left.mpr hUR', hidx] at h1
    exact h1.symm
  have hU2 : IsPGroup 2 U := (isPGroup_of_mem_rSet hR').to_le hUR'
  have huU : u ∈ U := S1911.mem_of_le_member hu hUJ' hU2 (by omega)
  have hwu : w ≠ u := by
    rintro rfl
    exact hne (ht.eq_of_isUniqueInvolution_member hJ' hJ hu hw)
  have hcomm : w * u = u * w := (Subgroup.mem_centralizer_singleton_iff.mp (hUw huU)).symm
  have h2 := hA J' hJ' u w hu ⟨x, hwx⟩ hwu hcomm U hU2 hUJ' hUw
  omega

end MuUse

end CFSG.ClassicalInvolution.Q3.Q3T6
