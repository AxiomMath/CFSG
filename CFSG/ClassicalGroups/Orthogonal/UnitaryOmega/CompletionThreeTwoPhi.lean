module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.ChartsThree
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Chamber
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.SeitzReduction.UnitaryPilot CFSG.Permutation.ProperSupportMaps

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {H : Type} [Group H]

theorem pair_ne_univ_four (i j : Fin 4) : ({i, j} : Finset (Fin 4)) ≠ Finset.univ :=
  (Finset.card_lt_iff_ne_univ _).mp (Finset.card_le_two.trans_lt (by simp))

@[expose] noncomputable def deletionPhiThree (t : Equiv.Perm (Fin 4) →* H)
    (κ : normOmega E 3 →* H) (S : Finset (Fin 4)) (hS : S ≠ Finset.univ) :
    normBlock E 4 S →* H :=
  properSupportPhi (hB := normBlock_mono E (3 + 1)) (a := deletionChart E 3 κ) (t := t)
    (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1)) S hS

variable {E} {t : Equiv.Perm (Fin 4) →* H} {κ : normOmega E 3 →* H}

theorem deletionPhiThree_of_subset
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {R S : Finset (Fin 4)} (hR : R ≠ Finset.univ) (hS : S ≠ Finset.univ) (hRS : R ⊆ S)
    {x : normOmega E 4} (hx : x ∈ normBlock E 4 R) :
    deletionPhiThree E t κ S hS ⟨x, normBlock_mono E 4 hRS hx⟩ =
      deletionPhiThree E t κ R hR ⟨x, hx⟩ := by
  classical
  have hcomp := properSupportPhi_comp_inclusion
    (hB := normBlock_mono E (3 + 1)) (a := deletionChart E 3 κ) (t := t)
    (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1))
    (fun (S : Finset (Fin (3 + 1))) _ hS => normBlock_eq_iSup_pairs E (3 + 1) S hS)
    (deletionChart_pairCovariance_three E t κ hT1 hC) (by simp) R S hR hS hRS
  exact DFunLike.congr_fun hcomp (⟨x, hx⟩ : normBlock E (3 + 1) R)

theorem commute_deletionPhiThree
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {R S : Finset (Fin 4)} (hR : R ≠ Finset.univ) (hS : S ≠ Finset.univ)
    (hRS : R ∪ S ≠ Finset.univ) {x y : normOmega E 4} (hx : x ∈ normBlock E 4 R)
    (hy : y ∈ normBlock E 4 S) (hxy : Commute x y) :
    Commute (deletionPhiThree E t κ R hR ⟨x, hx⟩) (deletionPhiThree E t κ S hS ⟨y, hy⟩) := by
  classical
  have hRT : R ⊆ R ∪ S := Finset.subset_union_left
  have hST : S ⊆ R ∪ S := Finset.subset_union_right
  have hxT : x ∈ normBlock E 4 (R ∪ S) := normBlock_mono E 4 hRT hx
  have hyT : y ∈ normBlock E 4 (R ∪ S) := normBlock_mono E 4 hST hy
  have hcomm : Commute (⟨x, hxT⟩ : normBlock E 4 (R ∪ S)) ⟨y, hyT⟩ := Subtype.ext hxy.eq
  have h := hcomm.map (deletionPhiThree E t κ (R ∪ S) hRS)
  rw [deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC hR hRS hRT hx,
    deletionPhiThree_of_subset (E := E) (t := t) (κ := κ) hT1 hC hS hRS hST hy] at h
  exact h

theorem deletionPhiThree_normOmegaCast
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {S : Finset (Fin 4)} (hS : S ≠ Finset.univ) (hS3 : (3 : Fin 4) ∉ S) (a : normOmega E 3)
    (ha : normOmegaCast E (Nat.le_succ 3) a ∈ normBlock E 4 S) :
    deletionPhiThree E t κ S hS ⟨_, ha⟩ = κ a := by
  classical
  have hSD : S ⊆ deletionSet (Fin.last 3) := by
    intro x hx
    rw [mem_deletionSet]
    intro hxlast
    have hx' : Fin.last 3 ∈ S := hxlast ▸ hx
    have hlast : Fin.last 3 = (3 : Fin 4) := rfl
    exact hS3 (hlast ▸ hx')
  have hsub := properSupportPhi_apply_of_subset
    (hB := normBlock_mono E (3 + 1)) (a := deletionChart E 3 κ) (t := t)
    (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1))
    (fun (S : Finset (Fin (3 + 1))) _ hS => normBlock_eq_iSup_pairs E (3 + 1) S hS)
    (deletionChart_pairCovariance_three E t κ hT1 hC) (by simp) S hS hSD
    ⟨normOmegaCast E (Nat.le_succ 3) a, ha⟩
  change properSupportPhi (hB := normBlock_mono E (3 + 1)) (a := deletionChart E 3 κ)
    (t := t) (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1)) S hS
    ⟨normOmegaCast E (Nat.le_succ 3) a, ha⟩ = κ a
  rw [hsub]
  have hmem : normOmegaCast E (Nat.le_succ 3) a ∈
      normBlock E (3 + 1) (deletionSet (Fin.last 3)) :=
    normBlock_mono E (3 + 1) hSD ha
  have harg : Subgroup.inclusion (normBlock_mono E (3 + 1) hSD)
      (⟨normOmegaCast E (Nat.le_succ 3) a, ha⟩ : normBlock E (3 + 1) S) =
      ⟨normOmegaCast E (Nat.le_succ 3) a, hmem⟩ := rfl
  rw [harg]
  exact deletionChart_apply E 3 κ a hmem

theorem exists_deletionPhiThree_singleton_three
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    {g : normOmega E 4} (hg : g ∈ normBlock E 4 {3}) :
    ∃ b ∈ normBlock E 3 {2}, deletionPhiThree E t κ {3} (by decide) ⟨g, hg⟩ =
      t (Equiv.swap 2 3) * κ b * (t (Equiv.swap 2 3))⁻¹ := by
  classical
  let τ : Equiv.Perm (Fin 4) := Equiv.swap 2 3
  have hτ : ({3} : Finset (Fin 4)).image τ = ({2} : Finset (Fin 4)) := by
    rw [Finset.image_singleton]
    congr 1
  have hττ : τ * τ = 1 := by
    dsimp [τ]
    exact Equiv.swap_mul_self 2 3
  have htτ : t τ * t τ = 1 := by
    rw [← map_mul, hττ, map_one]
  have hinv : (t τ)⁻¹ = t τ := inv_eq_of_mul_eq_one_right htτ
  have hσ : ({3} : Finset (Fin 4)).image τ ⊆ deletionSet (Fin.last 3) := by
    rw [hτ, Finset.singleton_subset_iff, mem_deletionSet]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hformula := properSupportPhi_apply_of_image_subset
    (hB := normBlock_mono E (3 + 1)) (a := deletionChart E 3 κ) (t := t)
    (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1))
    (fun (S : Finset (Fin (3 + 1))) _ hS => normBlock_eq_iSup_pairs E (3 + 1) S hS)
    (deletionChart_pairCovariance_three E t κ hT1 hC) (by simp)
    ({3} : Finset (Fin (3 + 1))) (by simp) τ hσ ⟨g, hg⟩
  let c := conjMapHom (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1)) τ
    ({3} : Finset (Fin (3 + 1))) ⟨g, hg⟩
  have hc : (c : normOmega E (3 + 1)) ∈
      normBlock E (3 + 1) ({2} : Finset (Fin (3 + 1))) :=
    normBlock_mono E (3 + 1) hτ.le c.2
  have hmap2 : (({2} : Finset (Fin 3)).map (Fin.castLEEmb (Nat.le_succ 3))) =
      ({2} : Finset (Fin 4)) := by
    rw [Finset.map_singleton]
    congr 1
  have hx' : (c : normOmega E 4) ∈
      (normBlock E 3 ({2} : Finset (Fin 3))).map (normOmegaCast E (Nat.le_succ 3)) := by
    rw [map_normBlock_normOmegaCast]
    exact normBlock_mono E (3 + 1) hmap2.ge hc
  obtain ⟨b, hb, hbc⟩ := Subgroup.mem_map.mp hx'
  have hmem : normOmegaCast E (Nat.le_succ 3) b ∈
      normBlock E (3 + 1) (deletionSet (Fin.last 3)) := by
    rw [hbc]
    exact normBlock_mono E (3 + 1) hσ c.2
  have hval : deletionChart E 3 κ
      (⟨(c : normOmega E (3 + 1)), normBlock_mono E (3 + 1) hσ c.2⟩ :
        normBlock E (3 + 1) (deletionSet (Fin.last 3))) = κ b := by
    have harg : (⟨(c : normOmega E (3 + 1)),
        normBlock_mono E (3 + 1) hσ c.2⟩ :
        normBlock E (3 + 1) (deletionSet (Fin.last 3))) =
        ⟨normOmegaCast E (Nat.le_succ 3) b, hmem⟩ := by
      apply Subtype.ext
      exact hbc.symm
    rw [harg]
    exact deletionChart_apply E 3 κ b hmem
  refine ⟨b, hb, ?_⟩
  have hformula' : deletionPhiThree E t κ ({3} : Finset (Fin 4)) (by decide) ⟨g, hg⟩ =
      (t τ)⁻¹ * deletionChart E 3 κ
        (⟨(c : normOmega E (3 + 1)), normBlock_mono E (3 + 1) hσ c.2⟩ :
          normBlock E (3 + 1) (deletionSet (Fin.last 3))) * t τ := hformula
  rw [hformula', hval, hinv]

theorem deletionPhiThree_normPerm_swap
    (hT1 : t.comp (Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb) = κ.comp (normPerm E le_rfl))
    (hC : ∀ y ∈ (anchorBlock E (by norm_num : 2 ≤ 3)).map κ, Commute (t (Equiv.swap 2 3)) y)
    (i j : Fin 4) :
    deletionPhiThree E t κ {i, j} (pair_ne_univ_four i j)
        ⟨normPerm E (by norm_num) (Equiv.swap i j),
          normPerm_swap_mem_normBlock E (by norm_num) i j⟩ =
      t (Equiv.swap i j) := by
  classical
  have hfix : ∀ x : Fin 4, x ∉ ({i, j} : Finset (Fin 4)) → Equiv.swap i j x = x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2
  have hmem : (normPerm E (by norm_num : 3 ≤ 3 + 1) (Equiv.swap i j) :
      normOmega E (3 + 1)) ∈ normBlock E (3 + 1) ({i, j} : Finset (Fin (3 + 1))) :=
    normPerm_swap_mem_normBlock E (by norm_num : 3 ≤ 3 + 1) i j
  exact properSupportPhi_apply_common
    (hB := normBlock_mono E (3 + 1)) (a := deletionChart E 3 κ) (t := t)
    (map_normBlock_normPerm E (by norm_num : 3 ≤ 3 + 1))
    (fun (S : Finset (Fin (3 + 1))) _ hS => normBlock_eq_iSup_pairs E (3 + 1) S hS)
    (deletionChart_pairCovariance_three E t κ hT1 hC) (by simp)
    ({i, j} : Finset (Fin (3 + 1))) (pair_ne_univ_four i j)
    (Equiv.swap i j) hfix hmem (deletionChart_common E (by norm_num : 3 ≤ 3) t κ hT1)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
