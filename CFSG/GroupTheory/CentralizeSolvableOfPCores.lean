module

public import CFSG.Open.LocalVocabulary
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_bot_of_forall_pCoreOf {J K : Subgroup G} (hK : IsSolvable K)
    (hJ : ⁅J, J⁆ = J) (hJK : J ≤ Subgroup.normalizer (K : Set G))
    (h : ∀ q : ℕ, q.Prime → ⁅J, CFSG.Open.pCoreOf q K⁆ = ⊥) :
    ⁅J, K⁆ = ⊥ := by
  let F : Subgroup G := (CFSG.fittingSubgroup (↥K)).map K.subtype
  have hF : F = ⨆ q : (Nat.card (↥K)).primeFactors.attach,
      CFSG.Open.pCoreOf q.1.1 K := by
    dsimp only [F, CFSG.Open.pCoreOf]
    rw [CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
  have hJF : ⁅J, F⁆ = ⊥ := by
    rw [hF, Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (S := fun q : (Nat.card (↥K)).primeFactors.attach =>
        CFSG.Open.pCoreOf q.1.1 K) ?_
    intro q
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (h q.1.1 (Nat.prime_of_mem_primeFactors q.1.2))
  have hFK : ⁅F, K⁆ ≤ F := by
    have hnorm : K ≤ Subgroup.normalizer (F : Set G) := by
      have hmap := Subgroup.le_normalizer_map
        (H := CFSG.fittingSubgroup (↥K)) K.subtype
      have hnormK : Subgroup.normalizer
          (CFSG.fittingSubgroup (↥K) : Set ↥K) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
        simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := K))
      rw [hnormK, htop] at hmap
      simpa [F] using hmap
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hnorm
  have hKJF : ⁅⁅K, J⁆, F⁆ = ⊥ := by
    have h1 : ⁅⁅J, F⁆, K⁆ = ⊥ := by
      rw [hJF, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅F, K⁆, J⁆ = ⊥ := by
      have hFJ : ⁅F, J⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact hJF
      exact le_bot_iff.mp (hFJ ▸ Subgroup.commutator_mono hFK le_rfl)
    exact Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := K) (H₂ := J) (H₃ := F) h1 h2
  have hKJ_le_K : ⁅K, J⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hJK
  have hKJ_le_F : ⁅K, J⁆ ≤ F := by
    refine (le_inf hKJ_le_K
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKJF)).trans ?_
    intro x hx
    obtain ⟨hxK, hxC⟩ := hx
    have hxcent : (⟨x, hxK⟩ : ↥K) ∈
        Subgroup.centralizer (CFSG.fittingSubgroup (↥K) : Set ↥K) := by
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.mp hxC (z : G)
        (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
    have hxfit : (⟨x, hxK⟩ : ↥K) ∈ CFSG.fittingSubgroup (↥K) :=
      CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hK hxcent
    exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hxfit, rfl⟩
  have hKJJ : ⁅⁅K, J⁆, J⁆ = ⊥ := by
    have hFJ : ⁅F, J⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hJF
    exact le_bot_iff.mp (hFJ ▸ Subgroup.commutator_mono hKJ_le_F le_rfl)
  have hJKJ : ⁅⁅J, K⁆, J⁆ = ⊥ := by
    rw [Subgroup.commutator_comm J K]
    exact hKJJ
  have hJJK : ⁅⁅J, J⁆, K⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := J) (H₂ := J) (H₃ := K) hJKJ hKJJ
  simpa [hJ] using hJJK

end CFSG.GroupTheory
