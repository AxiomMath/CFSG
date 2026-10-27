module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section InvolutionTop

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}

theorem rootGroup_sup_centralizer_invol (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (hq : 2 < p ^ f) :
    rootGroup J hJ ⊔
        Subgroup.centralizer ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = ⊤ := by
  refine top_unique ?_
  rw [← closure_rootGroup_weyl_eq_top J hJ (p ^ f) hK hfix hq, Subgroup.closure_le]
  refine Set.union_subset (fun x hx => Subgroup.mem_sup_left hx) ?_
  rw [Set.singleton_subset_iff]
  exact Subgroup.mem_sup_right (weyl_mem_centralizer_invol J hJ)

end InvolutionTop

theorem exists_involution_sup_eq_top_of_lieModel {L : Type} [Group L] [Finite L] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hL : CFSG.Blueprint.LieModel L .PSU 3 p f) (U : Sylow p L) :
    ∃ j ∈ Subgroup.normalizer ((U : Subgroup L) : Set L), orderOf j = 2 ∧
      CFSG.Open.IsElemAbelian p ((U : Subgroup L) ⊓ Subgroup.centralizer ({j} : Set L)) ∧
      Nat.card ((U : Subgroup L) ⊓ Subgroup.centralizer ({j} : Set L) : Subgroup L) = p ^ f ∧
      (U : Subgroup L) ⊔ Subgroup.centralizer ({j} : Set L) = ⊤ := by
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    exists_equiv_psu (hL.statedClassicalModel (by decide))
  have : CharP K p := charP_of_card Fact.out hK
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hC : (Subgroup.centralizer ({e'.symm (invol J hJ)} : Set L)).map e'.toMonoidHom =
      Subgroup.centralizer ({invol J hJ} : Set _) := by
    rw [map_centralizer_singleton, MulEquiv.apply_symm_apply]
  have hinf : ((U : Subgroup L) ⊓ Subgroup.centralizer ({e'.symm (invol J hJ)} : Set L)).map
      e'.toMonoidHom = rootGroup J hJ ⊓ Subgroup.centralizer ({invol J hJ} : Set _) := by
    rw [Subgroup.map_inf _ _ e'.toMonoidHom e'.injective, hU, hC]
  refine ⟨e'.symm (invol J hJ), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mem_map_iff e', hN, MulEquiv.apply_symm_apply]
    exact invol_mem_normalizer J hJ
  · rw [MulEquiv.orderOf_eq]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact invol_mul_self J hJ) (invol_ne_one J hJ h2)
  · rw [← isElemAbelian_map_iff e', hinf]
    exact isElemAbelian_inf_centralizer_invol J hJ hK hfix Fact.out hp2 h2
  · rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hinf]
    exact card_inf_centralizer_invol J hJ hK hfix h2
  · apply Subgroup.map_injective (f := e'.toMonoidHom) e'.injective
    rw [Subgroup.map_sup, hU, hC, Subgroup.map_top_of_surjective _ e'.surjective]
    exact rootGroup_sup_centralizer_invol J hJ hK hfix hq

end CFSG.AGLEmbedding.UnitaryModel
