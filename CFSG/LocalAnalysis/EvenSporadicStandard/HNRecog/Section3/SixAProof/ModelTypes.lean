module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ModelTheta

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open Equiv Equiv.Perm

private theorem sixA_sigma_mul_sigma_mul (w : Sym 7) : sixASigma * (sixASigma * w) = w := by
  rw [← mul_assoc, sixA_sigma_mul_self, one_mul]

private theorem sixA_ext_sq (ρ : Sym 5) (hρ : ρ ^ 2 = 1) : (sixAExt ρ) ^ 2 = 1 := by
  rw [← map_pow, hρ, map_one]

private theorem sixA_sigma_ext_sq (ρ : Sym 5) (hρ : ρ ^ 2 = 1) :
    (sixASigma * sixAExt ρ) ^ 2 = 1 := by
  rw [(sixAExt_disjoint ρ).commute.mul_pow 2, pow_two, sixA_sigma_mul_self, one_mul,
    sixA_ext_sq ρ hρ]

private theorem sixA_swap_nodup : [(0 : Fin 5), 1, 2, 3].Nodup := by decide

private theorem sixA_swap_cycleType : (Equiv.swap (0 : Fin 5) 1).cycleType = {2} :=
  Equiv.Perm.isSwap_iff_cycleType.1 ⟨0, 1, by decide, rfl⟩

private theorem sixA_swap_mul_cycleType :
    (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3).cycleType = {2, 2} :=
  Equiv.Perm.cycleType_swap_mul_swap_of_nodup sixA_swap_nodup

private theorem sixA_swap_sq : (Equiv.swap (0 : Fin 5) 1) ^ 2 = 1 := by
  rw [pow_two, Equiv.swap_mul_self]

private theorem sixA_swap_mul_sq :
    (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3) ^ 2 = 1 := by
  rw [(disjoint_swap_swap sixA_swap_nodup).commute.mul_pow 2, pow_two, pow_two,
    Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]

theorem sixA_model_cover {s : Sym 7}
    (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7))) (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1)
    (hsσ : s ≠ sixASigma) : sixAIsA s ∨ sixAIsB s ∨ sixAIsC s ∨ sixAIsD s := by
  obtain ⟨ρ, hρ | hρ⟩ := sixA_coord hs
  · subst hρ
    have hρ2 : ρ ^ 2 = 1 := by
      apply sixAExt_injective
      rw [map_pow, hs2, map_one]
    have hρ1 : ρ ≠ 1 := by
      intro h
      exact hs1 (by rw [h, map_one])
    rcases sixA_sym5_inv hρ2 hρ1 with h | h
    · refine Or.inl ⟨?_, ?_⟩
      · rw [sixA_cycleType_ext, h]
      · rw [sixA_cycleType_sigma_mul_ext, h]; rfl
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · rw [sixA_cycleType_ext, h]
      · rw [sixA_cycleType_sigma_mul_ext, h]; rfl
  · subst hρ
    have hsq : (sixAExt ρ) ^ 2 = 1 := by
      have h := hs2
      rw [(sixAExt_disjoint ρ).commute.mul_pow 2, pow_two, sixA_sigma_mul_self,
        one_mul] at h
      exact h
    have hρ2 : ρ ^ 2 = 1 := by
      apply sixAExt_injective
      rw [map_pow, hsq, map_one]
    have hρ1 : ρ ≠ 1 := by
      intro h
      exact hsσ (by rw [h, map_one, mul_one])
    rcases sixA_sym5_inv hρ2 hρ1 with h | h
    · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
      · rw [sixA_cycleType_sigma_mul_ext, h]; rfl
      · rw [sixA_sigma_mul_sigma_mul, sixA_cycleType_ext, h]
    · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
      · rw [sixA_cycleType_sigma_mul_ext, h]; rfl
      · rw [sixA_sigma_mul_sigma_mul, sixA_cycleType_ext, h]

theorem sixA_model_conj {s t : Sym 7}
    (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)))
    (ht : t ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)))
    (h1 : s.cycleType = t.cycleType) (h2 : (sixASigma * s).cycleType = (sixASigma * t).cycleType) :
    ∃ κ ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)), κ * s * κ⁻¹ = t := by
  obtain ⟨ρ, hρ | hρ⟩ := sixA_coord hs
  · obtain ⟨ρ', hρ' | hρ'⟩ := sixA_coord ht
    · subst hρ; subst hρ'
      rw [sixA_cycleType_ext, sixA_cycleType_ext] at h1
      have hconj : IsConj ρ ρ' := by
        rw [isConj_iff_cycleType_eq]
        exact h1
      obtain ⟨π, hπ⟩ := isConj_iff.1 hconj
      refine ⟨sixAExt π, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((sixAExt_disjoint π).commute).eq.symm
      · rw [← map_mul, ← map_inv, ← map_mul, hπ]
    · subst hρ; subst hρ'
      rw [sixA_cycleType_ext, sixA_cycleType_sigma_mul_ext] at h1
      rw [sixA_cycleType_sigma_mul_ext, sixA_sigma_mul_sigma_mul, sixA_cycleType_ext] at h2
      exfalso
      have e1 := congrArg Multiset.card h1
      have e2 := congrArg Multiset.card h2
      simp only [Multiset.card_add, Multiset.card_singleton] at e1 e2
      omega
  · obtain ⟨ρ', hρ' | hρ'⟩ := sixA_coord ht
    · subst hρ; subst hρ'
      rw [sixA_cycleType_sigma_mul_ext, sixA_cycleType_ext] at h1
      rw [sixA_sigma_mul_sigma_mul, sixA_cycleType_ext, sixA_cycleType_sigma_mul_ext] at h2
      exfalso
      have e1 := congrArg Multiset.card h1
      have e2 := congrArg Multiset.card h2
      simp only [Multiset.card_add, Multiset.card_singleton] at e1 e2
      omega
    · subst hρ; subst hρ'
      rw [sixA_sigma_mul_sigma_mul, sixA_sigma_mul_sigma_mul, sixA_cycleType_ext,
        sixA_cycleType_ext] at h2
      have hconj : IsConj ρ ρ' := by
        rw [isConj_iff_cycleType_eq]
        exact h2
      obtain ⟨π, hπ⟩ := isConj_iff.1 hconj
      refine ⟨sixAExt π, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((sixAExt_disjoint π).commute).eq.symm
      · have hκ : sixAExt π * sixASigma = sixASigma * sixAExt π :=
          ((sixAExt_disjoint π).commute).eq.symm
        calc sixAExt π * (sixASigma * sixAExt ρ) * (sixAExt π)⁻¹
            = sixAExt π * sixASigma * sixAExt ρ * (sixAExt π)⁻¹ := by
                rw [← mul_assoc (sixAExt π) sixASigma (sixAExt ρ)]
          _ = sixASigma * sixAExt π * sixAExt ρ * (sixAExt π)⁻¹ := by rw [hκ]
          _ = sixASigma * (sixAExt π * sixAExt ρ * (sixAExt π)⁻¹) := by
                simp only [mul_assoc]
          _ = sixASigma * sixAExt ρ' := by
                rw [← map_mul, ← map_inv, ← map_mul, hπ]

theorem sixA_model_exists_A :
    ∃ s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)), s ^ 2 = 1 ∧ sixAIsA s := by
  refine ⟨sixAExt (Equiv.swap (0 : Fin 5) 1), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((sixAExt_disjoint (Equiv.swap (0 : Fin 5) 1)).commute).eq.symm
  · exact sixA_ext_sq _ sixA_swap_sq
  · exact ⟨by rw [sixA_cycleType_ext, sixA_swap_cycleType],
      by rw [sixA_cycleType_sigma_mul_ext, sixA_swap_cycleType]; rfl⟩

theorem sixA_model_exists_B :
    ∃ s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)), s ^ 2 = 1 ∧ sixAIsB s := by
  refine ⟨sixAExt (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((sixAExt_disjoint _).commute).eq.symm
  · exact sixA_ext_sq _ sixA_swap_mul_sq
  · exact ⟨by rw [sixA_cycleType_ext, sixA_swap_mul_cycleType],
      by rw [sixA_cycleType_sigma_mul_ext, sixA_swap_mul_cycleType]; rfl⟩

theorem sixA_model_exists_C :
    ∃ s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)), s ^ 2 = 1 ∧ sixAIsC s := by
  refine ⟨sixASigma * sixAExt (Equiv.swap (0 : Fin 5) 1), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_assoc, ((sixAExt_disjoint _).commute).eq.symm]
  · exact sixA_sigma_ext_sq _ sixA_swap_sq
  · refine ⟨?_, ?_⟩
    · rw [sixA_cycleType_sigma_mul_ext, sixA_swap_cycleType]; rfl
    · rw [sixA_sigma_mul_sigma_mul, sixA_cycleType_ext, sixA_swap_cycleType]

theorem sixA_model_exists_D :
    ∃ s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)), s ^ 2 = 1 ∧ sixAIsD s := by
  refine ⟨sixASigma * sixAExt (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3), ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    rw [mul_assoc, ((sixAExt_disjoint _).commute).eq.symm]
  · exact sixA_sigma_ext_sq _ sixA_swap_mul_sq
  · refine ⟨?_, ?_⟩
    · rw [sixA_cycleType_sigma_mul_ext, sixA_swap_mul_cycleType]; rfl
    · rw [sixA_sigma_mul_sigma_mul, sixA_cycleType_ext, sixA_swap_mul_cycleType]

theorem sixAIsC_of_isA {s : Sym 7} (h : sixAIsA s) : sixAIsC (sixASigma * s) := by
  refine ⟨h.2, ?_⟩
  rw [sixA_sigma_mul_sigma_mul]
  exact h.1

theorem sixAIsD_of_isB {s : Sym 7} (h : sixAIsB s) : sixAIsD (sixASigma * s) := by
  refine ⟨h.2, ?_⟩
  rw [sixA_sigma_mul_sigma_mul]
  exact h.1

end CFSG.EvenSporadicStandard.HNRecog.Section3
