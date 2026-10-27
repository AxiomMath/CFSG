module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F3E1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F4Cl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F8G

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem sec8t84g_isPGroup_of_sq {g : G} (hg : g * g = 1) : IsPGroup 2 ↥(zpowers g) := by
  have h2 : g ^ 2 = 1 := by rw [pow_two]; exact hg
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

theorem sec8t84g_map_conj_mul (g h : G) (X : Subgroup G) :
    X.map (MulAut.conj (g * h)).toMonoidHom =
      (X.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem sec8t84g_map_E8 {T A : Subgroup G} {δ : G} (hδ : δ ∈ normalizer (T : Set G))
    (hA : A ≤ T) (h8 : IsElemAb2 A 8) :
    A.map (MulAut.conj δ).toMonoidHom ≤ T ∧ IsElemAb2 (A.map (MulAut.conj δ).toMonoidHom) 8 := by
  have hδmap : T.map (MulAut.conj δ).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hδ
  refine ⟨?_, h8.1.map (MulAut.conj δ).toMonoidHom, ?_⟩
  · rw [← hδmap]
    exact Subgroup.map_mono hA
  · rw [Subgroup.card_map_of_injective (MulAut.conj δ).injective, h8.2]

section TData

variable {t : G} {E T T1 T2 V1 V2 F1 F2 : Subgroup G}

theorem sec8t84g_perm_E12 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) (hE8 : IsElemAb2 E 8)
    (hT : IsSylow2Of T (normalizer (E : Set G))) {γ : G} (hγ : γ ∈ normalizer (T : Set G))
    (hγ2 : IsPGroup 2 ↥(zpowers γ)) (hγT : γ ∉ T) :
    ((V1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F2 ∧
        (F1 ⊔ V2).map (MulAut.conj γ).toMonoidHom = F1 ⊔ V2) ∨
      ((V1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = F1 ⊔ V2 ∧
        (F1 ⊔ V2).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F2) := by
  obtain ⟨hEγ, hE0γ⟩ := sec8t84_gamma_swaps D hE8 hT hγ hγ2 hγT
  obtain ⟨hdEA, hdEB, hdE0A, hdE0B, hdAB⟩ := sec8t84_four_distinct D
  have hinj : Function.Injective (Subgroup.map (MulAut.conj γ).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj γ).injective
  have hA : (V1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F2 ∨
      (V1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = F1 ⊔ V2 := by
    obtain ⟨hAT, hA8⟩ := sec8t84g_map_E8 hγ (sec8t84_VF2_le_T D) (sec8t84_VF2_isElemAb2 D)
    rcases sec8t84_classify_E8 D hAT hA8 with h | h | h | h
    · exact absurd (hinj (h.trans hE0γ.symm)) hdE0A.symm
    · exact absurd (hinj (h.trans hEγ.symm)) hdEA.symm
    · exact Or.inl h
    · exact Or.inr h
  have hB : (F1 ⊔ V2).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F2 ∨
      (F1 ⊔ V2).map (MulAut.conj γ).toMonoidHom = F1 ⊔ V2 := by
    obtain ⟨hBT, hB8⟩ := sec8t84g_map_E8 hγ (sec8t84_FV2_le_T D) (sec8t84_FV2_isElemAb2 D)
    rcases sec8t84_classify_E8 D hBT hB8 with h | h | h | h
    · exact absurd (hinj (h.trans hE0γ.symm)) hdE0B.symm
    · exact absurd (hinj (h.trans hEγ.symm)) hdEB.symm
    · exact Or.inl h
    · exact Or.inr h
  rcases hA with hA | hA
  · refine Or.inl ⟨hA, ?_⟩
    rcases hB with hB | hB
    · exact absurd (hinj (hB.trans hA.symm)) hdAB.symm
    · exact hB
  · refine Or.inr ⟨hA, ?_⟩
    rcases hB with hB | hB
    · exact hB
    · exact absurd (hinj (hB.trans hA.symm)) hdAB.symm

theorem sec8t84g_gamma_sq_eq_one (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2)
    (hE8 : IsElemAb2 E 8) (hT : IsSylow2Of T (normalizer (E : Set G))) {γ : G}
    (hγ : γ ∈ normalizer (T : Set G)) (hγ2 : IsPGroup 2 ↥(zpowers γ)) (hγT : γ ∉ T)
    (hsq : γ * γ ∈ zpowers t) : γ * γ = 1 := by
  by_contra hne
  have hγγ : γ * γ = t := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hsq
    have ht2 : t ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      exact D.t_sq
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
    · exact absurd (by rw [← hn, hk, zpow_mul, ht2, one_zpow]) hne
    · rw [← hn, hk, zpow_add_one, zpow_mul, ht2, one_zpow, one_mul]
  have hsqmap : ∀ X : Subgroup G, (X.map (MulAut.conj γ).toMonoidHom).map
      (MulAut.conj γ).toMonoidHom = X.map (MulAut.conj t).toMonoidHom := by
    intro X
    rw [← sec8t84g_map_conj_mul, hγγ]
  have h1 := sec8t84_VF2_conj D
  have hAB := (sec8t84_four_distinct D).2.2.2.2
  rcases sec8t84g_perm_E12 D hE8 hT hγ hγ2 hγT with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · apply hAB
    rw [← h1, ← hsqmap, hA, hA]
  · apply hAB
    rw [← h1, ← hsqmap, hA, hB]

theorem sec8t84g_gamma_fp (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) (hE8 : IsElemAb2 E 8)
    (hT : IsSylow2Of T (normalizer (E : Set G))) {γ : G} (hγ : γ ∈ normalizer (T : Set G))
    (hγ2 : IsPGroup 2 ↥(zpowers γ)) (hγT : γ ∉ T) (hsq : γ * γ ∈ zpowers t)
    (hcomm : γ * t = t * γ) :
    ∃ γ' : G, (γ' = γ ∨ γ' = γ * t) ∧ γ' ∈ normalizer (T : Set G) ∧ γ' ∉ T ∧ γ' * γ' = 1 ∧
      γ' * t = t * γ' ∧
      E.map (MulAut.conj γ').toMonoidHom = F1 ⊔ F2 ∧
      (F1 ⊔ F2).map (MulAut.conj γ').toMonoidHom = E ∧
      (V1 ⊔ F2).map (MulAut.conj γ').toMonoidHom = F1 ⊔ V2 ∧
      (F1 ⊔ V2).map (MulAut.conj γ').toMonoidHom = V1 ⊔ F2 := by
  have htT : t ∈ T := by
    have : t ∈ zpowers t ⊔ (T1 ⊔ T2) := (le_sup_left : zpowers t ≤ _) (mem_zpowers t)
    rwa [← D.T_eq] at this
  have hsq1 : γ * γ = 1 := sec8t84g_gamma_sq_eq_one D hE8 hT hγ hγ2 hγT hsq
  rcases sec8t84g_perm_E12 D hE8 hT hγ hγ2 hγT with ⟨hA, hB⟩ | ⟨hA, hB⟩
  ·
    have hγt : γ * t ∈ normalizer (T : Set G) := mul_mem hγ (le_normalizer htT)
    have hγtT : γ * t ∉ T := fun h => hγT (by simpa using mul_mem h (inv_mem htT))
    have hγt2 : (γ * t) * (γ * t) = 1 := by
      calc (γ * t) * (γ * t) = γ * (t * γ) * t := by simp only [mul_assoc]
        _ = γ * (γ * t) * t := by rw [hcomm]
        _ = (γ * γ) * (t * t) := by simp only [mul_assoc]
        _ = 1 := by rw [hsq1, D.t_sq, mul_one]
    obtain ⟨h1, h2⟩ := sec8t84_gamma_swaps D hE8 hT hγt (sec8t84g_isPGroup_of_sq hγt2) hγtT
    refine ⟨γ * t, Or.inr rfl, hγt, hγtT, hγt2, ?_, h1, h2, ?_, ?_⟩
    · rw [← mul_assoc, ← hcomm]
    · rw [sec8t84g_map_conj_mul, sec8t84_VF2_conj D, hB]
    · rw [sec8t84g_map_conj_mul, sec8t84_FV2_conj D, hA]
  ·
    obtain ⟨h1, h2⟩ := sec8t84_gamma_swaps D hE8 hT hγ hγ2 hγT
    exact ⟨γ, Or.inl rfl, hγ, hγT, hsq1, hcomm, h1, h2, hA, hB⟩

end TData

end CFSG.OddStandard.SmallF3.Omega
