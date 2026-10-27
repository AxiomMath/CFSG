module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Rank1
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Levi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Sign

theorem corootDiagF4_neg_one_sign {F : Type} [Field F] (δ : Fin (Tag.rank .F4) → ℤ)
    (i : Fin (Tag.rank .F4)) :
    corootDiagF4 δ (-1 : Fˣ) i = 1 ∨ corootDiagF4 δ (-1 : Fˣ) i = -1 := by
  rcases Int.even_or_odd (iform δ (Pi.single i 1) / 2) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

end Sign

section Roots

theorem eq_or_iform_eq_zero_of_even_F4 {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ)
    (he : Even (iform thetaF4 σ / 2)) : σ = thetaF4 ∨ σ = -thetaF4 ∨ iform thetaF4 σ = 0 := by
  have hb := abs_iform_thetaF4_le σ (mem_rootFinset.2 hσ)
  rw [abs_le] at hb
  obtain ⟨m, hm⟩ := he
  obtain ⟨n, hn⟩ := even_iform_of_long_F4 isRoot_thetaF4 iform_thetaF4_self σ
  have key : ∀ u : Fin (Tag.rank .F4) → ℤ, iform u u = 0 → u = 0 := fun u hu => by
    by_contra h
    have := iform_self_pos h
    omega
  have hσ2 := iform_self_isRoot_F4 hσ
  have hcs := iform_sq_le thetaF4 σ
  rw [iform_thetaF4_self] at hcs
  by_cases h4 : iform thetaF4 σ = 4
  · left
    have hσ4 : iform σ σ = 4 := by
      rcases hσ2 with h | h
      · rw [h4, h] at hcs; norm_num at hcs
      · exact h
    have : iform (σ - thetaF4) (σ - thetaF4) = 0 := by
      simp only [iform_sub_left, iform_sub_right]
      rw [iform_comm σ thetaF4, iform_thetaF4_self]
      omega
    exact sub_eq_zero.1 (key _ this)
  by_cases h3 : iform thetaF4 σ = -4
  · right; left
    have hσ4 : iform σ σ = 4 := by
      rcases hσ2 with h | h
      · rw [h3, h] at hcs; norm_num at hcs
      · exact h
    have : iform (σ + thetaF4) (σ + thetaF4) = 0 := by
      simp only [iform_add_left, iform_add_right]
      rw [iform_comm σ thetaF4, iform_thetaF4_self]
      omega
    have := key _ this
    exact eq_neg_of_add_eq_zero_left this
  · right; right
    omega

end Roots

section Main

variable {F : Type} [Field F]

variable (F) in
def leviMulRank1F4 : Subgroup (ModGL .F4 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .F4 F JF4, ∃ A : SL2 F, x = n * rootSL2 .F4 F thetaF4 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_F4 (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .F4 F thetaF4 A₁ * (n₂ * rootSL2 .F4 F thetaF4 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .F4 F thetaF4 A₁ * n₂) * rootSL2 .F4 F thetaF4 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_F4 hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem toralRootGroup_le_leviMulRank1F4 (hF : ringChar F ≠ 2) :
    toralRootGroup .F4 F (corootDiagF4 thetaF4 (-1 : Fˣ)) ≤ leviMulRank1F4 F := by
  refine sup_le (fun t ht => ⟨t, torusGroup_le_parabolicLevi JF4 ht, 1, by simp⟩) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaF4 σ / 2) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_corootDiagF4 isRoot_thetaF4 iform_thetaF4_self]
    exact hσ1
  have hL := (exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4).1
  rcases eq_or_iform_eq_zero_of_even_F4 hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .F4 F thetaF4 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    have : x ∈ rootRankOneGroup .F4 F thetaF4 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    exact ⟨x, rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_F4 hσr h0) hx, 1, by simp⟩

theorem mem_parabolicLevi_of_commute_rootSL2_F4 (hF : ringChar F ≠ 2) {c : ModGL .F4 F}
    (hcG : c ∈ adjointGroup .F4 F)
    (hc : ∀ A : SL2 F, c * rootSL2 .F4 F thetaF4 A = rootSL2 .F4 F thetaF4 A * c) :
    c ∈ parabolicLevi .F4 F JF4 := by
  have hdθ : rootDiagUnit .F4 (corootDiagF4 thetaF4 (-1 : Fˣ)) =
      rootSL2 .F4 F thetaF4 (HSL (-1)) := (rootTorusSL2_thetaF4 (-1)).symm
  have hcT : c ∈ toralCentralizer .F4 F (corootDiagF4 thetaF4 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨hcG, ?_⟩
    rw [hdθ, mul_inv_eq_iff_eq_mul]
    exact (hc _).symm
  have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inl rfl)) hF
    (corootDiagF4_neg_one_sign thetaF4) hcT
  obtain ⟨n, hn, A, rfl⟩ := toralRootGroup_le_leviMulRank1F4 hF hM
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaF4 (inv_mem hn)
  have hinj : Function.Injective (rootSL2 .F4 F thetaF4) :=
    ((exceptional_Lang_root_rank_one_data .F4 F thetaF4).2.2.2.2.2.2.2.1 hF).1
  have h1 : A * uSL (1 : F) = uSL (l : F) * A := by
    apply hinj
    have h := hc (uSL 1)
    have h' := hu 1
    rw [inv_inv, mul_one] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .F4 F thetaF4 A * rootSL2 .F4 F thetaF4 (uSL 1) =
        n⁻¹ * (n * rootSL2 .F4 F thetaF4 A * rootSL2 .F4 F thetaF4 (uSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .F4 F thetaF4 (uSL 1) * (n * rootSL2 .F4 F thetaF4 A)) := by rw [h]
      _ = _ := by group
  have h2 : A * vSL (1 : F) = vSL (((l⁻¹ : Fˣ)) : F) * A := by
    apply hinj
    have h := hc (vSL 1)
    have h' := hv 1
    rw [inv_inv, mul_one] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .F4 F thetaF4 A * rootSL2 .F4 F thetaF4 (vSL 1) =
        n⁻¹ * (n * rootSL2 .F4 F thetaF4 A * rootSL2 .F4 F thetaF4 (vSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .F4 F thetaF4 (vSL 1) * (n * rootSL2 .F4 F thetaF4 A)) := by rw [h]
      _ = _ := by group
  obtain ⟨a, rfl⟩ := exists_eq_HSL_of_conj_uSL_vSL h1 h2
  have hT := (exceptional_Lang_root_rank_one_torus_transport .F4 F isRoot_thetaF4).2.1 a
  exact mul_mem hn (torusGroup_le_parabolicLevi JF4 hT)

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
