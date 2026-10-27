module

public import CFSG.ClassicalInvolution.ModelFacts.TwistedE6PairRank1

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LeviE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi

section Sign

theorem toralCentralizer_le_toralRootGroup_of_sign_E6 {F : Type} [Field F] (hF : ringChar F ≠ 2)
    {a : Fin (Tag.rank .E6) → Fˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) :
    toralCentralizer .E6 F a ≤ toralRootGroup .E6 F a :=
  toralCentralizer_le_toralRootGroup a fun w hw => by
    rw [kernelReflectionGroup_eq_kernelWeylGroup hF ha,
      ← (sign_character_Weyl_stabilizer_quotients .E6 _).2.2.1 (Or.inr (Or.inr (Or.inl rfl)))]
    exact (mem_rootCharStabilizer_iff hF ha).1 hw

theorem even_of_neg_one_zpow_eq_one_E6 {F : Type} [Field F] (hF : ringChar F ≠ 2) {n : ℤ}
    (h : (-1 : Fˣ) ^ n = 1) : Even n := by
  rcases Int.even_or_odd n with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_zpow] at h
    exact Ring.neg_one_ne_one_of_char_ne_two hF (by simpa using congrArg Units.val h)

theorem neg_one_ne_one_units_E6 {F : Type} [Field F] (hF : ringChar F ≠ 2) : (-1 : Fˣ) ≠ 1 :=
  fun h => Ring.neg_one_ne_one_of_char_ne_two hF (by simpa using congrArg Units.val h)

theorem thetaDiag_neg_one_sign_E6 {F : Type} [Field F] (δ : Fin (Tag.rank .E6) → ℤ)
    (i : Fin (Tag.rank .E6)) :
    thetaDiag δ (-1 : Fˣ) i = 1 ∨ thetaDiag δ (-1 : Fˣ) i = -1 := by
  rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

end Sign

section Roots

theorem eq_or_iform_eq_zero_of_even_E6 {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ)
    (he : Even (iform thetaE6 σ)) : σ = thetaE6 ∨ σ = -thetaE6 ∨ iform thetaE6 σ = 0 := by
  have hb := abs_iform_le_two_E6 isRoot_thetaE6 hσ
  rw [abs_le] at hb
  obtain ⟨m, hm⟩ := he
  have key : ∀ u : Fin (Tag.rank .E6) → ℤ, iform u u = 0 → u = 0 := fun u hu => by
    by_contra h
    have := iform_self_pos h
    omega
  have hθ := iform_self_isRoot_E6 isRoot_thetaE6
  have hσ2 := iform_self_isRoot_E6 hσ
  by_cases h2 : iform thetaE6 σ = 2
  · left
    have : iform (σ - thetaE6) (σ - thetaE6) = 0 := by
      simp only [iform_sub_left, iform_sub_right]
      rw [iform_comm σ thetaE6]
      omega
    exact sub_eq_zero.1 (key _ this)
  by_cases h3 : iform thetaE6 σ = -2
  · right; left
    have : iform (σ + thetaE6) (σ + thetaE6) = 0 := by
      simp only [iform_add_left, iform_add_right]
      rw [iform_comm σ thetaE6]
      omega
    have := key _ this
    exact eq_neg_of_add_eq_zero_left this
  · right; right
    omega

end Roots

section Main

variable {F : Type} [Field F]

variable (F) in
def leviMulRank1 : Subgroup (ModGL .E6 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .E6 F JE6, ∃ A : SL2 F, x = n * rootSL2 .E6 F thetaE6 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E6 (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .E6 F thetaE6 A₁ * (n₂ * rootSL2 .E6 F thetaE6 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .E6 F thetaE6 A₁ * n₂) * rootSL2 .E6 F thetaE6 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E6 hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem toralRootGroup_le_leviMulRank1 (hF : ringChar F ≠ 2) :
    toralRootGroup .E6 F (thetaDiag thetaE6 (-1 : Fˣ)) ≤ leviMulRank1 F := by
  refine sup_le (fun t ht => ⟨t, torusGroup_le_parabolicLevi JE6 ht, 1, by simp⟩) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaE6 σ) := by
    refine even_of_neg_one_zpow_eq_one_E6 hF ?_
    rw [← rootChar_thetaDiag]
    exact hσ1
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E6 F isRoot_thetaE6).1
  rcases eq_or_iform_eq_zero_of_even_E6 hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .E6 F thetaE6 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    have : x ∈ rootRankOneGroup .E6 F thetaE6 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    exact ⟨x, rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_E6 hσr h0) hx, 1, by simp⟩

theorem mem_parabolicLevi_of_commute_rootSL2_E6 (hF : ringChar F ≠ 2) {c : ModGL .E6 F}
    (hcG : c ∈ adjointGroup .E6 F)
    (hu : c * rootSL2 .E6 F thetaE6 (uSL 1) = rootSL2 .E6 F thetaE6 (uSL 1) * c)
    (hv : c * rootSL2 .E6 F thetaE6 (vSL 1) = rootSL2 .E6 F thetaE6 (vSL 1) * c) :
    c ∈ parabolicLevi .E6 F JE6 := by
  have hdθ : rootDiagUnit .E6 (thetaDiag thetaE6 (-1 : Fˣ)) =
      rootSL2 .E6 F thetaE6 (HSL (-1)) := (rootTorusSL2_thetaE6 (-1)).symm
  have hcw : c * rootSL2 .E6 F thetaE6 (HSL (-1)) = rootSL2 .E6 F thetaE6 (HSL (-1)) * c := by
    rw [HSL_neg_one_eq_sq, vSL_neg_one, map_pow, map_mul, map_mul, map_inv]
    have h1 : Commute c (rootSL2 .E6 F thetaE6 (uSL 1)) := hu
    have h2 : Commute c (rootSL2 .E6 F thetaE6 (vSL 1)) := hv
    exact (((h1.mul_right h2.inv_right).mul_right h1).pow_right 2).eq
  have hcT : c ∈ toralCentralizer .E6 F (thetaDiag thetaE6 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨hcG, ?_⟩
    rw [hdθ, mul_inv_eq_iff_eq_mul]
    exact hcw.symm
  have hM := toralCentralizer_le_toralRootGroup_of_sign_E6 hF (thetaDiag_neg_one_sign_E6 thetaE6)
    hcT
  obtain ⟨n, hn, A, rfl⟩ := toralRootGroup_le_leviMulRank1 hF hM
  obtain ⟨l, hu', hv'⟩ := exists_levi_conj_rootSL2_thetaE6 (inv_mem hn)
  have hinj : Function.Injective (rootSL2 .E6 F thetaE6) :=
    ((exceptional_Lang_root_rank_one_data .E6 F thetaE6).2.2.2.2.2.2.2.1 hF).1
  have h1 : A * uSL (1 : F) = uSL ((l : F) * 1) * A := by
    apply hinj
    have h' := hu' 1
    rw [inv_inv] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .E6 F thetaE6 A * rootSL2 .E6 F thetaE6 (uSL 1) =
        n⁻¹ * (n * rootSL2 .E6 F thetaE6 A * rootSL2 .E6 F thetaE6 (uSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .E6 F thetaE6 (uSL 1) * (n * rootSL2 .E6 F thetaE6 A)) := by rw [hu]
      _ = _ := by group
  have h2 : A * vSL (1 : F) = vSL (((l⁻¹ : Fˣ) : F) * 1) * A := by
    apply hinj
    have h' := hv' 1
    rw [inv_inv] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .E6 F thetaE6 A * rootSL2 .E6 F thetaE6 (vSL 1) =
        n⁻¹ * (n * rootSL2 .E6 F thetaE6 A * rootSL2 .E6 F thetaE6 (vSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .E6 F thetaE6 (vSL 1) * (n * rootSL2 .E6 F thetaE6 A)) := by rw [hv]
      _ = _ := by group
  obtain ⟨a, rfl⟩ := exists_eq_HSL_of_conj_uSL_vSL_gen one_ne_zero one_ne_zero h1 h2
  have hT := (exceptional_Lang_root_rank_one_torus_transport .E6 F isRoot_thetaE6).2.1 a
  exact mul_mem hn (torusGroup_le_parabolicLevi JE6 hT)

end Main

end CFSG.ClassicalInvolution.ModelFacts.LeviE6
