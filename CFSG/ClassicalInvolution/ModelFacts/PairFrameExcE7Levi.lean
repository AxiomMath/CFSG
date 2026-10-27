module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Rank1
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Levi

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.RootSystem RootSpace

section Sign

theorem toralCentralizer_le_toralRootGroup_thetaE7 {F : Type} [Field F] (hF : ringChar F ≠ 2) :
    toralCentralizer .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) ≤
      toralRootGroup .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) := by
  refine toralCentralizer_le_toralRootGroup _ fun w hw => ?_
  have hev : ∀ j : Fin (Tag.rank .E7),
      Even (iform (w⁻¹ • thetaE7 - thetaE7) (Pi.single j 1)) := by
    intro j
    have h := hw (Pi.single j 1)
    rw [rootChar_thetaDiag, rootChar_thetaDiag] at h
    have h2 : iform thetaE7 (w • Pi.single j 1) = iform (w⁻¹ • thetaE7) (Pi.single j 1) := by
      rw [← iform_smul_smul w⁻¹ thetaE7 (w • Pi.single j 1), inv_smul_smul]
    rw [iform_sub_left, ← h2]
    have h3 : (-1 : Fˣ) ^ (iform thetaE7 (w • Pi.single j 1) -
        iform thetaE7 (Pi.single j 1)) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    exact even_of_neg_one_zpow_eq_one hF h3
  have hρ : w⁻¹ • thetaE7 = thetaE7 ∨ w⁻¹ • thetaE7 = -thetaE7 :=
    twinFree_E7 (IsRoot.smul isRoot_thetaE7 w⁻¹) isRoot_thetaE7 hev
  have hker : ∀ σ, IsRoot .E7 σ → iform σ thetaE7 = 0 →
      rootReflection σ ∈ kernelReflectionGroup (thetaDiag thetaE7 (-1 : Fˣ)) := fun σ hσ h0 =>
    rootReflection_mem_kernelReflectionGroup ⟨hσ, by
      rw [rootChar_thetaDiag, iform_comm, h0]; simp⟩
  have hstab : ∀ u : WeylGroup .E7, u • thetaE7 = thetaE7 →
      u ∈ kernelReflectionGroup (thetaDiag thetaE7 (-1 : Fˣ)) := by
    intro u hu
    set v : RootSpace .E7 := ofLattice thetaE7 with hv
    have hstab : u ∈ weylStabilizer .E7 v := by
      change weylAct .E7 u v = v
      rw [hv, weylAct_ofLattice, hu]
    rw [(exceptional_Lang_Weyl_chamber_point_stabilizers .E7).2.2.2.2.2 v] at hstab
    have hle : Subgroup.closure {s | ∃ α, IsRoot .E7 α ∧ inner ℝ (ofLattice α) v = 0 ∧
        s = rootReflection α} ≤ kernelReflectionGroup (thetaDiag thetaE7 (-1 : Fˣ)) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨σ, hσ, hinner, rfl⟩
      obtain ⟨cc, hcc, hform⟩ := exists_inner_ofLattice_eq_iform .E7
      rw [hv, hform] at hinner
      have h1 : (iform σ thetaE7 : ℝ) = 0 := by
        have : cc * (iform σ thetaE7 : ℝ) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hcc.ne'
        · exact h
      exact hker σ hσ (by exact_mod_cast h1)
    exact hle hstab
  have hsθ : rootReflection thetaE7 ∈ kernelReflectionGroup (thetaDiag thetaE7 (-1 : Fˣ)) :=
    rootReflection_mem_kernelReflectionGroup ⟨isRoot_thetaE7, by
      rw [rootChar_thetaDiag, iform_self_isRoot_E7 isRoot_thetaE7]; simp⟩
  rcases hρ with h | h
  · refine hstab w ?_
    calc w • thetaE7 = w • (w⁻¹ • thetaE7) := by rw [h]
      _ = thetaE7 := smul_inv_smul w _
  · have h1 : w • thetaE7 = -thetaE7 := by
      have : w • (w⁻¹ • thetaE7) = w • (-thetaE7) := by rw [h]
      rw [smul_inv_smul, smul_neg] at this
      exact (neg_eq_iff_eq_neg.1 this.symm).symm ▸ rfl
    have h2 : (rootReflection thetaE7 * w) • thetaE7 = thetaE7 := by
      rw [mul_smul, h1, smul_neg, rootReflection_smul_self isRoot_thetaE7, neg_neg]
    have h3 := hstab _ h2
    have : w = rootReflection thetaE7 * (rootReflection thetaE7 * w) := by
      rw [← mul_assoc, rootReflection_mul_self isRoot_thetaE7, one_mul]
    rw [this]
    exact mul_mem hsθ h3

theorem thetaDiag_neg_one_sign_E7 {F : Type} [Field F] (δ : Fin (Tag.rank .E7) → ℤ)
    (i : Fin (Tag.rank .E7)) :
    thetaDiag δ (-1 : Fˣ) i = 1 ∨ thetaDiag δ (-1 : Fˣ) i = -1 := by
  rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

end Sign

section Roots

theorem eq_or_iform_eq_zero_of_even_E7 {σ : Fin (Tag.rank .E7) → ℤ} (hσ : IsRoot .E7 σ)
    (he : Even (iform thetaE7 σ)) : σ = thetaE7 ∨ σ = -thetaE7 ∨ iform thetaE7 σ = 0 := by
  have hb := abs_iform_le_two_E7 isRoot_thetaE7 hσ
  rw [abs_le] at hb
  obtain ⟨m, hm⟩ := he
  have key : ∀ u : Fin (Tag.rank .E7) → ℤ, iform u u = 0 → u = 0 := fun u hu => by
    by_contra h
    have := iform_self_pos h
    omega
  have hθ := iform_self_isRoot_E7 isRoot_thetaE7
  have hσ2 := iform_self_isRoot_E7 hσ
  by_cases h2 : iform thetaE7 σ = 2
  · left
    have : iform (σ - thetaE7) (σ - thetaE7) = 0 := by
      simp only [iform_sub_left, iform_sub_right]
      rw [iform_comm σ thetaE7]
      omega
    exact sub_eq_zero.1 (key _ this)
  by_cases h3 : iform thetaE7 σ = -2
  · right; left
    have : iform (σ + thetaE7) (σ + thetaE7) = 0 := by
      simp only [iform_add_left, iform_add_right]
      rw [iform_comm σ thetaE7]
      omega
    have := key _ this
    exact eq_neg_of_add_eq_zero_left this
  · right; right
    omega

end Roots

section Main

variable {F : Type} [Field F]

variable (F) in
def leviMulRank1E7 : Subgroup (ModGL .E7 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .E7 F JE7, ∃ A : SL2 F, x = n * rootSL2 .E7 F thetaE7 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E7 (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .E7 F thetaE7 A₁ * (n₂ * rootSL2 .E7 F thetaE7 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .E7 F thetaE7 A₁ * n₂) * rootSL2 .E7 F thetaE7 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_E7 hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem toralRootGroup_le_leviMulRank1E7 (hF : ringChar F ≠ 2) :
    toralRootGroup .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) ≤ leviMulRank1E7 F := by
  refine sup_le (fun t ht => ⟨t, torusGroup_le_parabolicLevi JE7 ht, 1, by simp⟩) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaE7 σ) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_thetaDiag]
    exact hσ1
  obtain ⟨-, -, -, -, -, -, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport .E7 F
    isRoot_thetaE7
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E7 F isRoot_thetaE7).1
  rcases eq_or_iform_eq_zero_of_even_E7 hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .E7 F thetaE7 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    have : x ∈ rootRankOneGroup .E7 F thetaE7 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    exact ⟨x, rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_E7 hσr h0) hx, 1, by simp⟩

theorem mem_parabolicLevi_of_commute_rootSL2_E7 (hF : ringChar F ≠ 2) {c : ModGL .E7 F}
    (hcG : c ∈ adjointGroup .E7 F)
    (hc : ∀ A : SL2 F, c * rootSL2 .E7 F thetaE7 A = rootSL2 .E7 F thetaE7 A * c) :
    c ∈ parabolicLevi .E7 F JE7 := by
  have hdθ : rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootSL2 .E7 F thetaE7 (HSL (-1)) := (rootTorusSL2_thetaE7 (-1)).symm
  have hcT : c ∈ toralCentralizer .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨hcG, ?_⟩
    rw [hdθ, mul_inv_eq_iff_eq_mul]
    exact (hc _).symm
  have hM := toralCentralizer_le_toralRootGroup_thetaE7 hF hcT
  obtain ⟨n, hn, A, rfl⟩ := toralRootGroup_le_leviMulRank1E7 hF hM
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE7 (inv_mem hn)
  have hinj : Function.Injective (rootSL2 .E7 F thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 F thetaE7).2.2.2.2.2.2.2.1 hF).1
  have h1 : A * uSL (1 : F) = uSL (l : F) * A := by
    apply hinj
    have h := hc (uSL 1)
    have h' := hu 1
    rw [inv_inv, mul_one] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .E7 F thetaE7 A * rootSL2 .E7 F thetaE7 (uSL 1) =
        n⁻¹ * (n * rootSL2 .E7 F thetaE7 A * rootSL2 .E7 F thetaE7 (uSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .E7 F thetaE7 (uSL 1) * (n * rootSL2 .E7 F thetaE7 A)) := by rw [h]
      _ = _ := by group
  have h2 : A * vSL (1 : F) = vSL (((l⁻¹ : Fˣ)) : F) * A := by
    apply hinj
    have h := hc (vSL 1)
    have h' := hv 1
    rw [inv_inv, mul_one] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .E7 F thetaE7 A * rootSL2 .E7 F thetaE7 (vSL 1) =
        n⁻¹ * (n * rootSL2 .E7 F thetaE7 A * rootSL2 .E7 F thetaE7 (vSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .E7 F thetaE7 (vSL 1) * (n * rootSL2 .E7 F thetaE7 A)) := by rw [h]
      _ = _ := by group
  obtain ⟨a, rfl⟩ := exists_eq_HSL_of_conj_uSL_vSL h1 h2
  have hT := (exceptional_Lang_root_rank_one_torus_transport .E7 F isRoot_thetaE7).2.1 a
  exact mul_mem hn (torusGroup_le_parabolicLevi JE7 hT)

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
