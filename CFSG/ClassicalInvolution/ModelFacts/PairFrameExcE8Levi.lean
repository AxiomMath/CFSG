module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Sign

theorem toralCentralizer_le_toralRootGroup_of_sign {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {F : Type} [Field F] (hF : ringChar F ≠ 2)
    {a : Fin τ.rank → Fˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) :
    toralCentralizer τ F a ≤ toralRootGroup τ F a :=
  toralCentralizer_le_toralRootGroup a fun w hw => by
    rw [kernelReflectionGroup_eq_kernelWeylGroup hF ha,
      ← (sign_character_Weyl_stabilizer_quotients τ _).2.2.1 hτ]
    exact (mem_rootCharStabilizer_iff hF ha).1 hw

theorem even_of_neg_one_zpow_eq_one {F : Type} [Field F] (hF : ringChar F ≠ 2) {n : ℤ}
    (h : (-1 : Fˣ) ^ n = 1) : Even n := by
  rcases Int.even_or_odd n with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_zpow] at h
    exact Ring.neg_one_ne_one_of_char_ne_two hF (by simpa using congrArg Units.val h)

theorem neg_one_ne_one_units_of_ringChar {F : Type} [Field F] (hF : ringChar F ≠ 2) : (-1 : Fˣ) ≠ 1 :=
  fun h => Ring.neg_one_ne_one_of_char_ne_two hF (by simpa using congrArg Units.val h)

theorem thetaDiag_neg_one_sign {F : Type} [Field F] (δ : Fin (Tag.rank .E8) → ℤ)
    (i : Fin (Tag.rank .E8)) :
    thetaDiag δ (-1 : Fˣ) i = 1 ∨ thetaDiag δ (-1 : Fˣ) i = -1 := by
  rcases Int.even_or_odd (iform δ (Pi.single i 1)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

end Sign

section Roots

theorem eq_or_iform_eq_zero_of_even {σ : Fin (Tag.rank .E8) → ℤ} (hσ : IsRoot .E8 σ)
    (he : Even (iform thetaE8 σ)) : σ = thetaE8 ∨ σ = -thetaE8 ∨ iform thetaE8 σ = 0 := by
  have hb := abs_iform_le_two_E8 isRoot_thetaE8 hσ
  rw [abs_le] at hb
  obtain ⟨m, hm⟩ := he
  have key : ∀ u : Fin (Tag.rank .E8) → ℤ, iform u u = 0 → u = 0 := fun u hu => by
    by_contra h
    have := iform_self_pos h
    omega
  have hθ := iform_self_isRoot_E8 isRoot_thetaE8
  have hσ2 := iform_self_isRoot_E8 hσ
  by_cases h2 : iform thetaE8 σ = 2
  · left
    have : iform (σ - thetaE8) (σ - thetaE8) = 0 := by
      simp only [iform_sub_left, iform_sub_right]
      rw [iform_comm σ thetaE8]
      omega
    exact sub_eq_zero.1 (key _ this)
  by_cases h3 : iform thetaE8 σ = -2
  · right; left
    have : iform (σ + thetaE8) (σ + thetaE8) = 0 := by
      simp only [iform_add_left, iform_add_right]
      rw [iform_comm σ thetaE8]
      omega
    have := key _ this
    exact eq_neg_of_add_eq_zero_left this
  · right; right
    omega

end Roots

section Main

variable {F : Type} [Field F]

variable (F) in
def leviMulRank1 : Subgroup (ModGL .E8 F) where
  carrier := {x | ∃ n ∈ parabolicLevi .E8 F JE8, ∃ A : SL2 F, x = n * rootSL2 .E8 F thetaE8 A}
  mul_mem' := by
    rintro _ _ ⟨n₁, hn₁, A₁, rfl⟩ ⟨n₂, hn₂, A₂, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq (inv_mem hn₂) A₁
    rw [inv_inv] at hA'
    refine ⟨n₁ * n₂, mul_mem hn₁ hn₂, A' * A₂, ?_⟩
    calc n₁ * rootSL2 .E8 F thetaE8 A₁ * (n₂ * rootSL2 .E8 F thetaE8 A₂) =
        n₁ * n₂ * (n₂⁻¹ * rootSL2 .E8 F thetaE8 A₁ * n₂) * rootSL2 .E8 F thetaE8 A₂ := by group
      _ = _ := by rw [hA', map_mul]; group
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    rintro _ ⟨n, hn, A, rfl⟩
    obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq hn A⁻¹
    refine ⟨n⁻¹, inv_mem hn, A', ?_⟩
    rw [← hA', map_inv]
    group

theorem toralRootGroup_le_leviMulRank1 (hF : ringChar F ≠ 2) :
    toralRootGroup .E8 F (thetaDiag thetaE8 (-1 : Fˣ)) ≤ leviMulRank1 F := by
  refine sup_le (fun t ht => ⟨t, torusGroup_le_parabolicLevi JE8 ht, 1, by simp⟩) ?_
  refine iSup₂_le fun σ hσ => ?_
  obtain ⟨hσr, hσ1⟩ := hσ
  have hev : Even (iform thetaE8 σ) := by
    refine even_of_neg_one_zpow_eq_one hF ?_
    rw [← rootChar_thetaDiag]
    exact hσ1
  obtain ⟨-, -, -, -, -, -, -, -⟩ := exceptional_Lang_root_rank_one_torus_transport .E8 F
    isRoot_thetaE8
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E8 F isRoot_thetaE8).1
  rcases eq_or_iform_eq_zero_of_even hσr hev with rfl | rfl | h0
  · intro x hx
    have : x ∈ rootRankOneGroup .E8 F thetaE8 := by
      rw [hL]
      exact Subgroup.mem_sup_left hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    have : x ∈ rootRankOneGroup .E8 F thetaE8 := by
      rw [hL]
      exact Subgroup.mem_sup_right hx
    obtain ⟨A, rfl⟩ := this
    exact ⟨1, one_mem _, A, by simp⟩
  · intro x hx
    exact ⟨x, rootSubgroup_le_parabolicLevi' (mem_parabolicRoots_E8 hσr h0) hx, 1, by simp⟩

theorem mem_parabolicLevi_of_commute_rootSL2_E8 (hF : ringChar F ≠ 2) {c : ModGL .E8 F}
    (hcG : c ∈ adjointGroup .E8 F)
    (hc : ∀ A : SL2 F, c * rootSL2 .E8 F thetaE8 A = rootSL2 .E8 F thetaE8 A * c) :
    c ∈ parabolicLevi .E8 F JE8 := by
  have hdθ : rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Fˣ)) =
      rootSL2 .E8 F thetaE8 (HSL (-1)) := (rootTorusSL2_thetaE8 (-1)).symm
  have hcT : c ∈ toralCentralizer .E8 F (thetaDiag thetaE8 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨hcG, ?_⟩
    rw [hdθ, mul_inv_eq_iff_eq_mul]
    exact (hc _).symm
  have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inr rfl))) hF
    (thetaDiag_neg_one_sign thetaE8) hcT
  obtain ⟨n, hn, A, rfl⟩ := toralRootGroup_le_leviMulRank1 hF hM
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE8 (inv_mem hn)
  have hinj : Function.Injective (rootSL2 .E8 F thetaE8) :=
    ((exceptional_Lang_root_rank_one_data .E8 F thetaE8).2.2.2.2.2.2.2.1 hF).1
  have h1 : A * uSL (1 : F) = uSL (l : F) * A := by
    apply hinj
    have h := hc (uSL 1)
    have h' := hu 1
    rw [inv_inv, mul_one] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .E8 F thetaE8 A * rootSL2 .E8 F thetaE8 (uSL 1) =
        n⁻¹ * (n * rootSL2 .E8 F thetaE8 A * rootSL2 .E8 F thetaE8 (uSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .E8 F thetaE8 (uSL 1) * (n * rootSL2 .E8 F thetaE8 A)) := by rw [h]
      _ = _ := by group
  have h2 : A * vSL (1 : F) = vSL (((l⁻¹ : Fˣ)) : F) * A := by
    apply hinj
    have h := hc (vSL 1)
    have h' := hv 1
    rw [inv_inv, mul_one] at h'
    rw [map_mul, map_mul, ← h']
    calc rootSL2 .E8 F thetaE8 A * rootSL2 .E8 F thetaE8 (vSL 1) =
        n⁻¹ * (n * rootSL2 .E8 F thetaE8 A * rootSL2 .E8 F thetaE8 (vSL 1)) := by group
      _ = n⁻¹ * (rootSL2 .E8 F thetaE8 (vSL 1) * (n * rootSL2 .E8 F thetaE8 A)) := by rw [h]
      _ = _ := by group
  obtain ⟨a, rfl⟩ := exists_eq_HSL_of_conj_uSL_vSL h1 h2
  have hT := (exceptional_Lang_root_rank_one_torus_transport .E8 F isRoot_thetaE8).2.1 a
  exact mul_mem hn (torusGroup_le_parabolicLevi JE8 hT)

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
