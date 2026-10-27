module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.SteinbergBNPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dL5Proof

abbrev SL5 : Type := Matrix.SpecialLinearGroup (Fin (4 + 1)) (ZMod 2)

abbrev Mat5 : Type := Matrix (Fin (4 + 1)) (Fin (4 + 1)) (ZMod 2)

noncomputable abbrev sl5D : CFSG.LieType.Universal.UniversalRootDatum SL5 :=
  CFSG.LieType.Universal.SpecialLinear.rootDatum 4 (ZMod 2)

noncomputable abbrev sl5H : Fin sl5D.rank → Subgroup SL5 :=
  CFSG.LieType.Universal.SpecialLinear.torus 4 (ZMod 2)

noncomputable abbrev sl5n : Fin sl5D.rank → SL5 :=
  CFSG.LieType.Universal.SpecialLinear.weylRep 4 (ZMod 2)

noncomputable abbrev sl5B : Subgroup SL5 :=
  CFSG.LieType.Steinberg.borel sl5D sl5H

noncomputable abbrev sl5N : Subgroup SL5 :=
  CFSG.LieType.Steinberg.weylN sl5n sl5H

noncomputable abbrev sl5S : Set (CFSG.GH74.BNPair.WeylGroup sl5B sl5N) :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.simpleRefl sl5D sl5n sl5H

noncomputable instance sl5_cartan_normal : (CFSG.GH74.BNPair.cartan sl5B sl5N).Normal :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.cartan_borel_weylN_normal
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum 4 (ZMod 2))
    (CFSG.LieType.Universal.SpecialLinear.steinbergExtras 4 (ZMod 2))

theorem sl5_isBNPair : CFSG.GroupTheory.TitsSystem.IsBNPair sl5B sl5N sl5S :=
  CFSG.AGLEmbeddingD2.McLaughlin.Lie.isBNPair_borel_weylN
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum 4 (ZMod 2))
    (CFSG.LieType.Universal.SpecialLinear.steinbergExtras 4 (ZMod 2))

theorem sl5_overgroup_parabolic :
    ∀ P : Subgroup SL5, sl5B ≤ P →
      ∃! J : Set (CFSG.GH74.BNPair.WeylGroup sl5B sl5N),
        J ⊆ sl5S ∧ P = CFSG.GH74.BNPair.parabolic sl5B sl5N J :=
  (CFSG.GroupTheory.TitsSystem.bourbaki_tits_standard_parabolics sl5_isBNPair).2.2.1

@[expose] def upperSub5 : Subgroup SL5 where
  carrier := {g | ∀ i j : Fin (4 + 1), j < i → (g : Mat5) i j = 0}
  mul_mem' := by
    intro g h hg hh i j hji
    have hg' : ∀ i j : Fin (4 + 1), j < i → (g : Mat5) i j = 0 := hg
    have hh' : ∀ i j : Fin (4 + 1), j < i → (h : Mat5) i j = 0 := hh
    show ((g : Mat5) * (h : Mat5)) i j = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [hg' i k hk, zero_mul]
    · rw [hh' k j (lt_of_lt_of_le hji (not_lt.mp hk)), mul_zero]
  one_mem' := by
    intro i j hji
    exact Matrix.one_apply_ne hji.ne'
  inv_mem' := by
    intro g hg i j hji
    have hg' : ∀ i j : Fin (4 + 1), j < i → (g : Mat5) i j = 0 := hg
    have hut : (g : Mat5).IsUpperTriangular := fun ⦃i j⦄ h => hg' i j h
    have h1 : ((g⁻¹ : SL5) : Mat5) * (g : Mat5) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (g : Mat5) * ((g⁻¹ : SL5) : Mat5) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    letI : Invertible (g : Mat5) := ⟨((g⁻¹ : SL5) : Mat5), h1, h2⟩
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular (b := id) hut
    rw [Matrix.inv_eq_left_inv h1] at hinv
    exact hinv (show id j < id i from hji)

theorem ub5_mem_iff {g : SL5} :
    g ∈ upperSub5 ↔ ∀ i j : Fin (4 + 1), j < i → (g : Mat5) i j = 0 :=
  Iff.rfl

private theorem sl5B_def :
    sl5B = (⨆ k, sl5H k) ⊔ CFSG.LieType.Steinberg.posUnipotent sl5D :=
  rfl

private theorem ub5_rootSubgroup_le {i j : Fin (4 + 1)} (hij : i ≠ j) (hlt : i < j) :
    CFSG.LieType.Universal.SpecialLinear.rootSubgroup 4 (ZMod 2) hij ≤ upperSub5 := by
  rintro g hg
  obtain ⟨c, rfl⟩ := (CFSG.LieType.Universal.SpecialLinear.mem_rootSubgroup hij g).mp hg
  rw [ub5_mem_iff]
  intro r s hsr
  have hrs : r ≠ s := hsr.ne'
  have hne : ¬ (i = r ∧ j = s) := by
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hlt hsr
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne hrs,
    Matrix.single_apply_of_ne i j c r s hne, zero_add]

private theorem ub5_torus_le (k : Fin 4) :
    CFSG.LieType.Universal.SpecialLinear.torus 4 (ZMod 2) k ≤ upperSub5 := by
  unfold CFSG.LieType.Universal.SpecialLinear.torus
  rw [Subgroup.closure_le]
  rintro h ⟨t, ht⟩
  rw [SetLike.mem_coe, ub5_mem_iff]
  intro i j hji
  rw [ht, Matrix.diagonal_apply_ne _ hji.ne']

private theorem ub5_posUnipotent_le :
    CFSG.LieType.Steinberg.posUnipotent sl5D ≤ upperSub5 := by
  unfold CFSG.LieType.Steinberg.posUnipotent
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨hroot0, hpos0⟩ := hγ
  have hroot : γ ∈ CFSG.LieType.RootSystem.roots
      (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 4) ∅ := hroot0
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq] at hroot
  obtain ⟨i, j, hij, hγ'⟩ := hroot
  have hlt : i < j := by
    have hht := CFSG.LieType.Universal.SpecialLinear.ht_eq 4 hγ'
    have h2 : (0 : ℤ) < ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := lt_of_lt_of_eq hpos0 hht
    have h1 : (i : ℕ) < (j : ℕ) := by omega
    exact h1
  have heq : sl5D.rootGroup γ =
      CFSG.LieType.Universal.SpecialLinear.rootSubgroup 4 (ZMod 2) hij :=
    CFSG.LieType.Universal.SpecialLinear.rootGroup_eq 4 (ZMod 2) hij hγ'
  rw [heq]
  exact ub5_rootSubgroup_le hij hlt

theorem sl5B_le_upperSub5 : sl5B ≤ upperSub5 := by
  rw [sl5B_def]
  exact sup_le (iSup_le fun k => ub5_torus_le k) ub5_posUnipotent_le

theorem sl5S_ncard_le : sl5S.ncard ≤ 4 := by
  have hr : sl5S = Set.range (fun i : Fin sl5D.rank =>
      ((⟨sl5n i, CFSG.LieType.Steinberg.n_mem_weylN i⟩ : CFSG.LieType.Steinberg.weylN sl5n sl5H) :
        CFSG.GH74.BNPair.WeylGroup sl5B sl5N)) := rfl
  rw [hr]
  calc (Set.range _).ncard = ((fun i : Fin sl5D.rank =>
        ((⟨sl5n i, CFSG.LieType.Steinberg.n_mem_weylN i⟩ : CFSG.LieType.Steinberg.weylN sl5n sl5H) :
          CFSG.GH74.BNPair.WeylGroup sl5B sl5N)) '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin sl5D.rank)).ncard := Set.ncard_image_le Set.finite_univ
    _ = Nat.card (Fin sl5D.rank) := Set.ncard_univ _
    _ = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl

theorem sl5B_overgroups_ncard_le : {P : Subgroup SL5 | sl5B ≤ P}.ncard ≤ 16 := by
  have hfinS : sl5S.Finite := Set.toFinite _
  have hsub : {P : Subgroup SL5 | sl5B ≤ P} ⊆
      (fun J => CFSG.GH74.BNPair.parabolic sl5B sl5N J) '' sl5S.powerset := by
    intro P hP
    obtain ⟨J, hJ, hPJ⟩ := (sl5_overgroup_parabolic P hP).exists
    exact ⟨J, hJ, hPJ.symm⟩
  have hpow : sl5S.powerset.Finite := hfinS.powerset
  calc _ ≤ ((fun J => CFSG.GH74.BNPair.parabolic sl5B sl5N J) '' sl5S.powerset).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ sl5S.powerset.ncard := Set.ncard_image_le hpow
    _ = 2 ^ sl5S.ncard := Set.ncard_powerset sl5S hfinS
    _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) sl5S_ncard_le
    _ = 16 := by norm_num

end K21dL5Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
