module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyQuad
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalOpposite
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Holds
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartOne.KE6.E6LStd

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley.EvenOddRadical
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def e8T3CThreeRoot1 : Fin Tag.E8.rank → ℤ :=
  e6Lat Tag.E8 ![0, 0, 0, 1, 0, 0]

private def e8T3CThreeRoot2 : Fin Tag.E8.rank → ℤ :=
  e6Lat Tag.E8 ![0, 0, 1, 1, 1, 0]

private def e8T3CThreeRoot3 : Fin Tag.E8.rank → ℤ :=
  e6Lat Tag.E8 ![1, 0, 1, 1, 1, 1]

private theorem isRoot_e8T3CThreeRoot1 :
    IsRoot Tag.E8 e8T3CThreeRoot1 :=
  isRoot_e6Lat_iff.2 (isRoot_iff_mem_artifactRoots.2 (by decide +kernel))

private theorem isRoot_e8T3CThreeRoot2 :
    IsRoot Tag.E8 e8T3CThreeRoot2 :=
  isRoot_e6Lat_iff.2 (isRoot_iff_mem_artifactRoots.2 (by decide +kernel))

private theorem isRoot_e8T3CThreeRoot3 :
    IsRoot Tag.E8 e8T3CThreeRoot3 :=
  isRoot_e6Lat_iff.2 (isRoot_iff_mem_artifactRoots.2 (by decide +kernel))

private theorem mem_parabolic_e8T3CThreeRoot1 :
    e8T3CThreeRoot1 ∈ parabolicRoots Tag.E8 (e6Set Tag.E8) :=
  ⟨isRoot_e8T3CThreeRoot1, fun i hi =>
    e6Lat_apply_of_le (Nat.le_of_not_lt (by simpa [e6Set] using hi))⟩

private theorem mem_parabolic_e8T3CThreeRoot2 :
    e8T3CThreeRoot2 ∈ parabolicRoots Tag.E8 (e6Set Tag.E8) :=
  ⟨isRoot_e8T3CThreeRoot2, fun i hi =>
    e6Lat_apply_of_le (Nat.le_of_not_lt (by simpa [e6Set] using hi))⟩

private theorem mem_parabolic_e8T3CThreeRoot3 :
    e8T3CThreeRoot3 ∈ parabolicRoots Tag.E8 (e6Set Tag.E8) :=
  ⟨isRoot_e8T3CThreeRoot3, fun i hi =>
    e6Lat_apply_of_le (Nat.le_of_not_lt (by simpa [e6Set] using hi))⟩

private theorem permLattice_rho_e6Lat (β : Fin Tag.E6.rank → ℤ) :
    permLattice (rhoτ Tag.E8) (e6Lat Tag.E8 β) =
      e6Lat Tag.E8 (permLattice (rho6Perm) β) := by
  funext i
  by_cases hi : i ∈ e6Set Tag.E8
  · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := Tag.E8) (e6Set_lt hi)
    rw [permLattice, Function.comp_apply]
    have hs : (rhoτ Tag.E8).symm (e6Idx k) = e6Idx (rho6 k) := by
      rw [Equiv.symm_apply_eq, rhoτ_e6Idx, rho6_rho6]
    have hs' : (rho6Perm).symm k = rho6 k := by
      rw [Equiv.symm_apply_eq]
      show k = rho6 (rho6 k)
      rw [rho6_rho6]
    rw [hs, e6Lat_apply_e6Idx, e6Lat_apply_e6Idx, permLattice, Function.comp_apply, hs']
  · have hle : Tag.E6.rank ≤ i.val := Nat.le_of_not_lt (by simpa [e6Set] using hi)
    rw [permLattice, Function.comp_apply]
    have hfix : rhoτ Tag.E8 i = i := rhoτ_of_not_mem hi
    have hs : (rhoτ Tag.E8).symm i = i := by rw [Equiv.symm_apply_eq]; exact hfix.symm
    rw [hs]
    have hlt : ¬ i.val < Tag.E6.rank := not_lt.mpr hle
    simp [e6Lat, hlt]

private theorem permLattice_rho_e6Vec1 :
    permLattice (rho6Perm) (![0, 0, 0, 1, 0, 0] : Fin Tag.E6.rank → ℤ) =
      ![0, 0, 0, 1, 0, 0] := by
  funext k; fin_cases k <;> decide

private theorem permLattice_rho_e6Vec2 :
    permLattice (rho6Perm) (![0, 0, 1, 1, 1, 0] : Fin Tag.E6.rank → ℤ) =
      ![0, 0, 1, 1, 1, 0] := by
  funext k; fin_cases k <;> decide

private theorem permLattice_rho_e6Vec3 :
    permLattice (rho6Perm) (![1, 0, 1, 1, 1, 1] : Fin Tag.E6.rank → ℤ) =
      ![1, 0, 1, 1, 1, 1] := by
  funext k; fin_cases k <;> decide

private theorem permLattice_rho_e8T3CThreeRoot1 :
    permLattice (rhoτ Tag.E8) e8T3CThreeRoot1 = e8T3CThreeRoot1 := by
  exact (permLattice_rho_e6Lat (β := ![0, 0, 0, 1, 0, 0])).trans
    (congrArg (e6Lat Tag.E8) permLattice_rho_e6Vec1)

private theorem permLattice_rho_e8T3CThreeRoot2 :
    permLattice (rhoτ Tag.E8) e8T3CThreeRoot2 = e8T3CThreeRoot2 := by
  exact (permLattice_rho_e6Lat (β := ![0, 0, 1, 1, 1, 0])).trans
    (congrArg (e6Lat Tag.E8) permLattice_rho_e6Vec2)

private theorem permLattice_rho_e8T3CThreeRoot3 :
    permLattice (rhoτ Tag.E8) e8T3CThreeRoot3 = e8T3CThreeRoot3 := by
  exact (permLattice_rho_e6Lat (β := ![1, 0, 1, 1, 1, 1])).trans
    (congrArg (e6Lat Tag.E8) permLattice_rho_e6Vec3)

section Fixed

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

private theorem conj_pinnedX_eq_self_of_stdTwist [Infinite L]
    {n : ModGL Tag.E8 L} {π : Equiv.Perm (Fin Tag.E8.rank)}
    (hn : n ∈ monomialSubgroup Tag.E8 L) (hstd : StdTwist6 n π)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α)
    (hsupp : ∀ j, α j ≠ 0 → j ∈ e6Set Tag.E8)
    (hfix : permLattice π α = α) (c : L) :
    n * pinnedX Tag.E8 L α c * n⁻¹ = pinnedX Tag.E8 L α c := by
  classical
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hn
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hk
  have hmaps : MapsRootLines
      (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w) w := by
    simpa using (mapsRootLines_of_mem_torusGroup (rootDiagUnit_mem_torusGroup a)).mul
      (mapsRootLines_canonicalRep (R := L) w)
  have hconj : ∀ (γ : Fin Tag.E8.rank → ℤ), IsRoot Tag.E8 γ → ∀ d : L,
      (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w) * pinnedX Tag.E8 L γ d *
        (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w)⁻¹ =
      pinnedX Tag.E8 L (w • γ) ((rootChar a (w • γ) : L) * d) := by
    intro γ hγ d
    obtain ⟨ε, hε, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
    have hε1 : ε = 1 := eq_one_of_mul_self_eq_one_of_charTwo hε
    calc
      (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w) * pinnedX Tag.E8 L γ d *
          (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w)⁻¹
        = rootDiagUnit Tag.E8 a *
            (canonicalRep (coxeterSystem Tag.E8) L w * pinnedX Tag.E8 L γ d *
              (canonicalRep (coxeterSystem Tag.E8) L w)⁻¹) *
            (rootDiagUnit Tag.E8 a)⁻¹ := by group
      _ = rootDiagUnit Tag.E8 a * pinnedX Tag.E8 L (w • γ) (ε * d) *
            (rootDiagUnit Tag.E8 a)⁻¹ := by rw [hX]
      _ = pinnedX Tag.E8 L (w • γ) ((rootChar a (w • γ) : L) * (ε * d)) :=
            rootDiagUnit_conj_pinnedX a (IsRoot.smul hγ w) (ε * d)
      _ = pinnedX Tag.E8 L (w • γ) ((rootChar a (w • γ) : L) * d) := by
            rw [hε1, one_mul]
  have hscalar : ∀ j ∈ e6Set Tag.E8,
      w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) = Pi.single (π j) 1 ∧
        rootChar a (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) = 1 := by
    intro j hj
    have hγ : IsRoot Tag.E8 (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := isRoot_single _ _
    have hδ : IsRoot Tag.E8 (Pi.single (π j) 1 : Fin Tag.E8.rank → ℤ) := isRoot_single _ _
    have hgen : (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w) *
        pinnedX Tag.E8 L (Pi.single j 1) 1 *
        (rootDiagUnit Tag.E8 a * canonicalRep (coxeterSystem Tag.E8) L w)⁻¹ =
        pinnedX Tag.E8 L (Pi.single (π j) 1) 1 := by
      rw [pinnedX_single, pinnedX_single]
      exact (hstd.hgen j hj 1).1
    have heq : pinnedX Tag.E8 L (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ))
        ((rootChar a (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) : L) * 1) =
        pinnedX Tag.E8 L (Pi.single (π j) 1) 1 := by
      rw [← hconj (Pi.single j 1) hγ 1]
      exact hgen
    have hparam : (rootChar a (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) : L) * 1 ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) one_ne_zero
    have hmem : pinnedX Tag.E8 L (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ))
        ((rootChar a (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) : L) * 1) ∈
        rootSubgroup Tag.E8 L (Pi.single (π j) 1) := by
      rw [heq]
      exact mem_rootSubgroup.2 ⟨1, rfl⟩
    have hwj : w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) = Pi.single (π j) 1 :=
      eq_of_pinnedX_mem_rootSubgroup (IsRoot.smul hγ w) hδ hparam hmem
    refine ⟨hwj, ?_⟩
    have hpin : ∀ d : L, pinnedX Tag.E8 L (Pi.single (π j) 1)
        ((rootChar a (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) : L) * d) =
        pinnedX Tag.E8 L (Pi.single (π j) 1) d := by
      intro d
      have h2 := (hstd.hgen j hj d).1
      rw [← pinnedX_single, ← pinnedX_single] at h2
      rw [hconj (Pi.single j 1) hγ d, hwj] at h2
      rw [hwj]
      exact h2
    have h1 := pinnedX_injective Tag.E8 L (Pi.single (π j) 1) (hpin 1)
    simpa using h1
  have hwsum : w • α = ∑ j, α j • (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := by
    conv_lhs => rw [eq_sum_smul_single α]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm w (α j) _
  have hperm : permLattice π α =
      ∑ j, α j • (Pi.single (π j) 1 : Fin Tag.E8.rank → ℤ) := by
    conv_lhs => rw [eq_sum_smul_single α]
    funext i
    simp only [permLattice, Function.comp_apply, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, Equiv.symm_apply_eq, smul_eq_mul]
  have hwα : w • α = α := by
    rw [hwsum]
    calc ∑ j, α j • (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) =
        ∑ j, α j • (Pi.single (π j) 1 : Fin Tag.E8.rank → ℤ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j ∈ e6Set Tag.E8
          · rw [(hscalar j hj).1]
          · have h0 : α j = 0 := by
              by_contra hne
              exact hj (hsupp j hne)
            simp [h0]
      _ = permLattice π α := hperm.symm
      _ = α := hfix
  have hparamα : rootChar a (w • α) = 1 := by
    rw [hwsum, rootChar_sum]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [rootChar_zsmul]
    by_cases hj : j ∈ e6Set Tag.E8
    · rw [(hscalar j hj).2, one_zpow]
    · have h0 : α j = 0 := by
        by_contra hne
        exact hj (hsupp j hne)
      simp [h0]
  have hrc' : rootChar a α = 1 := by rw [← hwα]; exact hparamα
  rw [hconj α hα c, hwα, hrc', Units.val_one, one_mul]

end Fixed

theorem exists_three_qTorus_stdLayer_charTwo {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
    [Infinite L] {n₁ : ModGL Tag.E8 L} (hn₁ : n₁ ∈ monomialSubgroup Tag.E8 L)
    {π : Equiv.Perm (Fin Tag.E8.rank)} (hstd : StdTwist6 n₁ π) :
    ∃ T : Subgroup (ModGL Tag.E8 L), T ≤ stdLayer Tag.E8 2 1 n₁ ∧
      IsElemAbelian 3 T ∧ Nat.card T = 3 ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let roots : Fin 3 → (Fin Tag.E8.rank → ℤ) :=
    ![e8T3CThreeRoot1, e8T3CThreeRoot2, e8T3CThreeRoot3]
  have hsupp0 : ∀ (β : Fin Tag.E6.rank → ℤ) (j : Fin Tag.E8.rank),
      e6Lat Tag.E8 β j ≠ 0 → j ∈ e6Set Tag.E8 := by
    intro β j hj
    by_contra hnot
    exact hj (e6Lat_apply_of_le (Nat.le_of_not_lt (by simpa [e6Set] using hnot)))
  have hroot : ∀ i, IsRoot Tag.E8 (roots i) := by
    intro i
    fin_cases i
    · exact isRoot_e8T3CThreeRoot1
    · exact isRoot_e8T3CThreeRoot2
    · exact isRoot_e8T3CThreeRoot3
  have hpar : ∀ i, roots i ∈ parabolicRoots Tag.E8 (e6Set Tag.E8) := by
    intro i
    fin_cases i
    · exact mem_parabolic_e8T3CThreeRoot1
    · exact mem_parabolic_e8T3CThreeRoot2
    · exact mem_parabolic_e8T3CThreeRoot3
  have hsupp : ∀ (i : Fin 3) (j : Fin Tag.E8.rank), roots i j ≠ 0 → j ∈ e6Set Tag.E8 := by
    intro i j hj
    fin_cases i <;>
      exact hsupp0 _ j (by
        simpa [roots, e8T3CThreeRoot1, e8T3CThreeRoot2, e8T3CThreeRoot3] using hj)
  have hfix : ∀ i, permLattice π (roots i) = roots i := by
    intro i
    rcases hstd.hπ with hπ1 | hπrho
    · rw [hπ1]
      funext j
      rfl
    · rw [hπrho]
      fin_cases i
      · exact permLattice_rho_e8T3CThreeRoot1
      · exact permLattice_rho_e8T3CThreeRoot2
      · exact permLattice_rho_e8T3CThreeRoot3
  have hfixSL2 : ∀ (i : Fin 3) (A : SL2 L),
      n₁ * rootSL2 Tag.E8 L (roots i) A * n₁⁻¹ = rootSL2 Tag.E8 L (roots i) A := by
    intro i A
    have heq : (MulAut.conj n₁).toMonoidHom.comp (rootSL2 Tag.E8 L (roots i)) =
        rootSL2 Tag.E8 L (roots i) := by
      refine MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower ?_
      intro x hx
      rcases hx with ⟨d, rfl⟩ | ⟨d, rfl⟩
      · change n₁ * rootSL2 Tag.E8 L (roots i) (uSL d) * n₁⁻¹ =
          rootSL2 Tag.E8 L (roots i) (uSL d)
        rw [rootSL2_uSL_of_charTwo (hroot i) d,
          conj_pinnedX_eq_self_of_stdTwist hn₁ hstd (hroot i) (hsupp i) (hfix i) d]
      · change n₁ * rootSL2 Tag.E8 L (roots i) (vSL d) * n₁⁻¹ =
          rootSL2 Tag.E8 L (roots i) (vSL d)
        rw [rootSL2_vSL_of_charTwo (hroot i) d,
          conj_pinnedX_eq_self_of_stdTwist hn₁ hstd (IsRoot.neg (hroot i))
            (fun j hj => hsupp i j (by simpa using hj))
            (by rw [permLattice_neg, hfix i]) d]
    exact DFunLike.congr_fun heq A
  have hmap_c3 : Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) c3 = c3 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    fin_cases i <;> fin_cases j <;>
      simp [c3, iterateFrobenius_def, CharTwo.neg_eq, Matrix.map_apply]
  have hΦfix : ∀ i, Units.map (entrywiseHom (iterateFrobenius L 2 1))
      (rootSL2 Tag.E8 L (roots i) c3) = rootSL2 Tag.E8 L (roots i) c3 := by
    intro i
    rw [units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_rootSL2_of_charTwo (iterateFrobenius L 2 1) (hroot i) c3, hmap_c3]
  have hmem : ∀ i, rootSL2 Tag.E8 L (roots i) c3 ∈ stdLayer Tag.E8 2 1 n₁ := by
    intro i
    refine mem_stdLayer.2 ⟨?_, ?_⟩
    · rw [subsystemGroup_eq_rootSpan]
      refine rootSpan_mono ?_ (rootSL2_mem_rootSpan_pair (hroot i) c3)
      rintro γ (rfl | rfl)
      · exact hpar i
      · exact neg_mem_parabolicRoots (hpar i)
    · rw [hΦfix i]
      exact hfixSL2 i c3
  have hcomm : ∀ i j : Fin 3, i ≠ j → ∀ A B : SL2 L,
      Commute (rootSL2 Tag.E8 L (roots i) A) (rootSL2 Tag.E8 L (roots j) B) := by
    intro i j hij A B
    refine rootSL2_commute_of_orth' (by simp [SimplyLacedTag]) (hroot i) (hroot j) ?_ A B
    fin_cases i <;> fin_cases j <;> simp_all [roots] <;> decide
  obtain ⟨T, hTel, hTcard, hTgen⟩ :=
    exists_elemAbelian_pow_of_commuting_sl2 (p := 3) (c := (c3 : SL2 L))
      c3_pow_three c3_ne_one (fun i => rootSL2 Tag.E8 L (roots i))
      (fun i => rootSL2_injective_of_field (roots i)) hcomm
  exact ⟨T, hTgen (stdLayer Tag.E8 2 1 n₁) hmem, hTel, hTcard⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
