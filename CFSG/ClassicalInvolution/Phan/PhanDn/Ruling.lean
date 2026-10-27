module

public import CFSG.ClassicalInvolution.Phan.PhanDn.BaseChange
public import CFSG.ClassicalInvolution.Phan.PhanDn.Perp
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Unitary
open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K} [CharP K 2]

theorem quadPlus_bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (hg : ∀ x, Qn E n (g x) = Qn E n x)
    (v : Fin n ⊕ Fin n → K) : quadPlus n K (bcLin E n g v) = quadPlus n K v := by
  have hpol := polar_bcLin E n g hg
  have hv : v ∈ Submodule.span K (Set.range (jEmb (F := F) E n)) := by
    rw [span_range_jEmb]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun v _ => quadPlus n K (bcLin E n g v) = quadPlus n K v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨x, rfl⟩
    rw [bcLin_jEmb, quadPlus_jEmb, quadPlus_jEmb, hg x]
  · simp
  · intro u w _ _ hu hw
    rw [LinearMap.map_add, QuadraticMap.map_add (quadPlus n K),
      QuadraticMap.map_add (quadPlus n K), hu, hw, hpol u w]
  · intro c u _ hu
    rw [LinearMap.map_smul, QuadraticMap.map_smul, hu, QuadraticMap.map_smul]

noncomputable def bcLinHom (E : QuadExt F K σ) (n : ℕ) :
    Module.End F (Fin n → K) →* Module.End K (Fin n ⊕ Fin n → K) where
  toFun := bcLin E n
  map_one' := bcLin_id E n
  map_mul' g h := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, bcLin_comp]

noncomputable def rulingHom (E : QuadExt F K σ) (n : ℕ) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E n)) →* Multiplicative (ZMod 2) :=
  (quadPlusForm n K).dicksonHom
    ((bcLinHom E n).comp
      ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := Fin n → K)).comp
        (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)).subtype))
    (fun g v => by
      change (quadPlusForm n K).Q (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v) =
        (quadPlusForm n K).Q v
      rw [show (quadPlusForm n K).Q = ⇑(quadPlus n K) from (coe_quadPlus n K).symm]
      exact quadPlus_bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
        (fun x => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 x) v)
    (isLagrangian_stdLag n K)

theorem rulingHom_apply (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E n))) :
    rulingHom E n g =
      Multiplicative.ofAdd (dicksonInvariant (stdLag n K) (bcLin E n g)) := by
  simp only [rulingHom, QuadForm.dicksonHom_apply, MonoidHom.comp_apply,
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, Subgroup.coe_subtype]
  rfl

theorem rulingHom_tauAt (E : QuadExt F K σ) (n : ℕ) (k : Fin n) :
    rulingHom E n ⟨tauAt E k, tauAt_mem_orthogonalGroup E k⟩ =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [rulingHom_apply]
  rw [bcLin_tauAt]
  congr 1
  let a : Fin n ⊕ Fin n → K := stdE k + stdF k
  have hQa1 : (quadPlusForm n K).Q a = 1 := by
    dsimp only [a]
    rw [show (quadPlusForm n K).Q = ⇑(quadPlus n K) from (coe_quadPlus n K).symm]
    show quadPlus n K (stdE k + stdF k) = 1
    rw [quadPlus_apply, Finset.sum_eq_single k]
    · simp [stdE, stdF]
    · intro j _ hj
      simp [stdE, stdF, hj]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hβ : ∀ v : Fin n ⊕ Fin n → K,
      (quadPlusForm n K).polar.β v a = v (Sum.inl k) + v (Sum.inr k) := by
    intro v
    dsimp only [a]
    show quadPlusPolar n K v (stdE k + stdF k) = v (Sum.inl k) + v (Sum.inr k)
    rw [quadPlusPolar, Finset.sum_eq_single k]
    · simp [stdE, stdF]
    · intro j _ hj
      simp [stdE, stdF, hj]
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hswap : ∀ v : Fin n ⊕ Fin n → K,
      swapAt n k v = v - ((v (Sum.inl k) + v (Sum.inr k)) • a) := by
    intro v
    dsimp only [a]
    ext w
    cases w with
    | inl i =>
      rw [Pi.sub_apply, Pi.smul_apply, swapAt_inl]
      by_cases hi : i = k
      · rw [if_pos hi, hi]
        simp only [Pi.add_apply]
        rw [stdE_inl, stdF_inl, if_pos rfl, add_zero, smul_eq_mul, mul_one,
          CharTwo.sub_eq_add, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      · rw [if_neg hi, Pi.add_apply, stdE_inl, stdF_inl, if_neg hi, add_zero, smul_zero,
          sub_zero]
    | inr i =>
      rw [Pi.sub_apply, Pi.smul_apply, swapAt_inr]
      by_cases hi : i = k
      · rw [if_pos hi, hi]
        simp only [Pi.add_apply]
        rw [stdE_inr, stdF_inr, if_pos rfl, zero_add, smul_eq_mul, mul_one,
          CharTwo.sub_eq_add, add_comm (v (Sum.inr k)) (v (Sum.inl k) + v (Sum.inr k)),
          add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · rw [if_neg hi, Pi.add_apply, stdE_inr, stdF_inr, if_neg hi, add_zero, smul_zero,
          sub_zero]
  refine QuadForm.dicksonInvariant_eq_one_of_reflection (Φ := quadPlusForm n K)
    (X₀ := stdLag n K) (isLagrangian_stdLag n K) (g := swapAt n k) ?_ (Z := ⊥)
    (QuadForm.isTotallySingular_bot (Φ := quadPlusForm n K)) (a := a) ?_ ?_ ?_
  · intro v
    rw [← bcLin_tauAt E n k]
    rw [show (quadPlusForm n K).Q = ⇑(quadPlus n K) from (coe_quadPlus n K).symm]
    exact quadPlus_bcLin E n (tauAt E k)
      (fun x => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (tauAt_mem_orthogonalGroup E k) x) v
  · rw [ReflForm.perp_bot]
    exact Submodule.mem_top
  · rw [hQa1]
    exact one_ne_zero
  · intro v _
    rw [Submodule.mem_bot, hβ v, hQa1, div_one, hswap v, sub_self]

noncomputable def rulingGroup (E : QuadExt F K σ) (n : ℕ) :
    Subgroup ((Fin n → K) ≃ₗ[F] (Fin n → K)) :=
  (rulingHom E n).ker.map (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)).subtype

theorem mem_rulingGroup (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
    g ∈ rulingGroup E n ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) ∧
      Even (n - Module.finrank K ↥(stdLag n K ⊓ (stdLag n K).map (bcLin E n g))) := by
  constructor
  · intro hg
    rw [rulingGroup, Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    refine ⟨h.2, ?_⟩
    rw [MonoidHom.mem_ker, rulingHom_apply, ofAdd_eq_one] at hh
    rw [dicksonInvariant, finrank_stdLag, ZMod.natCast_eq_zero_iff_even] at hh
    exact hh
  · rintro ⟨hgO, hEven⟩
    refine Subgroup.mem_map.mpr ⟨⟨g, hgO⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker, rulingHom_apply, ofAdd_eq_one, dicksonInvariant, finrank_stdLag,
      ZMod.natCast_eq_zero_iff_even]
    exact hEven

theorem orthDerived_le_rulingGroup (E : QuadExt F K σ) (n : ℕ) :
    CFSG.RankThree.Classical2.orthDerived (Qn E n) ≤ rulingGroup E n := by
  rw [CFSG.RankThree.Classical2.orthDerived, rulingGroup, Subgroup.commutator_le]
  intro g hg h hh
  refine Subgroup.mem_map.mpr
    ⟨⟨⁅g, h⁆, Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hg hh)⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  have hcomm : (⟨⁅g, h⁆, Subgroup.commutator_le_self _
      (Subgroup.commutator_mem_commutator hg hh)⟩ :
      ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E n))) =
      ⁅(⟨g, hg⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E n))), ⟨h, hh⟩⁆ := rfl
  rw [hcomm, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]

private def twoVec {n : ℕ} (i j : Fin n) : Fin n → K :=
  Pi.single i (1 : K) + Pi.single j 1

omit [CharP K 2] in
private theorem twoVec_apply_self {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    twoVec (K := K) i j i = 1 := by
  simp [twoVec, hij]

omit [CharP K 2] in
private theorem twoVec_apply_other {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    twoVec (K := K) i j j = 1 := by
  simp [twoVec, Ne.symm hij]

private theorem Qn_smul_two (E : QuadExt F K σ) (n : ℕ) {i j : Fin n} (hij : i ≠ j) (a : K) :
    Qn E n (a • twoVec (K := K) i j) = 0 := by
  have hF2 : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  rw [Qn_apply]
  rw [← Finset.sum_subset (s₁ := {i, j}) (s₂ := Finset.univ) (Finset.subset_univ _) ?_]
  · rw [Finset.sum_pair hij]
    have hi : (a • twoVec (K := K) i j) i = a := by simp [twoVec, hij]
    have hj : (a • twoVec (K := K) i j) j = a := by simp [twoVec, Ne.symm hij]
    rw [hi, hj]
    exact CharTwo.add_self_eq_zero _
  · intro k _ hk
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hki, hkj⟩ := hk
    rw [Pi.smul_apply, twoVec, Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj,
      add_zero, smul_zero, QuadraticMap.map_zero]

private theorem polar_Qn_smul_two (E : QuadExt F K σ) (n : ℕ) {i j : Fin n} (hij : i ≠ j)
    (a b : K) :
    polar (Qn E n) (a • twoVec (K := K) i j) (b • twoVec (K := K) i j) = 0 := by
  have hF2 : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  rw [polar_Qn]
  rw [← Finset.sum_subset (s₁ := {i, j}) (s₂ := Finset.univ) (Finset.subset_univ _) ?_]
  · rw [Finset.sum_pair hij]
    have hi : (a • twoVec (K := K) i j) i = a := by simp [twoVec, hij]
    have hj : (a • twoVec (K := K) i j) j = a := by simp [twoVec, Ne.symm hij]
    have hi' : (b • twoVec (K := K) i j) i = b := by simp [twoVec, hij]
    have hj' : (b • twoVec (K := K) i j) j = b := by simp [twoVec, Ne.symm hij]
    rw [hi, hj, hi', hj']
    exact CharTwo.add_self_eq_zero _
  · intro k _ hk
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    obtain ⟨hki, hkj⟩ := hk
    rw [Pi.smul_apply, twoVec, Pi.add_apply, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj,
      add_zero, smul_zero, QuadraticMap.polar_zero_left]

omit [CharP K 2] in
private theorem polar_Qn_smul_disjoint (E : QuadExt F K σ) (n : ℕ)
    {i j i' j' : Fin n} (hii' : i ≠ i') (hij' : i ≠ j') (hji' : j ≠ i') (hjj' : j ≠ j')
    (a b : K) :
    polar (Qn E n) (a • twoVec (K := K) i j) (b • twoVec (K := K) i' j') = 0 := by
  rw [polar_Qn]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i ∨ k = j
  · have hy : (b • twoVec (K := K) i' j') k = 0 := by
      rcases hk with rfl | rfl
      · rw [Pi.smul_apply, twoVec, Pi.add_apply, Pi.single_eq_of_ne hii', Pi.single_eq_of_ne hij',
          add_zero, smul_zero]
      · rw [Pi.smul_apply, twoVec, Pi.add_apply, Pi.single_eq_of_ne hji', Pi.single_eq_of_ne hjj',
          add_zero, smul_zero]
    rw [hy, QuadraticMap.polar_zero_right]
  · rw [not_or] at hk
    have hx : (a • twoVec (K := K) i j) k = 0 := by
      rw [Pi.smul_apply, twoVec, Pi.add_apply, Pi.single_eq_of_ne hk.1, Pi.single_eq_of_ne hk.2,
        add_zero, smul_zero]
    rw [hx, QuadraticMap.polar_zero_left]

theorem exists_totallySingular_three (E : QuadExt F K σ) (n : ℕ) (hn : 4 ≤ n) :
    ∃ T : Submodule F (Fin n → K), Module.finrank F T = 3 ∧ ∀ x ∈ T, Qn E n x = 0 := by
  classical
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1]
  have h23 : i2 ≠ i3 := by simp [i2, i3]
  have h02 : i0 ≠ i2 := by simp [i0, i2]
  have h03 : i0 ≠ i3 := by simp [i0, i3]
  have h12 : i1 ≠ i2 := by simp [i1, i2]
  have h13 : i1 ≠ i3 := by simp [i1, i3]
  let u : Fin n → K := twoVec i0 i1
  let v : Fin n → K := bcTheta E • u
  let w : Fin n → K := twoVec i2 i3
  have hli : LinearIndependent F ![u, v, w] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have hc2 : c 2 = 0 := by
      have h := congrFun hc i2
      simp only [Fin.sum_univ_three] at h
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        u, v, w, twoVec, h02, h12] at h
      rw [Pi.single_eq_of_ne h23, smul_zero, add_zero, Algebra.smul_def, mul_one] at h
      exact (algebraMap F K).injective (by simpa using h)
    have hc0 : algebraMap F K (c 0) + algebraMap F K (c 1) * bcTheta E = 0 := by
      have h := congrFun hc i0
      simp only [Fin.sum_univ_three] at h
      simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        u, v, w, twoVec, h01, hc2] at h
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
      exact h
    have hc1 : c 1 = 0 := by
      by_contra h1
      have h1' : algebraMap F K (c 1) ≠ 0 := by
        intro h0
        exact h1 ((algebraMap F K).injective (by simpa using h0))
      have hlin : algebraMap F K (c 0) = algebraMap F K (c 1) * bcTheta E := by
        have := hc0
        rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at this
      have hθ : bcTheta E = algebraMap F K ((c 1)⁻¹ * c 0) := by
        calc bcTheta E = (algebraMap F K (c 1))⁻¹ * (algebraMap F K (c 1) * bcTheta E) := by
              rw [← mul_assoc, inv_mul_cancel₀ h1', one_mul]
          _ = (algebraMap F K (c 1))⁻¹ * algebraMap F K (c 0) := by rw [← hlin]
          _ = algebraMap F K ((c 1)⁻¹ * c 0) := by rw [map_mul, map_inv₀]
      exact bcTheta_not_fixed E (by rw [hθ, E.fix])
    have hc0' : c 0 = 0 := by
      have h := hc0
      rw [hc1, map_zero, zero_mul, add_zero] at h
      exact (algebraMap F K).injective (by simpa using h)
    fin_cases i
    · exact hc0'
    · exact hc1
    · exact hc2
  refine ⟨Submodule.span F (Set.range ![u, v, w]), ?_, ?_⟩
  · rw [finrank_span_eq_card hli]
    simp
  · have hS : ∀ x ∈ Set.range ![u, v, w], Qn E n x = 0 := by
      rintro x ⟨k, rfl⟩
      fin_cases k
      · simpa [u] using Qn_smul_two E n h01 1
      · simpa [v, u] using Qn_smul_two E n h01 (bcTheta E)
      · simpa [w] using Qn_smul_two E n h23 1
    have hB : ∀ x ∈ Set.range ![u, v, w], ∀ y ∈ Set.range ![u, v, w],
        polar (Qn E n) x y = 0 := by
      rintro x ⟨k, rfl⟩ y ⟨l, rfl⟩
      fin_cases k <;> fin_cases l
      · simpa using polar_Qn_smul_two E n h01 1 1
      · simpa [u, v] using polar_Qn_smul_two E n h01 1 (bcTheta E)
      · simpa [u, w] using polar_Qn_smul_disjoint E n h02 h03 h12 h13 (a := 1) (b := 1)
      · simpa [u, v] using polar_Qn_smul_two E n h01 (bcTheta E) 1
      · simpa [v] using polar_Qn_smul_two E n h01 (bcTheta E) (bcTheta E)
      · simpa [v, w] using polar_Qn_smul_disjoint E n h02 h03 h12 h13
          (a := bcTheta E) (b := 1)
      · simpa [u, w] using polar_Qn_smul_disjoint E n h02.symm h12.symm h03.symm h13.symm
          (a := 1) (b := 1)
      · simpa [v, w] using polar_Qn_smul_disjoint E n h02.symm h12.symm h03.symm h13.symm
          (a := 1) (b := bcTheta E)
      · simpa [w] using polar_Qn_smul_two E n h23 1 1
    intro x hx
    exact CFSG.ClassicalGroups.Orthogonal.map_eq_zero_of_mem_span hS hB hx

theorem even_ruling_map_iff (E : QuadExt F K σ) (n : ℕ)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)} (hg : g ∈ rulingGroup E n)
    {M : Submodule K (Fin n ⊕ Fin n → K)} (hM : (quadPlusForm n K).IsLagrangian M) :
    Even (n - Module.finrank K ↥(M.map (bcLin E n g) ⊓ stdLag n K)) ↔
      Even (n - Module.finrank K ↥(M ⊓ stdLag n K)) := by
  obtain ⟨hgO, hEven⟩ := (mem_rulingGroup E n g).mp hg
  have hgQ : ∀ v, (quadPlusForm n K).Q (bcLin E n g v) = (quadPlusForm n K).Q v := by
    intro v
    rw [show (quadPlusForm n K).Q = ⇑(quadPlus n K) from (coe_quadPlus n K).symm]
    exact quadPlus_bcLin E n g
      (fun x => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO x) v
  have hdick : dicksonInvariant M (bcLin E n g) = 0 := by
    rw [← QuadForm.dicksonInvariant_eq (isLagrangian_stdLag n K) hM hgQ]
    rw [dicksonInvariant, finrank_stdLag, ZMod.natCast_eq_zero_iff_even]
    exact hEven
  have hEvenM : Even (Module.finrank K M -
      Module.finrank K ↥(M ⊓ M.map (bcLin E n g))) := by
    rw [dicksonInvariant, ZMod.natCast_eq_zero_iff_even] at hdick
    exact hdick
  have hMdim : Module.finrank K M = n := by
    have := hM.2
    rw [finrank_flipSpace] at this
    omega
  have hXY : Even (n - Module.finrank K ↥(M.map (bcLin E n g) ⊓ M)) := by
    rw [inf_comm]
    rwa [hMdim] at hEvenM
  have hpar := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm n K) (n := n)
    (finrank_flipSpace n K) (X := M.map (bcLin E n g)) (Y := M) (Z := stdLag n K)
    (hM.map hgQ) hM (isLagrangian_stdLag n K)
  have hpar' : Even ((n - Module.finrank K ↥(M.map (bcLin E n g) ⊓ M)) +
      ((n - Module.finrank K ↥(M ⊓ stdLag n K)) +
        (n - Module.finrank K ↥(M.map (bcLin E n g) ⊓ stdLag n K)))) := by
    rw [add_assoc] at hpar
    exact hpar
  rw [Nat.even_add] at hpar'
  have hbc : Even (n - Module.finrank K ↥(M ⊓ stdLag n K)) ↔
      Even (n - Module.finrank K ↥(M.map (bcLin E n g) ⊓ stdLag n K)) := by
    have := hpar'.mp hXY
    rwa [Nat.even_add] at this
  exact hbc.symm

theorem mem_rulingGroup_of_map_stdLag (E : QuadExt F K σ) (n : ℕ)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (h : (stdLag n K).map (bcLin E n g) = stdLag n K) : g ∈ rulingGroup E n := by
  rw [mem_rulingGroup E n g]
  refine ⟨hg, ?_⟩
  rw [h, inf_idem, finrank_stdLag]
  exact ⟨0, by simp⟩

theorem bcLin_stdLag_of_isKLinear (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) (hKl : ∀ (a : K) x, g (a • x) = a • g x)
    (x : Fin n → K) : bcLin E n g (Sum.elim x 0 : Fin n ⊕ Fin n → K) ∈ stdLag n K := by
  let w : Fin n ⊕ Fin n → K := bcLin E n g (Sum.elim x 0)
  have hjEmb : ∀ y : Fin n → K, jEmb E n y =
      (Sum.elim y 0 : Fin n ⊕ Fin n → K) + dFlip σ (Sum.elim y 0) := by
    intro y
    ext v
    cases v <;> simp [jEmb, dFlip]
  have hA : jEmb E n (g x) = w + dFlip σ w := by
    rw [← bcLin_jEmb E n g x, hjEmb x, map_add]
    have h1 : bcLin E n g (dFlip σ (Sum.elim x 0 : Fin n ⊕ Fin n → K)) = dFlip σ w := by
      rw [bcLin_dFlip]
    rw [h1]
  have hB : jEmb E n (g (bcTheta E • x)) =
      bcTheta E • w + σ (bcTheta E) • dFlip σ w := by
    rw [← bcLin_jEmb E n g (bcTheta E • x), hjEmb (bcTheta E • x), map_add]
    have h1 : bcLin E n g
        (dFlip σ (Sum.elim (bcTheta E • x) 0 : Fin n ⊕ Fin n → K)) =
        dFlip σ (bcLin E n g (Sum.elim (bcTheta E • x) 0)) := bcLin_dFlip E n g _
    have h2 : (Sum.elim (bcTheta E • x) 0 : Fin n ⊕ Fin n → K) =
        bcTheta E • (Sum.elim x 0 : Fin n ⊕ Fin n → K) := by
      ext v
      cases v <;> simp
    have h3 : bcLin E n g (Sum.elim (bcTheta E • x) 0 : Fin n ⊕ Fin n → K) =
        bcTheta E • w := by
      rw [h2, map_smul]
    rw [h1, h3, dFlip_smul]
  have h1 : ∀ j, (g x) j = w (Sum.inl j) + σ (w (Sum.inr j)) := by
    intro j
    have := congrFun hA (Sum.inl j)
    simpa [Pi.add_apply, dFlip] using this
  have h2 : ∀ j, bcTheta E * (g x) j =
      bcTheta E * w (Sum.inl j) + σ (bcTheta E) * σ (w (Sum.inr j)) := by
    intro j
    have := congrFun hB (Sum.inl j)
    simpa [hKl (bcTheta E) x, Pi.add_apply, Pi.smul_apply, dFlip, smul_eq_mul] using this
  have h3 : ∀ j, (bcTheta E + σ (bcTheta E)) * σ (w (Sum.inr j)) = 0 := by
    intro j
    have hθj := h2 j
    rw [h1 j] at hθj
    rw [mul_add] at hθj
    have h' : bcTheta E * w (Sum.inl j) + bcTheta E * σ (w (Sum.inr j)) =
        bcTheta E * w (Sum.inl j) + σ (bcTheta E) * σ (w (Sum.inr j)) := hθj
    have h'' := add_left_cancel h'
    rw [add_mul, h'', CharTwo.add_self_eq_zero]
  have hδ : bcTheta E + σ (bcTheta E) ≠ 0 := by
    intro h
    apply bcTheta_not_fixed E
    have h' : bcTheta E = -σ (bcTheta E) := add_eq_zero_iff_eq_neg.mp h
    rw [CharTwo.neg_eq] at h'
    exact h'.symm
  have hw : ∀ j, w (Sum.inr j) = 0 := by
    intro j
    have h := h3 j
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hδ
    · exact σ.injective (by simpa using h0)
  rw [stdLag, LinearMap.mem_ker]
  ext j
  simpa using hw j

theorem map_stdLag_bcLin_le_iff (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[F] (Fin n → K)) :
    (stdLag n K).map (bcLin E n g) ≤ stdLag n K ↔ ∀ (a : K) x, g (a • x) = a • g x := by
  constructor
  · intro hle
    let G : (Fin n → K) → (Fin n → K) :=
      fun x i => bcLin E n g (Sum.elim x 0 : Fin n ⊕ Fin n → K) (Sum.inl i)
    have hw : ∀ x, bcLin E n g (Sum.elim x 0 : Fin n ⊕ Fin n → K) =
        Sum.elim (G x) 0 := by
      intro x
      have hmem : bcLin E n g (Sum.elim x 0 : Fin n ⊕ Fin n → K) ∈ stdLag n K :=
        hle (Submodule.mem_map_of_mem (f := bcLin E n g) (by
          rw [stdLag, LinearMap.mem_ker]
          rfl))
      ext v
      cases v with
      | inl i => rfl
      | inr i =>
          have := congrFun (LinearMap.mem_ker.mp hmem) i
          simpa using this
    have hjEmb : ∀ y : Fin n → K, jEmb E n y =
        (Sum.elim y 0 : Fin n ⊕ Fin n → K) + dFlip σ (Sum.elim y 0) := by
      intro y
      ext v
      cases v <;> simp [jEmb, dFlip]
    have hgG : ∀ x, g x = G x := by
      intro x
      apply jEmb_injective E n
      rw [← bcLin_jEmb E n g x, hjEmb x, map_add, hw x, bcLin_dFlip, hw x,
        hjEmb (G x)]
    intro a x
    rw [hgG (a • x), hgG x]
    funext i
    dsimp only [G]
    rw [show (Sum.elim (a • x) 0 : Fin n ⊕ Fin n → K) =
        a • (Sum.elim x 0 : Fin n ⊕ Fin n → K) from by ext v; cases v <;> simp]
    rw [map_smul]
    rfl
  · intro hKl y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    have hv' : v = Sum.elim (fun i => v (Sum.inl i)) 0 := by
      ext w
      cases w with
      | inl i => rfl
      | inr i =>
          have := congrFun (LinearMap.mem_ker.mp hv) i
          simpa using this
    rw [hv']
    exact bcLin_stdLag_of_isKLinear E n g hKl _

theorem rulingGroup_eq_orthDerived (E : QuadExt F K σ) [Finite K] {n : ℕ} (hn : 4 ≤ n) :
    rulingGroup E n = CFSG.RankThree.Classical2.orthDerived (Qn E n) := by
  have hFinF : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have hF2 : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have hFinDim : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hNontriv : Nontrivial (Fin n → K) :=
    Module.nontrivial_of_finrank_pos (R := F) (by
      rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, E.finrank_eq]
      omega)
  have hQ := Qn_polarBilin_nondegenerate E n
  have hthree := exists_totallySingular_three E n hn
  have hΩeq : CFSG.RankThree.Classical2.orthDerived (Qn E n) =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (Qn E n) hQ := by
    exact le_antisymm (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ)
      (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hthree)
  have hΩindex : (CFSG.RankThree.Classical2.orthDerived (Qn E n)).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)) = 2 := by
    rw [hΩeq, CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup]
  have hrulingO : rulingGroup E n ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
    intro g hg
    exact ((mem_rulingGroup E n g).mp hg).1
  have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hker : (rulingHom E n).ker.index = 2 := by
    have hFact : Fact (Nat.card (Multiplicative (ZMod 2))).Prime :=
      ⟨by rw [hcard]; norm_num⟩
    have hne : (rulingHom E n).range ≠ ⊥ := by
      intro hbot
      have hmem : rulingHom E n
          ⟨tauAt E ⟨0, by omega⟩, tauAt_mem_orthogonalGroup E _⟩ ∈
          (rulingHom E n).range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot, rulingHom_tauAt] at hmem
      rw [ofAdd_eq_one] at hmem
      exact one_ne_zero hmem
    have htop : (rulingHom E n).range = ⊤ := by
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (rulingHom E n).range with h | h
      · exact absurd h hne
      · exact h
    rw [Subgroup.index_ker, htop]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans hcard
  have hsub : (rulingGroup E n).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)) = (rulingHom E n).ker := by
    rw [rulingGroup, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self (f :=
      (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)).subtype)
      (by rw [Subgroup.ker_subtype]; exact bot_le)
  have hrel : (rulingGroup E n).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)) = 2 := by
    rw [Subgroup.relIndex, hsub, hker]
  have hle := orthDerived_le_rulingGroup E n
  have hmul := Subgroup.relIndex_mul_relIndex
    (CFSG.RankThree.Classical2.orthDerived (Qn E n)) (rulingGroup E n)
    (TauCeti.QuadraticMap.orthogonalGroup (Qn E n)) hle hrulingO
  rw [hrel, hΩindex] at hmul
  have hx : (CFSG.RankThree.Classical2.orthDerived (Qn E n)).relIndex
      (rulingGroup E n) = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hx) hle

end CFSG.ClassicalInvolution.PhanDn
