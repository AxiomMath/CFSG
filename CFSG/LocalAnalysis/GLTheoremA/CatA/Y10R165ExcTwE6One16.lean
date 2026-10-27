module
public import CFSG.LieType.Chevalley.E6A5CubeImages
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6One8

public section
namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6A5Cube
open CFSG.LocalAnalysis.ComponentInitial CFSG.SeitzReduction.E6Pilot
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6One CFSG.LieType.Steinberg.Exceptional
open CFSG.LieType.Chevalley.ExteriorCube


private theorem modelLin_diagonal_hImage {E : Type} [Field E] (b : Fin 6 → Eˣ)
    (j : Fin 6) :
    modelLin (Matrix.diagonal fun i => (b i : E))
        (Matrix.diagonal fun i => ((b i)⁻¹ : E)) (hImage (E := E) (j)) =
      hImage (E := E) (j) := by
  have hx : hImage (E := E) j =
      (Matrix.diagonal (fun i => (diagCoeff j i : E)), 0, 0, 0, 0) := rfl
  rw [hx, modelLin_apply]
  simp only [mul_zero, map_zero]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  have hfun : (fun i => (b i : E) * (diagCoeff j i : E) * ((b i)⁻¹ : E)) =
      fun i => (diagCoeff j i : E) := by
    funext i
    rw [mul_comm ((b i : E)) ((diagCoeff j i : E))]
    exact mul_inv_cancel_right₀ (Units.ne_zero (b i)) ((diagCoeff j i : E))
  rw [hfun]

private theorem modelLin_diagonal_rootImage_matRoot {E : Type} [Field E] (b : Fin 6 → Eˣ)
    {a b' : Fin 6} (hab : a ≠ b') :
    modelLin (Matrix.diagonal fun i => (b i : E))
        (Matrix.diagonal fun i => ((b i)⁻¹ : E)) (rootImage (E := E) (matRoot a b')) =
      ((b a * (b b')⁻¹ : Eˣ) : E) • rootImage (E := E) (matRoot a b') := by
  rw [rootImage_matRoot hab, modelLin_apply]
  simp only [mul_zero, map_zero]
  have hmat : Matrix.diagonal (fun i => (b i : E)) * Matrix.single a b' 1 *
      Matrix.diagonal (fun i => ((b i)⁻¹ : E)) =
      ((b a * (b b')⁻¹ : Eˣ) : E) • Matrix.single a b' 1 := by
    rw [diagonal_mul_single', single_mul_diagonal']
    rw [mul_one]
    ext i j
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hmat]
  simp

private theorem modelLin_diagonal_rootImage_lineP {E : Type} [Field E] (b : Fin 6 → Eˣ) :
    modelLin (Matrix.diagonal fun i => (b i : E))
        (Matrix.diagonal fun i => ((b i)⁻¹ : E)) (rootImage (E := E) e6HighestRoot) =
      rootImage (E := E) e6HighestRoot := by
  rw [rootImage_e6HighestRoot, modelLin_apply]
  simp

private theorem modelLin_diagonal_rootImage_lineN {E : Type} [Field E] (b : Fin 6 → Eˣ) :
    modelLin (Matrix.diagonal fun i => (b i : E))
        (Matrix.diagonal fun i => ((b i)⁻¹ : E)) (rootImage (E := E) (-e6HighestRoot)) =
      rootImage (E := E) (-e6HighestRoot) := by
  rw [rootImage_neg_e6HighestRoot, modelLin_apply]
  simp

private theorem modelLin_diagonal_rootImage_cubeP {E : Type} [Field E] (b : Fin 6 → Eˣ)
    (S : Set.powersetCard (Fin 6) 3) :
    modelLin (Matrix.diagonal fun i => (b i : E))
        (Matrix.diagonal fun i => ((b i)⁻¹ : E)) (rootImage (E := E) (cubeRoot S.1)) =
      ((∏ i ∈ S.1, b i : Eˣ) : E) • rootImage (E := E) (cubeRoot S.1) := by
  rw [rootImage_cubeRoot, modelLin_apply]
  simp only [map_zero]
  have hcube : (exteriorPower.map 3 (Matrix.toLin' (Matrix.diagonal fun i => (b i : E))))
      (cubeBasis S) = ((∏ i ∈ S.1, b i : Eˣ) : E) • cubeBasis S := by
    rw [show cubeBasis S = wedgeBasis (R := E) S from (wedgeBasis_eq_basis S).symm]
    change cubeEnd (Matrix.diagonal fun i => (b i : E)) (wedgeBasis (R := E) S) =
      ((∏ i ∈ S.1, b i : Eˣ) : E) • wedgeBasis (R := E) S
    rw [cubeEnd_diagonal_wedgeBasis]
    congr 1
    simp
  rw [hcube]
  simp

private theorem modelLin_diagonal_rootImage_cubeN {E : Type} [Field E] (b : Fin 6 → Eˣ)
    (S : Set.powersetCard (Fin 6) 3) :
    modelLin (Matrix.diagonal fun i => (b i : E))
        (Matrix.diagonal fun i => ((b i)⁻¹ : E)) (rootImage (E := E) (-cubeRoot S.1ᶜ)) =
      ((∏ i ∈ S.1, b i : Eˣ) : E) • rootImage (E := E) (-cubeRoot S.1ᶜ) := by
  rw [rootImage_neg_cubeRoot, modelLin_apply]
  simp only [map_zero]
  have hcube : (exteriorPower.map 3 (Matrix.toLin' (Matrix.diagonal fun i => (b i : E))))
      (cubeBasis S) = ((∏ i ∈ S.1, b i : Eˣ) : E) • cubeBasis S := by
    rw [show cubeBasis S = wedgeBasis (R := E) S from (wedgeBasis_eq_basis S).symm]
    change cubeEnd (Matrix.diagonal fun i => (b i : E)) (wedgeBasis (R := E) S) =
      ((∏ i ∈ S.1, b i : Eˣ) : E) • wedgeBasis (R := E) S
    rw [cubeEnd_diagonal_wedgeBasis]
    congr 1
    simp
  rw [hcube]
  simp

theorem realize_diagonal_mem_diagonalGroup {E : Type} [Field E] (h2 : (2 : E) = 0)
    (B : Matrix.SpecialLinearGroup (Fin 6) E) (b : Fin 6 → Eˣ)
    (hB : ((B : Matrix (Fin 6) (Fin 6) E)) = Matrix.diagonal fun i => (b i : E))
    (hB' : (((B⁻¹ : Matrix.SpecialLinearGroup (Fin 6) E)) : Matrix (Fin 6) (Fin 6) E) =
      Matrix.diagonal fun i => ((b i)⁻¹ : E)) :
    E6GraphLevi.realize h2 B ∈ (diagonalGroup : Subgroup (ModGL TwistTag.E6.tag E)) := by
  refine ⟨?_, ?_⟩
  · intro j
    rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
      toModel_hVec, modelLin_diagonal_hImage (E := E) (b := b) (j := j)]
    exact fromModel_hImage (E := E) h2 j
  · intro α hα
    rcases root_cases α (mem_rootFinset.2 hα) with ⟨a, b', hab, rfl⟩ | rfl | rfl |
      ⟨S, hS⟩ | ⟨S, hS⟩
    · refine ⟨b a * (b b')⁻¹, ?_⟩
      rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
        toModel_rootVec, modelLin_diagonal_rootImage_matRoot (E := E) (b := b) hab,
        LinearMap.map_smul, fromModel_rootImage (isRoot_matRoot hab)]
    · refine ⟨1, ?_⟩
      rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
        toModel_rootVec, modelLin_diagonal_rootImage_lineP (E := E) (b := b),
        fromModel_rootImage isRoot_e6HighestRoot]
      simp
    · refine ⟨1, ?_⟩
      rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
        toModel_rootVec, modelLin_diagonal_rootImage_lineN (E := E) (b := b),
        fromModel_rootImage (IsRoot.neg isRoot_e6HighestRoot)]
      simp
    · refine ⟨∏ i ∈ S, b i, ?_⟩
      rw [← hS.2]
      have hkey := modelLin_diagonal_rootImage_cubeP (E := E) (b := b)
        (⟨S, hS.1⟩ : Set.powersetCard (Fin 6) 3)
      rw [show (⟨S, hS.1⟩ : Set.powersetCard (Fin 6) 3).1 = S from rfl] at hkey
      rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
        toModel_rootVec, hkey, LinearMap.map_smul,
        fromModel_rootImage (isRoot_cubeRoot hS.1)]
    · refine ⟨∏ i ∈ S, b i, ?_⟩
      rw [← hS.2]
      have hkey := modelLin_diagonal_rootImage_cubeN (E := E) (b := b)
        (⟨S, hS.1⟩ : Set.powersetCard (Fin 6) 3)
      rw [show (⟨S, hS.1⟩ : Set.powersetCard (Fin 6) 3).1 = S from rfl] at hkey
      rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
        toModel_rootVec, hkey, LinearMap.map_smul,
        fromModel_rootImage (IsRoot.neg (isRoot_cubeRoot (card_compl_three hS.1)))]


theorem realize_diagonal_mem_torusGroup {E : Type} [Field E] (h2 : (2 : E) = 0)
    (B : Matrix.SpecialLinearGroup (Fin 6) E) (b : Fin 6 → Eˣ)
    (hB : ((B : Matrix (Fin 6) (Fin 6) E)) = Matrix.diagonal fun i => (b i : E))
    (hB' : (((B⁻¹ : Matrix.SpecialLinearGroup (Fin 6) E)) : Matrix (Fin 6) (Fin 6) E) =
      Matrix.diagonal fun i => ((b i)⁻¹ : E)) :
    E6GraphLevi.realize h2 B ∈ (torusGroup TwistTag.E6.tag E :
      Subgroup (ModGL TwistTag.E6.tag E)) := by
  refine CFSG.SeitzReduction.E6Pilot.mem_torusGroup_of_mem_adjointGroup_of_mem_diagonalGroup ?_ ?_
  · have hsub : E6GraphLevi.realize h2 B ∈
        subsystemGroup TwistTag.E6.tag E E6GraphLevi.setA := by
      rw [← E6GraphLevi.range_realize h2]
      exact ⟨B, rfl⟩
    exact E6GraphLevi.subsystemGroup_le_adjointGroup hsub
  · exact realize_diagonal_mem_diagonalGroup h2 B b hB hB'

theorem realize_diagonal_eq_rootDiagUnit {E : Type} [Field E] (h2 : (2 : E) = 0)
    (B : Matrix.SpecialLinearGroup (Fin 6) E) (b : Fin 6 → Eˣ)
    (hB : ((B : Matrix (Fin 6) (Fin 6) E)) = Matrix.diagonal fun i => (b i : E)) :
    E6GraphLevi.realize h2 B =
      rootDiagUnit .E6 ![b 0 / b 1, b 3 * b 4 * b 5, b 1 / b 2, b 2 / b 3, b 3 / b 4,
        b 4 / b 5] := by
  classical
  have hdet : (∏ i : Fin 6, (b i : E)) = 1 := by
    have h := B.2
    rwa [hB, Matrix.det_diagonal] at h
  have hB' : (((B⁻¹ : Matrix.SpecialLinearGroup (Fin 6) E)) :
      Matrix (Fin 6) (Fin 6) E) = Matrix.diagonal fun i => ((b i)⁻¹ : E) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hB, Matrix.adjugate_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hprod : (∏ x ∈ Finset.univ.erase i, (b x : E)) = ((b i)⁻¹ : E) := by
        apply eq_inv_of_mul_eq_one_right
        rw [Finset.mul_prod_erase Finset.univ (fun x : Fin 6 => (b x : E))
          (Finset.mem_univ i)]
        exact hdet
      simpa [Matrix.diagonal_apply_eq, hprod]
    · simp [Matrix.diagonal_apply_ne, hij]
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (realize_diagonal_mem_torusGroup h2 B b hB hB')
  have hpath : ∀ t : Fin 5, a (pathIdx t) = b t.castSucc / b t.succ := by
    intro t
    have hv := congrArg (fun g : ModGL TwistTag.E6.tag E =>
        (g : Module.End E (RootModule TwistTag.E6.tag E))
          (rootVec TwistTag.E6.tag E (Pi.single (pathIdx t) 1))) ha
    rw [← matRoot_adjacent t] at hv
    rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
      toModel_rootVec, modelLin_diagonal_rootImage_matRoot (E := E) (b := b)
        (castSucc_ne_succ t), LinearMap.map_smul,
      fromModel_rootImage (isRoot_matRoot (castSucc_ne_succ t))] at hv
    rw [show ((rootDiagUnit TwistTag.E6.tag a : ModGL TwistTag.E6.tag E) :
        Module.End E (RootModule TwistTag.E6.tag E)) = rootDiag a from rfl,
      rootDiag_rootVec a (isRoot_matRoot (castSucc_ne_succ t))] at hv
    have hchar : rootChar a (matRoot t.castSucc t.succ) = a (pathIdx t) := by
      rw [matRoot_adjacent t]
      simpa using rootChar_nsmul_single a (pathIdx t) 1
    rw [hchar] at hv
    have hne : rootVec TwistTag.E6.tag E (matRoot t.castSucc t.succ) ≠ 0 := by
      rw [E6GraphLevi.rootVec_eq_single' (isRoot_matRoot (castSucc_ne_succ t))]
      exact Finsupp.single_ne_zero.2 one_ne_zero
    have h := Units.ext (smul_left_injective E hne hv)
    simpa [div_eq_mul_inv] using h.symm
  have hoff : a 1 = b 3 * b 4 * b 5 := by
    let S : Set.powersetCard (Fin 6) 3 :=
      ⟨{3, 4, 5}, Set.powersetCard.mem_iff.2 (by decide)⟩
    have hcube : cubeRoot S.1 =
        (Pi.single (1 : Fin TwistTag.E6.tag.rank) (1 : ℤ)) := by
      change cubeRoot ({3, 4, 5} : Finset (Fin 6)) = _
      decide +kernel
    have hv := congrArg (fun g : ModGL TwistTag.E6.tag E =>
        (g : Module.End E (RootModule TwistTag.E6.tag E))
          (rootVec TwistTag.E6.tag E (Pi.single (1 : Fin TwistTag.E6.tag.rank) 1))) ha
    rw [← hcube] at hv
    rw [E6GraphLevi.coe_realize, LinearMap.comp_apply, LinearMap.comp_apply, hB, hB',
      toModel_rootVec, modelLin_diagonal_rootImage_cubeP (E := E) (b := b) S,
      LinearMap.map_smul, fromModel_rootImage (isRoot_cubeRoot S.2)] at hv
    rw [show ((rootDiagUnit TwistTag.E6.tag a : ModGL TwistTag.E6.tag E) :
        Module.End E (RootModule TwistTag.E6.tag E)) = rootDiag a from rfl,
      rootDiag_rootVec a (isRoot_cubeRoot S.2)] at hv
    have hprod : (∏ i ∈ S.1, b i) = b 3 * b 4 * b 5 := by
      change (∏ i ∈ ({3, 4, 5} : Finset (Fin 6)), b i) = b 3 * b 4 * b 5
      rw [show ({3, 4, 5} : Finset (Fin 6)) = insert 3 (insert 4 {5}) by decide]
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
      simp [mul_assoc]
    have hchar : rootChar a (cubeRoot S.1) = a 1 := by
      rw [hcube]
      simpa using rootChar_nsmul_single a 1 1
    rw [hprod, hchar] at hv
    have hne : rootVec TwistTag.E6.tag E (cubeRoot S.1) ≠ 0 := by
      rw [E6GraphLevi.rootVec_eq_single' (isRoot_cubeRoot S.2)]
      exact Finsupp.single_ne_zero.2 one_ne_zero
    have h := Units.ext (smul_left_injective E hne hv)
    simpa using h.symm
  let c : Fin TwistTag.E6.tag.rank → Eˣ :=
    ![b 0 / b 1, b 3 * b 4 * b 5, b 1 / b 2, b 2 / b 3, b 3 / b 4, b 4 / b 5]
  have hc : a = c := by
    funext i
    fin_cases i
    · change a 0 = b 0 / b 1
      exact hpath 0
    · change a 1 = b 3 * b 4 * b 5
      exact hoff
    · change a 2 = b 1 / b 2
      exact hpath 1
    · change a 3 = b 2 / b 3
      exact hpath 2
    · change a 4 = b 3 / b 4
      exact hpath 3
    · change a 5 = b 4 / b 5
      exact hpath 4
  simpa [c, TwistTag.tag] using ha.trans (congrArg (rootDiagUnit TwistTag.E6.tag) hc)

theorem realize_diagonal_eq_rootDiagUnit_cubic {E : Type} [Field E] (h2 : (2 : E) = 0)
    (B : Matrix.SpecialLinearGroup (Fin 6) E) (c d : Eˣ)
    (hB : ((B : Matrix (Fin 6) (Fin 6) E)) =
      Matrix.diagonal fun i => ((![c, c, c, d, d, d] : Fin 6 → Eˣ) i : E))
    (hc : c ^ 3 = 1) (hd : d ^ 3 = 1) :
    E6GraphLevi.realize h2 B =
      rootDiagUnit .E6 ![1, 1, 1, c / d, 1, 1] := by
  have h := realize_diagonal_eq_rootDiagUnit (E := E) h2 B
    (![c, c, c, d, d, d] : Fin 6 → Eˣ) hB
  rw [h]
  refine congrArg (rootDiagUnit Tag.E6) ?_
  funext i
  fin_cases i
  · change c / c = 1
    simp
  · change d * d * d = 1
    rw [← pow_three', hd]
  · change c / c = 1
    simp
  · change c / d = c / d
    rfl
  · change d / d = 1
    simp
  · change d / d = 1
    simp

theorem gramRealize_r3Hom_mem_torusGroup {f p : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) [NeZero p] (ζ : Kˣ) (hζ : orderOf ζ = p)
    (hζbar : h.bar (ζ : K) = ζ)
    (x : Multiplicative (ZMod p × ZMod p × ZMod p)) :
    gramRealize h (r3Hom h p ζ hζ hζbar x) ∈
      (torusGroup TwistTag.E6.tag K : Subgroup (ModGL TwistTag.E6.tag K)) := by
  have h2 : (2 : K) = 0 := two_eq_zero_of_unitaryFieldData h
  let b : Fin 6 → Kˣ := fun i => ![
    ζ ^ (x.toAdd.1).val, ζ ^ (x.toAdd.2.1).val, ζ ^ (x.toAdd.2.2).val,
    (ζ ^ (x.toAdd.2.2).val)⁻¹, (ζ ^ (x.toAdd.2.1).val)⁻¹, (ζ ^ (x.toAdd.1).val)⁻¹] i
  let B : Matrix.SpecialLinearGroup (Fin 6) K := gramToSL h (r3Hom h p ζ hζ hζbar x)
  have hB : (B : Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal fun i => (b i : K) := by
    dsimp only [B]
    rw [coe_gramToSL]
    rw [show ((r3Hom h p ζ hζ hζbar x : ↥(gramSU h
        ((antiIdGL K : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))) : GL (Fin 6) K) =
        diag3 (ζ ^ (x.toAdd.1).val) (ζ ^ (x.toAdd.2.1).val)
          (ζ ^ (x.toAdd.2.2).val) from rfl, coe_diag3]
    congr 1
    funext i
    fin_cases i <;> rfl
  let D : Matrix.SpecialLinearGroup (Fin 6) K :=
    ⟨Matrix.diagonal fun i => ((b i)⁻¹ : K), by
      rw [Matrix.det_diagonal, Fin.prod_univ_six]
      simp [b]⟩
  have hmul : B * D = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hB,
      Matrix.diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst hij
      simp [b]
    · simp [Matrix.diagonal_apply_ne, Matrix.one_apply_ne, hij]
  have hB' : (((B⁻¹ : Matrix.SpecialLinearGroup (Fin 6) K)) :
      Matrix (Fin 6) (Fin 6) K) = Matrix.diagonal fun i => ((b i)⁻¹ : K) := by
    have hinv : B⁻¹ = D := (eq_inv_of_mul_eq_one_right hmul).symm
    rw [hinv]
  rw [gramRealize_apply]
  exact realize_diagonal_mem_torusGroup h2 B b hB hB'
theorem R3Levi_le_torusGroup {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K →+* K} (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    R3Levi h p hp hp2 ζ hζ hζbar hσ ≤ torusGroup TwistTag.E6.tag K := by
  intro y hy
  rw [R3Levi] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [R3bar, r3ToP, MonoidHom.range_eq_map] at hz
  obtain ⟨x, -, rfl⟩ := hz
  change ((su6LeviEquiv h hσ ((QuotientGroup.mk' (N6 h)) (r3Hom h p ζ hζ hζbar x)) :
    su6Levi σ) : ModGL TwistTag.E6.tag K) ∈ torusGroup TwistTag.E6.tag K
  rw [coe_su6LeviEquiv_mk h hσ (r3Hom h p ζ hζ hζbar x)]
  exact gramRealize_r3Hom_mem_torusGroup h ζ hζ hζbar x

theorem thetaTorusP_le_graphFixedRootTorus {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k (GaloisField 2 (2 * f))] (hk : Nat.card k = 2 ^ f) (t : kˣ)
    (hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f) :
    ∀ x ∈ thetaTorusP (f := f) t,
      (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
        graphFixedRootTorus TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := by
  intro x hx
  have hxW : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈ W0 f k :=
    Subgroup.mem_subgroupOf.mp (thetaTorusP_le_thetaTorus hf hk t hx)
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hxW
  have hxC : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) := x.2
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hxC⟩
  · have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharP.cast_eq_zero _ 2
    have hadj := CFSG.LieType.Chevalley.E6EvenRootTorus.thetaTorusHom_mem_adjointGroup
      (k := GaloisField 2 (2 * f)) h2
      (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom a)
    rw [E6GraphLevi.thetaTorusHom_apply, rootTorusSL2_e6HighestRoot] at hadj
    rw [← ha, MonoidHom.comp_apply, E6GraphLevi.thetaTorusHom_apply,
      rootTorusSL2_e6HighestRoot]
    exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup _ hadj
  · exact (graphFixedRootGroup_le (t := TwistTag.E6)
      (K := GaloisField 2 (2 * f)) (σ := frobQ 2 f)) hxC

theorem R3Levi_le_graphFixedRootTorus {f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData 2 f K) (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    {σ : K →+* K} (ζ : Kˣ) (hζ : orderOf ζ = p) (hζbar : h.bar (ζ : K) = ζ)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    ∀ x ∈ R3Levi h p hp hp2 ζ hζ hζbar hσ,
      (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootTorus TwistTag.E6 K σ := by
  intro x hx
  have hxC : (x : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    R3Levi_le_C0 h p hp hp2 ζ hζ hζbar hσ hx
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, hxC⟩
  · exact R3Levi_le_torusGroup h p hp hp2 ζ hζ hζbar hσ hx
  · exact (graphFixedRootGroup_le (t := TwistTag.E6) (K := K) (σ := σ)) hxC

theorem range_twE6ThreeFrameHom_eq_model {f : ℕ} (hf : 1 ≤ f) (h3 : ¬ 3 ∣ 2 ^ f + 1)
    {k : Type} [Field k] [Finite k] [Algebra k (GaloisField 2 (2 * f))]
    (hk : Nat.card k = 2 ^ f)
    (h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)))
    {ζ : (GaloisField 2 (2 * f))ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3)
    (hζbar : h.bar (ζ : GaloisField 2 (2 * f)) = (ζ : GaloisField 2 (2 * f)))
    {t : kˣ} (ht : orderOf t = 3)
    (hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f) :
    (CFSG.StandardType.ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range =
      thetaTorusP (f := f) t ⊔
        (R3Levi h 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).subgroupOf (C0 f) := by
  have hsup : thetaTorusP (f := f) t ⊔
      (R3Levi h 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).subgroupOf (C0 f) ≤
      (CFSG.StandardType.ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range := by
    refine sup_le ?_ ?_
    · intro x hx
      exact CFSG.StandardType.ExcFrames.mem_range_twE6ThreeFrameHom_of_mem_torus
        hf h3 hζo hζ
        (thetaTorusP_le_graphFixedRootTorus hf hk t hσ x hx)
        ((isElemAbelian_thetaTorusP hf hk (by norm_num : Nat.Prime 3) ht).2 x hx)
    · intro x hx
      have hxR : (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) ∈
          R3Levi h 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ :=
        Subgroup.mem_subgroupOf.mp hx
      have hx3 : x ^ 3 = 1 := Subtype.ext (by
        simpa using (isElemAbelian_R3Levi h 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).2
          (x : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) hxR)
      exact CFSG.StandardType.ExcFrames.mem_range_twE6ThreeFrameHom_of_mem_torus
        hf h3 hζo hζ
        (R3Levi_le_graphFixedRootTorus h 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ x hxR)
        hx3
  have h4 : Tag.F4.rank = 4 := by decide
  have hdom : Nat.card (Multiplicative (Fin Tag.F4.rank → ZMod 3)) = 3 ^ 4 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_pi, h4]
    simp [Nat.card_zmod]
  have hRange : Nat.card ↥(CFSG.StandardType.ExcFrames.twE6ThreeFrameHom hf h3 ζ hζ).range =
      3 ^ 4 := by
    rw [← hdom]
    exact (Nat.card_congr (MonoidHom.ofInjective
      (CFSG.StandardType.ExcFrames.twE6ThreeFrameHom_injective hf h3 hζo hζ)).toEquiv).symm
  have hAcard : Nat.card ↥(thetaTorusP (f := f) t ⊔
      (R3Levi h 3 (by norm_num) (by norm_num) ζ hζo hζbar hσ).subgroupOf (C0 f)) = 3 ^ 4 :=
    card_thetaTorusP_sup_R3Levi (p := 3) hf hk h (by norm_num) (by norm_num) hζo hζbar ht hσ
  refine (Subgroup.eq_of_le_of_card_ge hsup ?_).symm
  rw [hRange, hAcard]
