module

public import CFSG.LieType.Chevalley.C2E6ExteriorCube
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public noncomputable section

namespace CFSG.LieType.Chevalley.ExteriorCube

open exteriorPower Set Matrix

variable {K : Type*} [Field K]

@[expose] def cubeEnd : Matrix (Fin 6) (Fin 6) K →* Module.End K (⋀[K]^3 (Fin 6 → K)) where
  toFun g := exteriorPower.map 3 (Matrix.toLin' g)
  map_one' := by
    rw [Matrix.toLin'_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [Matrix.toLin'_mul]
    exact exteriorPower.map_comp _ _

theorem cubeEnd_apply (g : Matrix (Fin 6) (Fin 6) K) :
    cubeEnd g = exteriorPower.map 3 (Matrix.toLin' g) := rfl

@[expose] def cubeHom :
    SpecialLinearGroup (Fin 6) K →* (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ :=
  (Units.map cubeEnd).comp SpecialLinearGroup.toGL

theorem coe_cubeHom (g : SpecialLinearGroup (Fin 6) K) :
    (cubeHom g : Module.End K (⋀[K]^3 (Fin 6 → K))) =
      exteriorPower.map 3 (Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) K)) := rfl

abbrev stdBasis : Module.Basis (Fin 6) K (Fin 6 → K) := Pi.basisFun K (Fin 6)

theorem stdBasis_coe : ⇑(stdBasis (K := K)) = fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K) := by
  funext i
  exact Pi.basisFun_apply K (Fin 6) i

abbrev single1 (j : Fin 6) : powersetCard (Fin 6) 1 := ⟨{j}, Finset.card_singleton j⟩

theorem basis_single1 (j : Fin 6) :
    stdBasis.ExteriorAlgebra ((single1 j : powersetCard (Fin 6) 1) : Finset (Fin 6)) =
      ExteriorAlgebra.ι K (Pi.single j (1 : K)) := by
  rw [ExteriorAlgebra.basis_apply_powersetCard, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one,
    Function.comp_apply, stdBasis_coe]
  congr 2
  exact Finset.mem_singleton.mp (enum_mem (single1 j) 0)

theorem basis_wedge (I : powersetCard (Fin 6) 3) :
    stdBasis.ExteriorAlgebra (I : Finset (Fin 6)) =
      ((wedgeBasis (R := K) I : ⋀[K]^3 (Fin 6 → K)) : ExteriorAlgebra K (Fin 6 → K)) := by
  rw [ExteriorAlgebra.basis_apply_powersetCard, wedgeBasis, ιMulti_family_apply_coe, stdBasis_coe]

theorem repr_single_mul_wedge (I : powersetCard (Fin 6) 3) (j : Fin 6) {r : Fin 6}
    (hr : r ∉ I.val) :
    stdBasis.ExteriorAlgebra.repr (ExteriorAlgebra.ι K (Pi.single j (1 : K)) *
        ((wedgeBasis (R := K) I : ⋀[K]^3 (Fin 6 → K)) : ExteriorAlgebra K (Fin 6 → K)))
        (insert r I.val) =
      if j = r then ((Equiv.Perm.sign (powersetCard.permOfDisjoint
        (s := single1 r) (t := I) (Finset.disjoint_singleton_left.mpr hr)) : ℤ) : K) else 0 := by
  rw [← basis_single1, ← basis_wedge]
  by_cases hjI : j ∈ I.val
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint _ _ _
      (Finset.not_disjoint_iff.mpr ⟨j, Finset.mem_singleton_self j, hjI⟩), map_zero,
      Finsupp.zero_apply, ite_eq_right]
    rintro rfl
    exact absurd hjI hr
  · have hd : Disjoint (single1 j).val I.val := Finset.disjoint_singleton_left.mpr hjI
    rw [ExteriorAlgebra.basis_mul_of_disjoint _ _ _ hd, Units.smul_def, map_zsmul,
      Module.Basis.repr_self, Finsupp.smul_apply]
    have hval : ((powersetCard.disjUnion hd : powersetCard (Fin 6) (1 + 3)) : Finset (Fin 6)) =
        insert j I.val := by
      rw [powersetCard.coe_disjUnion, Finset.disjUnion_eq_union, ← Finset.insert_eq]
    rw [hval]
    by_cases hjr : j = r
    · subst hjr
      rw [Finsupp.single_eq_same, ite_eq_left rfl, zsmul_eq_mul, mul_one]
    · rw [Finsupp.single_eq_of_ne, ite_eq_right hjr, smul_zero]
      intro h
      have : j ∈ insert r I.val := h ▸ Finset.mem_insert_self j I.val
      rcases Finset.mem_insert.mp this with h' | h'
      · exact hjr h'
      · exact hjI h'

theorem apply_eq_zero_of_mul_wedge_eq_zero {v : Fin 6 → K} {I : powersetCard (Fin 6) 3}
    (h : ExteriorAlgebra.ι K v *
        ((wedgeBasis (R := K) I : ⋀[K]^3 (Fin 6 → K)) : ExteriorAlgebra K (Fin 6 → K)) = 0)
    {r : Fin 6} (hr : r ∉ I.val) : v r = 0 := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : K) : Fin 6 → K) := by
    funext x
    rw [Finset.sum_apply]
    simp [Pi.single_apply]
  have h1 := congrArg (fun x => stdBasis.ExteriorAlgebra.repr x (insert r I.val)) h
  simp only [map_zero, Finsupp.zero_apply] at h1
  rw [hv, map_sum, Finset.sum_mul, map_sum, Finsupp.finsetSum_apply] at h1
  simp only [map_smul, smul_mul_assoc, Finsupp.smul_apply, repr_single_mul_wedge I _ hr,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  have hsign : ((Equiv.Perm.sign (powersetCard.permOfDisjoint (s := single1 r) (t := I)
      (Finset.disjoint_singleton_left.mpr hr)) : ℤ) : K) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (powersetCard.permOfDisjoint (s := single1 r)
      (t := I) (Finset.disjoint_singleton_left.mpr hr))) with hs | hs <;> rw [hs] <;> simp
  exact (mul_eq_zero.mp h1).resolve_right hsign

theorem apply_single_eq_zero_of_map_eq_id {f : (Fin 6 → K) →ₗ[K] (Fin 6 → K)}
    (hf : exteriorPower.map 3 f = LinearMap.id) (I : powersetCard (Fin 6) 3) {a r : Fin 6}
    (ha : a ∈ I.val) (hr : r ∉ I.val) : f (Pi.single a 1) r = 0 := by
  refine apply_eq_zero_of_mul_wedge_eq_zero ?_ hr
  have hw : ((wedgeBasis (R := K) I : ⋀[K]^3 (Fin 6 → K)) : ExteriorAlgebra K (Fin 6 → K)) =
      ExteriorAlgebra.ιMulti K 3 (f ∘ (fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I) := by
    have := congrArg (fun x : ⋀[K]^3 (Fin 6 → K) => (x : ExteriorAlgebra K (Fin 6 → K)))
      (LinearMap.congr_fun hf (wedgeBasis I))
    simp only [LinearMap.id_apply] at this
    rw [← this, wedgeBasis, map_apply_ιMulti_family, ιMulti_family_apply_coe]
    rfl
  rw [hw]
  obtain ⟨k, hk⟩ := exists_enum_eq ha
  set w : Fin 3 → Fin 6 → K := f ∘ (fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I
  set v4 : Fin 4 → Fin 6 → K := Fin.cons (f (Pi.single a 1)) w
  have hcons : ExteriorAlgebra.ι K (f (Pi.single a 1)) * ExteriorAlgebra.ιMulti K 3 w =
      ExteriorAlgebra.ιMulti K 4 v4 := by
    rw [ExteriorAlgebra.ιMulti_succ_apply (n := 3)]
    rfl
  rw [hcons]
  refine ExteriorAlgebra.ιMulti_eq_zero_of_not_inj fun hinj => ?_
  have h0 : v4 0 = v4 k.succ := by
    change f (Pi.single a 1) = w k
    simp only [w, Function.comp_apply, hk]
  exact Fin.succ_ne_zero k (hinj h0).symm

theorem exists_triple (a r : Fin 6) (h : a ≠ r) :
    ∃ I : powersetCard (Fin 6) 3, a ∈ I.val ∧ r ∉ I.val := by
  have : ∀ a r : Fin 6, a ≠ r → ∃ I : Finset (Fin 6), I.card = 3 ∧ a ∈ I ∧ r ∉ I := by
    decide
  obtain ⟨I, hI, haI, hrI⟩ := this a r h
  exact ⟨⟨I, hI⟩, haI, hrI⟩

theorem cubeEnd_smul_one (l : K) :
    cubeEnd (l • (1 : Matrix (Fin 6) (Fin 6) K)) = (l ^ 3) • (1 : Module.End K _) := by
  rw [cubeEnd_apply]
  refine ((Pi.basisFun K (Fin 6)).exteriorPower 3).ext fun I => ?_
  rw [← wedgeBasis_eq_basis, wedgeBasis, map_apply_ιMulti_family, LinearMap.smul_apply,
    Module.End.one_apply]
  have : (Matrix.toLin' (l • (1 : Matrix (Fin 6) (Fin 6) K)) ∘
      fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) = fun i => l • (Pi.single i 1 : Fin 6 → K) := by
    funext i
    rw [Function.comp_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [this, exteriorPower.ιMulti_family, exteriorPower.ιMulti_family]
  have h2 : ((fun i : Fin 6 => l • (Pi.single i 1 : Fin 6 → K)) ∘ enum I) =
      fun k => l • ((fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I) k := rfl
  rw [h2, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem cubeEnd_eq_one_iff (g : Matrix (Fin 6) (Fin 6) K) :
    cubeEnd g = 1 ↔ ∃ l : K, l ^ 3 = 1 ∧ g = l • 1 := by
  constructor
  · intro hg
    have hf : exteriorPower.map 3 (Matrix.toLin' g) = LinearMap.id := hg
    have hcol : ∀ a r : Fin 6, Matrix.toLin' g (Pi.single a 1) r = g r a := fun a r => by
      rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
      rfl
    have hdiag : ∀ a r : Fin 6, a ≠ r → g r a = 0 := fun a r h => by
      obtain ⟨I, haI, hrI⟩ := exists_triple a r h
      rw [← hcol]
      exact apply_single_eq_zero_of_map_eq_id hf I haI hrI
    have hcube : ∀ I : powersetCard (Fin 6) 3, ∏ k : Fin 3, g (enum I k) (enum I k) = 1 := by
      intro I
      have h1 := LinearMap.congr_fun hf (wedgeBasis I)
      rw [wedgeBasis, map_apply_ιMulti_family, LinearMap.id_apply, exteriorPower.ιMulti_family,
        exteriorPower.ιMulti_family] at h1
      have h2 : ((Matrix.toLin' g ∘ fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I) =
          fun k => g (enum I k) (enum I k) •
            ((fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I) k := by
        funext k
        ext r
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        rw [hcol]
        by_cases hr : r = enum I k
        · subst hr
          simp
        · rw [hdiag _ _ (Ne.symm hr), Pi.single_eq_of_ne hr, mul_zero]
      rw [h2, AlternatingMap.map_smul_univ] at h1
      have hne : exteriorPower.ιMulti K 3
          ((fun i : Fin 6 => (Pi.single i 1 : Fin 6 → K)) ∘ enum I) ≠ 0 := by
        have := ((Pi.basisFun K (Fin 6)).exteriorPower 3).ne_zero I
        rwa [← wedgeBasis_eq_basis] at this
      exact smul_left_injective K hne (h1.trans (one_smul K _).symm)
    have hprod : ∀ I : powersetCard (Fin 6) 3,
        ∏ k : Fin 3, g (enum I k) (enum I k) = ∏ i ∈ I.val, g i i := fun I =>
      Finset.prod_bij (fun k _ => enum I k) (fun k _ => enum_mem I k)
        (fun _ _ _ _ h => (enum I).injective h)
        (fun i hi => let ⟨k, hk⟩ := exists_enum_eq hi; ⟨k, Finset.mem_univ _, hk⟩)
        (fun _ _ => rfl)
    have heq : ∀ a d : Fin 6, g a a = g d d := by
      have key : ∀ a d : Fin 6, a ≠ d → ∃ I J : Finset (Fin 6), I.card = 3 ∧ J.card = 3 ∧
          I.erase a = J.erase d ∧ a ∈ I ∧ d ∈ J := by decide
      intro a d
      by_cases had : a = d
      · rw [had]
      obtain ⟨I, J, hIc, hJc, hIJ, haI, hdJ⟩ := key a d had
      have hI := hcube ⟨I, hIc⟩
      have hJ := hcube ⟨J, hJc⟩
      rw [hprod] at hI hJ
      rw [← Finset.mul_prod_erase _ _ haI] at hI
      rw [← Finset.mul_prod_erase _ _ hdJ, ← hIJ] at hJ
      have hne : ∏ i ∈ I.erase a, g i i ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hI
        exact zero_ne_one hI
      exact mul_right_cancel₀ hne (hI.trans hJ.symm)
    refine ⟨g 0 0, ?_, ?_⟩
    · set I0 : powersetCard (Fin 6) 3 :=
        ⟨{0, 1, 2}, show ({0, 1, 2} : Finset (Fin 6)).card = 3 by decide⟩
      have h := hcube I0
      have hprod0 : ∏ k : Fin 3, g (enum I0 k) (enum I0 k) = g 0 0 ^ 3 := by
        rw [Finset.prod_congr rfl fun k _ => heq _ 0, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      rw [← hprod0, h]
    · ext r a
      rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases hra : r = a
      · subst hra
        rw [ite_eq_left rfl, mul_one, heq]
      · rw [ite_eq_right hra, mul_zero, hdiag _ _ (Ne.symm hra)]
  · rintro ⟨l, hl, rfl⟩
    rw [cubeEnd_smul_one, hl, one_smul]

theorem cubeHom_eq_one_iff (g : SpecialLinearGroup (Fin 6) K) :
    cubeHom g = 1 ↔ ∃ l : K, l ^ 3 = 1 ∧ (g : Matrix (Fin 6) (Fin 6) K) = l • 1 := by
  rw [← cubeEnd_eq_one_iff, ← Units.val_eq_one]
  rfl

end CFSG.LieType.Chevalley.ExteriorCube
