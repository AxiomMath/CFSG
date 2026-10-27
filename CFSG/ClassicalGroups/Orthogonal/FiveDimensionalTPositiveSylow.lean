module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.GroupTheory.PowMemSupOfPGroup
public import CFSG.GH74.SmallRanks.Basic
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.RingTheory.RootsOfUnity.Basic

public noncomputable section

open Matrix QuadraticMap
open scoped commutatorElement
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonal

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

private def planeForm : QuadraticForm K (Fin 2 → K) :=
  Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) K)

private theorem toMatrix'_toLinEquiv (m : GL (Fin 2) K) :
    LinearMap.toMatrix' (((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K) m).toLinearMap) =
      (m : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K m) (Pi.single j 1) i =
    (m : Matrix (Fin 2) (Fin 2) K) i j
  rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  simp

private def planeToQuadratic (h2 : (2 : K) ≠ 0) :
    O2 K →* TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K).toMonoidHom.comp (O2 K).subtype).codRestrict
    (TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)))
    (fun m => by
      have hm : ((m : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∈
          Matrix.orthogonalGroup (Fin 2) K := by
        rw [Matrix.mem_orthogonalGroup_iff']
        exact m.2
      change CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K (m : GL (Fin 2) K) ∈
        TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K))
      rw [show planeForm (K := K) =
          Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) K) from rfl]
      rw [← TauCeti.toMatrix_mem_orthogonalGroup_iff (R := K) (n := Fin 2)
        (IsSMulRegular.of_ne_zero h2)]
      rw [toMatrix'_toLinEquiv]
      exact hm)

private theorem planeToQuadratic_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (planeToQuadratic (K := K) h2) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun g : TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) =>
    (g : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))) hab
  exact (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K).injective h

private theorem planeToQuadratic_surjective (h2 : (2 : K) ≠ 0) :
    Function.Surjective (planeToQuadratic (K := K) h2) := by
  intro e
  let m : GL (Fin 2) K := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K).symm (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
  have happ : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K m) = (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) :=
    MulEquiv.apply_symm_apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K)
      (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
  have hmat : (m : Matrix (Fin 2) (Fin 2) K) =
      LinearMap.toMatrix' ((e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)).toLinearMap) := by
    have h := congrArg
      (fun f : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K) =>
        LinearMap.toMatrix' (f.toLinearMap)) happ
    rw [toMatrix'_toLinEquiv] at h
    exact h
  have he : (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup
        (Matrix.toQuadraticForm' (1 : Matrix (Fin 2) (Fin 2) K)) := e.property
  have hm : (m : Matrix (Fin 2) (Fin 2) K) ∈ Matrix.orthogonalGroup (Fin 2) K := by
    rw [hmat]
    exact (TauCeti.toMatrix_mem_orthogonalGroup_iff (R := K) (n := Fin 2)
      (IsSMulRegular.of_ne_zero h2) (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))).mpr he
  have hmO : m ∈ O2 K := by
    change (m : Matrix (Fin 2) (Fin 2) K)ᵀ * (m : Matrix (Fin 2) (Fin 2) K) = 1
    exact (Matrix.mem_orthogonalGroup_iff' (n := Fin 2) (R := K)).mp hm
  refine ⟨⟨m, hmO⟩, ?_⟩
  apply Subtype.ext
  change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K m : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) =
    (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
  exact MulEquiv.apply_symm_apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2) K)
    (e : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))

private def planeEquiv (h2 : (2 : K) ≠ 0) :
    O2 K ≃* TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K)) :=
  MulEquiv.ofBijective (planeToQuadratic (K := K) h2)
    ⟨planeToQuadratic_injective (K := K) h2, planeToQuadratic_surjective (K := K) h2⟩

private def negIdx (i : Fin 2) : Fin 5 := if i = 0 then 0 else 1

private theorem negIdx_injective : Function.Injective (negIdx) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [negIdx] at hij ⊢

private def negVec (F : FrameData Q) (i : Fin 2) : Uminus F :=
  ⟨F.e (negIdx i), by
    rw [Module.End.mem_eigenspace_iff]
    have h : (negIdx i : ℕ) < 2 := by
      fin_cases i <;> simp [negIdx]
    simp [tOp, F.t_e, h]⟩

private theorem negVec_val (F : FrameData Q) (i : Fin 2) :
    (negVec F i).val = F.e (negIdx i) := rfl

private def negVecV (F : FrameData Q) (i : Fin 2) : V := F.e (negIdx i)

private theorem negVecV_linearIndependent (F : FrameData Q) :
    LinearIndependent K (negVecV F) :=
  F.e.linearIndependent.comp (negIdx) (negIdx_injective)

private theorem finrank_span_negVecV (F : FrameData Q) :
    Module.finrank K (Submodule.span K (Set.range (negVecV F))) = 2 := by
  rw [finrank_span_eq_card (negVecV_linearIndependent F), Fintype.card_fin]

private theorem span_negVecV_le_Uminus (F : FrameData Q) :
    Submodule.span K (Set.range (negVecV F)) ≤ Uminus F := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, rfl⟩
  exact (negVec F i).2

private theorem span_negVecV_eq_Uminus (F : FrameData Q) :
    Submodule.span K (Set.range (negVecV F)) = Uminus F := by
  apply Submodule.eq_of_le_of_finrank_eq (span_negVecV_le_Uminus F)
  rw [finrank_span_negVecV, finrank_Uminus]

private theorem range_negVecV (F : FrameData Q) :
    Set.range (negVecV F) = ({negVecV F 0, negVecV F 1} : Set V) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩

private def negCoords (F : FrameData Q) (u : Uminus F) : Fin 2 → K :=
  fun i => F.coord u.val (negIdx i)

private theorem negCoords_negVec (F : FrameData Q) (j : Fin 2) :
    negCoords F (negVec F j) = Pi.single j 1 := by
  ext i
  rw [negCoords, negVec_val, F.coord_e, Pi.single_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : negIdx i ≠ negIdx j := fun e => h (negIdx_injective e)
    simp [h, h']

private theorem negCoords_add (F : FrameData Q) (u v : Uminus F) :
    negCoords F (u + v) = negCoords F u + negCoords F v := by
  ext i
  simp [negCoords, map_add, Pi.add_apply]

private theorem negCoords_smul (F : FrameData Q) (a : K) (u : Uminus F) :
    negCoords F (a • u) = a • negCoords F u := by
  ext i
  simp [negCoords, map_smul, Pi.smul_apply]

private def negCoordsEquiv (F : FrameData Q) :
    Uminus F ≃ₗ[K] (Fin 2 → K) where
  toFun := negCoords F
  invFun := fun x => x 0 • negVec F 0 + x 1 • negVec F 1
  map_add' := negCoords_add F
  map_smul' := negCoords_smul F
  left_inv := by
    intro u
    have hu : u.val ∈ Submodule.span K (Set.range (negVecV F)) := by
      rw [span_negVecV_eq_Uminus]
      exact u.2
    have hspan : u.val ∈ Submodule.span K ({negVecV F 0, negVecV F 1} : Set V) := by
      rwa [range_negVecV F] at hu
    rw [Submodule.mem_span_pair] at hspan
    obtain ⟨a, b, hsum⟩ := hspan
    have hc0 : negCoords F u 0 = a := by
      have h := congrArg (fun v : V => F.coord v (negIdx 0)) hsum
      simpa [negCoords, negVecV, negIdx, F.coord_e, map_add, map_smul] using h.symm
    have hc1 : negCoords F u 1 = b := by
      have h := congrArg (fun v : V => F.coord v (negIdx 1)) hsum
      simpa [negCoords, negVecV, negIdx, F.coord_e, map_add, map_smul] using h.symm
    apply Subtype.ext
    change negCoords F u 0 • F.e (negIdx 0) + negCoords F u 1 • F.e (negIdx 1) = u.val
    rw [hc0, hc1, ← hsum]
    simp [negVecV]
  right_inv := by
    intro x
    ext i
    rw [negCoords_add, negCoords_smul, negCoords_smul, negCoords_negVec, negCoords_negVec]
    fin_cases i <;> simp [Pi.add_apply, Pi.smul_apply]

private theorem negCoordsEquiv_symm_apply (F : FrameData Q) (x : Fin 2 → K) :
    (negCoordsEquiv F).symm x = x 0 • negVec F 0 + x 1 • negVec F 1 := rfl

private theorem Q_negVec_zero (F : FrameData Q) : Q (negVec F 0).val = 1 := by
  rw [negVec_val]
  change Q (F.e 0) = 1
  exact F.norm 0 (by norm_num)

private theorem Q_negVec_one (F : FrameData Q) : Q (negVec F 1).val = 1 := by
  rw [negVec_val]
  change Q (F.e 1) = 1
  exact F.norm 1 (by norm_num)

private theorem polar_negVec (F : FrameData Q) :
    polar (⇑Q) (negVec F 0).val (negVec F 1).val = 0 := by
  rw [negVec_val, negVec_val]
  exact F.orth 1 0 (by norm_num) ▸ F.orth 0 1 (by norm_num)

private theorem Q_add_negVec (F : FrameData Q) (a b : K) :
    Q (a • (negVec F 0).val + b • (negVec F 1).val) = a ^ 2 + b ^ 2 := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul Q, QuadraticMap.map_smul Q,
    Q_negVec_zero, Q_negVec_one,
    QuadraticMap.polar_smul_left Q, QuadraticMap.polar_smul_right Q, polar_negVec]
  ring

private theorem quadU_eq_planeForm (F : FrameData Q) :
    (Q.comp (Uminus F).subtype).comp (negCoordsEquiv F).symm.toLinearMap =
      planeForm (K := K) := by
  ext x
  change Q ((negCoordsEquiv F).symm x).val = planeForm x
  rw [negCoordsEquiv_symm_apply]
  change Q ((x 0 • negVec F 0 + x 1 • negVec F 1 : Uminus F)).val = planeForm x
  rw [show (x 0 • negVec F 0 + x 1 • negVec F 1 : Uminus F).val =
      x 0 • (negVec F 0).val + x 1 • (negVec F 1).val from rfl]
  rw [Q_add_negVec]
  rw [planeForm, TauCeti.toQuadraticForm'_one_apply]
  rw [dotProduct, Fin.sum_univ_two]
  ring

private def uIsom (F : FrameData Q) :
    (Q.comp (Uminus F).subtype).IsometryEquiv (planeForm (K := K)) where
  toLinearEquiv := negCoordsEquiv F
  map_app' := by
    intro u
    have h := congrArg (fun q : QuadraticForm K (Fin 2 → K) => q ((negCoordsEquiv F) u))
      (quadU_eq_planeForm F)
    simpa [QuadraticMap.comp_apply] using h.symm

theorem natCard_Uminus_orthogonal (F : FrameData Q) (h2 : (2 : K) ≠ 0)
    {ε : ℤ} {m : ℕ} (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) (hm : (m : ℤ) = Nat.card K - ε) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Uminus F).subtype)) = 2 * m := by
  calc Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Uminus F).subtype))
      = Nat.card (TauCeti.QuadraticMap.orthogonalGroup (planeForm (K := K))) :=
        Nat.card_congr (TauCeti.QuadraticMap.orthogonalGroupCongr (uIsom F)).toEquiv
    _ = Nat.card (O2 K) :=
        (Nat.card_congr (planeEquiv (K := K) h2).toEquiv).symm
    _ = 2 * m := CFSG.ClassicalGroups.Orthogonal.PlaneSylow.natCard_O2_nat h2 ε hε hq m hm

theorem natCard_Wplus_orthogonal (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)) =
      2 * Nat.card K * (Nat.card K ^ 2 - 1) := by
  have h1 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype)) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) :=
    Nat.card_congr (traceZeroModel F hodd).equiv.toEquiv
  have h2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (traceZeroForm K)) =
      Nat.card (CFSG.GorensteinWalter.PGL2 K × rootsOfUnity 2 K) :=
    (Nat.card_congr (CFSG.ComponentClassification.CatalogueBOrthogonal.traceZeroProjectiveEquiv
      (K := K) F.two_ne_zero).toEquiv).symm
  rw [h1, h2, Nat.card_prod, CFSG.GorensteinWalter.pgl2_card_formula K,
    TauCeti.card_rootsOfUnity_two F.two_ne_zero]
  ring

private def C0Equiv (F : FrameData Q) :
    FiveDimensionalTPositive.C0 F ≃* (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Wplus F).subtype) ×
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (Uminus F).subtype)) :=
  (C0toOperatorEquiv F).trans
    (positiveOrthogonalCentralizerEquiv Q (tOp F) 1 one_ne_zero F.two_ne_zero
      (tOp_mul_self F) (tOp_selfAdjoint F))

theorem natCard_C0 (F : FrameData Q) (hodd : Odd (Nat.card K))
    {ε : ℤ} {m : ℕ} (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) (hm : (m : ℤ) = Nat.card K - ε) :
    Nat.card (FiveDimensionalTPositive.C0 F) = 4 * m * Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [Nat.card_congr (C0Equiv F).toEquiv, Nat.card_prod,
    natCard_Wplus_orthogonal F hodd,
    natCard_Uminus_orthogonal F F.two_ne_zero hε hq hm]
  ring

theorem negOrthogonal_mem_C0 (F : FrameData Q) :
    QuadraticMap.negOrthogonal Q ∈ FiveDimensionalTPositive.C0 F := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  simp [QuadraticMap.coe_negOrthogonal, FrameData.tO]

theorem detC0_negOrthogonal (F : FrameData Q) :
    detC0 F ⟨QuadraticMap.negOrthogonal Q, negOrthogonal_mem_C0 F⟩ = -1 := by
  apply Units.ext
  rw [detC0_apply, LinearEquiv.coe_det, QuadraticMap.coe_negOrthogonal]
  change LinearMap.det (-(LinearMap.id : V →ₗ[K] V)) = (-1 : K)
  rw [show (-(LinearMap.id : V →ₗ[K] V)) = (-1 : K) • LinearMap.id by ext x; simp]
  rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_eq_card_basis F.e, mul_one]
  norm_num

theorem detC0_range (F : FrameData Q) :
    (detC0 F).range = rootsOfUnity 2 K := by
  have hle : (detC0 F).range ≤ rootsOfUnity 2 K := by
    rintro x ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact detC0_sq F g
  have hneg : (-1 : Kˣ) ∈ (detC0 F).range :=
    ⟨⟨QuadraticMap.negOrthogonal Q, negOrthogonal_mem_C0 F⟩, detC0_negOrthogonal F⟩
  have hzp : Subgroup.zpowers (-1 : Kˣ) ≤ (detC0 F).range :=
    Subgroup.zpowers_le.mpr hneg
  have hzpcard : Nat.card (Subgroup.zpowers (-1 : Kˣ)) = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two]; simp
    · intro h
      have hval : (-1 : K) = 1 := congrArg Units.val h
      exact F.two_ne_zero (by rw [show (2 : K) = 1 - (-1 : K) by ring, hval]; ring)
  have hrootscard : Nat.card (rootsOfUnity 2 K) = 2 :=
    TauCeti.card_rootsOfUnity_two F.two_ne_zero
  have hzproots : Subgroup.zpowers (-1 : Kˣ) ≤ rootsOfUnity 2 K := by
    rw [Subgroup.zpowers_le, mem_rootsOfUnity]
    rw [pow_two]; simp
  have heq : Subgroup.zpowers (-1 : Kˣ) = rootsOfUnity 2 K := by
    apply Subgroup.eq_of_le_of_card_ge hzproots
    rw [hrootscard, hzpcard]
  exact le_antisymm hle (by rw [← heq]; exact hzp)

theorem detC0_ker_index (F : FrameData Q) : (detC0 F).ker.index = 2 := by
  rw [Subgroup.index_ker, detC0_range F]
  exact TauCeti.card_rootsOfUnity_two F.two_ne_zero

theorem natCard_CSO (F : FrameData Q) (hodd : Odd (Nat.card K))
    {ε : ℤ} {m : ℕ} (hε : ε = 1 ∨ ε = -1)
    (hq : (Nat.card K : ℤ) ≡ ε [ZMOD 4]) (hm : (m : ℤ) = Nat.card K - ε) :
    Nat.card (FiveDimensionalTPositive.CSO F) =
      2 * m * Nat.card K * (Nat.card K ^ 2 - 1) := by
  have hC0card := natCard_C0 F hodd hε hq hm
  have hmul := Subgroup.card_mul_index (detC0 F).ker
  have hidx : (detC0 F).ker.index = 2 := detC0_ker_index F
  have hker2 : Nat.card (detC0 F).ker * 2 =
      4 * m * Nat.card K * (Nat.card K ^ 2 - 1) := by
    calc Nat.card (detC0 F).ker * 2
        = Nat.card (detC0 F).ker * (detC0 F).ker.index := by rw [hidx]
      _ = Nat.card (FiveDimensionalTPositive.C0 F) := hmul
      _ = 4 * m * Nat.card K * (Nat.card K ^ 2 - 1) := hC0card
  have htarget2 : (2 * m * Nat.card K * (Nat.card K ^ 2 - 1)) * 2 =
      4 * m * Nat.card K * (Nat.card K ^ 2 - 1) := by ring
  have hker : Nat.card (detC0 F).ker =
      2 * m * Nat.card K * (Nat.card K ^ 2 - 1) :=
    Nat.eq_of_mul_eq_mul_right (by norm_num) (hker2.trans htarget2.symm)
  calc Nat.card (FiveDimensionalTPositive.CSO F)
      = Nat.card ((detC0 F).ker.map (FiveDimensionalTPositive.C0 F).subtype) := by
        rw [FiveDimensionalTPositive.CSO_eq_map_ker]
    _ = Nat.card (detC0 F).ker :=
        Subgroup.card_map_of_injective (FiveDimensionalTPositive.C0 F).subtype_injective
    _ = 2 * m * Nat.card K * (Nat.card K ^ 2 - 1) := hker

private theorem betaBaseO_eq_map (F : FrameData Q) (D : Subgroup (O2 K)) :
    betaBaseO F D = (betaBase F D).map (Q.specialOrthogonalWithin).subtype := by
  rw [betaBaseO, betaBase, Subgroup.map_map]
  rfl

private theorem swapSubO_eq_map (F : FrameData Q) :
    swapSubO F = (swapSub F).map (Q.specialOrthogonalWithin).subtype := by
  rw [swapSubO, swapSub, MonoidHom.map_zpowers]
  rfl

private theorem mem_wreathO_iff (F : FrameData Q) (D : Subgroup (O2 K))
    (x : TauCeti.QuadraticMap.orthogonalGroup Q) :
    x ∈ wreathO F D ↔
      ∃ b ∈ betaBaseO F D, ∃ c ∈ swapSubO F, x = b * c := by
  constructor
  · intro hx
    rw [← wreathSub_map_eq F D] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, c, hc, rfl⟩ := (mem_wreathSub_iff F D y).mp hy
    refine ⟨(Q.specialOrthogonalWithin).subtype b, ?_,
      (Q.specialOrthogonalWithin).subtype c, ?_, ?_⟩
    · rw [betaBaseO_eq_map]
      exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    · rw [swapSubO_eq_map]
      exact Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    · rw [← hyx, map_mul]
  · rintro ⟨b, hb, c, hc, rfl⟩
    rw [betaBaseO_eq_map] at hb
    rw [swapSubO_eq_map] at hc
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
    rw [← wreathSub_map_eq F D]
    refine Subgroup.mem_map.mpr ⟨b' * c', ?_, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left hb') (Subgroup.mem_sup_right hc')

theorem betaBaseO_le_C0 (F : FrameData Q) (D : Subgroup (O2 K)) :
    betaBaseO F D ≤ FiveDimensionalTPositive.C0 F := by
  rw [betaBaseO_eq_map]
  rintro x ⟨b, hb, rfl⟩
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  simpa [betaSOHom] using betaO_commute_tO F p.1 p.2

theorem betaBaseO_le_SO (F : FrameData Q) (D : Subgroup (O2 K)) :
    betaBaseO F D ≤ Q.specialOrthogonalWithin := by
  rw [betaBaseO_eq_map]
  exact Subgroup.map_subtype_le _

private theorem orderOf_sO (F : FrameData Q) : orderOf F.sO = 2 := by
  have h := orderOf_injective (Q.specialOrthogonalWithin).subtype
    (Subgroup.subtype_injective _) F.sSO
  rw [show (Q.specialOrthogonalWithin).subtype F.sSO = F.sO from rfl] at h
  rw [h, orderOf_sSO F]

theorem wreathO_inf_C0 (F : FrameData Q) (D : Subgroup (O2 K)) :
    wreathO F D ⊓ FiveDimensionalTPositive.C0 F = betaBaseO F D := by
  apply le_antisymm
  · rintro x ⟨hxT, hxC0⟩
    change x ∈ wreathO F D at hxT
    rw [mem_wreathO_iff] at hxT
    obtain ⟨b, hb, c, hc, rfl⟩ := hxT
    have hbC0 : b ∈ FiveDimensionalTPositive.C0 F := betaBaseO_le_C0 F D hb
    have hbcomm : b * F.tO = F.tO * b :=
      Subgroup.mem_centralizer_singleton_iff.mp hbC0
    have hxcomm : (b * c) * F.tO = F.tO * (b * c) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC0
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two (orderOf_sO F)).mp hc with hc1 | hcs
    · simpa [hc1] using hb
    · exfalso
      have hbinv : b⁻¹ * F.tO = F.tO * b⁻¹ := by
        have h' : b⁻¹ * F.tO * b = F.tO := by
          calc b⁻¹ * F.tO * b = b⁻¹ * (F.tO * b) := by group
            _ = b⁻¹ * (b * F.tO) := by rw [← hbcomm]
            _ = F.tO := by group
        calc b⁻¹ * F.tO = b⁻¹ * F.tO * (b * b⁻¹) := by group
          _ = (b⁻¹ * F.tO * b) * b⁻¹ := by group
          _ = F.tO * b⁻¹ := by rw [h']
      have hscomm : F.sO * F.tO = F.tO * F.sO := by
        have h := hxcomm
        rw [hcs] at h
        calc F.sO * F.tO = (b⁻¹ * b) * F.sO * F.tO := by group
          _ = b⁻¹ * ((b * F.sO) * F.tO) := by group
          _ = b⁻¹ * (F.tO * (b * F.sO)) := by rw [h]
          _ = (b⁻¹ * F.tO) * (b * F.sO) := by group
          _ = (F.tO * b⁻¹) * (b * F.sO) := by rw [hbinv]
          _ = F.tO * F.sO := by group
      have hzt : F.zO * F.tO = F.tO := by
        rw [← sO_conj_tO F]
        calc F.sO * F.tO * F.sO⁻¹ = (F.sO * F.tO) * F.sO⁻¹ := rfl
          _ = (F.tO * F.sO) * F.sO⁻¹ := by rw [hscomm]
          _ = F.tO := by group
      have hzt' : F.zO * F.tO = 1 * F.tO := by simpa using hzt
      exact zO_ne_one F (mul_right_cancel hzt')
  · intro x hx
    exact ⟨Subgroup.mem_sup_left hx, betaBaseO_le_C0 F D hx⟩

theorem natCard_betaBaseO (F : FrameData Q) (D : Subgroup (O2 K)) {r : ℕ}
    (hD : Nat.card D = 2 ^ (r + 1)) :
    Nat.card (betaBaseO F D) = 2 ^ (2 * r + 2) := by
  rw [betaBaseO_eq_map, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
    betaBase_card F D hD]

private lemma card_CSO_two_part_arith {q m m0 n r : ℕ}
    (hfac : m = 2 ^ r * m0) (hq2 : q ^ 2 - 1 = m * (2 * n)) :
    2 * m * q * (q ^ 2 - 1) = 2 ^ (2 * r + 2) * (q * m0 ^ 2 * n) := by
  rw [hq2, hfac]
  have hpow : 2 ^ (2 * r + 2) = 4 * 2 ^ r * 2 ^ r := by
    rw [show 2 * r + 2 = r + r + 2 by ring, pow_add, pow_add]
    norm_num
    ring
  rw [hpow]
  ring

private lemma sign_eq_of_mod_four {ε ε' : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hε' : ε' = 1 ∨ ε' = -1) (h : ε ≡ ε' [ZMOD 4]) : ε = ε' := by
  rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl
  · rfl
  · exfalso
    rw [Int.modEq_iff_dvd] at h
    norm_num at h
  · exfalso
    rw [Int.modEq_iff_dvd] at h
    norm_num at h
  · rfl

theorem natCard_CSO_twoPart (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F) :
    ∃ u : ℕ, Nat.card (FiveDimensionalTPositive.CSO F) =
      2 ^ (2 * W.r + 2) * u ∧ Odd u := by
  obtain ⟨ε, hε, hq, m, m0, hm, hfac, hm0⟩ := W.twoPart
  obtain ⟨ε', hε', hq', m', n, h', hm', hn', hoddn, hh', hoddh⟩ :=
    CFSG.NumberTheory.exists_sign_mod_four_odd_cofactors (q := Nat.card K) hodd
  have hεeq : ε' = ε := by
    apply sign_eq_of_mod_four hε' hε
    exact hq'.symm.trans hq
  have hn : (Nat.card K : ℤ) + ε = 2 * (n : ℤ) := by
    rw [← hεeq]
    exact hn'
  have hq2 : Nat.card K ^ 2 - 1 = m * (2 * n) := by
    rcases hε with rfl | rfl
    · have hqZ : (Nat.card K : ℤ) = (m : ℤ) + 1 := by omega
      have h2nZ : 2 * (n : ℤ) = (m : ℤ) + 2 := by
        have := hn
        rw [hqZ] at this
        omega
      have hq2Z : (Nat.card K : ℤ) ^ 2 - 1 = (m : ℤ) * (2 * (n : ℤ)) := by
        nlinarith
      have hq2one : 1 ≤ Nat.card K ^ 2 := by
        calc 1 = 1 ^ 2 := by norm_num
          _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left (Finite.one_lt_card.le) 2
      have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (m * (2 * n) : ℕ) := by
        rw [Nat.cast_sub hq2one]
        push_cast
        exact hq2Z
      exact Nat.cast_injective hcast
    · have hmpos : (1 : ℤ) ≤ (m : ℤ) := by
        have := hn
        have hqone : (1 : ℤ) ≤ (Nat.card K : ℤ) := by exact_mod_cast Finite.one_lt_card.le
        omega
      have hqZ : (Nat.card K : ℤ) = (m : ℤ) - 1 := by omega
      have h2nZ : 2 * (n : ℤ) = (m : ℤ) - 2 := by
        have := hn
        rw [hqZ] at this
        omega
      have hq2Z : (Nat.card K : ℤ) ^ 2 - 1 = (m : ℤ) * (2 * (n : ℤ)) := by
        nlinarith
      have hq2one : 1 ≤ Nat.card K ^ 2 := by
        calc 1 = 1 ^ 2 := by norm_num
          _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left (Finite.one_lt_card.le) 2
      have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (m * (2 * n) : ℕ) := by
        rw [Nat.cast_sub hq2one]
        push_cast
        exact hq2Z
      exact Nat.cast_injective hcast
  have hCSO := natCard_CSO F hodd hε hq hm
  refine ⟨Nat.card K * m0 ^ 2 * n, ?_, ?_⟩
  · calc Nat.card (FiveDimensionalTPositive.CSO F)
        = 2 * m * Nat.card K * (Nat.card K ^ 2 - 1) := hCSO
      _ = 2 ^ (2 * W.r + 2) * (Nat.card K * m0 ^ 2 * n) :=
          card_CSO_two_part_arith hfac hq2
  · exact ((hodd.mul (hm0.pow)).mul hoddn)

theorem isSylowOf_betaBaseO (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F) :
    CFSG.ABGLocalTools.IsSylowOf 2 (betaBaseO F W.D)
      (FiveDimensionalTPositive.CSO F) := by
  obtain ⟨u, hcard, hodd_u⟩ := natCard_CSO_twoPart F hodd W
  have hle : betaBaseO F W.D ≤ FiveDimensionalTPositive.CSO F :=
    fun x hx => ⟨betaBaseO_le_SO F W.D hx, betaBaseO_le_C0 F W.D hx⟩
  have hBcard : Nat.card (betaBaseO F W.D) = 2 ^ (2 * W.r + 2) :=
    natCard_betaBaseO F W.D W.hDcard
  have hfact : (Nat.card (FiveDimensionalTPositive.CSO F)).factorization 2 =
      2 * W.r + 2 := by
    rw [hcard]
    exact CFSG.GH74.SmallRanks.factorization_two_pow_mul_odd hodd_u
  exact CFSG.ABGLocalTools.isSylowOf_of_card hle (by rw [hBcard, hfact])

theorem CSO_le_normalizer_CG (F : FrameData Q)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    FiveDimensionalTPositive.CSO F ≤
      Subgroup.normalizer ((G ⊓ FiveDimensionalTPositive.C0 F :
        Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) : Set _) := by
  have hGnormal : G.Normal :=
    Subgroup.Normal.of_commutator_le (G := TauCeti.QuadraticMap.orthogonalGroup Q) hLG
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact ⟨hGnormal.conj_mem n hn.1 x,
      (FiveDimensionalTPositive.C0 F).mul_mem
        ((FiveDimensionalTPositive.C0 F).mul_mem hx.2 hn.2)
        ((FiveDimensionalTPositive.C0 F).inv_mem hx.2)⟩
  · intro hn
    refine ⟨?_, ?_⟩
    · have h := hGnormal.conj_mem (x * n * x⁻¹) hn.1 x⁻¹
      have heq : x⁻¹ * (x * n * x⁻¹) * x = n := by group
      simpa [heq] using h
    · have h := (FiveDimensionalTPositive.C0 F).mul_mem
        ((FiveDimensionalTPositive.C0 F).mul_mem
          ((FiveDimensionalTPositive.C0 F).inv_mem hx.2) hn.2) hx.2
      have heq : x⁻¹ * (x * n * x⁻¹) * x = n := by group
      simpa [heq] using h

theorem isSylowOf_betaBaseO_inf (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    CFSG.ABGLocalTools.IsSylowOf 2 (betaBaseO F W.D ⊓ G)
      (G ⊓ FiveDimensionalTPositive.C0 F) := by
  have hB := isSylowOf_betaBaseO F hodd W
  have hCGle : G ⊓ FiveDimensionalTPositive.C0 F ≤ FiveDimensionalTPositive.CSO F := by
    rintro x ⟨hxG, hxC0⟩
    exact ⟨hGSO hxG, hxC0⟩
  have hKN := CSO_le_normalizer_CG F G hLG
  have h := hB.inf_of_le_normalizer hCGle hKN
  have hEq : betaBaseO F W.D ⊓ (G ⊓ FiveDimensionalTPositive.C0 F) =
      betaBaseO F W.D ⊓ G := by
    rw [← inf_assoc]
    exact inf_eq_left.mpr (inf_le_left.trans (betaBaseO_le_C0 F W.D))
  simpa [hEq] using h

@[expose] def diagBeta (F : FrameData Q) : O2 K →* FiveDimensionalTPositive.C0 F where
  toFun d :=
    ⟨F.betaO d d, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact betaO_commute_tO F d d⟩
  map_one' := Subtype.ext (F.betaO_one)
  map_mul' d e := by
    apply Subtype.ext
    change F.betaO (d * e) (d * e) = F.betaO d d * F.betaO e e
    exact (F.betaO_mul d d e e).symm

@[expose] noncomputable def diagAction (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    O2 K →* CFSG.GorensteinWalter.PGL2 K :=
  (eta F hodd).comp (diagBeta F)

private def e2W (F : FrameData Q) : Wplus F :=
  ⟨F.e 2, by
    rw [Module.End.mem_eigenspace_iff]
    simp [tOp, F.t_e]⟩

private def e3W (F : FrameData Q) : Wplus F :=
  ⟨F.e 3, by
    rw [Module.End.mem_eigenspace_iff]
    simp [tOp, F.t_e]⟩

private def e4W (F : FrameData Q) : Wplus F :=
  ⟨F.e 4, by
    rw [Module.End.mem_eigenspace_iff]
    simp [tOp, F.t_e]⟩

private theorem diagBeta_val (F : FrameData Q) (d : O2 K) :
    ((diagBeta F d).val : V ≃ₗ[K] V) = F.beta d d := rfl

private theorem wplus_eval (F : FrameData Q) (hodd : Odd (Nat.card K)) (d : O2 K)
    (h : eta F hodd (diagBeta F d) = 1) :
    ∃ ε : K, ε ^ 2 = 1 ∧
      ∀ w : Wplus F, (resPlus F (diagBeta F d)).val w = ε • w := by
  have hrho : rho F hodd (resPlus F (diagBeta F d)) = 1 := by
    rw [← eta_apply F hodd (diagBeta F d)]
    exact h
  exact (rho_eq_one_iff F hodd (resPlus F (diagBeta F d))).mp hrho

private theorem diagBeta_kernel (F : FrameData Q) (hodd : Odd (Nat.card K))
    (d : O2 K) (hd : diagAction F hodd d = 1) : d = 1 := by
  obtain ⟨ε, hε, hact⟩ := wplus_eval F hodd d hd
  have h4ε : F.beta d d (F.e 4) = ε • F.e 4 := by
    have h := congrArg (fun w : Wplus F => w.val) (hact (e4W F))
    simpa [e4W, diagBeta_val, resPlus_apply] using h
  have hdet : ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det *
      ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    FrameData.O2_det_sq d
  have hε1 : ε = 1 := by
    have hc := congrArg (fun v : V => F.coord v 4) h4ε
    simp [F.beta_e_four, hdet] at hc
    exact hc.symm
  have h2 : F.beta d d (F.e 2) = F.e 2 := by
    have h := congrArg (fun w : Wplus F => w.val) (hact (e2W F))
    have h' : F.beta d d (F.e 2) = ε • F.e 2 := by
      simpa [e2W, diagBeta_val, resPlus_apply] using h
    simpa [hε1] using h'
  have h3 : F.beta d d (F.e 3) = F.e 3 := by
    have h := congrArg (fun w : Wplus F => w.val) (hact (e3W F))
    have h' : F.beta d d (F.e 3) = ε • F.e 3 := by
      simpa [e3W, diagBeta_val, resPlus_apply] using h
    simpa [hε1] using h'
  have h00 : ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = 1 := by
    have hc := congrArg (fun v : V => F.coord v 2) h2
    simpa [F.beta_e_two, F.coord_e, map_add, map_smul] using hc
  have h10 : ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have hc := congrArg (fun v : V => F.coord v 3) h2
    simpa [F.beta_e_two, F.coord_e, map_add, map_smul] using hc
  have h01 : ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by
    have hc := congrArg (fun v : V => F.coord v 2) h3
    simpa [F.beta_e_three, F.coord_e, map_add, map_smul] using hc
  have h11 : ((d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have hc := congrArg (fun v : V => F.coord v 3) h3
    simpa [F.beta_e_three, F.coord_e, map_add, map_smul] using hc
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem diagAction_injective (F : FrameData Q) (hodd : Odd (Nat.card K)) :
    Function.Injective (diagAction F hodd) := by
  intro d e hde
  have h : diagAction F hodd (d * e⁻¹) = 1 := by
    rw [map_mul, map_inv, hde, mul_inv_cancel]
  have hde1 : d * e⁻¹ = 1 := diagBeta_kernel F hodd (d * e⁻¹) h
  calc d = d * e⁻¹ * e := by group
    _ = 1 * e := by rw [hde1]
    _ = e := one_mul e

theorem diagAction_orderOf_cD (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F) :
    orderOf (diagAction F hodd W.cD) = 2 ^ W.r := by
  rw [orderOf_injective (diagAction F hodd) (diagAction_injective F hodd) W.cD]
  have h2 : orderOf ((O2 K).subtype (W.cD : O2 K)) = orderOf (W.cD : O2 K) :=
    orderOf_injective (O2 K).subtype (Subgroup.subtype_injective (O2 K))
      (W.cD : O2 K)
  have h3 : (O2 K).subtype (W.cD : O2 K) = W.c := W.hcD
  calc orderOf (W.cD : O2 K) = orderOf ((O2 K).subtype (W.cD : O2 K)) := h2.symm
    _ = orderOf W.c := by rw [h3]
    _ = 2 ^ W.r := W.hordc

abbrev outerWitness (F : FrameData Q) (W : FiveDimensionalWreathData F) :
    TauCeti.QuadraticMap.orthogonalGroup Q :=
  F.betaO W.cD W.cD

theorem outerWitness_mem_betaBaseO (F : FrameData Q) (D : Subgroup (O2 K)) (d : D) :
    F.betaO (d : O2 K) (d : O2 K) ∈ betaBaseO F D := by
  rw [betaBaseO]
  exact Subgroup.mem_map.mpr
    ⟨((d : O2 K), (d : O2 K)), ⟨d.property, d.property⟩, rfl⟩

theorem outerWitness_mem_G (F : FrameData Q)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) (d : O2 K) :
    F.betaO d d ∈ G :=
  hLG (betaO_diag_mem_derived F d)

theorem outerWitness_mem_inf (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    outerWitness F W ∈ betaBaseO F W.D ⊓ G :=
  ⟨outerWitness_mem_betaBaseO F W.D W.cD, outerWitness_mem_G F G hLG W.cD⟩

private lemma two_pow_not_dvd_of_odd {r n : ℕ} (hr : 1 ≤ r) (hn : Odd n) :
    ¬ 2 ^ r ∣ n := by
  intro h
  have h2r : 2 ∣ 2 ^ r := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0) with ⟨k, hk⟩
    rw [hk, pow_succ]
    exact dvd_mul_left 2 (2 ^ k)
  exact hn.not_two_dvd_nat (dvd_trans h2r h)

private lemma two_pow_not_dvd_half {r m0 : ℕ} (hr : 2 ≤ r) (hm0 : Odd m0) :
    ¬ 2 ^ r ∣ 2 ^ (r - 1) * m0 := by
  intro h
  have hsplit : 2 ^ r = 2 ^ (r - 1) * 2 := by
    have hr1 : r = (r - 1) + 1 := by omega
    calc 2 ^ r = 2 ^ ((r - 1) + 1) := congrArg (fun k => 2 ^ k) hr1
      _ = 2 ^ (r - 1) * 2 := by rw [pow_succ]
  rw [hsplit] at h
  exact hm0.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) h)

theorem diagAction_cD_not_mem_psl2Range (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F) :
    diagAction F hodd W.cD ∉
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  intro hmem
  let toPGL : CFSG.GorensteinWalter.PSL2 K →* CFSG.GorensteinWalter.PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hmem
  have hordx : orderOf x = 2 ^ W.r := by
    rw [← orderOf_injective toPGL (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective) x, hx]
    exact diagAction_orderOf_cD F hodd W
  obtain ⟨ε, hε, hq, m, m0, hm, hfac, hm0⟩ := W.twoPart
  obtain ⟨ε', hε', hq', m', n, h', hm', hn', hoddn, hh', hoddh⟩ :=
    CFSG.NumberTheory.exists_sign_mod_four_odd_cofactors (q := Nat.card K) hodd
  have hεeq : ε' = ε := by
    apply sign_eq_of_mod_four hε' hε
    exact hq'.symm.trans hq
  have hn : (Nat.card K : ℤ) + ε = 2 * (n : ℤ) := by
    rw [← hεeq]
    exact hn'
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hp, hF⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  have hF' : Nat.card K = ringChar K ^ (f : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hF
  have hdvd := CFSG.Glauberman.Dickson.psl2_orderOf_dvd
    (F := K) (p := ringChar K) (f := (f : ℕ)) hF' x
  have h2dvd : 2 ∣ Nat.card K - 1 :=
    Even.two_dvd (Nat.Odd.sub_odd hodd odd_one)
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := Nat.gcd_eq_right h2dvd
  rw [hgcd] at hdvd
  have hpodd : Odd (ringChar K) := by
    rcases hp.eq_two_or_odd with hp2 | hpodd
    · exfalso
      have h2dvdq : 2 ∣ Nat.card K := by
        rw [hF', hp2]
        exact dvd_pow_self 2 f.pos.ne' 
      exact hodd.not_two_dvd_nat h2dvdq
    · exact Nat.odd_iff.mpr hpodd
  have hr2 : 2 ≤ W.r := W.hr2
  have hnot_p : ¬ 2 ^ W.r ∣ ringChar K :=
    two_pow_not_dvd_of_odd (by omega) hpodd
  have hnot_q : ¬ 2 ^ W.r ∣ Nat.card K :=
    two_pow_not_dvd_of_odd (by omega) hodd
  have hpdvd : 2 ^ W.r ∣ orderOf x := by rw [hordx]
  rcases hε with rfl | rfl
  · have hq_eq : Nat.card K = m + 1 := by
      have hqZ : (Nat.card K : ℤ) = (m : ℤ) + 1 := by omega
      exact_mod_cast hqZ
    have hn_nat : Nat.card K + 1 = 2 * n := by
      exact_mod_cast hn
    have hhalf_same : (Nat.card K - 1) / 2 = 2 ^ (W.r - 1) * m0 := by
      have hqminus : Nat.card K - 1 = m := by omega
      rw [hqminus, hfac]
      have hsplit : 2 ^ W.r = 2 * 2 ^ (W.r - 1) := by
        have hr1 : W.r = (W.r - 1) + 1 := by omega
        calc 2 ^ W.r = 2 ^ ((W.r - 1) + 1) := congrArg (fun k => 2 ^ k) hr1
          _ = 2 ^ (W.r - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (W.r - 1) := by ring
      rw [hsplit, mul_assoc, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    have hhalf_other : (Nat.card K + 1) / 2 = n := by
      rw [hn_nat, Nat.mul_div_right n (by norm_num : 0 < 2)]
    have hnot_same : ¬ 2 ^ W.r ∣ (Nat.card K - 1) / 2 := by
      rw [hhalf_same]
      exact two_pow_not_dvd_half (by omega) hm0
    have hnot_other : ¬ 2 ^ W.r ∣ (Nat.card K + 1) / 2 := by
      rw [hhalf_other]
      exact two_pow_not_dvd_of_odd (by omega) hoddn
    rcases hdvd with h | h | h
    · exact hnot_p (dvd_trans hpdvd h)
    · exact hnot_same (dvd_trans hpdvd h)
    · exact hnot_other (dvd_trans hpdvd h)
  · have hqplusZ : (Nat.card K : ℤ) + 1 = (m : ℤ) := by
      have := hm
      norm_num at this ⊢
      linarith
    have hqplus : Nat.card K + 1 = m := by exact_mod_cast hqplusZ
    have hnZ : (Nat.card K : ℤ) - 1 = 2 * (n : ℤ) := by
      have := hn
      norm_num at this ⊢
      linarith
    have hn_nat : Nat.card K - 1 = 2 * n := by
      have hqone : 1 ≤ Nat.card K := Finite.one_lt_card.le
      have hcast : ((Nat.card K - 1 : ℕ) : ℤ) = (2 * n : ℕ) := by
        rw [Nat.cast_sub hqone]
        push_cast
        exact hnZ
      exact Nat.cast_injective hcast
    have hhalf_same : (Nat.card K + 1) / 2 = 2 ^ (W.r - 1) * m0 := by
      rw [hqplus, hfac]
      have hsplit : 2 ^ W.r = 2 * 2 ^ (W.r - 1) := by
        have hr1 : W.r = (W.r - 1) + 1 := by omega
        calc 2 ^ W.r = 2 ^ ((W.r - 1) + 1) := congrArg (fun k => 2 ^ k) hr1
          _ = 2 ^ (W.r - 1) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (W.r - 1) := by ring
      rw [hsplit, mul_assoc, Nat.mul_div_right _ (by norm_num : 0 < 2)]
    have hhalf_other : (Nat.card K - 1) / 2 = n := by
      rw [hn_nat, Nat.mul_div_right n (by norm_num : 0 < 2)]
    have hnot_same : ¬ 2 ^ W.r ∣ (Nat.card K + 1) / 2 := by
      rw [hhalf_same]
      exact two_pow_not_dvd_half (by omega) hm0
    have hnot_other : ¬ 2 ^ W.r ∣ (Nat.card K - 1) / 2 := by
      rw [hhalf_other]
      exact two_pow_not_dvd_of_odd (by omega) hoddn
    rcases hdvd with h | h | h
    · exact hnot_p (dvd_trans hpdvd h)
    · exact hnot_other (dvd_trans hpdvd h)
    · exact hnot_same (dvd_trans hpdvd h)

abbrev localX (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  tPositiveDerived F

abbrev localS (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  betaBaseO F W.D ⊓ G

abbrev localCG (F : FrameData Q)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  G ⊓ FiveDimensionalTPositive.C0 F

abbrev localK (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  tPositiveDerived F ⊔ localS F W G

abbrev localC (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  localK F W G ⊓ Subgroup.centralizer (tPositiveDerived F :
    Set (TauCeti.QuadraticMap.orthogonalGroup Q))

theorem localX_le_G (F : FrameData Q)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    localX F ≤ G := by
  intro x hx
  exact hLG (tPositiveDerived_le_commutator F hx)

theorem localK_le_C0 (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    localK F W G ≤ FiveDimensionalTPositive.C0 F := by
  refine sup_le (tPositiveDerived_le_C0 F) ?_
  intro x hx
  exact (betaBaseO_le_C0 F W.D) hx.1

theorem localK_le_CG (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    localK F W G ≤ localCG F G := by
  refine sup_le ?_ ?_
  · intro x hx
    exact ⟨localX_le_G F G hLG hx, tPositiveDerived_le_C0 F hx⟩
  · intro x hx
    exact ⟨hx.2, (betaBaseO_le_C0 F W.D) hx.1⟩

theorem localS_le_C0 (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    localS F W G ≤ FiveDimensionalTPositive.C0 F := by
  intro x hx
  exact (betaBaseO_le_C0 F W.D) hx.1

theorem localS_sylow_CG (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    CFSG.ABGLocalTools.IsSylowOf 2 (localS F W G) (localCG F G) :=
  isSylowOf_betaBaseO_inf F hodd W G hLG hGSO

theorem localS_sylowIn_CG (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    CFSG.Quasithin.IsSylowIn 2 (localS F W G) (localCG F G) := by
  have h := CFSG.ABGLocalTools.isSylowOf_iff.mp
    (localS_sylow_CG F hodd W G hLG hGSO)
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem localS_sylow_K (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    CFSG.ABGLocalTools.IsSylowOf 2 (localS F W G) (localK F W G) :=
  (localS_sylow_CG F hodd W G hLG hGSO).of_le
    (le_sup_right : localS F W G ≤ localK F W G)
    (localK_le_CG F W G hLG)

theorem localS_sylowIn_K (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    CFSG.Quasithin.IsSylowIn 2 (localS F W G) (localK F W G) := by
  have h := CFSG.ABGLocalTools.isSylowOf_iff.mp
    (localS_sylow_K F hodd W G hLG hGSO)
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem localS_le_normalizer_X (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    localS F W G ≤ Subgroup.normalizer (localX F :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)) :=
  (localS_le_C0 F W G).trans (tPositiveDerived_normalized F hodd)

@[expose] noncomputable def localPi (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    localK F W G →* CFSG.GorensteinWalter.PGL2 K :=
  (eta F hodd).comp (Subgroup.inclusion (localK_le_C0 F W G))

theorem localPi_apply (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) (y : localK F W G) :
    localPi F hodd W G y =
      eta F hodd ⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q),
        localK_le_C0 F W G y.property⟩ := rfl

theorem localPi_ker_eq (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    (localPi F hodd W G).ker = (localC F W G).subgroupOf (localK F W G) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_subgroupOf]
    refine ⟨y.property, ?_⟩
    have heta : eta F hodd ⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q),
        localK_le_C0 F W G y.property⟩ = 1 := hy
    have hcent := (eta_eq_one_iff_centralizes_X F hodd h3
      ⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q),
        localK_le_C0 F W G y.property⟩).mp heta
    show ∀ x ∈ (localX F : Set (TauCeti.QuadraticMap.orthogonalGroup Q)),
      x * (y.val : TauCeti.QuadraticMap.orthogonalGroup Q) =
        (y.val : TauCeti.QuadraticMap.orthogonalGroup Q) * x
    intro x hx
    exact (hcent ⟨x, hx⟩).symm
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨_, hyC⟩ := hy
    show localPi F hodd W G y = 1
    rw [localPi_apply]
    apply (eta_eq_one_iff_centralizes_X F hodd h3
      ⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q),
        localK_le_C0 F W G y.property⟩).mpr
    intro x
    have hyC' : ∀ z ∈ (localX F : Set (TauCeti.QuadraticMap.orthogonalGroup Q)),
        z * (y.val : TauCeti.QuadraticMap.orthogonalGroup Q) =
          (y.val : TauCeti.QuadraticMap.orthogonalGroup Q) * z :=
      Subgroup.mem_centralizer_iff.mp hyC
    exact (hyC' x.val x.property).symm

theorem localPi_surjective (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    Function.Surjective (localPi F hodd W G) := by
  let R := (localPi F hodd W G).range
  let J : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  have hJle : J ≤ R := by
    rw [show J = (etaX F hodd).range from (etaX_range F hodd h3).symm]
    rintro y ⟨x, rfl⟩
    refine ⟨⟨x.val, Subgroup.mem_sup_left x.property⟩, ?_⟩
    rw [localPi_apply]
    rfl
  have houter : diagAction F hodd W.cD ∈ R := by
    refine ⟨⟨outerWitness F W, Subgroup.mem_sup_right
      (outerWitness_mem_inf F W G hLG)⟩, ?_⟩
    rw [localPi_apply]
    rfl
  have hJne : J ≠ R := by
    intro hEq
    have houtJ : diagAction F hodd W.cD ∈ J := by
      simpa [hEq] using houter
    exact diagAction_cD_not_mem_psl2Range F hodd W houtJ
  have hcoatom : IsCoatom J := by
    apply Subgroup.isCoatom_of_index_prime
    rw [show J.index = 2 from CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two K
      (CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hodd)]
    norm_num
  have htop : R = ⊤ := hcoatom.2 R (lt_of_le_of_ne hJle hJne)
  rw [← MonoidHom.range_eq_top]
  exact htop

theorem localPi_ker_isPGroup (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    IsPGroup 2 (localPi F hodd W G).ker := by
  intro y
  have hyK : (y.val : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ localK F W G :=
    y.val.property
  obtain ⟨k, hk⟩ := CFSG.GroupTheory.exists_pow_prime_pow_mem_of_mem_sup
    (p := 2) (L := localX F) (T := localS F W G)
    (localS_sylow_K F hodd W G hLG hGSO).isPGroup
    (localS_le_normalizer_X F hodd W G) hyK
  refine ⟨k, ?_⟩
  have hpi : localPi F hodd W G (y.val ^ (2 ^ k)) = 1 := by
    rw [map_pow]
    have hy1 : localPi F hodd W G y = 1 := y.property
    rw [show localPi F hodd W G (y.val : localK F W G) = 1 from hy1]
    simp
  have hetaX : etaX F hodd
      (⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q) ^ (2 ^ k), hk⟩ :
        localX F) = 1 := by
    have hrel : localPi F hodd W G (y.val ^ (2 ^ k)) =
        etaX F hodd
          (⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q) ^ (2 ^ k), hk⟩ :
            localX F) := by
      rw [localPi_apply]
      rfl
    rwa [← hrel]
  have hx1 : (⟨(y.val : TauCeti.QuadraticMap.orthogonalGroup Q) ^ (2 ^ k), hk⟩ :
      localX F) = 1 := by
    apply etaX_injective F hodd
    rw [map_one]
    exact hetaX
  have hval : (y.val : TauCeti.QuadraticMap.orthogonalGroup Q) ^ (2 ^ k) = 1 := by
    have := congrArg Subtype.val hx1
    simpa using this
  apply Subtype.ext
  apply Subtype.ext
  simpa using hval

theorem localC_le_S (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    localC F W G ≤ localS F W G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSIn := localS_sylowIn_K F hodd W G hLG hGSO
  have hkerP := localPi_ker_isPGroup F hodd h3 W G hLG hGSO
  have hNle : (localPi F hodd W G).ker ≤
      (localS F W G).subgroupOf (localK F W G) := by
    have h := IsPGroup.le_sylow_of_normal (p := 2) hkerP hSIn.toSylow
    rwa [CFSG.Quasithin.IsSylowIn.coe_toSylow] at h
  intro c hc
  have hcK : c ∈ localK F W G := hc.1
  have hmemKer : (⟨c, hcK⟩ : localK F W G) ∈ (localPi F hodd W G).ker := by
    rw [localPi_ker_eq F hodd h3 W G]
    exact Subgroup.mem_subgroupOf.mpr hc
  exact Subgroup.mem_subgroupOf.mp (hNle hmemKer)

theorem localX_inf_localC_eq_bot (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    localX F ⊓ localC F W G = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨hxX, hxK, hxC⟩ := hx
  have hmemKer : (⟨x, hxK⟩ : localK F W G) ∈ (localPi F hodd W G).ker := by
    rw [localPi_ker_eq F hodd h3 W G]
    exact Subgroup.mem_subgroupOf.mpr ⟨hxK, hxC⟩
  have hxker1 : localPi F hodd W G ⟨x, hxK⟩ = 1 := hmemKer
  have hetaX : etaX F hodd ⟨x, hxX⟩ = 1 := by
    rw [localPi_apply] at hxker1
    exact hxker1
  have hx1 : (⟨x, hxX⟩ : localX F) = 1 := by
    apply etaX_injective F hodd
    rw [map_one]
    exact hetaX
  have hxone : x = 1 := congrArg Subtype.val hx1
  simpa using hxone

theorem localS_eq_P_inf_K (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hP : P = wreathO F W.D ⊓ G) :
    localS F W G = P ⊓ localK F W G := by
  have hPS : (wreathO F W.D ⊓ G) ⊓ localCG F G = localS F W G := by
    ext x
    constructor
    · rintro ⟨⟨hxT, hxG⟩, -, hxC0⟩
      have hxT0 : x ∈ wreathO F W.D ⊓ FiveDimensionalTPositive.C0 F := ⟨hxT, hxC0⟩
      rw [wreathO_inf_C0 F W.D] at hxT0
      exact ⟨hxT0, hxG⟩
    · rintro ⟨hxB, hxG⟩
      exact ⟨⟨Subgroup.mem_sup_left hxB, hxG⟩, hxG,
        (betaBaseO_le_C0 F W.D) hxB⟩
  have hKleCG := localK_le_CG F W G hLG
  have hPKleS : P ⊓ localK F W G ≤ localS F W G := by
    intro y hy
    have hyPCG : y ∈ P ⊓ localCG F G := ⟨hy.1, hKleCG hy.2⟩
    rwa [hP, hPS] at hyPCG
  have hSlePK : localS F W G ≤ P ⊓ localK F W G := by
    intro y hy
    refine ⟨?_, Subgroup.mem_sup_right hy⟩
    rw [hP]
    exact ⟨Subgroup.mem_sup_left hy.1, hy.2⟩
  exact le_antisymm hSlePK hPKleS

theorem localS_eq_P_inf_C0 (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hP : P = wreathO F W.D ⊓ G) :
    localS F W G = P ⊓ FiveDimensionalTPositive.C0 F := by
  rw [hP]
  ext x
  constructor
  · rintro ⟨hxB, hxG⟩
    exact ⟨⟨Subgroup.mem_sup_left hxB, hxG⟩, (betaBaseO_le_C0 F W.D) hxB⟩
  · rintro ⟨⟨hxT, hxG⟩, hxC0⟩
    have hxT0 : x ∈ wreathO F W.D ⊓ FiveDimensionalTPositive.C0 F := ⟨hxT, hxC0⟩
    rw [wreathO_inf_C0 F W.D] at hxT0
    exact ⟨hxT0, hxG⟩

structure TPositiveLocalPackage (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) where
  W : FiveDimensionalWreathData F
  T : Sylow 2 G
  P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)
  hP : P = (T : Subgroup G).map G.subtype
  hPw : P = wreathO F W.D ⊓ G
  X_le_G : localX F ≤ G
  X_le_K : localX F ≤ localK F W G
  K_le_CG : localK F W G ≤ localCG F G
  simple : IsSimpleGroup (localX F)
  noncomm : ¬ IsMulCommutative (localX F)
  S_sylow_CG : CFSG.Quasithin.IsSylowIn 2 (localS F W G) (localCG F G)
  S_sylow_K : CFSG.Quasithin.IsSylowIn 2 (localS F W G) (localK F W G)
  S_normalizes_X : localS F W G ≤ Subgroup.normalizer (localX F :
    Set (TauCeti.QuadraticMap.orthogonalGroup Q))
  pi_surjective : Function.Surjective (localPi F hodd W G)
  pi_ker_eq : (localPi F hodd W G).ker = (localC F W G).subgroupOf (localK F W G)
  pi_ker_isPGroup : IsPGroup 2 (localPi F hodd W G).ker
  C_le_S : localC F W G ≤ localS F W G
  X_inf_C : localX F ⊓ localC F W G = ⊥
  S_eq_P_inf_K : localS F W G = P ⊓ localK F W G
  S_eq_P_inf_C0 : localS F W G = P ⊓ FiveDimensionalTPositive.C0 F
  eX : localX F ≃* CFSG.GorensteinWalter.PSL2 K
  eX_toPGL : ∀ x : localX F,
    Matrix.ProjectiveSpecialLinearGroup.toPGL (eX x) = etaX F hodd x

@[expose]
noncomputable def localPackageOfData (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) (T : Sylow 2 G)
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin)
    (hPw : (T : Subgroup G).map G.subtype = wreathO F W.D ⊓ G) :
    TPositiveLocalPackage F hodd h3 G hLG hGSO where
  W := W
  T := T
  P := (T : Subgroup G).map G.subtype
  hP := rfl
  hPw := hPw
  X_le_G := localX_le_G F G hLG
  X_le_K := le_sup_left
  K_le_CG := localK_le_CG F W G hLG
  simple := tPositiveDerived_isSimpleGroup F hodd h3
  noncomm := tPositiveDerived_not_isMulCommutative F hodd h3
  S_sylow_CG := localS_sylowIn_CG F hodd W G hLG hGSO
  S_sylow_K := localS_sylowIn_K F hodd W G hLG hGSO
  S_normalizes_X := localS_le_normalizer_X F hodd W G
  pi_surjective := localPi_surjective F hodd h3 W G hLG hGSO
  pi_ker_eq := localPi_ker_eq F hodd h3 W G
  pi_ker_isPGroup := localPi_ker_isPGroup F hodd h3 W G hLG hGSO
  C_le_S := localC_le_S F hodd h3 W G hLG hGSO
  X_inf_C := localX_inf_localC_eq_bot F hodd h3 W G
  S_eq_P_inf_K := localS_eq_P_inf_K F hodd W G hLG _ hPw
  S_eq_P_inf_C0 := localS_eq_P_inf_C0 F W G _ hPw
  eX := eX F hodd h3
  eX_toPGL := toPGL_eX_apply F hodd h3

