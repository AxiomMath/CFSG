module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3UniBlock
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonU3TorusSU3
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersFrobenius
public import CFSG.RankThree.PartOne.K159G.PlaneGen

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CanonU3

open scoped BigOperators
open scoped Classical
open Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.RankThree.PartOne.KCUnitaryScalar CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.K159G
  CFSG.RankThree.PartOne.KCUnitaryCoord
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks
  CFSG.ShultStronglyClosedTI.OddPrimeInverters

theorem squarefree_minpoly_toLin_of_conj_diagonal {N : ℕ} {K : Type} [Field K]
    (P A : GL (Fin N) K) (d : Fin N → K)
    (hD : (((P⁻¹ * A * P : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) =
      Matrix.diagonal d) :
    Squarefree (minpoly K (Matrix.GeneralLinearGroup.toLin A :
      Module.End K (Fin N → K))) := by
  classical
  let D : GL (Fin N) K := P⁻¹ * A * P
  have hDm : ((D : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = Matrix.diagonal d := hD
  let s : Finset K := Finset.univ.image d
  let q : K[X] := ∏ a ∈ s, (X - C a)
  have hq : Squarefree q := by
    have hsep : q.Separable := by
      rw [show q = ∏ a ∈ s, (X - C (id a)) from rfl]
      refine Polynomial.separable_prod_X_sub_C_iff'.mpr ?_
      intro x _ y _ hxy
      exact hxy
    exact hsep.squarefree
  have hsingle : ∀ (i : Fin N) (c : K), (Matrix.GeneralLinearGroup.toLin D :
      Module.End K (Fin N → K)) (Pi.single i c) = d i • Pi.single i c := by
    intro i c
    rw [Matrix.GeneralLinearGroup.toLin_apply]
    change (D : GL (Fin N) K) *ᵥ (Pi.single i c : Fin N → K) = d i • Pi.single i c
    rw [hDm, Matrix.diagonal_mulVec_single]
    ext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [hji]
  have heval : ∀ i, q.eval (d i) = 0 := by
    intro i
    rw [show q = ∏ a ∈ s, (X - C a) from rfl, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_image_of_mem d (Finset.mem_univ i)) (by simp)
  have hkill : ∀ (i : Fin N) (c : K),
      (aeval (Matrix.GeneralLinearGroup.toLin D : Module.End K (Fin N → K))) q
        (Pi.single i c) = 0 := by
    intro i c
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hsingle i c), heval i, zero_smul]
  have hDzero : (aeval (Matrix.GeneralLinearGroup.toLin D :
      Module.End K (Fin N → K))) q = 0 := by
    apply LinearMap.ext
    intro v
    calc (aeval (Matrix.GeneralLinearGroup.toLin D : Module.End K (Fin N → K))) q v
        = (aeval (Matrix.GeneralLinearGroup.toLin D : Module.End K (Fin N → K))) q
            (∑ i, Pi.single i (v i)) := by
          rw [Finset.univ_sum_single]
      _ = ∑ i, (aeval (Matrix.GeneralLinearGroup.toLin D :
            Module.End K (Fin N → K))) q (Pi.single i (v i)) := by rw [map_sum]
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          exact hkill i (v i)
  have hAeq : (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin N → K)) =
      ↑(Matrix.GeneralLinearGroup.toLin P) *
        ↑(Matrix.GeneralLinearGroup.toLin D) *
        ↑(Matrix.GeneralLinearGroup.toLin P)⁻¹ := by
    have hPD : (Matrix.GeneralLinearGroup.toLin A :
        LinearMap.GeneralLinearGroup K (Fin N → K)) =
        Matrix.GeneralLinearGroup.toLin P * Matrix.GeneralLinearGroup.toLin D *
          (Matrix.GeneralLinearGroup.toLin P)⁻¹ := by
      rw [show D = P⁻¹ * A * P from rfl, map_mul, map_mul, map_inv]
      group
    exact congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (u : Module.End K (Fin N → K))) hPD
  have hxzero : (aeval (Matrix.GeneralLinearGroup.toLin A :
      Module.End K (Fin N → K))) q = 0 := by
    rw [hAeq, aeval_units_conj, hDzero, mul_zero, zero_mul]
  have hdvd : minpoly K (Matrix.GeneralLinearGroup.toLin A :
      Module.End K (Fin N → K)) ∣ q :=
    minpoly.dvd K (Matrix.GeneralLinearGroup.toLin A : Module.End K (Fin N → K)) hxzero
  exact hq.squarefree_of_dvd hdvd

theorem unitaryPrimaryData_toLin_of_conj_diagonal {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A P : primeFormUnitary h (idGram K N)}
    {d : Fin N → K}
    (hD : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d) :
    UnitaryPrimaryData h.bar (idForm h N)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) := by
  refine ⟨h.bar_bar, idForm_isSymm h N, idForm_separatingLeft h N,
    (toLin_mem_sesqUnitaryGroup_iff (A : GL (Fin N) K)).mpr A.2, ?_⟩
  exact squarefree_minpoly_toLin_of_conj_diagonal (P : GL (Fin N) K) (A : GL (Fin N) K) d hD

theorem specialBlock_fix_of_conj_diagonal {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    {A P : primeFormUnitary h (idGram K N)} {d : Fin N → K}
    (hD : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
    {g : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hg : g ∈ specialBlock (idForm h N)
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ))
    {s : Fin N} (hs : d s ≠ μ) :
    (g : Module.End K (Fin N → K))
        ((Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) : Module.End K (Fin N → K))
          (Pi.single s 1)) =
      (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) : Module.End K (Fin N → K))
        (Pi.single s 1) := by
  classical
  let D : GL (Fin N) K := P⁻¹ * A * P
  let Dm : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin D
  let u : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K)
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let v : Fin N → K := u (Pi.single s 1)
  have hDm : (D : Matrix (Fin N) (Fin N) K) = Matrix.diagonal d := hD
  have hDsingle : Dm (Pi.single s 1) = d s • Pi.single s 1 := by
    rw [Matrix.GeneralLinearGroup.toLin_apply]
    change (D : GL (Fin N) K) *ᵥ (Pi.single s 1 : Fin N → K) = d s • Pi.single s 1
    rw [hDm, Matrix.diagonal_mulVec_single]
    ext j
    by_cases hji : j = s
    · subst hji; simp
    · simp [hji]
  have hmult : x * u = u * Dm := by
    have hA : (A : GL (Fin N) K) = (P : GL (Fin N) K) * D * (P : GL (Fin N) K)⁻¹ := by
      rw [show D = P⁻¹ * A * P from rfl]
      symm
      calc (P : GL (Fin N) K) * (P⁻¹ * A * P) * (P : GL (Fin N) K)⁻¹
          = ((P : GL (Fin N) K) * P⁻¹) * A * ((P : GL (Fin N) K) * (P : GL (Fin N) K)⁻¹) := by
            group
        _ = A := by simp
    have hAP : (A : GL (Fin N) K) * (P : GL (Fin N) K) = (P : GL (Fin N) K) * D := by
      rw [hA]
      calc ((P : GL (Fin N) K) * D * P⁻¹) * P = (P : GL (Fin N) K) * D * (P⁻¹ * P) := by
            group
        _ = (P : GL (Fin N) K) * D := by simp
    have hlin := congrArg (fun z : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin z : LinearMap.GeneralLinearGroup K (Fin N → K))) hAP
    have hlin' : (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) *
          Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) *
          Matrix.GeneralLinearGroup.toLin D := by
      rw [← map_mul, ← map_mul]; exact hlin
    exact congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (z : Module.End K (Fin N → K))) hlin'
  have hvne : v ≠ 0 := by
    have hsingle : (Pi.single s 1 : Fin N → K) ≠ 0 := by
      intro h0
      have := congrFun h0 s
      simp at this
    intro hv0
    apply hsingle
    have h1 : (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
        Module.End K (Fin N → K)) (u (Pi.single s 1)) = Pi.single s 1 := by
      calc (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
            Module.End K (Fin N → K)) (u (Pi.single s 1))
          = ((↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
              Module.End K (Fin N → K)) *
              (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
                Module.End K (Fin N → K))) (Pi.single s 1) := rfl
        _ = (1 : Module.End K (Fin N → K)) (Pi.single s 1) := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = Pi.single s 1 := rfl
    rw [show u (Pi.single s 1) = 0 from hv0, map_zero] at h1
    exact h1.symm
  have hxP : x v = d s • v := by
    calc x v = (x * u) (Pi.single s 1) := rfl
      _ = (u * Dm) (Pi.single s 1) := by rw [hmult]
      _ = u (Dm (Pi.single s 1)) := rfl
      _ = u (d s • Pi.single s 1) := by rw [hDsingle]
      _ = d s • u (Pi.single s 1) := by rw [map_smul]
  have hxEig : x.HasEigenvalue (d s) := by
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    have hmem : v ∈ x.eigenspace (d s) := by
      rw [Module.End.mem_eigenspace_iff]
      exact hxP
    rw [hbot] at hmem
    exact hvne (by simpa using hmem)
  have hb : (X - C (d s) : K[X]) ∈ primaryFactors x :=
    X_sub_C_mem_primaryFactors hxEig
  have hvmem : v ∈ primaryComponent x (X - C (d s)) :=
    mem_primaryComponent_X_sub_C.mpr hxP
  have hbar0 : h.bar μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ
    exact zero_ne_one hμ
  have hdual : dualPoly h.bar (X - C μ) = X - C μ := by
    rw [dualPoly_X_sub_C hbar0, inv_eq_of_mul_eq_one_right hμ]
  have hbS : (X - C (d s) : K[X]) ∉
      ({(X - C μ : K[X]), dualPoly h.bar (X - C μ)} : Set K[X]) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨?_, ?_⟩
    · intro heq
      apply hs
      have := congrArg (fun p : K[X] => p.coeff 0) heq
      simpa using this
    · rw [hdual]
      intro heq
      apply hs
      have := congrArg (fun p : K[X] => p.coeff 0) heq
      simpa using this
  have horbit := (mem_specialBlock.mp hg).1
  exact horbit.2 (X - C (d s)) hb hbS v hvmem

theorem toLin_conj_diagonal_apply {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {A P : primeFormUnitary h (idGram K N)} {d : Fin N → K}
    (hD : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d) (s : Fin N) :
    (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))
        ((Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) : Module.End K (Fin N → K))
          (Pi.single s 1)) =
      d s • (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) : Module.End K (Fin N → K))
        (Pi.single s 1) := by
  let D : GL (Fin N) K := P⁻¹ * A * P
  let Dm : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin D
  let u : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K)
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  have hDm : (D : Matrix (Fin N) (Fin N) K) = Matrix.diagonal d := hD
  have hDsingle : Dm (Pi.single s 1) = d s • Pi.single s 1 := by
    rw [Matrix.GeneralLinearGroup.toLin_apply]
    change (D : GL (Fin N) K) *ᵥ (Pi.single s 1 : Fin N → K) = d s • Pi.single s 1
    rw [hDm, Matrix.diagonal_mulVec_single]
    ext j
    by_cases hji : j = s
    · subst hji; simp
    · simp [hji]
  have hmult : x * u = u * Dm := by
    have hA : (A : GL (Fin N) K) = (P : GL (Fin N) K) * D * (P : GL (Fin N) K)⁻¹ := by
      rw [show D = P⁻¹ * A * P from rfl]
      symm
      calc (P : GL (Fin N) K) * (P⁻¹ * A * P) * (P : GL (Fin N) K)⁻¹
          = ((P : GL (Fin N) K) * P⁻¹) * A * ((P : GL (Fin N) K) * (P : GL (Fin N) K)⁻¹) := by
            group
        _ = A := by simp
    have hAP : (A : GL (Fin N) K) * (P : GL (Fin N) K) = (P : GL (Fin N) K) * D := by
      rw [hA]
      calc ((P : GL (Fin N) K) * D * P⁻¹) * P = (P : GL (Fin N) K) * D * (P⁻¹ * P) := by
            group
        _ = (P : GL (Fin N) K) * D := by simp
    have hlin := congrArg (fun z : GL (Fin N) K =>
      (Matrix.GeneralLinearGroup.toLin z : LinearMap.GeneralLinearGroup K (Fin N → K))) hAP
    have hlin' : (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) *
          Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) *
          Matrix.GeneralLinearGroup.toLin D := by
      rw [← map_mul, ← map_mul]; exact hlin
    exact congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (z : Module.End K (Fin N → K))) hlin'
  calc x (u (Pi.single s 1)) = (x * u) (Pi.single s 1) := rfl
    _ = (u * Dm) (Pi.single s 1) := by rw [hmult]
    _ = u (Dm (Pi.single s 1)) := rfl
    _ = u (d s • Pi.single s 1) := by rw [hDsingle]
    _ = d s • u (Pi.single s 1) := by rw [map_smul]

theorem apply_eq_self_of_mem_orthogonal_block {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    {A P : primeFormUnitary h (idGram K N)} {d : Fin N → K}
    (hD : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d)
    {μ : K}
    {p p' : Fin N} (hpp' : p ≠ p')
    {s : GL (Fin N) K} (hs : s ∈ blk h hpp')
    (hdp : d p = μ) (hdp' : d p' = μ)
    {v : Fin N → K}
    (hv : ∀ w ∈ primaryComponent
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))
      (X - C μ), idForm h N w v = 0) :
    (Matrix.GeneralLinearGroup.toLin
        ((P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹) :
        Module.End K (Fin N → K)) v = v := by
  classical
  let u : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K)
  let sE : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin s
  let x : Module.End K (Fin N → K) := Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let w : Fin N → K := (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
    Module.End K (Fin N → K)) v
  have hvw : u w = v := by
    calc u w = (u * (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
        Module.End K (Fin N → K))) v := rfl
      _ = (1 : Module.End K (Fin N → K)) v := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      _ = v := rfl
  obtain ⟨Y, hYmem, hYmat⟩ := (mem_blk_iff hpp').mp hs
  have hB : ∀ r : Fin N, d r = μ → w r = 0 := by
    intro r hr
    have hxr : x (u (Pi.single r 1)) = μ • (u (Pi.single r 1)) := by
      rw [toLin_conj_diagonal_apply (h := h) (A := A) (P := P) hD r, hr]
    have hmem : u (Pi.single r 1) ∈ primaryComponent x (X - C μ) :=
      mem_primaryComponent_X_sub_C.mpr hxr
    have h0 : idForm h N (u (Pi.single r 1)) v = 0 := hv _ hmem
    rw [← hvw] at h0
    have hP : ((((P : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map h.bar))ᵀ *
        (P : GL (Fin N) K) = 1 := by
      simpa [idGram] using (mem_primeFormUnitary.mp P.2)
    have hcalc : idForm h N (u (Pi.single r 1)) (u w) = w r := by
      change gramForm h (idGram K N)
        ((P : GL (Fin N) K) *ᵥ (Pi.single r 1 : Fin N → K))
        ((P : GL (Fin N) K) *ᵥ w) = w r
      rw [gramForm_mulVec]
      have hP' : ((((P : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map h.bar))ᵀ *
          idGram K N * (P : GL (Fin N) K) = 1 := by
        simpa [idGram] using hP
      rw [hP', gramForm_apply]
      simp only [idGram, Matrix.one_mulVec]
      have hsingle : (fun a => h.bar ((Pi.single r 1 : Fin N → K) a)) =
          (Pi.single r 1 : Fin N → K) := by
        funext a
        by_cases ha : a = r
        · subst ha; simp
        · simp [Pi.single, ha]
      rw [hsingle, single_one_dotProduct]
    rw [hcalc] at h0
    exact h0
  have hsw : ((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w = w := by
    ext k
    have hk := coordEmbed_mulVec (K := K) hpp'
      (Y : Matrix (Fin 2) (Fin 2) K) w k
    have hentry : (((s : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ w) k =
        (coordEmbed K p p' (Y : Matrix (Fin 2) (Fin 2) K) *ᵥ w) k := by
      rw [← hYmat]
    rw [hentry, hk]
    by_cases hkp : k = p
    · rw [if_pos hkp, hkp, hB p hdp, hB p' hdp']
      ring
    · by_cases hkp' : k = p'
      · rw [if_neg hkp, if_pos hkp', hkp', hB p hdp, hB p' hdp']
        ring
      · rw [if_neg hkp, if_neg hkp']
  have hsE : sE w = w := by
    rw [Matrix.GeneralLinearGroup.toLin_apply]
    exact hsw
  have hy : (Matrix.GeneralLinearGroup.toLin
      ((P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹) : Module.End K (Fin N → K)) =
      u * sE * (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
        Module.End K (Fin N → K)) := by
    rw [show (Matrix.GeneralLinearGroup.toLin
        ((P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹) :
        LinearMap.GeneralLinearGroup K (Fin N → K)) =
        Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) *
          Matrix.GeneralLinearGroup.toLin s *
          (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ from by
      rw [map_mul, map_mul, map_inv]]
    rfl
  rw [hy]
  have hu_inv : (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
      Module.End K (Fin N → K)) (u w) = w := by
    calc (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
          Module.End K (Fin N → K)) (u w)
        = ((↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
            Module.End K (Fin N → K)) * u) w := rfl
      _ = (1 : Module.End K (Fin N → K)) w := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      _ = w := rfl
  calc (u * sE * (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
        Module.End K (Fin N → K))) v
      = (u * sE * (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
          Module.End K (Fin N → K))) (u w) := by rw [hvw]
    _ = u (sE w) := by
          rw [show (u * sE * (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
              Module.End K (Fin N → K))) (u w) =
              (u * sE) ((↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
                Module.End K (Fin N → K)) (u w)) from rfl, hu_inv]
          rfl
    _ = u w := by rw [hsE]
    _ = v := hvw

theorem primeFormConjHom_eq_of_mem_blockImage_of_eq_on {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K)
    (A Ai P : primeFormUnitary h (idGram K N)) {d e : Fin N → K}
    (hd : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d)
    (he : (((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal e)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K)))
    (heI : ∀ r s : Fin N, d r = μ → d s = μ → e r = e s)
    {t : primeFormP h (idGram K N)}
    (ht : t ∈ blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ)) :
    primeFormConjHom h (idGram K N) Ai t = t := by
  classical
  let x : LinearMap.GeneralLinearGroup K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let Z := normOneScalars h (gramSU h (idGram K N)) N
  let π := QuotientGroup.mk' Z
  obtain ⟨g, hgcomap, hgt⟩ := Subgroup.mem_map.mp ht
  have hgS : Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) ∈
      specialBlock (idForm h N) x (X - C μ) := by
    rw [← toLinSU_apply]
    exact Subgroup.mem_comap.mp hgcomap
  have hgc : Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) ∈ gl_centralizer x :=
    (mem_specialBlock.mp hgS).2.1
  have hgA : (g : GL (Fin N) K) * (A : GL (Fin N) K) =
      (A : GL (Fin N) K) * (g : GL (Fin N) K) := by
    apply Matrix.GeneralLinearGroup.toLin.injective
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hgc
    rw [map_mul, map_mul]
    simpa [x, toLinSU_apply] using hcomm
  let cP := MulAut.conj (P : GL (Fin N) K)
  let G : GL (Fin N) K := cP.symm (g : GL (Fin N) K)
  let D : GL (Fin N) K := cP.symm (A : GL (Fin N) K)
  let Dai : GL (Fin N) K := cP.symm (Ai : GL (Fin N) K)
  have hGmat : (G : Matrix (Fin N) (Fin N) K) =
      (P : GL (Fin N) K)⁻¹ * (g : GL (Fin N) K) * (P : GL (Fin N) K) := by
    dsimp only [G, cP]
    rw [MulAut.conj_symm_apply]
    simp
  have hDmat : (D : Matrix (Fin N) (Fin N) K) = Matrix.diagonal d := by
    dsimp only [D, cP]
    rw [MulAut.conj_symm_apply]
    simpa using hd
  have hDaimat : (Dai : Matrix (Fin N) (Fin N) K) = Matrix.diagonal e := by
    dsimp only [Dai, cP]
    rw [MulAut.conj_symm_apply]
    simpa using he
  have hGD : G * D = D * G := by
    have h := congrArg cP.symm hgA
    simpa [G, D, map_mul] using h
  have hGent : ∀ r s : Fin N, (G : Matrix (Fin N) (Fin N) K) r s * d s =
      d r * (G : Matrix (Fin N) (Fin N) K) r s := by
    intro r s
    have h := congrFun (congrFun (congrArg (fun z : GL (Fin N) K =>
      ((z : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) hGD) r) s
    change ((G : Matrix (Fin N) (Fin N) K) * (D : Matrix (Fin N) (Fin N) K)) r s =
      ((D : Matrix (Fin N) (Fin N) K) * (G : Matrix (Fin N) (Fin N) K)) r s at h
    rw [hDmat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    exact h
  have hGfix : ∀ s : Fin N, d s ≠ μ →
      (G : Matrix (Fin N) (Fin N) K) *ᵥ (Pi.single s 1) = Pi.single s 1 := by
    intro s hs
    have hfix := specialBlock_fix_of_conj_diagonal (h := h) (A := A) (P := P)
      (d := d) hd (μ := μ) hμ ha hgS hs
    have hG' : G = (P : GL (Fin N) K)⁻¹ * (g : GL (Fin N) K) * (P : GL (Fin N) K) := by
      dsimp only [G, cP]
      rw [MulAut.conj_symm_apply]
    have hGconj : (Matrix.GeneralLinearGroup.toLin G : Module.End K (Fin N → K)) =
        (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
          Module.End K (Fin N → K)) *
          (Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) :
            Module.End K (Fin N → K)) *
          (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
            Module.End K (Fin N → K)) := by
      have h : (Matrix.GeneralLinearGroup.toLin G :
          LinearMap.GeneralLinearGroup K (Fin N → K)) =
          (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ *
            Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) *
            Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) := by
        rw [hG', map_mul, map_mul, map_inv]
      exact congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin N → K) =>
        (z : Module.End K (Fin N → K))) h
    have hu_inv : (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
        Module.End K (Fin N → K))
        ((Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
          Module.End K (Fin N → K)) (Pi.single s 1)) = Pi.single s 1 := by
      calc (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
            Module.End K (Fin N → K))
            ((Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
              Module.End K (Fin N → K)) (Pi.single s 1))
          = ((↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
              Module.End K (Fin N → K)) *
              (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
                Module.End K (Fin N → K))) (Pi.single s 1) := rfl
        _ = (1 : Module.End K (Fin N → K)) (Pi.single s 1) := by
              rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        _ = Pi.single s 1 := rfl
    have hGend : (Matrix.GeneralLinearGroup.toLin G : Module.End K (Fin N → K))
        (Pi.single s 1) = Pi.single s 1 := by
      rw [hGconj]
      calc ((↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
            Module.End K (Fin N → K)) *
            (Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) :
              Module.End K (Fin N → K)) *
            (Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
              Module.End K (Fin N → K))) (Pi.single s 1)
          = (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
              Module.End K (Fin N → K))
              ((Matrix.GeneralLinearGroup.toLin (g : GL (Fin N) K) :
                Module.End K (Fin N → K))
                ((Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
                  Module.End K (Fin N → K)) (Pi.single s 1))) := rfl
        _ = (↑(Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K))⁻¹ :
              Module.End K (Fin N → K))
              ((Matrix.GeneralLinearGroup.toLin (P : GL (Fin N) K) :
                Module.End K (Fin N → K)) (Pi.single s 1)) := by rw [hfix]
        _ = Pi.single s 1 := hu_inv
    simpa [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply] using hGend
  have hGe : (G : Matrix (Fin N) (Fin N) K) * Matrix.diagonal e =
      Matrix.diagonal e * (G : Matrix (Fin N) (Fin N) K) := by
    ext r s
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hsI : d s = μ
    · by_cases hrI : d r = μ
      · rw [heI r s hrI hsI]
        ring
      · have hdr : d r ≠ μ := hrI
        have hzero : (G : Matrix (Fin N) (Fin N) K) r s = 0 := by
          have h := hGent r s
          rw [hsI, mul_comm ((G : Matrix (Fin N) (Fin N) K) r s) μ] at h
          have h2 : (d r - μ) * (G : Matrix (Fin N) (Fin N) K) r s = 0 := by
            rw [sub_mul, ← h, sub_self]
          exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hdr)
        rw [hzero, mul_zero, zero_mul]
    · have hentry : (G : Matrix (Fin N) (Fin N) K) r s =
          if r = s then 1 else 0 := by
        have h := congrFun (hGfix s hsI) r
        rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
        rw [h]
        by_cases hrs : r = s
        · subst hrs; simp
        · simp [Pi.single_eq_of_ne hrs, hrs]
      by_cases hrs : r = s
      · subst hrs
        ring
      · rw [hentry]
        simp [hrs]
  have hGDai : G * Dai = Dai * G := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDaimat]
    exact hGe
  have hgAi : (g : GL (Fin N) K) * (Ai : GL (Fin N) K) =
      (Ai : GL (Fin N) K) * (g : GL (Fin N) K) := by
    have h := congrArg cP hGDai
    simpa [G, Dai, map_mul] using h
  have hconj : (Ai : GL (Fin N) K) * (g : GL (Fin N) K) * (Ai : GL (Fin N) K)⁻¹ =
      (g : GL (Fin N) K) := by
    rw [← hgAi, mul_assoc, mul_inv_cancel, mul_one]
  have hgt' : t = (g : primeFormP h (idGram K N)) := hgt.symm
  rw [hgt', primeFormConjHom_mk]
  congr 1
  apply Subtype.ext
  exact hconj

theorem not_isSolvable_inf_fixSubgroup_of_diagonal {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) (hN : 3 ≤ N)
    (A Ai P : primeFormUnitary h (idGram K N)) {d e : Fin N → K}
    (hd : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d)
    (he : (((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal e)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    {p p' : Fin N} (hpp' : p ≠ p') (hdp : d p = μ) (hdp' : d p' = μ) (hep : e p = e p') :
    ¬ IsSolvable ↥(blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K N) Ai)) := by
  classical
  let x : LinearMap.GeneralLinearGroup K (Fin N → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)
  let S : Subgroup (GL (Fin N) K) := blk h hpp'
  let HGL : Subgroup (GL (Fin N) K) := S.map (MulAut.conj (P : GL (Fin N) K)).toMonoidHom
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hSperf : Group.IsPerfect S := by
    haveI : Group.IsPerfect (coordSU h hpp') := isPerfect_coordSU h hq hpp'
    exact Group.IsPerfect.map (f := (primeFormUnitary h (idGram K N)).subtype) (H := coordSU h hpp')
  have hSle : S ≤ gramSU h (idGram K N) := by
    intro s hs
    have hsU : s ∈ unitarySU 2 f K N := blk_le_unitarySU (h := h) hpp' hs
    rwa [unitarySU_eq_gramSU h N] at hsU
  have hHperf : Group.IsPerfect HGL := by
    haveI : Group.IsPerfect S := hSperf
    exact Group.IsPerfect.map (f := (MulAut.conj (P : GL (Fin N) K)).toMonoidHom) (H := S)
  have hHle : HGL ≤ gramSU h (idGram K N) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hy
    exact conj_mem_gramSU h (idGram K N) P.2 (hSle hs)
  let Z := normOneScalars h (gramSU h (idGram K N)) N
  let π := QuotientGroup.mk' Z
  let Φ : HGL →* primeFormP h (idGram K N) :=
    { toFun := fun y => π ⟨(y : GL (Fin N) K), hHle y.2⟩
      map_one' := by
        apply congrArg π
        apply Subtype.ext
        rfl
      map_mul' := fun y z => by
        apply congrArg π
        apply Subtype.ext
        rfl }
  let T : Subgroup (primeFormP h (idGram K N)) := Φ.range
  have hTperf : Group.IsPerfect T := Group.IsPerfect.range Φ
  have hH : UnitaryPrimaryData h.bar (idForm h N) x :=
    unitaryPrimaryData_toLin_of_conj_diagonal h hd
  have conj_eq : ∀ B : primeFormUnitary h (idGram K N),
      (B : GL (Fin N) K) = (P : GL (Fin N) K) *
        (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) *
        (P : GL (Fin N) K)⁻¹ := by
    intro B
    have hco : (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        (P : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K) * (P : GL (Fin N) K) := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    symm
    calc (P : GL (Fin N) K) *
          (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) *
          (P : GL (Fin N) K)⁻¹
        = (P : GL (Fin N) K) * ((P : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K) *
            (P : GL (Fin N) K)) * (P : GL (Fin N) K)⁻¹ := by rw [hco]
      _ = ((P : GL (Fin N) K) * P⁻¹) * (B : GL (Fin N) K) *
            ((P : GL (Fin N) K) * (P : GL (Fin N) K)⁻¹) := by simp [mul_assoc]
      _ = (B : GL (Fin N) K) := by simp [mul_inv_cancel]
  have hcommDiag : ∀ s : GL (Fin N) K, s ∈ S →
      s * ((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
        ((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) * s := by
    intro s hs
    obtain ⟨sU, hsU, rfl⟩ := Subgroup.mem_map.mp hs
    have hmem := coordSU_le_centralizer_diagonal h hpp' d (hdp.trans hdp'.symm)
      (D := P⁻¹ * A * P) hd
    have h1 := hmem hsU
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have h2 : (sU : GL (Fin N) K) *
        (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) *
          (sU : GL (Fin N) K) := by
      exact congrArg (fun z : primeFormUnitary h (idGram K N) => (z : GL (Fin N) K)) h1
    simpa using h2
  have hcommDiagAi : ∀ s : GL (Fin N) K, s ∈ S →
      s * ((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
        ((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) * s := by
    intro s hs
    obtain ⟨sU, hsU, rfl⟩ := Subgroup.mem_map.mp hs
    have hmem := coordSU_le_centralizer_diagonal h hpp' e hep
      (D := P⁻¹ * Ai * P) he
    have h1 := hmem hsU
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    have h2 : (sU : GL (Fin N) K) *
        (((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        (((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) *
          (sU : GL (Fin N) K) := by
      exact congrArg (fun z : primeFormUnitary h (idGram K N) => (z : GL (Fin N) K)) h1
    simpa using h2
  have hspecial : ∀ y : HGL,
      Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) ∈
        specialBlock (idForm h N) x (X - C μ) := by
    intro y
    obtain ⟨s, hs, hy⟩ := Subgroup.mem_map.mp y.2
    have hsg : s ∈ gramSU h (idGram K N) := hSle hs
    have hyU : (P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹ ∈
        primeFormUnitary h (idGram K N) :=
      (conj_mem_gramSU h (idGram K N) P.2 hsg).1
    have hyGL : (y : GL (Fin N) K) = (P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹ := by
      have hyconj : (MulAut.conj (P : GL (Fin N) K)) s = (y : GL (Fin N) K) := hy
      rw [← hyconj, MulAut.conj_apply]
    have hgU : Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) ∈
        sesqUnitaryGroup (idForm h N) := by
      rw [hyGL]
      exact (toLin_mem_sesqUnitaryGroup_iff (h := h) (n := N)
        ((P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹)).mpr hyU
    have hcommA : Commute (Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) :
        Module.End K (Fin N → K)) (x : Module.End K (Fin N → K)) := by
      have hDcomm : s * ((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
          ((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) * s :=
        hcommDiag s hs
      have hAdef : (A : GL (Fin N) K) =
          (P : GL (Fin N) K) * ((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) *
            (P : GL (Fin N) K)⁻¹ := conj_eq A
      have hyA : (y : GL (Fin N) K) * (A : GL (Fin N) K) =
          (A : GL (Fin N) K) * (y : GL (Fin N) K) := by
        have hyconj : (MulAut.conj (P : GL (Fin N) K)) s = (y : GL (Fin N) K) := hy
        have hDconj : (MulAut.conj (P : GL (Fin N) K))
            ((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
            (A : GL (Fin N) K) := by
          rw [MulAut.conj_apply, conj_eq A]
        simpa only [map_mul, hyconj, hDconj] using
          congrArg (MulAut.conj (P : GL (Fin N) K)) (hcommDiag s hs)
      have hyEnd : (Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) :
          Module.End K (Fin N → K)) * (x : Module.End K (Fin N → K)) =
          (x : Module.End K (Fin N → K)) * (Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) :
            Module.End K (Fin N → K)) := by
        have h := congrArg (fun z : GL (Fin N) K =>
          (Matrix.GeneralLinearGroup.toLin z : LinearMap.GeneralLinearGroup K (Fin N → K))) hyA
        have h' : (Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) :
            LinearMap.GeneralLinearGroup K (Fin N → K)) *
            Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) =
            Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) *
              Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) := by
          rw [← map_mul, ← map_mul]; exact h
        exact congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin N → K) =>
          (z : Module.End K (Fin N → K))) h'
      exact hyEnd
    have hid : ∀ v : Fin N → K,
        (∀ w ∈ primaryComponent (x : Module.End K (Fin N → K)) (X - C μ),
          idForm h N w v = 0) →
          (Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) :
            Module.End K (Fin N → K)) v = v := by
      intro v hv
      have hfix := apply_eq_self_of_mem_orthogonal_block (h := h) (A := A) (P := P)
        (d := d) hd (μ := μ) hpp' hs hdp hdp' hv
      rw [hyGL]
      exact hfix
    have hdet : LinearMap.det (Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) :
        Module.End K (Fin N → K)) = 1 := by
      have hSU : Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) ∈
          sesqSpecialUnitaryGroup (idForm h N) :=
        (toLin_mem_sesqSpecialUnitaryGroup_iff h (idGram K N) (y : GL (Fin N) K)).mpr
          (hHle y.2)
      exact (mem_sesqSpecialUnitaryGroup.mp hSU).2
    exact mem_specialBlock_of_degree_one (hK := h) hH hμ ha hgU hcommA hid hdet
  have hTblock : T ≤ blockImage h x (X - C μ) := by
    intro t ht
    obtain ⟨y, rfl⟩ := ht
    have hySp : Matrix.GeneralLinearGroup.toLin (y : GL (Fin N) K) ∈
        specialBlock (idForm h N) x (X - C μ) := hspecial y
    have hmem : (⟨(y : GL (Fin N) K), hHle y.2⟩ : gramSU h (idGram K N)) ∈
        (specialBlock (idForm h N) x (X - C μ)).comap (toLinSU h N) := by
      rw [Subgroup.mem_comap]
      exact hySp
    exact Subgroup.mem_map.mpr ⟨⟨(y : GL (Fin N) K), hHle y.2⟩, hmem, rfl⟩
  have hTfix : T ≤ fixSubgroup (primeFormConjHom h (idGram K N) Ai) := by
    intro t ht
    obtain ⟨y, rfl⟩ := ht
    rw [mem_fixSubgroup]
    obtain ⟨s, hs, hy⟩ := Subgroup.mem_map.mp y.2
    have hyGL : (y : GL (Fin N) K) = (P : GL (Fin N) K) * s * (P : GL (Fin N) K)⁻¹ := by
      have hyconj : (MulAut.conj (P : GL (Fin N) K)) s = (y : GL (Fin N) K) := hy
      rw [← hyconj, MulAut.conj_apply]
    have hAidef : (Ai : GL (Fin N) K) =
        (P : GL (Fin N) K) * ((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) *
          (P : GL (Fin N) K)⁻¹ := conj_eq Ai
    have hsE : s * ((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
        ((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) * s :=
      hcommDiagAi s hs
    have hyAi : (y : GL (Fin N) K) * (Ai : GL (Fin N) K) =
        (Ai : GL (Fin N) K) * (y : GL (Fin N) K) := by
      have hyconj : (MulAut.conj (P : GL (Fin N) K)) s = (y : GL (Fin N) K) := hy
      have hEconj : (MulAut.conj (P : GL (Fin N) K))
          ((P⁻¹ * Ai * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) =
          (Ai : GL (Fin N) K) := by
        rw [MulAut.conj_apply, conj_eq Ai]
      simpa only [map_mul, hyconj, hEconj] using
        congrArg (MulAut.conj (P : GL (Fin N) K)) hsE
    have hconj : (Ai : GL (Fin N) K) * (y : GL (Fin N) K) * (Ai : GL (Fin N) K)⁻¹ =
        (y : GL (Fin N) K) := by
      rw [← hyAi]
      group
    let g : gramSU h (idGram K N) := ⟨(y : GL (Fin N) K), hHle y.2⟩
    have hΦ : Φ y = (g : primeFormP h (idGram K N)) := rfl
    rw [hΦ, primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    exact hconj
  have hTle : T ≤ blockImage h x (X - C μ) ⊓ fixSubgroup (primeFormConjHom h (idGram K N) Ai) :=
    le_inf hTblock hTfix
  have hTne : T ≠ ⊥ := by
    intro hbot
    let s0 : GL (Fin N) K :=
      ((swapCoord h hpp' : primeFormUnitary h (idGram K N)) : GL (Fin N) K)
    have hs0 : s0 ∈ S := by
      refine Subgroup.mem_map.mpr ⟨swapCoord h hpp', swapCoord_mem_coordSU h hpp', rfl⟩
    let y0 : HGL := ⟨(P : GL (Fin N) K) * s0 * (P : GL (Fin N) K)⁻¹,
      Subgroup.mem_map.mpr ⟨s0, hs0, rfl⟩⟩
    have hΦ1 : Φ y0 = 1 := by
      have : Φ y0 ∈ T := ⟨y0, rfl⟩
      rw [hbot] at this
      simpa using this
    have hZ : (⟨(y0 : GL (Fin N) K), hHle y0.2⟩ : gramSU h (idGram K N)) ∈ Z :=
      (QuotientGroup.eq_one_iff _).mp hΦ1
    obtain ⟨c, -, -, hscalar⟩ := mem_normOneScalars.mp hZ
    have hy0scalar : (y0 : GL (Fin N) K) = GeneralLinearGroup.scalar (Fin N) c := hscalar
    have hs0scalar : s0 = GeneralLinearGroup.scalar (Fin N) c := by
      calc s0 = (P : GL (Fin N) K)⁻¹ * (y0 : GL (Fin N) K) * (P : GL (Fin N) K) := by
            change s0 = (P : GL (Fin N) K)⁻¹ *
              ((P : GL (Fin N) K) * s0 * (P : GL (Fin N) K)⁻¹) * (P : GL (Fin N) K)
            group
        _ = (P : GL (Fin N) K)⁻¹ * GeneralLinearGroup.scalar (Fin N) c *
              (P : GL (Fin N) K) := by rw [hy0scalar]
        _ = GeneralLinearGroup.scalar (Fin N) c := by
            have hcomm : (P : GL (Fin N) K) * GeneralLinearGroup.scalar (Fin N) c =
                GeneralLinearGroup.scalar (Fin N) c * (P : GL (Fin N) K) :=
              (commute_scalar c (P : GL (Fin N) K)).eq
            calc (P : GL (Fin N) K)⁻¹ * GeneralLinearGroup.scalar (Fin N) c *
                  (P : GL (Fin N) K)
                = (P : GL (Fin N) K)⁻¹ *
                    (GeneralLinearGroup.scalar (Fin N) c * (P : GL (Fin N) K)) := by rw [mul_assoc]
              _ = (P : GL (Fin N) K)⁻¹ *
                    ((P : GL (Fin N) K) * GeneralLinearGroup.scalar (Fin N) c) := by rw [hcomm]
              _ = GeneralLinearGroup.scalar (Fin N) c := by group
    have h1 : (((s0 : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) p p' = 1 := by
      exact swapCoord_apply h hpp'
    have h0 : (((s0 : GL (Fin N) K)) : Matrix (Fin N) (Fin N) K) p p' = 0 := by
      rw [hs0scalar]
      simp [Matrix.scalar_apply, hpp']
    rw [h1] at h0
    exact one_ne_zero h0
  have hTnontriv : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTne
  have hTnsolv : ¬ Group.IsSolvable T := Group.IsPerfect.not_isSolvable T
  intro hsol
  haveI : Group.IsSolvable ↥(blockImage h x (X - C μ) ⊓
      fixSubgroup (primeFormConjHom h (idGram K N) Ai)) := hsol
  have hTsolv : Group.IsSolvable T :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hTle) (Subgroup.inclusion_injective hTle)
  exact hTnsolv hTsolv

theorem not_isSolvable_and_of_diagonal {f N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (A A1 A2 P : primeFormUnitary h (idGram K N)) {c₁ c₂ : Kˣ}
    (hA1 : (A1 : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c₁)
    (hA2 : (A2 : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c₂)
    {d e1 e2 : Fin N → K}
    (hd : (((P⁻¹ * A * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal d)
    (he1 : (((P⁻¹ * A1 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal e1)
    (he2 : (((P⁻¹ * A2 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
      Matrix (Fin N) (Fin N) K) = Matrix.diagonal e2)
    {μ : K} (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ) ∈ primaryFactors
      ((Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K) : Module.End K (Fin N → K))))
    (hI : (Finset.univ.filter fun r => d r = μ).card = 3)
    (hmoves₂ : ∀ k : ℕ, ∃ t ∈ blockImage h
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K)) (X - C μ),
      (primeFormConjHom h (idGram K N) A2 * primeFormConjHom h (idGram K N) A1 ^ k) t ≠ t) :
    ¬ (IsSolvable ↥(blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K))
          (X - C μ) ⊓ fixSubgroup (primeFormConjHom h (idGram K N) A1)) ∧
      IsSolvable ↥(blockImage h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin N) K))
          (X - C μ) ⊓ fixSubgroup (primeFormConjHom h (idGram K N) A2))) := by
  classical
  let I : Finset (Fin N) := Finset.univ.filter fun r => d r = μ
  let e : I ≃ Fin 3 := Finset.equivFinOfCardEq hI
  let ι : Fin 3 → Fin N := fun k => (e.symm k : Fin N)
  have hιd : ∀ k, d (ι k) = μ := fun k => by
    have hmem : (e.symm k : Fin N) ∈ I := (e.symm k).2
    have hmem' : (e.symm k : Fin N) ∈ Finset.univ.filter (fun r => d r = μ) := by
      simpa [I] using hmem
    exact (Finset.mem_filter.mp hmem').2
  have hιinj : Function.Injective ι := by
    intro k l hkl
    apply e.symm.injective
    apply Subtype.ext
    exact hkl
  have hN : 3 ≤ N := by
    have hcard := Finset.card_le_univ I
    rw [show I.card = 3 from hI] at hcard
    simpa using hcard
  have hconj_scalar : ∀ c : Kˣ,
      (P : GL (Fin N) K)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) c * (P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    intro c
    rw [show (P : GL (Fin N) K)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin N) c *
          (P : GL (Fin N) K) =
        Matrix.GeneralLinearGroup.scalar (Fin N) c * (P : GL (Fin N) K)⁻¹ *
          (P : GL (Fin N) K) from by
      rw [(commute_scalar c ((P : GL (Fin N) K)⁻¹)).eq]]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hpow : ∀ (B : primeFormUnitary h (idGram K N)) (c : Kˣ),
      (B : GL (Fin N) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c →
      ∀ {g : Fin N → K},
        (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
          Matrix (Fin N) (Fin N) K) = Matrix.diagonal g →
      ∀ r, g r ^ 3 = c := by
    intro B c hB g hg r
    have hco : (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        (P : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K) * (P : GL (Fin N) K) := by
      simp [Subgroup.coe_mul, Subgroup.coe_inv]
    have hpowB : ((((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) ^ 3) =
        Matrix.GeneralLinearGroup.scalar (Fin N) c := by
      rw [hco, show ((P : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K) * (P : GL (Fin N) K)) ^ 3 =
          (P : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K) ^ 3 * (P : GL (Fin N) K) from conj_pow]
      rw [hB, hconj_scalar c]
    have hmat1 : (((((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) ^ 3 :
        GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = Matrix.diagonal (fun r => g r ^ 3) := by
      rw [Units.val_pow_eq_pow_val, hg, Matrix.diagonal_pow]
      simp [Pi.pow_apply]
    have hmat2 : (((((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) ^ 3 :
        GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
        Matrix.diagonal (fun _ => (c : K)) := by
      rw [hpowB]
      simp [Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [hmat1] at hmat2
    exact (Matrix.diagonal_eq_diagonal_iff.mp hmat2) r
  let u : Fin 3 → K := fun k => e1 (ι k)
  let v : Fin 3 → K := fun k => e2 (ι k)
  have hu : ∀ k, u k ^ 3 = (c₁ : K) := fun k =>
    hpow A1 c₁ hA1 he1 (ι k)
  have hv : ∀ k, v k ^ 3 = (c₂ : K) := fun k =>
    hpow A2 c₂ hA2 he2 (ι k)
  have huv : ∀ k : ℕ, ¬ ∀ r s, v r * u r ^ k = v s * u s ^ k := by
    intro k hconst
    let B : primeFormUnitary h (idGram K N) := A2 * A1 ^ k
    let cP : MulAut (GL (Fin N) K) := MulAut.conj (P : GL (Fin N) K)
    have hconjB : (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        cP.symm (B : GL (Fin N) K) := by
      dsimp only [cP]
      rw [MulAut.conj_symm_apply]
      simp
    have hconj2 : (((P⁻¹ * A2 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        cP.symm (A2 : GL (Fin N) K) := by
      dsimp only [cP]
      rw [MulAut.conj_symm_apply]
      simp
    have hconj1 : (((P⁻¹ * A1 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        cP.symm (A1 : GL (Fin N) K) := by
      dsimp only [cP]
      rw [MulAut.conj_symm_apply]
      simp
    have hcoB : (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K)) =
        ((P⁻¹ * A2 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) *
          (((P⁻¹ * A1 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) ^ k) := by
      calc (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K))
          = cP.symm (B : GL (Fin N) K) := hconjB
        _ = cP.symm ((A2 : GL (Fin N) K) * (A1 : GL (Fin N) K) ^ k) := by
              rw [show B = A2 * A1 ^ k from rfl]; rfl
        _ = cP.symm (A2 : GL (Fin N) K) * (cP.symm (A1 : GL (Fin N) K)) ^ k := by
              rw [map_mul, map_pow]
        _ = ((P⁻¹ * A2 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) *
              (((P⁻¹ * A1 * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) ^ k) := by
              rw [← hconj2, ← hconj1]
    have hBdiag : (((P⁻¹ * B * P : primeFormUnitary h (idGram K N)) : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K) = Matrix.diagonal (fun r => e2 r * e1 r ^ k) := by
      rw [hcoB, Units.val_mul, Units.val_pow_eq_pow_val, he2, he1, Matrix.diagonal_pow,
        Matrix.diagonal_mul_diagonal]
      rw [Matrix.diagonal_eq_diagonal_iff]
      intro r
      simp [Pi.pow_apply]
    have heI : ∀ r s : Fin N, d r = μ → d s = μ → e2 r * e1 r ^ k = e2 s * e1 s ^ k := by
      intro r s hr hs
      let kr : Fin 3 := e ⟨r, by simp [I, hr]⟩
      let ks : Fin 3 := e ⟨s, by simp [I, hs]⟩
      have hkr : ι kr = r := by
        dsimp only [ι, kr]
        rw [Equiv.symm_apply_apply]
      have hks : ι ks = s := by
        dsimp only [ι, ks]
        rw [Equiv.symm_apply_apply]
      have h := hconst kr ks
      simpa [u, v, hkr, hks] using h
    obtain ⟨t, ht, htne⟩ := hmoves₂ k
    have hfix := primeFormConjHom_eq_of_mem_blockImage_of_eq_on (h := h) (A := A)
      (Ai := B) (P := P) hd hBdiag hμ ha heI ht
    have hhom : primeFormConjHom h (idGram K N) B t =
        (primeFormConjHom h (idGram K N) A2 *
          primeFormConjHom h (idGram K N) A1 ^ k) t := by
      simp only [B, map_mul, map_pow]
    rw [hhom] at hfix
    exact htne hfix
  obtain ⟨r, s', hrs, hcase⟩ :=
    exists_eq_of_pow_three_eq u v (c := (c₁ : K)) (c' := (c₂ : K)) hu hv huv
  have hpne : ι r ≠ ι s' := fun h => hrs (hιinj h)
  have hdp : d (ι r) = μ := hιd r
  have hdp' : d (ι s') = μ := hιd s'
  intro hsol
  rcases hcase with heq | heq
  · have hep : e1 (ι r) = e1 (ι s') := heq
    exact (not_isSolvable_inf_fixSubgroup_of_diagonal (h := h) hf hN A A1 P hd he1
      hμ ha hpne hdp hdp' hep) hsol.1
  · have hep : e2 (ι r) = e2 (ι s') := heq
    exact (not_isSolvable_inf_fixSubgroup_of_diagonal (h := h) hf hN A A2 P hd he2
      hμ ha hpne hdp hdp' hep) hsol.2

end CFSG.LocalAnalysis.GLTheoremA.CanonU3
