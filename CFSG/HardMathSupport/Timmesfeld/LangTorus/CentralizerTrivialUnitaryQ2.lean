module

public import CFSG.Mathlib.LinearAlgebra.Matrix.DiagonalPermutationCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgExcCore
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256j
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CommonFactor

public section
namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.RankThree.Classical2 Matrix
open scoped MatrixGroups

section FixedMatrices
variable {L : Type} [Field L] [CharP L 2] {n : ℕ}

theorem stdUnitary_diag2n (sigma : L →+* L) {i j : Fin n} (hij : i ≠ j)
    (omega : Lˣ) (hbar : Units.map sigma.toMonoidHom omega = omega⁻¹) :
    stdUnitary sigma (Matrix.SpecialLinearGroup.diag2n hij (omega : L) omega.ne_zero) =
      Matrix.SpecialLinearGroup.diag2n hij (omega : L) omega.ne_zero := by
  let d : Fin n → L := fun k => if k = i then (omega : L) else
    if k = j then (omega : L)⁻¹ else 1
  have hcoe : ((Matrix.SpecialLinearGroup.diag2n hij (omega : L) omega.ne_zero : SL(n, L)) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal d := Matrix.SpecialLinearGroup.diag2n_coe hij (omega : L) omega.ne_zero
  have hmap : (Matrix.diagonal d).map sigma =
      Matrix.diagonal (fun k => (d k)⁻¹) := by
    rw [Matrix.diagonal_map (map_zero sigma)]
    congr 1
    funext k
    by_cases hki : k = i
    · subst k
      have h := congrArg (fun z : Lˣ => (z : L)) hbar
      simpa [d] using h
    · by_cases hkj : k = j
      · subst k
        have h := congrArg (fun z : Lˣ => (z : L)) (map_inv (Units.map sigma.toMonoidHom) omega)
        rw [hbar] at h
        simpa [d, hki] using h
      · simp [d, hki, hkj]
  have hinv : (Matrix.diagonal (fun k => (d k)⁻¹))⁻¹ = Matrix.diagonal d := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    have hk : d k ≠ 0 := by
      by_cases hki : k = i
      · subst k; simpa [d] using omega.ne_zero
      · by_cases hkj : k = j
        · subst k; simpa [d, hki] using (omega⁻¹).ne_zero
        · simp [d, hki, hkj]
    exact mul_inv_cancel₀ hk
  apply Subtype.ext
  rw [coe_stdUnitary, hcoe, hmap, hinv, Matrix.diagonal_transpose]

theorem stdUnitary_eq_self_of_permMatrix
    {L : Type} [Field L] {n : ℕ} (sigma : L →+* L)
    (pi : Equiv.Perm (Fin n)) (X : SL(n, L))
    (hX : (X : Matrix (Fin n) (Fin n) L) = pi.permMatrix L) :
    stdUnitary sigma X = X := by
  have hmap : (pi.permMatrix L).map sigma = pi.permMatrix L := by
    ext a b
    simp [Equiv.Perm.permMatrix, map_zero, map_one]
  have hinv : (pi.permMatrix L)⁻¹ = (pi.permMatrix L)ᵀ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  apply Subtype.ext
  rw [coe_stdUnitary, hX, hmap, hinv, Matrix.transpose_transpose]

theorem eq_scalar_of_commute_stdUnitary_of_charTwo
    (sigma : L →+* L) (hn : 3 ≤ n) (omega : Lˣ) (hne : omega ≠ 1)
    (hbar : Units.map sigma.toMonoidHom omega = omega⁻¹)
    (M : Matrix (Fin n) (Fin n) L)
    (hcomm : ∀ X : SL(n, L), stdUnitary sigma X = X → M * (X : Matrix (Fin n) (Fin n) L) =
      (X : Matrix (Fin n) (Fin n) L) * M) :
    M = Matrix.scalar (Fin n) (M ⟨0, by omega⟩ ⟨0, by omega⟩) := by
  apply Matrix.eq_scalar_of_commute_diag2n_permMatrix hn omega hne M
  · intro i k hik
    exact hcomm _ (stdUnitary_diag2n sigma hik omega hbar)
  · intro i j
    let X : SL(n, L) := ⟨(Equiv.swap i j).permMatrix L, by
      rw [Matrix.det_permutation, Equiv.Perm.sign_swap']
      split_ifs <;> simp [CharTwo.neg_eq]⟩
    exact hcomm X (stdUnitary_eq_self_of_permMatrix sigma (Equiv.swap i j) X rfl)

end FixedMatrices

theorem conjSLn_eq_self_of_commute_stdUnitary
    {L : Type} [Field L] [CharP L 2] {nu : ℕ} (hnu : 3 ≤ nu)
    (sigma : L ≃+* L) (omega : Lˣ) (hne : omega ≠ 1)
    (hbar : Units.map sigma.toRingHom.toMonoidHom omega = omega⁻¹)
    {H : Type} [Group H] (psi : SL(nu, L) →* H)
    (hker : psi.ker ≤ Subgroup.center SL(nu, L))
    (hperf : Group.IsPerfect (fixSubgroup (stdUnitaryEquiv (ν := nu) sigma)))
    (M : GL (Fin nu) L)
    (hfix : ∀ X : SL(nu, L), stdUnitary sigma.toRingHom X = X → psi (conjSLn M X) = psi X) :
    ∀ X : SL(nu, L), conjSLn M X = X := by
  let C := fixSubgroup (stdUnitaryEquiv (ν := nu) sigma)
  let alpha : C →* SL(nu, L) := (conjSLn M).comp C.subtype
  have heq : ∀ X : C, alpha X = C.subtype X :=
    CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq psi hker hperf alpha C.subtype (fun X => by
      exact hfix X (by simpa only [C, mem_fixSubgroup, stdUnitaryEquiv_apply] using X.property))
  have hcomm : ∀ X : SL(nu, L), stdUnitary sigma.toRingHom X = X →
      (M : Matrix (Fin nu) (Fin nu) L) * X = (X : Matrix (Fin nu) (Fin nu) L) * M := by
    intro X hX
    have hmem : X ∈ C := by simpa only [C, mem_fixSubgroup, stdUnitaryEquiv_apply] using hX
    have h := congrArg (fun A : SL(nu, L) => (A : Matrix (Fin nu) (Fin nu) L)) (heq ⟨X, hmem⟩)
    change (M : Matrix (Fin nu) (Fin nu) L) * X * ((M⁻¹ : GL (Fin nu) L) : Matrix (Fin nu) (Fin nu) L) = X at h
    have hm := congrArg (fun A : Matrix (Fin nu) (Fin nu) L => A * (M : Matrix (Fin nu) (Fin nu) L)) h
    simpa only [Matrix.mul_assoc, M.inv_mul, Matrix.mul_one] using hm
  have hsc := eq_scalar_of_commute_stdUnitary_of_charTwo sigma.toRingHom
    hnu omega hne hbar (M : Matrix (Fin nu) (Fin nu) L) hcomm
  have hAll : ∀ X : SL(nu, L), (M : Matrix (Fin nu) (Fin nu) L) * X =
      (X : Matrix (Fin nu) (Fin nu) L) * M := by
    intro X
    rw [hsc]
    exact Matrix.scalar_comm _ (fun _ => Commute.all _ _) _
  intro X
  apply Subtype.ext
  rw [coe_conjSLn, hAll X, Matrix.mul_assoc, M.mul_inv, Matrix.mul_one]


theorem unitary_fixed_image_le_rationalComponent
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    {nu : ℕ} (hnu : 4 ≤ nu) (psi : SL(nu, L) →* ModGL tau L)
    (hpsi : psi.range = rootSpan tau L (componentRoots (rootCharHom a) i))
    (sigma : L ≃+* L) (hsigma : ∀ c, sigma c = c ^ 2)
    (z : ModGL tau L)
    (hnorm : ∀ g, g ∈ rootSpan tau L (componentRoots (rootCharHom a) i) ↔
      z * g * z⁻¹ ∈ rootSpan tau L (componentRoots (rootCharHom a) i))
    (hconj : ∀ X : SL(nu, L), S.D.step (z * psi X * z⁻¹) =
      z * psi (stdUnitary sigma.toRingHom X) * z⁻¹) :
    ∀ X : SL(nu, L), stdUnitary sigma.toRingHom X = X →
      z * psi X * z⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  let C := fixSubgroup (stdUnitaryEquiv (ν := nu) sigma)
  have hNot : (nu, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have he := congrArg Prod.fst h
    omega
  have hCperf : Group.IsPerfect C :=
    ((stdUnitary_fixSubgroup Nat.prime_two (f := 1) (by decide) sigma
      (fun c => by simpa using hsigma c) (by omega)).2.1 hNot).1
  let f : C →* ModGL tau L := (MulAut.conj z).toMonoidHom.comp (psi.comp C.subtype)
  have hP : f.range ≤ rootSpan tau L (rationalRoots S.ρ (rootCharHom a) i) ⊓ S.D.model := by
    rintro g ⟨X, rfl⟩
    have hX : stdUnitary sigma.toRingHom (X : SL(nu, L)) = X := by
      simpa only [C, mem_fixSubgroup, stdUnitaryEquiv_apply] using X.property
    apply Subgroup.mem_inf.mpr
    constructor
    · rw [CFSG.StandardType.F4ExplicitPos.CommonFactor.rationalRoots_eq_componentRoots_of_orbitLength_one i hs]
      exact (hnorm _).mp (hpsi ▸ MonoidHom.mem_range.mpr ⟨X, rfl⟩)
    · rw [S.D.mem_model]
      constructor
      · exact (rootSpan_le_adjointGroup L (componentRoots (rootCharHom a) i))
          ((hnorm _).mp (hpsi ▸ MonoidHom.mem_range.mpr ⟨X, rfl⟩))
      · change S.D.step (z * psi X * z⁻¹) = z * psi X * z⁻¹
        rw [hconj, hX]
  haveI : Group.IsPerfect C := hCperf
  have hPperf : ⁅f.range, f.range⁆ = f.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range f)
  have hle := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256j.le_rationalComponent_of_perfect S i hP hPperf
  intro X hX
  have hmem : X ∈ C := by simpa only [C, mem_fixSubgroup, stdUnitaryEquiv_apply] using hX
  exact hle ⟨⟨X, hmem⟩, rfl⟩


theorem commute_rootSpan_of_commute_unitary_component_two
    {tau : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p0 : ℕ}
    (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (hT : rootDiagUnit tau a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (hq : S.D.q = 2) {nu : ℕ} (hnu : 4 ≤ nu)
    (psi : SL(nu, L) →* ModGL tau L) {sigmaf : Fin nu → Fin nu → Fin tau.rank → ℤ}
    (hpsi : IsSLFrame psi sigmaf) (hRoots : componentRoots (rootCharHom a) i = frameRoots sigmaf)
    (pi : Equiv.Perm (Fin nu))
    (hpi : ∀ x y, x ≠ y → (S.ρ : (Fin tau.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (sigmaf x y) = sigmaf (pi y) (pi x))
    (omega : Lˣ) (homega : omega ^ 3 = 1) (hne : omega ≠ 1)
    (actor : ModGL tau L)
    (hActor : actor ∈ torusGroup tau L ⊔ rootSpan tau L (kernelRoots (rootCharHom a)))
    (hcomm : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, Commute actor x) :
    ∀ y ∈ rootSpan tau L (componentRoots (rootCharHom a) i), Commute actor y := by
  classical
  have hqpow : S.D.q = 2 ^ 1 := by simpa using hq
  obtain ⟨sigma, z, hsigma, hzZ, hnorm, hconj⟩ :=
    exists_unitary_untwist_kd264alg S hT i (by omega) hpsi hRoots pi hpi
      Nat.prime_two (inferInstance : CharP L 2) (by decide : 0 < (1 : ℕ)) hqpow
  have hsigmaTwo : ∀ c, sigma c = c ^ 2 := by
    intro c
    simpa only [hs, mul_one, pow_one] using hsigma c
  have hconjOne : ∀ X : SL(nu, L), S.D.step (z * psi X * z⁻¹) =
      z * psi (stdUnitary sigma.toRingHom X) * z⁻¹ := by
    intro X
    have h := hconj X
    rw [hs] at h
    change S.D.step (z * psi X * z⁻¹) = z * psi (stdUnitary sigma.toRingHom X) * z⁻¹ at h
    exact h
  have hFixedMem := unitary_fixed_image_le_rationalComponent S i hs hnu psi
    (hpsi.range.trans (by rw [hRoots])) sigma hsigmaTwo z (hnorm i) hconjOne
  have hCperf : Group.IsPerfect (fixSubgroup (stdUnitaryEquiv (ν := nu) sigma)) := by
    have hNot : (nu, 2 ^ 1) ≠ (3, 2) := by
      intro h
      have he := congrArg Prod.fst h
      omega
    exact ((stdUnitary_fixSubgroup Nat.prime_two (f := 1) (by decide) sigma
      (fun c => by simpa using hsigmaTwo c) (by omega)).2.1 hNot).1
  have hbar : Units.map sigma.toRingHom.toMonoidHom omega = omega⁻¹ := by
    apply Units.ext
    rw [Units.coe_map, Units.val_inv_eq_inv_val]
    change sigma (omega : L) = (omega : L)⁻¹
    rw [hsigmaTwo]
    have hCube : (omega : L) ^ 3 = 1 := congrArg (fun u : Lˣ => (u : L)) homega
    apply mul_right_cancel₀ omega.ne_zero
    calc (omega : L) ^ 2 * (omega : L) = 1 := by simpa only [pow_succ] using hCube
      _ = (omega : L)⁻¹ * (omega : L) := (inv_mul_cancel₀ omega.ne_zero).symm
  have hZM : z⁻¹ * actor * z ∈ torusGroup tau L ⊔ rootSpan tau L (kernelRoots (rootCharHom a)) :=
    mul_mem (mul_mem (inv_mem hzZ) hActor) hzZ
  obtain ⟨M, hM⟩ := exists_conj_frame_of_mem_kd264alg i (by omega) hpsi hRoots hZM
  have hfix : ∀ X : SL(nu, L), stdUnitary sigma.toRingHom X = X → psi (conjSLn M X) = psi X := by
    intro X hX
    have hx := (hcomm _ (hFixedMem X hX)).eq
    have hc : actor * (z * psi X * z⁻¹) * actor⁻¹ = z * psi X * z⁻¹ := by
      rw [hx, mul_inv_cancel_right]
    have h := hM X
    change (z⁻¹ * actor * z) * psi X * (z⁻¹ * actor * z)⁻¹ = psi (conjSLn M X) at h
    rw [← h]
    calc (z⁻¹ * actor * z) * psi X * (z⁻¹ * actor * z)⁻¹ =
        z⁻¹ * (actor * (z * psi X * z⁻¹) * actor⁻¹) * z := by group
      _ = psi X := by rw [hc]; group
  have hker := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.frame_ker_le_center
    (by omega) hpsi
  have htriv := conjSLn_eq_self_of_commute_stdUnitary (by omega) sigma omega hne hbar
    psi hker hCperf M hfix
  intro y hy
  have hy' : z⁻¹ * y * z ∈ rootSpan tau L (componentRoots (rootCharHom a) i) := by
    have h := (hnorm i (z⁻¹ * y * z)).mpr
    apply h
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hy
  rw [hRoots, ← hpsi.range] at hy'
  obtain ⟨X, hX⟩ := hy'
  have hyX : y = z * psi X * z⁻¹ := by rw [hX]; group
  have hGeo : (z⁻¹ * actor * z) * psi X * (z⁻¹ * actor * z)⁻¹ = psi X := by
    rw [hM, htriv]
  have hActorFix : actor * y * actor⁻¹ = y := by
    rw [hyX]
    calc actor * (z * psi X * z⁻¹) * actor⁻¹ = z *
        ((z⁻¹ * actor * z) * psi X * (z⁻¹ * actor * z)⁻¹) * z⁻¹ := by group
      _ = z * psi X * z⁻¹ := by rw [hGeo]
  exact mul_inv_eq_iff_eq_mul.mp hActorFix


end CFSG.HardMathSupport.Timmesfeld.LangTorus
