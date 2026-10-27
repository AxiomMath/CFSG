module

public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.ClassicalGroups.UnitaryFlag.LineSU2
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.LieType.BorelTits
open scoped Matrix

theorem exists_isPrimitiveRoot_two_pow_sub_one {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ ζ : K, IsPrimitiveRoot ζ (2 ^ n - 1) := by
  classical
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  have hsq : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ n) 1
  have hdvd : 2 ^ n + 1 ∣ orderOf g := by
    rw [hord, hsq]
    exact dvd_mul_right _ _
  have hord' : orderOf (g ^ (2 ^ n + 1)) = 2 ^ n - 1 := by
    rw [orderOf_pow_of_dvd (by omega) hdvd, hord, hsq,
      Nat.mul_div_cancel_left _ (by omega)]
  exact ⟨((g ^ (2 ^ n + 1) : Kˣ) : K),
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hord')⟩

noncomputable abbrev eigenSubmodule {K : Type} [Field K] (m : ℕ) (A : GL (Fin 3) K) (ζ : K)
    (i : Fin m) : Submodule K (Fin 3 → K) :=
  Module.End.eigenspace (Matrix.mulVecLin ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (ζ ^ (i : ℤ))

theorem exists_isInternal_eigenspaces {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) {A : GL (Fin 3) K}
    (hA : A ^ (2 ^ n - 1) = 1) :
    ∃ ζ : K, IsPrimitiveRoot ζ (2 ^ n - 1) ∧
      DirectSum.IsInternal (fun i : Fin (2 ^ n - 1) =>
        Module.End.eigenspace (Matrix.mulVecLin ((A : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) (ζ ^ (i : ℤ))) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_two_pow_sub_one hK
  have hm2 : 2 ≤ 2 ^ n - 1 := by
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  let g : (Fin 3 → K) ≃ₗ[K] (Fin 3 → K) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 3 → K)
      (Matrix.GeneralLinearGroup.toLin A)
  have hgpow : g ^ (2 ^ n - 1) = 1 := by
    dsimp [g]
    rw [← map_pow, ← map_pow, hA, map_one, map_one]
  have hdir := CFSG.proposition_2_4_a (F := K) (V := Fin 3 → K) (g := g)
    hgpow hm2 hζ
  exact ⟨ζ, hζ, by simpa [g, Matrix.GeneralLinearGroup.coe_toLin] using hdir⟩

theorem bar_eq_self_of_pow_two_pow_sub_one_eq_one {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {c : K} (hc : c ^ (2 ^ n - 1) = 1) : h.bar c = c := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  calc h.bar c = c ^ 2 ^ n := h.bar_apply c
    _ = c ^ (2 ^ n - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel hq]
    _ = c := by rw [hc, one_mul]

theorem bar_eq_self_of_isPrimitiveRoot_pow {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1))
    (i : Fin (2 ^ n - 1)) : h.bar (ζ ^ (i : ℤ)) = ζ ^ (i : ℤ) := by
  rw [show ζ ^ (i : ℤ) = ζ ^ (i : ℕ) by rw [zpow_natCast]]
  apply bar_eq_self_of_pow_two_pow_sub_one_eq_one h
  rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

theorem mul_self_eq_one_iff_eq_one {K : Type} [Field K] [CharP K 2] {μ : K} :
    μ * μ = 1 ↔ μ = 1 := by
  constructor
  · intro h
    rcases mul_self_eq_one_iff.mp h with h1 | h1
    · exact h1
    · rw [h1, CharTwo.neg_eq]
  · rintro rfl
    simp

def powInvIndex {m : ℕ} [NeZero m] (i : Fin m) : Fin m :=
  if h : i = 0 then 0 else ⟨m - i.val, by
    have hi : 0 < i.val := Nat.pos_of_ne_zero fun h0 => h (Fin.ext (by simpa using h0))
    omega⟩

theorem zpow_powInvIndex {K : Type} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (i : Fin m) :
    ζ ^ (powInvIndex i : ℤ) = (ζ ^ (i : ℤ))⁻¹ := by
  by_cases hi : i = 0
  · subst hi
    simp [powInvIndex]
  · have hile : i.val ≤ m := le_of_lt i.isLt
    rw [zpow_natCast, zpow_natCast, powInvIndex, dif_neg hi]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, Nat.sub_add_cancel hile, hζ.pow_eq_one]

theorem eq_of_zpow_eq {K : Type} [Field K] {m : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    {i j : Fin m} (h : ζ ^ (i : ℤ) = ζ ^ (j : ℤ)) : i = j := by
  have h' : ζ ^ (i : ℕ) = ζ ^ (j : ℕ) := by simpa only [zpow_natCast] using h
  exact Fin.ext (hζ.pow_inj i.isLt j.isLt h')

theorem powInvIndex_eq_zero_iff {K : Type} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (i : Fin m) : powInvIndex i = 0 ↔ i = 0 := by
  constructor
  · intro h
    have hz := zpow_powInvIndex hζ i
    rw [h] at hz
    have h1 : ζ ^ (i : ℤ) = 1 := by simpa using hz.symm
    exact eq_of_zpow_eq hζ (by simpa using h1)
  · rintro rfl
    simp [powInvIndex]

theorem powInvIndex_ne_zero {K : Type} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) {i : Fin m} (hi : i ≠ 0) : powInvIndex i ≠ 0 :=
  fun h => hi ((powInvIndex_eq_zero_iff hζ i).mp h)

theorem powInvIndex_ne_self {K : Type} [Field K] {m : ℕ} [NeZero m] {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) [CharP K 2] {i : Fin m} (hi : i ≠ 0) :
    powInvIndex i ≠ i := by
  intro h
  apply hi
  have hz := zpow_powInvIndex hζ i
  rw [h] at hz
  have h2 : ζ ^ (i : ℤ) * ζ ^ (i : ℤ) = 1 := by
    nth_rewrite 1 [hz]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (hζ.ne_zero NeZero.out))
  have h1 : ζ ^ (i : ℤ) = 1 := mul_self_eq_one_iff_eq_one.mp h2
  exact eq_of_zpow_eq hζ (by simpa using h1)

theorem stdHermForm_eq_zero_of_eigen {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {B : GL (Fin 3) K} (hB : B ∈ unitarySU 2 n K 3)
    {μ ν : K} (hμ : h.bar μ = μ) (hμν : μ * ν ≠ 1) {x y : Fin 3 → K}
    (hx : B *ᵥ x = μ • x) (hy : B *ᵥ y = ν • y) :
    stdHermForm h 3 x y = 0 := by
  have hiso := stdHermForm_smul_smul h ⟨B, hB⟩ x y
  rw [unitarySU_smul_def h, unitarySU_smul_def h, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply, hx, hy] at hiso
  simp only [map_smulₛₗ, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul, hμ] at hiso
  have h0 : (μ * ν - 1) * stdHermForm h 3 x y = 0 := by linear_combination hiso
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμν)

theorem eigenspace_stdHermForm_eq_zero {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {μ : K} (hμ : h.bar μ = μ) (hμ2 : μ * μ ≠ 1) :
    ∀ y ∈ Module.End.eigenspace (Matrix.mulVecLin A) μ,
      ∀ w ∈ Module.End.eigenspace (Matrix.mulVecLin A) μ, stdHermForm h 3 y w = 0 := by
  intro y hy w hw
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hy hw
  exact stdHermForm_eq_zero_of_eigen h hA hμ hμ2 hy hw

theorem finrank_le_one_of_stdHermForm_eq_zero {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {W : Submodule K (Fin 3 → K)}
    (hiso : ∀ y ∈ W, ∀ w ∈ W, stdHermForm h 3 y w = 0) :
    Module.finrank K W ≤ 1 := by
  classical
  haveI := h.charP
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, Nat.mul_comm 2 n]
  by_contra hle
  have h2 : 2 ≤ Module.finrank K W := by omega
  obtain ⟨u, hu⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := W) h2
  let uV : Fin 2 → (Fin 3 → K) := fun i => (u i : Fin 3 → K)
  have huV : LinearIndependent K uV :=
    hu.map' (Submodule.subtype W) (Submodule.ker_subtype W)
  let U : Submodule K (Fin 3 → K) := Submodule.span K (Set.range uV)
  have hU2 : Module.finrank K U = 2 := by
    rw [finrank_span_eq_card huV]
    simp
  have hUle : U ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (u i).2
  let F : ReflForm K (Fin 3 → K) := unitaryForm 2 n hK 3
  have hβ : ∀ y w, F.β y w = stdHermForm h 3 y w := by
    intro y w
    rw [show F.β y w = ∑ i, unitaryInvolution K 2 n (y i) * w i from
      unitaryForm_β hK y w, stdHermForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [unitaryInvolution_apply, h.bar_apply]
  have hUiso : F.IsTotallyIsotropic U := by
    intro y hy
    rw [ReflForm.mem_perp]
    intro w hw
    rw [hβ w y]
    exact hiso w (hUle hw) y (hUle hy)
  have hperp := F.finrank_perp U
  rw [hU2, Module.finrank_fin_fun] at hperp
  have hmono : Module.finrank K U ≤ Module.finrank K (F.perp U) :=
    Submodule.finrank_mono hUiso
  omega

theorem stdHermForm_eq_zero_of_eigenSubmodule {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    {i k : Fin (2 ^ n - 1)} (hik : k ≠ powInvIndex i) :
    ∀ y ∈ eigenSubmodule (2 ^ n - 1) A ζ i,
      ∀ z ∈ eigenSubmodule (2 ^ n - 1) A ζ k, stdHermForm h 3 y z = 0 := by
  intro y hy z hz
  have hμ : h.bar (ζ ^ (i : ℤ)) = ζ ^ (i : ℤ) := bar_eq_self_of_isPrimitiveRoot_pow h hζ i
  have hν : ζ ^ (k : ℤ) ≠ (ζ ^ (i : ℤ))⁻¹ := by
    intro hk
    apply hik
    apply eq_of_zpow_eq hζ
    rw [hk, zpow_powInvIndex hζ i]
  have hμν : ζ ^ (i : ℤ) * ζ ^ (k : ℤ) ≠ 1 := fun hprod =>
    hν (eq_inv_of_mul_eq_one_right hprod)
  have hy' : A *ᵥ y = (ζ ^ (i : ℤ)) • y := by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hy
    exact hy
  have hz' : A *ᵥ z = (ζ ^ (k : ℤ)) • z := by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hz
    exact hz
  exact stdHermForm_eq_zero_of_eigen h hA hμ hμν hy' hz'

theorem eq_bot_of_eigenSubmodule_powInvIndex_eq_bot {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    (hdir : DirectSum.IsInternal (eigenSubmodule (2 ^ n - 1) A ζ))
    {i : Fin (2 ^ n - 1)} (hi : i ≠ 0)
    (hbot : eigenSubmodule (2 ^ n - 1) A ζ (powInvIndex i) = ⊥) :
    eigenSubmodule (2 ^ n - 1) A ζ i = ⊥ := by
  classical
  haveI := h.charP
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hμ := bar_eq_self_of_isPrimitiveRoot_pow h hζ i
  have hμ2 : ζ ^ (i : ℤ) * ζ ^ (i : ℤ) ≠ 1 := by
    intro h2
    have h1 : ζ ^ (i : ℤ) = 1 := mul_self_eq_one_iff_eq_one.mp h2
    exact hi (eq_of_zpow_eq hζ (by simpa using h1))
  have hforall : ∀ w, stdHermForm h 3 y w = 0 := by
    intro w
    have hw : w ∈ ⨆ k, eigenSubmodule (2 ^ n - 1) A ζ k := by
      rw [hdir.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (p := eigenSubmodule (2 ^ n - 1) A ζ)
      (motive := fun x => stdHermForm h 3 y x = 0) hw ?_ ?_ ?_
    · intro k z hz
      by_cases hki : k = i
      · subst hki
        exact eigenspace_stdHermForm_eq_zero h hA hμ hμ2 y hy z hz
      · by_cases hkj : k = powInvIndex i
        · subst hkj
          rw [hbot] at hz
          have hz0 : z = 0 := by simpa using hz
          rw [hz0]
          simp
        · exact stdHermForm_eq_zero_of_eigenSubmodule h hA hζ hkj y hy z hz
    · simp
    · intro x z hx hz
      rw [map_add, hx, hz, add_zero]
  exact stdHermForm_separatingLeft h 3 y hforall

theorem eigenSubmodule_powInvIndex_ne_bot {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    (hdir : DirectSum.IsInternal (eigenSubmodule (2 ^ n - 1) A ζ))
    {i : Fin (2 ^ n - 1)} (hEi : eigenSubmodule (2 ^ n - 1) A ζ i ≠ ⊥) :
    eigenSubmodule (2 ^ n - 1) A ζ (powInvIndex i) ≠ ⊥ := by
  intro hbot
  by_cases hi : i = 0
  · subst hi
    exact hEi (by simpa [powInvIndex] using hbot)
  · exact hEi (eq_bot_of_eigenSubmodule_powInvIndex_eq_bot h hA hζ hdir hi hbot)

theorem exists_eigenSubmodule_ne_bot_of_ne_one {K : Type} [Field K] {n : ℕ}
    {A : GL (Fin 3) K} {ζ : K} [NeZero (2 ^ n - 1)]
    (hdir : DirectSum.IsInternal (eigenSubmodule (2 ^ n - 1) A ζ)) (hAne : A ≠ 1) :
    ∃ i : Fin (2 ^ n - 1), i ≠ 0 ∧
      eigenSubmodule (2 ^ n - 1) A ζ i ≠ ⊥ := by
  classical
  by_contra h
  push Not at h
  have hbot : ∀ i : Fin (2 ^ n - 1), i ≠ 0 → eigenSubmodule (2 ^ n - 1) A ζ i = ⊥ :=
    fun i hi => h i hi
  have hE0top : eigenSubmodule (2 ^ n - 1) A ζ 0 = ⊤ := by
    have hsum :=
      CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension.sum_finrank_eq hdir
    have hsum0 : ∑ k, Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ k) =
        Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ 0) := by
      refine Finset.sum_eq_single 0 ?_ ?_
      · intro k _ hk
        rw [hbot k hk, finrank_bot]
      · intro hnot
        exact absurd (Finset.mem_univ 0) hnot
    have h3 : Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ 0) = 3 := by
      rw [← hsum0, hsum, Module.finrank_fin_fun]
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [h3, Module.finrank_fin_fun]
  have hfix : ∀ v : Fin 3 → K, A *ᵥ v = v := by
    intro v
    have hv : v ∈ eigenSubmodule (2 ^ n - 1) A ζ 0 := by rw [hE0top]; trivial
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
    simpa using hv
  have hA1 : A = 1 := by
    ext r c
    have h := congrArg (fun v : Fin 3 → K => v r) (hfix (Pi.single c 1))
    simpa [Matrix.one_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using h
  exact hAne hA1

theorem finrank_eigenSubmodule_eq_one {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    {i : Fin (2 ^ n - 1)} (hi : i ≠ 0)
    (hEi : eigenSubmodule (2 ^ n - 1) A ζ i ≠ ⊥) :
    Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ i) = 1 := by
  haveI := h.charP
  have hμ := bar_eq_self_of_isPrimitiveRoot_pow h hζ i
  have hμ1 : ζ ^ (i : ℤ) ≠ 1 := by
    intro h1
    exact hi (eq_of_zpow_eq hζ (by simpa using h1))
  have hμ2 : ζ ^ (i : ℤ) * ζ ^ (i : ℤ) ≠ 1 := fun h2 =>
    hμ1 (mul_self_eq_one_iff_eq_one.mp h2)
  have hle : Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ i) ≤ 1 :=
    finrank_le_one_of_stdHermForm_eq_zero h (eigenspace_stdHermForm_eq_zero h hA hμ hμ2)
  have hge : 1 ≤ Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ i) := by
    rw [Submodule.one_le_finrank_iff]
    exact hEi
  omega

theorem finrank_eigenSubmodule_zero_eq_one {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    (hdir : DirectSum.IsInternal (eigenSubmodule (2 ^ n - 1) A ζ)) (hAne : A ≠ 1) :
    Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ 0) = 1 := by
  classical
  haveI := h.charP
  let E : Fin (2 ^ n - 1) → Submodule K (Fin 3 → K) := eigenSubmodule (2 ^ n - 1) A ζ
  let f : Fin (2 ^ n - 1) → ℕ := fun k => Module.finrank K (E k)
  have hsum : ∑ k, f k = 3 := by
    have h := CFSG.LinearAlgebra.CoprimeActions.DistinctEigenspaceCommutantDimension.sum_finrank_eq
      hdir
    simpa [f, E, Module.finrank_fin_fun] using h
  obtain ⟨i, hi, hEi⟩ := exists_eigenSubmodule_ne_bot_of_ne_one hdir hAne
  have hEi' : E i ≠ ⊥ := by simpa [E] using hEi
  set j : Fin (2 ^ n - 1) := powInvIndex i with hjdef
  have hz : ζ ^ (j : ℤ) = (ζ ^ (i : ℤ))⁻¹ := by
    simpa [j] using zpow_powInvIndex hζ i
  have hEj : E j ≠ ⊥ := by
    simpa [E, j] using eigenSubmodule_powInvIndex_ne_bot h hA hζ hdir hEi
  have hj : j ≠ 0 := by
    intro hj0
    have h1 : ζ ^ (i : ℤ) = 1 := by
      have h2 := hz
      rw [hj0] at h2
      simpa using h2.symm
    exact hi (eq_of_zpow_eq hζ (by simpa using h1))
  have hij : i ≠ j := by
    intro h
    apply hi
    have h2 : ζ ^ (i : ℤ) * ζ ^ (i : ℤ) = 1 := by
      have h3 := hz
      rw [← h] at h3
      nth_rewrite 1 [h3]
      exact inv_mul_cancel₀ (zpow_ne_zero _ (hζ.ne_zero NeZero.out))
    have h1 : ζ ^ (i : ℤ) = 1 := mul_self_eq_one_iff_eq_one.mp h2
    exact eq_of_zpow_eq hζ (by simpa using h1)
  have hfi : f i = 1 := by
    simpa [f, E] using finrank_eigenSubmodule_eq_one h hA hζ hi hEi
  have hfj : f j = 1 := by
    simpa [f, E] using finrank_eigenSubmodule_eq_one h hA hζ hj hEj
  let R : Finset (Fin (2 ^ n - 1)) := (Finset.univ.erase i).erase j
  have hRsum : R.sum f = 1 := by
    have h1 : (Finset.univ.erase i).sum f + f i = Finset.univ.sum f :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have h2 : R.sum f + f j = (Finset.univ.erase i).sum f := by
      simpa [R] using Finset.sum_erase_add (Finset.univ.erase i) f
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
    have h3 : R.sum f + f j + f i = 3 := by
      rw [h2, h1, hsum]
    rw [hfi, hfj] at h3
    omega
  have h0R : (0 : Fin (2 ^ n - 1)) ∈ R := by
    simp only [R, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hj.symm, hi.symm⟩
  have hE0ne : E 0 ≠ ⊥ := by
    intro hE0
    have hf0 : f 0 = 0 := by simp [f, hE0]
    have hRne : R.sum f ≠ 0 := by rw [hRsum]; norm_num
    obtain ⟨k, hkR, hfk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hRne
    have hkE : E k ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hfk
      exact hfk rfl
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hfk
      rw [hk0]
      simpa [f] using hf0
    let l : Fin (2 ^ n - 1) := powInvIndex k
    have hlE : E l ≠ ⊥ := by
      simpa [l, E] using eigenSubmodule_powInvIndex_ne_bot h hA hζ hdir hkE
    have hlk : l ≠ k := by
      intro h
      apply hk0
      have h2 : ζ ^ (k : ℤ) * ζ ^ (k : ℤ) = 1 := by
        have h3 : ζ ^ (l : ℤ) = (ζ ^ (k : ℤ))⁻¹ := by
          simpa [l] using zpow_powInvIndex hζ k
        rw [h] at h3
        nth_rewrite 1 [h3]
        exact inv_mul_cancel₀ (zpow_ne_zero _ (hζ.ne_zero NeZero.out))
      have h1 : ζ ^ (k : ℤ) = 1 := mul_self_eq_one_iff_eq_one.mp h2
      exact eq_of_zpow_eq hζ (by simpa using h1)
    have hli : l ≠ i := by
      intro h
      have hkR' := Finset.mem_erase.mp hkR
      apply hkR'.1
      apply eq_of_zpow_eq hζ
      have h3 : ζ ^ (l : ℤ) = (ζ ^ (k : ℤ))⁻¹ := by
        simpa [l] using zpow_powInvIndex hζ k
      rw [h] at h3
      rw [hz]
      rw [h3, inv_inv]
    have hlj : l ≠ j := by
      intro h
      have hkR' := Finset.mem_erase.mp hkR
      have hkR'' := Finset.mem_erase.mp hkR'.2
      apply hkR''.1
      apply eq_of_zpow_eq hζ
      have h3 : ζ ^ (l : ℤ) = (ζ ^ (k : ℤ))⁻¹ := by
        simpa [l] using zpow_powInvIndex hζ k
      rw [h] at h3
      have h4 : (ζ ^ (j : ℤ))⁻¹ = ζ ^ (i : ℤ) := by rw [hz, inv_inv]
      rw [show ζ ^ (k : ℤ) = (ζ ^ (j : ℤ))⁻¹ by rw [h3, inv_inv], h4]
    have hlR : l ∈ R := by
      simp only [R, Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨hlj, hli⟩
    have hsub : ({k, l} : Finset (Fin (2 ^ n - 1))) ⊆ R := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hkR
      · exact hlR
    have hkl : k ≠ l := fun h => hlk h.symm
    have hpair : ({k, l} : Finset (Fin (2 ^ n - 1))).sum f = f k + f l := by
      rw [Finset.sum_insert (by simp [hkl]), Finset.sum_singleton]
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.zero_le (f x))
    rw [hpair, hRsum] at hle
    have hfk1 : 1 ≤ f k := by rw [Submodule.one_le_finrank_iff]; exact hkE
    have hfl1 : 1 ≤ f l := by rw [Submodule.one_le_finrank_iff]; exact hlE
    omega
  have h0le : f 0 ≤ 1 := by
    have hsub : ({0} : Finset (Fin (2 ^ n - 1))) ⊆ R := by
      intro x hx
      rw [Finset.mem_singleton] at hx
      simpa [hx] using h0R
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => Nat.zero_le (f x))
    simpa [hRsum] using hle
  have h0ge : 1 ≤ f 0 := by
    rw [Submodule.one_le_finrank_iff]
    exact hE0ne
  have hf0 : f 0 = 1 := by omega
  simpa [f, E] using hf0

theorem exists_stdHermForm_ne_zero_of_eigenSubmodule {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    (hdir : DirectSum.IsInternal (eigenSubmodule (2 ^ n - 1) A ζ))
    {i : Fin (2 ^ n - 1)} (hi : i ≠ 0) {y : Fin 3 → K}
    (hy : y ∈ eigenSubmodule (2 ^ n - 1) A ζ i) (hy0 : y ≠ 0) :
    ∃ z ∈ eigenSubmodule (2 ^ n - 1) A ζ (powInvIndex i), stdHermForm h 3 y z ≠ 0 := by
  classical
  haveI := h.charP
  by_contra hzero
  push Not at hzero
  have hμ := bar_eq_self_of_isPrimitiveRoot_pow h hζ i
  have hμ1 : ζ ^ (i : ℤ) ≠ 1 := by
    intro h1
    exact hi (eq_of_zpow_eq hζ (by simpa using h1))
  have hμ2 : ζ ^ (i : ℤ) * ζ ^ (i : ℤ) ≠ 1 := fun h2 =>
    hμ1 (mul_self_eq_one_iff_eq_one.mp h2)
  have hforall : ∀ w, stdHermForm h 3 y w = 0 := by
    intro w
    have hw : w ∈ ⨆ k, eigenSubmodule (2 ^ n - 1) A ζ k := by
      rw [hdir.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (p := eigenSubmodule (2 ^ n - 1) A ζ)
      (motive := fun x => stdHermForm h 3 y x = 0) hw ?_ ?_ ?_
    · intro k z hz
      by_cases hki : k = i
      · subst hki
        exact eigenspace_stdHermForm_eq_zero h hA hμ hμ2 y hy z hz
      · by_cases hkp : k = powInvIndex i
        · subst hkp
          exact hzero z hz
        · exact stdHermForm_eq_zero_of_eigenSubmodule h hA hζ hkp y hy z hz
    · simp
    · intro x z hx hz
      rw [map_add, hx, hz, add_zero]
  exact hy0 (stdHermForm_separatingLeft h 3 y hforall)

theorem stdHermForm_self_ne_zero_of_eigenSubmodule_zero {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {A : GL (Fin 3) K} (hA : A ∈ unitarySU 2 n K 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (2 ^ n - 1)) [NeZero (2 ^ n - 1)]
    (hdir : DirectSum.IsInternal (eigenSubmodule (2 ^ n - 1) A ζ))
    (hE0 : Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ 0) = 1)
    {v : Fin 3 → K} (hv : v ∈ eigenSubmodule (2 ^ n - 1) A ζ 0) (hv0 : v ≠ 0) :
    stdHermForm h 3 v v ≠ 0 := by
  classical
  haveI := h.charP
  intro hvv
  have hspan : eigenSubmodule (2 ^ n - 1) A ζ 0 = Submodule.span K {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hE0 hv hv0
  have hforall : ∀ w, stdHermForm h 3 v w = 0 := by
    intro w
    have hw : w ∈ ⨆ k, eigenSubmodule (2 ^ n - 1) A ζ k := by
      rw [hdir.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (p := eigenSubmodule (2 ^ n - 1) A ζ)
      (motive := fun x => stdHermForm h 3 v x = 0) hw ?_ ?_ ?_
    · intro k z hz
      by_cases hk0 : k = 0
      · subst hk0
        rw [hspan, Submodule.mem_span_singleton] at hz
        obtain ⟨c, rfl⟩ := hz
        rw [map_smul, hvv, smul_eq_mul, mul_zero]
      · have hk : k ≠ powInvIndex (0 : Fin (2 ^ n - 1)) := by
          simpa [powInvIndex] using hk0
        exact stdHermForm_eq_zero_of_eigenSubmodule h hA hζ hk v hv z hz
    · simp
    · intro x z hx hz
      rw [map_add, hx, hz, add_zero]
  exact hv0 (stdHermForm_separatingLeft h 3 v hforall)

theorem exists_hyperbolic_eigenbasis_of_pow_eq_one {K : Type} [Field K] {n : ℕ}
    (h : UnitaryFieldData 2 n K) {a : StatedSU 3 (2 ^ n) K} (ha : a ≠ 1)
    (hpow : a ^ (2 ^ n - 1) = 1) :
    ∃ (v e f : Fin 3 → K) (t : K), t ≠ 1 ∧
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v ∧
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec e = t • e ∧
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec f = t⁻¹ • f ∧
      stdHermForm h 3 v v ≠ 0 ∧ stdHermForm h 3 e e = 0 ∧ stdHermForm h 3 f f = 0 ∧
      stdHermForm h 3 e f = 1 ∧ stdHermForm h 3 e v = 0 ∧ stdHermForm h 3 f v = 0 ∧
      ∀ w : Fin 3 → K, ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w →
        ∃ c : K, w = c • v := by
  classical
  haveI := h.finite
  haveI := h.charP
  have hnpos : 1 ≤ n := h.one_le
  rcases Nat.lt_or_ge n 2 with hn1 | hn
  · have hn1' : n = 1 := by omega
    subst hn1'
    have ha1 : a = 1 := by simpa using hpow
    exact absurd ha1 ha
  · have hK : Nat.card K = (2 ^ n) ^ 2 := by
      rw [h.card, ← pow_mul, Nat.mul_comm 2 n]
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    haveI : NeZero (2 ^ n - 1) := ⟨by omega⟩
    let A : GL (Fin 3) K := (a : GL (Fin 3) K)
    have hA : A ^ (2 ^ n - 1) = 1 := by
      simpa [A] using congrArg (fun x : StatedSU 3 (2 ^ n) K => (x : GL (Fin 3) K)) hpow
    obtain ⟨ζ, hζ, hdir⟩ := exists_isInternal_eigenspaces hK hn hA
    have hAU : A ∈ unitarySU 2 n K 3 := a.2
    have hAne : A ≠ 1 := by
      intro hA1
      exact ha (Subtype.ext hA1)
    obtain ⟨i, hi, hEi⟩ := exists_eigenSubmodule_ne_bot_of_ne_one hdir hAne
    let j : Fin (2 ^ n - 1) := powInvIndex i
    have hzj : ζ ^ (j : ℤ) = (ζ ^ (i : ℤ))⁻¹ := by
      simpa [j] using zpow_powInvIndex hζ i
    have hj0 : j ≠ 0 := by simpa [j] using powInvIndex_ne_zero hζ hi
    have hij : i ≠ j := by
      intro h
      exact powInvIndex_ne_self hζ hi (by simpa [j] using h.symm)
    have hf0 : Module.finrank K (eigenSubmodule (2 ^ n - 1) A ζ 0) = 1 :=
      finrank_eigenSubmodule_zero_eq_one h hAU hζ hdir hAne
    have hE0 : eigenSubmodule (2 ^ n - 1) A ζ 0 ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hf0
      exact Nat.zero_ne_one hf0
    obtain ⟨e, heE, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hEi
    obtain ⟨v, hvE, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE0
    obtain ⟨z, hzE, hzf⟩ := exists_stdHermForm_ne_zero_of_eigenSubmodule h hAU hζ hdir
      hi heE he0
    have hzEj : z ∈ eigenSubmodule (2 ^ n - 1) A ζ j := by simpa [j] using hzE
    let f : Fin 3 → K := (stdHermForm h 3 e z)⁻¹ • z
    have hfE : f ∈ eigenSubmodule (2 ^ n - 1) A ζ j :=
      Submodule.smul_mem _ _ hzEj
    have hbar_i : h.bar (ζ ^ (i : ℤ)) = ζ ^ (i : ℤ) :=
      bar_eq_self_of_isPrimitiveRoot_pow h hζ i
    have hi1 : ζ ^ (i : ℤ) ≠ 1 := by
      intro h1
      exact hi (eq_of_zpow_eq hζ (by simpa using h1))
    have hi2 : ζ ^ (i : ℤ) * ζ ^ (i : ℤ) ≠ 1 := fun h2 =>
      hi1 (mul_self_eq_one_iff_eq_one.mp h2)
    have hbar_j : h.bar (ζ ^ (j : ℤ)) = ζ ^ (j : ℤ) :=
      bar_eq_self_of_isPrimitiveRoot_pow h hζ j
    have hj1 : ζ ^ (j : ℤ) ≠ 1 := by
      intro h1
      exact hj0 (eq_of_zpow_eq hζ (by simpa using h1))
    have hj2 : ζ ^ (j : ℤ) * ζ ^ (j : ℤ) ≠ 1 := fun h2 =>
      hj1 (mul_self_eq_one_iff_eq_one.mp h2)
    have hee : stdHermForm h 3 e e = 0 :=
      eigenspace_stdHermForm_eq_zero h hAU hbar_i hi2 e heE e heE
    have hzz : stdHermForm h 3 z z = 0 :=
      eigenspace_stdHermForm_eq_zero h hAU hbar_j hj2 z hzEj z hzEj
    have hff : stdHermForm h 3 f f = 0 := by
      simp [f, hzz]
    have hef : stdHermForm h 3 e f = 1 := by
      simp only [f, map_smul, smul_eq_mul]
      exact inv_mul_cancel₀ hzf
    have hev : stdHermForm h 3 e v = 0 :=
      stdHermForm_eq_zero_of_eigenSubmodule h hAU hζ
        (by simpa [j] using (Ne.symm hj0)) e heE v hvE
    have hfv : stdHermForm h 3 f v = 0 :=
      stdHermForm_eq_zero_of_eigenSubmodule h hAU hζ
        (Ne.symm (powInvIndex_ne_zero hζ hj0)) f hfE v hvE
    have hvv : stdHermForm h 3 v v ≠ 0 :=
      stdHermForm_self_ne_zero_of_eigenSubmodule_zero h hAU hζ hdir hf0 hvE hv0
    have hAv : A *ᵥ v = v := by
      have hv := hvE
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
      simpa using hv
    have hAe : A *ᵥ e = (ζ ^ (i : ℤ)) • e := by
      have he := heE
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at he
      exact he
    have hAz : A *ᵥ z = (ζ ^ (j : ℤ)) • z := by
      have hz := hzEj
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hz
      exact hz
    have hAf : A *ᵥ f = (ζ ^ (i : ℤ))⁻¹ • f := by
      have hc : f = (stdHermForm h 3 e z)⁻¹ • z := rfl
      rw [hc, Matrix.mulVec_smul, hAz, smul_smul, smul_smul, hzj, mul_comm]
    refine ⟨v, e, f, ζ ^ (i : ℤ), hi1, hAv, hAe, hAf, hvv, hee, hff, hef, hev, hfv, ?_⟩
    intro w hw
    have hwE : w ∈ eigenSubmodule (2 ^ n - 1) A ζ 0 := by
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      simpa using hw
    have hspan : eigenSubmodule (2 ^ n - 1) A ζ 0 = Submodule.span K {v} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hf0 hvE hv0
    rw [hspan, Submodule.mem_span_singleton] at hwE
    obtain ⟨c, hc⟩ := hwE
    exact ⟨c, hc.symm⟩

end CFSG.ClassicalGroups.UnitaryFlag

end
