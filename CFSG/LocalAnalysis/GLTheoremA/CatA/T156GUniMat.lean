module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearMat
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryMat
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Uni

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.StandardType
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective det_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.RankThree.Classical2 (permGL_mul_diagHom_mul_inv det_permGL)
open scoped Matrix

variable {d : ℕ}

section Adjoint

variable {K : Type} [Field K]

@[expose] def uAdj (j : ℕ) (M : Matrix (Fin d) (Fin d) K) : Matrix (Fin d) (Fin d) K :=
  (M.map (· ^ 2 ^ j))ᵀ

theorem uAdj_def (j : ℕ) (M : Matrix (Fin d) (Fin d) K) : uAdj j M = (M.map (· ^ 2 ^ j))ᵀ :=
  rfl

theorem uAdj_one (j : ℕ) : uAdj j (1 : Matrix (Fin d) (Fin d) K) = 1 := by
  rw [uAdj_def, Matrix.map_one (fun x : K => x ^ 2 ^ j) (by simp) (by simp), Matrix.transpose_one]

theorem uAdj_mul [CharP K 2] (j : ℕ) (M N : Matrix (Fin d) (Fin d) K) :
    uAdj j (M * N) = uAdj j N * uAdj j M := by
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have hmap : ∀ X : Matrix (Fin d) (Fin d) K,
      X.map (· ^ 2 ^ j) = X.map (iterateFrobenius K 2 j) := fun X => rfl
  rw [uAdj_def, uAdj_def, uAdj_def, hmap, hmap, hmap, Matrix.map_mul, Matrix.transpose_mul]

theorem uAdj_smul (j : ℕ) (c : K) (M : Matrix (Fin d) (Fin d) K) :
    uAdj j (c • M) = c ^ 2 ^ j • uAdj j M := by
  ext a b
  simp only [uAdj_def, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    mul_pow]

end Adjoint

section Elements

variable {k : Type} [Field k] {g : ℕ}

theorem diagHom_mem_su [Finite k] [CharP k 2] (t : Fin d → kˣ) (hprod : ∏ i, t i = 1)
    (hnorm : ∀ i, (t i : k) ^ (2 ^ g + 1) = 1) :
    diagHom d t ∈ LargeEvenSUGroup (Fin d) k (2 ^ g) := by
  rw [mem_LargeEvenSU_iff]
  refine ⟨?_, ?_⟩
  · rw [det_diagHom, ← Units.coe_prod, hprod, Units.val_one]
  · rw [coe_diagHom, Matrix.diagonal_map (f := fun x : k => x ^ 2 ^ g) (by simp),
      Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← pow_succ, hnorm i]

theorem permGL_mem_su [Finite k] [CharP k 2] (π : Equiv.Perm (Fin d)) :
    (permGL π : GL (Fin d) k) ∈ LargeEvenSUGroup (Fin d) k (2 ^ g) := by
  rw [mem_LargeEvenSU_iff]
  refine ⟨?_, ?_⟩
  · rw [det_permGL]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
    · rw [h]
      simp
    · rw [h]
      simp [CharTwo.neg_eq]
  · rw [MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply]
    have hmap : ((π⁻¹).permMatrix k).map (· ^ 2 ^ g) = (π⁻¹).permMatrix k := by
      ext a b
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs
      · exact one_pow _
      · exact zero_pow (by positivity)
    rw [hmap, Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_inv, inv_mul_cancel,
      Matrix.permMatrix_one]

theorem exists_norm_one_ne_one [Finite k] (hg : 1 ≤ g) (hk : Nat.card k = (2 ^ g) ^ 2) :
    ∃ ζ : kˣ, (ζ : k) ^ (2 ^ g + 1) = 1 ∧ ζ ≠ 1 := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := kˣ)
  have hcard : Nat.card kˣ = (2 ^ g) ^ 2 - 1 := by rw [Nat.card_units, hk]
  have hord : orderOf γ = (2 ^ g) ^ 2 - 1 := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hγ
  have hq : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  have hlt : 2 ^ g < (2 ^ g) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hsq : (2 ^ g - 1) * (2 ^ g + 1) = (2 ^ g) ^ 2 - 1 := by
    have h1 : 1 ≤ 2 ^ g := by omega
    have h2 : 1 ≤ (2 ^ g) ^ 2 := by omega
    zify [h1, h2]
    ring
  refine ⟨γ ^ (2 ^ g - 1), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← pow_mul, hsq, ← hord, pow_orderOf_eq_one, Units.val_one]
  · intro h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega

theorem exists_ne_ne (hd : 3 ≤ d) (a b : Fin d) : ∃ c : Fin d, c ≠ a ∧ c ≠ b := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {a, b} := fun x _ => by
    by_cases hx : x = a
    · rw [hx]
      exact Finset.mem_insert_self _ _
    · rw [h x hx]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_le_two (a := a) (b := b)
  omega

variable {K : Type} [Field K]

theorem map_diagHom (ι : k →+* K) (t : Fin d → kˣ) :
    Matrix.GeneralLinearGroup.map ι (diagHom d t) =
      diagHom d (fun i => Units.map ι.toMonoidHom (t i)) := by
  apply Units.ext
  change ((diagHom d t : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).map ι = _
  rw [coe_diagHom, coe_diagHom, Matrix.diagonal_map (map_zero ι)]
  rfl

theorem map_permGL (ι : k →+* K) (π : Equiv.Perm (Fin d)) :
    Matrix.GeneralLinearGroup.map ι (permGL π : GL (Fin d) k) = permGL π := by
  apply Units.ext
  change ((permGL π : GL (Fin d) k) : Matrix (Fin d) (Fin d) k).map ι = _
  rw [MonoidHom.coe_toHomUnits, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply,
    Matrix.permMatrixHom_apply]
  ext a b
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs
  · exact map_one ι
  · exact map_zero ι

theorem mem_scalars_of_commute_su [Finite k] [CharP k 2] (hg : 1 ≤ g)
    (hk : Nat.card k = (2 ^ g) ^ 2) (hd : 3 ≤ d) (ι : k →+* K) {A : GL (Fin d) K}
    (h : ∀ x ∈ LargeEvenSUGroup (Fin d) k (2 ^ g),
      Commute A (Matrix.GeneralLinearGroup.map ι x)) :
    A ∈ LargeEvenScalars (Fin d) K := by
  classical
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hg hk
  have hsingle : ∀ (u : kˣ), (u : k) ^ (2 ^ g + 1) = 1 → ∀ (b i : Fin d),
      (((Pi.mulSingle b u : Fin d → kˣ) i : kˣ) : k) ^ (2 ^ g + 1) = 1 := by
    intro u hu b i
    by_cases hb : i = b
    · subst hb
      rw [Pi.mulSingle_eq_same]
      exact hu
    · rw [Pi.mulSingle_eq_of_ne hb, Units.val_one, one_pow]
  have hζinv : ((ζ⁻¹ : kˣ) : k) ^ (2 ^ g + 1) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hζ, inv_one]
  have hnorm : ∀ (a c i : Fin d),
      ((TableBUM.swapDiag a c ζ i : kˣ) : k) ^ (2 ^ g + 1) = 1 := by
    intro a c i
    simp only [TableBUM.swapDiag, Pi.mul_apply]
    rw [Units.val_mul, mul_pow, hsingle ζ hζ a i, hsingle ζ⁻¹ hζinv c i, one_mul]
  obtain ⟨β, rfl⟩ : ∃ β : Fin d → Kˣ, A = diagHom d β := by
    refine TableBUM.exists_diagHom_of_commute
      (W := {σ | A * diagHom d σ = diagHom d σ * A}) ?_ (fun σ hσ => hσ)
    intro a b hab
    obtain ⟨c, hca, hcb⟩ := exists_ne_ne hd a b
    refine ⟨fun i => Units.map ι.toMonoidHom (TableBUM.swapDiag a c ζ i), ?_, ?_⟩
    · have hx : diagHom d (TableBUM.swapDiag a c ζ) ∈ LargeEvenSUGroup (Fin d) k (2 ^ g) :=
        diagHom_mem_su _ (TableBUM.prod_swapDiag ζ) (hnorm a c)
      have h1 := (h _ hx).eq
      rw [map_diagHom] at h1
      exact h1
    · simp only
      rw [TableBUM.swapDiag_left (Ne.symm hca), TableBUM.swapDiag_of_ne (Ne.symm hab) (Ne.symm hcb),
        map_one]
      intro heq
      apply hζ1
      apply Units.ext
      have h1 := congrArg (fun u : Kˣ => (u : K)) heq
      simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h1
      rw [Units.val_one]
      exact ι.injective (h1.trans (map_one ι).symm)
  have hconst : ∀ a b : Fin d, β a = β b := by
    intro a b
    have hP := h _ (permGL_mem_su (k := k) (g := g) (Equiv.swap a b))
    rw [map_permGL] at hP
    have h1 : (permGL (Equiv.swap a b) : GL (Fin d) K) * diagHom d β *
        (permGL (Equiv.swap a b))⁻¹ = diagHom d β := by
      rw [← hP.eq, mul_inv_cancel_right]
    rw [permGL_mul_diagHom_mul_inv] at h1
    have h2 := congrFun (diagHom_injective d h1) a
    have h3 : β b = β a := by
      simpa [Equiv.symm_swap, Equiv.swap_apply_left] using h2
    exact h3.symm
  rw [largeEvenScalars_def]
  refine ⟨β ⟨0, by omega⟩, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply]
  congr 1
  funext i
  rw [hconst i ⟨0, by omega⟩]

theorem commutator_su [Finite k] (hk : Nat.card k = (2 ^ g) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ g) ≠ (3, 2)) :
    ⁅LargeEvenSUGroup (Fin d) k (2 ^ g), LargeEvenSUGroup (Fin d) k (2 ^ g)⁆ =
      LargeEvenSUGroup (Fin d) k (2 ^ g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Group.IsPerfect ↥(LargeEvenSUGroup (Fin d) k (2 ^ g)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := g) hk hd hdq
  exact (Subgroup.isPerfect_iff (H := LargeEvenSUGroup (Fin d) k (2 ^ g))).1 hP

end Elements

section Similitudes

variable {K : Type} [Field K] [CharP K 2] {j : ℕ}

theorem conj_mem_su [Finite K] {A : GL (Fin d) K} (hA : A ∈ LargeEvenGUSet (Fin d) K (2 ^ j))
    {x : GL (Fin d) K} (hx : x ∈ LargeEvenSUGroup (Fin d) K (2 ^ j)) :
    A * x * A⁻¹ ∈ LargeEvenSUGroup (Fin d) K (2 ^ j) := by
  obtain ⟨μ, hμ0, -, hAμ⟩ := hA
  rw [mem_LargeEvenSU_iff] at hx ⊢
  obtain ⟨hdet, hu⟩ := hx
  have hAμ' : uAdj j (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K) =
      μ • (1 : Matrix (Fin d) (Fin d) K) := hAμ
  have hu' : uAdj j (x : Matrix (Fin d) (Fin d) K) * (x : Matrix (Fin d) (Fin d) K) = 1 := hu
  have hab : (A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hFb : uAdj j ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      uAdj j (A : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← uAdj_mul, hab, uAdj_one]
  have hFa : uAdj j (A : Matrix (Fin d) (Fin d) K) =
      μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    calc uAdj j (A : Matrix (Fin d) (Fin d) K)
        = uAdj j (A : Matrix (Fin d) (Fin d) K) *
            ((A : Matrix (Fin d) (Fin d) K) * ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
          rw [hab, Matrix.mul_one]
      _ = (uAdj j (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K)) *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by rw [Matrix.mul_assoc]
      _ = μ • ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          rw [hAμ', Matrix.smul_mul, Matrix.one_mul]
  have hFbb : μ • (uAdj j ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) = 1 := by
    rw [← Matrix.mul_smul, ← hFa, hFb]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, hab, Matrix.det_one]
  · change uAdj j (((A * x * A⁻¹ : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) *
      ((A * x * A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1
    rw [Units.val_mul, Units.val_mul, uAdj_mul, uAdj_mul]
    calc uAdj j ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (uAdj j (x : Matrix (Fin d) (Fin d) K) * uAdj j (A : Matrix (Fin d) (Fin d) K)) *
          ((A : Matrix (Fin d) (Fin d) K) * (x : Matrix (Fin d) (Fin d) K) *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
        = uAdj j ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            (uAdj j (x : Matrix (Fin d) (Fin d) K) *
              ((uAdj j (A : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K)) *
                (x : Matrix (Fin d) (Fin d) K))) *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
          simp only [Matrix.mul_assoc]
      _ = μ • (uAdj j ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
            (uAdj j (x : Matrix (Fin d) (Fin d) K) * (x : Matrix (Fin d) (Fin d) K)) *
            ((A⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) := by
          rw [hAμ', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_smul,
            Matrix.smul_mul]
      _ = 1 := by rw [hu', Matrix.mul_one, hFbb]

theorem mem_guSet_of_map {k : Type} [Field k] (ι : k →+* K) {q q₀ : ℕ}
    (hpow : ∀ b : k, ι (b ^ q₀) = ι b ^ q) (hK : ∀ c : K, (c ^ q) ^ q = c) (hd : 1 ≤ d)
    {A : GL (Fin d) K} (hA : A ∈ LargeEvenGUSet (Fin d) K q) {B : GL (Fin d) k} {μ : K}
    (hμ : μ ≠ 0)
    (hB : (B : Matrix (Fin d) (Fin d) k).map ι = μ • (A : Matrix (Fin d) (Fin d) K)) :
    B ∈ LargeEvenGUSet (Fin d) k q₀ := by
  obtain ⟨l, hl0, hlq, hAl⟩ := hA
  set N : Matrix (Fin d) (Fin d) k :=
    ((B : Matrix (Fin d) (Fin d) k).map (· ^ q₀))ᵀ * (B : Matrix (Fin d) (Fin d) k) with hN
  have hNmap : N.map ι = (μ ^ q * μ * l) • (1 : Matrix (Fin d) (Fin d) K) := by
    have h1 : N.map ι = (((B : Matrix (Fin d) (Fin d) k).map ι).map (· ^ q))ᵀ *
        (B : Matrix (Fin d) (Fin d) k).map ι := by
      have hc : ((B : Matrix (Fin d) (Fin d) k).map (· ^ q₀)).map ι =
          ((B : Matrix (Fin d) (Fin d) k).map ι).map (· ^ q) := by
        ext a b
        simp only [Matrix.map_apply]
        exact hpow _
      rw [hN, Matrix.map_mul, Matrix.transpose_map, hc]
    have h2 : (μ • (A : Matrix (Fin d) (Fin d) K)).map (· ^ q) =
        μ ^ q • (A : Matrix (Fin d) (Fin d) K).map (· ^ q) := by
      ext a b
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, mul_pow]
    rw [h1, hB, h2, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hAl, smul_smul,
      smul_smul, mul_assoc]
  have hentry : ∀ a b : Fin d, ι (N a b) = if a = b then μ ^ q * μ * l else 0 := by
    intro a b
    have h1 := congrFun (congrFun hNmap a) b
    rw [Matrix.map_apply] at h1
    rw [h1, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  set i₀ : Fin d := ⟨0, by omega⟩
  set ν : k := N i₀ i₀ with hν
  have hιν : ι ν = μ ^ q * μ * l := by
    rw [hν, hentry, if_pos rfl]
  have hνne : ν ≠ 0 := by
    intro h0
    have h1 : ι ν = 0 := by rw [h0, map_zero]
    rw [hιν] at h1
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hμ) hμ) hl0 h1
  refine ⟨ν, hνne, ?_, ?_⟩
  · apply ι.injective
    rw [hpow, hιν, mul_pow, mul_pow, hK μ, hlq]
    ring
  · ext a b
    apply ι.injective
    rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    change ι (N a b) = _
    rw [hentry]
    split_ifs with hab
    · rw [mul_one, hιν]
    · rw [mul_zero, map_zero]

end Similitudes

end CFSG.LocalAnalysis.GLTheoremA.T156.Uni

end
