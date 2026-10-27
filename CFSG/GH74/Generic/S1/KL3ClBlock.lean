module

public import CFSG.GH74.Filter.Small.Eigenbasis
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import Mathlib.RingTheory.PiTensorProduct

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.GH74.Generic.S1

section Block

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (K : Type*) [Field K]

def kl3clIncl (ν : κ → ι) : Matrix ι κ K := Matrix.of fun a i => if ν i = a then 1 else 0

def kl3clBlk (ν : κ → ι) (X : Matrix κ κ K) : Matrix ι ι K :=
  1 + kl3clIncl K ν * (X - 1) * (kl3clIncl K ν).transpose

variable {K}

omit [Fintype κ] in
theorem kl3clIncl_transpose_mul {ν : κ → ι} (hν : Function.Injective ν) :
    (kl3clIncl K ν).transpose * kl3clIncl K ν = 1 := by
  ext i j
  simp [Matrix.mul_apply, kl3clIncl, Matrix.one_apply, hν.eq_iff]

theorem kl3clBlk_mul {ν : κ → ι} (hν : Function.Injective ν) (X Y : Matrix κ κ K) :
    kl3clBlk K ν (X * Y) = kl3clBlk K ν X * kl3clBlk K ν Y := by
  have hE := kl3clIncl_transpose_mul (K := K) hν
  set E := kl3clIncl K ν with hEdef
  have h1 : E * (X - 1) * E.transpose * (E * (Y - 1) * E.transpose) =
      E * ((X - 1) * (Y - 1)) * E.transpose := by
    calc E * (X - 1) * E.transpose * (E * (Y - 1) * E.transpose)
        = E * (X - 1) * (E.transpose * E) * (Y - 1) * E.transpose := by
          simp only [Matrix.mul_assoc]
      _ = E * ((X - 1) * (Y - 1)) * E.transpose := by
          rw [hE, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have h3 : E * (X * Y - 1) * E.transpose = E * (X - 1) * E.transpose + E * (Y - 1) * E.transpose +
      E * ((X - 1) * (Y - 1)) * E.transpose := by
    rw [h2, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  unfold kl3clBlk
  rw [← hEdef, h3, ← h1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  abel

omit [Fintype ι] in
theorem kl3clBlk_one (ν : κ → ι) : kl3clBlk K ν 1 = 1 := by
  simp [kl3clBlk]

theorem kl3clBlk_det {ν : κ → ι} (hν : Function.Injective ν) (X : Matrix κ κ K) :
    (kl3clBlk K ν X).det = X.det := by
  have hE := kl3clIncl_transpose_mul (K := K) hν
  unfold kl3clBlk
  rw [Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hE, Matrix.one_mul, add_sub_cancel]

theorem kl3clBlk_compress {ν : κ → ι} (hν : Function.Injective ν) (X : Matrix κ κ K) :
    (kl3clIncl K ν).transpose * kl3clBlk K ν X * kl3clIncl K ν = X := by
  have hE := kl3clIncl_transpose_mul (K := K) hν
  unfold kl3clBlk
  calc (kl3clIncl K ν).transpose * (1 + kl3clIncl K ν * (X - 1) * (kl3clIncl K ν).transpose) *
        kl3clIncl K ν
      = (kl3clIncl K ν).transpose * kl3clIncl K ν +
        (kl3clIncl K ν).transpose * kl3clIncl K ν * (X - 1) *
          ((kl3clIncl K ν).transpose * kl3clIncl K ν) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = X := by rw [hE, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]

theorem kl3clBlk_injective {ν : κ → ι} (hν : Function.Injective ν) :
    Function.Injective (kl3clBlk K ν) := fun X Y h => by
  rw [← kl3clBlk_compress hν X, h, kl3clBlk_compress hν Y]

omit [Fintype ι] in
theorem kl3clBlk_apply_of_ne {ν : κ → ι} {a : ι} (ha : ∀ i, ν i ≠ a) (X : Matrix κ κ K) :
    kl3clBlk K ν X a a = 1 := by
  simp [kl3clBlk, Matrix.mul_apply, kl3clIncl, ha]

theorem kl3clBlk_commute_diagonal {ν : κ → ι} (s : ι → K) (c : K) (hc : ∀ i, s (ν i) = c)
    (X : Matrix κ κ K) :
    kl3clBlk K ν X * Matrix.diagonal s = Matrix.diagonal s * kl3clBlk K ν X := by
  have h1 : (kl3clIncl K ν).transpose * Matrix.diagonal s = c • (kl3clIncl K ν).transpose := by
    ext i a
    by_cases h : ν i = a
    · subst h; simp [Matrix.mul_diagonal, kl3clIncl, hc]
    · simp [Matrix.mul_diagonal, kl3clIncl, h]
  have h2 : Matrix.diagonal s * kl3clIncl K ν = c • kl3clIncl K ν := by
    ext a i
    by_cases h : ν i = a
    · subst h; simp [Matrix.diagonal_mul, kl3clIncl, hc]
    · simp [Matrix.diagonal_mul, kl3clIncl, h]
  have hL : kl3clIncl K ν * (X - 1) * (kl3clIncl K ν).transpose * Matrix.diagonal s =
      c • (kl3clIncl K ν * (X - 1) * (kl3clIncl K ν).transpose) := by
    rw [Matrix.mul_assoc (kl3clIncl K ν * (X - 1)), h1, Matrix.mul_smul]
  have hR : Matrix.diagonal s * (kl3clIncl K ν * (X - 1) * (kl3clIncl K ν).transpose) =
      c • (kl3clIncl K ν * (X - 1) * (kl3clIncl K ν).transpose) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.smul_mul, Matrix.smul_mul]
  unfold kl3clBlk
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hL, hR]

def kl3clBlkHom {ν : κ → ι} (hν : Function.Injective ν) : Matrix κ κ K →* Matrix ι ι K where
  toFun := kl3clBlk K ν
  map_one' := kl3clBlk_one ν
  map_mul' := kl3clBlk_mul hν

def kl3clBlockGL {ν : κ → ι} (hν : Function.Injective ν) :
    Matrix.SpecialLinearGroup κ K →* GL ι K :=
  (Units.map (kl3clBlkHom hν)).comp Matrix.SpecialLinearGroup.toGL

theorem kl3clBlockGL_coe {ν : κ → ι} (hν : Function.Injective ν)
    (X : Matrix.SpecialLinearGroup κ K) :
    ((kl3clBlockGL hν X : GL ι K) : Matrix ι ι K) = kl3clBlk K ν (X : Matrix κ κ K) := by
  rfl

theorem kl3clBlockGL_injective {ν : κ → ι} (hν : Function.Injective ν) :
    Function.Injective (kl3clBlockGL (K := K) hν) :=
  (Units.map_injective (kl3clBlk_injective hν)).comp Matrix.SpecialLinearGroup.toGL_injective

theorem kl3cl_block_of_class {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (y Pg : GL ι K) (s : ι → K)
    (hD : ((Pg⁻¹ * y * Pg : GL ι K) : Matrix ι ι K) = Matrix.diagonal s)
    (I : Finset ι) (c : K) (hc : ∀ a ∈ I, s a = c) (hIne : ∃ a, a ∉ I) (hI2 : 2 ≤ I.card)
    (hperf : 3 ≤ I.card ∨ ∃ t : Finset K, t.card = 4) :
    ∃ Q : Subgroup (GL ι K), ⁅Q, Q⁆ = Q ∧ Q ≠ ⊥ ∧ (∀ g ∈ Q, (g : Matrix ι ι K).det = 1) ∧
      (∀ g ∈ Q, g * y = y * g) ∧
      (∀ g ∈ Q, (∃ c : Kˣ, (g : Matrix ι ι K) = (c : K) • (1 : Matrix ι ι K)) → g = 1) := by
  let ν : Fin I.card → ι := fun i => ((I.equivFin.symm i : I) : ι)
  have hν : Function.Injective ν := Subtype.val_injective.comp I.equivFin.symm.injective
  have hνI : ∀ i, ν i ∈ I := fun i => (I.equivFin.symm i).2
  let β := kl3clBlockGL (K := K) hν
  let θ : Matrix.SpecialLinearGroup (Fin I.card) K →* GL ι K :=
    (MulAut.conj Pg).toMonoidHom.comp β
  have hθ : ∀ X, θ X = Pg * β X * Pg⁻¹ := fun X => rfl
  have hθinj : Function.Injective θ := (MulAut.conj Pg).injective.comp (kl3clBlockGL_injective hν)
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin I.card) K) :=
    CFSG.LinearGroups.special_linear_isPerfect hI2 hperf
  have hnt : Nontrivial (Matrix.SpecialLinearGroup (Fin I.card) K) := by
    have : Nontrivial (Fin I.card) := Fin.nontrivial_iff_two_le.2 hI2
    have : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin I.card) K) := inferInstance
    exact Function.Surjective.nontrivial (f := (QuotientGroup.mk :
      Matrix.SpecialLinearGroup (Fin I.card) K →
        Matrix.ProjectiveSpecialLinearGroup (Fin I.card) K)) QuotientGroup.mk_surjective
  refine ⟨θ.range, ?_, ?_, ?_, ?_, ?_⟩
  · have : Group.IsPerfect θ.range := Group.IsPerfect.range θ
    exact Subgroup.isPerfect_iff.1 this
  · obtain ⟨X, hX⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin I.card) K)
    intro hbot
    apply hX
    have : θ X ∈ θ.range := ⟨X, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hθinj (this.trans (map_one θ).symm)
  · rintro _ ⟨X, rfl⟩
    rw [hθ]
    have hPP : (Pg : Matrix ι ι K).det * ((Pg⁻¹ : GL ι K) : Matrix ι ι K).det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, hPP, one_mul]
    show (kl3clBlk K ν (X : Matrix _ _ K)).det = 1
    rw [kl3clBlk_det hν, X.2]
  · rintro _ ⟨X, rfl⟩
    rw [hθ]
    have hy : y = Pg * (Pg⁻¹ * y * Pg) * Pg⁻¹ := by group
    have hcomm : β X * (Pg⁻¹ * y * Pg) = (Pg⁻¹ * y * Pg) * β X := by
      generalize Pg⁻¹ * y * Pg = Dg at hD
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hD]
      exact kl3clBlk_commute_diagonal s c (fun i => hc _ (hνI i)) _
    calc Pg * β X * Pg⁻¹ * y = Pg * β X * Pg⁻¹ * (Pg * (Pg⁻¹ * y * Pg) * Pg⁻¹) := by rw [← hy]
      _ = Pg * (β X * (Pg⁻¹ * y * Pg)) * Pg⁻¹ := by group
      _ = Pg * ((Pg⁻¹ * y * Pg) * β X) * Pg⁻¹ := by rw [hcomm]
      _ = (Pg * (Pg⁻¹ * y * Pg) * Pg⁻¹) * (Pg * β X * Pg⁻¹) := by group
      _ = y * (Pg * β X * Pg⁻¹) := by rw [← hy]
  · rintro _ ⟨X, rfl⟩ ⟨u, hu⟩
    rw [hθ] at hu
    have h1 : (β X : GL ι K) = Pg⁻¹ * (Pg * β X * Pg⁻¹) * Pg := by group
    have h2 : ((β X : GL ι K) : Matrix ι ι K) = (u : K) • (1 : Matrix ι ι K) := by
      rw [h1, Units.val_mul, Units.val_mul, hu, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
        Units.inv_mul]
    obtain ⟨a, ha⟩ := hIne
    have hνa : ∀ i, ν i ≠ a := fun i h => ha (h ▸ hνI i)
    have hu1 : (u : K) = 1 := by
      have h3 := congrFun (congrFun h2 a) a
      rw [kl3clBlockGL_coe, kl3clBlk_apply_of_ne hνa] at h3
      simpa using h3.symm
    have hX1 : X = 1 := by
      apply Subtype.ext
      apply kl3clBlk_injective hν
      rw [← kl3clBlockGL_coe hν X, h2, hu1, one_smul]
      exact (kl3clBlk_one ν).symm
    rw [hX1, map_one]

theorem kl3cl_diagonalize {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) (y : GL ι K) (hy : y * y = 1) :
    ∃ (Pg : GL ι K) (s : ι → K), (∀ a, s a = 1 ∨ s a = -1) ∧
      ((Pg⁻¹ * y * Pg : GL ι K) : Matrix ι ι K) = Matrix.diagonal s := by
  let T : Module.End K (ι → K) := Matrix.toLin' (y : Matrix ι ι K)
  have hT2 : T * T = 1 := by
    show Matrix.toLin' (y : Matrix ι ι K) * Matrix.toLin' (y : Matrix ι ι K) = 1
    have h : (y : Matrix ι ι K) * (y : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, hy, Units.val_one]
    have h' : Matrix.toLin' ((y : Matrix ι ι K) * (y : Matrix ι ι K)) = LinearMap.id := by
      rw [h, Matrix.toLin'_one]
    rw [Matrix.toLin'_mul] at h'
    exact h'
  have hT2' : T ^ 2 = 1 := by rw [sq, hT2]
  obtain ⟨b, μ, hb⟩ := CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2
    (fun _ : Fin 1 => T) (fun _ _ => Commute.refl _) (fun _ => hT2')
  have hcard : Fintype.card ι = Module.finrank K (ι → K) :=
    (Module.finrank_fintype_fun_eq_card K).symm
  let e : Fin (Module.finrank K (ι → K)) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  let b' : Module.Basis ι K (ι → K) := b.reindex e
  let s : ι → K := fun a => μ 0 (e.symm a)
  have hb' : ∀ a, T (b' a) = s a • b' a := fun a => by
    have := hb 0 (e.symm a)
    simpa [b', s] using this
  have hsq : ∀ a, s a * s a = 1 := fun a => by
    have h1 : T (T (b' a)) = b' a := by
      have : (T * T) (b' a) = (1 : Module.End K (ι → K)) (b' a) := by rw [hT2]
      simpa using this
    rw [hb', map_smul, hb', smul_smul] at h1
    have h3 : (s a * s a - 1) • b' a = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b'.ne_zero a))
  have hsign : ∀ a, s a = 1 ∨ s a = -1 := fun a => by
    have : (s a - 1) * (s a + 1) = 0 := by linear_combination hsq a
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  let P : Matrix ι ι K := (Pi.basisFun K ι).toMatrix b'
  have hPunit : IsUnit P := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := (Pi.basisFun K ι).isUnit_det b'
    rwa [Module.Basis.det_apply] at this
  obtain ⟨Pg, hPg⟩ := hPunit
  have hPapp : ∀ a c, P a c = b' c a := fun a c => by
    simp [P, Module.Basis.toMatrix_apply]
  have hyP : (y : Matrix ι ι K) * P = P * Matrix.diagonal s := by
    ext a c
    have h1 : ((y : Matrix ι ι K) * P) a c = (T (b' c)) a := by
      simp only [Matrix.mul_apply, hPapp]
      rfl
    rw [h1, hb' c, Matrix.mul_diagonal, hPapp, Pi.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨Pg, s, hsign, ?_⟩
  have hyPg : (y : Matrix ι ι K) * (Pg : Matrix ι ι K) =
      (Pg : Matrix ι ι K) * Matrix.diagonal s := by
    rw [hPg]; exact hyP
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hyPg, ← Matrix.mul_assoc, Units.inv_mul,
    Matrix.one_mul]

theorem kl3cl_exists_perfect_block {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (h2 : (2 : K) ≠ 0)
    (hn : Fintype.card ι = 5 ∨ (Fintype.card ι = 4 ∧ 4 ≤ Nat.card K))
    (y : GL ι K) (hy : y * y = 1)
    (hns : ∀ c : Kˣ, (y : Matrix ι ι K) ≠ (c : K) • (1 : Matrix ι ι K)) :
    ∃ Q : Subgroup (GL ι K), ⁅Q, Q⁆ = Q ∧ Q ≠ ⊥ ∧ (∀ g ∈ Q, (g : Matrix ι ι K).det = 1) ∧
      (∀ g ∈ Q, g * y = y * g) ∧
      (∀ g ∈ Q, (∃ c : Kˣ, (g : Matrix ι ι K) = (c : K) • (1 : Matrix ι ι K)) → g = 1) := by
  classical
  obtain ⟨Pg, s, hs, hD⟩ := kl3cl_diagonalize h2 y hy
  obtain ⟨Dg, hDg⟩ : ∃ Dg : GL ι K, Dg = Pg⁻¹ * y * Pg := ⟨_, rfl⟩
  have hy' : y = Pg * Dg * Pg⁻¹ := by rw [hDg]; group
  have hD' : (Dg : Matrix ι ι K) = Matrix.diagonal s := by rw [hDg]; exact hD
  have hscal : ∀ c : Kˣ, ¬ ∀ a, s a = (c : K) := by
    intro c hc
    apply hns c
    have hDc : (Dg : Matrix ι ι K) = (c : K) • (1 : Matrix ι ι K) := by
      rw [hD', Matrix.smul_one_eq_diagonal]
      exact congrArg Matrix.diagonal (funext hc)
    rw [hy', Units.val_mul, Units.val_mul, hDc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Units.mul_inv]
  have hne₁ : ∃ a, s a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hscal 1 fun a => by simpa using hcon a
  have hne₂ : ∃ a, s a = 1 := by
    by_contra hcon
    push Not at hcon
    refine hscal (-1) fun a => ?_
    rcases hs a with h | h
    · exact absurd h (hcon a)
    · simpa using h
  obtain ⟨a₁, ha₁⟩ := hne₁
  obtain ⟨a₂, ha₂⟩ := hne₂
  let Ip : Finset ι := Finset.univ.filter (fun a => s a = 1)
  let Im : Finset ι := Finset.univ.filter (fun a => ¬ s a = 1)
  have hcard : Ip.card + Im.card = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hIp1 : 1 ≤ Ip.card := Finset.card_pos.2 ⟨a₂, by simp [Ip, ha₂]⟩
  have hIm1 : 1 ≤ Im.card := Finset.card_pos.2 ⟨a₁, by simp [Im, ha₁]⟩
  have hcIp : ∀ a ∈ Ip, s a = 1 := fun a ha => (Finset.mem_filter.1 ha).2
  have hcIm : ∀ a ∈ Im, s a = -1 := fun a ha =>
    (hs a).resolve_left (Finset.mem_filter.1 ha).2
  have hoIp : ∃ a, a ∉ Ip := ⟨a₁, fun h => ha₁ (hcIp a₁ h)⟩
  have hoIm : ∃ a, a ∉ Im := ⟨a₂, fun h => (Finset.mem_filter.1 h).2 ha₂⟩
  have hK4 : (Fintype.card ι = 4 ∧ 4 ≤ Nat.card K) → ∃ t : Finset K, t.card = 4 := by
    rintro ⟨-, h4⟩
    have : Fintype K := Fintype.ofFinite K
    have h4' : 4 ≤ (Finset.univ : Finset K).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4'
    exact ⟨t, ht⟩
  rcases hn with h5 | ⟨h4, hK⟩
  · by_cases hu : 3 ≤ Ip.card
    · exact kl3cl_block_of_class y Pg s hD Ip 1 hcIp hoIp (by omega) (Or.inl hu)
    · exact kl3cl_block_of_class y Pg s hD Im (-1) hcIm hoIm (by omega) (Or.inl (by omega))
  · by_cases hu : 3 ≤ Ip.card
    · exact kl3cl_block_of_class y Pg s hD Ip 1 hcIp hoIp (by omega) (Or.inl hu)
    · by_cases hv : 3 ≤ Im.card
      · exact kl3cl_block_of_class y Pg s hD Im (-1) hcIm hoIm (by omega) (Or.inl hv)
      · exact kl3cl_block_of_class y Pg s hD Ip 1 hcIp hoIp (by omega)
          (Or.inr (hK4 ⟨h4, hK⟩))

end Block

end CFSG.GH74.Generic.S1
