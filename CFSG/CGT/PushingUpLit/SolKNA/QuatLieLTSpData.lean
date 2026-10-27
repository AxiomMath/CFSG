module

public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSp
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Complement
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.LieType.Universal.Symplectic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.LTSp

open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.ModelFacts.TG3
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

section Pure

variable {K : Type} [Field K]

theorem mem_center_of_mat_eq_neg_one {n : ℕ} {x : StatedSp n K} (h : mat n K x = -1) :
    x ∈ Subgroup.center (StatedSp n K) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply mat_injective
  rw [map_mul, map_mul, h, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]

theorem coords_zero_compl : (coords (0 : Fin 2))ᶜ = coords (1 : Fin 2) := by
  ext a
  rcases a with a | a <;> fin_cases a <;> simp [coords]

theorem mat_longInv_one_mul_zero : mat 2 K (longInv K 2 1 * longInv K 2 0) = -1 := by
  rw [map_mul, mat_longInv, mat_longInv, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one,
    Matrix.diagonal_neg]
  congr 1
  funext a
  rcases a with a | a <;> fin_cases a <;> simp [coords]

end Pure

section Model


open CFSG.ClassicalInvolution.Generic

theorem two_data :
    ∃ R₀ : Subgroup (StatedSp 2 (GaloisField 3 1)),
      R₀ ∈ fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D ∧
      ∃ z₀ w₀ : StatedSp 2 (GaloisField 3 1),
        z₀ ∈ R₀ ∧ z₀ * z₀ = 1 ∧ z₀ ≠ 1 ∧
          w₀ * z₀ * w₀⁻¹ * z₀⁻¹ ∈ Subgroup.center (StatedSp 2 (GaloisField 3 1)) ∧
          ∀ a ∈ R₀, ∀ b ∈ R₀, Commute (w₀ * a * w₀⁻¹) b := by
  have hadm : StatedLieAdmissible .PSp 2 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, fun h => by simpa using congrArg Prod.snd h⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hR : ∀ k : Fin 2, longRootSp2 (GaloisField 3 1) 2 k ∈
      fundamentalSubgroups .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D := fun k =>
    (ModelFacts.fund_iff_isLongRootSp2 hadm h2 _).mpr ⟨_, isLongRootSp2_standard k⟩
  obtain ⟨g, hg'⟩ : ∃ g : StatedSp 2 (GaloisField 3 1), longRootSp2 (GaloisField 3 1) 2 1 =
      (longRootSp2 (GaloisField 3 1) 2 0).map (MulAut.conj g).toMonoidHom :=
    (ModelFacts.fundamentalSingleClass .PSp 2 3 1 Nat.prime_three trivial hadm
      (by decide) (by decide)) _ (hR 0) _ (hR 1)
  have h0 := isLongRootSp2_standard (K := GaloisField 3 1) (n := 2) 0
  have h1 := isLongRootSp2_standard (K := GaloisField 3 1) (n := 2) 1
  have hord := (h0.isClassicalSL2 h2).orderOf_eq_two
  have hz2 : longInv (GaloisField 3 1) 2 0 * longInv (GaloisField 3 1) 2 0 = 1 := by
    have := pow_orderOf_eq_one (longInv (GaloisField 3 1) 2 0)
    rwa [hord, sq] at this
  have hconj : IsLongRootSp2 (longRootSp2 (GaloisField 3 1) 2 1)
      (g * longInv (GaloisField 3 1) 2 0 * g⁻¹) := by
    rw [hg']
    exact h0.conj g
  have hi : g * longInv (GaloisField 3 1) 2 0 * g⁻¹ = longInv (GaloisField 3 1) 2 1 :=
    hconj.involution_unique h2 h1
  refine ⟨longRootSp2 (GaloisField 3 1) 2 0, hR 0, longInv (GaloisField 3 1) 2 0, g,
    longInv_mem_longRootSp2 0, hz2, ?_, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · rw [hi]
    apply mem_center_of_mat_eq_neg_one
    rw [inv_eq_of_mul_eq_one_right hz2]
    exact mat_longInv_one_mul_zero
  · intro a ha b hb
    have hga : g * a * g⁻¹ ∈ suppGroup (coords (0 : Fin 2))ᶜ := by
      rw [coords_zero_compl, ← longRootSp2_eq_suppGroup, hg']
      exact ⟨a, ha, rfl⟩
    have hb' : b ∈ suppGroup (coords (0 : Fin 2)) := by
      rw [← longRootSp2_eq_suppGroup]
      exact hb
    exact (commute_suppGroup_compl hb' hga).symm

theorem comp_data (n : ℕ) (hn : 3 ≤ n) :
    ∃ R₀ : Subgroup (StatedSp n (GaloisField 3 1)),
      R₀ ∈ fundamentalSubgroups .PSp (modelUniv .PSp n 3 1 Nat.prime_three).D ∧
      ∃ z₀ : StatedSp n (GaloisField 3 1), z₀ ∈ R₀ ∧ z₀ * z₀ = 1 ∧ z₀ ≠ 1 ∧
        ∃ E₀ : Subgroup (StatedSp n (GaloisField 3 1)),
          (∀ y ∈ E₀, y * z₀ = z₀ * y) ∧
          (∀ a, a * z₀ * a⁻¹ * z₀⁻¹ ∈ Subgroup.center (StatedSp n (GaloisField 3 1)) →
            ∀ y ∈ E₀, a * y * a⁻¹ ∈ E₀) ∧
          CFSG.IsQuasisimple ↥E₀ ∧
          ∀ y ∈ E₀, y ∈ Subgroup.center (StatedSp n (GaloisField 3 1)) → y = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hadm : StatedLieAdmissible .PSp (m + 1) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, fun h => by simpa using congrArg Prod.snd h⟩
  have hadm' : StatedLieAdmissible .PSp m 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, fun h => by simpa using congrArg Prod.snd h⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have h0 := isLongRootSp2_standard (K := GaloisField 3 1) (n := m + 1) 0
  have hcl := h0.isClassicalSL2 h2
  have hord := hcl.orderOf_eq_two
  have hz2 : longInv (GaloisField 3 1) (m + 1) 0 * longInv (GaloisField 3 1) (m + 1) 0 = 1 := by
    have := pow_orderOf_eq_one (longInv (GaloisField 3 1) (m + 1) 0)
    rwa [hord, sq] at this
  refine ⟨longRootSp2 (GaloisField 3 1) (m + 1) 0,
    (ModelFacts.fund_iff_isLongRootSp2 hadm h2 _).mpr ⟨_, h0⟩, longInv (GaloisField 3 1) (m + 1) 0,
    longInv_mem_longRootSp2 0, hz2, ?_, complGroup (longInv (GaloisField 3 1) (m + 1) 0),
    ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · intro y hy
    exact (h0.commute_of_mem_complGroup h2 hcl.mem hy).symm.eq
  · intro a ha y hy
    have hc : a * longInv (GaloisField 3 1) (m + 1) 0 =
        longInv (GaloisField 3 1) (m + 1) 0 * a := by
      have h1 := h0.conj a
      have hLeq : longRootSp2 (GaloisField 3 1) (m + 1) 0 =
          (longRootSp2 (GaloisField 3 1) (m + 1) 0).map (MulAut.conj a).toMonoidHom :=
        eq_of_central_ratio_longRootSp (by omega) (by omega) h0 h1 ha
      have hmem : a * longInv (GaloisField 3 1) (m + 1) 0 * a⁻¹ ∈
          longRootSp2 (GaloisField 3 1) (m + 1) 0 := by
        rw [hLeq]
        exact (h1.isClassicalSL2 h2).mem
      have hci := h0.eq_of_orderOf_eq_two h2 hmem (h1.isClassicalSL2 h2).orderOf_eq_two
      calc a * longInv (GaloisField 3 1) (m + 1) 0
          = a * longInv (GaloisField 3 1) (m + 1) 0 * a⁻¹ * a := by group
        _ = longInv (GaloisField 3 1) (m + 1) 0 * a := by rw [hci]
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := h0.exists_mul_of_mem_centralizer h2
      (Subgroup.mem_centralizer_singleton_iff.mpr hc)
    have hy' : b₁ * y * b₁⁻¹ ∈ complGroup (longInv (GaloisField 3 1) (m + 1) 0) :=
      (complGroup _).mul_mem ((complGroup _).mul_mem hb₁ hy) ((complGroup _).inv_mem hb₁)
    have hc1 := (h0.commute_of_mem_complGroup h2 ha₁ hy').eq
    have e1 : a₁ * b₁ * y * (a₁ * b₁)⁻¹ = b₁ * y * b₁⁻¹ := by
      calc a₁ * b₁ * y * (a₁ * b₁)⁻¹ = a₁ * (b₁ * y * b₁⁻¹) * a₁⁻¹ := by group
        _ = b₁ * y * b₁⁻¹ * a₁ * a₁⁻¹ := by rw [hc1]
        _ = b₁ * y * b₁⁻¹ := by group
    rw [e1]
    exact hy'
  · obtain ⟨e⟩ := h0.nonempty_mulEquiv_complGroup h2
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible m (GaloisField 3 1) hadm'
        (GaloisField.card 3 1 (by norm_num)))
  · intro y hy hz
    rw [complGroup_longInv h2] at hy
    exact eq_one_of_mem_center_of_mem_suppGroup hz hy (t := Sum.inl 0)
      (fun h => Set.mem_compl_iff _ _ |>.mp h (inl_mem_coords 0))

end Model

end CFSG.CGT.PushingUpLit.SolKNA.LTSp
