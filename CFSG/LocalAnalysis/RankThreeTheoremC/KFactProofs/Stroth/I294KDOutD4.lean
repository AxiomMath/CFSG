module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicDFour

open scoped Matrix

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedOmega StatedQuadPlus StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.RankThreeTheoremC (mem_commutator_of_pow_three)

@[expose] def d4LZ (p q : Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Matrix.of fun i j =>
    if i = .inl p then (if j = .inr q then 1 else 0)
    else if i = .inl q then (if j = .inr p then -1 else 0)
    else if i = .inr p then (if j = .inl q then 1 else 0) - (if j = .inr p then 1 else 0)
    else if i = .inr q then -(if j = .inr q then 1 else 0) - (if j = .inl p then 1 else 0)
    else (if i = j then 1 else 0)

@[expose] def d4RZ (p q : Fin 4) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
  Matrix.of fun i j =>
    if i = .inl p then (if j = .inl q then 1 else 0)
    else if i = .inl q then -(if j = .inl p then 1 else 0) - (if j = .inl q then 1 else 0)
    else if i = .inr p then (if j = .inr q then 1 else 0) - (if j = .inr p then 1 else 0)
    else if i = .inr q then -(if j = .inr p then 1 else 0)
    else (if i = j then 1 else 0)

theorem d4LZ_cube : ∀ p q : Fin 4, p ≠ q → d4LZ p q * (d4LZ p q * d4LZ p q) = 1 := by
  decide +kernel

theorem d4RZ_cube : ∀ p q : Fin 4, p ≠ q → d4RZ p q * (d4RZ p q * d4RZ p q) = 1 := by
  decide +kernel

theorem d4_comm_LR : d4LZ 0 1 * d4RZ 0 1 = d4RZ 0 1 * d4LZ 0 1 := by decide +kernel
theorem d4_comm_LL : d4LZ 0 1 * d4LZ 2 3 = d4LZ 2 3 * d4LZ 0 1 := by decide +kernel
theorem d4_comm_LR' : d4LZ 0 1 * d4RZ 2 3 = d4RZ 2 3 * d4LZ 0 1 := by decide +kernel
theorem d4_comm_RL' : d4RZ 0 1 * d4LZ 2 3 = d4LZ 2 3 * d4RZ 0 1 := by decide +kernel
theorem d4_comm_RR : d4RZ 0 1 * d4RZ 2 3 = d4RZ 2 3 * d4RZ 0 1 := by decide +kernel
theorem d4_comm_LR'' : d4LZ 2 3 * d4RZ 2 3 = d4RZ 2 3 * d4LZ 2 3 := by decide +kernel

@[expose, reducible] def Robust (N : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → ℤ) : Prop :=
  (∃ i : Fin 4 ⊕ Fin 4, ∃ j : Fin 4 ⊕ Fin 4, i ≠ j ∧ (N i j = 1 ∨ N i j = -1)) ∨
    (∃ i : Fin 4 ⊕ Fin 4, ∃ j : Fin 4 ⊕ Fin 4, N i i - N j j = 1 ∨ N i i - N j j = -1)

theorem d4_robust_table : ∀ a b c d : Fin 3, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) →
    Robust (fun i j => (d4LZ 0 1 ^ a.val * d4RZ 0 1 ^ b.val * d4LZ 2 3 ^ c.val *
      d4RZ 2 3 ^ d.val) i j) := by
  decide +kernel

section GLSec

variable (F : Type) [Field F]

@[expose] def d4GL (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (h : M * (M * M) = 1) :
    GL (Fin 4 ⊕ Fin 4) F :=
  ⟨(Int.castRingHom F).mapMatrix M, (Int.castRingHom F).mapMatrix (M * M),
    by rw [← map_mul, h, map_one], by rw [← map_mul, mul_assoc, h, map_one]⟩

variable {F}

theorem coe_d4GL (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (h : M * (M * M) = 1) :
    ((d4GL F M h : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
      (Int.castRingHom F).mapMatrix M := rfl

theorem d4GL_pow_three (M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (h : M * (M * M) = 1) :
    (d4GL F M h) ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, coe_d4GL, ← map_pow, pow_succ, pow_two, mul_assoc,
    h, map_one]

theorem d4GL_commute (M N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (hM : M * (M * M) = 1)
    (hN : N * (N * N) = 1) (h : M * N = N * M) : Commute (d4GL F M hM) (d4GL F N hN) := by
  show d4GL F M hM * d4GL F N hN = d4GL F N hN * d4GL F M hM
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_d4GL, coe_d4GL, ← map_mul, ← map_mul, h]

@[expose] def d4A₁ (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  d4GL F (d4LZ 0 1) (d4LZ_cube 0 1 (by decide))

@[expose] def d4A₂ (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  d4GL F (d4RZ 0 1) (d4RZ_cube 0 1 (by decide))

@[expose] def d4A₃ (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  d4GL F (d4LZ 2 3) (d4LZ_cube 2 3 (by decide))

@[expose] def d4A₄ (F : Type) [Field F] : GL (Fin 4 ⊕ Fin 4) F :=
  d4GL F (d4RZ 2 3) (d4RZ_cube 2 3 (by decide))

theorem d4A₁_pow_three : (d4A₁ F) ^ 3 = 1 := d4GL_pow_three _ _
theorem d4A₂_pow_three : (d4A₂ F) ^ 3 = 1 := d4GL_pow_three _ _
theorem d4A₃_pow_three : (d4A₃ F) ^ 3 = 1 := d4GL_pow_three _ _
theorem d4A₄_pow_three : (d4A₄ F) ^ 3 = 1 := d4GL_pow_three _ _

theorem d4_commute₁₂ : Commute (d4A₁ F) (d4A₂ F) := d4GL_commute _ _ _ _ d4_comm_LR
theorem d4_commute₁₃ : Commute (d4A₁ F) (d4A₃ F) := d4GL_commute _ _ _ _ d4_comm_LL
theorem d4_commute₁₄ : Commute (d4A₁ F) (d4A₄ F) := d4GL_commute _ _ _ _ d4_comm_LR'
theorem d4_commute₂₃ : Commute (d4A₂ F) (d4A₃ F) := d4GL_commute _ _ _ _ d4_comm_RL'
theorem d4_commute₂₄ : Commute (d4A₂ F) (d4A₄ F) := d4GL_commute _ _ _ _ d4_comm_RR
theorem d4_commute₃₄ : Commute (d4A₃ F) (d4A₄ F) := d4GL_commute _ _ _ _ d4_comm_LR''

theorem d4A₁_quad (v : Fin 4 ⊕ Fin 4 → F) :
    StatedQuadPlus 4 F ((d4A₁ F : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      StatedQuadPlus 4 F v := by
  simp only [StatedQuadPlus, d4A₁, coe_d4GL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_four, d4LZ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp
  ring

theorem d4A₂_quad (v : Fin 4 ⊕ Fin 4 → F) :
    StatedQuadPlus 4 F ((d4A₂ F : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      StatedQuadPlus 4 F v := by
  simp only [StatedQuadPlus, d4A₂, coe_d4GL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_four, d4RZ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp
  ring

theorem d4A₃_quad (v : Fin 4 ⊕ Fin 4 → F) :
    StatedQuadPlus 4 F ((d4A₃ F : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      StatedQuadPlus 4 F v := by
  simp only [StatedQuadPlus, d4A₃, coe_d4GL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_four, d4LZ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp
  ring

theorem d4A₄_quad (v : Fin 4 ⊕ Fin 4 → F) :
    StatedQuadPlus 4 F ((d4A₄ F : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) *ᵥ v) =
      StatedQuadPlus 4 F v := by
  simp only [StatedQuadPlus, d4A₄, coe_d4GL, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_four, d4RZ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp
  ring

theorem d4_independent (a b c d : ℕ)
    (h : (d4A₁ F) ^ a * (d4A₂ F) ^ b * (d4A₃ F) ^ c * (d4A₄ F) ^ d ∈
      StatedScalars (Fin 4 ⊕ Fin 4) F) :
    3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c ∧ 3 ∣ d := by
  rw [pow_eq_pow_mod a (d4A₁_pow_three (F := F)), pow_eq_pow_mod b (d4A₂_pow_three (F := F)),
    pow_eq_pow_mod c (d4A₃_pow_three (F := F)), pow_eq_pow_mod d (d4A₄_pow_three (F := F))] at h
  by_contra hne
  have hres : (⟨a % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) ≠ 0 ∨
      (⟨b % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) ≠ 0 ∨
      (⟨c % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) ≠ 0 ∨
      (⟨d % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) ≠ 0 := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero]
    omega
  have hrob := d4_robust_table _ _ _ _ hres
  simp only at hrob
  set NZ : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ :=
    d4LZ 0 1 ^ (a % 3) * d4RZ 0 1 ^ (b % 3) * d4LZ 2 3 ^ (c % 3) * d4RZ 2 3 ^ (d % 3) with hNZ
  have hP : (((d4A₁ F) ^ (a % 3) * (d4A₂ F) ^ (b % 3) * (d4A₃ F) ^ (c % 3) *
      (d4A₄ F) ^ (d % 3) : GL (Fin 4 ⊕ Fin 4) F) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) =
      (Int.castRingHom F).mapMatrix NZ := by
    simp only [hNZ, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    rfl
  obtain ⟨c0, hc0⟩ := h
  have hent : ∀ i j : Fin 4 ⊕ Fin 4, ((NZ i j : ℤ) : F) = if i = j then (c0 : F) else 0 := by
    intro i j
    have := congrArg (fun g : GL (Fin 4 ⊕ Fin 4) F =>
      (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) F) i j) hc0
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
      at this
    rw [hP] at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom] at this
    rw [← this]
  rcases hrob with ⟨i, j, hij, hv⟩ | ⟨i, j, hv⟩
  · have hv' : NZ i j = 1 ∨ NZ i j = -1 := hv
    have h0 := hent i j
    rw [if_neg hij] at h0
    rcases hv' with hv' | hv' <;> rw [hv'] at h0 <;> simp at h0
  · have hv' : NZ i i - NZ j j = 1 ∨ NZ i i - NZ j j = -1 := hv
    have h1 := hent i i
    have h2 := hent j j
    rw [if_pos rfl] at h1 h2
    have h3 : ((NZ i i - NZ j j : ℤ) : F) = 0 := by
      rw [Int.cast_sub, h1, h2, sub_self]
    rcases hv' with hv' | hv' <;> rw [hv'] at h3 <;> simp at h3

end GLSec

theorem d4ThreeRankFour_holds : D4ThreeRankFour := by
  intro X _ _ ℓ f h
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hab := orthogonal_model_isometry_abelianization_order_bound X .POmegaPlus
    (.inr (.inl rfl)) 4 ℓ f h K hK (quadPlus 4 K) (coe_quadPlus 4 K) e
  have hmem : ∀ g : GL (Fin 4 ⊕ Fin 4) K,
      (∀ v, StatedQuadPlus 4 K ((g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ v) =
        StatedQuadPlus 4 K v) → g ^ 3 = 1 → g ∈ StatedOmega (StatedQuadPlus 4 K) := by
    intro g hg hg3
    rw [statedOmega_eq_comap (coe_quadPlus 4 K), Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    refine mem_commutator_of_pow_three _ hab.1 ?_ ?_
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [toLinEquiv_apply, coe_quadPlus]
      exact hg v
    · rw [← map_pow, hg3, map_one]
  exact four_le_pRank_statedProj (StatedOmega (StatedQuadPlus 4 K)) e (d4A₁ K) (d4A₂ K)
    (d4A₃ K) (d4A₄ K) (hmem _ d4A₁_quad d4A₁_pow_three) (hmem _ d4A₂_quad d4A₂_pow_three)
    (hmem _ d4A₃_quad d4A₃_pow_three) (hmem _ d4A₄_quad d4A₄_pow_three) d4A₁_pow_three
    d4A₂_pow_three d4A₃_pow_three d4A₄_pow_three d4_commute₁₂ d4_commute₁₃ d4_commute₁₄
    d4_commute₂₃ d4_commute₂₄ d4_commute₃₄ d4_independent

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
