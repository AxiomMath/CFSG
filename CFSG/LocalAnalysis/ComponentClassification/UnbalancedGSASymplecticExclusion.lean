module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Matrix CFSG.Assembly.LowTwoRank

namespace SymplecticExclusion

theorem exists_quaternion_of_hom {S G : Type*} [Group S] [Group G] (φ : S →* G) {x y z : S}
    (hz2 : z ^ 2 = 1) (hx : x ^ 2 = z) (hy : y ^ 2 = z) (hxy : x * y = z * (y * x))
    (hz : φ z ≠ 1) : ∃ H : Subgroup G, Nonempty (H ≃* QuaternionGroup 2) := by
  have hz2' : φ z ^ 2 = 1 := by rw [← map_pow φ, hz2, map_one]
  have hx' : φ x ^ 2 = φ z := by rw [← map_pow φ, hx]
  have hy' : φ y ^ 2 = φ z := by rw [← map_pow φ, hy]
  have hxy' : φ x * φ y = φ z * (φ y * φ x) := by
    rw [← map_mul φ, hxy, map_mul φ, map_mul φ]
  obtain ⟨H, -, -, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.exists_quaternion_subgroup_of_anticommuting hz hz2' hx' hy'
      hxy'
  exact ⟨H, ⟨e.symm⟩⟩

theorem exists_quaternion_of_sl2_hom {k G : Type*} [Field k] [Finite k] [Group G]
    (hk : ringChar k ≠ 2) (φ : SpecialLinearGroup (Fin 2) k →* G) (hφ : φ (-1) ≠ 1) :
    ∃ H : Subgroup G, Nonempty (H ≃* QuaternionGroup 2) := by
  obtain ⟨a, b, hab⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hk (-1)
  obtain ⟨x, y, -, -, hx, hy, hxy⟩ :=
    LocalAnalysis.ComponentInitial.sl2_exists_anticommuting_pair hab
  exact exists_quaternion_of_hom φ (by rw [neg_one_sq]) hx hy hxy hφ

variable {K : Type} [Field K] {n : ℕ}

@[expose] def famMat (X : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (diagonal fun j => X j 0 0) (diagonal fun j => X j 0 1)
    (diagonal fun j => X j 1 0) (diagonal fun j => X j 1 1)

theorem famMat_one : famMat (1 : Fin n → Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp only [famMat, Pi.one_apply, one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [diagonal_one, diagonal_zero, fromBlocks_one]

theorem famMat_mul (X Y : Fin n → Matrix (Fin 2) (Fin 2) K) :
    famMat (X * Y) = famMat X * famMat Y := by
  simp only [famMat, fromBlocks_multiply, diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> congr 1 <;> funext j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def famHom : (Fin n → Matrix (Fin 2) (Fin 2) K) →*
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K where
  toFun := famMat
  map_one' := famMat_one
  map_mul' := famMat_mul

theorem famMat_symplectic {X : Fin n → Matrix (Fin 2) (Fin 2) K} (hX : ∀ j, (X j).det = 1) :
    (famMat X)ᵀ * fromBlocks 0 1 (-1) 0 * famMat X = fromBlocks 0 1 (-1) 0 := by
  have hX' : ∀ j, X j 0 0 * X j 1 1 - X j 0 1 * X j 1 0 = 1 := fun j => by
    rw [← det_fin_two]
    exact hX j
  simp only [famMat, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, neg_mul,
    diagonal_mul_diagonal, diagonal_neg, diagonal_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> ext a b <;>
    simp only [diagonal_apply, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply] <;>
    split_ifs <;> first | rfl | ring1 | linear_combination hX' a | linear_combination -hX' a

@[expose] noncomputable def planeGL (i : Fin n) :
    SpecialLinearGroup (Fin 2) K →* GL (Fin n ⊕ Fin n) K :=
  (Units.map ((famHom (K := K) (n := n)).comp
    (MonoidHom.mulSingle (fun _ => Matrix (Fin 2) (Fin 2) K) i))).comp
    SpecialLinearGroup.toGL

theorem coe_planeGL (i : Fin n) (B : SpecialLinearGroup (Fin 2) K) :
    ((planeGL i B : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      famMat (Pi.mulSingle i (B : Matrix (Fin 2) (Fin 2) K)) :=
  rfl

theorem planeGL_mem (i : Fin n) (B : SpecialLinearGroup (Fin 2) K) :
    planeGL i B ∈ StatedSp n K := by
  refine Subgroup.subset_closure ?_
  change (famMat (Pi.mulSingle i (B : Matrix (Fin 2) (Fin 2) K)))ᵀ * fromBlocks 0 1 (-1) 0 *
    famMat (Pi.mulSingle i (B : Matrix (Fin 2) (Fin 2) K)) = fromBlocks 0 1 (-1) 0
  refine famMat_symplectic fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same]
    exact B.2
  · rw [Pi.mulSingle_eq_of_ne hj, det_one]

@[expose] noncomputable def planeProj (i : Fin n) :
    SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSp n K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))).comp
    ((planeGL i).codRestrict (StatedSp n K) (planeGL_mem i))

theorem planeProj_neg_one_ne_one (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) :
    planeProj (K := K) (⟨0, by omega⟩ : Fin n) (-1) ≠ 1 := by
  intro h
  rw [planeProj, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := h
  have hc' : famMat (Pi.mulSingle (⟨0, by omega⟩ : Fin n)
      ((-1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) =
      scalar (Fin n ⊕ Fin n) (c : K) := by
    rw [← GeneralLinearGroup.coe_scalar, hc]
    rfl
  have h0 := congrFun₂ hc' (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)
  have h1 := congrFun₂ hc' (Sum.inl ⟨1, by omega⟩) (Sum.inl ⟨1, by omega⟩)
  have hne : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  simp only [famMat, fromBlocks_apply₁₁, diagonal_apply_eq, scalar_apply] at h0 h1
  rw [Pi.mulSingle_eq_same] at h0
  rw [Pi.mulSingle_eq_of_ne hne, one_apply_eq] at h1
  have hm : ((-1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = -1 := by
    simp
  rw [hm] at h0
  apply h2
  linear_combination h1 - h0

end SymplecticExclusion

open SymplecticExclusion

theorem dihedral_sylow_symplectic_model_exclusion {T : Type} [Group T] {n p f : ℕ}
    (hT : StatedClassicalModel T .PSp n p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
  have : Finite T := Finite.of_equiv _ eT.symm.toEquiv
  obtain ⟨hrank, hQ8⟩ :=
    SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩
  have hchar : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle := SectionRank.ClassicalOdd.le_pRank_Sp hn hK
    rw [← SectionRank.pRank_top_eq_of_mulEquiv one_lt_two eT, ←
      SectionRank.pRank_eq_open_pRank_top] at hle
    have h3 : 3 ≤ f * (n + 1) := le_trans (by omega : 3 ≤ 1 * (n + 1)) (Nat.mul_le_mul_right _ hf)
    omega
  ·
    have hkchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hkchar
    obtain ⟨H, ⟨eH⟩⟩ := exists_quaternion_of_sl2_hom hkchar
      (eT.symm.toMonoidHom.comp (planeProj (K := K) (⟨0, by omega⟩ : Fin n)))
      (by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Ne, map_eq_one_iff _ eT.symm.injective]
        exact planeProj_neg_one_ne_one h2 hn)
    exact hQ8 ⟨H, ⟨eH⟩⟩

end CFSG.ComponentClassification.UnbalancedGS
