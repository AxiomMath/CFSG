module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResSpBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerUnitaryBlocks
public import CFSG.GroupTheory.WeirSylow.Symplectic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

section Blk

variable {K : Type} [Field K] {e n : ℕ}

@[expose] def blkIdx₀ (hn : 2 * e ≤ n) : Fin e → Fin n := fun i => ⟨i, by have := i.2; omega⟩

@[expose] def blkIdx₁ (hn : 2 * e ≤ n) : Fin e → Fin n := fun i => ⟨e + i, by have := i.2; omega⟩

theorem blkIdx₀_injective (hn : 2 * e ≤ n) : Function.Injective (blkIdx₀ hn) := by
  intro i j h
  simpa [blkIdx₀, Fin.ext_iff] using h

theorem blkIdx₁_injective (hn : 2 * e ≤ n) : Function.Injective (blkIdx₁ hn) := by
  intro i j h
  simpa [blkIdx₁, Fin.ext_iff] using h

theorem blkIdx_disjoint (hn : 2 * e ≤ n) (i i' : Fin e) : blkIdx₀ hn i ≠ blkIdx₁ hn i' := by
  intro h
  have := congrArg Fin.val h
  have h2 := i.2
  simp only [blkIdx₀, blkIdx₁] at this
  omega

@[expose] noncomputable def blkSpOf {s : Fin e → Fin n} (hs : Function.Injective s) :
    StatedSp e K →* StatedSp n K :=
  ((extGL (spIncl_transpose_mul (K := K) hs)).comp (StatedSp e K).subtype).codRestrict
    (StatedSp n K) fun g => by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
      exact extMat_symplectic (spIncl_transpose_mul hs) (formJ_mul_spIncl (K := K) s)
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 g.2)

theorem coe_blkSpOf {s : Fin e → Fin n} (hs : Function.Injective s) (g : StatedSp e K) :
    (((blkSpOf hs g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      extMat (spIncl K s) ((g : GL (Fin e ⊕ Fin e) K) : Matrix (Fin e ⊕ Fin e) (Fin e ⊕ Fin e) K) :=
  rfl

theorem fieldSp_blkSpOf {s : Fin e → Fin n} (hs : Function.Injective s) (σ : K ≃+* K)
    (g : StatedSp e K) : fieldSp n K σ (blkSpOf hs g) = blkSpOf hs (fieldSp e K σ g) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_fieldSp, coe_blkSpOf, coe_blkSpOf, coe_fieldSp]
  exact extMat_map (φ := σ.toRingHom) (spIncl_map σ s) _

theorem blkSpOf_comm (hn : 2 * e ≤ n) (g h : StatedSp e K) :
    blkSpOf (K := K) (blkIdx₀_injective hn) g * blkSpOf (K := K) (blkIdx₁_injective hn) h =
      blkSpOf (K := K) (blkIdx₁_injective hn) h * blkSpOf (K := K) (blkIdx₀_injective hn) g := by
  apply Subtype.ext
  exact extGL_comm (spIncl_transpose_mul (blkIdx₀_injective hn))
    (spIncl_transpose_mul (blkIdx₁_injective hn))
    (spIncl_transpose_mul_disjoint (blkIdx_disjoint hn)) _ _

@[expose] noncomputable def blkSp2 (hn : 2 * e ≤ n) : (Fin 2 → StatedSp e K) →* StatedSp n K where
  toFun x := blkSpOf (K := K) (blkIdx₀_injective hn) (x 0) *
    blkSpOf (K := K) (blkIdx₁_injective hn) (x 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, map_mul]
    have hc := blkSpOf_comm (K := K) hn (y 0) (x 1)
    set a₀ := blkSpOf (K := K) (blkIdx₀_injective hn) (x 0)
    set b₀ := blkSpOf (K := K) (blkIdx₀_injective hn) (y 0)
    set a₁ := blkSpOf (K := K) (blkIdx₁_injective hn) (x 1)
    set b₁ := blkSpOf (K := K) (blkIdx₁_injective hn) (y 1)
    calc a₀ * b₀ * (a₁ * b₁) = a₀ * (b₀ * a₁) * b₁ := by group
      _ = a₀ * (a₁ * b₀) * b₁ := by rw [hc]
      _ = a₀ * a₁ * (b₀ * b₁) := by group

theorem blkSp2_apply (hn : 2 * e ≤ n) (x : Fin 2 → StatedSp e K) :
    blkSp2 (K := K) hn x = blkSpOf (K := K) (blkIdx₀_injective hn) (x 0) *
      blkSpOf (K := K) (blkIdx₁_injective hn) (x 1) := rfl

theorem blkSp2_retract₀ (hn : 2 * e ≤ n) (x : Fin 2 → StatedSp e K) :
    (spIncl K (blkIdx₀ hn))ᵀ *
      (((blkSp2 (K := K) hn x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * spIncl K (blkIdx₀ hn) =
      (((x 0 : StatedSp e K) : GL (Fin e ⊕ Fin e) K) : Matrix (Fin e ⊕ Fin e) (Fin e ⊕ Fin e) K) := by
  have h01 := spIncl_transpose_mul_disjoint (K := K) (blkIdx_disjoint hn)
  have h10 : (spIncl K (blkIdx₁ hn))ᵀ * spIncl K (blkIdx₀ hn) = 0 := by
    have := congrArg Matrix.transpose h01
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this
  exact extGL_retract (spIncl_transpose_mul (blkIdx₀_injective hn))
    (spIncl_transpose_mul (blkIdx₁_injective hn)) h10 _ _

theorem blkSp2_retract₁ (hn : 2 * e ≤ n) (x : Fin 2 → StatedSp e K) :
    (spIncl K (blkIdx₁ hn))ᵀ *
      (((blkSp2 (K := K) hn x : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * spIncl K (blkIdx₁ hn) =
      (((x 1 : StatedSp e K) : GL (Fin e ⊕ Fin e) K) : Matrix (Fin e ⊕ Fin e) (Fin e ⊕ Fin e) K) := by
  have h01 := spIncl_transpose_mul_disjoint (K := K) (blkIdx_disjoint hn)
  rw [blkSp2_apply, blkSpOf_comm]
  exact extGL_retract (spIncl_transpose_mul (blkIdx₁_injective hn))
    (spIncl_transpose_mul (blkIdx₀_injective hn)) h01 _ _

theorem blkSp2_injective (hn : 2 * e ≤ n) : Function.Injective (blkSp2 (K := K) hn) := by
  intro x y hxy
  funext t
  fin_cases t
  · have h1 := blkSp2_retract₀ (K := K) hn x
    rw [hxy, blkSp2_retract₀] at h1
    exact Subtype.ext (Units.ext h1.symm)
  · have h1 := blkSp2_retract₁ (K := K) hn x
    rw [hxy, blkSp2_retract₁] at h1
    exact Subtype.ext (Units.ext h1.symm)

theorem fieldSp_blkSp2 (hn : 2 * e ≤ n) (σ : K ≃+* K) (x : Fin 2 → StatedSp e K) :
    fieldSp n K σ (blkSp2 (K := K) hn x) = blkSp2 (K := K) hn (fun t => fieldSp e K σ (x t)) := by
  rw [blkSp2_apply, blkSp2_apply, map_mul, fieldSp_blkSpOf, fieldSp_blkSpOf]

theorem spScalars_sq (hn : 1 ≤ n) {y : StatedSp n K} (hy : y ∈ spScalars n K) :
    ∃ c : Kˣ, (y : GL (Fin n ⊕ Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∧
      c ^ 2 = 1 := by
  have hy' := hy
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hy'
  obtain ⟨c, hc⟩ := hy'
  refine ⟨c, hc.symm, ?_⟩
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.1 y.2
  rw [← hc] at h
  have h00 := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inr ⟨0, hn⟩)
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.fromBlocks] at h00
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
  exact h00

theorem eq_one_of_spScalars_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {y : StatedSp n K} (hy : y ∈ spScalars n K) (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨c, hc, hc2⟩ := spScalars_sq hn hy
  have hcp : c ^ p = 1 := by
    have h1 : ((y : GL (Fin n ⊕ Fin n) K)) ^ p = 1 := by
      have := congrArg Subtype.val hyp
      simpa using this
    rw [hc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl ⟨0, hn⟩)
        (Sum.inl ⟨0, hn⟩)) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc2, hcp⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [hc, hc1, map_one]
  rfl

theorem dvd_card_statedSp_of_dvd [Finite K] {p e : ℕ} (he : 1 ≤ e)
    (hpe : (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 2) ^ e - 1) : p ∣ Nat.card (StatedSp e K) := by
  have h := CFSG.GroupTheory.WeirSylow.natCard_statedSp_cast K e
  refine Int.natCast_dvd_natCast.1 ?_
  rw [h]
  exact (hpe.trans (Finset.dvd_prod_of_mem (fun j : ℕ => ((Nat.card K : ℤ) ^ 2) ^ j - 1)
    (Finset.mem_Icc.2 ⟨he, le_rfl⟩))).mul_left _

theorem exists_two_indep_fixed_sp [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e)
    (hn : 2 * e ≤ n) (hdvd : p ∣ Nat.card (StatedSp e K)) {τ : K ≃+* K} (hτ : τ ^ p = 1) :
    ∃ x₁ x₂ : StatedProj (StatedSp n K), Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      fieldAut n K τ x₁ = x₁ ∧ fieldAut n K τ x₂ = x₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgτ⟩ := exists_fixed_orderOf_eq_prime (fieldSp e K τ)
    (by rw [← map_pow, hτ, map_one]) hdvd
  have hker : ∀ y : StatedSp n K, proj n K y = 1 → y ^ p = 1 → y = 1 := fun y hy hyp =>
    eq_one_of_spScalars_of_pow_eq_one hp hp2 (by omega) ((QuotientGroup.eq_one_iff y).1 hy) hyp
  obtain ⟨hc, h0, h1, hi⟩ := two_indep_of_blockHom (blkSp2 (K := K) hn)
    (blkSp2_injective hn) (proj n K) hg hker
  refine ⟨_, _, hc, h0, h1, hi, ?_⟩
  have hfix : ∀ t : Fin 2, fieldAut n K τ (proj n K (blkSp2 (K := K) hn (Pi.mulSingle t g))) =
      proj n K (blkSp2 (K := K) hn (Pi.mulSingle t g)) := by
    intro t
    rw [fieldAut_proj, fieldSp_blkSp2]
    congr 2
    funext s
    by_cases hst : s = t
    · subst hst
      simp [hgτ]
    · simp [Pi.mulSingle_eq_of_ne hst]
  exact ⟨hfix 0, hfix 1⟩

end Blk

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
