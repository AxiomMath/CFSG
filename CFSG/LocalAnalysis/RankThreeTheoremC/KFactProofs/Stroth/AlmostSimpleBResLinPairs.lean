module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerUnitaryBlocks
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Blocks

variable {K : Type} [Field K] [Finite K]

theorem exists_two_indep_fixed_blocks_of_dvd {p e n : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K - 1) (he : 1 ≤ e) (hdvd : p ∣ Nat.card (GL (Fin e) K))
    (hn : 2 * e ≤ n) {τ : K ≃+* K} (hτ : τ ^ p = 1) :
    ∃ x₁ x₂ : projectiveSL n K, Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      fieldAut n K τ x₁ = x₁ ∧ fieldAut n K τ x₂ = x₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, hgτ⟩ := exists_fixed_orderOf_eq_prime
    (UnitaryHigher.glAut (ι := Fin e) (K := K) τ) (by rw [← map_pow, hτ, map_one]) hdvd
  have hdet : GeneralLinearGroup.det g = 1 := by
    have h1 : (GeneralLinearGroup.det g) ^ p = 1 := by
      rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
    have h2 : orderOf (GeneralLinearGroup.det g) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (GeneralLinearGroup.det g) ∣ Nat.card K - 1 := by
      have := orderOf_dvd_natCard (GeneralLinearGroup.det g)
      rwa [Nat.card_units] at this
    rcases (Nat.dvd_prime hp).1 h2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ h3) hpK
  let g' : SpecialLinearGroup (Fin e) K := ⟨(g : Matrix (Fin e) (Fin e) K), by
    rw [← GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  have htoGL : SpecialLinearGroup.toGL g' = g := Units.ext rfl
  have hg' : orderOf g' = p := by
    have h1 := orderOf_injective SpecialLinearGroup.toGL
      CFSG.LieType.SeitzGeneration.toGL_injective' g'
    rw [htoGL, hg] at h1
    exact h1.symm
  let σ₂ : (Fin e × Fin 2) ⊕ Fin (n - 2 * e) ≃ Fin n :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  have hn0 : 0 < n := by omega
  obtain ⟨hc, h0, h1, hi⟩ := two_indep_blocks hp hpK hn0 σ₂ hg'
  refine ⟨_, _, hc, h0, h1, hi, ?_⟩
  have hτg : SpecialLinearGroup.map τ.toRingHom g' = g' := by
    apply Subtype.ext
    have := congrArg (fun x : GL (Fin e) K => (x : Matrix (Fin e) (Fin e) K)) hgτ
    exact this
  have hmul : ∀ t : Fin 2, fieldAut n K τ (proj n K (blkSL σ₂ (Pi.mulSingle t g'))) =
      proj n K (blkSL σ₂ (Pi.mulSingle t g')) := by
    intro t
    rw [fieldAut_proj, map_blkSL]
    congr 2
    funext s
    by_cases hst : s = t
    · subst hst
      simp only [Pi.mulSingle_eq_same]
      exact hτg
    · simp [Pi.mulSingle_eq_of_ne hst]
  exact ⟨hmul 0, hmul 1⟩

end Blocks

section Diag

variable {K : Type} [Field K]

theorem eq_one_of_mem_scalars_of_pow_eq_one_of_not_dvd {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hn : 0 < n) {y : SpecialLinearGroup (Fin n) K} (hy : y ∈ scalars n K) (hyp : y ^ p = 1) :
    y = 1 := by
  obtain ⟨c, hcn, hyc⟩ := hy
  have hcp : c ^ p = 1 := by
    have h1 : ((y ^ p : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hyp]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hyc, ← map_pow] at h1
    have h2 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
    rw [scalar_apply, diagonal_apply_eq, one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcp, hcn⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [hyc, hc1]
  simp

@[expose] def weights3 (x : Fin 2 → Kˣ) : Fin 3 → Kˣ := ![x 0, x 1 * (x 0)⁻¹, (x 1)⁻¹]

theorem prod_weights3 (x : Fin 2 → Kˣ) : ∏ i, weights3 x i = 1 := by
  rw [Fin.prod_univ_three]
  simp only [weights3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [mul_comm (x 1) (x 0)⁻¹, ← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel]

theorem weights3_one : weights3 (1 : Fin 2 → Kˣ) = 1 := by
  funext i
  fin_cases i <;> simp [weights3]

theorem weights3_mul (x y : Fin 2 → Kˣ) : weights3 (x * y) = weights3 x * weights3 y := by
  funext i
  fin_cases i <;> simp [weights3, mul_inv, mul_comm, mul_left_comm, mul_assoc]

@[expose] noncomputable def diagThree : (Fin 2 → Kˣ) →* SpecialLinearGroup (Fin 3) K where
  toFun x := CFSG.LieType.SeitzGeneration.diagSLn (weights3 x) (prod_weights3 x)
  map_one' := CFSG.LieType.SeitzGeneration.toGL_injective' (by
    rw [CFSG.LieType.SeitzGeneration.toGL_diagSLn, map_one, weights3_one,
      CFSG.RankThree.PartOne.KFU.diagU_one])
  map_mul' x y := CFSG.LieType.SeitzGeneration.toGL_injective' (by
    rw [map_mul, CFSG.LieType.SeitzGeneration.toGL_diagSLn,
      CFSG.LieType.SeitzGeneration.toGL_diagSLn, CFSG.LieType.SeitzGeneration.toGL_diagSLn,
      weights3_mul, CFSG.RankThree.PartOne.KFU.diagU_mul])

theorem weights3_injective : Function.Injective (weights3 (K := K)) := by
  intro x y h
  have e0 : x 0 = y 0 := by simpa [weights3] using congrFun h 0
  have e1' : x 1 * (x 0)⁻¹ = y 1 * (y 0)⁻¹ := by simpa [weights3] using congrFun h 1
  have e1 : x 1 = y 1 := by
    rw [e0] at e1'
    exact mul_right_cancel e1'
  funext i
  fin_cases i
  · exact e0
  · exact e1

theorem diagThree_injective : Function.Injective (diagThree (K := K)) := by
  intro x y h
  refine weights3_injective (CFSG.RankThree.PartOne.KFU.diagU_injective (K := K) ?_)
  have := congrArg Matrix.SpecialLinearGroup.toGL h
  simpa [diagThree, CFSG.LieType.SeitzGeneration.toGL_diagSLn] using this

theorem map_diagSLn {n : ℕ} {τ : K ≃+* K} {w : Fin n → Kˣ} (hw : ∏ i, w i = 1)
    (hτ : ∀ i, τ ((w i : Kˣ) : K) = (w i : K)) :
    SpecialLinearGroup.map τ.toRingHom (CFSG.LieType.SeitzGeneration.diagSLn w hw) =
      CFSG.LieType.SeitzGeneration.diagSLn w hw := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  change τ (Matrix.diagonal (fun i => ((w i : Kˣ) : K)) i j) = Matrix.diagonal _ i j
  by_cases hij : i = j
  · subst hij
    simp [hτ]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem map_diagThree {τ : K ≃+* K} {x : Fin 2 → Kˣ}
    (hx : ∀ i, τ ((x i : Kˣ) : K) = (x i : K)) :
    SpecialLinearGroup.map τ.toRingHom (diagThree x) = diagThree x := by
  refine map_diagSLn (prod_weights3 x) fun i => ?_
  have h0 := hx 0
  have h1 := hx 1
  fin_cases i <;> simp [weights3, h0, h1, map_mul, map_inv₀]

@[expose] noncomputable def unitsAut : (K ≃+* K) →* MulAut Kˣ where
  toFun τ := Units.mapEquiv τ.toMulEquiv
  map_one' := by
    ext u
    simp
  map_mul' τ σ := by
    ext u
    simp

variable [Finite K]

theorem exists_two_indep_fixed_diag {p n : ℕ} (hp : p.Prime) (hn : 3 ≤ n) (hpn : ¬ p ∣ n)
    (hpK : p ∣ Nat.card K - 1) {τ : K ≃+* K} (hτ : τ ^ p = 1) :
    ∃ x₁ x₂ : projectiveSL n K, Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      fieldAut n K τ x₁ = x₁ ∧ fieldAut n K τ x₂ = x₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ, hζτ⟩ := exists_fixed_orderOf_eq_prime (unitsAut τ)
    (by rw [← map_pow, hτ, map_one]) (by rwa [Nat.card_units])
  have hζτ' : τ (ζ : K) = (ζ : K) := by
    have := congrArg (fun u : Kˣ => (u : K)) hζτ
    exact this
  let σ₁ : (Fin 3 × Fin 1) ⊕ Fin (n - 3) ≃ Fin n :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  let Φ : (Fin 2 → Kˣ) →* SpecialLinearGroup (Fin n) K :=
    (blkSL σ₁).comp (Pi.monoidHom fun _ : Fin 1 => diagThree)
  have hΦ : Function.Injective Φ := by
    intro x y h
    have h1 := blkSL_injective σ₁ h
    exact diagThree_injective (congrFun h1 0)
  have hker : ∀ y : SpecialLinearGroup (Fin n) K, proj n K y = 1 → y ^ p = 1 → y = 1 :=
    fun y hy hyp => eq_one_of_mem_scalars_of_pow_eq_one_of_not_dvd hp hpn (by omega)
      (proj_eq_one_iff.1 hy) hyp
  obtain ⟨hc, h0, h1, hi⟩ := two_indep_of_blockHom Φ hΦ (proj n K) hζ hker
  refine ⟨_, _, hc, h0, h1, hi, ?_⟩
  have hfix : ∀ t : Fin 2, fieldAut n K τ (proj n K (Φ (Pi.mulSingle t ζ))) =
      proj n K (Φ (Pi.mulSingle t ζ)) := by
    intro t
    rw [fieldAut_proj]
    congr 1
    change SpecialLinearGroup.map τ.toRingHom
      (blkSL σ₁ (fun _ : Fin 1 => diagThree (Pi.mulSingle t ζ))) =
        blkSL σ₁ (fun _ : Fin 1 => diagThree (Pi.mulSingle t ζ))
    rw [map_blkSL]
    congr 1
    funext _
    refine map_diagThree fun i => ?_
    by_cases hit : i = t
    · subst hit
      simpa using hζτ'
    · simp [Pi.mulSingle_eq_of_ne hit]
  exact ⟨hfix 0, hfix 1⟩

end Diag

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
