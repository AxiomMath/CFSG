module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUniDiag
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLinPairs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KFU (diagU diagUHom diagU_val diagU_injective det_diagU)

section Torus

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def normOneUnits (ℓ f : ℕ) (K : Type) [Field K] : Subgroup Kˣ :=
  (powMonoidHom (ℓ ^ f + 1) : Kˣ →* Kˣ).ker

theorem mem_normOneUnits {u : Kˣ} : u ∈ normOneUnits ℓ f K ↔ u ^ (ℓ ^ f + 1) = 1 :=
  MonoidHom.mem_ker

theorem bar_mul_self_of_mem (hU : UnitaryFieldData ℓ f K) {u : Kˣ} (hu : u ∈ normOneUnits ℓ f K) :
    hU.bar (u : K) * (u : K) = 1 := by
  rw [hU.bar_apply, ← pow_succ]
  have := congrArg (fun v : Kˣ => (v : K)) (mem_normOneUnits.1 hu)
  simpa using this

@[expose] def weights3Hom : (Fin 2 → Kˣ) →* (Fin 3 → Kˣ) where
  toFun := weights3
  map_one' := weights3_one
  map_mul' := weights3_mul

theorem diagU_weights3_mem_gramSU (hU : UnitaryFieldData ℓ f K) {y : Fin 2 → Kˣ}
    (hy : ∀ i, y i ∈ normOneUnits ℓ f K) :
    diagU (weights3 y) ∈ gramSU hU (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hw : ∀ i, weights3 y i ∈ normOneUnits ℓ f K := by
    intro i
    fin_cases i
    · simpa [weights3] using hy 0
    · simpa [weights3] using (normOneUnits ℓ f K).mul_mem (hy 1)
        ((normOneUnits ℓ f K).inv_mem (hy 0))
    · simpa [weights3] using (normOneUnits ℓ f K).inv_mem (hy 1)
  refine mem_gramSU.2 ⟨?_, ?_⟩
  · rw [Matrix.mul_one, diagU_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have : (fun i => hU.bar ((weights3 y i : Kˣ) : K) * ((weights3 y i : Kˣ) : K)) =
        fun _ => 1 := funext fun i => bar_mul_self_of_mem hU (hw i)
    rw [this, Matrix.diagonal_one]
  · rw [det_diagU, ← Units.coe_prod, prod_weights3, Units.val_one]

@[expose] noncomputable def diagThreeU (hU : UnitaryFieldData ℓ f K) :
    (Fin 2 → ↥(normOneUnits ℓ f K)) →* gramSU hU (1 : Matrix (Fin 3) (Fin 3) K) :=
  ((diagUHom.comp weights3Hom).comp
    (MonoidHom.compLeft (normOneUnits ℓ f K).subtype (Fin 2))).codRestrict
    (gramSU hU (1 : Matrix (Fin 3) (Fin 3) K))
    (fun x => diagU_weights3_mem_gramSU hU (fun i => (x i).2))

theorem coe_diagThreeU (hU : UnitaryFieldData ℓ f K) (x : Fin 2 → ↥(normOneUnits ℓ f K)) :
    ((diagThreeU hU x : gramSU hU (1 : Matrix (Fin 3) (Fin 3) K)) : GL (Fin 3) K) =
      diagU (weights3 fun i => ((x i : ↥(normOneUnits ℓ f K)) : Kˣ)) := rfl

theorem diagThreeU_injective (hU : UnitaryFieldData ℓ f K) : Function.Injective (diagThreeU hU) := by
  intro x y h
  have h1 : diagU (weights3 fun i => ((x i : ↥(normOneUnits ℓ f K)) : Kˣ)) =
      diagU (weights3 fun i => ((y i : ↥(normOneUnits ℓ f K)) : Kˣ)) := congrArg Subtype.val h
  have h2 := weights3_injective (diagU_injective h1)
  funext i
  exact Subtype.ext (congrFun h2 i)

theorem map_diagU_eq {n : ℕ} {τ : K ≃+* K} {w : Fin n → Kˣ}
    (hτ : ∀ i, τ ((w i : Kˣ) : K) = (w i : K)) :
    ((diagU w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map τ =
      ((diagU w : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  ext i j
  rw [diagU_val]
  by_cases hij : i = j
  · subst hij
    simp [hτ]
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem eq_one_of_mem_normOneScalars_of_pow_eq_one_of_not_dvd (hU : UnitaryFieldData ℓ f K)
    {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : 0 < n)
    {y : gramSU hU (1 : Matrix (Fin n) (Fin n) K)}
    (hy : y ∈ normOneScalars hU (gramSU hU (1 : Matrix (Fin n) (Fin n) K)) n)
    (hyp : y ^ p = 1) : y = 1 := by
  obtain ⟨c, -, hcn, hyc⟩ := hy
  have hcp : c ^ p = 1 := by
    have h1 : ((y : GL (Fin n) K)) ^ p = 1 := by
      have := congrArg Subtype.val hyp
      simpa using this
    rw [hyc, ← map_pow] at h1
    have h2 := congrArg
      (fun g : GL (Fin n) K => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ⟨0, hn⟩ ⟨0, hn⟩) h1
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext h2
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcp, hcn⟩
    rwa [hcop, pow_one] at this
  apply Subtype.ext
  rw [hyc, hc1, map_one]
  rfl

theorem tau_fixed_weights3 {τ : K ≃+* K} {y : Fin 2 → Kˣ}
    (hy : ∀ i, τ ((y i : Kˣ) : K) = (y i : K)) (i : Fin 3) :
    τ ((weights3 y i : Kˣ) : K) = (weights3 y i : K) := by
  have h0 := hy 0
  have h1 := hy 1
  fin_cases i <;> simp [weights3, h0, h1, map_mul, map_inv₀]

variable [Finite K]

theorem exists_two_indep_fixed_diag_unitary (hU : UnitaryFieldData ℓ f K) {p n : ℕ} (hp : p.Prime)
    (hn : 3 ≤ n) (hpn : ¬ p ∣ n) (hpq : p ∣ ℓ ^ f + 1) {τ : K ≃+* K} (hτ : τ ^ p = 1) :
    ∃ x₁ x₂ : primeFormP hU (idCn n K), Commute x₁ x₂ ∧ x₁ ^ p = 1 ∧ x₂ ^ p = 1 ∧
      (∀ i j : ℤ, x₁ ^ i * x₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧
      primeFormFieldHom hU (isPrimeFormGram_one' (n := n)) τ x₁ = x₁ ∧
      primeFormFieldHom hU (isPrimeFormGram_one' (n := n)) τ x₂ = x₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvdU : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hU.card]
    have h1 : ℓ ^ (2 * f) - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      rw [pow_mul']
      simpa using Nat.sq_sub_sq (ℓ ^ f) 1
    rw [h1]
    exact hpq.mul_right _
  obtain ⟨ζ, hζ, hζτ⟩ := exists_fixed_orderOf_eq_prime (unitsAut τ)
    (by rw [← map_pow, hτ, map_one]) hdvdU
  have hζτ' : τ (ζ : K) = (ζ : K) := congrArg (fun u : Kˣ => (u : K)) hζτ
  have hζM : ζ ∈ normOneUnits ℓ f K := by
    rw [mem_normOneUnits]
    exact orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hpq)
  let ζ' : ↥(normOneUnits ℓ f K) := ⟨ζ, hζM⟩
  have hζ' : orderOf ζ' = p := by
    rw [← Subgroup.orderOf_coe ζ']
    exact hζ
  let σ₁ : (Fin 3 × Fin 1) ⊕ Fin (n - 3) ≃ Fin n :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  let Φ : (Fin 2 → ↥(normOneUnits ℓ f K)) →* gramSU hU (1 : Matrix (Fin n) (Fin n) K) :=
    (blkSU hU σ₁).comp (Pi.monoidHom fun _ : Fin 1 => diagThreeU hU)
  have hΦ : Function.Injective Φ := fun x y h =>
    diagThreeU_injective hU (congrFun (blkSU_injective hU σ₁ h) 0)
  let π := QuotientGroup.mk'
    (normOneScalars hU (gramSU hU (1 : Matrix (Fin n) (Fin n) K)) n)
  have hker : ∀ y : gramSU hU (1 : Matrix (Fin n) (Fin n) K), π y = 1 → y ^ p = 1 → y = 1 :=
    fun y hy hyp => eq_one_of_mem_normOneScalars_of_pow_eq_one_of_not_dvd hU hp hpn (by omega)
      ((QuotientGroup.eq_one_iff y).1 hy) hyp
  obtain ⟨hc, h0, h1, hi⟩ := two_indep_of_blockHom Φ hΦ π hζ' hker
  have hfix : ∀ t : Fin 2, primeFormFieldSU hU (isPrimeFormGram_one' (n := n)) τ
      (Φ (Pi.mulSingle t ζ')) = Φ (Pi.mulSingle t ζ') := by
    intro t
    apply Subtype.ext
    change ((primeFormFieldSU hU (isPrimeFormGram_one' (n := n)) τ
      (blkSU hU σ₁ (fun _ : Fin 1 => diagThreeU hU (Pi.mulSingle t ζ'))) :
        gramSU hU (1 : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K) =
      ((blkSU hU σ₁ (fun _ : Fin 1 => diagThreeU hU (Pi.mulSingle t ζ')) :
        gramSU hU (1 : Matrix (Fin n) (Fin n) K)) : GL (Fin n) K)
    rw [coe_primeFormFieldSU, coe_blkSU]
    apply Units.ext
    rw [coe_glAut, coe_blkGL]
    refine (blkMat_map (τ : K →+* K) σ₁ _).trans ?_
    congr 1
    funext s
    change (((diagThreeU hU (Pi.mulSingle t ζ') : gramSU hU (1 : Matrix (Fin 3) (Fin 3) K)) :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map τ = _
    rw [coe_diagThreeU]
    refine map_diagU_eq fun i => tau_fixed_weights3 (fun j => ?_) i
    by_cases hjt : j = t
    · subst hjt
      simpa using hζτ'
    · simp [Pi.mulSingle_eq_of_ne hjt]
  have hfld : ∀ t : Fin 2, primeFormFieldHom hU (isPrimeFormGram_one' (n := n)) τ
      (π (Φ (Pi.mulSingle t ζ'))) = π (Φ (Pi.mulSingle t ζ')) := by
    intro t
    change primeFormFieldAut hU (isPrimeFormGram_one' (n := n)) τ
      ((Φ (Pi.mulSingle t ζ') : gramSU hU _) : primeFormP hU _) = _
    rw [primeFormFieldAut_mk, hfix t]
    rfl
  exact ⟨_, _, hc, h0, h1, hi, hfld 0, hfld 1⟩

end Torus

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
