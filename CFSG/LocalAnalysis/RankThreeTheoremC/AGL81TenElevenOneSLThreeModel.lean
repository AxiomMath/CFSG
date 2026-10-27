module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiField

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_scalar_tau (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) :
    ∃ t : slPi π 3 (p ^ f) K,
      ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = τ • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set τu := Units.mk0 τ hτ0 with hτu
  have hτu3 : (τu : K) ^ 3 = 1 := by rw [hτu, Units.val_mk0, hτ]
  exact ⟨⟨GeneralLinearGroup.scalar (Fin 3) τu, scalar_mem_slPi_of_cube hK hq hτu3⟩,
    by rw [coe_scalar_eq_smul, hτu, Units.val_mk0]⟩

theorem inf_centralizer_eq_zpowers (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {t : slPi π 3 (p ^ f) K}
    (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = τ • (1 : Matrix (Fin 3) (Fin 3) K)) :
    orderOf (e.symm t : G) = 3 ∧
      L ⊓ centralizer (L : Set G) = zpowers (e.symm t : G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htc : ∀ s : slPi π 3 (p ^ f) K, t * s = s * t := fun s => by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, ht, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun s : slPi π 3 (p ^ f) K => ((s : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0) h
    simp only [ht, Subgroup.coe_one, Units.val_one, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at this
    exact hτ1 this
  have ht3 : t ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ht, smul_pow, one_pow, hτ, one_smul,
      Subgroup.coe_one, Units.val_one]
  set z₀ : G := (e.symm t : G) with hz₀
  have hz₀L : z₀ ∈ L := (e.symm t).2
  have hz₀C : z₀ ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : e.symm t * ⟨l, hl⟩ = ⟨l, hl⟩ * e.symm t := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, htc]
    exact (congrArg Subtype.val h1).symm
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    apply ht1
    apply e.symm.injective
    rw [map_one]
    exact Subtype.ext h
  have hz₀3 : z₀ ^ 3 = 1 := by
    rw [hz₀, ← Subgroup.coe_pow, ← map_pow, ht3, map_one, Subgroup.coe_one]
  refine ⟨orderOf_eq_prime hz₀3 hz₀1, le_antisymm ?_ (zpowers_le.mpr ⟨hz₀L, hz₀C⟩)⟩
  rintro l ⟨hlL, hlC⟩
  have hcen : ∀ x ∈ slPi π 3 (p ^ f) K, (e ⟨l, hlL⟩ : GL (Fin 3) K) * x = x * e ⟨l, hlL⟩ := by
    intro x hx
    obtain ⟨m, hm⟩ := e.surjective ⟨x, hx⟩
    have h1 : (⟨l, hlL⟩ : L) * m = m * ⟨l, hlL⟩ :=
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hlC _ m.2).symm)
    have h2 := congrArg (fun s : L => ((e s : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) h1
    simp only [map_mul, Subgroup.coe_mul, hm] at h2
    exact h2
  obtain ⟨k, hk⟩ := exists_tau_pow_of_mem_center hK hq hτ hτ1 (e ⟨l, hlL⟩).2 hcen
  have hel : e ⟨l, hlL⟩ = t ^ (k : ℕ) := by
    apply Subtype.ext
    apply Units.ext
    rw [hk, Subgroup.coe_pow, Units.val_pow_eq_pow_val, ht, smul_pow, one_pow]
  have hl : l = z₀ ^ (k : ℕ) := by
    have := congrArg (fun s => (e.symm s : G)) hel
    simp only [MulEquiv.symm_apply_apply, map_pow, Subgroup.coe_pow] at this
    exact this
  rw [hl]
  exact npow_mem_zpowers _ _

theorem slAct_eq_of_mem_centralizer (e : L ≃* slPi π 3 (p ^ f) K) {c : G}
    (hc : c ∈ centralizer (L : Set G)) (s : slPi π 3 (p ^ f) K) :
    slAct e ⟨c, mem_normalizer_of_normal c⟩ s = s := by
  apply Subtype.ext
  rw [(isPGLAt_of_mem_centralizer e hc).2 s, one_mul, inv_one, mul_one]

theorem slAct_mul_comm_of_commutator (e : L ≃* slPi π 3 (p ^ f) K) {a σ : G}
    (haσ : ⁅a, σ⁆ ∈ centralizer (L : Set G)) (s : slPi π 3 (p ^ f) K) :
    slAct e ⟨a * σ, mem_normalizer_of_normal _⟩ s =
      slAct e ⟨σ * a, mem_normalizer_of_normal _⟩ s := by
  have e1 : (⟨a * σ, mem_normalizer_of_normal _⟩ : normalizer (L : Set G)) =
      ⟨⁅a, σ⁆ * (σ * a), mem_normalizer_of_normal _⟩ :=
    Subtype.ext (by rw [commutatorElement_def]; group)
  rw [e1, slAct_mul_apply, slAct_eq_of_mem_centralizer e haσ]

theorem exists_normalized_field_of_pow (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    (e : L ≃* slPi π 3 (p ^ f) K) {σ : G}
    (hσ3 : slAct e ⟨σ, mem_normalizer_of_normal σ⟩ ^ 3 = 1) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K)
    (hσg : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        g * frobGL ψ s * g⁻¹) :
    ∃ e' : L ≃* slPi π 3 (p ^ f) K, (∀ s : slPi π 3 (p ^ f) K,
      ((slAct e' ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s) ∧ ∀ (b : G) (y : GL (Fin 3) K), IsPGLAt e b y → ∃ y', IsPGLAt e' b y' := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hσ3' : ∀ A ∈ slPi π 3 (p ^ f) K,
      g * frobGL ψ (g * frobGL ψ (g * frobGL ψ A * g⁻¹) * g⁻¹) * g⁻¹ = A := by
    intro A hA
    have h1 := congrArg (fun α : MulAut (slPi π 3 (p ^ f) K) =>
      ((α ⟨A, hA⟩ : slPi π 3 (p ^ f) K) : GL (Fin 3) K)) hσ3
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hσg, hσg, hσg] at h1
    exact h1
  obtain ⟨h, hh, hconj⟩ := exists_conj_frobGL hK hq hf hφ hφ3 hψ hg hσ3'
  refine ⟨e.trans (conjSL hπ hh), fun s => ?_, fun b y hy => ⟨h⁻¹ * y * h,
    mul_mem (mul_mem (inv_mem hh) hy.1) hh, fun s => ?_⟩⟩
  swap
  · have h1 := hy.2 ((conjSL hπ hh).symm s)
    rw [slAct_apply] at h1 ⊢
    simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, coe_conjSL]
    rw [h1, coe_conjSL_symm]
    group
  have h1 := hσg ((conjSL hπ hh).symm s)
  rw [slAct_apply] at h1 ⊢
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, coe_conjSL]
  rw [h1, coe_conjSL_symm, hconj _ (conj_mem_slPi hπ hh s.2)]
  have e1 : h⁻¹ * (h * (s : GL (Fin 3) K) * h⁻¹) * h = s := by group
  rw [e1]
  group

theorem exists_fixed_lift_of_commutator (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {f₀ : ℕ} (hf : f = 3 * f₀) {φ : K ≃+* K} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀))
    (hφ3 : orderOf φ = 3) {ψ : K ≃+* K} (hψ : ψ = φ ∨ ψ = φ ^ 2)
    {e : L ≃* slPi π 3 (p ^ f) K} {σ : G}
    (hσψ : ∀ s : slPi π 3 (p ^ f) K,
      ((slAct e ⟨σ, mem_normalizer_of_normal σ⟩ s : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {a : G} (haσ : ⁅a, σ⁆ ∈ centralizer (L : Set G)) {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    ∃ y', IsPGLAt e a y' ∧ frobGL ψ y' = y' := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hψ3 := ringAut_apply_three' hφ3 hψ
  have hΨ3 : ∀ A : GL (Fin 3) K, frobGL ψ (frobGL ψ (frobGL ψ A)) = A := by
    intro A
    apply Units.ext
    rw [coe_frobGL, coe_frobGL, coe_frobGL]
    ext i k
    simp only [Matrix.map_apply, hψ3]
  have hcomm : ∀ t ∈ slPi π 3 (p ^ f) K, (y⁻¹ * frobGL ψ y) * t = t * (y⁻¹ * frobGL ψ y) := by
    intro t ht
    have hs : frobGL ψ (frobGL ψ t) ∈ slPi π 3 (p ^ f) K :=
      frobGL_mem_slPi hK ψ (frobGL_mem_slPi hK ψ ht)
    have hst : frobGL ψ (frobGL ψ (frobGL ψ t)) = t := hΨ3 t
    have h1 := congrArg (fun s : slPi π 3 (p ^ f) K => (s : GL (Fin 3) K))
      (slAct_mul_comm_of_commutator e haσ ⟨_, hs⟩).symm
    rw [slAct_mul_apply, slAct_mul_apply, hσψ, hy.2, hy.2, hσψ] at h1
    change frobGL ψ (y * frobGL ψ (frobGL ψ t) * y⁻¹) = y * frobGL ψ (frobGL ψ (frobGL ψ t)) *
      y⁻¹ at h1
    rw [map_mul, map_mul, map_inv, hst] at h1
    calc y⁻¹ * frobGL ψ y * t = y⁻¹ * (frobGL ψ y * t * (frobGL ψ y)⁻¹) * frobGL ψ y := by
          group
      _ = y⁻¹ * (y * t * y⁻¹) * frobGL ψ y := by rw [h1]
      _ = t * (y⁻¹ * frobGL ψ y) := by group
  obtain ⟨ℓ, hℓ⟩ := mem_statedScalars_of_commute hπ hq' hτ hτ1 hcomm
  have hyψ : frobGL ψ y = y * GeneralLinearGroup.scalar (Fin 3) ℓ := by rw [hℓ]; group
  have hℓT : ℓ ∈ rootsOfUnity (qSubPi π (p ^ f)) K := by
    rw [← scalar_mem_glPi_iff hK, hℓ]
    exact mul_mem (inv_mem hy.1) (frobGL_mem_glPi hK ψ hy.1)
  have s1 : frobGL ψ (frobGL ψ y) = y * GeneralLinearGroup.scalar (Fin 3) ℓ *
      GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) ℓ) := by
    rw [hyψ, map_mul, hyψ, frobGL_scalar]
  have s2 : frobGL ψ (frobGL ψ (frobGL ψ y)) = y * (GeneralLinearGroup.scalar (Fin 3) ℓ *
      GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) ℓ) *
      GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) (Units.map (ψ : K →* K) ℓ))) := by
    rw [s1, map_mul, map_mul, hyψ, frobGL_scalar, frobGL_scalar]
    group
  have hN : (ℓ : K) * ψ ℓ * ψ (ψ ℓ) = 1 := by
    have h1 : GeneralLinearGroup.scalar (Fin 3) ℓ *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) ℓ) *
        GeneralLinearGroup.scalar (Fin 3) (Units.map (ψ : K →* K) (Units.map (ψ : K →* K) ℓ)) =
          1 := by
      have := hΨ3 y
      rw [s2] at this
      exact mul_eq_left.mp this
    have h2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [Units.val_mul, ← map_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq, Units.coe_map,
      MonoidHom.coe_ofClass] at h2
    exact h2
  obtain ⟨μ, hμT, hμ⟩ := exists_frob_mul_eq hK hq hf hφ hφ3 hψ hℓT hN
  refine ⟨y * GeneralLinearGroup.scalar (Fin 3) μ,
    isPGLAt_mul_scalar hy ((scalar_mem_glPi_iff hK μ).mpr hμT), ?_⟩
  have hμu : ℓ * Units.map (ψ : K →* K) μ = μ := by
    apply Units.ext
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, mul_comm]
    exact hμ
  rw [map_mul, hyψ, frobGL_scalar, mul_assoc, ← map_mul, hμu]

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
