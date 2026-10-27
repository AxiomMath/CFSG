module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneTypeThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open Subgroup CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ}

theorem exists_w_of_irred (hK : PiField true p f K) (hq : ModThree true (p ^ f)) {f₀ : ℕ}
    (hf : f = 3 * f₀) (hq₀ : ModThree true (p ^ f₀)) {φ : K ≃+* K}
    (hφ : ∀ c, φ c = c ^ piCard true (p ^ f₀)) (hφ3 : orderOf φ = 3) {ψ : K ≃+* K}
    (hψ : ψ = φ ∨ ψ = φ ^ 2) (e : L ≃* slPi true 3 (p ^ f) K) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {t : slPi true 3 (p ^ f) K}
    (ht : ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = τ • (1 : Matrix (Fin 3) (Fin 3) K))
    {a : G} (ha3 : a ^ 3 = 1) (haLC : a ∉ L ⊔ centralizer (L : Set G))
    (haψ : ∀ s : slPi true 3 (p ^ f) K,
      ((slAct e ⟨a, mem_normalizer_of_normal a⟩ s : slPi true 3 (p ^ f) K) : GL (Fin 3) K) =
        frobGL ψ s)
    {x : G} (hx3 : x ^ 3 = 1) {y : GL (Fin 3) K} (hy : IsPGLAt e x y) {ℓ : K}
    (hℓ : ∀ μ : K, μ ^ 3 ≠ ℓ) (hyℓ : (y : Matrix (Fin 3) (Fin 3) K) ^ 3 = ℓ • 1) :
    ∃ w : G, w * x = x * w ∧ w ^ 3 = 1 ∧ w ∉ zpowers x ⊔ zpowers (e.symm t : G) := by
  have hπ : true = false → UnitaryFieldData p f K := fun h => absurd h (by decide)
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨hzo, hLC⟩ := inf_centralizer_eq_zpowers hK hq e hτ hτ1 ht
  set z : G := (e.symm t : G) with hz
  have htS : (t : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_eq_smul ht hτ0
  have hxLC : x ∉ L ⊔ centralizer (L : Set G) := by
    intro hx
    obtain ⟨Y, hYL, hY⟩ := exists_isPGLAt_of_mem_sup hπ e hx
    obtain ⟨s, hs⟩ := isPGLAt_inv_mul_mem hK hq hy hY
    have hYy : Y = y * GeneralLinearGroup.scalar (Fin 3) s := by rw [hs]; group
    have hdet := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) hYy
    simp only [Units.val_mul, det_mul, det_scalar_three] at hdet
    rw [(mem_slPi_true _).mp hYL, det_eq_of_cube hℓ hyℓ] at hdet
    apply hℓ ((s⁻¹ : Kˣ) : K)
    have hs0 : (s : K) ≠ 0 := s.ne_zero
    rw [Units.val_inv_eq_inv_val, inv_pow]
    field_simp
    rw [mul_comm]
    exact hdet
  have hCLx : ∀ k ∈ L, k * x = x * k → IsPGroup 3 (zpowers k) → k ∈ zpowers z := by
    intro k hkL hkx hkp
    obtain ⟨n, hn⟩ := hkp ⟨k, mem_zpowers k⟩
    have hkn : (⟨k, hkL⟩ : L) ^ 3 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    have h2 : slAct e ⟨x, mem_normalizer_of_normal x⟩ (e ⟨k, hkL⟩) = e ⟨k, hkL⟩ := by
      rw [slAct_apply, MulEquiv.symm_apply_apply]
      congr 1
      apply Subtype.ext
      rw [coe_normalizerMonoidHom]
      change x * k * x⁻¹ = k
      rw [← hkx]
      group
    have h1 := hy.2 (e ⟨k, hkL⟩)
    rw [h2] at h1
    have hKy : ((e ⟨k, hkL⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K) * y =
        y * (e ⟨k, hkL⟩ : slPi true 3 (p ^ f) K) := by
      calc _ = y * ((e ⟨k, hkL⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K) * y⁻¹ * y := by
            rw [← h1]
        _ = _ := by group
    have hKn : ((e ⟨k, hkL⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K) ^ 3 ^ n = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hkn, map_one, Subgroup.coe_one]
    have hto : orderOf (t : GL (Fin 3) K) = 3 := by
      rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e.symm, ← Subgroup.orderOf_coe]
      exact hzo
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (mem_zpowers_of_commute_irred hK hq hℓ hyℓ t.2
      (commute_of_mem_statedScalars htS y).symm hto (e ⟨k, hkL⟩).2 hKy hKn)
    have hkt : e ⟨k, hkL⟩ = t ^ j := Subtype.ext (by rw [Subgroup.coe_zpow, hj])
    have := congrArg (fun s => (e.symm s : G)) hkt
    simp only [MulEquiv.symm_apply_apply, map_zpow, Subgroup.coe_zpow] at this
    exact mem_zpowers_iff.2 ⟨j, this.symm⟩
  obtain ⟨W, hWdet, hW3, hWy⟩ := exists_w_linear hτ hτ1 hℓ hyℓ
  have hWL : W ∈ slPi true 3 (p ^ f) K := (mem_slPi_true _).mpr hWdet
  have hcomm : slAct e ⟨x, mem_normalizer_of_normal x⟩ ⟨W, hWL⟩ * (⟨W, hWL⟩)⁻¹ = t ^ 2 := by
    apply Subtype.ext
    apply Units.ext
    have hWy' : (y : Matrix (Fin 3) (Fin 3) K) * W =
        τ ^ 2 • ((W : Matrix (Fin 3) (Fin 3) K) * y) := by
      rw [hWy, smul_smul, ← pow_succ, hτ, one_smul]
    have hyy : (y : Matrix (Fin 3) (Fin 3) K) *
        ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hWW : (W : Matrix (Fin 3) (Fin 3) K) *
        ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hy.2, Units.val_mul, Units.val_mul, Units.val_mul,
      Subgroup.coe_pow, Units.val_pow_eq_pow_val, ht, smul_pow, one_pow]
    change (y : Matrix (Fin 3) (Fin 3) K) * W *
      ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((W⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [hWy', Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc
      (W : Matrix (Fin 3) (Fin 3) K), hyy, Matrix.mul_one, hWW]
  have hxh : ⁅x, (e.symm ⟨W, hWL⟩ : G)⁆ = z ^ 2 := by
    have h1 := congrArg (fun s => (e.symm s : G)) hcomm
    simp only [map_mul, map_inv, map_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_pow, slAct_apply, MulEquiv.symm_apply_apply, coe_normalizerMonoidHom] at h1
    rw [commutatorElement_def, ← h1]
  have hxh1 : ⁅x, (e.symm ⟨W, hWL⟩ : G)⁆ ≠ 1 := by
    rw [hxh]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hzo]; norm_num)
  have hh3 : (e.symm ⟨W, hWL⟩ : G) ^ 3 = 1 := by
    have : (⟨W, hWL⟩ : slPi true 3 (p ^ f) K) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hW3)
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hfx : ∃ l ∈ L, ⁅l⁻¹ * a, x⁆ ∈ centralizer (L : Set G) := by
    obtain ⟨r, hr, hψr⟩ := exists_pow_mod_three hq₀ hφ hψ
    obtain ⟨m, hmL, hm⟩ := exists_slThree_frob_conj hK hq hr hψr hℓ hyℓ
    have hl : IsPGLAt e (e.symm ⟨m, hmL⟩ : G) m := by
      simpa using isPGLAt_of_mem e hπ (e.symm ⟨m, hmL⟩).2
    refine ⟨(e.symm ⟨m, hmL⟩ : G), (e.symm _).2, ?_⟩
    have e1 : ⁅(e.symm ⟨m, hmL⟩ : G)⁻¹ * a, x⁆ =
        (e.symm ⟨m, hmL⟩ : G)⁻¹ * (a * x * a⁻¹) * (e.symm ⟨m, hmL⟩ : G) * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e1]
    exact mem_centralizer_of_isPGLAt_scalar (isPGLAt_mul e (isPGLAt_mul e (isPGLAt_mul e
      (isPGLAt_inv hπ hl) (isPGLAt_conj_of_frob e haψ hy)) hl) (isPGLAt_inv hπ hy)) hm
  have hF1 : ∀ f₁ : G, IsPGroup 3 (zpowers f₁) → f₁ * a⁻¹ ∈ L →
      ⁅f₁, x⁆ ∈ centralizer (L : Set G) → f₁ ^ 3 ∈ centralizer (L : Set G) → False := by
    intro f₁ _ hf₁a hf₁x hf₁3
    have hσ3 : slAct e ⟨f₁, mem_normalizer_of_normal f₁⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨f₁, mem_normalizer_of_normal f₁⟩ : normalizer (L : Set G)) ^ 3 =
          ⟨f₁ ^ 3, mem_normalizer_of_normal _⟩ := Subtype.ext (by rw [Subgroup.coe_pow])
      rw [this]
      exact MulEquiv.ext fun s => slAct_eq_of_mem_centralizer e hf₁3 s
    have hσg : ∀ s : slPi true 3 (p ^ f) K,
        ((slAct e ⟨f₁, mem_normalizer_of_normal f₁⟩ s : slPi true 3 (p ^ f) K) :
          GL (Fin 3) K) =
        (e ⟨f₁ * a⁻¹, hf₁a⟩ : GL (Fin 3) K) * frobGL ψ s *
          ((e ⟨f₁ * a⁻¹, hf₁a⟩ : slPi true 3 (p ^ f) K) : GL (Fin 3) K)⁻¹ := by
      intro s
      have e1 : (⟨f₁, mem_normalizer_of_normal f₁⟩ : normalizer (L : Set G)) =
          ⟨f₁ * a⁻¹ * a, mem_normalizer_of_normal _⟩ := Subtype.ext (by group)
      rw [e1, slAct_mul_apply, (isPGLAt_of_mem e hπ hf₁a).2, haψ]
    obtain ⟨e₁, he₁, htr⟩ := exists_normalized_field_of_pow hK hq hf hφ hφ3 hψ e hσ3
      (mem_glPi_true _ _) hσg
    obtain ⟨y₁, hy₁⟩ := htr x y hy
    have hxf : ⁅x, f₁⁆ ∈ centralizer (L : Set G) := by
      have := inv_mem hf₁x
      rwa [commutatorElement_inv] at this
    obtain ⟨y', hy', hy'ψ⟩ := exists_fixed_lift_of_commutator hK hq hf hφ hφ3 hψ he₁ hxf hy₁
    exact hxLC (mem_sup_centralizer_of_fixed hK hq hf hφ hφ3 hψ hy' hy'ψ)
  exact exists_commute_of_typeThree hzo hLC hx3 hxLC hCLx (e.symm _).2 hh3
    (hxh ▸ npow_mem_zpowers z 2) hxh1 ha3 haLC hfx hF1

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
