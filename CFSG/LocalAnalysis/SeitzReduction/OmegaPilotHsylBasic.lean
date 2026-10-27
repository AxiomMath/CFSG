module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a b a₂ b₂ a₃ b₃ : Fin d}

theorem IsHypCoord.eichler_apply_left (h : IsHypCoord Q a b) {u w : Fin d → K}
    (hu : u ∈ perpSub K a b) (hw : w ∈ perpSub K a b) :
    eichler Q u w (Pi.single a 1) = Pi.single a 1 :=
  (h.eichler_mem_stabSub hu hw).1

theorem IsHypCoord.eichler_apply_right (h : IsHypCoord Q a b) {u w : Fin d → K}
    (hu : u ∈ perpSub K a b) (hw : w ∈ perpSub K a b) :
    eichler Q u w (Pi.single b 1) = Pi.single b 1 :=
  (h.eichler_mem_stabSub hu hw).2

theorem IsHypCoord.polar_perpPart_left (h : IsHypCoord Q a b) (y : Fin d → K) {y' : Fin d → K}
    (hy' : y' ∈ perpSub K a b) : polar Q (perpPart a b y) y' = polar Q y y' := by
  rw [perpPart, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, h.polar_left,
    h.polar_right, hy'.1, hy'.2, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, sub_zero, sub_zero]

theorem eq_planePart_of_forall_eichler_fix (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    {y : Fin d → K}
    (hye : ∀ w ∈ perpSub K a b, polar Q (Pi.single a₂ 1) w = 0 →
      eichler Q (Pi.single a₂ 1) w y = y)
    (hyf : ∀ w ∈ perpSub K a b, polar Q (Pi.single b₂ 1) w = 0 →
      eichler Q (Pi.single b₂ 1) w y = y) :
    y = y a • Pi.single a 1 + y b • Pi.single b 1 := by
  have hperp := polar_eq_zero_of_forall_eichler_apply_eq_two (U := perpSub K a b)
    (P := h₂.hypPair) (P' := h₃.hypPair) (h₂.orth h₃ d₂₃) (h₂.hypPair_mem_perpSub d₂).2
    (h₃.hypPair_mem_perpSub d₃).1 hye hyf
  have h0 : perpPart a b y = 0 := by
    refine h.polarNondegOn_perpSub hQ _ (perpPart_mem h.ne y) fun y' hy' => ?_
    rw [h.polar_perpPart_left y hy']
    exact hperp y' hy'
  conv_lhs => rw [eq_add_perpPart a b y, h0, add_zero]

theorem eq_smul_on_perpSub_of_commute (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    {φ : (Fin d → K) ≃+ (Fin d → K)} {σ : K ≃+* K} {μ : K} (hμ : μ ≠ 0)
    (hφs : ∀ (c : K) x, φ (c • x) = σ c • φ x) (hφQ : ∀ x, Q (φ x) = μ * σ (Q x))
    (hDe : ∀ w ∈ perpSub K a b, polar Q (Pi.single a₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single a₂ 1) w x) = eichler Q (Pi.single a₂ 1) w (φ x))
    (hDf : ∀ w ∈ perpSub K a b, polar Q (Pi.single b₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single b₂ 1) w x) = eichler Q (Pi.single b₂ 1) w (φ x)) :
    (∀ c, σ c = c) ∧ (∃ γ : K, γ ≠ 0 ∧ ∀ x ∈ perpSub K a b, φ x = γ • x) ∧
      φ (Pi.single a 1) =
        φ (Pi.single a 1) a • Pi.single a 1 + φ (Pi.single a 1) b • Pi.single b 1 ∧
      φ (Pi.single b 1) =
        φ (Pi.single b 1) a • Pi.single a 1 + φ (Pi.single b 1) b • Pi.single b 1 := by
  have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a b ∧
      (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a b := h₂.hypPair_mem_perpSub d₂
  have hu₃ : (Pi.single a₃ 1 : Fin d → K) ∈ perpSub K a b ∧
      (Pi.single b₃ 1 : Fin d → K) ∈ perpSub K a b := h₃.hypPair_mem_perpSub d₃
  have key : ∀ ψ : (Fin d → K) ≃+ (Fin d → K),
      (∀ w ∈ perpSub K a b, polar Q (Pi.single a₂ 1) w = 0 → ∀ x,
        ψ (eichler Q (Pi.single a₂ 1) w x) = eichler Q (Pi.single a₂ 1) w (ψ x)) →
      (∀ w ∈ perpSub K a b, polar Q (Pi.single b₂ 1) w = 0 → ∀ x,
        ψ (eichler Q (Pi.single b₂ 1) w x) = eichler Q (Pi.single b₂ 1) w (ψ x)) →
      ∀ v, (∀ u w, u ∈ perpSub K a b → w ∈ perpSub K a b → eichler Q u w v = v) →
        ψ v = ψ v a • Pi.single a 1 + ψ v b • Pi.single b 1 := by
    intro ψ hψe hψf v hv
    exact eq_planePart_of_forall_eichler_fix hQ h h₂ h₃ d₂ d₃ d₂₃
      (fun w hw hw' => by rw [← hψe w hw hw' v, hv _ _ hu₂.1 hw])
      (fun w hw hw' => by rw [← hψf w hw hw' v, hv _ _ hu₂.2 hw])
  have hsymm : ∀ (u : Fin d → K), (∀ w ∈ perpSub K a b, polar Q u w = 0 → ∀ x,
      φ (eichler Q u w x) = eichler Q u w (φ x)) → ∀ w ∈ perpSub K a b, polar Q u w = 0 → ∀ x,
      φ.symm (eichler Q u w x) = eichler Q u w (φ.symm x) := by
    intro u hu w hw hw' x
    apply φ.injective
    rw [hu w hw hw', AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hea := key φ hDe hDf _ fun u w hu hw => h.eichler_apply_left hu hw
  have heb := key φ hDe hDf _ fun u w hu hw => h.eichler_apply_right hu hw
  have hea' := key φ.symm (hsymm _ hDe) (hsymm _ hDf) _ fun u w hu hw => h.eichler_apply_left hu hw
  have heb' := key φ.symm (hsymm _ hDe) (hsymm _ hDf) _ fun u w hu hw =>
    h.eichler_apply_right hu hw
  have hpol := polar_map_of_semisim (φ := φ) (σ := σ) hφQ
  have hWU : ∀ (s t : K) {x : Fin d → K}, x ∈ perpSub K a b →
      polar Q (s • Pi.single a 1 + t • Pi.single b 1) x = 0 := by
    intro s t x hx
    rw [polar_add_left, polar_smul_left, polar_smul_left, h.polar_left, h.polar_right, hx.1, hx.2,
      smul_eq_mul, smul_eq_mul, mul_zero, mul_zero, add_zero]
  have hφU : ∀ x ∈ perpSub K a b, φ x ∈ perpSub K a b := by
    intro x hx
    constructor
    · rw [← h.polar_right (φ x), ← AddEquiv.apply_symm_apply φ (Pi.single b 1), hpol, heb',
        hWU _ _ hx, map_zero, mul_zero]
    · rw [← h.polar_left (φ x), ← AddEquiv.apply_symm_apply φ (Pi.single a 1), hpol, hea',
        hWU _ _ hx, map_zero, mul_zero]
  obtain ⟨hσ, γ, hγ0, hφγ⟩ := eq_smul_of_commute_of_commute (h.polarNondegOn_perpSub hQ)
    (h₂.orth h₃ d₂₃) hu₂.1 hu₂.2 hu₃.1 hu₃.2 hμ hφs hφQ hφU
    (fun w hw hw' x _ => hDe w hw hw' x) (fun w hw hw' x _ => hDf w hw hw' x)
  exact ⟨hσ, ⟨γ, hγ0, hφγ⟩, hea, heb⟩

theorem eq_smul_torusLin_of_commute [CharP K 2] (hQ : (polarBilin Q).Nondegenerate)
    (h : IsHypCoord Q a b) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a b a₂ b₂) (d₃ : PairDisjoint a b a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    {φ : (Fin d → K) ≃+ (Fin d → K)} {σ : K ≃+* K} {μ : K} (hμ : μ ≠ 0)
    (hφs : ∀ (c : K) x, φ (c • x) = σ c • φ x) (hφQ : ∀ x, Q (φ x) = μ * σ (Q x))
    (hDe : ∀ w ∈ perpSub K a b, polar Q (Pi.single a₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single a₂ 1) w x) = eichler Q (Pi.single a₂ 1) w (φ x))
    (hDf : ∀ w ∈ perpSub K a b, polar Q (Pi.single b₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single b₂ 1) w x) = eichler Q (Pi.single b₂ 1) w (φ x))
    {c₀ : Kˣ} (hc₀ : c₀ ≠ 1) (hX : ∀ x, φ (torusLin a b c₀ x) = torusLin a b c₀ (φ x)) :
    (∀ c, σ c = c) ∧ ∃ (γ : K) (α : Kˣ), γ ≠ 0 ∧ ∀ x, φ x = γ • torusLin a b α x := by
  obtain ⟨hσ, ⟨γ, hγ0, hφγ⟩, hea, heb⟩ :=
    eq_smul_on_perpSub_of_commute hQ h h₂ h₃ d₂ d₃ d₂₃ hμ hφs hφQ hDe hDf
  have hφl : ∀ (c : K) x, φ (c • x) = c • φ x := fun c x => by rw [hφs, hσ]
  have hne : ((c₀⁻¹ : Kˣ) : K) ≠ c₀ := units_inv_ne_self hc₀
  have hab : φ (Pi.single a 1) b = 0 := by
    have h1 := congrFun (hX (Pi.single a 1)) b
    rw [torusLin_single_left h.ne, hφl, torusLin_apply_right h.ne, Pi.smul_apply,
      smul_eq_mul] at h1
    have : ((c₀ : K) - ((c₀⁻¹ : Kˣ) : K)) * φ (Pi.single a 1) b = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)
  have hba : φ (Pi.single b 1) a = 0 := by
    have h1 := congrFun (hX (Pi.single b 1)) a
    rw [torusLin_single_right h.ne, hφl, torusLin_apply_left, Pi.smul_apply, smul_eq_mul] at h1
    have : (((c₀⁻¹ : Kˣ) : K) - c₀) * φ (Pi.single b 1) a = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  set s := φ (Pi.single a 1) a with hs
  set s' := φ (Pi.single b 1) b with hs'
  rw [hab, zero_smul, add_zero] at hea
  rw [hba, zero_smul, zero_add] at heb
  have hpol := polar_map_of_semisim (φ := φ) (σ := σ) hφQ
  have hss' : s * s' = μ := by
    have h1 := hpol (Pi.single a 1) (Pi.single b 1)
    rw [hea, heb, polar_smul_left, polar_smul_right, h.polar_left] at h1
    simpa only [Pi.single_eq_same, map_one, smul_eq_mul, mul_one] using h1
  have hμγ : μ = γ * γ := by
    have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a b ∧
        (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a b := h₂.hypPair_mem_perpSub d₂
    have hQx : Q (Pi.single a₂ 1 + Pi.single b₂ 1) = 1 := h₂.map_single_add
    have h1 := hφQ (Pi.single a₂ 1 + Pi.single b₂ 1)
    rw [hφγ _ ((perpSub K a b).add_mem hu₂.1 hu₂.2), map_smul_eq_sq, hQx, map_one] at h1
    linear_combination -h1
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_mul, hμγ] at hss'
    exact hγ0 (mul_self_eq_zero.mp hss'.symm)
  refine ⟨hσ, γ, Units.mk0 (s / γ) (div_ne_zero hs0 hγ0), hγ0, fun x => ?_⟩
  have hs'eq : s' = γ * γ / s := by
    field_simp
    linear_combination hss' + hμγ
  have hinv : ((Units.mk0 (s / γ) (div_ne_zero hs0 hγ0))⁻¹ : Kˣ) = Units.mk0 (γ / s)
      (div_ne_zero hγ0 hs0) := by
    ext
    simp
  have hp := perpPart_mem h.ne x
  have hφx : φ x = x a • (s • Pi.single a 1) + x b • (s' • Pi.single b 1) +
      γ • perpPart a b x := by
    conv_lhs => rw [eq_add_perpPart a b x]
    rw [map_add, map_add, hφl, hφl, hea, heb, hφγ _ hp]
  have htx : ∀ α : Kˣ, torusLin a b α x = x a • ((α : K) • Pi.single a 1) +
      x b • (((α⁻¹ : Kˣ) : K) • Pi.single b 1) + perpPart a b x := by
    intro α
    conv_lhs => rw [eq_add_perpPart a b x]
    rw [map_add, map_add, map_smul, map_smul, torusLin_single_left h.ne,
      torusLin_single_right h.ne, torusLin_eq_self_of hp.1 hp.2]
  rw [hφx, htx, hinv, Units.val_mk0, Units.val_mk0, hs'eq]
  match_scalars <;> field_simp

end CFSG.SeitzReduction.OmegaPilot
