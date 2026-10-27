module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAutUBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoTorus

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Aut

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' a₂ b₂ a₃ b₃ : Fin d}
  {b c : K}

theorem IsAnisoCoord.polar_perpPart_left (h : IsAnisoCoord Q a a' b c) (y : Fin d → K)
    {y' : Fin d → K} (hy' : y' ∈ perpSub K a a') : polar Q (perpPart a a' y) y' = polar Q y y' := by
  rw [perpPart, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, h.polar_left,
    h.polar_right, hy'.1, hy'.2, smul_eq_mul, smul_eq_mul, mul_zero, mul_zero]
  simp

theorem IsAnisoCoord.polarNondegOn_perpSub (hQ : (polarBilin Q).Nondegenerate)
    (h : IsAnisoCoord Q a a' b c) : PolarNondegOn Q (perpSub K a a') := by
  intro x hx hxU
  apply eq_zero_of_polar_eq_zero hQ
  intro y
  have hy := hxU _ (perpPart_mem h.ne y)
  have e : polar Q x y = polar Q x (perpPart a a' y) + y a * polar Q (Pi.single a 1) x +
      y a' * polar Q (Pi.single a' 1) x := by
    conv_lhs => rw [eq_add_perpPart a a' y]
    rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
      polar_comm Q x (Pi.single a 1), polar_comm Q x (Pi.single a' 1), smul_eq_mul, smul_eq_mul]
    ring
  rw [e, hy, h.polar_left, h.polar_right, hx.1, hx.2]
  ring

theorem IsAnisoCoord.eichler_mem_stabSub (h : IsAnisoCoord Q a a' b c) {u w : Fin d → K}
    (hu : u ∈ perpSub K a a') (hw : w ∈ perpSub K a a') : eichler Q u w ∈ stabSub a a' :=
  ⟨eichler_apply_of_polar_eq_zero (by rw [h.polar_left, hu.2, mul_zero])
      (by rw [h.polar_left, hw.2, mul_zero]),
    eichler_apply_of_polar_eq_zero (by rw [h.polar_right, hu.1, mul_zero])
      (by rw [h.polar_right, hw.1, mul_zero])⟩

theorem IsAnisoCoord.eq_planePart_of_forall_eichler_fix (hQ : (polarBilin Q).Nondegenerate)
    (h : IsAnisoCoord Q a a' b c) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a a' a₂ b₂) (d₃ : PairDisjoint a a' a₃ b₃)
    (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃) {y : Fin d → K}
    (hye : ∀ w ∈ perpSub K a a', polar Q (Pi.single a₂ 1) w = 0 →
      eichler Q (Pi.single a₂ 1) w y = y)
    (hyf : ∀ w ∈ perpSub K a a', polar Q (Pi.single b₂ 1) w = 0 →
      eichler Q (Pi.single b₂ 1) w y = y) :
    y = y a • Pi.single a 1 + y a' • Pi.single a' 1 := by
  have hperp := polar_eq_zero_of_forall_eichler_apply_eq_two (U := perpSub K a a')
    (P := h₂.hypPair) (P' := h₃.hypPair) (h₂.orth h₃ d₂₃) (h₂.hypPair_mem_perpSub d₂).2
    (h₃.hypPair_mem_perpSub d₃).1 hye hyf
  have h0 : perpPart a a' y = 0 := by
    refine h.polarNondegOn_perpSub hQ _ (perpPart_mem h.ne y) fun y' hy' => ?_
    rw [h.polar_perpPart_left y hy']
    exact hperp y' hy'
  conv_lhs => rw [eq_add_perpPart a a' y, h0, add_zero]

theorem IsAnisoCoord.eq_smul_on_perpSub_of_commute (hQ : (polarBilin Q).Nondegenerate)
    (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0) (h₂ : IsHypCoord Q a₂ b₂)
    (h₃ : IsHypCoord Q a₃ b₃) (d₂ : PairDisjoint a a' a₂ b₂) (d₃ : PairDisjoint a a' a₃ b₃)
    (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    {φ : (Fin d → K) ≃+ (Fin d → K)} {σ : K ≃+* K} {μ : K} (hμ : μ ≠ 0)
    (hφs : ∀ (c : K) x, φ (c • x) = σ c • φ x) (hφQ : ∀ x, Q (φ x) = μ * σ (Q x))
    (hDe : ∀ w ∈ perpSub K a a', polar Q (Pi.single a₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single a₂ 1) w x) = eichler Q (Pi.single a₂ 1) w (φ x))
    (hDf : ∀ w ∈ perpSub K a a', polar Q (Pi.single b₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single b₂ 1) w x) = eichler Q (Pi.single b₂ 1) w (φ x)) :
    (∀ c, σ c = c) ∧ (∃ γ : K, γ ≠ 0 ∧ ∀ x ∈ perpSub K a a', φ x = γ • x) ∧
      φ (Pi.single a 1) =
        φ (Pi.single a 1) a • Pi.single a 1 + φ (Pi.single a 1) a' • Pi.single a' 1 ∧
      φ (Pi.single a' 1) =
        φ (Pi.single a' 1) a • Pi.single a 1 + φ (Pi.single a' 1) a' • Pi.single a' 1 := by
  have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a a' ∧
      (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a a' := h₂.hypPair_mem_perpSub d₂
  have hu₃ : (Pi.single a₃ 1 : Fin d → K) ∈ perpSub K a a' ∧
      (Pi.single b₃ 1 : Fin d → K) ∈ perpSub K a a' := h₃.hypPair_mem_perpSub d₃
  have key : ∀ ψ : (Fin d → K) ≃+ (Fin d → K),
      (∀ w ∈ perpSub K a a', polar Q (Pi.single a₂ 1) w = 0 → ∀ x,
        ψ (eichler Q (Pi.single a₂ 1) w x) = eichler Q (Pi.single a₂ 1) w (ψ x)) →
      (∀ w ∈ perpSub K a a', polar Q (Pi.single b₂ 1) w = 0 → ∀ x,
        ψ (eichler Q (Pi.single b₂ 1) w x) = eichler Q (Pi.single b₂ 1) w (ψ x)) →
      ∀ v, (∀ u w, u ∈ perpSub K a a' → w ∈ perpSub K a a' → eichler Q u w v = v) →
        ψ v = ψ v a • Pi.single a 1 + ψ v a' • Pi.single a' 1 := by
    intro ψ hψe hψf v hv
    exact h.eq_planePart_of_forall_eichler_fix hQ h₂ h₃ d₂ d₃ d₂₃
      (fun w hw hw' => by rw [← hψe w hw hw' v, hv _ _ hu₂.1 hw])
      (fun w hw hw' => by rw [← hψf w hw hw' v, hv _ _ hu₂.2 hw])
  have hsymm : ∀ (u : Fin d → K), (∀ w ∈ perpSub K a a', polar Q u w = 0 → ∀ x,
      φ (eichler Q u w x) = eichler Q u w (φ x)) → ∀ w ∈ perpSub K a a', polar Q u w = 0 → ∀ x,
      φ.symm (eichler Q u w x) = eichler Q u w (φ.symm x) := by
    intro u hu w hw hw' x
    apply φ.injective
    rw [hu w hw hw', AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hea := key φ hDe hDf _ fun u w hu hw => (h.eichler_mem_stabSub hu hw).1
  have heb := key φ hDe hDf _ fun u w hu hw => (h.eichler_mem_stabSub hu hw).2
  have hea' := key φ.symm (hsymm _ hDe) (hsymm _ hDf) _ fun u w hu hw =>
    (h.eichler_mem_stabSub hu hw).1
  have heb' := key φ.symm (hsymm _ hDe) (hsymm _ hDf) _ fun u w hu hw =>
    (h.eichler_mem_stabSub hu hw).2
  have hpol := polar_map_of_semisim (φ := φ) (σ := σ) hφQ
  have hφU : ∀ x ∈ perpSub K a a', φ x ∈ perpSub K a a' := by
    intro x hx
    constructor
    · have h1 : b * φ x a = 0 := by
        rw [← h.polar_right (φ x), ← AddEquiv.apply_symm_apply φ (Pi.single a' 1), hpol, heb',
          h.polar_plane_perp _ _ hx, map_zero, mul_zero]
      exact (mul_eq_zero.mp h1).resolve_left hb
    · have h1 : b * φ x a' = 0 := by
        rw [← h.polar_left (φ x), ← AddEquiv.apply_symm_apply φ (Pi.single a 1), hpol, hea',
          h.polar_plane_perp _ _ hx, map_zero, mul_zero]
      exact (mul_eq_zero.mp h1).resolve_left hb
  obtain ⟨hσ, γ, hγ0, hφγ⟩ := eq_smul_of_commute_of_commute (h.polarNondegOn_perpSub hQ)
    (h₂.orth h₃ d₂₃) hu₂.1 hu₂.2 hu₃.1 hu₃.2 hμ hφs hφQ hφU
    (fun w hw hw' x _ => hDe w hw hw' x) (fun w hw hw' x _ => hDf w hw hw' x)
  exact ⟨hσ, ⟨γ, hγ0, hφγ⟩, hea, heb⟩

theorem IsAnisoCoord.eq_smul_rot_of_commute [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (h : IsAnisoCoord Q a a' b c)
    (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃) (d₂ : PairDisjoint a a' a₂ b₂)
    (d₃ : PairDisjoint a a' a₃ b₃) (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃)
    {φ : (Fin d → K) ≃+ (Fin d → K)} {σ : K ≃+* K} {μ : K} (hμ : μ ≠ 0)
    (hφs : ∀ (c : K) x, φ (c • x) = σ c • φ x) (hφQ : ∀ x, Q (φ x) = μ * σ (Q x))
    (hDe : ∀ w ∈ perpSub K a a', polar Q (Pi.single a₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single a₂ 1) w x) = eichler Q (Pi.single a₂ 1) w (φ x))
    (hDf : ∀ w ∈ perpSub K a a', polar Q (Pi.single b₂ 1) w = 0 → ∀ x,
      φ (eichler Q (Pi.single b₂ 1) w x) = eichler Q (Pi.single b₂ 1) w (φ x))
    (hX : ∀ x, φ (anisoRotLin a a' b c 1 (b / c) x) = anisoRotLin a a' b c 1 (b / c) (φ x)) :
    (∀ c, σ c = c) ∧ ∃ γ p s : K, p ^ 2 + b * p * s + c * s ^ 2 = 1 ∧ γ ≠ 0 ∧
      ∀ x, φ x = γ • anisoRotLin a a' b c p s x := by
  have hb := h.b_ne_zero
  have hc := h.c_ne_zero
  have hβ : b / c ≠ 0 := div_ne_zero hb hc
  obtain ⟨hσ, ⟨γ, hγ0, hφγ⟩, hea, heb⟩ :=
    h.eq_smul_on_perpSub_of_commute hQ hb h₂ h₃ d₂ d₃ d₂₃ hμ hφs hφQ hDe hDf
  have hφl : ∀ (c : K) x, φ (c • x) = c • φ x := fun c x => by rw [hφs, hσ]
  set p := φ (Pi.single a 1) a with hp
  set s := φ (Pi.single a 1) a' with hs
  set r := φ (Pi.single a' 1) a with hr
  set u := φ (Pi.single a' 1) a' with hu
  have key := hX (Pi.single a 1)
  rw [anisoRotLin_single_left h.ne, map_add, hφl, hφl, hea, heb] at key
  have ka := congrFun key a
  have kb := congrFun key a'
  rw [anisoRotLin_apply_left] at ka
  rw [anisoRotLin_apply_right h.ne] at kb
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    Pi.single_eq_of_ne h.ne, Pi.single_eq_of_ne h.ne.symm, mul_one, mul_zero, add_zero,
    zero_add, one_mul] at ka kb
  have hrcs : r = c * s := by
    have : b / c * (r - c * s) = 0 := by linear_combination ka
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβ)
  have hup : u = p + b * s := by
    have : b / c * (u - (p + b * s)) = 0 := by linear_combination kb
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβ)
  have hμγ : μ = γ * γ := by
    have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a a' ∧
        (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a a' := h₂.hypPair_mem_perpSub d₂
    have hQx : Q (Pi.single a₂ 1 + Pi.single b₂ 1) = 1 := h₂.map_single_add
    have h1 := hφQ (Pi.single a₂ 1 + Pi.single b₂ 1)
    rw [hφγ _ ((perpSub K a a').add_mem hu₂.1 hu₂.2), map_smul_eq_sq, hQx, map_one] at h1
    linear_combination -h1
  have hNγ : p ^ 2 + b * p * s + c * s ^ 2 = γ * γ := by
    have h1 := hφQ (Pi.single a 1)
    rw [hea, h.map_left, map_one, mul_one, hμγ] at h1
    have h2 := h.map_add_smul p s (p := 0) rfl rfl
    rw [add_zero, QuadraticMap.map_zero, add_zero] at h2
    rw [← h2, h1]
  have hN : (p / γ) ^ 2 + b * (p / γ) * (s / γ) + c * (s / γ) ^ 2 = 1 := by
    field_simp
    linear_combination hNγ
  refine ⟨hσ, γ, p / γ, s / γ, hN, hγ0, fun x => ?_⟩
  have hpx := perpPart_mem (K := K) h.ne x
  have hφx : φ x = x a • (p • Pi.single a 1 + s • Pi.single a' 1) +
      x a' • ((c * s) • Pi.single a 1 + (p + b * s) • Pi.single a' 1) +
        γ • perpPart a a' x := by
    conv_lhs => rw [eq_add_perpPart a a' x]
    rw [map_add, map_add, hφl, hφl, hea, heb, hφγ _ hpx, hrcs, hup]
  have hrx : anisoRotLin a a' b c (p / γ) (s / γ) x =
      x a • ((p / γ) • Pi.single a 1 + (s / γ) • Pi.single a' 1) +
        x a' • ((c * (s / γ)) • Pi.single a 1 + (p / γ + b * (s / γ)) • Pi.single a' 1) +
          perpPart a a' x := by
    conv_lhs => rw [eq_add_perpPart a a' x]
    rw [map_add, map_add, map_smul, map_smul, anisoRotLin_single_left h.ne, anisoRotLin_single_right h.ne,
      anisoRotLin_apply_of_mem_perpSub _ _ hpx]
  rw [hφx, hrx]
  match_scalars <;> (field_simp; try ring)

theorem IsAnisoCoord.exists_mem_anisoTorusOf_eq_conj [Finite K] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (h : IsAnisoCoord Q a a' b c) (h₂ : IsHypCoord Q a₂ b₂) (h₃ : IsHypCoord Q a₃ b₃)
    (d₂ : PairDisjoint a a' a₂ b₂) (d₃ : PairDisjoint a a' a₃ b₃)
    (d₂₃ : PairDisjoint a₂ b₂ a₃ b₃) {β : MulAut (matrixProjectiveDerived Q)}
    (hβE : β ∈ matrixProjectiveImage Q) (hX : ∀ x ∈ anisoTorusOf Q h.ne b c, β x = x)
    (hD : ∀ x ∈ pairPerpOf Q a a', β x = x) :
    ∃ x ∈ anisoTorusOf Q h.ne b c, β = MulAut.conj x := by
  have hQ' := h.exists_ne_zero
  obtain ⟨g, rfl⟩ := hβE
  have hu₂ : (Pi.single a₂ 1 : Fin d → K) ∈ perpSub K a a' ∧
      (Pi.single b₂ 1 : Fin d → K) ∈ perpSub K a a' := h₂.hypPair_mem_perpSub d₂
  have hDcomm : ∀ u ∈ perpSub K a a', ∀ w ∈ perpSub K a a', ∀ x,
      simMap g (eichler Q u w x) = eichler Q u w (simMap g x) := by
    intro u hu w hw x
    exact commute_of_kappa_projHom_eq hQ' g
      (E := ⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩)
      (hD _ ⟨⟨eichler Q u w, eichler_mem_orthDerived hQ hT u w⟩, h.eichler_mem_stabSub hu hw,
        rfl⟩) x
  have hN₀ := h.norm_rot_one
  set x₀ : orthDerived Q := ⟨anisoRotEquiv h.ne b c hN₀,
    h.anisoRotSub_le_orthDerived hQ hT (anisoRotEquiv_mem_anisoRotSub h.ne hN₀)⟩ with hx₀def
  have hXcomm : ∀ x, simMap g (anisoRotLin a a' b c 1 (b / c) x) =
      anisoRotLin a a' b c 1 (b / c) (simMap g x) :=
    commute_of_kappa_projHom_eq hQ' g (E := x₀) (hX _ ⟨x₀, anisoRotEquiv_mem_anisoRotSub h.ne hN₀, rfl⟩)
  obtain ⟨-, γ, p, s, hN, hγ0, hφ⟩ := h.eq_smul_rot_of_commute hQ h₂ h₃ d₂ d₃ d₂₃
    (Units.ne_zero (multiplier Q g)) (simMap_smul g) (map_simMap g)
    (fun w hw _ x => hDcomm _ hu₂.1 w hw x) (fun w hw _ x => hDcomm _ hu₂.2 w hw x) hXcomm
  set R : orthDerived Q := ⟨anisoRotEquiv h.ne b c hN,
    h.anisoRotSub_le_orthDerived hQ hT (anisoRotEquiv_mem_anisoRotSub h.ne hN)⟩ with hRdef
  exact ⟨projHom Q R, ⟨R, anisoRotEquiv_mem_anisoRotSub h.ne hN, rfl⟩,
    kappa_eq_conj_of_eq_smul g R hγ0 hφ⟩

end Aut

end CFSG.SeitzReduction.OmegaPilot
