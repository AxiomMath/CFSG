module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourStandardAnisoBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace mem_commSpace)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Torus

variable {K : Type*} [Field K] {d : ℕ}

@[expose] noncomputable def anisoTorusOf [CharP K 2] (Q : QuadraticForm K (Fin d → K))
    {a a' : Fin d} (hne : a ≠ a') (b c : K) : Subgroup (matrixProjectiveDerived Q) :=
  ((anisoRotSub hne b c).subgroupOf (orthDerived Q)).map (projHom Q)

variable {Q : QuadraticForm K (Fin d → K)} {a a' : Fin d} {b c : K}

theorem anisoRotLin_single_left (hne : a ≠ a') (p s : K) :
    anisoRotLin a a' b c p s (Pi.single a 1) = p • Pi.single a 1 + s • Pi.single a' 1 := by
  funext i
  by_cases hia : i = a
  · rw [hia, anisoRotLin_apply_left]
    simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
  · by_cases hib : i = a'
    · rw [hib, anisoRotLin_apply_right hne]
      simp [Pi.single_eq_of_ne hne.symm]
    · rw [anisoRotLin_apply_of_ne hia hib]
      simp [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]

theorem anisoRotLin_single_right (hne : a ≠ a') (p s : K) :
    anisoRotLin a a' b c p s (Pi.single a' 1) =
      (c * s) • Pi.single a 1 + (p + b * s) • Pi.single a' 1 := by
  funext i
  by_cases hia : i = a
  · rw [hia, anisoRotLin_apply_left]
    simp [Pi.single_eq_of_ne hne]
  · by_cases hib : i = a'
    · rw [hib, anisoRotLin_apply_right hne]
      simp [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
    · rw [anisoRotLin_apply_of_ne hia hib]
      simp [Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]

theorem IsAnisoCoord.exists_ne_zero (h : IsAnisoCoord Q a a' b c) : ∃ v, Q v ≠ 0 :=
  ⟨_, by rw [h.map_left]; exact one_ne_zero⟩

theorem IsAnisoCoord.apply_mem_perpSub_of_mem_stabSub (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ stabSub a a') {u : Fin d → K} (hu : u ∈ perpSub K a a') : g u ∈ perpSub K a a' := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single a 1) u
  have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (Pi.single a' 1) u
  rw [hg.1, h.polar_left, h.polar_left, hu.2, mul_zero] at h1
  rw [hg.2, h.polar_right, h.polar_right, hu.1, mul_zero] at h2
  exact ⟨(mul_eq_zero.mp h2).resolve_left hb, (mul_eq_zero.mp h1).resolve_left hb⟩

theorem IsAnisoCoord.commute_rot_of_mem_stabSub (h : IsAnisoCoord Q a a' b c) (hb : b ≠ 0)
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : g ∈ stabSub a a') (p s : K) (v : Fin d → K) :
    g (anisoRotLin a a' b c p s v) = anisoRotLin a a' b c p s (g v) := by
  have hpa := perpPart_mem (K := K) h.ne v
  have hgpp := h.apply_mem_perpSub_of_mem_stabSub hb hgO hg hpa
  have hW : ∀ w ∈ planeSub K a a', g w = w := by
    intro w hw
    rw [eq_planePart_of_mem h.ne hw, map_add, map_smul, map_smul, hg.1, hg.2]
  have hrW : anisoRotLin a a' b c p s (v a • Pi.single a 1 + v a' • Pi.single a' 1) ∈
      planeSub K a a' := anisoRotLin_mem_planeSub p s (planePart_mem v)
  have e1 : anisoRotLin a a' b c p s v = perpPart a a' v +
      anisoRotLin a a' b c p s (v a • Pi.single a 1 + v a' • Pi.single a' 1) := by
    conv_lhs => rw [← perpPart_add_planePart (a := a) (b := a') v]
    rw [map_add, anisoRotLin_apply_of_mem_perpSub p s hpa]
  have e2 : g v = g (perpPart a a' v) + (v a • Pi.single a 1 + v a' • Pi.single a' 1) := by
    conv_lhs => rw [← perpPart_add_planePart (a := a) (b := a') v]
    rw [map_add, hW _ (planePart_mem v)]
  calc g (anisoRotLin a a' b c p s v)
      = g (perpPart a a' v + anisoRotLin a a' b c p s (v a • Pi.single a 1 + v a' • Pi.single a' 1)) := by
        rw [e1]
    _ = g (perpPart a a' v) + anisoRotLin a a' b c p s (v a • Pi.single a 1 + v a' • Pi.single a' 1) := by
        rw [map_add, hW _ hrW]
    _ = anisoRotLin a a' b c p s (g (perpPart a a' v)) +
          anisoRotLin a a' b c p s (v a • Pi.single a 1 + v a' • Pi.single a' 1) := by
        rw [anisoRotLin_apply_of_mem_perpSub p s hgpp]
    _ = anisoRotLin a a' b c p s (g v) := by rw [e2]; exact (map_add _ _ _).symm

variable [Finite K] [CharP K 2]

theorem IsAnisoCoord.anisoTorusOf_le_centralizer_pairPerpOf (h : IsAnisoCoord Q a a' b c) :
    anisoTorusOf Q h.ne b c ≤
      centralizer (pairPerpOf Q a a' : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  obtain ⟨p, s, -, hyp⟩ := hy
  have hyp' : ∀ v, ((y : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) v =
      anisoRotLin a a' b c p s v := hyp
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((y : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
    (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((z : (Fin d → K) ≃ₗ[K] (Fin d → K)) v)
  rw [hyp', hyp', h.commute_rot_of_mem_stabSub h.b_ne_zero (Subgroup.commutator_le_self _ z.2) hz]

omit [Finite K] in
theorem IsAnisoCoord.anisoTorusOf_le_centralizer_self (h : IsAnisoCoord Q a a' b c) :
    anisoTorusOf Q h.ne b c ≤
      centralizer (anisoTorusOf Q h.ne b c : Set (matrixProjectiveDerived Q)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨z, hz, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (anisoRotSub_comm h.ne hz hy)

theorem IsAnisoCoord.odd_card_anisoTorusOf (h : IsAnisoCoord Q a a' b c) :
    Odd (Nat.card (anisoTorusOf Q h.ne b c)) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := anisoTorusOf Q h.ne b c) 2 h2
  obtain ⟨y, hy, hyx⟩ := x.2
  have hx2 : x * x = 1 := by rw [← _root_.sq, ← hx, pow_orderOf_eq_one]
  have hyy : y * y = 1 := by
    apply projHom_injective h.exists_ne_zero
    rw [map_mul, hyx, map_one]
    exact congrArg Subtype.val hx2
  have hy1 : ((y : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) = 1 :=
    eq_one_of_mem_anisoRotSub_of_mul_self h.ne h.b_ne_zero hy (congrArg Subtype.val hyy)
  have hx1 : x = 1 := by
    apply Subtype.ext
    rw [← hyx, show y = 1 from Subtype.ext hy1, map_one]
    rfl
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by decide)

omit [Finite K] in
theorem IsAnisoCoord.norm_rot_one (h : IsAnisoCoord Q a a' b c) :
    (1 : K) ^ 2 + b * 1 * (b / c) + c * (b / c) ^ 2 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hc := h.c_ne_zero
  field_simp
  linear_combination (b ^ 2) * h2

theorem IsAnisoCoord.centralizer_anisoTorusOf (h : IsAnisoCoord Q a a' b c)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    centralizer (anisoTorusOf Q h.ne b c : Set (matrixProjectiveDerived Q)) =
      anisoTorusOf Q h.ne b c ⊔ pairPerpOf Q a a' := by
  apply le_antisymm
  · intro z hz
    obtain ⟨g, rfl⟩ := projHom_surjective Q z
    have hb := h.b_ne_zero
    have hc := h.c_ne_zero
    have hβ : b / c ≠ 0 := div_ne_zero hb hc
    have hN₀ := h.norm_rot_one
    set x₀ : orthDerived Q := ⟨anisoRotEquiv h.ne b c hN₀,
      h.anisoRotSub_le_orthDerived hQ hT (anisoRotEquiv_mem_anisoRotSub h.ne hN₀)⟩ with hx₀def
    have hx₀ : projHom Q x₀ ∈ anisoTorusOf Q h.ne b c :=
      ⟨x₀, anisoRotEquiv_mem_anisoRotSub h.ne hN₀, rfl⟩
    set G : (Fin d → K) ≃ₗ[K] (Fin d → K) := (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) with hG
    have hgO : G ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ g.2
    have hcomm : ∀ v, G (anisoRotLin a a' b c 1 (b / c) v) = anisoRotLin a a' b c 1 (b / c) (G v) := by
      have h1 := mem_centralizer_iff.mp hz _ hx₀
      rw [← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val (projHom_injective h.exists_ne_zero h1)
      intro v
      exact (LinearEquiv.congr_fun h2 v).symm
    have hWimg : ∀ w ∈ planeSub K a a', G w ∈ planeSub K a a' := by
      intro w hw
      have hw' : w ∈ commSpace (anisoRotEquiv h.ne b c hN₀) := by
        rw [commSpace_eq_planeSub_of_rot h.ne hb hN₀ hβ (fun v => rfl)]
        exact hw
      obtain ⟨y, rfl⟩ := mem_commSpace.mp hw'
      rw [map_sub]
      change G (anisoRotLin a a' b c 1 (b / c) y) - G y ∈ planeSub K a a'
      rw [hcomm y]
      exact sub_mem_planeSub_of_rot (g := anisoRotEquiv h.ne b c hN₀) (fun v => rfl) _
    set p := G (Pi.single a 1) a with hp
    set s := G (Pi.single a 1) a' with hs
    set r := G (Pi.single a' 1) a with hr
    set u := G (Pi.single a' 1) a' with hu
    have hga : G (Pi.single a 1) = p • Pi.single a 1 + s • Pi.single a' 1 :=
      eq_planePart_of_mem h.ne (hWimg _ single_left_mem_planeSub)
    have hgb : G (Pi.single a' 1) = r • Pi.single a 1 + u • Pi.single a' 1 :=
      eq_planePart_of_mem h.ne (hWimg _ single_right_mem_planeSub)
    have key := hcomm (Pi.single a 1)
    rw [anisoRotLin_single_left h.ne, map_add, map_smul, map_smul, hga, hgb] at key
    have ka := congrFun key a
    have kb := congrFun key a'
    rw [anisoRotLin_apply_left] at ka
    rw [anisoRotLin_apply_right h.ne] at kb
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne h.ne, Pi.single_eq_of_ne h.ne.symm, mul_one, mul_zero, add_zero,
      zero_add] at ka kb
    have hrcs : r = c * s := by
      have : b / c * (r - c * s) = 0 := by linear_combination ka
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβ)
    have hup : u = p + b * s := by
      have : b / c * (u - (p + b * s)) = 0 := by linear_combination kb
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hβ)
    have hN : p ^ 2 + b * p * s + c * s ^ 2 = 1 := by
      have h1 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO (Pi.single a 1)
      rw [hga, h.map_left] at h1
      have h2 := h.map_add_smul p s (p := 0) rfl rfl
      rw [add_zero, QuadraticMap.map_zero, add_zero] at h2
      rw [← h2, h1]
    set R : orthDerived Q := ⟨anisoRotEquiv h.ne b c hN,
      h.anisoRotSub_le_orthDerived hQ hT (anisoRotEquiv_mem_anisoRotSub h.ne hN)⟩ with hRdef
    have hRa : (R : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a 1) = G (Pi.single a 1) := by
      change anisoRotLin a a' b c p s (Pi.single a 1) = _
      rw [anisoRotLin_single_left h.ne, hga]
    have hRb : (R : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a' 1) = G (Pi.single a' 1) := by
      change anisoRotLin a a' b c p s (Pi.single a' 1) = _
      rw [anisoRotLin_single_right h.ne, hgb, hrcs, hup]
    have hstab : ((R⁻¹ * g : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ stabSub a a' := by
      refine ⟨?_, ?_⟩
      · change (R : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ (G (Pi.single a 1)) = Pi.single a 1
        rw [← hRa]
        exact (R : (Fin d → K) ≃ₗ[K] (Fin d → K)).symm_apply_apply _
      · change (R : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ (G (Pi.single a' 1)) = Pi.single a' 1
        rw [← hRb]
        exact (R : (Fin d → K) ≃ₗ[K] (Fin d → K)).symm_apply_apply _
    have hg : g = R * (R⁻¹ * g) := by group
    rw [hg, map_mul]
    exact mul_mem_sup ⟨R, anisoRotEquiv_mem_anisoRotSub h.ne hN, rfl⟩ ⟨R⁻¹ * g, hstab, rfl⟩
  · exact sup_le h.anisoTorusOf_le_centralizer_self
      (le_centralizer_iff.mp h.anisoTorusOf_le_centralizer_pairPerpOf)

end Torus

end CFSG.SeitzReduction.OmegaPilot
