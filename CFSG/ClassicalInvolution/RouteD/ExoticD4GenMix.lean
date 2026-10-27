module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenEich
public import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Span

theorem polar_eq_zero_of_span_eq_perp {fr₁ fr₃ : OFrame Q} (hY : fr₃.span = fr₁.perp) {x y : V}
    (hx : x ∈ fr₁.span) (hy : y ∈ fr₃.span) : polar Q x y = 0 := by
  have hy' : fr₁.coords y = 0 := by
    rw [← fr₁.mem_perp_iff, ← hY]
    exact hy
  calc polar Q x y = polar Q y x := polar_comm Q x y
    _ = polar Q y (fr₁.incl (fr₁.coords x)) := by rw [← fr₁.mem_span_iff.mp hx]
    _ = 0 := by rw [fr₁.polar_incl_right, hy']; simp

theorem coords_eq_zero_of_mem_perp_swap {fr : OFrame Q} {x : V} (hx : x ∈ fr.perp) :
    fr.swap.coords x = 0 := by
  rw [Frame.coords_swap, fr.mem_perp_iff.mp hx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaLin_apply]

theorem omega_apply_of_mem_perp (fr : OFrame Q) {g : V ≃ₗ[F] V} (hg : g ∈ omegaGrp fr) {x : V}
    (hx : x ∈ fr.perp) : g x = x := by
  have hxs : fr.swap.coords x = 0 := coords_eq_zero_of_mem_perp_swap hx
  have hle : omegaGrp fr ≤ MulAction.stabilizer (V ≃ₗ[F] V) x := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      exact Frame.La_apply_of_coords_eq_zero fr A (fr.mem_perp_iff.mp hx)
    · rintro _ ⟨A, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      exact Frame.La_apply_of_coords_eq_zero fr.swap A hxs
  have := MulAction.mem_stabilizer_iff.mp (hle hg)
  exact this

end Span

section Frame4

variable (fr₁ fr₃ : OFrame Q)

@[expose] def mixVec : Fin 4 → Bool → V := fun i s =>
  cond s (![fr₁.e₁, fr₁.e₂, fr₃.e₁, fr₃.e₂] i) (![fr₁.f₁, fr₁.f₂, fr₃.f₁, fr₃.f₂] i)

variable {fr₁ fr₃}

theorem mixVec_Q (i : Fin 4) (s : Bool) : Q (mixVec fr₁ fr₃ i s) = 0 := by
  fin_cases i <;> cases s <;>
    simp [mixVec, fr₁.Q_e₁, fr₁.Q_e₂, fr₁.Q_f₁, fr₁.Q_f₂, fr₃.Q_e₁, fr₃.Q_e₂, fr₃.Q_f₁, fr₃.Q_f₂]

theorem mixVec_polar_not (i : Fin 4) (s : Bool) :
    polar Q (mixVec fr₁ fr₃ i s) (mixVec fr₁ fr₃ i (!s)) = 1 := by
  fin_cases i <;> cases s <;>
    simp [mixVec, fr₁.polar_e₁_f₁, fr₁.polar_f₁_e₁, fr₁.polar_e₂_f₂, fr₁.polar_f₂_e₂,
      fr₃.polar_e₁_f₁, fr₃.polar_f₁_e₁, fr₃.polar_e₂_f₂, fr₃.polar_f₂_e₂]

theorem mixVec_polar_ne (hY : fr₃.span = fr₁.perp) {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    polar Q (mixVec fr₁ fr₃ i s) (mixVec fr₁ fr₃ j t) = 0 := by
  have c13 : ∀ x y, x ∈ fr₁.span → y ∈ fr₃.span → polar Q x y = 0 := fun x y hx hy =>
    polar_eq_zero_of_span_eq_perp hY hx hy
  have c31 : ∀ x y, x ∈ fr₃.span → y ∈ fr₁.span → polar Q x y = 0 := fun x y hx hy => by
    rw [polar_comm]
    exact c13 y x hy hx
  have a1 := Frame.e₁_mem_span fr₁
  have a2 := Frame.f₁_mem_span fr₁
  have a3 := Frame.e₂_mem_span fr₁
  have a4 := Frame.f₂_mem_span fr₁
  have b1 := Frame.e₁_mem_span fr₃
  have b2 := Frame.f₁_mem_span fr₃
  have b3 := Frame.e₂_mem_span fr₃
  have b4 := Frame.f₂_mem_span fr₃
  fin_cases i <;> fin_cases j <;> simp at hij <;> cases s <;> cases t <;>
    simp [mixVec, fr₁.polar_e₁_e₂, fr₁.polar_e₁_f₂, fr₁.polar_f₁_e₂, fr₁.polar_f₁_f₂,
      fr₁.polar_e₂_e₁, fr₁.polar_f₂_e₁, fr₁.polar_e₂_f₁, fr₁.polar_f₂_f₁, fr₃.polar_e₁_e₂,
      fr₃.polar_e₁_f₂, fr₃.polar_f₁_e₂, fr₃.polar_f₁_f₂, fr₃.polar_e₂_e₁, fr₃.polar_f₂_e₁,
      fr₃.polar_e₂_f₁, fr₃.polar_f₂_f₁, c13 _ _ a1 b1, c13 _ _ a1 b2, c13 _ _ a1 b3,
      c13 _ _ a1 b4, c13 _ _ a2 b1, c13 _ _ a2 b2, c13 _ _ a2 b3, c13 _ _ a2 b4, c13 _ _ a3 b1,
      c13 _ _ a3 b2, c13 _ _ a3 b3, c13 _ _ a3 b4, c13 _ _ a4 b1, c13 _ _ a4 b2, c13 _ _ a4 b3,
      c13 _ _ a4 b4, c31 _ _ b1 a1, c31 _ _ b1 a2, c31 _ _ b1 a3, c31 _ _ b1 a4, c31 _ _ b2 a1,
      c31 _ _ b2 a2, c31 _ _ b2 a3, c31 _ _ b2 a4, c31 _ _ b3 a1, c31 _ _ b3 a2, c31 _ _ b3 a3,
      c31 _ _ b3 a4, c31 _ _ b4 a1, c31 _ _ b4 a2, c31 _ _ b4 a3, c31 _ _ b4 a4]

end Frame4

section Mixed

variable {fr₁ fr₃ : OFrame Q}

theorem mem_perp_of_mem_span₃ (hY : fr₃.span = fr₁.perp) {y : V} (hy : y ∈ fr₃.span) :
    y ∈ fr₁.perp := hY ▸ hy

theorem mem_perp₃_of_mem_span₁ (hY : fr₃.span = fr₁.perp) {x : V} (hx : x ∈ fr₁.span) :
    x ∈ fr₃.perp := by
  rw [Frame.mem_perp_iff, Frame.coords_apply]
  have h := fun y (hy : y ∈ fr₃.span) => polar_eq_zero_of_span_eq_perp hY hx hy
  simp [h _ (Frame.e₁_mem_span fr₃), h _ (Frame.f₁_mem_span fr₃), h _ (Frame.e₂_mem_span fr₃),
    h _ (Frame.f₂_mem_span fr₃)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eichler_mixed_mem (hY : fr₃.span = fr₁.perp) {G : Subgroup (V ≃ₗ[F] V)}
    (h₁ : omegaGrp fr₁ ≤ G) (h₃ : omegaGrp fr₃ ≤ G) {s y : V} (hs : s ∈ fr₁.span)
    (hy : y ∈ fr₃.span) (hQs : Q s = 0) (hQy : Q y = 0) (hs0 : s ≠ 0) (hy0 : y ≠ 0)
    (hE : eichler Q s y ∈ G) {s₁ y₁ : V} (hs₁ : s₁ ∈ fr₁.span) (hy₁ : y₁ ∈ fr₃.span)
    (hQs₁ : Q s₁ = 0) (hQy₁ : Q y₁ = 0) : eichler Q s₁ y₁ ∈ G := by
  by_cases hs₁0 : s₁ = 0
  · rw [hs₁0, eichler_zero_left]
    exact Subgroup.one_mem _
  by_cases hy₁0 : y₁ = 0
  · rw [hy₁0, eichler_zero_right]
    exact Subgroup.one_mem _
  obtain ⟨A₁, B₁, hg₁⟩ := exists_mul_apply_eq fr₁ hs hs₁ hs0 hs₁0 hQs hQs₁
  obtain ⟨A₃, B₃, hg₃⟩ := exists_mul_apply_eq fr₃ hy hy₁ hy0 hy₁0 hQy hQy₁
  set g₁ : V ≃ₗ[F] V := fr₁.La A₁ * fr₁.swap.La B₁ with hg₁def
  set g₃ : V ≃ₗ[F] V := fr₃.La A₃ * fr₃.swap.La B₃ with hg₃def
  have hg₁Ω : g₁ ∈ omegaGrp fr₁ :=
    Subgroup.mul_mem _ (La_mem_omegaGrp fr₁ A₁) (swapLa_mem_omegaGrp fr₁ B₁)
  have hg₃Ω : g₃ ∈ omegaGrp fr₃ :=
    Subgroup.mul_mem _ (La_mem_omegaGrp fr₃ A₃) (swapLa_mem_omegaGrp fr₃ B₃)
  have hgΩ : g₁ * g₃ ∈ G := Subgroup.mul_mem _ (h₁ hg₁Ω) (h₃ hg₃Ω)
  have hgO : g₁ * g₃ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.mul_mem _ (omegaGrp_le_orthogonalGroup fr₁ hg₁Ω)
      (omegaGrp_le_orthogonalGroup fr₃ hg₃Ω)
  have e1 : (g₁ * g₃) s = s₁ := by
    rw [LinearEquiv.mul_apply, omega_apply_of_mem_perp fr₃ hg₃Ω (mem_perp₃_of_mem_span₁ hY hs), hg₁]
  have e2 : (g₁ * g₃) y = y₁ := by
    rw [LinearEquiv.mul_apply, hg₃, omega_apply_of_mem_perp fr₁ hg₁Ω
      (mem_perp_of_mem_span₃ hY hy₁)]
  have h := eichler_conj hgO s y
  rw [e1, e2] at h
  rw [← h]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgΩ hE) (Subgroup.inv_mem _ hgΩ)

end Mixed

section Final

open CFSG.LieType.Universal.Spin

variable {fr₁ fr₃ : OFrame Q}

noncomputable def mixFrame (hY : fr₃.span = fr₁.perp) : HypFrame Q 4 where
  vec := mixVec fr₁ fr₃
  map_vec := mixVec_Q
  polar_vec_of_ne := fun _ _ hij s t => mixVec_polar_ne hY hij s t
  polar_vec_not := mixVec_polar_not
  exists_aux := by
    intro i j
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 4, k ≠ i ∧ k ≠ j := by
      revert i j
      decide
    refine ⟨mixVec fr₁ fr₃ k true + mixVec fr₁ fr₃ k false, ?_, fun s => ?_⟩
    · have h1 : Q (mixVec fr₁ fr₃ k true + mixVec fr₁ fr₃ k false) = 1 := by
        rw [QuadraticMap.map_add Q, mixVec_Q, mixVec_Q]
        simpa using mixVec_polar_not (fr₁ := fr₁) (fr₃ := fr₃) k true
      rw [h1]
      exact isUnit_one
    · refine ⟨?_, ?_⟩
      · rw [polar_add_right, mixVec_polar_ne hY (Ne.symm hki), mixVec_polar_ne hY (Ne.symm hki),
          add_zero]
      · rw [polar_add_right, mixVec_polar_ne hY (Ne.symm hkj), mixVec_polar_ne hY (Ne.symm hkj),
          add_zero]

theorem eq_zero_of_polar_mixFrame (hY : fr₃.span = fr₁.perp) {v : V}
    (hv : ∀ k r, polar Q v ((mixFrame hY).vec k r) = 0) : v = 0 := by
  have h1 : fr₁.coords v = 0 := by
    rw [Frame.coords_apply]
    have a := hv 0 false
    have b := hv 1 false
    have c := hv 1 true
    have d := hv 0 true
    simp [mixFrame, mixVec] at a b c d
    simp [a, b, c, d]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h3 : fr₃.coords v = 0 := by
    rw [Frame.coords_apply]
    have a := hv 2 false
    have b := hv 3 false
    have c := hv 3 true
    have d := hv 2 true
    simp [mixFrame, mixVec] at a b c d
    simp [a, b, c, d]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hp : v ∈ fr₃.span := by
    rw [hY]
    exact fr₁.mem_perp_iff.mpr h1
  have hq : v ∈ fr₃.perp := fr₃.mem_perp_iff.mpr h3
  exact Submodule.disjoint_def.mp fr₃.isCompl_span_perp.disjoint v hp hq

theorem mixVec_mem₁ {i : Fin 4} (hi : i.val < 2) (s : Bool) : mixVec fr₁ fr₃ i s ∈ fr₁.span := by
  fin_cases i <;> simp at hi <;> cases s <;>
    simp [mixVec, Frame.e₁_mem_span, Frame.f₁_mem_span, Frame.e₂_mem_span, Frame.f₂_mem_span]

theorem mixVec_mem₃ {i : Fin 4} (hi : ¬ i.val < 2) (s : Bool) : mixVec fr₁ fr₃ i s ∈ fr₃.span := by
  fin_cases i <;> simp at hi <;> cases s <;>
    simp [mixVec, Frame.e₁_mem_span, Frame.f₁_mem_span, Frame.e₂_mem_span, Frame.f₂_mem_span]

theorem elementaryGroup_le_of_mixed (h2 : (2 : F) ≠ 0) (hY : fr₃.span = fr₁.perp)
    {G : Subgroup (V ≃ₗ[F] V)} (h₁ : omegaGrp fr₁ ≤ G) (h₃ : omegaGrp fr₃ ≤ G) {s y : V}
    (hs : s ∈ fr₁.span) (hy : y ∈ fr₃.span) (hQs : Q s = 0) (hs0 : s ≠ 0) (hy0 : y ≠ 0)
    (hE : eichler Q s y ∈ G) : elementaryGroup Q ≤ G := by
  obtain ⟨y', hy', hQy', hy0', hE'⟩ :
      ∃ y' ∈ fr₃.span, Q y' = 0 ∧ y' ≠ 0 ∧ eichler Q s y' ∈ G := by
    by_cases hQy : Q y = 0
    · exact ⟨y, hy, hQy, hy0, hE⟩
    · have hyZ : y = fr₃.incl (fr₃.coords y) := fr₃.mem_span_iff.mp hy
      set Z : Matrix (Fin 2) (Fin 2) F := fr₃.coords y with hZ
      set w : V := fr₃.incl (Z * !![0, 1; 0, 0]) with hw
      have hw_mem : w ∈ fr₃.span := ⟨_, rfl⟩
      have hQw : Q w = 0 := by
        rw [hw, Frame.Q_incl, Matrix.det_mul]
        simp
      have hdet : Z.det ≠ 0 := by
        intro h
        apply hQy
        rw [hyZ, Frame.Q_incl]
        exact h
      have hw0 : w ≠ 0 := by
        intro h
        have h0 : Z * !![0, 1; 0, 0] = 0 := by
          have := congrArg fr₃.coords h
          rwa [hw, Frame.coords_incl, map_zero] at this
        apply hdet
        have e1 := congrFun (congrFun h0 0) 1
        have e2 := congrFun (congrFun h0 1) 1
        simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
        rw [Matrix.det_fin_two, e1, e2]
        ring
      have hpyw : polar Q y w = 0 := by
        rw [hw, fr₃.polar_incl_right, ← hZ]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
        ring
      have hyy : polar Q y y ≠ 0 := by
        rw [polar_self_eq_two_mul]
        exact mul_ne_zero h2 hQy
      set b : V := (-(polar Q y y)⁻¹) • y with hb
      have hb_mem : b ∈ fr₃.span := Submodule.smul_mem _ _ hy
      have hpwb : polar Q w b = 0 := by
        rw [hb, polar_smul_right_eq, polar_comm Q w y, hpyw, mul_zero]
      have hpyb : polar Q y b = -1 := by
        rw [hb, polar_smul_right_eq, neg_mul, inv_mul_cancel₀ hyy]
      have hβ : eichler Q w b ∈ omegaGrp fr₃ := eichler_mem_omegaGrp fr₃ hw_mem hb_mem hQw hpwb
      have hβO := omegaGrp_le_orthogonalGroup fr₃ hβ
      have hcr : ∀ z ∈ fr₃.span, polar Q s z = 0 := fun z hz =>
        polar_eq_zero_of_span_eq_perp hY hs hz
      have hβs : eichler Q w b s = s :=
        eichler_apply_of_polar_eq_zero (hcr w hw_mem) (hcr b hb_mem)
      have hβy : eichler Q w b y = y + w := by
        rw [eichler_apply hQw hpwb, hpyw, hpyb]
        simp
      have hc := eichler_conj hβO s y
      rw [hβs, hβy] at hc
      have hmul := eichler_mul (u := s) (v := y) (w := w) (hcr y hy) (hcr w hw_mem)
      refine ⟨w, hw_mem, hQw, hw0, ?_⟩
      have h1 : eichler Q s w = (eichler Q s y)⁻¹ * (eichler Q w b * eichler Q s y *
          (eichler Q w b)⁻¹) := by
        rw [hc, ← hmul]
        group
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (h₃ hβ) hE) (Subgroup.inv_mem _ (h₃ hβ)))
  have hmix : ∀ {s₁ y₁ : V}, s₁ ∈ fr₁.span → y₁ ∈ fr₃.span → Q s₁ = 0 → Q y₁ = 0 →
      eichler Q s₁ y₁ ∈ G := fun hs₁ hy₁ hQs₁ hQy₁ =>
    eichler_mixed_mem hY h₁ h₃ hs hy' hQs hQy' hs0 hy0' hE' hs₁ hy₁ hQs₁ hQy₁
  have hlong : ∀ {i j : Fin 4}, i ≠ j → ∀ (s' t : Bool) (c : F),
      eichler Q ((mixFrame hY).vec j t) (c • (mixFrame hY).vec i s') ∈ G := by
    intro i j hij s' t c
    change eichler Q (mixVec fr₁ fr₃ j t) (c • mixVec fr₁ fr₃ i s') ∈ G
    have hQw : Q (c • mixVec fr₁ fr₃ i s') = 0 := by
      rw [map_smul_eq_sq, mixVec_Q, mul_zero]
    have hQu : Q (mixVec fr₁ fr₃ j t) = 0 := mixVec_Q j t
    have hp : polar Q (mixVec fr₁ fr₃ j t) (c • mixVec fr₁ fr₃ i s') = 0 := by
      rw [polar_smul_right_eq, mixVec_polar_ne hY (Ne.symm hij) t s', mul_zero]
    by_cases hi : i.val < 2 <;> by_cases hj : j.val < 2
    · exact h₁ (eichler_mem_omegaGrp fr₁ (mixVec_mem₁ hj t)
        (Submodule.smul_mem _ _ (mixVec_mem₁ hi s')) hQu hp)
    · rw [eichler_swap' hQu hQw hp]
      exact hmix (Submodule.smul_mem _ _ (mixVec_mem₁ hi s'))
        (Submodule.neg_mem _ (mixVec_mem₃ hj t)) hQw (by rw [QuadraticMap.map_neg, hQu])
    · exact hmix (mixVec_mem₁ hj t) (Submodule.smul_mem _ _ (mixVec_mem₃ hi s')) hQu hQw
    · exact h₃ (eichler_mem_omegaGrp fr₃ (mixVec_mem₃ hj t)
        (Submodule.smul_mem _ _ (mixVec_mem₃ hi s')) hQu hp)
  refine (mixFrame hY).elementaryGroup_le hlong (fun i s' v hv => ?_)
    (fun v hv _ => eq_zero_of_polar_mixFrame hY hv)
  rw [eq_zero_of_polar_mixFrame hY hv, eichler_zero_right]
  exact Subgroup.one_mem _

end Final

end CFSG.ClassicalInvolution.RouteD.Exotic
