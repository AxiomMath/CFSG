module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
public import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {m : ℕ}

@[expose] def _root_.CFSG.LieType.Universal.Spin.HypFrame.toFrame (F : HypFrame Q m) {i j : Fin m}
    (hij : i ≠ j) (s t : Bool) : Frame Q where
  P := ⟨F.vec i s, F.vec i (!s), F.map_vec i s, F.map_vec i (!s), F.polar_vec_not i s⟩
  P' := ⟨F.vec j t, F.vec j (!t), F.map_vec j t, F.map_vec j (!t), F.polar_vec_not j t⟩
  orth := ⟨F.polar_vec_of_ne hij s t, F.polar_vec_of_ne hij s (!t),
    F.polar_vec_of_ne hij (!s) t, F.polar_vec_of_ne hij (!s) (!t)⟩

theorem coe_upperSL2_eq_transvection (c : K) :
    upperSL2 c = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c :=
  Subtype.ext ((coe_upperSL2 c).trans (Frame.coe_transvection_zero_one c).symm)

theorem coe_lowerSL2_eq_transvection (c : K) :
    lowerSL2 c = Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) c :=
  Subtype.ext ((coe_lowerSL2 c).trans (Frame.coe_transvection_one_zero c).symm)

theorem spinAction_comp_longSL2 (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) :
    (spinAction Q).comp (F.longSL2 hij s t) = (F.toFrame hij s t).La := by
  refine MonoidHom.ext fun A => ?_
  let φ : SL(2, K) →* (V ≃ₗ[K] V) × (V ≃ₗ[K] V) :=
    ((spinAction Q).comp (F.longSL2 hij s t)).prod (F.toFrame hij s t).La
  have h : φ A ∈ (MonoidHom.fst (V ≃ₗ[K] V) (V ≃ₗ[K] V)).eqLocus
      (MonoidHom.snd (V ≃ₗ[K] V) (V ≃ₗ[K] V)) := by
    refine Frame.sl2_apply_mem φ _ (fun c => ?_) (fun c => ?_) A
    · change spinAction Q (F.longSL2 hij s t _) = (F.toFrame hij s t).La _
      rw [← coe_upperSL2_eq_transvection, HypFrame.longSL2_upperSL2,
        HypFrame.spinAction_longRoot_eq_eichler, coe_upperSL2_eq_transvection,
        Frame.La_transvection_zero_one]
      rfl
    · change spinAction Q (F.longSL2 hij s t _) = (F.toFrame hij s t).La _
      rw [← coe_lowerSL2_eq_transvection, HypFrame.longSL2_lowerSL2,
        HypFrame.spinAction_longRoot_eq_eichler, coe_lowerSL2_eq_transvection,
        Frame.La_transvection_one_zero]
      rfl
  exact h

theorem map_longSL2_range (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool) :
    (F.longSL2 hij s t).range.map (spinAction Q) = (F.toFrame hij s t).La.range := by
  rw [← MonoidHom.range_comp, spinAction_comp_longSL2]

end Frame

section Core

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

theorem La_range_eq_map_conj {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {fr fr₀ : Frame Q} {g : V ≃ₗ[K] V}
    (h : ∀ A : SL(2, K), fr.La A = g * fr₀.La A * g⁻¹) :
    fr.La.range = fr₀.La.range.map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨fr₀.La A, ⟨A, rfl⟩, (h A).symm⟩
  · rintro ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨A, h A⟩

theorem map_conj_map {K Γ : Type} [Group K] [Group Γ] (θ : K →* Γ) (x : K) (R : Subgroup K) :
    (R.map (MulAut.conj x).toMonoidHom).map θ = (R.map θ).map (MulAut.conj (θ x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun y => ?_
  simp [MulAut.conj_apply]

theorem exists_conj_longSL2_of_isClassicalMember [Finite (spinGroup Q)]
    (hodd : Odd (Nat.card (GaloisField p f))) (h4 : 4 ≤ Nat.card (GaloisField p f))
    (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hK : CFSG.Open.IsQuasisimple (spinGroup Q))
    {m : ℕ} (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    (hperp : 2 ≤ Module.finrank (GaloisField p f) (F₀.toFrame hij s t).perp)
    {L : Subgroup (spinGroup Q)} {z : spinGroup Q} (h : IsClassicalMember p f L z) :
    ∃ x : spinGroup Q, L = (F₀.longSL2 hij s t).range.map (MulAut.conj x).toMonoidHom := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card (GaloisField p f) hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  set fr₀ := F₀.toFrame hij s t with hfr₀
  have : Nontrivial V := ⟨⟨fr₀.e₁, 0, fr₀.P.e_ne_zero⟩⟩
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hker2 : ∀ c ∈ (spinAction Q).ker, c * c = 1 := by
    intro c hc
    rcases (mem_ker_spinAction_iff Q hQnd c).mp hc with rfl | rfl
    · exact one_mul 1
    · apply Subtype.ext
      simp
  have hθy : ∀ A : SL(2, GaloisField p f), spinAction Q (F₀.longSL2 hij s t A) = fr₀.La A :=
    fun A => DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) A
  by_cases hz : spinAction Q z = 1
  · exfalso
    have hzc : z ∈ Subgroup.center (spinGroup Q) := hker (MonoidHom.mem_ker.mpr hz)
    set y : spinGroup Q := F₀.longSL2 hij s t (-1) with hy
    have hy1 : spinAction Q y ≠ 1 := by
      rw [hy, hθy]
      intro h1
      exact sl2_neg_one_ne_one hodd (fr₀.La_injective (h1.trans fr₀.La.map_one.symm))
    have hyy : y * y = 1 := by
      rw [hy, ← map_mul]
      have : (-1 : SL(2, GaloisField p f)) * (-1) = 1 := by simp
      rw [this, map_one]
    have hy2 : orderOf y = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hyy) (fun h1 => hy1 (by rw [h1, map_one]))
    exact false_of_isClassicalMember_of_central hK hodd h hzc hy2
      (fun hyz => hy1 (by rw [hyz]; exact hz))
  · obtain ⟨fr, hfr⟩ := exists_frame_map_eq_of_isClassicalMember hodd h4 hQ hker hker2 hrange h hz
    obtain ⟨x, hx⟩ := exists_spin_conj hodd hQ fr₀ fr hperp
    have hperf : Group.IsPerfect SL(2, GaloisField p f) := sl2_isPerfect h4
    have hR₀ : ⁅(F₀.longSL2 hij s t).range, (F₀.longSL2 hij s t).range⁆ =
        (F₀.longSL2 hij s t).range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
    refine ⟨x, eq_of_map_eq_of_isPerfect (spinAction Q) hker
      (Subgroup.isPerfect_iff.mp h.perfect) ?_ ?_⟩
    · rw [← Subgroup.map_commutator, hR₀]
    · rw [hfr, map_conj_map, map_longSL2_range, La_range_eq_map_conj hx]

end Core

end CFSG.ClassicalInvolution.ModelFacts
