module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Orthogonal.CharTwo

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Witt

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_totallySingular {T : Submodule K V} (hT : ∀ x ∈ T, Q x = 0)
    {x y : V} (hx : x ∈ T) (hy : y ∈ T) : polar Q x y = 0 := by
  rw [polar, hT _ (T.add_mem hx hy), hT x hx, hT y hy, sub_zero, sub_zero]

theorem exists_totallySingular_perp_of_not_mem [FiniteDimensional K V] {W T : Submodule K V}
    (P : HypPair Q) (hfW : P.f ∈ W) (hTW : T ≤ W) (hT : ∀ x ∈ T, Q x = 0)
    (hfT : P.f ∉ T) :
    ∃ T' : Submodule K V, T' ≤ W ⊓ P.perp ∧ (∀ x ∈ T', Q x = 0) ∧
      finrank K T ≤ finrank K T' + 1 := by
  set g : T →ₗ[K] K := (polarBilin Q P.f).domRestrict T with hg
  set φ : V →ₗ[K] V := LinearMap.id - (polarBilin Q P.e).smulRight P.f with hφ
  have hφapp : ∀ t, φ t = t - polar Q P.e t • P.f := fun t => rfl
  set ψ : LinearMap.ker g →ₗ[K] V := φ ∘ₗ T.subtype ∘ₗ (LinearMap.ker g).subtype with hψ
  have hker : ∀ t : LinearMap.ker g, polar Q P.f (t : T) = 0 := fun t => t.2
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    change φ ((t : T) : V) = 0 at ht
    rw [hφapp, sub_eq_zero] at ht
    by_cases hc : polar Q P.e ((t : T) : V) = 0
    · rw [hc, zero_smul] at ht
      exact Subtype.ext (Subtype.ext ht)
    · exfalso
      apply hfT
      have hmem : polar Q P.e ((t : T) : V) • P.f ∈ T := ht ▸ (t : T).2
      have := T.smul_mem (polar Q P.e ((t : T) : V))⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  refine ⟨LinearMap.range ψ, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    change φ ((t : T) : V) ∈ W ⊓ P.perp
    rw [hφapp]
    refine Submodule.mem_inf.mpr ⟨W.sub_mem (hTW (t : T).2) (W.smul_mem _ hfW), ?_⟩
    rw [HypPair.mem_perp, polar_sub_right, polar_sub_right, polar_smul_right_eq,
      polar_smul_right_eq, P.polar_ef, P.polar_ff, hker t]
    exact ⟨by ring, by ring⟩
  · rintro _ ⟨t, rfl⟩
    change Q (φ ((t : T) : V)) = 0
    rw [hφapp, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.map_smul, P.Q_f, hT _ (t : T).2, polar_neg_right, polar_smul_right_eq,
      polar_comm Q _ P.f, hker t]
    simp
  · rw [LinearMap.finrank_range_of_inj hψinj]
    have hrank := LinearMap.finrank_range_add_finrank_ker g
    have hle : finrank K (LinearMap.range g) ≤ 1 :=
      (Submodule.finrank_le _).trans_eq (Module.finrank_self K)
    omega

theorem finrank_le_of_totallySingular_tailSpace [FiniteDimensional K V] {P : ℕ → HypPair Q}
    {r : ℕ} (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0) :
    ∀ k j : ℕ, j + k = r → ∀ T : Submodule K V, T ≤ tailSpace P j → (∀ x ∈ T, Q x = 0) →
      finrank K T ≤ k := by
  intro k
  induction k with
  | zero =>
    intro j hj T hTj hT
    rw [add_zero] at hj
    subst hj
    have hbot : T = ⊥ := (Submodule.eq_bot_iff T).mpr fun x hx => hA x (hTj hx) (hT x hx)
    rw [hbot, finrank_bot]
  | succ k ih =>
    intro j hj T hTj hT
    have hjr : j < r := by omega
    have heW : (P j).e ∈ tailSpace P j := e_mem_tailSpace hP le_rfl hjr
    have hfW : (P j).f ∈ tailSpace P j := f_mem_tailSpace hP le_rfl hjr
    have key : ∀ P' : HypPair Q, P'.perp = (P j).perp → P'.e ∈ tailSpace P j →
        P'.f ∈ tailSpace P j → P'.f ∉ T → finrank K T ≤ k + 1 := by
      intro P' hperp he hf hfT
      obtain ⟨T', hT'W, hT'Q, hdim⟩ :=
        exists_totallySingular_perp_of_not_mem P' hf hTj hT hfT
      have h' := ih (j + 1) (by omega) T' (by rw [tailSpace_succ, ← hperp]; exact hT'W) hT'Q
      omega
    by_cases hf : (P j).f ∈ T
    · have he : (P j).e ∉ T := fun he => by
        have h := polar_eq_zero_of_totallySingular hT he hf
        rw [(P j).polar_ef] at h
        exact one_ne_zero h
      let P' : HypPair Q :=
        { e := (P j).f, f := (P j).e, Q_e := (P j).Q_f, Q_f := (P j).Q_e,
          polar_ef := (P j).polar_fe }
      refine key P' ?_ hfW heW he
      ext x
      rw [HypPair.mem_perp, HypPair.mem_perp]
      exact and_comm
    · exact key (P j) rfl heW hfW hf

theorem finrank_le_of_totallySingular [FiniteDimensional K V] {P : ℕ → HypPair Q} {r : ℕ}
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j))
    (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0) {T : Submodule K V}
    (hT : ∀ x ∈ T, Q x = 0) : finrank K T ≤ r :=
  finrank_le_of_totallySingular_tailSpace hP hA r 0 (zero_add r) T
    (by rw [show tailSpace P 0 = ⊤ from rfl]; exact le_top) hT

end Witt

end CFSG.LocalAnalysis.ComponentInitial
