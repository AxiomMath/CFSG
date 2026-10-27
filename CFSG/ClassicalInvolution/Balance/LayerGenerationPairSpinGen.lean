module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame
public import CFSG.LieType.Universal.Spin.Generation.Frame
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalTransfer

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

section Eichler

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def frameOfVectors (w w' u u' : V) (hw : Q w = 0) (hw' : Q w' = 0) (hu : Q u = 0)
    (hu' : Q u' = 0) (hww' : polar Q w w' = 1) (huu' : polar Q u u' = 1) (h1 : polar Q w u = 0)
    (h2 : polar Q w u' = 0) (h3 : polar Q w' u = 0) (h4 : polar Q w' u' = 0) : Frame Q :=
  ⟨⟨w, w', hw, hw', hww'⟩, ⟨u, u', hu, hu', huu'⟩, ⟨h1, h2, h3, h4⟩⟩

theorem La_transvection_frameOfVectors (w w' u u' : V) (hw : Q w = 0) (hw' : Q w' = 0)
    (hu : Q u = 0) (hu' : Q u' = 0) (hww' : polar Q w w' = 1) (huu' : polar Q u u' = 1)
    (h1 : polar Q w u = 0) (h2 : polar Q w u' = 0) (h3 : polar Q w' u = 0)
    (h4 : polar Q w' u' = 0) (c : F) :
    (frameOfVectors w w' u u' hw hw' hu hu' hww' huu' h1 h2 h3 h4).La
        (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      eichler Q u (c • w) :=
  Frame.La_transvection_zero_one _ c

theorem map_eq_zero_of_polar_self {x : V} (h2 : (2 : F) ≠ 0) (h : polar Q x x = 0) : Q x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left h2

theorem eichler_mem_of_frames_in {m : ℕ} (F₀ : HypFrame Q m) (h2 : (2 : F) ≠ 0) {i j : Fin m}
    (hij : i ≠ j) (s : Bool) {H : Subgroup (V ≃ₗ[F] V)} {W : Submodule F V}
    (hH : ∀ fr : Frame Q, fr.e₁ ∈ W → fr.f₁ ∈ W → fr.e₂ ∈ W → fr.f₂ ∈ W → fr.La.range ≤ H)
    (hWi : F₀.vec i s ∈ W) (hWi' : F₀.vec i (!s) ∈ W) (hWj : F₀.vec j true ∈ W)
    (hWj' : F₀.vec j false ∈ W) {v : V} (hvW : v ∈ W)
    (hv : ∀ k r, polar Q v (F₀.vec k r) = 0) : eichler Q (F₀.vec i s) v ∈ H := by
  set u := F₀.vec i s with hu
  set u' := F₀.vec i (!s) with hu'
  set e := F₀.vec j true with he
  set f := F₀.vec j false with hf
  set a : F := (2 : F)⁻¹ with ha
  have h2a : 2 * a = 1 := mul_inv_cancel₀ h2
  set t : F := a * a * Q v with ht
  set m₀ : V := e - t • f with hm₀
  set e' : V := a • v + m₀ with he'
  set f'' : V := a • v - m₀ with hf''
  have Qu : Q u = 0 := F₀.map_vec i s
  have Qu' : Q u' = 0 := F₀.map_vec i (!s)
  have Qe : Q e = 0 := F₀.map_vec j true
  have Qf : Q f = 0 := F₀.map_vec j false
  have puu' : polar Q u u' = 1 := F₀.polar_vec_not i s
  have pef : polar Q e f = 1 := F₀.polar_vec_not j true
  have pee : polar Q e e = 0 := F₀.polar_vec_self j true
  have pff : polar Q f f = 0 := F₀.polar_vec_self j false
  have pfe : polar Q f e = 1 := by rw [polar_comm, pef]
  have peu : polar Q e u = 0 := F₀.polar_vec_of_ne hij.symm true s
  have peu' : polar Q e u' = 0 := F₀.polar_vec_of_ne hij.symm true (!s)
  have pfu : polar Q f u = 0 := F₀.polar_vec_of_ne hij.symm false s
  have pfu' : polar Q f u' = 0 := F₀.polar_vec_of_ne hij.symm false (!s)
  have pvu : polar Q v u = 0 := hv i s
  have pvu' : polar Q v u' = 0 := hv i (!s)
  have pve : polar Q v e = 0 := hv j true
  have pvf : polar Q v f = 0 := hv j false
  have pvv : polar Q v v = 2 * Q v := by rw [QuadraticMap.polar_self, two_nsmul, two_mul]
  have hvm : polar Q v m₀ = 0 := by
    simp only [hm₀, polar_sub_right, polar_smul_right, pve, pvf, smul_eq_mul]
    ring
  have hmv : polar Q m₀ v = 0 := by rw [polar_comm, hvm]
  have pmf : polar Q m₀ f = 1 := by
    simp only [hm₀, polar_sub_left, polar_smul_left, pef, pff, smul_eq_mul]
    ring
  have pfm : polar Q f m₀ = 1 := by rw [polar_comm, pmf]
  have pmu : polar Q m₀ u = 0 := by
    simp only [hm₀, polar_sub_left, polar_smul_left, peu, pfu, smul_eq_mul]
    ring
  have pmu' : polar Q m₀ u' = 0 := by
    simp only [hm₀, polar_sub_left, polar_smul_left, peu', pfu', smul_eq_mul]
    ring
  have pm₀ : polar Q m₀ m₀ = -(2 * t) := by
    simp only [hm₀, polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right, pee, pff,
      pef, pfe, smul_eq_mul]
    ring
  have pe'e' : polar Q e' e' = 0 := by
    simp only [he', polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, pvv,
      smul_eq_mul]
    rw [hvm, hmv, pm₀, ht]
    ring
  have pf''f'' : polar Q f'' f'' = 0 := by
    simp only [hf'', polar_sub_left, polar_sub_right, polar_smul_left, polar_smul_right, pvv,
      smul_eq_mul]
    rw [hvm, hmv, pm₀, ht]
    ring
  have Qe' : Q e' = 0 := map_eq_zero_of_polar_self h2 pe'e'
  have Qf'' : Q f'' = 0 := map_eq_zero_of_polar_self h2 pf''f''
  have hsum : e' + f'' = v := by
    have : e' + f'' = (a + a) • v := by
      simp only [he', hf'']
      module
    rw [this, ← two_mul, h2a, one_smul]
  have pe'f : polar Q e' f = 1 := by
    simp only [he', polar_add_left, polar_smul_left, pvf, pmf, smul_eq_mul]
    ring
  have pe'u : polar Q e' u = 0 := by
    simp only [he', polar_add_left, polar_smul_left, pvu, pmu, smul_eq_mul]
    ring
  have pe'u' : polar Q e' u' = 0 := by
    simp only [he', polar_add_left, polar_smul_left, pvu', pmu', smul_eq_mul]
    ring
  have pf''f : polar Q f'' f = -1 := by
    simp only [hf'', polar_sub_left, polar_smul_left, pvf, pmf, smul_eq_mul]
    ring
  have pf''u : polar Q f'' u = 0 := by
    simp only [hf'', polar_sub_left, polar_smul_left, pvu, pmu, smul_eq_mul]
    ring
  have pf''u' : polar Q f'' u' = 0 := by
    simp only [hf'', polar_sub_left, polar_smul_left, pvu', pmu', smul_eq_mul]
    ring
  have Qnf : Q (-f) = 0 := by rw [QuadraticMap.map_neg, Qf]
  let frA : Frame Q := frameOfVectors e' f u u' Qe' Qf Qu Qu' pe'f puu' pe'u pe'u' pfu pfu'
  let frB : Frame Q := frameOfVectors f'' (-f) u u' Qf'' Qnf Qu Qu' (by rw [polar_neg_right, pf''f,
    neg_neg]) puu' pf''u pf''u' (by rw [polar_neg_left, pfu, neg_zero])
    (by rw [polar_neg_left, pfu', neg_zero])
  have hWe' : e' ∈ W :=
    W.add_mem (W.smul_mem a hvW) (W.sub_mem hWj (W.smul_mem t hWj'))
  have hWf'' : f'' ∈ W :=
    W.sub_mem (W.smul_mem a hvW) (W.sub_mem hWj (W.smul_mem t hWj'))
  have hLA : frA.La.range ≤ H := hH frA hWe' hWj' hWi hWi'
  have hLB : frB.La.range ≤ H := hH frB hWf'' (W.neg_mem hWj') hWi hWi'
  have hA : eichler Q u ((1 : F) • e') ∈ H := by
    have := hLA ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1, rfl⟩
    rw [Frame.La_transvection_zero_one] at this
    exact this
  have hB : eichler Q u ((1 : F) • f'') ∈ H := by
    have := hLB ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1, rfl⟩
    rw [Frame.La_transvection_zero_one] at this
    exact this
  have hmul : eichler Q u ((1 : F) • e') * eichler Q u ((1 : F) • f'') = eichler Q u v := by
    rw [eichler_mul (by rw [one_smul, polar_comm]; exact pe'u)
      (by rw [one_smul, polar_comm]; exact pf''u), one_smul, one_smul, hsum]
  rw [← hmul]
  exact H.mul_mem hA hB

theorem eichler_mem_of_fixed {m : ℕ} (F₀ : HypFrame Q m) (h2 : (2 : F) ≠ 0) {i j : Fin m}
    (hij : i ≠ j) (s : Bool) {H : Subgroup (V ≃ₗ[F] V)} {T : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hH : ∀ fr : Frame Q, (∀ A : SL(2, F), T * fr.La A = fr.La A * T) → fr.La.range ≤ H)
    (hTi : T (F₀.vec i s) = F₀.vec i s) (hTi' : T (F₀.vec i (!s)) = F₀.vec i (!s))
    (hTj : T (F₀.vec j true) = F₀.vec j true) (hTj' : T (F₀.vec j false) = F₀.vec j false) {v : V}
    (hTv : T v = v) (hv : ∀ k r, polar Q v (F₀.vec k r) = 0) :
    eichler Q (F₀.vec i s) v ∈ H := by
  refine eichler_mem_of_frames_in F₀ h2 hij s
    (W := LinearMap.eqLocus (T : V →ₗ[F] V) LinearMap.id) (fun fr h1 h2' h3 h4 => hH fr fun A => ?_)
    hTi hTi' hTj hTj' hTv hv
  have h11 : (1 : F) * 1 = 1 := mul_one 1
  have hsmul : ∀ Y, T (fr.incl Y) = (1 : F) • fr.incl Y := fun Y =>
    incl_smul_of_vectors fr (by rw [one_smul]; exact h1) (by rw [one_smul]; exact h2')
      (by rw [one_smul]; exact h3) (by rw [one_smul]; exact h4) Y
  exact comm_La_of_smul fr hT h11 hsmul A

theorem elementaryGroup_le_of_pairs {m : ℕ} (F₀ : HypFrame Q m) (h2 : (2 : F) ≠ 0)
    {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d)
    (hrest : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → Q v = 0 → v = 0)
    {H : Subgroup (V ≃ₗ[F] V)}
    (hH : ∀ fr : Frame Q,
      ((∀ A : SL(2, F), (F₀.toFrame hab true true).La (-1) * fr.La A =
          fr.La A * (F₀.toFrame hab true true).La (-1)) ∨
        (∀ A : SL(2, F), (F₀.toFrame hcd true true).La (-1) * fr.La A =
          fr.La A * (F₀.toFrame hcd true true).La (-1)) ∨
        (∀ A : SL(2, F), ((F₀.toFrame hab true true).La (-1) *
            (F₀.toFrame hcd true true).La (-1)) * fr.La A =
          fr.La A * ((F₀.toFrame hab true true).La (-1) *
            (F₀.toFrame hcd true true).La (-1)))) → fr.La.range ≤ H) :
    elementaryGroup Q ≤ H := by
  set T₁ := (F₀.toFrame hab true true).La (-1) with hT₁
  set T₂ := (F₀.toFrame hcd true true).La (-1) with hT₂
  have hO₁ : T₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Frame.La_mem_orthogonalGroup _ _
  have hO₂ : T₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Frame.La_mem_orthogonalGroup _ _
  have hfix₁ : ∀ k r, ¬ (k = a ∨ k = b) → T₁ (F₀.vec k r) = F₀.vec k r := fun k r hk => by
    rw [hT₁, La_neg_one_toFrame_vec, ite_eq_right hk, one_smul]
  have hfix₂ : ∀ k r, ¬ (k = c ∨ k = d) → T₂ (F₀.vec k r) = F₀.vec k r := fun k r hk => by
    rw [hT₂, La_neg_one_toFrame_vec, ite_eq_right hk, one_smul]
  have hvfix₁ : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → T₁ v = v := fun v hv => by
    refine La_neg_one_of_mem_perp _ ?_
    rw [Frame.mem_perp_iff]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Frame.coords_apply, HypFrame.toFrame, hv]
  have hvfix₂ : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → T₂ v = v := fun v hv => by
    refine La_neg_one_of_mem_perp _ ?_
    rw [Frame.mem_perp_iff]
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Frame.coords_apply, HypFrame.toFrame, hv]
  have hH₁ : ∀ fr : Frame Q, (∀ A : SL(2, F), T₁ * fr.La A = fr.La A * T₁) → fr.La.range ≤ H :=
    fun fr h => hH fr (Or.inl h)
  have hH₂ : ∀ fr : Frame Q, (∀ A : SL(2, F), T₂ * fr.La A = fr.La A * T₂) → fr.La.range ≤ H :=
    fun fr h => hH fr (Or.inr (Or.inl h))
  refine F₀.elementaryGroup_le (H := H) ?_ ?_ hrest
  · intro i j hij s t c
    have := hH _ (exists_comm_toFrame_of_pairs F₀ hab hcd hij s t)
      ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c, rfl⟩
    rw [Frame.La_transvection_zero_one] at this
    exact this
  · intro i s v hv
    by_cases hia : i = a
    · subst hia
      have h1 : ¬ (i = c ∨ i = d) := by
        rintro (h | h)
        exacts [hac h, had h]
      have h2' : ¬ (b = c ∨ b = d) := by
        rintro (h | h)
        exacts [hbc h, hbd h]
      exact eichler_mem_of_fixed F₀ h2 hab s hO₂ hH₂ (hfix₂ _ _ h1) (hfix₂ _ _ h1)
        (hfix₂ _ _ h2') (hfix₂ _ _ h2') (hvfix₂ v hv) hv
    by_cases hib : i = b
    · subst hib
      have h1 : ¬ (i = c ∨ i = d) := by
        rintro (h | h)
        exacts [hbc h, hbd h]
      have h2' : ¬ (a = c ∨ a = d) := by
        rintro (h | h)
        exacts [hac h, had h]
      exact eichler_mem_of_fixed F₀ h2 (Ne.symm hab) s hO₂ hH₂ (hfix₂ _ _ h1) (hfix₂ _ _ h1)
        (hfix₂ _ _ h2') (hfix₂ _ _ h2') (hvfix₂ v hv) hv
    have hi1 : ¬ (i = a ∨ i = b) := by
      rintro (h | h)
      exacts [hia h, hib h]
    by_cases hic : i = c
    · subst hic
      have h2' : ¬ (d = a ∨ d = b) := by
        rintro (h | h)
        exacts [had h.symm, hbd h.symm]
      exact eichler_mem_of_fixed F₀ h2 hcd s hO₁ hH₁ (hfix₁ _ _ hi1) (hfix₁ _ _ hi1)
        (hfix₁ _ _ h2') (hfix₁ _ _ h2') (hvfix₁ v hv) hv
    by_cases hid : i = d
    · subst hid
      have h2' : ¬ (c = a ∨ c = b) := by
        rintro (h | h)
        exacts [hac h.symm, hbc h.symm]
      exact eichler_mem_of_fixed F₀ h2 (Ne.symm hcd) s hO₁ hH₁ (hfix₁ _ _ hi1) (hfix₁ _ _ hi1)
        (hfix₁ _ _ h2') (hfix₁ _ _ h2') (hvfix₁ v hv) hv
    have h2' : ¬ (c = a ∨ c = b) := by
      rintro (h | h)
      exacts [hac h.symm, hbc h.symm]
    exact eichler_mem_of_fixed F₀ h2 hic s hO₁ hH₁ (hfix₁ _ _ hi1) (hfix₁ _ _ hi1)
      (hfix₁ _ _ h2') (hfix₁ _ _ h2') (hvfix₁ v hv) hv

end Eichler

section Main

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

omit [Finite F] [FiniteDimensional F V] in
theorem eq_top_of_frames_all [Nontrivial V] (h2 : (2 : F) ≠ 0) {m : ℕ} (F₀ : HypFrame Q m)
    (hm : 2 ≤ m) (hrest : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → Q v = 0 → v = 0)
    (hperfK : Group.IsPerfect (spinGroup Q)) (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (N : Subgroup (spinGroup Q)) (hN : ∀ fr : Frame Q, fr.La.range ≤ N.map (spinAction Q)) :
    N = ⊤ := by
  have := hperfK
  have hlong : ∀ {i j : Fin m}, i ≠ j → ∀ (s t : Bool) (c : F),
      eichler Q (F₀.vec j t) (c • F₀.vec i s) ∈ N.map (spinAction Q) := by
    intro i j hij s t c
    have := hN (F₀.toFrame hij s t)
      ⟨Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c, rfl⟩
    rw [Frame.La_transvection_zero_one] at this
    exact this
  have hperp : ∀ (i : Fin m) (s : Bool) (v : V), (∀ k r, polar Q v (F₀.vec k r) = 0) →
      eichler Q (F₀.vec i s) v ∈ N.map (spinAction Q) := by
    intro i s v hv
    let a₀ : Fin m := ⟨0, by omega⟩
    let a₁ : Fin m := ⟨1, by omega⟩
    have h01 : a₀ ≠ a₁ := fun h => by simpa [a₀, a₁] using congrArg Fin.val h
    by_cases hi : i = a₀
    · exact eichler_mem_of_frames_in F₀ h2 (j := a₁) (hi ▸ h01) s (W := ⊤)
        (fun fr _ _ _ _ => hN fr) trivial trivial trivial trivial trivial hv
    · exact eichler_mem_of_frames_in F₀ h2 (j := a₀) hi s (W := ⊤)
        (fun fr _ _ _ _ => hN fr) trivial trivial trivial trivial trivial hv
  have hEH : elementaryGroup Q ≤ N.map (spinAction Q) :=
    F₀.elementaryGroup_le (H := N.map (spinAction Q)) hlong hperp hrest
  exact eq_top_of_range_le_map (spinAction Q) (ker_spinAction_le_center Q) (hrange.trans hEH)

omit [Finite F] [FiniteDimensional F V] in
theorem eq_top_of_frames_pairs [Nontrivial V] (h2 : (2 : F) ≠ 0) {m : ℕ} (F₀ : HypFrame Q m)
    {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hrest : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → Q v = 0 → v = 0)
    (hperfK : Group.IsPerfect (spinGroup Q)) (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (N : Subgroup (spinGroup Q)) (x : spinGroup Q)
    (hN : ∀ fr : Frame Q,
      ((∀ A : SL(2, F), (F₀.toFrame hab true true).La (-1) * fr.La A =
          fr.La A * (F₀.toFrame hab true true).La (-1)) ∨
        (∀ A : SL(2, F), (F₀.toFrame hcd true true).La (-1) * fr.La A =
          fr.La A * (F₀.toFrame hcd true true).La (-1)) ∨
        (∀ A : SL(2, F), ((F₀.toFrame hab true true).La (-1) *
            (F₀.toFrame hcd true true).La (-1)) * fr.La A =
          fr.La A * ((F₀.toFrame hab true true).La (-1) *
            (F₀.toFrame hcd true true).La (-1)))) →
      ∀ A : SL(2, F), spinAction Q x * fr.La A * (spinAction Q x)⁻¹ ∈ N.map (spinAction Q)) :
    N = ⊤ := by
  have := hperfK
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  set θx : V ≃ₗ[F] V := spinAction Q x with hθx
  let H : Subgroup (V ≃ₗ[F] V) := (N.map (spinAction Q)).map (MulAut.conj θx⁻¹).toMonoidHom
  have hEH : elementaryGroup Q ≤ H :=
    elementaryGroup_le_of_pairs F₀ h2 hab hcd hac had hbc hbd hrest (H := H) fun fr hfr => by
      rintro _ ⟨A, rfl⟩
      refine ⟨θx * fr.La A * θx⁻¹, hN fr hfr A, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have hrangeN : (spinAction Q).range ≤ N.map (spinAction Q) := by
    intro g hg
    have hθxE : θx ∈ elementaryGroup Q := hrange ⟨x, rfl⟩
    have hgE : θx⁻¹ * g * θx ∈ elementaryGroup Q :=
      (elementaryGroup Q).mul_mem ((elementaryGroup Q).mul_mem
        ((elementaryGroup Q).inv_mem hθxE) (hrange hg)) hθxE
    obtain ⟨t, ht, hteq⟩ := hEH hgE
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hteq
    have : t = g := by
      have h1 : θx * (θx⁻¹ * t * θx) * θx⁻¹ = θx * (θx⁻¹ * g * θx) * θx⁻¹ := by rw [hteq]
      simpa [mul_assoc] using h1
    rw [← this]
    exact ht
  exact eq_top_of_range_le_map (spinAction Q) hker hrangeN

omit [Finite F] in
theorem false_of_four_pairs [Invertible (2 : F)] (F₀ : HypFrame Q 3)
    (hrest : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → Q v = 0 → v = 0)
    (P : Fin 4 → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) : False := by
  have hv : IsHypFam Q (fun (i : Fin 3) s => F₀.vec i s) :=
    ⟨fun i s => F₀.map_vec i s, fun i j hij s t => F₀.polar_vec_of_ne hij s t,
      fun i s => F₀.polar_vec_not i s⟩
  have hv' : IsHypFam Q (hypPairFam fun i : Fin 3 => P (Fin.castSucc i)) :=
    isHypFam_hypPairFam _ fun i j hij => hP _ _ fun h => hij (Fin.castSucc_injective _ h)
  obtain ⟨ω, hω, hωv⟩ := exists_isometry_of_isHypFam hv hv'
  have hωinv : ω.symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hω
  have h3 : ∀ k : Fin 3, (3 : Fin 4) ≠ Fin.castSucc k := fun k h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hu : ω.symm (P 3).e = 0 := by
    apply hrest
    · intro k r
      have h1 : ω.symm (ω (F₀.vec k r)) = F₀.vec k r := ω.symm_apply_apply _
      rw [← h1, polar_map_of_mem hωinv, hωv k r]
      cases r
      · exact (hP _ _ (h3 k)).ef
      · exact (hP _ _ (h3 k)).ee
    · rw [map_of_mem hωinv]
      exact (P 3).Q_e
  have : (P 3).e = 0 := by
    have := congrArg ω hu
    simpa using this
  exact (P 3).e_ne_zero this

theorem frames_of_single_class [Nontrivial V] (hodd : Odd (Nat.card F)) (hQ : Q.Nondegenerate)
    (𝓕 : Set (Subgroup (spinGroup Q))) (R₀ : Subgroup (spinGroup Q)) (fr₀ : Frame Q)
    (hR₀ : R₀.map (spinAction Q) = fr₀.La.range) (hperp : 2 ≤ Module.finrank F fr₀.perp)
    (hconj : ∀ y : spinGroup Q, Generic.conjSub y R₀ ∈ 𝓕)
    (hsingle : ∀ R ∈ 𝓕, ∃ y : spinGroup Q, R = Generic.conjSub y R₀) :
    (∀ R ∈ 𝓕, ∃ fr : Frame Q, R.map (spinAction Q) = fr.La.range) ∧
      ∀ fr : Frame Q, ∃ R ∈ 𝓕, R.map (spinAction Q) = fr.La.range := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hQ' : (polarBilin Q).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have himg : ∀ y : spinGroup Q, (Generic.conjSub y R₀).map (spinAction Q) =
      fr₀.La.range.map (MulAut.conj (spinAction Q y)).toMonoidHom := fun y => by
    rw [Generic.conjSub, map_conj_map, hR₀]
  refine ⟨fun R hR => ?_, fun fr => ?_⟩
  · obtain ⟨y, rfl⟩ := hsingle R hR
    have hθ : spinAction Q y ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q y)
    refine ⟨fr₀.map hθ, ?_⟩
    rw [himg y]
    exact (La_range_eq_map_conj fun A => Frame.map_La fr₀ hθ A).symm
  · obtain ⟨y, hy⟩ := exists_spin_conj hodd hQ' fr₀ fr hperp
    refine ⟨Generic.conjSub y R₀, hconj y, ?_⟩
    rw [himg y]
    exact (La_range_eq_map_conj hy).symm

theorem commutingGeneration_spin [Nontrivial V] (hodd : Odd (Nat.card F)) (hQ : Q.Nondegenerate)
    {m : ℕ} (F₀ : HypFrame Q m) (hm : 3 ≤ m)
    (hrest : ∀ v : V, (∀ k r, polar Q v (F₀.vec k r) = 0) → Q v = 0 → v = 0)
    (hperfK : Group.IsPerfect (spinGroup Q)) (hrange : (spinAction Q).range ≤ elementaryGroup Q)
    (𝓕 : Set (Subgroup (spinGroup Q)))
    (hframe : ∀ R ∈ 𝓕, ∃ fr : Frame Q, R.map (spinAction Q) = fr.La.range)
    (hlift : ∀ fr : Frame Q, ∃ R ∈ 𝓕, R.map (spinAction Q) = fr.La.range)
    (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R) : CommutingGeneration 𝓕 := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  set Big : Subgroup (spinGroup Q) := ⨆ R ∈ 𝓕, ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set _) ∨
    R ≤ Subgroup.centralizer ({c₂} : Set _) ∨ R ≤ Subgroup.centralizer ({c₁ * c₂} : Set _)), R
    with hBig
  have hmemBig : ∀ R ∈ 𝓕, (R ≤ Subgroup.centralizer ({c₁} : Set _) ∨
      R ≤ Subgroup.centralizer ({c₂} : Set _) ∨ R ≤ Subgroup.centralizer ({c₁ * c₂} : Set _)) →
      R ≤ Big := fun R hR hc => le_iSup₂_of_le R hR (le_iSup_of_le hc le_rfl)
  have hcentBig : ∀ (c : spinGroup Q), (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) → ∀ fr : Frame Q,
      (∀ A : SL(2, F), spinAction Q c * fr.La A = fr.La A * spinAction Q c) →
      fr.La.range ≤ Big.map (spinAction Q) := by
    intro c hc fr hfr
    obtain ⟨R, hR, hRfr⟩ := hlift fr
    have hRc : R ≤ Subgroup.centralizer ({c} : Set _) := by
      have hmem : c ∈ Subgroup.centralizer (R : Set (spinGroup Q)) :=
        Models.Transfer.mem_centralizer_of_map (θ := spinAction Q) hker (hperf R hR) (by
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rw [hRfr] at ht
          obtain ⟨A, rfl⟩ := ht
          exact (hfr A).symm)
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hmem y hy)
    have hRBig : R ≤ Big := by
      rcases hc with rfl | rfl | rfl
      · exact hmemBig R hR (Or.inl hRc)
      · exact hmemBig R hR (Or.inr (Or.inl hRc))
      · exact hmemBig R hR (Or.inr (Or.inr hRc))
    rw [← hRfr]
    exact Subgroup.map_mono hRBig
  have hcentral : ∀ c : spinGroup Q, (c = c₁ ∨ c = c₂ ∨ c = c₁ * c₂) → spinAction Q c = 1 →
      (⊤ : Subgroup (spinGroup Q)) ≤ Big := fun c hc hθ => by
    have := eq_top_of_frames_all h2 F₀ (by omega) hrest hperfK hrange Big fun fr =>
      hcentBig c hc fr fun B => by rw [hθ, one_mul, mul_one]
    rw [this]
  by_cases hθ₁ : spinAction Q c₁ = 1
  · exact hcentral c₁ (Or.inl rfl) hθ₁
  by_cases hθ₂ : spinAction Q c₂ = 1
  · exact hcentral c₂ (Or.inr (Or.inl rfl)) hθ₂
  by_cases hθ₁₂ : spinAction Q (c₁ * c₂) = 1
  · exact hcentral (c₁ * c₂) (Or.inr (Or.inr rfl)) hθ₁₂
  obtain ⟨fr₁, hfr₁⟩ := hframe R₁ hR₁
  obtain ⟨fr₂, hfr₂⟩ := hframe R₂ hR₂
  have hi₁ : spinAction Q c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction Q c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  have hne : fr₂.La (-1) ≠ fr₁.La (-1) := fun h => hθ₁₂ (by
    rw [map_mul, hi₁, hi₂, h, ← map_mul, neg_mul_neg, one_mul, map_one])
  have hc : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
    rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hx₂₁ c₁ hc₁]
  have hcent : ∀ A : SL(2, F), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
    intro A
    obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction Q) := hfr₁ ▸ ⟨A, rfl⟩
    rw [← hi₂, ← hrA, ← map_mul, ← map_mul, hx₂₁ r hr]
  have horth : ∀ X Y, polar Q (fr₁.incl X) (fr₂.incl Y) = 0 :=
    (Frame.orth_or_eq h2 hc hcent).resolve_right hne
  have hm4 : 4 ≤ m := by
    by_contra hlt
    obtain rfl : m = 3 := by omega
    exact false_of_four_pairs F₀ hrest _ (frames_pairs_pairwise_orth horth)
  let a₀ : Fin m := ⟨0, by omega⟩
  let a₁ : Fin m := ⟨1, by omega⟩
  let a₂ : Fin m := ⟨2, by omega⟩
  let a₃ : Fin m := ⟨3, by omega⟩
  have h01 : a₀ ≠ a₁ := fun h => by simpa [a₀, a₁] using congrArg Fin.val h
  have h23 : a₂ ≠ a₃ := fun h => by simpa [a₂, a₃] using congrArg Fin.val h
  have h02 : a₀ ≠ a₂ := fun h => by simpa [a₀, a₂] using congrArg Fin.val h
  have h03 : a₀ ≠ a₃ := fun h => by simpa [a₀, a₃] using congrArg Fin.val h
  have h12 : a₁ ≠ a₂ := fun h => by simpa [a₁, a₂] using congrArg Fin.val h
  have h13 : a₁ ≠ a₃ := fun h => by simpa [a₁, a₃] using congrArg Fin.val h
  obtain ⟨x, hx₁, hx₂⟩ := exists_spin_conj_orth_pair hodd hQ (F₀.toFrame h01 true true)
    (F₀.toFrame h23 true true) fr₁ fr₂
    (polar_incl_toFrame_of_disjoint F₀ h01 h23 h02 h03 h12 h13 true true true true) horth
  have hθxO : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)
  have hfin := eq_top_of_frames_pairs h2 F₀ h01 h23 h02 h03 h12 h13 hrest hperfK hrange Big x
    fun fr hfr A => by
      have hconj : ∀ (T L : V ≃ₗ[F] V), T * L = L * T →
          (spinAction Q x * T * (spinAction Q x)⁻¹) * (spinAction Q x * L * (spinAction Q x)⁻¹) =
            (spinAction Q x * L * (spinAction Q x)⁻¹) * (spinAction Q x * T * (spinAction Q x)⁻¹) :=
        by
        intro T L h
        calc (spinAction Q x * T * (spinAction Q x)⁻¹) * (spinAction Q x * L * (spinAction Q x)⁻¹)
            = spinAction Q x * (T * L) * (spinAction Q x)⁻¹ := by group
          _ = spinAction Q x * (L * T) * (spinAction Q x)⁻¹ := by rw [h]
          _ = (spinAction Q x * L * (spinAction Q x)⁻¹) *
              (spinAction Q x * T * (spinAction Q x)⁻¹) := by group
      have hmapLa : ∀ B : SL(2, F),
          (fr.map hθxO).La B = spinAction Q x * fr.La B * (spinAction Q x)⁻¹ :=
        fun B => Frame.map_La fr hθxO B
      rw [← hmapLa A]
      rcases hfr with hT | hT | hT
      · exact hcentBig c₁ (Or.inl rfl) _ (fun B => by
          rw [hi₁, ← hx₁, hmapLa B]
          exact hconj _ _ (hT B)) ⟨A, rfl⟩
      · exact hcentBig c₂ (Or.inr (Or.inl rfl)) _ (fun B => by
          rw [hi₂, ← hx₂, hmapLa B]
          exact hconj _ _ (hT B)) ⟨A, rfl⟩
      · refine hcentBig (c₁ * c₂) (Or.inr (Or.inr rfl)) _ (fun B => ?_) ⟨A, rfl⟩
        have : spinAction Q (c₁ * c₂) = spinAction Q x * ((F₀.toFrame h01 true true).La (-1) *
            (F₀.toFrame h23 true true).La (-1)) * (spinAction Q x)⁻¹ := by
          rw [map_mul, hi₁, hi₂, ← hx₁, ← hx₂]
          group
        rw [this, hmapLa B]
        exact hconj _ _ (hT B)
  rw [hfin]

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
