module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutToral

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped Matrix MatrixGroups

section Compl

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {m : ℕ} (Fr : HypFrame Q m)

theorem torus_vec_gen {a b : Fin m} (hab : a ≠ b) (s t : Bool) (u : Fˣ) (n : Fin m) (r : Bool) :
    spinAction Q (Fr.longTorus hab s t u) (Fr.vec n r) =
      ((u : F) ^ longCoroot a b s t n r) • Fr.vec n r := by
  rw [Fr.spinAction_longTorus_vec, Units.val_zpow_eq_zpow_val]

theorem longCoroot_bounds_gen {a b : Fin m} (hab : a ≠ b) (s t : Bool) (n : Fin m) (r : Bool) :
    -1 ≤ longCoroot a b s t n r ∧ longCoroot a b s t n r ≤ 1 := by
  by_cases h1 : n = a
  · subst h1
    simp [longCoroot, hab]
    split_ifs <;> omega
  · by_cases h2 : n = b
    · subst h2
      simp [longCoroot, h1]
      split_ifs <;> omega
    · simp [longCoroot, h1, h2]

theorem torus_fix_of_orth {a b : Fin m} (hab : a ≠ b) (s t : Bool) (u : Fˣ) {y : V}
    (hy : ∀ c r, polar Q y (Fr.vec c r) = 0) :
    spinAction Q (Fr.longTorus hab s t u) y = y := by
  rw [Fr.spinAction_longTorus hab s t u y]
  simp [hy]

theorem eta_eq_one_gen (h2 : (2 : F) ≠ 0) (g : V →ₗ[F] V) (hg : Function.Injective g) {u : Fˣ}
    (hu2 : (u : F) ≠ -1) {a b : Fin m} (hab : a ≠ b) (s t : Bool) {η : F}
    (hη : η = 1 ∨ η = -1)
    (hcomm : ∀ x, g (spinAction Q (Fr.longTorus hab s t u) x) =
      η • spinAction Q (Fr.longTorus hab s t u) (g x))
    {j : Fin m} (hja : j ≠ a) (hjb : j ≠ b) : η = 1 := by
  rcases hη with rfl | rfl
  · rfl
  exfalso
  set T := spinAction Q (Fr.longTorus hab s t u) with hT
  have hv0 : T (Fr.vec j true) = Fr.vec j true := by
    rw [hT, torus_vec_gen Fr hab s t u j true]
    simp [longCoroot, hja, hjb]
  have h1 := hcomm (Fr.vec j true)
  rw [hv0, neg_one_smul] at h1
  have hy : T (g (Fr.vec j true)) = (-1 : F) • g (Fr.vec j true) := by
    rw [neg_one_smul]
    have := congrArg Neg.neg h1
    rw [neg_neg] at this
    exact this.symm
  have horth : ∀ n r, polar Q (g (Fr.vec j true)) (Fr.vec n r) = 0 := by
    intro n r
    refine polar_eq_zero_of_eigen (τ := T) (fun x => map_spinAction Q _ x) hy
      (torus_vec_gen Fr hab s t u n r) ?_
    have := zpow_ne_neg_one h2 hu2 (longCoroot_bounds_gen hab s t n r)
    intro h
    exact this (by linear_combination -h)
  have hfix : T (g (Fr.vec j true)) = g (Fr.vec j true) := torus_fix_of_orth Fr hab s t u horth
  have h3 : g (Fr.vec j true) = 0 := by
    have h4 : (2 : F) • g (Fr.vec j true) = 0 := by
      have h5 : (-1 : F) • g (Fr.vec j true) = g (Fr.vec j true) := by rw [← hy]; exact hfix
      calc (2 : F) • g (Fr.vec j true) = g (Fr.vec j true) - (-1 : F) • g (Fr.vec j true) := by
            module
        _ = 0 := by rw [h5, sub_self]
    exact (smul_eq_zero.mp h4).resolve_left h2
  exact polar_vec_ne_zero Fr j true (hg (by rw [h3, map_zero]))

theorem polar_g_vec_eq_zero_gen (g : V →ₗ[F] V) {u : Fˣ} (hu1 : (u : F) ≠ 1)
    (hu2 : (u : F) ≠ -1) {a b : Fin m} (hab : a ≠ b) (s t : Bool)
    (hcomm : ∀ x, g (spinAction Q (Fr.longTorus hab s t u) x) =
      spinAction Q (Fr.longTorus hab s t u) (g x)) (s' : Bool) (n : Fin m) (r : Bool)
    (hw : longCoroot a b s t n r + longCoroot a b s t a s' ≠ 0) :
    polar Q (g (Fr.vec a s')) (Fr.vec n r) = 0 := by
  set T := spinAction Q (Fr.longTorus hab s t u) with hT
  have hy : T (g (Fr.vec a s')) = ((u : F) ^ longCoroot a b s t a s') • g (Fr.vec a s') := by
    rw [← hcomm, hT, torus_vec_gen Fr hab s t u a s', map_smul]
  refine polar_eq_zero_of_eigen (τ := T) (fun x => map_spinAction Q _ x) hy
    (torus_vec_gen Fr hab s t u n r) ?_
  intro h
  rw [← zpow_add₀ u.ne_zero] at h
  have hb1 := longCoroot_bounds_gen hab s t a s'
  have hb2 := longCoroot_bounds_gen hab s t n r
  have := (zpow_eq_one_iff_of_abs_le hu1 hu2 (w := longCoroot a b s t a s' +
    longCoroot a b s t n r) (by omega)).mp h
  exact hw (by omega)

theorem orth_sub_smul_vec {x : V} (i : Fin m) (s : Bool)
    (hx : ∀ a r, (a, r) ≠ (i, !s) → polar Q x (Fr.vec a r) = 0) (a : Fin m) (r : Bool) :
    polar Q (x - polar Q x (Fr.vec i (!s)) • Fr.vec i s) (Fr.vec a r) = 0 := by
  rw [polar_sub_left, polar_smul_left, Fr.polar_vec_vec, smul_eq_mul]
  by_cases h : i = a ∧ s = !r
  · obtain ⟨h1, h2⟩ := h
    subst h1
    have hr : r = !s := by rw [h2]; simp
    subst hr
    simp
  · have hne : (a, r) ≠ (i, !s) := fun hh => h ⟨(Prod.ext_iff.mp hh).1.symm, by
      have hr : r = !s := (Prod.ext_iff.mp hh).2
      rw [hr]; simp⟩
    rw [ite_eq_right h, mul_zero, sub_zero, hx a r hne]

theorem exists_smul_vec_of_torus_pair (h2 : (2 : F) ≠ 0) (g : V →ₗ[F] V)
    (hg : Function.Injective g) {u : Fˣ} (hu1 : (u : F) ≠ 1) (hu2 : (u : F) ≠ -1)
    {i k j : Fin m} (hik : i ≠ k) (hji : j ≠ i) (hjk : j ≠ k)
    (hc₁ : ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x,
      g (spinAction Q (Fr.longTorus hik true false u) x) =
        η • spinAction Q (Fr.longTorus hik true false u) (g x))
    (hc₂ : ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x,
      g (spinAction Q (Fr.longTorus hik true true u) x) =
        η • spinAction Q (Fr.longTorus hik true true u) (g x)) (s : Bool) :
    ∃ c : F, g (Fr.vec i s) = c • Fr.vec i s := by
  obtain ⟨η₁, hη₁, hcomm₁⟩ := hc₁
  obtain ⟨η₂, hη₂, hcomm₂⟩ := hc₂
  have e1 := eta_eq_one_gen Fr h2 g hg hu2 hik true false hη₁ hcomm₁ hji hjk
  have e2 := eta_eq_one_gen Fr h2 g hg hu2 hik true true hη₂ hcomm₂ hji hjk
  subst e1 e2
  simp only [one_smul] at hcomm₁ hcomm₂
  have hx : ∀ n r, (n, r) ≠ (i, !s) → polar Q (g (Fr.vec i s)) (Fr.vec n r) = 0 := by
    intro n r hnr
    by_contra hne
    have w1 : longCoroot i k true false n r + longCoroot i k true false i s = 0 := by
      by_contra h
      exact hne (polar_g_vec_eq_zero_gen Fr g hu1 hu2 hik true false hcomm₁ s n r h)
    have w2 : longCoroot i k true true n r + longCoroot i k true true i s = 0 := by
      by_contra h
      exact hne (polar_g_vec_eq_zero_gen Fr g hu1 hu2 hik true true hcomm₂ s n r h)
    by_cases hn : n = i
    · subst hn
      apply hnr
      cases r <;> cases s <;> simp [longCoroot, hik] at w1 ⊢
    · by_cases hnk : n = k
      · subst hnk
        cases r <;> cases s <;> simp [longCoroot, hik, hn] at w1 w2
      · simp [longCoroot, hn, hnk, hik] at w1
        cases s <;> simp at w1
  have horth := orth_sub_smul_vec Fr i s hx
  set c := polar Q (g (Fr.vec i s)) (Fr.vec i (!s)) with hc
  set y := g (Fr.vec i s) - c • Fr.vec i s with hy
  refine ⟨c, ?_⟩
  have hyT : spinAction Q (Fr.longTorus hik true false u) y = y :=
    torus_fix_of_orth Fr hik true false u horth
  have hxT : spinAction Q (Fr.longTorus hik true false u) (g (Fr.vec i s)) =
      ((u : F) ^ longCoroot i k true false i s) • g (Fr.vec i s) := by
    rw [← hcomm₁, torus_vec_gen Fr hik true false u i s, map_smul]
  have hvT : spinAction Q (Fr.longTorus hik true false u) (Fr.vec i s) =
      ((u : F) ^ longCoroot i k true false i s) • Fr.vec i s :=
    torus_vec_gen Fr hik true false u i s
  have hdecomp : g (Fr.vec i s) = c • Fr.vec i s + y := by rw [hy]; abel
  have hy0 : y = 0 := by
    have h1 : spinAction Q (Fr.longTorus hik true false u) (g (Fr.vec i s)) =
        c • (((u : F) ^ longCoroot i k true false i s) • Fr.vec i s) + y := by
      rw [hdecomp, map_add, map_smul, hvT, hyT]
    rw [hxT, hdecomp, smul_add, smul_smul, smul_smul, mul_comm] at h1
    have h3 : (((u : F) ^ longCoroot i k true false i s) - 1) • y = 0 := by
      rw [sub_smul, one_smul]
      have := add_left_cancel h1
      rw [this, sub_self]
    have hne : ((u : F) ^ longCoroot i k true false i s) - 1 ≠ 0 := by
      refine sub_ne_zero.mpr fun h => ?_
      have hb := longCoroot_bounds_gen hik true false i s
      have hnz : longCoroot i k true false i s ≠ 0 := by
        cases s <;> simp [longCoroot, hik]
      have := (zpow_eq_one_iff_of_abs_le hu1 hu2 (w := longCoroot i k true false i s)
        (by omega)).mp h
      exact hnz this
    exact (smul_eq_zero.mp h3).resolve_left hne
  rw [hdecomp, hy0, add_zero]


section Eigenframe

variable {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem exists_third (hm : 4 ≤ m) (i₀ i₁ i : Fin m) : ∃ k : Fin m, k ≠ i₀ ∧ k ≠ i₁ ∧ k ≠ i := by
  classical
  have hcard : 0 < (Finset.univ \ {i₀, i₁, i}).card := by
    have h1 : (Finset.univ : Finset (Fin m)).card = m := by simp
    have h2 : ({i₀, i₁, i} : Finset (Fin m)).card ≤ 3 := by
      refine (Finset.card_insert_le _ _).trans ?_
      have := (Finset.card_insert_le i₁ ({i} : Finset (Fin m)))
      simp at this ⊢
      omega
    have h3 := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m)) {i₀, i₁, i}
    have h4 : ((Finset.univ : Finset (Fin m)) ∩ {i₀, i₁, i}).card ≤ 3 := by
      refine (Finset.card_le_card (Finset.inter_subset_right)).trans h2
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hk
  exact ⟨k, hk.1, hk.2.1, hk.2.2⟩

theorem polar_eq_zero_of_coords_eq_zero {x : V}
    (hx : (firstFrame Fr h01 s₀ t₀).coords x = 0) (r : Bool) :
    polar Q x (Fr.vec i₀ r) = 0 ∧ polar Q x (Fr.vec i₁ r) = 0 := by
  have e00 := congrFun (congrFun hx 0) 0
  have e01 := congrFun (congrFun hx 0) 1
  have e10 := congrFun (congrFun hx 1) 0
  have e11 := congrFun (congrFun hx 1) 1
  simp only [Frame.coords_apply, firstFrame, HypFrame.toFrame, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.zero_apply, neg_eq_zero] at e00 e01 e10 e11
  have a1 : polar Q x (Fr.vec i₀ (!s₀)) = 0 := e00
  have a2 : polar Q x (Fr.vec i₁ (!t₀)) = 0 := e01
  have a3 : polar Q x (Fr.vec i₁ t₀) = 0 := e10
  have a4 : polar Q x (Fr.vec i₀ s₀) = 0 := e11
  constructor
  · rcases Bool.eq_or_eq_not r s₀ with h | h
    · rw [h]
      exact a4
    · rw [h]
      exact a1
  · rcases Bool.eq_or_eq_not r t₀ with h | h
    · rw [h]
      exact a3
    · rw [h]
      exact a2

theorem coords_eq_zero_of_orth {y : V} (hy : ∀ a r, polar Q y (Fr.vec a r) = 0) :
    (firstFrame Fr h01 s₀ t₀).coords y = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Frame.coords_apply, firstFrame, HypFrame.toFrame, hy]


theorem exists_eigenframe_compl (hm : 4 ≤ m) (h2 : (2 : F) ≠ 0)
    (g : V →ₗ[F] V) (hg : Function.Injective g) {μ : F} (hμ : ∀ x, Q (g x) = μ * Q x)
    {u : Fˣ} (hu1 : (u : F) ≠ 1) (hu2 : (u : F) ≠ -1)
    (hI1 : ∀ (A : SL(2, F)) x,
      g ((firstFrame Fr h01 s₀ t₀).La A x) = (firstFrame Fr h01 s₀ t₀).La A (g x))
    (hI2 : ∀ (i k : Fin m) (hik : i ≠ k), i ≠ i₀ → i ≠ i₁ → k ≠ i₀ → k ≠ i₁ → ∀ t : Bool,
      ∃ η : F, (η = 1 ∨ η = -1) ∧ ∀ x,
        g (spinAction Q (Fr.longTorus hik true t u) x) =
          η • spinAction Q (Fr.longTorus hik true t u) (g x))
    (hI3 : ∀ (B : SL(2, F)) x,
      g (g ((firstFrame Fr h01 s₀ t₀).swap.La B x)) =
        (firstFrame Fr h01 s₀ t₀).swap.La B (g (g x)))
    {i₂ : Fin m} (hi20 : i₂ ≠ i₀) (hi21 : i₂ ≠ i₁)
    (hI4 : ∀ x, g (g (eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) x)) =
      eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (g (g x))) :
    ∃ (B : SL(2, F)) (lam : Fin m → Bool → F),
      (∀ i s, (firstFrame Fr h01 s₀ t₀).swap.La B
        (g (((firstFrame Fr h01 s₀ t₀).swap.La B).symm (Fr.vec i s))) = lam i s • Fr.vec i s) ∧
      (∀ i, lam i true * lam i false = μ) ∧
      (∀ y : V, (∀ a r, polar Q y (Fr.vec a r) = 0) → ∀ a r,
        polar Q ((firstFrame Fr h01 s₀ t₀).swap.La B
          (g (((firstFrame Fr h01 s₀ t₀).swap.La B).symm y))) (Fr.vec a r) = 0) := by
  classical
  set fr := firstFrame Fr h01 s₀ t₀ with hfr
  obtain ⟨h, hh, hperp⟩ := exists_mulRight_of_commute_La fr g hI1
  have v00 : Fr.vec i₀ s₀ = fr.incl !![1, 0; 0, 0] := by rw [hfr, incl_firstFrame]; simp
  have v01 : Fr.vec i₀ (!s₀) = fr.incl !![0, 0; 0, 1] := by rw [hfr, incl_firstFrame]; simp
  have v10 : Fr.vec i₁ (!t₀) = fr.incl !![0, 0; 1, 0] := by rw [hfr, incl_firstFrame]; simp
  have v11 : Fr.vec i₁ t₀ = fr.incl !![0, -1; 0, 0] := by rw [hfr, incl_firstFrame]; simp
  have hmul : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g (Fr.vec i s) = c • Fr.vec i s := by
    intro i hi0 hi1 s
    obtain ⟨k, hk0, hk1, hki⟩ := exists_third hm i₀ i₁ i
    exact exists_smul_vec_of_torus_pair Fr h2 g hg hu1 hu2 hki.symm hi0.symm hk0.symm
      (hI2 i k hki.symm hi0 hi1 hk0 hk1 false) (hI2 i k hki.symm hi0 hi1 hk0 hk1 true) s
  choose! ci hci using hmul
  obtain ⟨c₁, hc₁⟩ := exists_scalar_of_commute_La_swap fr (g ∘ₗ g)
    (fun A x => by simp only [LinearMap.comp_apply]; rw [hI1, hI1])
    (fun B x => hI3 B x)
  have hsq : h * h = c₁ • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 := hc₁ 1
    simp only [LinearMap.comp_apply] at h1
    rw [hh, hh, ← map_smul] at h1
    have := fr.incl_injective h1
    simpa using this
  have hE : eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (Fr.vec i₂ true) =
      Fr.vec i₂ true + Fr.vec i₁ (!t₀) := by
    rw [eichler_apply (Fr.map_vec i₂ false) (Fr.polar_vec_of_ne hi21 false (!t₀))]
    simp [Fr.polar_vec_vec, hi21]
  have ha : ∀ s, g (g (Fr.vec i₂ s)) = (ci i₂ s * ci i₂ s) • Fr.vec i₂ s := fun s => by
    rw [hci i₂ hi20 hi21 s, map_smul, hci i₂ hi20 hi21 s, smul_smul]
  have hc₁a : c₁ = ci i₂ true * ci i₂ true := by
    have h1 := hI4 (Fr.vec i₂ true)
    rw [hE, map_add, map_add, ha true, map_smul, hE, smul_add] at h1
    have h3 : g (g (Fr.vec i₁ (!t₀))) = (ci i₂ true * ci i₂ true) • Fr.vec i₁ (!t₀) :=
      add_left_cancel h1
    have h4 := hc₁ !![0, 0; 1, 0]
    rw [← v10] at h4
    simp only [LinearMap.comp_apply] at h4
    rw [h3] at h4
    have h5 : (ci i₂ true * ci i₂ true - c₁) • Fr.vec i₁ (!t₀) = 0 := by
      rw [sub_smul, h4, sub_self]
    exact (sub_eq_zero.mp
      ((smul_eq_zero.mp h5).resolve_right (polar_vec_ne_zero Fr i₁ (!t₀)))).symm
  have ha0 : ci i₂ true ≠ 0 := by
    intro h0
    have hz : g (Fr.vec i₂ true) = 0 := by rw [hci i₂ hi20 hi21 true, h0, zero_smul]
    have hz' : Fr.vec i₂ true = 0 := hg (by rw [hz, map_zero])
    exact polar_vec_ne_zero Fr i₂ true hz'
  obtain ⟨S, d₁, d₂, hd₁, hd₂, hS⟩ := exists_sl2_diag h2 ha0 (by rw [hsq, hc₁a])
  let B : SL(2, F) := ⟨sigmaLin (S : Matrix (Fin 2) (Fin 2) F), by rw [det_sigmaLin]; exact S.2⟩
  have hBσ : sigmaLin (B : Matrix (Fin 2) (Fin 2) F) = (S : Matrix (Fin 2) (Fin 2) F) :=
    sigmaLin_sigmaLin _
  have hρ : ∀ Y, fr.swap.La B (fr.incl Y) = fr.incl (Y * (S : Matrix (Fin 2) (Fin 2) F)) :=
    fun Y => by rw [swap_La_incl, hBσ]
  have hρ' : ∀ Y, (fr.swap.La B).symm (fr.incl Y) =
      fr.incl (Y * ((S⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) := fun Y => by
    rw [LinearEquiv.symm_apply_eq, hρ, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  have hplane : ∀ (Y₀ : Matrix (Fin 2) (Fin 2) F) (d : F),
      Y₀ * !![d₁, 0; 0, d₂] = d • Y₀ →
        fr.swap.La B (g ((fr.swap.La B).symm (fr.incl Y₀))) = d • fr.incl Y₀ := by
    intro Y₀ d hY
    rw [hρ', hh, hρ]
    have : Y₀ * ((S⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * h *
        (S : Matrix (Fin 2) (Fin 2) F) = d • Y₀ := by
      rw [Matrix.mul_assoc _ h, hS, ← Matrix.mul_assoc, Matrix.mul_assoc Y₀,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_one, hY]
    rw [this, map_smul]
  have hρiso : ∀ x, Q (fr.swap.La B x) = Q x := fun x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (fr.swap.La_mem_orthogonalGroup B) x
  have hρfix : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ r, fr.swap.La B (Fr.vec i r) = Fr.vec i r :=
    fun i hi0 hi1 r => Frame.La_apply_of_coords_eq_zero fr.swap B
      (by rw [hfr]; exact swap_coords_firstFrame_vec Fr h01 s₀ t₀ hi0 hi1 r)
  have hex : ∀ i s, ∃ l : F, fr.swap.La B (g ((fr.swap.La B).symm (Fr.vec i s))) =
      l • Fr.vec i s := by
    intro i s
    by_cases hi0 : i = i₀
    · subst hi0
      rcases Bool.eq_or_eq_not s s₀ with hs | hs
      · exact ⟨d₁, by
          rw [hs, v00]
          refine hplane _ _ ?_
          ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
      · exact ⟨d₂, by
          rw [hs, v01]
          refine hplane _ _ ?_
          ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
    · by_cases hi1 : i = i₁
      · subst hi1
        rcases Bool.eq_or_eq_not s t₀ with hs | hs
        · exact ⟨d₂, by
            rw [hs, v11]
            refine hplane _ _ ?_
            ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
        · exact ⟨d₁, by
            rw [hs, v10]
            refine hplane _ _ ?_
            ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩
      · refine ⟨ci i s, ?_⟩
        have e1 : (fr.swap.La B).symm (Fr.vec i s) = Fr.vec i s :=
          (LinearEquiv.symm_apply_eq (fr.swap.La B)).mpr (hρfix i hi0 hi1 s).symm
        rw [e1, hci i hi0 hi1 s, map_smul, hρfix i hi0 hi1 s]
  choose lam hlam using hex
  refine ⟨B, lam, hlam, fun i => ?_, ?_⟩
  · have hQsymm : ∀ x, Q ((fr.swap.La B).symm x) = Q x := fun x => by
      rw [← hρiso ((fr.swap.La B).symm x), LinearEquiv.apply_symm_apply]
    let G : V →ₗ[F] V := (fr.swap.La B).toLinearMap ∘ₗ g ∘ₗ (fr.swap.La B).symm.toLinearMap
    have hG : ∀ x, G x = fr.swap.La B (g ((fr.swap.La B).symm x)) := fun x => rfl
    have hQG : ∀ x, Q (G x) = μ * Q x := fun x => by rw [hG, hρiso, hμ, hQsymm]
    have hpG : ∀ x y, polar Q (G x) (G y) = μ * polar Q x y := fun x y => by
      simp only [QuadraticMap.polar, ← map_add, hQG, mul_sub]
    have := hpG (Fr.vec i true) (Fr.vec i false)
    rw [hG, hG, hlam, hlam, polar_smul_left, polar_smul_right] at this
    have h1 := Fr.polar_vec_not i true
    simp only [Bool.not_true] at h1
    rw [h1] at this
    simpa using this
  · intro y hy a r
    have hcy : fr.coords y = 0 := coords_eq_zero_of_orth Fr h01 s₀ t₀ hy
    have hρy : fr.swap.La B y = y := Frame.La_apply_of_coords_eq_zero fr.swap B
      (by rw [Frame.coords_swap, hcy, map_zero])
    have e1 : (fr.swap.La B).symm y = y :=
      (LinearEquiv.symm_apply_eq (fr.swap.La B)).mpr hρy.symm
    rw [e1]
    have hgc : fr.coords (g y) = 0 := hperp y hcy
    have hρgy : fr.swap.La B (g y) = g y := Frame.La_apply_of_coords_eq_zero fr.swap B
      (by rw [Frame.coords_swap, hgc, map_zero])
    rw [hρgy]
    by_cases ha0 : a = i₀
    · subst ha0
      exact (polar_eq_zero_of_coords_eq_zero Fr h01 s₀ t₀ hgc r).1
    · by_cases ha1 : a = i₁
      · subst ha1
        exact (polar_eq_zero_of_coords_eq_zero Fr h01 s₀ t₀ hgc r).2
      · obtain ⟨k, hk0, hk1, hka⟩ := exists_third hm i₀ i₁ a
        obtain ⟨η, hη, hcomm⟩ := hI2 a k hka.symm ha0 ha1 hk0 hk1 false
        have e := eta_eq_one_gen Fr h2 g hg hu2 hka.symm true false hη hcomm (Ne.symm ha0)
          (Ne.symm hk0)
        subst e
        simp only [one_smul] at hcomm
        have hTy : spinAction Q (Fr.longTorus hka.symm true false u) (g y) = g y := by
          rw [← hcomm y, torus_fix_of_orth Fr _ _ _ _ hy]
        have hw : (u : F) ^ longCoroot a k true false a r ≠ 1 := by
          intro hh1
          have hb := longCoroot_bounds_gen hka.symm true false a r
          have hnz : longCoroot a k true false a r ≠ 0 := by
            cases r <;> simp [longCoroot, hka.symm]
          exact hnz ((zpow_eq_one_iff_of_abs_le hu1 hu2 (w := longCoroot a k true false a r)
            (by omega)).mp hh1)
        refine polar_eq_zero_of_eigen (τ := spinAction Q (Fr.longTorus hka.symm true false u))
          (fun x => map_spinAction Q _ x) (a := 1) ?_
          (torus_vec_gen Fr hka.symm true false u a r) (by rw [one_mul]; exact hw)
        rw [one_smul]
        exact hTy

end Eigenframe

end Compl

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
