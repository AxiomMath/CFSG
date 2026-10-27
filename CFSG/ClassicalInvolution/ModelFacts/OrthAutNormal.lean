module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutCompl
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutDiag

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OrthAut

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped Matrix MatrixGroups

section Eigenframe

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {m : ℕ} (Fr : HypFrame Q m) {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem exists_eigenframe_of_diag (h2 : (2 : F) ≠ 0)
    (g : V →ₗ[F] V) (hg : Function.Injective g) {μ : F} (hμ : ∀ x, Q (g x) = μ * Q x)
    (hI1 : ∀ (A : SL(2, F)) x,
      g ((firstFrame Fr h01 s₀ t₀).La A x) = (firstFrame Fr h01 s₀ t₀).La A (g x))
    (hmul : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g (Fr.vec i s) = c • Fr.vec i s)
    (hI3 : ∀ (B : SL(2, F)) x,
      g (g ((firstFrame Fr h01 s₀ t₀).swap.La B x)) =
        (firstFrame Fr h01 s₀ t₀).swap.La B (g (g x)))
    {i₂ : Fin m} (hi20 : i₂ ≠ i₀) (hi21 : i₂ ≠ i₁)
    (hI4 : ∀ x, g (g (eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) x)) =
      eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (g (g x))) :
    ∃ (B : SL(2, F)) (lam : Fin m → Bool → F),
      (∀ i s, (firstFrame Fr h01 s₀ t₀).swap.La B
        (g (((firstFrame Fr h01 s₀ t₀).swap.La B).symm (Fr.vec i s))) = lam i s • Fr.vec i s) ∧
      ∀ i, lam i true * lam i false = μ := by
  classical
  set fr := firstFrame Fr h01 s₀ t₀ with hfr
  obtain ⟨h, hh, -⟩ := exists_mulRight_of_commute_La fr g hI1
  have v00 : Fr.vec i₀ s₀ = fr.incl !![1, 0; 0, 0] := by rw [hfr, incl_firstFrame]; simp
  have v01 : Fr.vec i₀ (!s₀) = fr.incl !![0, 0; 0, 1] := by rw [hfr, incl_firstFrame]; simp
  have v10 : Fr.vec i₁ (!t₀) = fr.incl !![0, 0; 1, 0] := by rw [hfr, incl_firstFrame]; simp
  have v11 : Fr.vec i₁ t₀ = fr.incl !![0, -1; 0, 0] := by rw [hfr, incl_firstFrame]; simp
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
    have : g (Fr.vec i₂ true) = 0 := by rw [hci i₂ hi20 hi21 true, h0, zero_smul]
    exact polar_vec_ne_zero Fr i₂ true (hg (by rw [this, map_zero]))
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
    have : Y₀ * ((S⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * h * (S : Matrix (Fin 2) (Fin 2) F) =
        d • Y₀ := by
      rw [Matrix.mul_assoc _ h, hS, ← Matrix.mul_assoc, Matrix.mul_assoc Y₀,
        ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_one, hY]
    rw [this, map_smul]
  have hρiso : ∀ x, Q (fr.swap.La B x) = Q x := fun x =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (fr.swap.La_mem_orthogonalGroup B) x
  have hρfix : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ r, fr.swap.La B (Fr.vec i r) = Fr.vec i r :=
    fun i hi0 hi1 r => Frame.La_apply_of_coords_eq_zero fr.swap B
      (by rw [hfr]; exact swap_coords_firstFrame_vec Fr h01 s₀ t₀ hi0 hi1 r)
  have hex : ∀ i s, ∃ l : F, fr.swap.La B (g ((fr.swap.La B).symm (Fr.vec i s))) = l • Fr.vec i s := by
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
  refine ⟨B, lam, hlam, fun i => ?_⟩
  have hQsymm : ∀ x, Q ((fr.swap.La B).symm x) = Q x := fun x => by
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

end Eigenframe


section CommutingRoots

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {m : ℕ} (Fr : HypFrame Q m)

theorem polar_map_of_similitude (g : V →ₗ[F] V) {μ : F} (hμ : ∀ x, Q (g x) = μ * Q x) (x y : V) :
    polar Q (g x) (g y) = μ * polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hμ, mul_sub]

theorem map_vec_of_commute {g : V →ₗ[F] V} {a b : Fin m} (hab : a ≠ b) (s t : Bool)
    (hcomm : ∀ x, g (eichler Q (Fr.vec b t) (Fr.vec a s) x) =
      eichler Q (Fr.vec b t) (Fr.vec a s) (g x)) :
    g (Fr.vec a s) = polar Q (g (Fr.vec b (!t))) (Fr.vec b t) • Fr.vec a s -
      polar Q (g (Fr.vec b (!t))) (Fr.vec a s) • Fr.vec b t := by
  have hu : Q (Fr.vec b t) = 0 := Fr.map_vec b t
  have huw : polar Q (Fr.vec b t) (Fr.vec a s) = 0 := Fr.polar_vec_of_ne hab.symm t s
  have hE : eichler Q (Fr.vec b t) (Fr.vec a s) (Fr.vec b (!t)) =
      Fr.vec b (!t) + Fr.vec a s := by
    rw [eichler_apply hu huw, Fr.polar_not_vec b t, Fr.polar_vec_of_ne hab.symm (!t) s,
      Fr.map_vec a s]
    simp
  have h1 := hcomm (Fr.vec b (!t))
  rw [hE, map_add, eichler_apply hu huw] at h1
  simp only [Fr.map_vec, zero_mul, add_zero] at h1
  rw [add_sub_assoc] at h1
  exact add_left_cancel h1

theorem diag_of_commuting_roots (g : V →ₗ[F] V) (hg : Function.Injective g) {μ : F}
    (hμ : ∀ x, Q (g x) = μ * Q x) {O : Fin m → Prop} {a₁ a₂ : Fin m} (ha₁ : O a₁) (ha₂ : O a₂)
    (h12 : a₁ ≠ a₂)
    (hcomm : ∀ a b, a ≠ b → O a → O b → ∀ s t x,
      g (eichler Q (Fr.vec b t) (Fr.vec a s) x) = eichler Q (Fr.vec b t) (Fr.vec a s) (g x)) :
    ∃ r : F, r ≠ 0 ∧ r * r = μ ∧ ∀ a, O a → ∀ s, g (Fr.vec a s) = r • Fr.vec a s := by
  classical
  have hpartner : ∀ a, O a → ∃ b, O b ∧ b ≠ a := fun a ha => by
    by_cases h : a = a₁
    · exact ⟨a₂, ha₂, fun h' => h12 (h.symm.trans h'.symm)⟩
    · exact ⟨a₁, ha₁, fun h' => h h'.symm⟩
  have hdiag : ∀ a, O a → ∀ s, ∃ c : F, g (Fr.vec a s) = c • Fr.vec a s := by
    intro a ha s
    obtain ⟨b, hb, hba⟩ := hpartner a ha
    have hab : a ≠ b := hba.symm
    have hQ : ∀ t, polar Q (g (Fr.vec b (!t))) (Fr.vec a s) = 0 := by
      intro t
      have h1 := map_vec_of_commute Fr hab s t (hcomm a b hab ha hb s t)
      have h2 := map_vec_of_commute Fr hab s (!t) (hcomm a b hab ha hb s (!t))
      have e1 : polar Q (g (Fr.vec a s)) (Fr.vec b (!t)) =
          -polar Q (g (Fr.vec b (!t))) (Fr.vec a s) := by
        rw [h1, polar_sub_left, polar_smul_left, polar_smul_left, Fr.polar_vec_of_ne hab s (!t),
          Fr.polar_vec_not b t]
        simp
      have e2 : polar Q (g (Fr.vec a s)) (Fr.vec b (!t)) = 0 := by
        rw [h2, polar_sub_left, polar_smul_left, polar_smul_left, Fr.polar_vec_of_ne hab s (!t),
          Fr.polar_vec_self]
        simp
      rw [e2] at e1
      exact neg_eq_zero.mp e1.symm
    refine ⟨polar Q (g (Fr.vec b (!true))) (Fr.vec b true), ?_⟩
    rw [map_vec_of_commute Fr hab s true (hcomm a b hab ha hb s true), hQ true, zero_smul,
      sub_zero]
  choose! c hc using hdiag
  have hrel : ∀ a b, a ≠ b → O a → O b → ∀ s t, c a s = c b (!t) := by
    intro a b hab ha hb s t
    have h1 := map_vec_of_commute Fr hab s t (hcomm a b hab ha hb s t)
    have hQ : polar Q (g (Fr.vec b (!t))) (Fr.vec a s) = 0 := by
      rw [hc b hb (!t), polar_smul_left, Fr.polar_vec_of_ne hab.symm (!t) s, smul_zero]
    rw [hQ, zero_smul, sub_zero, hc b hb (!t), polar_smul_left, Fr.polar_not_vec b t,
      smul_eq_mul, mul_one, hc a ha s] at h1
    have h3 : (c a s - c b (!t)) • Fr.vec a s = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (polar_vec_ne_zero Fr a s))
  have hall : ∀ a, O a → ∀ s, c a s = c a₁ true := by
    intro a ha s
    by_cases h : a = a₁
    · subst h
      cases s
      · have h1 := hrel a a₂ h12 ha ha₂ false false
        have h2 := hrel a a₂ h12 ha ha₂ true false
        rw [h1, ← h2]
      · rfl
    · exact (hrel a a₁ h ha ha₁ s false)
  have hr0 : c a₁ true ≠ 0 := by
    intro h0
    have := hc a₁ ha₁ true
    rw [h0, zero_smul] at this
    exact polar_vec_ne_zero Fr a₁ true (hg (by rw [this, map_zero]))
  refine ⟨c a₁ true, hr0, ?_, fun a ha s => by rw [hc a ha s, hall a ha s]⟩
  have hpol := polar_map_of_similitude g hμ (Fr.vec a₁ true) (Fr.vec a₁ false)
  have hnot := Fr.polar_vec_not a₁ true
  simp only [Bool.not_true] at hnot
  rw [hc a₁ ha₁ true, hc a₁ ha₁ false, hall a₁ ha₁ false, polar_smul_left, polar_smul_right,
    hnot] at hpol
  simpa using hpol

end CommutingRoots


section Normalized

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {m : ℕ} (Fr : HypFrame Q m)

theorem map_vec_of_normalized {g : V →ₗ[F] V} {u w x : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (hxu : polar Q x u = 1) (hxw : polar Q x w = 0) {r c' : F}
    (hgx : g x = r • x) (hnorm : g (eichler Q u w x) = eichler Q u (c' • w) (g x)) :
    g w = (r * c') • w := by
  have hcw : polar Q u (c' • w) = 0 := by rw [polar_smul_right, huw, smul_zero]
  have e1 : eichler Q u w x = x + w := by
    rw [eichler_apply hu huw, hxu, hxw, hw]
    simp
  have e2 : eichler Q u (c' • w) (r • x) = r • x + (r * c') • w := by
    rw [eichler_apply hu hcw, polar_smul_left, polar_smul_right, polar_smul_left, hxu, hxw,
      QuadraticMap.map_smul, hw]
    simp only [smul_eq_mul, mul_one, mul_zero, zero_mul, zero_add, zero_smul, sub_zero, smul_smul]
  rw [e1, map_add, hgx, e2] at hnorm
  exact add_left_cancel hnorm

theorem map_vec_not_of_diag
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0) {g : V →ₗ[F] V} {μ : F}
    (hμ : ∀ x, Q (g x) = μ * Q x) (hμ0 : μ ≠ 0) {c : Fin m} (s : Bool) {l : F}
    (hl : g (Fr.vec c s) = l • Fr.vec c s) (hl0 : l ≠ 0)
    (hperp : ∀ a r, a ≠ c → polar Q (g (Fr.vec c (!s))) (Fr.vec a r) = 0) :
    g (Fr.vec c (!s)) = (μ * l⁻¹) • Fr.vec c (!s) := by
  have hwQ : Q (Fr.vec c (!s)) = 0 := Fr.map_vec c (!s)
  have hws : polar Q (Fr.vec c (!s)) (Fr.vec c s) = 1 := Fr.polar_not_vec c s
  have hb : polar Q (g (Fr.vec c (!s))) (Fr.vec c s) = μ * l⁻¹ := by
    have h1 := polar_map_of_similitude g hμ (Fr.vec c (!s)) (Fr.vec c s)
    rw [hl, polar_smul_right, hws, smul_eq_mul, mul_one] at h1
    rw [eq_mul_inv_iff_mul_eq₀ hl0, mul_comm]
    exact h1
  have hxo : ∀ a r, (a, r) ≠ (c, !s) →
      polar Q (g (Fr.vec c (!s)) - (μ * l⁻¹) • Fr.vec c (!s)) (Fr.vec a r) = 0 := by
    intro a r har
    rw [polar_sub_left, polar_smul_left]
    by_cases hac : a = c
    · rw [hac]
      rcases Bool.eq_or_eq_not r s with hr | hr
      · rw [hr, hb, hws, smul_eq_mul, mul_one, sub_self]
      · exact absurd (by rw [hac, hr]) har
    · rw [hperp a r hac, Fr.polar_vec_of_ne (Ne.symm hac) (!s) r, smul_zero, sub_zero]
  have hx' := eq_smul_vec_of_polar_eq_zero Fr hspan c s hxo
  obtain ⟨a', ha'⟩ : ∃ a', a' = polar Q (g (Fr.vec c (!s)) - (μ * l⁻¹) • Fr.vec c (!s))
      (Fr.vec c (!s)) := ⟨_, rfl⟩
  rw [← ha'] at hx'
  have hy : g (Fr.vec c (!s)) = (μ * l⁻¹) • Fr.vec c (!s) + a' • Fr.vec c s := by
    rw [← hx']
    abel
  have hQ : Q (g (Fr.vec c (!s))) = 0 := by rw [hμ, hwQ, mul_zero]
  have hμl : μ * l⁻¹ ≠ 0 := mul_ne_zero hμ0 (inv_ne_zero hl0)
  have ha0 : a' = 0 := by
    have h1 : Q ((μ * l⁻¹) • Fr.vec c (!s) + a' • Fr.vec c s) = (μ * l⁻¹) * a' := by
      rw [QuadraticMap.map_add Q, polar_smul_left, polar_smul_right, hws, QuadraticMap.map_smul,
        QuadraticMap.map_smul, hwQ, Fr.map_vec]
      simp
    rw [hy, h1] at hQ
    exact (mul_eq_zero.mp hQ).resolve_left hμl
  rw [hy, ha0, zero_smul, add_zero]

variable {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem hmul_of_normalized
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0) (hm : 5 ≤ m)
    (g : V →ₗ[F] V) (hg : Function.Injective g) {μ : F} (hμ : ∀ x, Q (g x) = μ * Q x)
    (hμ0 : μ ≠ 0)
    (hI1 : ∀ (A : SL(2, F)) x,
      g ((firstFrame Fr h01 s₀ t₀).La A x) = (firstFrame Fr h01 s₀ t₀).La A (g x))
    {c₀ j : Fin m} (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀) (hj1 : j ≠ i₁) (hjc : c₀ ≠ j)
    (s₁ t₁ : Bool)
    (hO : ∀ a b : Fin m, a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) x, g (eichler Q (Fr.vec b t) (Fr.vec a s) x) =
        eichler Q (Fr.vec b t) (Fr.vec a s) (g x))
    {c' : F} (hN : ∀ z, g (eichler Q (Fr.vec j t₁) (Fr.vec c₀ s₁) z) =
      eichler Q (Fr.vec j t₁) (c' • Fr.vec c₀ s₁) (g z)) :
    ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g (Fr.vec i s) = c • Fr.vec i s := by
  classical
  obtain ⟨a₁, a₂, ha₁0, ha₁1, ha₁c, ha₂0, ha₂1, ha₂c, h12⟩ := exists_two_others hm i₀ i₁ c₀
  obtain ⟨r, hr0, -, hr⟩ := diag_of_commuting_roots Fr g hg hμ
    (O := fun a => a ≠ i₀ ∧ a ≠ i₁ ∧ a ≠ c₀) ⟨ha₁0, ha₁1, ha₁c⟩ ⟨ha₂0, ha₂1, ha₂c⟩ h12
    (fun a b hab ha hb s t x => hO a b hab ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2 s t x)
  have hl : g (Fr.vec c₀ s₁) = (r * c') • Fr.vec c₀ s₁ :=
    map_vec_of_normalized (g := g) (Fr.map_vec j t₁) (Fr.map_vec c₀ s₁)
      (Fr.polar_vec_of_ne hjc.symm t₁ s₁) (Fr.polar_not_vec j t₁)
      (Fr.polar_vec_of_ne hjc.symm (!t₁) s₁) (hr j ⟨hj0, hj1, hjc.symm⟩ (!t₁)) (hN _)
  have hl0 : r * c' ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hl
    exact polar_vec_ne_zero Fr c₀ s₁ (hg (by rw [hl, map_zero]))
  obtain ⟨-, -, hcoords⟩ := exists_mulRight_of_commute_La (firstFrame Fr h01 s₀ t₀) g hI1
  have hcw : (firstFrame Fr h01 s₀ t₀).coords (g (Fr.vec c₀ (!s₁))) = 0 :=
    hcoords _ (coords_firstFrame_vec Fr h01 s₀ t₀ hc0 hc1 (!s₁))
  have hperp : ∀ a r', a ≠ c₀ → polar Q (g (Fr.vec c₀ (!s₁))) (Fr.vec a r') = 0 := by
    intro a r' hac
    by_cases ha0 : a = i₀
    · rw [ha0]
      exact (polar_eq_zero_of_coords_eq_zero Fr h01 s₀ t₀ hcw r').1
    · by_cases ha1 : a = i₁
      · rw [ha1]
        exact (polar_eq_zero_of_coords_eq_zero Fr h01 s₀ t₀ hcw r').2
      · have h1 := polar_map_of_similitude g hμ (Fr.vec c₀ (!s₁)) (Fr.vec a r')
        rw [hr a ⟨ha0, ha1, hac⟩ r', polar_smul_right, Fr.polar_vec_of_ne hac.symm (!s₁) r',
          mul_zero, smul_eq_mul] at h1
        exact (mul_eq_zero.mp h1).resolve_left hr0
  have hd := map_vec_not_of_diag Fr hspan hμ hμ0 s₁ hl hl0 hperp
  intro i hi0 hi1 s
  by_cases hic : i = c₀
  · rw [hic]
    rcases Bool.eq_or_eq_not s s₁ with hs | hs
    · exact ⟨r * c', by rw [hs]; exact hl⟩
    · exact ⟨μ * (r * c')⁻¹, by rw [hs]; exact hd⟩
  · exact ⟨r, hr i ⟨hi0, hi1, hic⟩ s⟩

end Normalized


section Ambiguity

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {p : ℕ}

theorem eq_of_mul_inv_mem_center_of_pow {K : Type*} [Group K]
    (hZ : ∀ ζ ∈ Subgroup.center K, ζ ^ p = 1 → ζ = 1) {y y' : K} (hy : y ^ p = 1) (hy' : y' ^ p = 1)
    (h : y * y'⁻¹ ∈ Subgroup.center K) : y = y' := by
  have hyy : y = (y * y'⁻¹) * y' := by group
  have hc : Commute (y * y'⁻¹) y' := (Subgroup.mem_center_iff.mp h y').symm
  have hp : (y * y'⁻¹) ^ p = 1 := by
    have h1 := hy
    rw [hyy, hc.mul_pow, hy', mul_one] at h1
    exact h1
  rw [hyy, hZ _ h hp, one_mul]

theorem conjTwist_eq_of_sigma_eq {X : Type*} [Group X]
    (hZ : ∀ ζ ∈ Subgroup.center (spinGroup Q), ζ ^ p = 1 → ζ = 1) (θ : spinGroup Q →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup Q)) (σ : X ≃* X) (α : spinGroup Q ≃* spinGroup Q)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (k : spinGroup Q) {x x' : spinGroup Q} (hx : x ^ p = 1)
    (hx' : x' ^ p = 1) (h : σ (θ (k * x * k⁻¹)) = θ (k * x' * k⁻¹)) :
    conjTwist α k x = x' := by
  have h1 : α (k * x * k⁻¹) * (k * x' * k⁻¹)⁻¹ ∈ Subgroup.center (spinGroup Q) :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, h, mul_inv_cancel])
  have h2 : conjTwist α k x * x'⁻¹ ∈ Subgroup.center (spinGroup Q) := by
    have h3 := Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center (spinGroup Q)).Normal)
      _ h1 k⁻¹
    have e : conjTwist α k x * x'⁻¹ =
        k⁻¹ * (α (k * x * k⁻¹) * (k * x' * k⁻¹)⁻¹) * k⁻¹⁻¹ := by
      rw [conjTwist_apply]
      group
    rw [e]
    exact h3
  have hy : (conjTwist α k x) ^ p = 1 := by rw [← map_pow, hx, map_one]
  exact eq_of_mul_inv_mem_center_of_pow hZ hy hx' h2

end Ambiguity

section GroupLevel

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
  (Fr : HypFrame Q m) {i₀ i₁ : Fin m} (h01 : i₀ ≠ i₁) (s₀ t₀ : Bool)

theorem exists_linear_conj {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g)
    (k : spinGroup Q)
    (hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c))
    (hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) :
    ∃ gL : V →ₗ[F] V, (∀ c, g.φ c = c) ∧ (∀ x, gL x = g.conjSpin k x) ∧
      (∀ y x, spinAction Q (conjTwist α k y) (gL x) = gL (spinAction Q y x)) ∧
      (∀ x, Q (gL x) = (g.μ : F) * Q x) ∧ Function.Injective gL ∧
      ∀ (A : SL(2, F)) x, gL ((firstFrame Fr h01 s₀ t₀).La A x) =
        (firstFrame Fr h01 s₀ t₀).La A (gL x) := by
  classical
  have hα₁c : IsConj (conjTwist α k) (g.conjSpin k) := hα.conjSpin k
  have hφ : ∀ c, (g.conjSpin k).φ c = c := fun c => hα₁c.phi_eq_of_fix Fr h01 s₀ t₀ hA1 c
  have hfixSL : ∀ A : SL(2, F), conjTwist α k (Fr.longSL2 h01 s₀ t₀ A) =
      Fr.longSL2 h01 s₀ t₀ A := by
    intro A
    have := Frame.sl2_apply_mem (Fr.longSL2 h01 s₀ t₀)
      (MonoidHom.eqLocus (conjTwist α k : spinGroup Q →* spinGroup Q) (MonoidHom.id _))
      (fun c => ?_) (fun c => ?_) A
    · exact this
    · rw [← coe_upperSL2_eq_transvection, HypFrame.longSL2_upperSL2]
      exact hA1 c
    · rw [← coe_lowerSL2_eq_transvection, HypFrame.longSL2_lowerSL2]
      exact hA1' c
  refine ⟨(g.conjSpin k).toLinear hφ, hφ, fun x => rfl, fun y x => hα₁c y x, fun x => ?_, ?_, ?_⟩
  · change Q ((g.conjSpin k) x) = _
    rw [(g.conjSpin k).map_Q, hφ]
    rfl
  · exact fun x y hxy => (g.conjSpin k).bijective.1 hxy
  · intro A x
    have hLA : (firstFrame Fr h01 s₀ t₀).La A = spinAction Q (Fr.longSL2 h01 s₀ t₀ A) :=
      (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ t₀) A).symm
    rw [hLA]
    change (g.conjSpin k) (spinAction Q (Fr.longSL2 h01 s₀ t₀ A) x) =
      spinAction Q (Fr.longSL2 h01 s₀ t₀ A) ((g.conjSpin k) x)
    rw [← hα₁c (Fr.longSL2 h01 s₀ t₀ A) x, hfixSL A]

theorem exists_diag_form_of_diag {p : ℕ} [Fact p.Prime] [CharP F p] (hm : 3 ≤ m)
    (h2 : (2 : F) ≠ 0) (hp2 : p ≠ 2) (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g) (hα2 : ∀ y, α (α y) = y)
    (k : spinGroup Q)
    (hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c))
    (hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c))
    (hmul : ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g.conjSpin k (Fr.vec i s) = c • Fr.vec i s) :
    ∃ (κ : spinGroup Q) (lam : Fin m → Bool → F), (∀ i, lam i true * lam i false = g.μ) ∧
      ∀ (i j : Fin m) (hij : i ≠ j) (s t : Bool) (c : F),
        α (κ * Fr.longRoot hij s t (.ofAdd c) * κ⁻¹) =
          κ * Fr.longRoot hij s t (.ofAdd (lam j t * ((g.μ : F)⁻¹ * (lam i s * c)))) * κ⁻¹ := by
  classical
  obtain ⟨gL, hφ, hgL, hconj, hμL, hginj, hI1⟩ := exists_linear_conj Fr h01 s₀ t₀ hα k hA1 hA1'
  have hα₁c : IsConj (conjTwist α k) (g.conjSpin k) := hα.conjSpin k
  have hα₁2 : ∀ y, conjTwist α k (conjTwist α k y) = y := conjTwist_sq α hα2 k
  have hI3 : ∀ (B : SL(2, F)) x, gL (gL ((firstFrame Fr h01 s₀ t₀).swap.La B x)) =
      (firstFrame Fr h01 s₀ t₀).swap.La B (gL (gL x)) := by
    intro B x
    have hLB : (firstFrame Fr h01 s₀ t₀).swap.La B =
        spinAction Q (Fr.longSL2 h01 s₀ (!t₀) B) := by
      rw [firstFrame, swap_toFrame]
      exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
    rw [hLB, hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 _ x
  obtain ⟨i₂, hi20, hi21⟩ := exists_ne_and_ne hm i₀ i₁
  have hI4 : ∀ x, gL (gL (eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) x)) =
      eichler Q (Fr.vec i₂ false) (Fr.vec i₁ (!t₀)) (gL (gL x)) := by
    intro x
    have e := Fr.spinAction_longRoot_eq_eichler (show i₁ ≠ i₂ from hi21.symm) (!t₀) false 1
    rw [one_smul] at e
    rw [← e, hgL, hgL, hgL, hgL]
    exact hα₁c.comm_sq hα₁2 _ x
  obtain ⟨B, lam, hlam, hprod⟩ := exists_eigenframe_of_diag Fr h01 s₀ t₀ h2 gL hginj hμL hI1
    (fun i hi0 hi1 s => by
      obtain ⟨c, hc⟩ := hmul i hi0 hi1 s
      exact ⟨c, by rw [hgL]; exact hc⟩) hI3 hi20 hi21 hI4
  set r := Fr.longSL2 h01 s₀ (!t₀) B with hr
  have hρ : (firstFrame Fr h01 s₀ t₀).swap.La B = spinAction Q r := by
    rw [firstFrame, swap_toFrame]
    exact (DFunLike.congr_fun (spinAction_comp_longSL2 Fr h01 s₀ (!t₀)) B).symm
  have hρsymm : ∀ w, ((firstFrame Fr h01 s₀ t₀).swap.La B).symm w = spinAction Q r⁻¹ w :=
    fun w => by
    rw [LinearEquiv.symm_apply_eq, hρ, spinAction_apply_inv]
  have hg₂ : ∀ i s, g.conjSpin (k * r⁻¹) (Fr.vec i s) = lam i s • Fr.vec i s := by
    intro i s
    have h1 := hlam i s
    rw [hρsymm, hρ, hgL] at h1
    rw [SemiSim.conjSpin_apply, mul_inv_rev, inv_inv, spinAction_mul_apply r k⁻¹,
      spinAction_mul_apply k r⁻¹]
    exact h1
  have hα₂c : IsConj (conjTwist α (k * r⁻¹)) (g.conjSpin (k * r⁻¹)) := hα.conjSpin _
  refine ⟨k * r⁻¹, lam, hprod, fun i j hij s t c => ?_⟩
  have h3 := IsConj.longRoot_eq hp2 hker2 Fr hα₂c lam (fun _ s => s) hg₂ hij s t c
  have e1 : α (k * r⁻¹ * Fr.longRoot hij s t (.ofAdd c) * (k * r⁻¹)⁻¹) =
      k * r⁻¹ * conjTwist α (k * r⁻¹) (Fr.longRoot hij s t (.ofAdd c)) * (k * r⁻¹)⁻¹ := by
    rw [conjTwist_apply]
    group
  have hφ₂ : ∀ c, (g.conjSpin (k * r⁻¹)).φ c = c := hφ
  rw [e1, h3, hφ₂ c]
  rfl

theorem hmul_of_normalized_group
    (hspan : ∀ x : V, (∀ a r, polar Q x (Fr.vec a r) = 0) → x = 0) (hm : 5 ≤ m)
    {α : spinGroup Q ≃* spinGroup Q} {g : SemiSim Q} (hα : IsConj α g) (k : spinGroup Q)
    (hA1 : ∀ c : F, conjTwist α k (Fr.longRoot h01 s₀ t₀ (.ofAdd c)) =
      Fr.longRoot h01 s₀ t₀ (.ofAdd c))
    (hA1' : ∀ c : F, conjTwist α k (Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c)) =
      Fr.longRoot h01.symm (!t₀) (!s₀) (.ofAdd c))
    {c₀ j : Fin m} (hc0 : c₀ ≠ i₀) (hc1 : c₀ ≠ i₁) (hj0 : j ≠ i₀) (hj1 : j ≠ i₁) (hjc : c₀ ≠ j)
    (s₁ t₁ : Bool)
    (hO : ∀ (a b : Fin m) (hab : a ≠ b), a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) (c : F), conjTwist α k (Fr.longRoot hab s t (.ofAdd c)) =
        Fr.longRoot hab s t (.ofAdd c))
    {c' : F} (hN : conjTwist α k (Fr.longRoot hjc s₁ t₁ (.ofAdd 1)) =
      Fr.longRoot hjc s₁ t₁ (.ofAdd c')) :
    ∀ i, i ≠ i₀ → i ≠ i₁ → ∀ s, ∃ c : F, g.conjSpin k (Fr.vec i s) = c • Fr.vec i s := by
  classical
  obtain ⟨gL, hφ, hgL, hconj, hμL, hginj, hI1⟩ := exists_linear_conj Fr h01 s₀ t₀ hα k hA1 hA1'
  have hμ0 : (g.μ : F) ≠ 0 := g.μ.ne_zero
  have hcomm : ∀ a b : Fin m, a ≠ b → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → b ≠ i₀ → b ≠ i₁ → b ≠ c₀ →
      ∀ (s t : Bool) x, gL (eichler Q (Fr.vec b t) (Fr.vec a s) x) =
        eichler Q (Fr.vec b t) (Fr.vec a s) (gL x) := by
    intro a b hab ha0 ha1 hac hb0 hb1 hbc s t x
    have e := Fr.spinAction_longRoot_eq_eichler hab s t 1
    rw [one_smul] at e
    rw [← e, ← hconj, hO a b hab ha0 ha1 hac hb0 hb1 hbc s t 1]
  have hnorm : ∀ z, gL (eichler Q (Fr.vec j t₁) (Fr.vec c₀ s₁) z) =
      eichler Q (Fr.vec j t₁) (c' • Fr.vec c₀ s₁) (gL z) := by
    intro z
    have e := Fr.spinAction_longRoot_eq_eichler hjc s₁ t₁ 1
    rw [one_smul] at e
    have e' := Fr.spinAction_longRoot_eq_eichler hjc s₁ t₁ c'
    rw [← e, ← e', ← hconj, hN]
  intro i hi0 hi1 s
  obtain ⟨c, hc⟩ := hmul_of_normalized Fr h01 s₀ t₀ hspan hm gL hginj hμL hμ0 hI1 hc0 hc1 hj0 hj1
    hjc s₁ t₁ hcomm hnorm i hi0 hi1 s
  exact ⟨c, by rw [← hgL]; exact hc⟩

end GroupLevel

end CFSG.ClassicalInvolution.ModelFacts.OrthAut
