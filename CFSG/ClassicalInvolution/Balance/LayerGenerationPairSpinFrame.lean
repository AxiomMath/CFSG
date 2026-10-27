module

public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

section Family

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def hypPairVec (P : HypPair Q) (s : Bool) : V := cond s P.e P.f

@[expose] def hypPairFam {m : ℕ} (P : Fin m → HypPair Q) : Fin m → Bool → V :=
  fun i s => hypPairVec (P i) s

theorem isHypFam_hypPairFam {m : ℕ} (P : Fin m → HypPair Q)
    (h : ∀ i j, i ≠ j → (P i).Orth (P j)) : IsHypFam Q (hypPairFam P) := by
  refine ⟨fun i s => ?_, fun i j hij s t => ?_, fun i s => ?_⟩
  · cases s
    · exact (P i).Q_f
    · exact (P i).Q_e
  · have := h i j hij
    cases s <;> cases t
    · exact this.ff
    · exact this.fe
    · exact this.ef
    · exact this.ee
  · cases s
    · exact (P i).polar_fe
    · exact (P i).polar_ef

end Family

section Normalization

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Invertible (2 : F)] [FiniteDimensional F V]

theorem exists_spin_normalization_isometry [Finite F] [Nontrivial V] (hodd : Odd (Nat.card F))
    (hQ : Q.Nondegenerate) {m : ℕ} {v v' : Fin m → Bool → V} (hv : IsHypFam Q v)
    (hv' : IsHypFam Q v') {P : Submodule F V} (hP : (Q.restrict P).Nondegenerate)
    (hP2 : 2 ≤ Module.finrank F P) :
    ∃ (x : spinGroup Q) (h : V ≃ₗ[F] V), h ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ y ∈ P, h y ∈ P) ∧ (∀ z, (∀ y ∈ P, polar Q y z = 0) → h z = z) ∧
        ∀ i s, v' i s = spinAction Q x (h (v i s)) := by
  obtain ⟨ω, hω, hωv⟩ := exists_isometry_of_isHypFam hv hv'
  have hQ' : (polarBilin Q).Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hWP : ∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P, ∀ y ∈ P, polar Q y x = 0 :=
    fun x hx y hy => by
      have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) y hy
      simpa [polarBilin_apply_apply] using this
  obtain ⟨h₁, hfix, hdet, hsn⟩ := exists_reflection_correction hodd hQ hWP hP hP2 ⟨ω, hω⟩
  have hd : QuadraticMap.orthogonalDet Q (⟨ω, hω⟩ * h₁) = 1 := by
    rw [map_mul, hdet, ← pow_two]
    exact TauCeti.QuadraticMap.orthogonalDet_sq hQ'.1 ⟨ω, hω⟩
  have hs : CliffordAlgebra.orthogonalSpinorNorm Q hQ (⟨ω, hω⟩ * h₁) = 1 := by
    rw [map_mul, hsn]
    exact mul_inv_cancel _
  obtain ⟨x, hx⟩ := exists_spinAction_eq hQ _ hd hs
  have hfix' : ∀ z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P,
      (h₁ : V ≃ₗ[F] V) z = z := hfix
  have hpres := mem_of_fixes_orthogonal hQ' h₁.2 P hfix'
  refine ⟨x, (h₁ : V ≃ₗ[F] V).symm, (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem h₁.2,
    symm_mem_of_mem _ P hpres, fun z hz => ?_, fun i s => ?_⟩
  · have hz' : z ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) P :=
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn => by
        simpa [polarBilin_apply_apply] using hz n hn
    rw [LinearEquiv.symm_apply_eq]
    exact (hfix' z hz').symm
  · rw [hx]
    change v' i s = ω ((h₁ : V ≃ₗ[F] V) ((h₁ : V ≃ₗ[F] V).symm (v i s)))
    rw [LinearEquiv.apply_symm_apply, hωv]

end Normalization

section FrameLemmas

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem La_neg_one_of_mem_span (fr : Frame Q) {x : V} (hx : x ∈ fr.span) :
    fr.La (-1) x = -x := by
  rw [Frame.La_neg_one_apply, ← (Frame.mem_span_iff fr).mp hx, two_smul]
  abel

theorem La_neg_one_of_mem_perp (fr : Frame Q) {x : V} (hx : x ∈ fr.perp) :
    fr.La (-1) x = x := by
  rw [Frame.La_neg_one_apply, (Frame.mem_perp_iff fr).mp hx]
  simp

theorem mem_perp_map_of_smul (fr : Frame Q) {T : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {ε : F} (hε : ε * ε = 1)
    (hTε : ∀ Y, T (fr.incl Y) = ε • fr.incl Y) {r : V} (hr : r ∈ fr.perp) : T r ∈ fr.perp := by
  rw [Frame.mem_perp_iff_forall_incl] at hr ⊢
  intro Y
  have h1 : fr.incl Y = ε • T (fr.incl Y) := by rw [hTε, smul_smul, hε, one_smul]
  rw [h1, polar_smul_right, polar_map_of_mem hT, hr, smul_zero]

theorem comm_La_of_smul (fr : Frame Q) {T : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {ε : F} (hε : ε * ε = 1)
    (hTε : ∀ Y, T (fr.incl Y) = ε • fr.incl Y) (A : SL(2, F)) :
    T * fr.La A = fr.La A * T := by
  refine LinearEquiv.ext fun x => ?_
  have key : ∀ (c : Matrix (Fin 2) (Fin 2) F) (r : V), r ∈ fr.perp →
      T (fr.La A (fr.incl c + r)) = fr.La A (T (fr.incl c + r)) := by
    intro c r hr
    have hTr := mem_perp_map_of_smul fr hT hε hTε hr
    have e1 : fr.La A (fr.incl c + r) =
        fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * c) + r := by
      rw [map_add, Frame.La_apply_incl, Frame.La_apply_of_coords_eq_zero fr A
        ((Frame.mem_perp_iff fr).mp hr)]
    have e2 : T (fr.incl c + r) = ε • fr.incl c + T r := by rw [map_add, hTε]
    have e3 : fr.La A (ε • fr.incl c + T r) =
        ε • fr.incl ((A : Matrix (Fin 2) (Fin 2) F) * c) + T r := by
      rw [map_add, map_smul, Frame.La_apply_incl, Frame.La_apply_of_coords_eq_zero fr A
        ((Frame.mem_perp_iff fr).mp hTr)]
    rw [e1, e2, e3, map_add, hTε]
  have hr : x - fr.incl (fr.coords x) ∈ fr.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have := key (fr.coords x) (x - fr.incl (fr.coords x)) hr
  rwa [add_sub_cancel] at this

theorem incl_smul_of_vectors (fr : Frame Q) {T : V ≃ₗ[F] V} {ε : F} (h1 : T fr.e₁ = ε • fr.e₁)
    (h2 : T fr.f₁ = ε • fr.f₁) (h3 : T fr.e₂ = ε • fr.e₂) (h4 : T fr.f₂ = ε • fr.f₂)
    (Y : Matrix (Fin 2) (Fin 2) F) : T (fr.incl Y) = ε • fr.incl Y := by
  rw [Frame.incl_apply]
  simp only [map_add, map_smul, h1, h2, h3, h4]
  module

theorem map_central_eq_one_or_neg_one {K : Type} [Group K] (θ : K →* (V ≃ₗ[F] V)) (R : Subgroup K)
    (fr : Frame Q) (hR : R.map θ = fr.La.range) {c : K} (hc : c ∈ R)
    (hcc : ∀ r ∈ R, c * r = r * c) : θ c = 1 ∨ θ c = fr.La (-1) := by
  have hmem : θ c ∈ fr.La.range := hR ▸ ⟨c, hc, rfl⟩
  obtain ⟨A, hA⟩ := hmem
  have hcent : A ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have hB : fr.La B ∈ R.map θ := hR ▸ ⟨B, rfl⟩
    obtain ⟨r, hr, hrB⟩ := hB
    have h1 : θ c * θ r = θ r * θ c := by rw [← map_mul, ← map_mul, hcc r hr]
    rw [← hA, hrB] at h1
    apply fr.La_injective
    rw [map_mul, map_mul]
    exact h1.symm
  rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff A).1 hcent with h | h
  · left
    rw [← hA, h, map_one]
  · right
    rw [← hA, h]

end FrameLemmas

section StdFrame

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
  (F₀ : HypFrame Q m)

theorem vec_mem_span_toFrame {i j : Fin m} (hij : i ≠ j) (s t : Bool) {k : Fin m}
    (hk : k = i ∨ k = j) (r : Bool) : F₀.vec k r ∈ (F₀.toFrame hij s t).span := by
  rcases hk with rfl | rfl
  · by_cases hr : r = s
    · subst hr
      exact Frame.e₁_mem_span (F₀.toFrame hij r t)
    · have : r = !s := by cases r <;> cases s <;> simp_all
      subst this
      exact Frame.f₁_mem_span (F₀.toFrame hij s t)
  · by_cases hr : r = t
    · subst hr
      exact Frame.e₂_mem_span (F₀.toFrame hij s r)
    · have : r = !t := by cases r <;> cases t <;> simp_all
      subst this
      exact Frame.f₂_mem_span (F₀.toFrame hij s t)

theorem vec_mem_perp_toFrame {i j : Fin m} (hij : i ≠ j) (s t : Bool) {k : Fin m} (hki : k ≠ i)
    (hkj : k ≠ j) (r : Bool) : F₀.vec k r ∈ (F₀.toFrame hij s t).perp := by
  rw [Frame.mem_perp_iff]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Frame.coords_apply, HypFrame.toFrame, F₀.polar_vec_of_ne hki, F₀.polar_vec_of_ne hkj]

theorem La_neg_one_toFrame_vec {i j : Fin m} (hij : i ≠ j) (s t : Bool) (k : Fin m) (r : Bool) :
    (F₀.toFrame hij s t).La (-1) (F₀.vec k r) =
      (if k = i ∨ k = j then (-1 : F) else 1) • F₀.vec k r := by
  by_cases hk : k = i ∨ k = j
  · rw [ite_eq_left hk, La_neg_one_of_mem_span _ (vec_mem_span_toFrame F₀ hij s t hk r),
      neg_one_smul]
  · push Not at hk
    rw [ite_eq_right (by push Not; exact hk), La_neg_one_of_mem_perp _
      (vec_mem_perp_toFrame F₀ hij s t hk.1 hk.2 r), one_smul]

theorem polar_incl_toFrame_of_disjoint {i j k l : Fin m} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (s t s' t' : Bool) (X Y : Matrix (Fin 2) (Fin 2) F) :
    polar Q ((F₀.toFrame hij s t).incl X) ((F₀.toFrame hkl s' t').incl Y) = 0 := by
  simp only [Frame.incl_apply, polar_add_left, polar_add_right, polar_smul_left,
    polar_smul_right]
  simp [HypFrame.toFrame, F₀.polar_vec_of_ne hik, F₀.polar_vec_of_ne hil, F₀.polar_vec_of_ne hjk,
    F₀.polar_vec_of_ne hjl]

theorem comm_La_toFrame_of_sign {T : V ≃ₗ[F] V}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ : Fin m → F} (hσ : ∀ i, σ i * σ i = 1)
    (hTσ : ∀ i r, T (F₀.vec i r) = σ i • F₀.vec i r) {k l : Fin m} (hkl : k ≠ l) (s t : Bool)
    (hσkl : σ k = σ l) (A : SL(2, F)) :
    T * (F₀.toFrame hkl s t).La A = (F₀.toFrame hkl s t).La A * T :=
  comm_La_of_smul (F₀.toFrame hkl s t) hT (hσ k)
    (incl_smul_of_vectors _ (hTσ k s) (hTσ k (!s))
      (by have := hTσ l t; rw [← hσkl] at this; exact this)
      (by have := hTσ l (!t); rw [← hσkl] at this; exact this)) A

theorem exists_comm_toFrame_of_pairs {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) {k l : Fin m}
    (hkl : k ≠ l) (s t : Bool) :
    (∀ A : SL(2, F), (F₀.toFrame hab true true).La (-1) * (F₀.toFrame hkl s t).La A =
      (F₀.toFrame hkl s t).La A * (F₀.toFrame hab true true).La (-1)) ∨
    (∀ A : SL(2, F), (F₀.toFrame hcd true true).La (-1) * (F₀.toFrame hkl s t).La A =
      (F₀.toFrame hkl s t).La A * (F₀.toFrame hcd true true).La (-1)) ∨
    (∀ A : SL(2, F), ((F₀.toFrame hab true true).La (-1) * (F₀.toFrame hcd true true).La (-1)) *
      (F₀.toFrame hkl s t).La A =
      (F₀.toFrame hkl s t).La A *
        ((F₀.toFrame hab true true).La (-1) * (F₀.toFrame hcd true true).La (-1))) := by
  set T₁ := (F₀.toFrame hab true true).La (-1) with hT₁
  set T₂ := (F₀.toFrame hcd true true).La (-1) with hT₂
  have hO₁ : T₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Frame.La_mem_orthogonalGroup _ _
  have hO₂ : T₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Frame.La_mem_orthogonalGroup _ _
  let σ₁ : Fin m → F := fun i => if i = a ∨ i = b then (-1 : F) else 1
  let σ₂ : Fin m → F := fun i => if i = c ∨ i = d then (-1 : F) else 1
  have hσ₁ : ∀ i, σ₁ i * σ₁ i = 1 := fun i => by
    by_cases h : i = a ∨ i = b <;> simp [σ₁, h]
  have hσ₂ : ∀ i, σ₂ i * σ₂ i = 1 := fun i => by
    by_cases h : i = c ∨ i = d <;> simp [σ₂, h]
  have hT₁σ : ∀ i r, T₁ (F₀.vec i r) = σ₁ i • F₀.vec i r := fun i r =>
    La_neg_one_toFrame_vec F₀ hab true true i r
  have hT₂σ : ∀ i r, T₂ (F₀.vec i r) = σ₂ i • F₀.vec i r := fun i r =>
    La_neg_one_toFrame_vec F₀ hcd true true i r
  have hT₁₂σ : ∀ i r, (T₁ * T₂) (F₀.vec i r) = (σ₁ i * σ₂ i) • F₀.vec i r := fun i r => by
    rw [LinearEquiv.mul_apply, hT₂σ, map_smul, hT₁σ, smul_smul, mul_comm]
  have hO₁₂ : T₁ * T₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem hO₁ hO₂
  by_cases h1 : σ₁ k = σ₁ l
  · exact Or.inl (comm_La_toFrame_of_sign F₀ hO₁ hσ₁ hT₁σ hkl s t h1)
  by_cases h2 : σ₂ k = σ₂ l
  · exact Or.inr (Or.inl (comm_La_toFrame_of_sign F₀ hO₂ hσ₂ hT₂σ hkl s t h2))
  refine Or.inr (Or.inr (comm_La_toFrame_of_sign F₀ hO₁₂ (σ := fun i => σ₁ i * σ₂ i)
    (fun i => by
      have := hσ₁ i
      have := hσ₂ i
      calc σ₁ i * σ₂ i * (σ₁ i * σ₂ i) = (σ₁ i * σ₁ i) * (σ₂ i * σ₂ i) := by ring
        _ = 1 := by rw [hσ₁ i, hσ₂ i, mul_one]) hT₁₂σ hkl s t ?_))
  have hpm : ∀ x y : F, x * x = 1 → y * y = 1 → x ≠ y → y = -x := by
    intro x y hx hy hxy
    have h : (x - y) * (x + y) = 0 := by linear_combination hx - hy
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hxy
    · linear_combination h
  have e1 := hpm _ _ (hσ₁ k) (hσ₁ l) h1
  have e2 := hpm _ _ (hσ₂ k) (hσ₂ l) h2
  show σ₁ k * σ₂ k = σ₁ l * σ₂ l
  rw [e1, e2]
  ring

end StdFrame

section Pair

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem frame_pairs_orth {fr fr' : Frame Q}
    (h : ∀ X Y, polar Q (fr.incl X) (fr'.incl Y) = 0) :
    fr.P.Orth fr'.P ∧ fr.P.Orth fr'.P' ∧ fr.P'.Orth fr'.P ∧ fr.P'.Orth fr'.P' := by
  have e1 : fr.P.e = fr.incl !![1, 0; 0, 0] := Frame.e₁_eq_incl fr
  have f1 : fr.P.f = fr.incl !![0, 0; 0, 1] := Frame.f₁_eq_incl fr
  have e2 : fr.P'.e = fr.incl !![0, -1; 0, 0] := Frame.e₂_eq_incl fr
  have f2 : fr.P'.f = fr.incl !![0, 0; 1, 0] := Frame.f₂_eq_incl fr
  have e1' : fr'.P.e = fr'.incl !![1, 0; 0, 0] := Frame.e₁_eq_incl fr'
  have f1' : fr'.P.f = fr'.incl !![0, 0; 0, 1] := Frame.f₁_eq_incl fr'
  have e2' : fr'.P'.e = fr'.incl !![0, -1; 0, 0] := Frame.e₂_eq_incl fr'
  have f2' : fr'.P'.f = fr'.incl !![0, 0; 1, 0] := Frame.f₂_eq_incl fr'
  have hh : ∀ (u v : V) (X Y : Matrix (Fin 2) (Fin 2) F), u = fr.incl X → v = fr'.incl Y →
      polar Q u v = 0 := fun u v X Y hu hv => by rw [hu, hv]; exact h X Y
  exact ⟨⟨hh _ _ _ _ e1 e1', hh _ _ _ _ e1 f1', hh _ _ _ _ f1 e1', hh _ _ _ _ f1 f1'⟩,
    ⟨hh _ _ _ _ e1 e2', hh _ _ _ _ e1 f2', hh _ _ _ _ f1 e2', hh _ _ _ _ f1 f2'⟩,
    ⟨hh _ _ _ _ e2 e1', hh _ _ _ _ e2 f1', hh _ _ _ _ f2 e1', hh _ _ _ _ f2 f1'⟩,
    ⟨hh _ _ _ _ e2 e2', hh _ _ _ _ e2 f2', hh _ _ _ _ f2 e2', hh _ _ _ _ f2 f2'⟩⟩

theorem frames_pairs_pairwise_orth {fr fr' : Frame Q}
    (h : ∀ X Y, polar Q (fr.incl X) (fr'.incl Y) = 0) :
    ∀ i j : Fin 4, i ≠ j →
      (![fr.P, fr.P', fr'.P, fr'.P'] i).Orth (![fr.P, fr.P', fr'.P, fr'.P'] j) := by
  obtain ⟨s02, s03, s12, s13⟩ := frame_pairs_orth h
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact fr.orth
    | exact fr.orth.symm
    | exact fr'.orth
    | exact fr'.orth.symm
    | exact s02
    | exact s02.symm
    | exact s03
    | exact s03.symm
    | exact s12
    | exact s12.symm
    | exact s13
    | exact s13.symm

theorem map_incl_eq_of_vectors {g : V ≃ₗ[F] V} {fr fr' : Frame Q} (h1 : g fr.e₁ = fr'.e₁)
    (h2 : g fr.f₁ = fr'.f₁) (h3 : g fr.e₂ = fr'.e₂) (h4 : g fr.f₂ = fr'.f₂)
    (Y : Matrix (Fin 2) (Fin 2) F) : g (fr.incl Y) = fr'.incl Y := by
  rw [Frame.incl_apply, Frame.incl_apply]
  simp only [map_add, map_smul, h1, h2, h3, h4]

theorem comm_La_neg_one_of_preserves (fr : Frame Q) {h : V ≃ₗ[F] V}
    (hspan : ∀ y ∈ fr.span, h y ∈ fr.span) (hperp : ∀ r ∈ fr.perp, h r = r) :
    h * fr.La (-1) = fr.La (-1) * h := by
  refine LinearEquiv.ext fun y => ?_
  have hr : y - fr.incl (fr.coords y) ∈ fr.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have hu : fr.incl (fr.coords y) ∈ fr.span := ⟨_, rfl⟩
  have hy : y = fr.incl (fr.coords y) + (y - fr.incl (fr.coords y)) := by abel
  have hhu := hspan _ hu
  have e1 : fr.La (-1) y = -fr.incl (fr.coords y) + (y - fr.incl (fr.coords y)) := by
    conv_lhs => rw [hy]
    rw [map_add, La_neg_one_of_mem_span fr hu, La_neg_one_of_mem_perp fr hr]
  have e2 : h y = h (fr.incl (fr.coords y)) + (y - fr.incl (fr.coords y)) := by
    conv_lhs => rw [hy]
    rw [map_add, hperp _ hr]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, map_add, map_neg, hperp _ hr, e2, map_add,
    La_neg_one_of_mem_span fr hhu, La_neg_one_of_mem_perp fr hr]

theorem exists_spin_conj_orth_pair [Finite F] [FiniteDimensional F V] [Nontrivial V]
    (hodd : Odd (Nat.card F)) (hQ : Q.Nondegenerate) (std₁ std₂ fr₁ fr₂ : Frame Q)
    (hstd : ∀ X Y, polar Q (std₁.incl X) (std₂.incl Y) = 0)
    (hfr : ∀ X Y, polar Q (fr₁.incl X) (fr₂.incl Y) = 0) :
    ∃ x : spinGroup Q,
      spinAction Q x * std₁.La (-1) * (spinAction Q x)⁻¹ = fr₁.La (-1) ∧
      spinAction Q x * std₂.La (-1) * (spinAction Q x)⁻¹ = fr₂.La (-1) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  obtain ⟨s02, s03, s12, s13⟩ := frame_pairs_orth hstd
  obtain ⟨t02, t03, t12, t13⟩ := frame_pairs_orth hfr
  let Pstd : Fin 4 → HypPair Q := ![std₁.P, std₁.P', std₂.P, std₂.P']
  let Pfr : Fin 4 → HypPair Q := ![fr₁.P, fr₁.P', fr₂.P, fr₂.P']
  have hPstd : ∀ i j, i ≠ j → (Pstd i).Orth (Pstd j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact std₁.orth
      | exact std₁.orth.symm
      | exact std₂.orth
      | exact std₂.orth.symm
      | exact s02
      | exact s02.symm
      | exact s03
      | exact s03.symm
      | exact s12
      | exact s12.symm
      | exact s13
      | exact s13.symm
  have hPfr : ∀ i j, i ≠ j → (Pfr i).Orth (Pfr j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact fr₁.orth
      | exact fr₁.orth.symm
      | exact fr₂.orth
      | exact fr₂.orth.symm
      | exact t02
      | exact t02.symm
      | exact t03
      | exact t03.symm
      | exact t12
      | exact t12.symm
      | exact t13
      | exact t13.symm
  have hv := isHypFam_hypPairFam Pstd hPstd
  have hv' := isHypFam_hypPairFam Pfr hPfr
  have hP : (Q.restrict std₁.span).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_restrict (Frame.polarNondegOn_span std₁))
  have hP2 : 2 ≤ Module.finrank F std₁.span := by
    rw [Frame.finrank_span]
    norm_num
  obtain ⟨x, h, hhO, hhP, hhfix, hxeq⟩ :=
    exists_spin_normalization_isometry hodd hQ hv hv' hP hP2
  have hθ : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q x)
  set g : V ≃ₗ[F] V := spinAction Q x * h with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem hθ hhO
  have hgv : ∀ i s, g (hypPairFam Pstd i s) = hypPairFam Pfr i s := fun i s =>
    (hxeq i s).symm
  have hg1 : ∀ Y, g (std₁.incl Y) = fr₁.incl Y := fun Y =>
    map_incl_eq_of_vectors (hgv 0 true) (hgv 0 false) (hgv 1 true) (hgv 1 false) Y
  have hg2 : ∀ Y, g (std₂.incl Y) = fr₂.incl Y := fun Y =>
    map_incl_eq_of_vectors (hgv 2 true) (hgv 2 false) (hgv 3 true) (hgv 3 false) Y
  have hperp1 : ∀ r ∈ std₁.perp, h r = r := by
    intro r hr
    refine hhfix r fun y hy => ?_
    obtain ⟨Y, rfl⟩ := hy
    rw [polar_comm]
    exact (Frame.mem_perp_iff_forall_incl std₁).mp hr Y
  have hcomm : h * std₁.La (-1) = std₁.La (-1) * h :=
    comm_La_neg_one_of_preserves std₁ hhP hperp1
  have hfix2 : ∀ Y, h (std₂.incl Y) = std₂.incl Y := fun Y => by
    refine hhfix _ fun y hy => ?_
    obtain ⟨X, rfl⟩ := hy
    exact hstd X Y
  have hθ2 : ∀ Y, spinAction Q x (std₂.incl Y) = fr₂.incl Y := fun Y => by
    rw [← hg2 Y, hg, LinearEquiv.mul_apply, hfix2]
  refine ⟨x, ?_, ?_⟩
  · have h1 := Frame.map_La std₁ hgO (-1)
    rw [Frame.map_eq_of_incl hgO hg1] at h1
    rw [h1, hg]
    have h3 : h * std₁.La (-1) * h⁻¹ = std₁.La (-1) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hcomm
    calc spinAction Q x * std₁.La (-1) * (spinAction Q x)⁻¹
        = spinAction Q x * (h * std₁.La (-1) * h⁻¹) * (spinAction Q x)⁻¹ := by rw [h3]
      _ = spinAction Q x * h * std₁.La (-1) * (spinAction Q x * h)⁻¹ := by group
  · have h1 := Frame.map_La std₂ hθ (-1)
    rw [Frame.map_eq_of_incl hθ hθ2] at h1
    exact h1.symm

end Pair

end CFSG.ClassicalInvolution.Balance.Bootstrap
