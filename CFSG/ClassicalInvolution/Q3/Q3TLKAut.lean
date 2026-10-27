module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Lift
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WL65

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
open CFSG.ClassicalInvolution.G2D4Models.Twin (LiftSimAt)
open scoped MatrixGroups

section Lift

theorem sl2_eq_mul_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (A : SL(2, K)) :
    ∃ x y : SL(2, K), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ (x⁻¹ * A * y⁻¹) ^ 3 = 1 := by
  obtain ⟨ε⟩ := Q3W.nonempty_ringEquiv_zmod_three hK
  set e : SL(2, K) ≃* SL(2, ZMod 3) := Q3W.slEquiv ε 2 with he
  obtain ⟨x, y, hx, hy, hc⟩ := Q3T.sl2Three_eq_mul_three (e A)
  refine ⟨e.symm x, e.symm y, ?_, ?_, ?_⟩
  · rw [← map_pow, hx, map_one]
  · rw [← map_pow, hy, map_one]
  · have h : (e.symm x)⁻¹ * A * (e.symm y)⁻¹ = e.symm (x⁻¹ * e A * y⁻¹) := by
      simp [map_mul, map_inv]
    rw [h, ← map_pow, hc, map_one]

theorem fixed_of_pow_three {N : Type*} [Group N] (α : N ≃* N)
    (hZ3 : ∀ c ∈ Subgroup.center N, ¬ 3 ∣ orderOf c) {s : N} (hs3 : s ^ 3 = 1)
    (hz : s⁻¹ * α s ∈ Subgroup.center N) : α s = s := by
  set z : N := s⁻¹ * α s with hzdef
  have hαs : α s = s * z := by rw [hzdef]; group
  have hz3 : z ^ 3 = 1 := by
    have h1 : (α s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
    have h2 : (s * z) ^ 3 = s ^ 3 * z ^ 3 := Commute.mul_pow (Subgroup.mem_center_iff.mp hz s) 3
    rw [hαs, h2, hs3, one_mul] at h1
    exact h1
  have hz1 : z = 1 := by
    by_contra hne
    have h3 : orderOf z = 3 := orderOf_eq_prime hz3 hne
    exact hZ3 z hz (by rw [h3])
  rw [hαs, hz1, mul_one]

theorem exists_fixed_lift_of_pow_three {N M : Type*} [Group N] [Group M] (θ : N →* M)
    (hker : θ.ker ≤ Subgroup.center N) (hZ3 : ∀ c ∈ Subgroup.center N, ¬ 3 ∣ orderOf c)
    (α : N ≃* N) {P : Subgroup M} (hP : P ≤ θ.range)
    (hcentral : ∀ s ∈ P.comap θ, s⁻¹ * α s ∈ Subgroup.center N) {g : M} (hg : g ∈ P)
    (hg3 : g ^ 3 = 1) : ∃ s : N, θ s = g ∧ α s = s := by
  obtain ⟨s₀, hs₀⟩ := hP hg
  have hker3 : s₀ ^ 3 ∈ θ.ker := by rw [MonoidHom.mem_ker, map_pow, hs₀, hg3]
  have hm : ¬ 3 ∣ orderOf (s₀ ^ 3) := hZ3 _ (hker hker3)
  set s : N := s₀ ^ (orderOf (s₀ ^ 3) * orderOf (s₀ ^ 3)) with hs
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← pow_mul, mul_comm _ 3, pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_mul_right _ _)
  have hθs : θ s = g := by
    rw [hs, map_pow, hs₀, pow_eq_pow_mod _ hg3, Q3T.mul_self_mod_three hm, pow_one]
  have hsP : s ∈ P.comap θ := by
    rw [Subgroup.mem_comap, hθs]
    exact hg
  exact ⟨s, hθs, fixed_of_pow_three α hZ3 hs3 (hcentral s hsP)⟩

theorem exists_fixed_lift_of_sl2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {N M : Type*} [Group N] [Group M] (θ : N →* M) (hker : θ.ker ≤ Subgroup.center N)
    (hZ3 : ∀ c ∈ Subgroup.center N, ¬ 3 ∣ orderOf c) (α : N ≃* N) {P : Subgroup M}
    (hP : P ≤ θ.range) (hcentral : ∀ s ∈ P.comap θ, s⁻¹ * α s ∈ Subgroup.center N)
    (f : SL(2, K) →* M) (hf : ∀ A, f A ∈ P) (A : SL(2, K)) :
    ∃ s : N, θ s = f A ∧ α s = s := by
  obtain ⟨x, y, hx, hy, hc⟩ := sl2_eq_mul_three hK A
  have key : ∀ B : SL(2, K), B ^ 3 = 1 → ∃ s : N, θ s = f B ∧ α s = s := fun B hB =>
    exists_fixed_lift_of_pow_three θ hker hZ3 α hP hcentral (hf B)
      (by rw [← map_pow, hB, map_one])
  obtain ⟨sx, hsx, hαx⟩ := key x hx
  obtain ⟨sy, hsy, hαy⟩ := key y hy
  obtain ⟨sc, hsc, hαc⟩ := key _ hc
  refine ⟨sx * sc * sy, ?_, ?_⟩
  · have hA : f A = f x * f (x⁻¹ * A * y⁻¹) * f y := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    rw [hA, map_mul, map_mul, hsx, hsy, hsc]
  · rw [map_mul, map_mul, hαx, hαy, hαc]

end Lift

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem exists_aut_of_centralizing_at3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (σ : ↥ψ.range ≃* ↥ψ.range) (hlift : LiftSimAt Q ψ σ)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (a : (ι → F) ≃ₗ[F] (ι → F)) (c : F),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) ∧
      (∀ x ∈ fr.span, a x = c • x) ∧ (∃ μ : Fˣ, (μ : F) = c ^ 2 ∧
        ∀ v, Q (a v) = μ * Q v) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  obtain ⟨α, hαψ, A, φ, μ, hsim, hmat⟩ := hlift
  set P : Subgroup ((ι → F) ≃ₗ[F] (ι → F)) := fr.La.range ⊔ fr.swap.La.range with hP
  have hPE : P ≤ θ.range := by
    rw [hrange]
    exact sup_le (fun g ⟨A, hA⟩ => hA ▸ fr.La_mem_elementaryGroup A)
      (fun g ⟨A, hA⟩ => hA ▸ fr.swap.La_mem_elementaryGroup A)
  have hcentral : ∀ s ∈ P.comap θ, s⁻¹ * α s ∈ Subgroup.center (spinGroup Q) := by
    intro s hs
    have hℓ := hσ s (Subgroup.mem_comap.mp hs)
    set x := ψ.rangeRestrict s with hx
    have hζ : ∀ m : ↥ψ.range, (x⁻¹ * σ x) * m = m * (x⁻¹ * σ x) := by
      intro m
      obtain ⟨ℓ, rfl⟩ := σ.surjective m
      have h1 := hℓ ℓ
      rw [map_mul, map_mul, map_inv] at h1
      calc x⁻¹ * σ x * σ ℓ = x⁻¹ * (σ x * σ ℓ * (σ x)⁻¹) * σ x := by group
        _ = x⁻¹ * (x * σ ℓ * x⁻¹) * σ x := by rw [h1]
        _ = σ ℓ * (x⁻¹ * σ x) := by group
    refine Orth15.mem_center_of_commutators_central fun t => hψ ?_
    rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_commutatorElement, map_mul,
      map_inv, hαψ s]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hζ _)
  have hfixLa : ∀ B : SL(2, F), ∃ s : spinGroup Q, θ s = fr.La B ∧ α s = s := fun B =>
    exists_fixed_lift_of_sl2 hF3 θ (ker_spinAction_le_center Q) hZ3 α hPE hcentral fr.La
      (fun B' => Subgroup.mem_sup_left ⟨B', rfl⟩) B
  have hfixSw : ∀ B : SL(2, F), ∃ s : spinGroup Q, θ s = fr.swap.La B ∧ α s = s := fun B =>
    exists_fixed_lift_of_sl2 hF3 θ (ker_spinAction_le_center Q) hZ3 α hPE hcentral fr.swap.La
      (fun B' => Subgroup.mem_sup_right ⟨B', rfl⟩) B
  have hN : (LinearMap.toMatrix' (nuLin fr)) ≠ 0 := by
    intro h0
    exact nuLin_ne_zero fr ((LinearMap.toMatrix').injective (by rw [h0, map_zero]))
  have hφ : φ = RingEquiv.refl F := by
    refine ringEquiv_eq_refl_of_commute (LinearMap.toMatrix' (nuLin fr)) hN A φ fun c => ?_
    obtain ⟨s, hsg, hαs⟩ := hfixLa
      (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) c)
    have hm := hmat s
    rw [hαs] at hm
    have hM : ((spinMatrix Q s : GL ι F) : Matrix ι ι F) =
        1 + c • LinearMap.toMatrix' (nuLin fr) := by
      rw [coe_spinMatrix, hsg]
      have := La_transvection_eq fr c
      rw [show ((fr.La (Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 2) ≠ 1 by decide) c) : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) →ₗ[F] (ι → F)) =
          1 + c • nuLin fr from this, map_add, map_smul, LinearMap.toMatrix'_one]
    have hMA : ((spinMatrix Q s : GL ι F) : Matrix ι ι F) * (A : Matrix ι ι F) =
        (A : Matrix ι ι F) * (((spinMatrix Q s : GL ι F) : Matrix ι ι F).map φ) := by
      set G := glFieldEquiv ι φ (spinMatrix Q s) with hG
      have h1 : spinMatrix Q s * A = A * G := by
        calc spinMatrix Q s * A = (A * G * A⁻¹) * A := by rw [← hm]
          _ = A * G := by group
      have h2' := congrArg (fun g : GL ι F => (g : Matrix ι ι F)) h1
      simp only [Units.val_mul] at h2'
      have hGm : (G : Matrix ι ι F) = ((spinMatrix Q s : GL ι F) : Matrix ι ι F).map φ := by
        ext i j
        exact glFieldEquiv_entry ι φ _ i j
      rw [hGm] at h2'
      exact h2'
    rw [hM] at hMA
    exact hMA.symm
  subst hφ
  have hmat' : ∀ x, spinMatrix Q (α x) = A * spinMatrix Q x * A⁻¹ := by
    intro x
    rw [hmat x, glFieldEquiv_refl]
  set a : (ι → F) ≃ₗ[F] (ι → F) := glLin A with ha
  have hθα : ∀ x, θ (α x) = a * θ x * a⁻¹ := by
    intro x
    rw [← glLin_spinMatrix, hmat', map_mul, map_mul, map_inv, glLin_spinMatrix]
  have hcomm : ∀ (g : (ι → F) ≃ₗ[F] (ι → F)) (s : spinGroup Q), θ s = g → α s = s →
      a * g = g * a := by
    intro g s hsg hαs
    have h1 := hθα s
    rw [hαs, hsg] at h1
    calc a * g = (a * g * a⁻¹) * a := by group
      _ = g * a := by rw [← h1]
  obtain ⟨⟨c, hc⟩, -⟩ := scalar_on_span_of_commute h2 fr
    (fun A₀ => by
      obtain ⟨s, hsg, hαs⟩ := hfixLa A₀
      exact hcomm _ s hsg hαs)
    (fun B₀ => by
      obtain ⟨s, hsg, hαs⟩ := hfixSw B₀
      exact hcomm _ s hsg hαs)
  have hsim' : ∀ v, Q (a v) = μ * Q v := by
    intro v
    have := hsim v
    simpa [ha, glLin_apply] using this
  refine ⟨α, a, c, hαψ, hθα, hc, μ, ?_, hsim'⟩
  have hv := hsim' (fr.incl 1)
  rw [hc _ ⟨1, rfl⟩, QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one] at hv
  rw [pow_two]
  simpa using hv.symm

end Core

section Final

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem exists_isometry_of_centralizing_at3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (σ : ↥ψ.range ≃* ↥ψ.range) (hlift : LiftSimAt Q ψ σ)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (w : (ι → F) ≃ₗ[F] (ι → F)),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ x ∈ fr.span, w x = x) ∧
      ∀ x, spinAction Q (α x) = w * spinAction Q x * w⁻¹ := by
  classical
  set θ := spinAction Q with hθ
  obtain ⟨α, a, c, hαψ, hθα, hc, μ, hμc, hsim⟩ :=
    exists_aut_of_centralizing_at3 hodd hF3 hrange hZ3 fr hψ σ hlift hσ
  have hc0 : c ≠ 0 := by
    intro h0
    apply μ.ne_zero
    rw [hμc, h0]
    ring
  set sm : (ι → F) ≃ₗ[F] (ι → F) := LinearEquiv.smulOfNeZero F (ι → F) c hc0 with hsm_def
  set sm' : (ι → F) ≃ₗ[F] (ι → F) :=
    LinearEquiv.smulOfNeZero F (ι → F) c⁻¹ (inv_ne_zero hc0) with hsm'_def
  have hsm_comm : ∀ g : (ι → F) ≃ₗ[F] (ι → F), sm * g = g * sm := fun g => by
    ext x
    simp [sm]
  have hsm_inv : sm * sm' = 1 := by
    ext x
    simp [sm, sm', hc0]
  set w : (ι → F) ≃ₗ[F] (ι → F) := sm' * a with hw
  have ha : a = sm * w := by rw [hw, ← mul_assoc, hsm_inv, one_mul]
  have hwspan : ∀ x ∈ fr.span, w x = x := by
    intro x hx
    rw [hw, LinearEquiv.mul_apply, hc x hx]
    simp [sm', hc0]
  have hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have h1 : w x = c⁻¹ • a x := by
      rw [hw, LinearEquiv.mul_apply]
      simp [sm']
    rw [h1, QuadraticMap.map_smul, hsim, hμc]
    simp only [smul_eq_mul]
    field_simp
  have hθw : ∀ x, θ (α x) = w * θ x * w⁻¹ := by
    intro x
    rw [hθα, ha, _root_.mul_inv_rev]
    calc sm * w * θ x * (w⁻¹ * sm⁻¹) = sm * (w * θ x * w⁻¹) * sm⁻¹ := by group
      _ = (w * θ x * w⁻¹) * sm * sm⁻¹ := by rw [hsm_comm]
      _ = w * θ x * w⁻¹ := by group
  exact ⟨α, w, hαψ, hwiso, hwspan, hθw⟩

theorem exists_isometry_of_centralizing3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (fr : Frame Q) {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSim Q ψ) (σ : ↥ψ.range ≃* ↥ψ.range)
    (hσ : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, σ (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * σ ℓ * (ψ.rangeRestrict s)⁻¹) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (w : (ι → F) ≃ₗ[F] (ι → F)),
      (∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x)) ∧
      w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ x ∈ fr.span, w x = x) ∧
      ∀ x, spinAction Q (α x) = w * spinAction Q x * w⁻¹ :=
  exists_isometry_of_centralizing_at3 hodd hF3 hrange hZ3 fr hψ σ (hlift σ) hσ

end Final

end CFSG.ClassicalInvolution.Q3.Q3TLK
