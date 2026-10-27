module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Lift
public import CFSG.ClassicalInvolution.Q3.Q3TLKD4Fix
public import CFSG.ClassicalInvolution.Q3.Q3TLKAct
public import CFSG.ClassicalInvolution.RouteD.TWZLinkAux
public import CFSG.ClassicalInvolution.RouteD.TWZPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Q3.Q3TD
open CFSG.ClassicalInvolution.ModelFacts hiding fundamentalSubgroups
open scoped MatrixGroups commutatorElement


section Model3

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 𝔽₃
local notation "θ₄" => spinAction (quadPlus 4 𝔽₃)

section Lift

theorem exists_lift_isometry3_aut {X : Type} [Group X] (ψ : spinGroup Q₄ →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) (τ : X ≃* X)
    (hτr : ∀ k, τ (ψ k) ∈ ψ.range) (fr : OFrame Q₄) (A B : Subgroup (spinGroup Q₄))
    (hA : A.map θ₄ = fr.La.range) (hB : B.map θ₄ = fr.swap.La.range) (hAp : Pow3 A)
    (hBp : Pow3 B) (hfixA : ∀ r ∈ A, τ (ψ r) = ψ r) (hfixB : ∀ r ∈ B, τ (ψ r) = ψ r) :
    ∃ (α : spinGroup Q₄ ≃* spinGroup Q₄) (w : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)),
      (∀ y, ψ (α y) = τ (ψ y)) ∧ w ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ ∧
      (∀ x ∈ fr.span, w x = x) ∧ (∀ y, θ₄ (α y) = w * θ₄ y * w⁻¹) := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hfin : Finite (spinGroup Q₄) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hτL : ∀ l ∈ ψ.range, τ l ∈ ψ.range := by
    rintro _ ⟨k, rfl⟩
    exact hτr k
  have : Finite ↥ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  let σ : ↥ψ.range ≃* ↥ψ.range := RouteD.TWT4.restrictAut ψ.range τ hτL
  have hσc : ∀ l : ↥ψ.range, ((σ l : ↥ψ.range) : X) = τ l := fun l => rfl
  have hθker : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup Q₄) := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hC : ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup Q₄)) :=
    not_dvd_card_center_plus (p := 3) (f := 1) (by norm_num) hn3
  have hθC : ¬ 3 ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hθker))
  obtain ⟨α, hα⟩ := (ModelFacts.OrthAut.centralPSection_spinPlus (p := 3) hn3).exists_mulEquiv_lift
    ψ.rangeRestrict ψ.rangeRestrict_surjective hθker hθC σ
  have hαψ : ∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x) := hα
  have hαψ' : ∀ y, ψ (α y) = τ (ψ y) := fun y => congrArg Subtype.val (hαψ y)
  have hcenA : ∀ r ∈ A, r⁻¹ * α r ∈ Subgroup.center (spinGroup Q₄) := fun r hr => hψ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαψ', hfixA r hr, inv_mul_cancel])
  have hcenB : ∀ r ∈ B, r⁻¹ * α r ∈ Subgroup.center (spinGroup Q₄) := fun r hr => hψ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαψ', hfixB r hr, inv_mul_cancel])
  have hαA := eq_of_central_pow3 α hAp center_cop_spin4 hcenA
  have hαB := eq_of_central_pow3 α hBp center_cop_spin4 hcenB
  obtain ⟨w₀, hw₀Q, hθw₀⟩ := exists_isometry_lift3 hA hB hAp hBp hαA hαB
  have hcommA : ∀ A₁ : SL(2, 𝔽₃), w₀ * fr.La A₁ = fr.La A₁ * w₀ := by
    intro A₁
    have : fr.La A₁ ∈ A.map θ₄ := by
      rw [hA]
      exact ⟨A₁, rfl⟩
    obtain ⟨s, hs, hsA⟩ := this
    have h1 := hθw₀ s
    rw [hαA s hs, hsA] at h1
    calc w₀ * fr.La A₁ = (w₀ * fr.La A₁ * w₀⁻¹) * w₀ := by group
      _ = fr.La A₁ * w₀ := by rw [← h1]
  have hcommB : ∀ B₁ : SL(2, 𝔽₃), w₀ * fr.swap.La B₁ = fr.swap.La B₁ * w₀ := by
    intro B₁
    have : fr.swap.La B₁ ∈ B.map θ₄ := by
      rw [hB]
      exact ⟨B₁, rfl⟩
    obtain ⟨s, hs, hsB⟩ := this
    have h1 := hθw₀ s
    rw [hαB s hs, hsB] at h1
    calc w₀ * fr.swap.La B₁ = (w₀ * fr.swap.La B₁ * w₀⁻¹) * w₀ := by group
      _ = fr.swap.La B₁ * w₀ := by rw [← h1]
  obtain ⟨⟨c, hc⟩, -⟩ := scalar_on_span_of_commute h2 fr hcommA hcommB
  have he₁ : fr.e₁ ∈ fr.span := fr.e₁_mem_span
  have hc2 : c * c = 1 := by
    have hv := hw₀Q (fr.incl 1)
    rw [hc _ ⟨1, rfl⟩, QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one] at hv
    simpa using hv
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0] at hc2
    norm_num at hc2
  set sm : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃) :=
    LinearEquiv.smulOfNeZero 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) c hc0 with hsm_def
  set sm' : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃) :=
    LinearEquiv.smulOfNeZero 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) c⁻¹ (inv_ne_zero hc0) with hsm'_def
  have hsm_comm : ∀ g : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃), sm * g = g * sm :=
    fun g => by
    ext x
    simp [sm]
  have hsm_inv : sm * sm' = 1 := by
    ext x
    simp [sm, sm', hc0]
  set w : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃) := sm' * w₀ with hw
  have ha : w₀ = sm * w := by rw [hw, ← mul_assoc, hsm_inv, one_mul]
  have hwspan : ∀ x ∈ fr.span, w x = x := by
    intro x hx
    rw [hw, LinearEquiv.mul_apply, hc x hx]
    simp [sm', hc0]
  have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    have h1 : w x = c⁻¹ • w₀ x := by
      rw [hw, LinearEquiv.mul_apply]
      simp [sm']
    rw [h1, QuadraticMap.map_smul, hw₀Q]
    simp only [smul_eq_mul]
    rw [← mul_inv, hc2, inv_one, one_mul]
  have hθw : ∀ y, θ₄ (α y) = w * θ₄ y * w⁻¹ := by
    intro y
    rw [hθw₀, ha, _root_.mul_inv_rev]
    calc sm * w * θ₄ y * (w⁻¹ * sm⁻¹) = sm * (w * θ₄ y * w⁻¹) * sm⁻¹ := by group
      _ = (w * θ₄ y * w⁻¹) * sm * sm⁻¹ := by rw [hsm_comm]
      _ = w * θ₄ y * w⁻¹ := by group
  exact ⟨α, w, hαψ', hwO, hwspan, hθw⟩

end Lift

section Core

theorem fixes_of_isometry_fixing_span {frN : OFrame Q₄} {N : Subgroup (spinGroup Q₄)}
    (hN : N.map θ₄ = frN.La.range) (hNp : Pow3 N)
    {w : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄) (hw : ∀ x ∈ frN.span, w x = x)
    {α : spinGroup Q₄ ≃* spinGroup Q₄} (hα : ∀ y, θ₄ (α y) = w * θ₄ y * w⁻¹) :
    ∀ r ∈ N, α r = r := by
  have hmap : frN.map hwO = frN := Frame.map_eq_of_incl hwO fun Y => hw _ ⟨Y, rfl⟩
  have hfix : ∀ A' : SL(2, 𝔽₃), w * frN.La A' * w⁻¹ = frN.La A' := fun A' => by
    rw [← Frame.map_La frN hwO A', hmap]
  have hcen : ∀ r ∈ N, r⁻¹ * α r ∈ Subgroup.center (spinGroup Q₄) := by
    intro r hr
    have hmem : θ₄ r ∈ frN.La.range := hN ▸ Subgroup.mem_map_of_mem _ hr
    obtain ⟨A', hA'⟩ := hmem
    refine ker_spinAction_le_center Q₄ ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hα, ← hA', hfix, inv_mul_cancel]
  exact eq_of_central_pow3 α hNp center_cop_spin4 hcen

theorem parity_core3 {X : Type} [Group X] (ψ : spinGroup Q₄ →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) (σ : X ≃* X)
    (hσr : ∀ k, σ (ψ k) ∈ ψ.range) {fr fr₂ frN : OFrame Q₄}
    {A B C C' N : Subgroup (spinGroup Q₄)} (hA : A.map θ₄ = fr.La.range)
    (hB : B.map θ₄ = fr.swap.La.range) (hC : C.map θ₄ = fr₂.La.range)
    (hC' : C'.map θ₄ = fr₂.swap.La.range) (hN : N.map θ₄ = frN.La.range) (hAp : Pow3 A)
    (hBp : Pow3 B) (hCp : Pow3 C) (hC'p : Pow3 C') (hNp : Pow3 N) (hS : fr.span = fr₂.perp)
    {n xC : spinGroup Q₄} (hnθ : θ₄ n = frN.La (-1)) (hxCθ : θ₄ xC = fr₂.La (-1))
    (hnA : θ₄ n * fr.La (-1) = fr.La (-1) * θ₄ n)
    (hnC : θ₄ n * fr₂.La (-1) = fr₂.La (-1) * θ₄ n)
    (hσA : ∀ r ∈ A, σ (ψ r) = ψ r) (hσB : ∀ r ∈ B, σ (ψ r) = ψ r)
    (hσC : ∀ r ∈ C, σ (ψ r) = ψ (n * r * n⁻¹)) (hσC' : ∀ r ∈ C', σ (ψ r) = ψ (n * r * n⁻¹)) :
    (∀ r ∈ N, σ (ψ r) = ψ r) ∨ (∀ r ∈ N, σ (ψ (xC * r * xC⁻¹)) = ψ r) := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  obtain ⟨α, w₁, hαψ, hw₁O, hw₁S, hθα⟩ :=
    exists_lift_isometry3_aut ψ hψ σ hσr fr A B hA hB hAp hBp hσA hσB
  have hαfix : ∀ {R : Subgroup (spinGroup Q₄)}, Pow3 R →
      (∀ r ∈ R, σ (ψ r) = ψ (n * r * n⁻¹)) → ∀ r ∈ R, α r = n * r * n⁻¹ := by
    intro R hRp hσR
    set β : spinGroup Q₄ ≃* spinGroup Q₄ := α.trans (MulAut.conj n⁻¹) with hβ
    have hcen : ∀ r ∈ R, r⁻¹ * β r ∈ Subgroup.center (spinGroup Q₄) := by
      intro r hr
      refine hψ ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have h1 : ψ (β r) = (ψ n)⁻¹ * σ (ψ r) * ψ n := by
        rw [hβ]
        show ψ (n⁻¹ * α r * n⁻¹⁻¹) = _
        rw [map_mul, map_mul, map_inv, hαψ, inv_inv]
      rw [h1, hσR r hr, map_mul, map_mul, map_inv]
      group
    intro r hr
    have h := eq_of_central_pow3 β hRp center_cop_spin4 hcen r hr
    have h' : n⁻¹ * α r * n = r := by simpa [hβ, MulAut.conj_apply] using h
    calc α r = n * (n⁻¹ * α r * n) * n⁻¹ := by group
      _ = n * r * n⁻¹ := by rw [h']
  have hαC := hαfix hCp hσC
  have hαC' := hαfix hC'p hσC'
  set u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃) := (θ₄ n)⁻¹ * w₁ with hu
  have hcomm : ∀ R : Subgroup (spinGroup Q₄), (∀ r ∈ R, α r = n * r * n⁻¹) →
      ∀ g ∈ R, u * θ₄ g = θ₄ g * u := by
    intro R hαR g hg
    have h1 := hθα g
    rw [hαR g hg, map_mul, map_mul, map_inv] at h1
    calc u * θ₄ g = (θ₄ n)⁻¹ * (w₁ * θ₄ g * w₁⁻¹) * w₁ := by rw [hu]; group
      _ = (θ₄ n)⁻¹ * (θ₄ n * θ₄ g * (θ₄ n)⁻¹) * w₁ := by rw [← h1]
      _ = θ₄ g * u := by rw [hu]; group
  have hLa₂ : ∀ A' : SL(2, 𝔽₃), u * fr₂.La A' = fr₂.La A' * u := by
    intro A'
    have : fr₂.La A' ∈ C.map θ₄ := by rw [hC]; exact ⟨A', rfl⟩
    obtain ⟨g, hg, hgA⟩ := this
    rw [← hgA]
    exact hcomm C hαC g hg
  have hsw₂ : ∀ B' : SL(2, 𝔽₃), u * fr₂.swap.La B' = fr₂.swap.La B' * u := by
    intro B'
    have : fr₂.swap.La B' ∈ C'.map θ₄ := by rw [hC']; exact ⟨B', rfl⟩
    obtain ⟨g, hg, hgA⟩ := this
    rw [← hgA]
    exact hcomm C' hαC' g hg
  obtain ⟨⟨c, hc⟩, -⟩ := scalar_on_span_of_commute h2 fr₂ hLa₂ hsw₂
  have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have hnO : ∀ v, Q₄ (θ₄ n v) = Q₄ v := fun v => map_spinAction Q₄ n v
    have hnO' : ∀ v, Q₄ ((θ₄ n)⁻¹ v) = Q₄ v := fun v => by
      rw [show (θ₄ n)⁻¹ = θ₄ n⁻¹ from (map_inv θ₄ n).symm]
      exact map_spinAction Q₄ n⁻¹ v
    have hw := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hw₁O
    show Q₄ ((θ₄ n)⁻¹ (w₁ v)) = Q₄ v
    rw [hnO', hw]
  have hc2 : c * c = 1 := by
    have hv := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp huO (fr₂.incl 1)
    rw [hc _ ⟨1, rfl⟩, QuadraticMap.map_smul, Frame.Q_incl, Matrix.det_one] at hv
    simpa using hv
  have hcpm : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp this with h | h
    · left; exact sub_eq_zero.mp h
    · right; exact eq_neg_of_add_eq_zero_left h
  have hST : IsCompl fr.span fr₂.span := by
    rw [hS]
    exact (Frame.isCompl_span_perp (F := fr₂)).symm
  have hnS : ∀ v ∈ fr.span, θ₄ n v ∈ fr.span := fun v hv =>
    Frame.map_mem_span (F := fr) h2 hnA hv
  have hnT : ∀ v ∈ fr₂.span, θ₄ n v ∈ fr₂.span := fun v hv =>
    Frame.map_mem_span (F := fr₂) h2 hnC hv
  have hdec : ∀ x ∈ frN.span, ∃ s ∈ fr.span, ∃ t' ∈ fr₂.span,
      x = s + t' ∧ θ₄ n s = -s ∧ θ₄ n t' = -t' := by
    intro x hx
    have hnx : θ₄ n x = -x := by
      rw [hnθ]
      exact (Frame.mem_span_iff_inv frN h2).mp hx
    have hxsup : x ∈ fr.span ⊔ fr₂.span := by
      rw [hST.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨s, hs, t', ht', hst⟩ := Submodule.mem_sup.mp hxsup
    have hsum : (θ₄ n s + s) + (θ₄ n t' + t') = 0 := by
      have h1 : θ₄ n (s + t') = -(s + t') := by rw [hst]; exact hnx
      rw [map_add] at h1
      calc (θ₄ n s + s) + (θ₄ n t' + t') = (θ₄ n s + θ₄ n t') + (s + t') := by abel
        _ = 0 := by rw [h1]; abel
    have hmemS : θ₄ n s + s ∈ fr.span := fr.span.add_mem (hnS s hs) hs
    have hmemT : θ₄ n t' + t' ∈ fr₂.span := fr₂.span.add_mem (hnT t' ht') ht'
    have hz : θ₄ n s + s = 0 := by
      have h3 : θ₄ n s + s = -(θ₄ n t' + t') := eq_neg_of_add_eq_zero_left hsum
      have hmem : θ₄ n s + s ∈ fr₂.span := by rw [h3]; exact fr₂.span.neg_mem hmemT
      exact Submodule.disjoint_def.mp hST.disjoint _ hmemS hmem
    have hz' : θ₄ n t' + t' = 0 := by
      have h3 : θ₄ n t' + t' = -(θ₄ n s + s) := eq_neg_of_add_eq_zero_right hsum
      rw [h3, hz, neg_zero]
    exact ⟨s, hs, t', ht', hst.symm, eq_neg_of_add_eq_zero_left hz, eq_neg_of_add_eq_zero_left hz'⟩
  have hw₁u : w₁ = θ₄ n * u := by rw [hu]; group
  have hw₁t : ∀ t' ∈ fr₂.span, θ₄ n t' = -t' → w₁ t' = -(c • t') := by
    intro t' ht' hnt
    rw [hw₁u, LinearEquiv.mul_apply, hc t' ht', map_smul, hnt, smul_neg]
  rcases hcpm with hc1 | hc1
  ·
    right
    have hxCO : θ₄ xC ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q₄ xC v
    have hwO : w₁ * θ₄ xC ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
      Subgroup.mul_mem _ hw₁O hxCO
    have hwx : ∀ x ∈ frN.span, (w₁ * θ₄ xC) x = x := by
      intro x hx
      obtain ⟨s, hs, t', ht', hx', hns, hnt⟩ := hdec x hx
      have hi2s : θ₄ xC s = s := by
        rw [hxCθ]
        exact (Frame.mem_perp_iff_fix fr₂ h2).mp (hS ▸ hs)
      have hi2t : θ₄ xC t' = -t' := by
        rw [hxCθ]
        exact (Frame.mem_span_iff_inv fr₂ h2).mp ht'
      calc (w₁ * θ₄ xC) x = w₁ (θ₄ xC (s + t')) := by rw [LinearEquiv.mul_apply, hx']
        _ = w₁ (s + -t') := by rw [map_add, hi2s, hi2t]
        _ = s + t' := by
          rw [map_add, map_neg, hw₁S s hs, hw₁t t' ht' hnt, hc1]
          simp
        _ = x := hx'.symm
    have hθα₂ : ∀ y, θ₄ (((MulAut.conj xC).trans α) y) = (w₁ * θ₄ xC) * θ₄ y * (w₁ * θ₄ xC)⁻¹ := by
      intro y
      show θ₄ (α (xC * y * xC⁻¹)) = _
      rw [hθα, map_mul, map_mul, map_inv, mul_inv_rev]
      group
    have hfix := fixes_of_isometry_fixing_span hN hNp hwO hwx hθα₂
    intro r hr
    have h1 := hfix r hr
    calc σ (ψ (xC * r * xC⁻¹)) = ψ (α (xC * r * xC⁻¹)) := (hαψ _).symm
      _ = ψ (((MulAut.conj xC).trans α) r) := rfl
      _ = ψ r := by rw [h1]
  ·
    left
    have hwx : ∀ x ∈ frN.span, w₁ x = x := by
      intro x hx
      obtain ⟨s, hs, t', ht', hx', hns, hnt⟩ := hdec x hx
      rw [hx', map_add, hw₁S s hs, hw₁t t' ht' hnt, hc1]
      simp
    have hfix := fixes_of_isometry_fixing_span hN hNp hw₁O hwx hθα
    intro r hr
    rw [← hαψ, hfix r hr]

end Core

end Model3

end CFSG.ClassicalInvolution.Q3.Q3P21
