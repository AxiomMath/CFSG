module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R4Ord
public import CFSG.ClassicalInvolution.Q3.Q3TY35
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
public import CFSG.ClassicalInvolution.RouteD.TWS7Lift
public import CFSG.ClassicalInvolution.Q3.Q3TY34

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Models.Transfer
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.ModelFacts.D4Rigid
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TY CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.ModelFacts hiding fundamentalSubgroups
open scoped MatrixGroups commutatorElement


section Lift3

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 𝔽₃
local notation "θ₄" => spinAction (quadPlus 4 𝔽₃)

theorem center_cop_spin4 :
    ∀ w ∈ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)), ¬ 3 ∣ orderOf w := by
  intro w hw h3
  have h4 := pow_four_of_mem_center_spinPlus (K := 𝔽₃) (by norm_num : 3 ≤ 4) hw
  have := h3.trans (orderOf_dvd_of_pow_eq_one h4)
  omega

theorem exists_isometry_lift3 {fr' : OFrame Q₄} {α : spinGroup Q₄ ≃* spinGroup Q₄}
    {A B : Subgroup (spinGroup Q₄)} (hA : A.map θ₄ = fr'.La.range)
    (hB : B.map θ₄ = fr'.swap.La.range) (hAp : Pow3 A) (hBp : Pow3 B)
    (hαA : ∀ g ∈ A, α g = g) (hαB : ∀ g ∈ B, α g = g) :
    ∃ w₀ : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃),
      (∀ v, Q₄ (w₀ v) = Q₄ v) ∧ ∀ y, θ₄ (α y) = w₀ * θ₄ y * w₀⁻¹ := by
  classical
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have cq := centralQuot3_plus (m := 4) le_rfl
  set θ := θ₄ with hθ
  set fr₀ : Frame Q₄ := (D4Rigid.fr 𝔽₃).toFrame ne01 true false with hfr₀
  have hswap : fr₀.swap = (D4Rigid.fr 𝔽₃).toFrame ne01 true true :=
    Frame.ext_vec rfl rfl rfl rfl
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by rw [finrank_plus]
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  obtain ⟨x, hx⟩ := exists_spin_incl_eq hodd (nondegenerate_polarBilin_quadPlus 4 _) fr₀ fr' hperp
  have hθx : θ x ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q₄ x v
  have hmap : fr₀.map hθx = fr' := Frame.map_eq_of_incl hθx hx
  have hmap' : fr₀.swap.map hθx = fr'.swap := by
    refine Frame.map_eq_of_incl hθx fun Y => ?_
    rw [Frame.incl_swap, Frame.incl_swap, hx]
  have hLa : ∀ A : SL(2, 𝔽₃), fr'.La A = θ x * fr₀.La A * (θ x)⁻¹ := fun A => by
    rw [← hmap, Frame.map_La]
  have hLa' : ∀ A : SL(2, 𝔽₃), fr'.swap.La A = θ x * fr₀.swap.La A * (θ x)⁻¹ := fun A => by
    rw [← hmap', Frame.map_La]
  set c : spinGroup Q₄ ≃* spinGroup Q₄ := MulAut.conj x with hc
  set β : spinGroup Q₄ ≃* spinGroup Q₄ := c.trans (α.trans c.symm) with hβ
  have hstd : ∀ (i j : Fin 4) (hij : i ≠ j) (s t : Bool),
      ((D4Rigid.fr 𝔽₃).longSL2 hij s t).range.map θ =
        ((D4Rigid.fr 𝔽₃).toFrame hij s t).La.range := fun i j hij s t =>
    map_longSL2_range _ hij s t
  have hcθ : ∀ s : spinGroup Q₄, θ (c s) = θ x * θ s * (θ x)⁻¹ := fun s => by
    rw [hc, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hpow0 : Pow3 ((stdSL2 𝔽₃ 0).map c.toMonoidHom) :=
    rootSL2_map_conj_pow3 (plusFrame 4 𝔽₃ (by norm_num)) 0 1 (by omega) (by omega) (by omega)
      true false x
  have hpow1 : Pow3 ((stdSL2 𝔽₃ 1).map c.toMonoidHom) :=
    rootSL2_map_conj_pow3 (plusFrame 4 𝔽₃ (by norm_num)) 0 1 (by omega) (by omega) (by omega)
      true true x
  have hAeq : A = (stdSL2 𝔽₃ 0).map c.toMonoidHom := by
    refine eq_of_map_eq_of_pow3 θ (ker_spinAction_le_center Q₄) cq.cop hAp hpow0 ?_
    rw [hA, Subgroup.map_map]
    ext g
    constructor
    · rintro ⟨A₁, rfl⟩
      have : fr₀.La A₁ ∈ (stdSL2 𝔽₃ 0).map θ := by
        rw [show (stdSL2 𝔽₃ 0).map θ = fr₀.La.range from hstd 0 1 ne01 true false]
        exact ⟨A₁, rfl⟩
      obtain ⟨s, hs, hsA⟩ := this
      exact ⟨s, hs, by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hcθ, hsA, hLa]⟩
    · rintro ⟨s, hs, rfl⟩
      have : θ s ∈ fr₀.La.range := by
        rw [← show (stdSL2 𝔽₃ 0).map θ = fr₀.La.range from hstd 0 1 ne01 true false]
        exact ⟨s, hs, rfl⟩
      obtain ⟨A₁, hA₁⟩ := this
      exact ⟨A₁, by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hcθ, ← hA₁, hLa]⟩
  have hBeq : B = (stdSL2 𝔽₃ 1).map c.toMonoidHom := by
    refine eq_of_map_eq_of_pow3 θ (ker_spinAction_le_center Q₄) cq.cop hBp hpow1 ?_
    rw [hB, Subgroup.map_map]
    ext g
    constructor
    · rintro ⟨A₁, rfl⟩
      have : fr₀.swap.La A₁ ∈ (stdSL2 𝔽₃ 1).map θ := by
        rw [show (stdSL2 𝔽₃ 1).map θ = fr₀.swap.La.range by
          rw [hswap]; exact hstd 0 1 ne01 true true]
        exact ⟨A₁, rfl⟩
      obtain ⟨s, hs, hsA⟩ := this
      exact ⟨s, hs, by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hcθ, hsA, hLa']⟩
    · rintro ⟨s, hs, rfl⟩
      have : θ s ∈ fr₀.swap.La.range := by
        rw [← show (stdSL2 𝔽₃ 1).map θ = fr₀.swap.La.range by
          rw [hswap]; exact hstd 0 1 ne01 true true]
        exact ⟨s, hs, rfl⟩
      obtain ⟨A₁, hA₁⟩ := this
      exact ⟨A₁, by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
        rw [hcθ, ← hA₁, hLa']⟩
  have h0 : ∀ g ∈ stdSL2 𝔽₃ 0, β g = g := by
    intro g hg
    have hcg : c g ∈ A := by
      rw [hAeq]
      exact ⟨g, hg, rfl⟩
    show c.symm (α (c g)) = g
    rw [hαA _ hcg]
    exact c.symm_apply_apply g
  have h1 : ∀ g ∈ stdSL2 𝔽₃ 1, β g = g := by
    intro g hg
    have hcg : c g ∈ B := by
      rw [hBeq]
      exact ⟨g, hg, rfl⟩
    show c.symm (α (c g)) = g
    rw [hαB _ hcg]
    exact c.symm_apply_apply g
  obtain ⟨a, hQa, hθa⟩ := d4FixLift_std (p := 3) (f := 1) (by norm_num) h0 h1
  have hθβ : ∀ y, θ (β y) = a * θ y * a⁻¹ := by
    intro y
    refine LinearEquiv.ext fun v => ?_
    have := hθa y (a.symm v)
    simpa [LinearEquiv.mul_apply] using this
  refine ⟨θ x * a * (θ x)⁻¹, fun v => ?_, fun y => ?_⟩
  · show Q₄ (θ x (a ((θ x)⁻¹ v))) = Q₄ v
    rw [map_spinAction, hQa, show (θ x)⁻¹ = θ x⁻¹ from (map_inv θ x).symm, map_spinAction]
  · have hαy : α y = c (β (c.symm y)) := by
      show α y = c (c.symm (α (c (c.symm y))))
      rw [c.apply_symm_apply, c.apply_symm_apply]
    have e2 : θ (c.symm y) = (θ x)⁻¹ * θ y * θ x := by
      rw [hc, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
    rw [hαy, hc, MulAut.conj_apply, map_mul, map_mul, map_inv, hθβ, ← hc, e2]
    group

theorem exists_lift_isometry3 {X : Type} [Group X] (ψ : spinGroup Q₄ →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) (τ : X ≃* X) (hτ2 : ∀ y, τ (τ y) = y)
    (hτr : ∀ k, τ (ψ k) ∈ ψ.range) (fr : OFrame Q₄) (A B : Subgroup (spinGroup Q₄))
    (hA : A.map θ₄ = fr.La.range) (hB : B.map θ₄ = fr.swap.La.range) (hAp : Pow3 A)
    (hBp : Pow3 B) (hfixA : ∀ r ∈ A, τ (ψ r) = ψ r) (hfixB : ∀ r ∈ B, τ (ψ r) = ψ r) :
    ∃ (α : spinGroup Q₄ ≃* spinGroup Q₄) (w : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)),
      (∀ y, ψ (α y) = τ (ψ y)) ∧ w ∈ TauCeti.QuadraticMap.orthogonalGroup Q₄ ∧
      (∀ x ∈ fr.span, w x = x) ∧ (∀ y, θ₄ (α y) = w * θ₄ y * w⁻¹) ∧ w * w = 1 ∧
      (∀ y, α (α y) = y) := by
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
  have hα2 : ∀ y, α (α y) = y := by
    have key := CFSG.ClassicalInvolution.ModelFacts.OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup Q₄ →* spinGroup Q₄).comp (α : spinGroup Q₄ →* spinGroup Q₄))
      (MonoidHom.id (spinGroup Q₄)) (fun x => by
        apply hψ
        rw [MonoidHom.mem_ker]
        change ψ (x⁻¹ * α (α x)) = 1
        rw [map_mul, map_inv, hαψ', hαψ', hτ2, inv_mul_cancel])
    exact fun y => (DFunLike.congr_fun key y).symm
  have hy_mem : w * w ∈ elementaryGroup Q₄ :=
    sq_mem_of_frame hodd (nondegenerate_polarBilin_quadPlus 4 _) fr
      (by rw [show Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 by rw [finrank_plus]]; omega) hwO
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift (range_spinAction_quadPlus hn3) α hy_mem hθw
  have hŷc : ŷ ∈ Subgroup.center (spinGroup Q₄) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := hαα x
    rw [hα2 x] at this
    exact (mul_inv_eq_iff_eq_mul.mp this.symm).symm
  obtain ⟨μ, hμ⟩ := exists_smul_of_central (range_spinAction_quadPlus hn3)
    (centerScalar_quadPlus hn3) hŷc
  have hww : ∀ v, (w * w) v = μ • v := fun v => by
    rw [← hŷ]
    exact hμ v
  have he₁0 : fr.e₁ ≠ 0 := by
    intro h0
    have := fr.polar_e₁_f₁
    rw [h0] at this
    simp at this
  have hμ1 : μ = 1 := by
    have h1 : (w * w) fr.e₁ = fr.e₁ := by
      rw [LinearEquiv.mul_apply, hwspan _ he₁, hwspan _ he₁]
    rw [hww] at h1
    have h2' : (μ - 1) • fr.e₁ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2').resolve_right he₁0)
  refine ⟨α, w, hαψ', hwO, hwspan, hθw, ?_, hα2⟩
  refine LinearEquiv.ext fun v => ?_
  rw [hww, hμ1, one_smul]
  rfl

end Lift3

end CFSG.ClassicalInvolution.Q3.Q3TD
