module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
public import CFSG.ClassicalInvolution.Q3.Q3TLKAut
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
import CFSG.ClassicalInvolution.ModelFacts.Orth15D4FixTop
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthConj
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge
public import CFSG.ClassicalInvolution.Q3.Q3WADict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.D4Rigid CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ComponentClassification.CatalogueBHigherLinearField Matrix
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups commutatorElement

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

section Fix


theorem center_plus4_no_three :
    ∀ c ∈ Subgroup.center (spinGroup Q₄), ¬ 3 ∣ orderOf c := by
  have hn3 : 3 ≤ 4 := by norm_num
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup Q₄) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hC : ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup Q₄)) :=
    RouteD.Gaps.not_dvd_card_center_plus (p := 3) (f := 1) (by norm_num) hn3
  intro c hc h3
  apply hC
  have := orderOf_dvd_natCard (⟨c, hc⟩ : Subgroup.center (spinGroup Q₄))
  rw [Subgroup.orderOf_mk] at this
  exact h3.trans this

theorem d4FixLift3 (fr' : Frame Q₄) (α : spinGroup Q₄ ≃* spinGroup Q₄)
    (hα : ∀ g ∈ (fr'.La.range ⊔ fr'.swap.La.range).comap (spinAction Q₄), g ^ 3 = 1 →
      α g = g) :
    ∃ (A : GL (Fin 4 ⊕ Fin 4) 𝔽₃) (φ : 𝔽₃ ≃+* 𝔽₃) (μ : 𝔽₃ˣ),
      (∀ v : Fin 4 ⊕ Fin 4 → 𝔽₃, Q₄ (A.val *ᵥ (fun i => φ (v i))) = μ * φ (Q₄ v)) ∧
      ∀ x, spinMatrix Q₄ (α x) = A * glFieldEquiv (Fin 4 ⊕ Fin 4) φ (spinMatrix Q₄ x) * A⁻¹ := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  set θ := spinAction Q₄ with hθ
  set fr₀ : Frame Q₄ := (D4Rigid.fr 𝔽₃).toFrame ne01 true false with hfr₀
  have hswap : fr₀.swap = (D4Rigid.fr 𝔽₃).toFrame ne01 true true :=
    Frame.ext_vec rfl rfl rfl rfl
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
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
  set P₀ := fr₀.La.range ⊔ fr₀.swap.La.range with hP₀
  set P := fr'.La.range ⊔ fr'.swap.La.range with hP
  set c : spinGroup Q₄ ≃* spinGroup Q₄ := MulAut.conj x with hc
  have hP₀P : ∀ h ∈ P₀, θ x * h * (θ x)⁻¹ ∈ P := by
    have : P₀ ≤ P.comap (MulAut.conj (θ x)).toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro _ ⟨A, rfl⟩
        change θ x * fr₀.La A * (θ x)⁻¹ ∈ P
        rw [← hLa]
        exact Subgroup.mem_sup_left ⟨A, rfl⟩
      · rintro _ ⟨A, rfl⟩
        change θ x * fr₀.swap.La A * (θ x)⁻¹ ∈ P
        rw [← hLa']
        exact Subgroup.mem_sup_right ⟨A, rfl⟩
    exact fun h hh => this hh
  have hcP : ∀ g ∈ P₀.comap θ, c g ∈ P.comap θ := by
    intro g hg
    have := hP₀P _ hg
    simpa [hc, MulAut.conj_apply, map_mul, map_inv] using this
  set β : spinGroup Q₄ ≃* spinGroup Q₄ := c.trans (α.trans c.symm) with hβ
  have hβfix : ∀ g ∈ P₀.comap θ, g ^ 3 = 1 → β g = g := by
    intro g hg hg3
    have h := hα (c g) (hcP g hg) (by rw [← map_pow, hg3, map_one])
    show c.symm (α (c g)) = g
    rw [h]
    exact c.symm_apply_apply g
  have hstd : ∀ (i j : Fin 4) (hij : i ≠ j) (s t : Bool),
      ((D4Rigid.fr 𝔽₃).longSL2 hij s t).range.map θ =
        ((D4Rigid.fr 𝔽₃).toFrame hij s t).La.range := fun i j hij s t =>
    map_longSL2_range _ hij s t
  have hle3 : ∀ (i j : Fin 4) (hij : i ≠ j) (s t : Bool),
      ((D4Rigid.fr 𝔽₃).longSL2 hij s t).range.map θ ≤ P₀ →
        ∀ g ∈ ((D4Rigid.fr 𝔽₃).longSL2 hij s t).range, β g = g := by
    intro i j hij s t hle g hg
    obtain ⟨A, rfl⟩ := hg
    set f := (D4Rigid.fr 𝔽₃).longSL2 hij s t with hf
    have key : ∀ B : SL(2, 𝔽₃), B ^ 3 = 1 → β (f B) = f B := fun B hB =>
      hβfix (f B) (hle ⟨f B, ⟨B, rfl⟩, rfl⟩) (by rw [← map_pow, hB, map_one])
    obtain ⟨x₁, y₁, hx₁, hy₁, hc₁⟩ := sl2_eq_mul_three card_gf3 A
    have hA : A = x₁ * (x₁⁻¹ * A * y₁⁻¹) * y₁ := by group
    rw [hA, map_mul, map_mul, map_mul, map_mul, key x₁ hx₁, key y₁ hy₁, key _ hc₁]
  have h0 : ∀ g ∈ stdSL2 𝔽₃ 0, β g = g := by
    have e : stdSL2 𝔽₃ 0 = ((D4Rigid.fr 𝔽₃).longSL2 ne01 true false).range := rfl
    rw [e]
    refine hle3 0 1 ne01 true false ?_
    rw [hstd 0 1 ne01 true false]
    exact le_sup_left
  have h1 : ∀ g ∈ stdSL2 𝔽₃ 1, β g = g := by
    have e : stdSL2 𝔽₃ 1 = ((D4Rigid.fr 𝔽₃).longSL2 ne01 true true).range := rfl
    rw [e]
    refine hle3 0 1 ne01 true true ?_
    rw [hstd 0 1 ne01 true true, ← hswap]
    exact le_sup_right
  obtain ⟨a, hQa, hθa⟩ := d4FixLift_std (p := 3) (f := 1) hp2 h0 h1
  have hθβ : ∀ y, θ (β y) = a * θ y * a⁻¹ := by
    intro y
    refine LinearEquiv.ext fun v => ?_
    have := hθa y (a.symm v)
    simpa [LinearEquiv.mul_apply] using this
  obtain ⟨A, hA⟩ := glLin_surjective (θ x * a * (θ x)⁻¹)
  refine ⟨A, RingEquiv.refl _, 1, fun v => ?_, fun y => ?_⟩
  · have h1 : ((A : Matrix _ _ _).mulVec (fun i => (RingEquiv.refl 𝔽₃) (v i))) =
        θ x (a ((θ x)⁻¹ v)) := by
      have := glLin_apply A v
      rw [hA] at this
      simpa [LinearEquiv.mul_apply] using this.symm
    rw [h1, map_spinAction, hQa, show (θ x)⁻¹ = θ x⁻¹ from (map_inv θ x).symm, map_spinAction]
    simp
  · rw [glFieldEquiv_refl]
    refine glLin_injective ?_
    rw [map_mul, map_mul, map_inv, hA, glLin_spinMatrix, glLin_spinMatrix]
    have hαy : α y = c (β (c.symm y)) := by
      show α y = c (c.symm (α (c (c.symm y))))
      rw [c.apply_symm_apply, c.apply_symm_apply]
    change θ (α y) = θ x * a * (θ x)⁻¹ * θ y * (θ x * a * (θ x)⁻¹)⁻¹
    have e2 : θ (c.symm y) = (θ x)⁻¹ * θ y * θ x := by
      rw [hc, MulAut.conj_symm_apply, map_mul, map_mul, map_inv]
    rw [hαy, hc, MulAut.conj_apply, map_mul, map_mul, map_inv, hθβ, ← hc, e2]
    group

theorem liftSimFr3_plus4 {H : Type} [Group H] (ψ : spinGroup Q₄ →* H)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q₄)) : LiftSimFr Q₄ ψ := by
  intro fr σ hσ
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup Q₄) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hC : ¬ 3 ∣ Nat.card (Subgroup.center (spinGroup Q₄)) :=
    RouteD.Gaps.not_dvd_card_center_plus (p := 3) (f := 1) hp2 hn3
  have hZ3 := center_plus4_no_three
  have hθker : ψ.rangeRestrict.ker ≤ Subgroup.center (spinGroup Q₄) := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hθC : ¬ 3 ∣ Nat.card ψ.rangeRestrict.ker := fun hd =>
    hC (hd.trans (Subgroup.card_dvd_of_le hθker))
  obtain ⟨α, hα⟩ := (ModelFacts.OrthAut.centralPSection_spinPlus (p := 3) (F := 𝔽₃)
    hn3).exists_mulEquiv_lift ψ.rangeRestrict ψ.rangeRestrict_surjective hθker hθC σ
  have hαψ : ∀ x, ψ.rangeRestrict (α x) = σ (ψ.rangeRestrict x) := hα
  have hcentral : ∀ s ∈ (fr.La.range ⊔ fr.swap.La.range).comap (spinAction Q₄),
      s⁻¹ * α s ∈ Subgroup.center (spinGroup Q₄) := by
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
    refine mem_center_of_commutators_central fun t => hψ ?_
    rw [← MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, map_commutatorElement, map_mul,
      map_inv, hαψ s]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hζ _)
  have h3fix : ∀ g ∈ (fr.La.range ⊔ fr.swap.La.range).comap (spinAction Q₄), g ^ 3 = 1 →
      α g = g := fun g hg hg3 => fixed_of_pow_three α hZ3 hg3 (hcentral g hg)
  obtain ⟨A, φ, μ, hsim, hmat⟩ := d4FixLift3 fr α h3fix
  exact ⟨α, hαψ, A, φ, μ, hsim, hmat⟩

end Fix

end CFSG.ClassicalInvolution.Q3.Q3TLK
