module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthSO2
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Fundamental
public import TauCeti.LinearAlgebra.QuadraticForm.Hyperbolic

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Frame4

variable {F : Frame Q}

theorem embGrp_transportEquiv_eq (h2 : (2 : K) ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g * F.La (-1) = F.La (-1) * g) (hfix : ∀ x ∈ F.perp, g x = x) :
    F.embGrp (Frame.transportEquiv h2 hg) = g := by
  refine LinearEquiv.ext fun x => ?_
  have hr : x - F.incl (F.coords x) ∈ F.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  have h1 := hfix _ hr
  rw [map_sub] at h1
  rw [Frame.embGrp_apply, Frame.embLin_apply]
  change x + F.incl (F.transport g (F.coords x) - F.coords x) = g x
  rw [map_sub, Frame.incl_transport h2 hg]
  calc x + (g (F.incl (F.coords x)) - F.incl (F.coords x))
      = (x - F.incl (F.coords x)) + g (F.incl (F.coords x)) := by abel
    _ = (g x - g (F.incl (F.coords x))) + g (F.incl (F.coords x)) := by rw [h1]
    _ = g x := by abel

theorem exists_mul_of_isPerfect_fix (h2 : (2 : K) ≠ 0) {A : Subgroup (V ≃ₗ[K] V)}
    (hA : ⁅A, A⁆ = A) (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hAc : ∀ a ∈ A, a * F.La (-1) = F.La (-1) * a) (hAfix : ∀ a ∈ A, ∀ x ∈ F.perp, a x = x) :
    ∀ a ∈ A, ∃ n ∈ F.La.range, ∃ m ∈ F.swap.La.range, a = n * m := by
  let ρ : A →* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    { toFun := fun a => Frame.transportEquiv h2 (hAc a.1 a.2)
      map_one' := LinearEquiv.ext fun Y => by
        simp [Frame.transportEquiv_apply, Frame.transport_apply, Frame.coords_incl]
      map_mul' := fun a b => LinearEquiv.ext fun Y => by
        have := LinearMap.congr_fun (Frame.transport_mul h2 (hAc b.1 b.2) (g := a.1)) Y
        simpa [Frame.transportEquiv_apply] using this }
  have hperf : Group.IsPerfect A := Subgroup.isPerfect_iff.mpr hA
  have hρ : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  have hρO : ρ.range ≤ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) := by
    rintro _ ⟨a, rfl⟩
    exact Frame.transportEquiv_mem_orthogonalGroup h2 (hAO a.2) (hAc a.1 a.2)
  have hLR := le_mulSub_of_isPerfect h2 (Subgroup.isPerfect_iff.mp hρ) hρO
  intro a ha
  obtain ⟨l, hl, r, hr, hlr⟩ := hLR ⟨⟨a, ha⟩, rfl⟩
  have hρa : ρ ⟨a, ha⟩ = l * r := hlr
  have hEmb := embGrp_transportEquiv_eq h2 (hAc a ha) (hAfix a ha)
  refine ⟨F.embGrp l, ?_, F.embGrp r, ?_, ?_⟩
  · rw [Frame.La_range_eq_map]
    exact ⟨l, hl, rfl⟩
  · rw [Frame.swap_La_range_eq_map]
    exact ⟨r, hr, rfl⟩
  · rw [← map_mul, ← hlr]
    exact hEmb.symm

theorem exists_frame_of_isometryEquiv [Invertible (2 : K)] [FiniteDimensional K V]
    (W : Submodule K V)
    (φ : (Q.restrict W).IsometryEquiv
      ((TauCeti.hyperbolicPlane K).prod (TauCeti.hyperbolicPlane K))) :
    ∃ F : Frame Q, F.span = W := by
  set ψ : (Fin 2 → K) × (Fin 2 → K) → V := fun p => ((φ.symm p : W) : V) with hψ
  have hψadd : ∀ p q, ψ (p + q) = ψ p + ψ q := fun p q => by
    simp [hψ, map_add]
  have hψsmul : ∀ (c : K) p, ψ (c • p) = c • ψ p := fun c p => by
    simp [hψ, map_smul]
  have hψQ : ∀ p, Q (ψ p) = ((TauCeti.hyperbolicPlane K).prod (TauCeti.hyperbolicPlane K)) p := by
    intro p
    have := φ.symm.map_app p
    exact this
  have hψpolar : ∀ p q, polar Q (ψ p) (ψ q) =
      polar ((TauCeti.hyperbolicPlane K).prod (TauCeti.hyperbolicPlane K)) p q := by
    intro p q
    simp only [QuadraticMap.polar, ← hψadd, hψQ]
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  set e : Fin 2 → K := ![1, 1] with he
  set f : Fin 2 → K := ![(⅟2 : K) * ⅟2, -((⅟2 : K) * ⅟2)] with hf
  have hH : ∀ x : Fin 2 → K, TauCeti.hyperbolicPlane K x = x 0 ^ 2 - x 1 ^ 2 :=
    TauCeti.hyperbolicPlane_apply
  have hHp : ∀ x y : Fin 2 → K, polar (TauCeti.hyperbolicPlane K) x y =
      2 * (x 0 * y 0 - x 1 * y 1) := TauCeti.polar_hyperbolicPlane
  have hQe : TauCeti.hyperbolicPlane K e = 0 := by simp [hH, he]
  have hQf : TauCeti.hyperbolicPlane K f = 0 := by simp [hH, hf]
  have hef : polar (TauCeti.hyperbolicPlane K) e f = 1 := by
    rw [hHp]
    simp only [he, hf, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h := mul_invOf_self (2 : K)
    calc (2 : K) * (1 * (⅟2 * ⅟2) - 1 * -(⅟2 * ⅟2)) = ((2 : K) * ⅟2) * ((2 : K) * ⅟2) := by ring
      _ = 1 := by rw [h, one_mul]
  have hQ1 : Q (ψ (e, 0)) = 0 := by rw [hψQ]; simp [QuadraticMap.prod_apply, hQe]
  have hQ2 : Q (ψ (f, 0)) = 0 := by rw [hψQ]; simp [QuadraticMap.prod_apply, hQf]
  have hQ3 : Q (ψ (0, e)) = 0 := by rw [hψQ]; simp [QuadraticMap.prod_apply, hQe]
  have hQ4 : Q (ψ (0, f)) = 0 := by rw [hψQ]; simp [QuadraticMap.prod_apply, hQf]
  have hp1 : polar Q (ψ (e, 0)) (ψ (f, 0)) = 1 := by
    rw [hψpolar, QuadraticMap.polar_prod]; simp [hef]
  have hp2 : polar Q (ψ (0, e)) (ψ (0, f)) = 1 := by
    rw [hψpolar, QuadraticMap.polar_prod]; simp [hef]
  let P : HypPair Q := ⟨ψ (e, 0), ψ (f, 0), hQ1, hQ2, hp1⟩
  let P' : HypPair Q := ⟨ψ (0, e), ψ (0, f), hQ3, hQ4, hp2⟩
  have horth : P.Orth P' :=
    ⟨by rw [hψpolar, QuadraticMap.polar_prod]; simp,
      by rw [hψpolar, QuadraticMap.polar_prod]; simp,
      by rw [hψpolar, QuadraticMap.polar_prod]; simp,
      by rw [hψpolar, QuadraticMap.polar_prod]; simp⟩
  let F : Frame Q := ⟨P, P', horth⟩
  refine ⟨F, ?_⟩
  have hmemW : ∀ p, ψ p ∈ W := fun p => (φ.symm p).2
  have hle : F.span ≤ W := by
    rintro _ ⟨X, rfl⟩
    rw [Frame.incl_apply]
    exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ (hmemW _)) (W.smul_mem _ (hmemW _)))
      (W.smul_mem _ (hmemW _))) (W.smul_mem _ (hmemW _))
  have hinj : Function.Injective F.incl := fun X Y h => by
    have := congrArg F.coords h
    rwa [Frame.coords_incl, Frame.coords_incl] at this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 : Module.finrank K F.span = 4 := by
    rw [Frame.span, LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix]
    simp
  have h2' : Module.finrank K W = 4 := by
    have := φ.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at this
    exact this
  rw [h1, h2']

theorem eq_bot_of_le_center_of_isPerfect {G : Type*} [Group G] {R B : Subgroup G}
    (hB : B ≤ (Subgroup.center R).map R.subtype) (hperf : ⁅B, B⁆ = B) : B = ⊥ := by
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := hB hx
    obtain ⟨y', hy', rfl⟩ := hB hy
    have := (Subgroup.mem_center_iff.mp hx' y').symm
    exact congrArg Subtype.val this
  rw [eq_bot_iff, ← hperf]
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  exact hcomm x hx y hy

theorem eq_La_range_or_eq_swap [Finite K] (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (F : Frame Q) {T A : Subgroup (V ≃ₗ[K] V)} (hsub : IsSubnormal A T) (hA : ⁅A, A⁆ = A)
    (hR₁ : F.La.range ≤ T) (hR₂ : F.swap.La.range ≤ T)
    (hdec : ∀ a ∈ A, ∃ n ∈ F.La.range, ∃ m ∈ F.swap.La.range, a = n * m)
    (hiA : F.La (-1) ∈ A)
    (huniq : ∀ a ∈ A, ∀ b ∈ A, orderOf a = 2 → orderOf b = 2 → a * b = b * a → a = b) :
    A = F.La.range ∨ A = F.swap.La.range := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hcomm : ∀ x ∈ F.La.range, ∀ y ∈ F.swap.La.range, x * y = y * x := by
    rintro _ ⟨A', rfl⟩ _ ⟨B', rfl⟩
    exact F.La_comm_La_swap A' B'
  have hq₁ : CFSG.IsQuasisimple F.La.range := native_isQuasisimple
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (MonoidHom.ofInjective F.La_injective).symm (isQuasisimple_specialLinearGroup_two h4))
  have hq₂ : CFSG.IsQuasisimple F.swap.La.range := native_isQuasisimple
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (MonoidHom.ofInjective F.swap.La_injective).symm (isQuasisimple_specialLinearGroup_two h4))
  obtain ⟨B₁, B₂, hB₁, hB₂, hB₁p, hB₂p, hAB⟩ :=
    exists_perfect_mul_of_isSubnormal_perfect hR₁ hR₂ hcomm hA hsub hdec
  have hs₁ := isSubnormal_inf hsub hR₁
  have hs₂ := isSubnormal_inf hsub hR₂
  have hR₁f : IsFundamental Q F.La.range (F.La (-1)) := IsFundamental.of_frame F
  have hR₂f : IsFundamental Q F.swap.La.range (F.La (-1)) := IsFundamental.of_frame_swap F
  have hinf : F.La.range ⊓ F.swap.La.range = Subgroup.zpowers (F.La (-1)) :=
    IsFundamental.inf_twin hodd hR₁f hR₂f (Frame.La_range_ne_swap_La_range F).symm
  have hFi2 : orderOf (F.La (-1)) = 2 := hR₁f.orderOf_eq_two hodd
  have hFi1 : F.La (-1) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hFi2
    exact absurd hFi2 (by norm_num)
  have hiR : F.La (-1) * F.La (-1) = 1 := F.La_neg_one_mul_self
  have hzp : ∀ x ∈ Subgroup.zpowers (F.La (-1)), x = 1 ∨ x = F.La (-1) := by
    rintro _ ⟨k, rfl⟩
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      show F.La (-1) ^ (2 * m) = 1
      rw [zpow_mul, zpow_two, hiR, one_zpow]
    · right
      show F.La (-1) ^ (2 * m + 1) = F.La (-1)
      rw [zpow_add_one, zpow_mul, zpow_two, hiR, one_zpow, one_mul]
  have hbot_of : ∀ {R B : Subgroup (V ≃ₗ[K] V)}, B ≤ (Subgroup.center R).map R.subtype →
      ⁅B, B⁆ = B → B = ⊥ := fun hB hp => eq_bot_of_le_center_of_isPerfect hB hp
  rcases eq_or_le_center_of_isSubnormal hs₁ hq₁ with h₁ | h₁ <;>
    rcases eq_or_le_center_of_isSubnormal hs₂ hq₂ with h₂ | h₂
  ·
    exfalso
    have hR₁A : F.La.range ≤ A := fun x hx => by
      have : x ∈ A ⊓ F.La.range := by rw [h₁]; exact hx
      exact this.1
    have hR₂A : F.swap.La.range ≤ A := fun x hx => by
      have : x ∈ A ⊓ F.swap.La.range := by rw [h₂]; exact hx
      exact this.1
    obtain ⟨J, hJ⟩ : ∃ J : SL(2, K), (J : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
      ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩
    have hJJ : J * J = -1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [Matrix.SpecialLinearGroup.coe_mul, hJ]
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hJ1 : J ≠ 1 := fun h => by
      have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp [hJ] at this
    have hJn : J ≠ -1 := fun h => by
      have := congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h
      simp [hJ] at this
    set j := F.La J * F.swap.La J with hj
    have hjA : j ∈ A := A.mul_mem (hR₁A ⟨J, rfl⟩) (hR₂A ⟨J, rfl⟩)
    have hjj : j * j = 1 := by
      calc j * j = F.La J * (F.swap.La J * F.La J) * F.swap.La J := by rw [hj]; group
        _ = F.La J * (F.La J * F.swap.La J) * F.swap.La J := by rw [← F.La_comm_La_swap J J]
        _ = F.La (J * J) * F.swap.La (J * J) := by rw [map_mul, map_mul]; group
        _ = 1 := by rw [hJJ, F.La_swap_neg_one, hiR]
    have hjci : j * F.La (-1) = F.La (-1) * j := by
      rw [hj, mul_assoc, ← F.La_swap_neg_one_comm J, ← mul_assoc, ← F.La_neg_one_comm J]
      group
    have hjne : ∀ x ∈ F.La.range ⊓ F.swap.La.range, x ≠ F.La J :=
      fun x hx hxJ => by
        rcases hzp x (hinf ▸ hx) with h | h
        · exact hJ1 (F.La_injective (by rw [← hxJ, h, map_one]))
        · exact hJn (F.La_injective (by rw [← hxJ, h]))
    have hj1 : j ≠ 1 := fun h => by
      refine hjne (F.La J) ⟨⟨J, rfl⟩, ?_⟩ rfl
      have : F.La J = (F.swap.La J)⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this, ← map_inv]
      exact ⟨J⁻¹, rfl⟩
    have hji : j ≠ F.La (-1) := fun h => by
      refine hjne (F.La J) ⟨⟨J, rfl⟩, ?_⟩ rfl
      have : F.La J = F.La (-1) * (F.swap.La J)⁻¹ := by
        rw [← h, hj]; group
      rw [this, ← F.La_swap_neg_one, ← map_inv, ← map_mul]
      exact ⟨_, rfl⟩
    have hj2 : orderOf j = 2 := orderOf_eq_prime (by rw [pow_two]; exact hjj) hj1
    exact hji (huniq j hjA _ hiA hj2 hFi2 hjci)
  ·
    left
    have hB₂ : B₂ = ⊥ := hbot_of (hB₂.trans h₂) hB₂p
    refine le_antisymm (fun a ha => ?_) (fun x hx => ?_)
    · obtain ⟨c, hc, d, hd, rfl⟩ := hAB a ha
      rw [hB₂, Subgroup.mem_bot] at hd
      rw [hd, mul_one]
      exact (hB₁ hc).2
    · have : x ∈ A ⊓ F.La.range := by rw [h₁]; exact hx
      exact this.1
  ·
    right
    have hB₁' : B₁ = ⊥ := hbot_of (hB₁.trans h₁) hB₁p
    refine le_antisymm (fun a ha => ?_) (fun x hx => ?_)
    · obtain ⟨c, hc, d, hd, rfl⟩ := hAB a ha
      rw [hB₁', Subgroup.mem_bot] at hc
      rw [hc, one_mul]
      exact (hB₂ hd).2
    · have : x ∈ A ⊓ F.swap.La.range := by rw [h₂]; exact hx
      exact this.1
  ·
    exfalso
    have hB₁' : B₁ = ⊥ := hbot_of (hB₁.trans h₁) hB₁p
    have hB₂' : B₂ = ⊥ := hbot_of (hB₂.trans h₂) hB₂p
    obtain ⟨c, hc, d, hd, hcd⟩ := hAB _ hiA
    rw [hB₁', Subgroup.mem_bot] at hc
    rw [hB₂', Subgroup.mem_bot] at hd
    rw [hc, hd, mul_one] at hcd
    exact hFi1 hcd

end Frame4

end CFSG.ClassicalInvolution.ModelFacts
