module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def rV : E × ZMod 2 := (0, 1)

@[expose] def qV (Q : QuadraticForm (ZMod 2) E) (v : E × ZMod 2) : ZMod 2 := Q v.1 + v.2

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  rcases zmod_two_cases c with rfl | rfl <;> decide

theorem zmod2_mul_self (c : ZMod 2) : c * c = c := by
  rcases zmod_two_cases c with rfl | rfl <;> decide

theorem zmod2_neg (c : ZMod 2) : -c = c := by
  rcases zmod_two_cases c with rfl | rfl <;> decide

theorem neg_eq_self_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero_zmod_two x)

theorem sub_eq_add_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self_zmod2]

theorem eq_of_add_eq_zero_zmod2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M}
    (h : x + y = 0) : x = y := by
  rw [← sub_eq_zero, sub_eq_add_zmod2, h]

variable {b : LinearMap.BilinForm (ZMod 2) E}

abbrev sE (s : bilinIsometryGroup b) : E →ₗ[ZMod 2] E :=
  ((s : LinearMap.GeneralLinearGroup (ZMod 2) E) : E →ₗ[ZMod 2] E)

theorem sE_mul (s t : bilinIsometryGroup b) (x : E) : sE (s * t) x = sE s (sE t x) :=
  rfl

theorem sE_one (x : E) : sE (1 : bilinIsometryGroup b) x = x :=
  rfl

theorem sE_inv_apply (s : bilinIsometryGroup b) (x : E) : sE s⁻¹ (sE s x) = x := by
  rw [← sE_mul, inv_mul_cancel, sE_one]

theorem sE_apply_inv (s : bilinIsometryGroup b) (x : E) : sE s (sE s⁻¹ x) = x := by
  rw [← sE_mul, mul_inv_cancel, sE_one]

theorem b_sE (s : bilinIsometryGroup b) (x y : E) : b (sE s x) (sE s y) = b x y :=
  s.2 x y

@[expose] def tau (hb : b.IsAlt) (u : E) : bilinIsometryGroup b :=
  ⟨binarySymplecticTransvection b hb u, transvection_mem_bilinIsometryGroup hb u⟩

theorem sE_tau (hb : b.IsAlt) (u x : E) : sE (tau hb u) x = x + b x u • u :=
  rfl

section Quadratic

variable {Q : QuadraticForm (ZMod 2) E}

theorem Q_add (hQ : QuadraticMap.polarBilin Q = b) (x y : E) : Q (x + y) = Q x + Q y + b x y := by
  have h := congrArg (fun B : LinearMap.BilinForm (ZMod 2) E => B x y) hQ
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar] at h
  rw [← h]
  ring

theorem Q_smul (c : ZMod 2) (x : E) : Q (c • x) = c * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, zmod2_mul_self]

@[expose] def hLin (hQ : QuadraticMap.polarBilin Q = b) (g : E →ₗ[ZMod 2] E)
    (hg : ∀ x y, b (g x) (g y) = b x y) : (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2) where
  toFun v := (g v.1, v.2 + Q v.1 + Q (g v.1))
  map_add' v w := by
    refine Prod.ext (map_add g v.1 w.1) ?_
    simp only [Prod.snd_add, Prod.fst_add, map_add, Q_add hQ, hg]
    generalize Q v.1 = p₁
    generalize Q w.1 = p₂
    generalize Q (g v.1) = p₃
    generalize Q (g w.1) = p₄
    generalize b v.1 w.1 = p₅
    generalize v.2 = p₆
    generalize w.2 = p₇
    revert p₁ p₂ p₃ p₄ p₅ p₆ p₇
    decide
  map_smul' c v := by
    refine Prod.ext (map_smul g c v.1) ?_
    simp only [Prod.smul_snd, Prod.smul_fst, map_smul, Q_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem hLin_apply (hQ : QuadraticMap.polarBilin Q = b) (g : E →ₗ[ZMod 2] E)
    (hg : ∀ x y, b (g x) (g y) = b x y) (v : E × ZMod 2) :
    hLin hQ g hg v = (g v.1, v.2 + Q v.1 + Q (g v.1)) :=
  rfl

theorem hLin_comp (hQ : QuadraticMap.polarBilin Q = b) (g g' : E →ₗ[ZMod 2] E)
    (hg : ∀ x y, b (g x) (g y) = b x y) (hg' : ∀ x y, b (g' x) (g' y) = b x y)
    (v : E × ZMod 2) :
    hLin hQ g hg (hLin hQ g' hg' v) =
      hLin hQ (g ∘ₗ g') (fun x y => (hg _ _).trans (hg' x y)) v := by
  simp only [hLin_apply, LinearMap.comp_apply]
  refine Prod.ext rfl ?_
  simp only
  generalize Q v.1 = p₁
  generalize Q (g' v.1) = p₂
  generalize Q (g (g' v.1)) = p₃
  generalize v.2 = p₄
  revert p₁ p₂ p₃ p₄
  decide

@[expose] def hGL (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b) :
    LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.ofLinearMap (hLin hQ (sE s) (b_sE s)) (hLin hQ (sE s⁻¹) (b_sE s⁻¹))
      (LinearMap.ext fun v => by
        rw [LinearMap.comp_apply, hLin_comp]
        simp only [hLin_apply, LinearMap.comp_apply, sE_apply_inv, LinearMap.id_apply]
        refine Prod.ext rfl ?_
        simp only
        rw [add_assoc, zmod2_add_self, add_zero])
      (LinearMap.ext fun v => by
        rw [LinearMap.comp_apply, hLin_comp]
        simp only [hLin_apply, LinearMap.comp_apply, sE_inv_apply, LinearMap.id_apply]
        refine Prod.ext rfl ?_
        simp only
        rw [add_assoc, zmod2_add_self, add_zero]))

@[expose] def hHom (hQ : QuadraticMap.polarBilin Q = b) :
    bilinIsometryGroup b →* LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2) where
  toFun := hGL hQ
  map_one' := gl_ext fun v => by
    change (v.1, v.2 + Q v.1 + Q v.1) = v
    rw [add_assoc, zmod2_add_self, add_zero]
  map_mul' s t := gl_ext fun v => by
    change hLin hQ (sE (s * t)) (b_sE (s * t)) v =
      hLin hQ (sE s) (b_sE s) (hLin hQ (sE t) (b_sE t) v)
    rw [hLin_comp]
    rfl

theorem hHom_apply (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    (v : E × ZMod 2) :
    ((hHom hQ s : LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2)) :
      (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2)) v = (sE s v.1, v.2 + Q v.1 + Q (sE s v.1)) :=
  rfl

theorem hHom_rV (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b) :
    ((hHom hQ s : LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2)) :
      (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2)) rV = rV := by
  rw [hHom_apply]
  simp only [rV, map_zero, add_zero]

theorem qV_hHom (hQ : QuadraticMap.polarBilin Q = b) (s : bilinIsometryGroup b)
    (v : E × ZMod 2) :
    qV Q (((hHom hQ s : LinearMap.GeneralLinearGroup (ZMod 2) (E × ZMod 2)) :
      (E × ZMod 2) →ₗ[ZMod 2] (E × ZMod 2)) v) = qV Q v := by
  rw [hHom_apply, qV, qV]
  simp only
  generalize Q v.1 = p₁
  generalize Q (sE s v.1) = p₂
  generalize v.2 = p₃
  revert p₁ p₂ p₃
  decide

end Quadratic

theorem eq_zero_of_forall_fixed (hb : b.IsAlt) (hnd : b.Nondegenerate) {v : E}
    (hv : ∀ s : bilinIsometryGroup b, sE s v = v) : v = 0 := by
  by_contra h
  obtain ⟨u, hu⟩ := exists_apply_eq_one hnd h
  have h1 := hv (tau hb u)
  rw [sE_tau, symm_apply hb u v, hu, one_smul, add_eq_left] at h1
  rw [h1, map_zero, LinearMap.zero_apply] at hu
  exact absurd hu (by decide)

theorem exists_orth_of_ne (hb : b.IsAlt) (hnd : b.Nondegenerate) [Finite E]
    (hE : 4 < Nat.card E) {v w : E} (hw : w ≠ 0) (hvw : w ≠ v) :
    ∃ u, b v u = 0 ∧ b w u = 1 ∧ u ≠ v := by
  obtain ⟨u₀, hu₀v, hu₀w⟩ : ∃ u₀, b v u₀ = 0 ∧ b w u₀ = 1 := by
    obtain ⟨x, hx⟩ := exists_apply_eq_one hnd hw
    rw [← symm_apply hb] at hx
    rcases zmod_two_cases (b v x) with hvx | hvx
    · exact ⟨x, hvx, hx⟩
    · have hvw' : v + w ≠ 0 := fun h => hvw (eq_of_add_eq_zero_zmod2 h).symm
      obtain ⟨y, hy⟩ := exists_apply_eq_one hnd hvw'
      rw [← symm_apply hb, map_add, LinearMap.add_apply] at hy
      rcases zmod_two_cases (b v y) with hvy | hvy
      · rw [hvy, zero_add] at hy
        exact ⟨y, hvy, hy⟩
      · refine ⟨x + y, ?_, ?_⟩
        · rw [map_add, hvx, hvy]
          decide
        · rw [map_add, hx]
          rw [hvy] at hy
          have hwy : b w y = 0 := by
            rcases zmod_two_cases (b w y) with h | h
            · exact h
            · rw [h] at hy
              exact absurd hy (by decide)
          rw [hwy, add_zero]
  have : Fintype E := Fintype.ofFinite E
  have hE' : Fintype.card (ZMod 2 × ZMod 2) < Fintype.card E :=
    calc Fintype.card (ZMod 2 × ZMod 2) = 4 := rfl
      _ < Nat.card E := hE
      _ = Fintype.card E := Nat.card_eq_fintype_card
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun x : E => (b v x, b w x)) hE'
  simp only [Prod.mk.injEq] at hf
  have hk0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hkv : b v (x - y) = 0 := by rw [map_sub, hf.1, sub_self]
  have hkw : b w (x - y) = 0 := by rw [map_sub, hf.2, sub_self]
  by_cases h : u₀ = v
  · refine ⟨u₀ + (x - y), by rw [map_add, hu₀v, hkv, add_zero],
      by rw [map_add, hu₀w, hkw, add_zero], fun h' => hk0 ?_⟩
    rw [h, add_eq_left] at h'
    exact h'
  · exact ⟨u₀, hu₀v, hu₀w, h⟩

theorem eq_zero_or_eq_of_forall_transvection (hb : b.IsAlt) (hnd : b.Nondegenerate) [Finite E]
    (hE : 4 < Nat.card E) {v w : E}
    (h : ∀ u, b v u = 0 → b w u • u = 0 ∨ b w u • u = v) : w = 0 ∨ w = v := by
  by_contra hc
  push Not at hc
  obtain ⟨u, huv, huw, hne⟩ := exists_orth_of_ne hb hnd hE hc.1 hc.2
  rcases h u huv with h0 | h1
  · rw [huw, one_smul] at h0
    rw [h0, map_zero] at huw
    exact absurd huw (by decide)
  · rw [huw, one_smul] at h1
    exact hne h1

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
