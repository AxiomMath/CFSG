module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralTwoCoverTransfer
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

open scoped commutatorElement

section Norm

variable {D W : Type*} [Group D] [Fintype D] [CommGroup W] [MulDistribMulAction D W]

variable (D W) in
@[expose] noncomputable def actNorm : W →* W where
  toFun w := ∏ d : D, d • w
  map_one' := by simp only [smul_one, Finset.prod_const_one]
  map_mul' w w' := by simp only [smul_mul', Finset.prod_mul_distrib]

theorem actNorm_apply (w : W) : actNorm D W w = ∏ d : D, d • w := rfl

theorem smul_actNorm (d₀ : D) (w : W) : d₀ • actNorm D W w = actNorm D W w := by
  rw [actNorm_apply, Finset.smul_prod']
  exact Fintype.prod_equiv (Equiv.mulLeft d₀) _ _ fun d => (mul_smul d₀ d w).symm

theorem actNorm_smul (d₀ : D) (w : W) : actNorm D W (d₀ • w) = actNorm D W w := by
  simp only [actNorm_apply, ← mul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight d₀) _ _ fun d => rfl

theorem actNorm_of_forall_smul_eq {w : W} (hw : ∀ d : D, d • w = w) :
    actNorm D W w = w ^ Fintype.card D := by
  simp only [actNorm_apply, hw, Finset.prod_const, Finset.card_univ]

end Norm

section Lift

variable {K : Type*} [Group K]

theorem conj_eq_of_mk_eq {g g' : K} (h : (g : K ⧸ Subgroup.center K) = g') (x : K) :
    g' * x * g'⁻¹ = g * x * g⁻¹ := by
  rw [QuotientGroup.eq] at h
  have hc := Subgroup.mem_center_iff.mp h x
  calc g' * x * g'⁻¹ = g * ((g⁻¹ * g') * x * (g⁻¹ * g')⁻¹) * g⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [← hc, mul_inv_cancel_right]

theorem commutatorElement_eq_of_mk_eq {a a' b b' : K}
    (ha : (a : K ⧸ Subgroup.center K) = a') (hb : (b : K ⧸ Subgroup.center K) = b') :
    ⁅a', b'⁆ = ⁅a, b⁆ := by
  rw [QuotientGroup.eq] at ha hb
  have ha' : a' = (a⁻¹ * a') * a := by
    rw [← Subgroup.mem_center_iff.mp ha a, mul_inv_cancel_left]
  have hb' : b' = (b⁻¹ * b') * b := by
    rw [← Subgroup.mem_center_iff.mp hb b, mul_inv_cancel_left]
  rw [ha', hb', CentralTwoCover.commutatorElement_central_mul_left
    (Subgroup.mem_center_iff.mp ha), CentralTwoCover.commutatorElement_central_mul_right
    (Subgroup.mem_center_iff.mp hb)]

@[expose] noncomputable def liftConj (d : K ⧸ Subgroup.center K) (x : K) : K :=
  Quotient.out d * x * (Quotient.out d)⁻¹

theorem liftConj_eq {g : K} {d : K ⧸ Subgroup.center K} (h : (g : K ⧸ Subgroup.center K) = d)
    (x : K) : liftConj d x = g * x * g⁻¹ :=
  conj_eq_of_mk_eq (h.trans (QuotientGroup.out_eq' d).symm) x

theorem liftConj_one (x : K) : liftConj 1 x = x := by
  rw [liftConj_eq (g := 1) (d := 1) (QuotientGroup.mk_one _), one_mul, inv_one, mul_one]

theorem liftConj_mul (d₁ d₂ : K ⧸ Subgroup.center K) (x : K) :
    liftConj (d₁ * d₂) x = liftConj d₁ (liftConj d₂ x) := by
  have h : ((Quotient.out d₁ * Quotient.out d₂ : K) : K ⧸ Subgroup.center K) = d₁ * d₂ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  rw [liftConj_eq h, liftConj, liftConj]
  group

theorem liftConj_mul_left (d : K ⧸ Subgroup.center K) (x y : K) :
    liftConj d (x * y) = liftConj d x * liftConj d y := by
  simp only [liftConj]
  group

theorem liftConj_commutatorElement (d : K ⧸ Subgroup.center K) (x y : K) :
    liftConj d ⁅x, y⁆ = ⁅liftConj d x, liftConj d y⁆ := by
  simp only [liftConj, commutatorElement_def]
  group

theorem liftConj_of_mem_center (d : K ⧸ Subgroup.center K) {x : K}
    (hx : x ∈ Subgroup.center K) : liftConj d x = x := by
  rw [liftConj, Subgroup.mem_center_iff.mp hx, mul_inv_cancel_right]

theorem mk_liftConj (d : K ⧸ Subgroup.center K) (x : K) :
    ((liftConj d x : K) : K ⧸ Subgroup.center K) = d * (x : K ⧸ Subgroup.center K) * d⁻¹ := by
  rw [liftConj, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.out_eq']

@[expose, instance_reducible] noncomputable def liftConjAction
    (D : Subgroup (K ⧸ Subgroup.center K)) (W : Subgroup K)
    (hDW : ∀ d ∈ D, ∀ w ∈ W, liftConj d w ∈ W) : MulDistribMulAction D W where
  smul d w := ⟨liftConj d w, hDW d d.2 w w.2⟩
  one_smul w := Subtype.ext (liftConj_one (w : K))
  mul_smul d₁ d₂ w := Subtype.ext (liftConj_mul (d₁ : K ⧸ Subgroup.center K) d₂ (w : K))
  smul_mul d w₁ w₂ := Subtype.ext (liftConj_mul_left (d : K ⧸ Subgroup.center K) w₁ w₂)
  smul_one d := Subtype.ext (by
    change liftConj (d : K ⧸ Subgroup.center K) 1 = 1
    rw [liftConj, mul_one, mul_inv_cancel])

theorem liftConjAction_smul (D : Subgroup (K ⧸ Subgroup.center K)) (W : Subgroup K)
    (hDW : ∀ d ∈ D, ∀ w ∈ W, liftConj d w ∈ W) (d : D) (w : W) :
    (((liftConjAction D W hDW).smul d w : W) : K) = liftConj (d : K ⧸ Subgroup.center K) w :=
  rfl

end Lift

section Perfect

variable {K : Type*} [Group K]

theorem eq_conj_of_perfect (hperf : commutator K = ⊤) (σ : K →* K) (r : K)
    (h : ∀ k : K, ((σ k : K) : K ⧸ Subgroup.center K) = ((r * k * r⁻¹ : K) : K ⧸ _))
    (k : K) : σ k = r * k * r⁻¹ := by
  have hc : ∀ k : K, (r * k * r⁻¹)⁻¹ * σ k ∈ Subgroup.center K := fun k =>
    QuotientGroup.eq.mp (h k).symm
  let ψ : K →* Subgroup.center K :=
    { toFun := fun k => ⟨(r * k * r⁻¹)⁻¹ * σ k, hc k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun k l => Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul]
        have hk := Subgroup.mem_center_iff.mp (hc k) ((r * l * r⁻¹)⁻¹)
        calc (r * (k * l) * r⁻¹)⁻¹ * (σ k * σ l)
            = (r * l * r⁻¹)⁻¹ * ((r * k * r⁻¹)⁻¹ * σ k) * σ l := by group
          _ = (r * k * r⁻¹)⁻¹ * σ k * ((r * l * r⁻¹)⁻¹ * σ l) := by
            rw [hk, mul_assoc]) }
  have hker : commutator K ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  rw [hperf] at hker
  have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top k)))
  exact (inv_mul_eq_one.mp h1).symm

@[expose] noncomputable def centralQuotientAut (σ : MulAut K) :
    MulAut (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr _ _ σ (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)

theorem centralQuotientAut_mk (σ : MulAut K) (k : K) :
    centralQuotientAut σ (k : K ⧸ Subgroup.center K) = ((σ k : K) : K ⧸ Subgroup.center K) :=
  rfl

theorem exists_eq_conj_of_perfect (hperf : commutator K = ⊤) {Q : Subgroup K}
    (haut : ∀ σ : MulAut (K ⧸ Subgroup.center K),
      (∀ q ∈ Q.map (QuotientGroup.mk' (Subgroup.center K)), σ q = q) →
        ∃ r ∈ Q.map (QuotientGroup.mk' (Subgroup.center K)), ∀ k, σ k = r * k * r⁻¹)
    (σ : MulAut K) (hσ : ∀ q ∈ Q, σ q = q) : ∃ r ∈ Q, ∀ k, σ k = r * k * r⁻¹ := by
  obtain ⟨_, ⟨r, hrQ, rfl⟩, hr⟩ := haut (centralQuotientAut σ) (by
    rintro _ ⟨q, hq, rfl⟩
    rw [QuotientGroup.mk'_apply, centralQuotientAut_mk, hσ q hq])
  refine ⟨r, hrQ, eq_conj_of_perfect hperf σ.toMonoidHom r fun k => ?_⟩
  have h := hr (k : K ⧸ Subgroup.center K)
  rw [centralQuotientAut_mk, QuotientGroup.mk'_apply] at h
  rw [MulEquiv.coe_toMonoidHom, h, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv]

end Perfect

section Indicator

variable {G : Type*} [Group G]

@[expose] noncomputable def neOneIndicator (s : G) : ZMod 2 := by
  classical
  exact if s = 1 then 0 else 1

theorem neOneIndicator_one : neOneIndicator (1 : G) = 0 := by
  simp [neOneIndicator]

theorem eq_one_of_neOneIndicator_eq_zero {s : G} (h : neOneIndicator s = 0) : s = 1 := by
  by_contra hs
  simp [neOneIndicator, hs] at h

theorem neOneIndicator_mul {s t : G} (h : s = 1 ∨ t = 1 ∨ s = t) (hs : s * s = 1) :
    neOneIndicator (s * t) = neOneIndicator s + neOneIndicator t := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  rcases h with rfl | rfl | rfl
  · rw [one_mul, neOneIndicator_one, zero_add]
  · rw [mul_one, neOneIndicator_one, add_zero]
  · rw [hs, neOneIndicator_one, h2]

end Indicator

end CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover
