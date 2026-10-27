module

public import CFSG.ClassicalInvolution.Q3.Q3ZACalc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups commutatorElement
open Matrix

section Rel

variable {G : Type} [Group G]

theorem form_FF_of {v w : V4} (a b c d : F3) (hv : v = a • bF0 + b • bF1)
    (hw : w = c • bF0 + d • bF1) : form v w = 0 := by
  subst hv hw
  exact form_FF a b c d

theorem form_EE_of {v w : V4} (a b c d : F3) (hv : v = a • bE0 + b • bE1)
    (hw : w = c • bE0 + d • bE1) : form v w = 0 := by
  subst hv hw
  exact form_EE a b c d

theorem comm_conj_of_commute {h c : G} (p : G) (hc : c * h = h * c) :
    ⁅h * p * h⁻¹, c⁆ = h * ⁅p, c⁆ * h⁻¹ := by
  have hc' : h * c * h⁻¹ = c := by rw [← hc]; group
  calc ⁅h * p * h⁻¹, c⁆ = ⁅h * p * h⁻¹, h * c * h⁻¹⁆ := by rw [hc']
    _ = h * ⁅p, c⁆ * h⁻¹ := by simp only [commutatorElement_def]; group

theorem commute_conj_of_commute {h c p : G} (hc : c * h = h * c) (hpc : Commute p c) :
    Commute (h * p * h⁻¹) c := by
  rw [← commutatorElement_eq_one_iff_commute, comm_conj_of_commute p hc,
    commutatorElement_eq_one_iff_commute.mpr hpc, mul_one, mul_inv_cancel]

theorem conj_inv {H : Type} [Group H] (w q : H) : w * q⁻¹ * w⁻¹ = (w * q * w⁻¹)⁻¹ := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem hom_conj_inv {H K : Type} [Group H] [Group K] (θ : H →* K) (w q : H) :
    θ w * (θ q)⁻¹ * (θ w)⁻¹ = θ (w * q⁻¹ * w⁻¹) := by
  simp only [map_mul, map_inv]

theorem conj_commutator (g x y : G) : g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

structure HeisCtx (θA θB θX : StatedSp 2 F3 →* G) (φ : Heis →* G) : Prop where
  e0 : ph φ bE0 = θA (weyl₁ * sbU * weyl₁⁻¹)
  e1 : ph φ bE1 = θB (weyl₁ * sbU * weyl₁⁻¹)
  f0 : ph φ bF0 = (θA sbL)⁻¹
  f1 : ph φ bF1 = (θB sbU)⁻¹
  act : ∀ (s : StatedSp 2 F3) (x : Heis), θX s * φ x * (θX s)⁻¹ = φ (heisAct s x)
  hub : θA weyl₁ = θB weyl₀
  cent : ∀ r, θX r * θA weyl₁ = θA weyl₁ * θX r

theorem weyl₁_conj_conj_inv' : weyl₁ * (weyl₁ * sbU * weyl₁⁻¹)⁻¹ * weyl₁⁻¹ = sbU := by
  rw [conj_inv, weyl₁_conj_conj, inv_inv]

theorem weyl₀_conj_inv' : weyl₀ * (weyl₁ * sbU * weyl₁⁻¹)⁻¹ * weyl₀⁻¹ = sbL := by
  rw [conj_inv, weyl₀_conj, inv_inv]

structure SwapCtx (θA θB θX : StatedSp 2 F3 →* G) (sg : G) (e : F3) : Prop where
  e_sq : e * e = 1
  aU : ∀ u, sg * rU θA u * sg⁻¹ = rL θA u
  aL : ∀ u, sg * rL θA u * sg⁻¹ = rU θA u
  cU : ∀ u, sg * rU θX u * sg⁻¹ = rU θB (e * u)
  bU : ∀ u, sg * rU θB u * sg⁻¹ = rU θX (e * u)
  cL : ∀ u, sg * rL θX u * sg⁻¹ = rL θB (e * u)
  bL : ∀ u, sg * rL θB u * sg⁻¹ = rL θX (e * u)

namespace HeisCtx

variable {θA θB θX : StatedSp 2 F3 →* G} {φ : Heis →* G} (H : HeisCtx θA θB θX φ)

include H

theorem rL_A (u : F3) : rL θA u = ph φ ((-u) • bF0) := by
  refine congrFun (eq_of_add_of_one (f := rL θA) (g := fun u => ph φ ((-u) • bF0)) (rL_add θA)
    ?_ ?_) u
  · intro s t
    simp only [neg_add, ph_smul_add]
  · show θA sbL = ph φ ((-1) • bF0)
    rw [neg_smul, one_smul, ph_neg, H.f0, inv_inv]

theorem rU_B (u : F3) : rU θB u = ph φ ((-u) • bF1) := by
  refine congrFun (eq_of_add_of_one (f := rU θB) (g := fun u => ph φ ((-u) • bF1)) (rU_add θB)
    ?_ ?_) u
  · intro s t
    simp only [neg_add, ph_smul_add]
  · show θB sbU = ph φ ((-1) • bF1)
    rw [neg_smul, one_smul, ph_neg, H.f1, inv_inv]

theorem rU_A (u : F3) : rU θA u = θA weyl₁ * ph φ ((-u) • bE0) * (θA weyl₁)⁻¹ := by
  refine congrFun (eq_of_add_of_one (f := rU θA)
    (g := fun u => θA weyl₁ * ph φ ((-u) • bE0) * (θA weyl₁)⁻¹) (rU_add θA) ?_ ?_) u
  · intro s t
    simp only [neg_add, ph_smul_add]
    group
  · show θA sbU = θA weyl₁ * ph φ ((-1) • bE0) * (θA weyl₁)⁻¹
    rw [neg_smul, one_smul, ph_neg, H.e0, hom_conj_inv, weyl₁_conj_conj_inv']

theorem rL_B (u : F3) : rL θB u = θA weyl₁ * ph φ ((-u) • bE1) * (θA weyl₁)⁻¹ := by
  rw [H.hub]
  refine congrFun (eq_of_add_of_one (f := rL θB)
    (g := fun u => θB weyl₀ * ph φ ((-u) • bE1) * (θB weyl₀)⁻¹) (rL_add θB) ?_ ?_) u
  · intro s t
    simp only [neg_add, ph_smul_add]
    group
  · show θB sbL = θB weyl₀ * ph φ ((-1) • bE1) * (θB weyl₀)⁻¹
    rw [neg_smul, one_smul, ph_neg, H.e1, hom_conj_inv, weyl₀_conj_inv']

theorem rel₂ (s t : F3) : ⁅rL θA s, rU θX t⁆ = rU θB (s * t) := by
  have hM : mat 2 F3 (sb (usl t)) *ᵥ ((-s) • bF0) = (-s) • bF0 + (s * t) • bF1 := by
    rw [Matrix.mulVec_smul, sb_usl_f0]
    module
  have hv : form ((-s) • bF0) (mat 2 F3 (sb (usl t)) *ᵥ ((-s) • bF0)) = 0 :=
    form_FF_of (-s) 0 (-s) (s * t) (by module) hM
  have hvec : (-s) • bF0 - ((-s) • bF0 + (s * t) • bF1) = (-(s * t)) • bF1 := by module
  rw [H.rL_A, H.rU_B, rU, comm_ph_theta H.act _ _ hv, hM, hvec]

theorem rel₆ (s t : F3) : ⁅rU θB s, rL θX t⁆ = rL θA (s * t) := by
  have hM : mat 2 F3 (sb (lsl t)) *ᵥ ((-s) • bF1) = (s * t) • bF0 + (-s) • bF1 := by
    rw [Matrix.mulVec_smul, sb_lsl_f1]
    module
  have hv : form ((-s) • bF1) (mat 2 F3 (sb (lsl t)) *ᵥ ((-s) • bF1)) = 0 :=
    form_FF_of 0 (-s) (s * t) (-s) (by module) hM
  have hvec : (-s) • bF1 - ((s * t) • bF0 + (-s) • bF1) = (-(s * t)) • bF0 := by module
  rw [H.rU_B, H.rL_A, rL, comm_ph_theta H.act _ _ hv, hM, hvec]

theorem comm_bc (s t : F3) : Commute (rU θB s) (rU θX t) := by
  rw [H.rU_B, rU]
  exact commute_ph_theta H.act _ _ (by rw [Matrix.mulVec_smul, sb_usl_f1])

theorem comm_a'c' (s t : F3) : Commute (rL θA s) (rL θX t) := by
  rw [H.rL_A, rL]
  exact commute_ph_theta H.act _ _ (by rw [Matrix.mulVec_smul, sb_lsl_f0])

theorem comm_ba' (s t : F3) : Commute (rU θB s) (rL θA t) := by
  rw [H.rU_B, H.rL_A]
  exact ph_comm φ (form_FF_of (v := (-s) • bF1) (w := (-t) • bF0) 0 (-s) (-t) 0 (by module)
    (by module))

theorem rel₃ (s t : F3) : ⁅rU θA s, rL θX t⁆ = rL θB (-(s * t)) := by
  have hM : mat 2 F3 (sb (lsl t)) *ᵥ ((-s) • bE0) = (-s) • bE0 + (-(s * t)) • bE1 := by
    rw [Matrix.mulVec_smul, sb_lsl_e0]
    module
  have hv : form ((-s) • bE0) (mat 2 F3 (sb (lsl t)) *ᵥ ((-s) • bE0)) = 0 :=
    form_EE_of (-s) 0 (-s) (-(s * t)) (by module) hM
  have hvec : (-s) • bE0 - ((-s) • bE0 + (-(s * t)) • bE1) = (-(-(s * t))) • bE1 := by module
  rw [H.rU_A, H.rL_B, rL, comm_conj_of_commute _ (H.cent (sb (lsl t))),
    comm_ph_theta H.act _ _ hv, hM, hvec]

theorem rel₅ (s t : F3) : ⁅rL θB s, rU θX t⁆ = rU θA (-(s * t)) := by
  have hM : mat 2 F3 (sb (usl t)) *ᵥ ((-s) • bE1) = (-(s * t)) • bE0 + (-s) • bE1 := by
    rw [Matrix.mulVec_smul, sb_usl_e1]
    module
  have hv : form ((-s) • bE1) (mat 2 F3 (sb (usl t)) *ᵥ ((-s) • bE1)) = 0 :=
    form_EE_of 0 (-s) (-(s * t)) (-s) (by module) hM
  have hvec : (-s) • bE1 - ((-(s * t)) • bE0 + (-s) • bE1) = (-(-(s * t))) • bE0 := by module
  rw [H.rL_B, H.rU_A, rU, comm_conj_of_commute _ (H.cent (sb (usl t))),
    comm_ph_theta H.act _ _ hv, hM, hvec]

theorem comm_ac (s t : F3) : Commute (rU θA s) (rU θX t) := by
  rw [H.rU_A, rU]
  exact commute_conj_of_commute (H.cent _)
    (commute_ph_theta H.act _ _ (by rw [Matrix.mulVec_smul, sb_usl_e0]))

theorem comm_b'c' (s t : F3) : Commute (rL θB s) (rL θX t) := by
  rw [H.rL_B, rL]
  exact commute_conj_of_commute (H.cent _)
    (commute_ph_theta H.act _ _ (by rw [Matrix.mulVec_smul, sb_lsl_e1]))

theorem comm_ab' (s t : F3) : Commute (rU θA s) (rL θB t) := by
  rw [H.rU_A, H.rL_B]
  exact (ph_comm φ (form_EE_of (v := (-s) • bE0) (w := (-t) • bE1) (-s) 0 0 (-t) (by module)
    (by module))).map (MulAut.conj (θA weyl₁))

theorem rel₁ {sg : G} {e : F3} (S : SwapCtx θA θB θX sg e) (s t : F3) :
    ⁅rU θA s, rU θB t⁆ = rU θX (s * t) := by
  have h := congrArg (fun x => sg * x * sg⁻¹) (H.rel₂ s (e * t))
  simp only [conj_commutator, S.aL, S.cU, S.bU] at h
  have e1 : e * (e * t) = t := by rw [← mul_assoc, S.e_sq, one_mul]
  have e2 : e * (s * (e * t)) = s * t := by
    calc e * (s * (e * t)) = (e * e) * (s * t) := by ring
      _ = s * t := by rw [S.e_sq, one_mul]
  rwa [e1, e2] at h

theorem rel₄ {sg : G} {e : F3} (S : SwapCtx θA θB θX sg e) (s t : F3) :
    ⁅rL θA s, rL θB t⁆ = rL θX (-(s * t)) := by
  have h := congrArg (fun x => sg * x * sg⁻¹) (H.rel₃ s (e * t))
  simp only [conj_commutator, S.aU, S.cL, S.bL] at h
  have e1 : e * (e * t) = t := by rw [← mul_assoc, S.e_sq, one_mul]
  have e2 : e * (-(s * (e * t))) = -(s * t) := by
    calc e * (-(s * (e * t))) = -((e * e) * (s * t)) := by ring
      _ = -(s * t) := by rw [S.e_sq, one_mul]
  rwa [e1, e2] at h

theorem steinbergFamily {sg : G} {e : F3} (S : SwapCtx θA θB θX sg e) :
    SteinbergFamily (rU θA) (rU θB) (rU θX) (rL θA) (rL θB) (rL θX) where
  add_a := rU_add θA
  add_b := rU_add θB
  add_c := rU_add θX
  add_a' := rL_add θA
  add_b' := rL_add θB
  add_c' := rL_add θX
  comm_ac := H.comm_ac
  comm_ab' := H.comm_ab'
  comm_bc := H.comm_bc
  comm_ba' := H.comm_ba'
  comm_a'c' := H.comm_a'c'
  comm_b'c' := H.comm_b'c'
  rel₁ := H.rel₁ S
  rel₂ := H.rel₂
  rel₃ := H.rel₃
  rel₄ := H.rel₄ S
  rel₅ := H.rel₅
  rel₆ := H.rel₆

end HeisCtx

end Rel

end CFSG.ClassicalInvolution.Q3.Q3ZA
