module

public import CFSG.ClassicalInvolution.Phan.PhanQ43Theta
public import CFSG.ClassicalInvolution.Phan.PhanQ7Dict
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs

section Rot

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem vecK_rot (hε : ε ≠ 0) (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1) (z : NPair ε) :
    vecK D (z.rot hε s t hst) = (algebraMap F K s + D.θ * algebraMap F K t) • vecK D z := by
  unfold vecK
  ext i
  simp only [NPair.rot_x, NPair.rot_y, Pi.add_apply, Pi.smul_apply, extV, smul_eq_mul, one_mul,
    map_add, map_mul, map_neg]
  have h := theta_mul_theta D
  have ht : algebraMap F K (t / ε) = -(D.θ * D.θ) * algebraMap F K t := by
    rw [h, neg_neg, ← map_mul]
    congr 1
    ring
  rw [ht]
  ring

theorem vecK_injective (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {z w : NPair ε}
    (h : vecK D z = vecK D w) : z = w := by
  have h' : extV K (z.x - w.x) + D.θ • extV K (z.y - w.y) = 0 := by
    ext i
    have := congrFun h i
    simp only [vecK, Pi.add_apply, Pi.smul_apply, extV, smul_eq_mul, one_mul, map_sub,
      Pi.sub_apply, Pi.zero_apply] at this ⊢
    linear_combination this
  obtain ⟨h1, h3⟩ := extV_theta_indep h2 hε h'
  ext1
  · exact sub_eq_zero.1 h1
  · exact sub_eq_zero.1 h3

theorem norm_eq_one_of_vecK_smul (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {z w : NPair ε} {κ : K}
    (h : vecK D z = κ • vecK D w) : κ * D.τ κ = 1 := by
  have h1 := her_vecK_self D hε z
  rw [h, her_smul_left, her_smul_right, her_vecK_self D hε] at h1
  have h4 : algebraMap F K 4 ≠ 0 := (map_ne_zero _).2 (four_ne_zero_of_algebra (F := F) h2)
  have : (κ * D.τ κ - 1) * algebraMap F K 4 = 0 := by linear_combination h1
  have := (mul_eq_zero.1 this).resolve_right h4
  linear_combination this

theorem exists_rot_of_vecK_smul (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {z w : NPair ε} {κ : K}
    (h : vecK D z = κ • vecK D w) :
    ∃ (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1), z = w.rot hε s t hst := by
  have hn := norm_eq_one_of_vecK_smul D h2 hε h
  obtain ⟨s, t, hκ⟩ := exists_decomp D h2 hε κ
  have hst : s ^ 2 + t ^ 2 / ε = 1 := by
    rw [hκ] at hn
    have h3 := theta_mul_theta D
    rw [map_add, map_mul, D.tau_alg, D.tau_alg, D.tau_theta] at hn
    have e1 : algebraMap F K (s ^ 2 + t ^ 2 / ε) = algebraMap F K s ^ 2 +
        algebraMap F K (1 / ε) * algebraMap F K t ^ 2 := by
      simp [div_eq_mul_inv, mul_comm]
    have h5 : algebraMap F K (s ^ 2 + t ^ 2 / ε) = algebraMap F K 1 := by
      rw [e1, map_one]
      linear_combination hn + (algebraMap F K t) ^ 2 * h3
    exact (algebraMap F K).injective h5
  refine ⟨s, t, hst, vecK_injective D h2 hε ?_⟩
  rw [vecK_rot, h, hκ]

theorem rotScalar_mul_conj (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1) :
    (algebraMap F K s + D.θ * algebraMap F K t) *
      D.τ (algebraMap F K s + D.θ * algebraMap F K t) = 1 := by
  have h3 := theta_mul_theta D
  rw [map_add, map_mul, D.tau_alg, D.tau_alg, D.tau_theta]
  have e1 : algebraMap F K (s ^ 2 + t ^ 2 / ε) = algebraMap F K s ^ 2 +
      algebraMap F K (1 / ε) * algebraMap F K t ^ 2 := by
    simp [div_eq_mul_inv, mul_comm]
  have h5 := congrArg (algebraMap F K) hst
  rw [e1, map_one] at h5
  linear_combination h5 - (algebraMap F K t) ^ 2 * h3

theorem rotScalar_ne_zero (s t : F) (hst : s ^ 2 + t ^ 2 / ε = 1) :
    algebraMap F K s + D.θ * algebraMap F K t ≠ 0 := by
  intro h
  have := rotScalar_mul_conj D s t hst
  rw [h, zero_mul] at this
  exact zero_ne_one this

end Rot

section PtLine

variable {p e : ℕ} [Fact p.Prime] (M : StdModel p e) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  (D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε)

@[expose] noncomputable def ptVec (g : spinGroup (quadPlus 4 (GaloisField p e))) :
    V8 (GaloisField p (2 * e)) :=
  vecK D (g • z0 M.ε)

variable {M D}

include hp2 hq in
theorem ptVec_mul_of_mem {g k : spinGroup (quadPlus 4 (GaloisField p e))}
    (hk : k ∈ parab M.S {1, 2, 3}) :
    ∃ κ : GaloisField p (2 * e), κ ≠ 0 ∧ ptVec M D (g * k) = κ • ptVec M D g := by
  obtain ⟨s, t, hst, hrot⟩ := exists_rot_of_mem_parab M hp2 hq hk
  refine ⟨_, rotScalar_ne_zero D s t hst, ?_⟩
  unfold ptVec
  rw [NPair.mul_smul', hrot, smul_rot M.hε, vecK_rot D M.hε]

theorem ptVec_ne_zero (h2 : (2 : GaloisField p (2 * e)) ≠ 0)
    (g : spinGroup (quadPlus 4 (GaloisField p e))) : ptVec M D g ≠ 0 := by
  intro h0
  have := (ffK_vecK D h2 M.hε (g • z0 M.ε)).2
  apply this
  unfold ptVec at h0
  rw [h0]
  unfold her
  simp

end PtLine

section LineOfPt

variable {p e : ℕ} [Fact p.Prime] (M : StdModel p e)
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  (D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)

@[expose] noncomputable def lineOfPt
    (x : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}) :
    Submodule (GaloisField p (2 * e)) (V8 (GaloisField p (2 * e))) :=
  Quotient.liftOn' x (fun g => Submodule.span _ {ptVec M D g}) (fun a b hab => by
    have hk : a⁻¹ * b ∈ parab M.S {1, 2, 3} := QuotientGroup.leftRel_apply.1 hab
    obtain ⟨κ, hκ, h⟩ := ptVec_mul_of_mem hp2 hq (g := a) hk
    rw [mul_inv_cancel_left] at h
    show Submodule.span _ {ptVec M D a} = Submodule.span _ {ptVec M D b}
    rw [h, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hκ)])

variable {M D}

theorem lineOfPt_mk (g : spinGroup (quadPlus 4 (GaloisField p e))) :
    lineOfPt M D hp2 hq (g : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}) =
      Submodule.span _ {ptVec M D g} := rfl

include hp2 hq in
theorem lineOfPt_injective : Function.Injective (lineOfPt M D hp2 hq) := by
  intro x y hxy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [lineOfPt_mk, lineOfPt_mk] at hxy
  have h2K := two_ne_zero_gf hp2 (2 * e)
  have hmem : ptVec M D g ∈ Submodule.span _ {ptVec M D h} :=
    hxy ▸ Submodule.mem_span_singleton_self _
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.1 hmem
  obtain ⟨s, t, hst, hrot⟩ := exists_rot_of_vecK_smul D h2K M.hε (z := g • z0 M.ε)
    (w := h • z0 M.ε) (κ := κ) hκ.symm
  have h1 : (h⁻¹ * g) • z0 M.ε = (z0 M.ε).rot M.hε s t hst := by
    have : g • z0 M.ε = h • (z0 M.ε).rot M.hε s t hst := by
      rw [smul_rot M.hε, ← hrot]
    rw [NPair.mul_smul', this, NPair.inv_smul_smul']
  have h3 := mem_parab_of_rot M hp2 hq h1
  apply QuotientGroup.eq.2
  simpa using inv_mem h3

theorem lineOfPt_ff (h2K : (2 : GaloisField p (2 * e)) ≠ 0)
    (x : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}) :
    ∃ v : V8 (GaloisField p (2 * e)), v ≠ 0 ∧ ffK D v ∧
      lineOfPt M D hp2 hq x = Submodule.span _ {v} := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨ptVec M D g, ptVec_ne_zero h2K g, ffK_vecK D h2K M.hε _, rfl⟩

include hp2 hq in
theorem exists_pt_of_ffK {v : V8 (GaloisField p (2 * e))} (hv : ffK D v) :
    ∃ x, lineOfPt M D hp2 hq x = Submodule.span _ {v} := by
  have h2 := two_ne_zero_gf hp2 e
  have h2K := two_ne_zero_gf hp2 (2 * e)
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  obtain ⟨κ, hκ, z, rfl⟩ := exists_npair_of_ffK D hodd h2K M.hε hv
  obtain ⟨g, rfl⟩ := exists_smul_z0 h2 hodd M.hε M.h4 z
  refine ⟨(g : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}), ?_⟩
  rw [lineOfPt_mk, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hκ)]
  rfl

include hp2 hq in
theorem adj_iff_adjL (x y : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}) :
    (ptGraph M.S).Adj x y ↔ AdjL D (lineOfPt M D hp2 hq x) (lineOfPt M D hp2 hq y) := by
  have h2K := two_ne_zero_gf hp2 (2 * e)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  rw [adj_iff M hp2 hq, lineOfPt_mk, lineOfPt_mk, adjL_span_iff, ptVec, ptVec,
    colK_vecK_iff D h2K M.hε]

end LineOfPt

end CFSG.ClassicalInvolution.PhanQ
