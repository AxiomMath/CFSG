module

public import CFSG.LargeExtraspecial.S11EightA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

variable (hy : Hyp S g) (K : Conf S g t τ u)
include hy K

omit hy in
theorem Conf.cl_commutator_mem {h : G} (hh : h ∈ S.QG) :
    S.cl ((τ : G) * h * (τ : G)⁻¹ * h⁻¹) ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hρ : S.ρ ⟨(τ : G), τ.2⟩ = t := K.rho_eq
  rw [S.cl_commutator τ.2 hh, hρ]
  exact sub_mem_commSpace _ _

theorem Conf.commutator_commute {h : G} (hh : h ∈ S.QG) :
    (τ : G) * h * (τ : G)⁻¹ * h⁻¹ * τ = τ * ((τ : G) * h * (τ : G)⁻¹ * h⁻¹) :=
  commute_of_cl_mem_commSpace K.rho_eq K.conj_eq
    (isTypeA_of_linCase hy.hyp4 K.ne_one K.lin).2.2.2.2
    (S.QG.mul_mem (S.conj_mem_QG τ.2 hh) (S.QG.inv_mem hh)) (K.cl_commutator_mem hh)

omit hy in
theorem Conf.commutator_commute_of_mem {h x : G} (hh : h ∈ S.QG)
    (hx : x ∈ S.QG ⊓ centralizer ({(τ : G)} : Set G)) :
    (τ : G) * h * (τ : G)⁻¹ * h⁻¹ * x = x * ((τ : G) * h * (τ : G)⁻¹ * h⁻¹) := by
  have hc : (τ : G) * h * (τ : G)⁻¹ * h⁻¹ ∈ S.QG :=
    S.QG.mul_mem (S.conj_mem_QG τ.2 hh) (S.QG.inv_mem hh)
  have hxQ : x ∈ S.QG := (mem_inf.mp hx).1
  rw [← S.polar_cl_eq_zero_iff hc hxQ]
  have hfx := K.clSub_centralizer_le_fixSpace (S.cl_mem_clSub hx hxQ)
  rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self K.mul_self),
    LinearMap.BilinForm.mem_orthogonal_iff] at hfx
  exact hfx _ (K.cl_commutator_mem hh)

theorem Conf.commute_of_commutator_mem_V (hCE : CentralExtInput.{u_G}) {h : G} (hh : h ∈ S.QG)
    (hc : (τ : G) * h * (τ : G)⁻¹ * h⁻¹ ∈ V S g t) {e : G} (he : e ∈ S.QG ⊓ S.Qa u) :
    h * e = e * h := by
  have hρ : S.ρ ⟨(τ : G), τ.2⟩ = t := K.rho_eq
  have h1 : S.cl ((τ : G) * h * (τ : G)⁻¹ * h⁻¹) ∈ Vt S g t := (S.mem_clPre.mp hc).2
  rw [S.cl_commutator τ.2 hh, hρ] at h1
  have h2 := K.mem_Wt_of_sub_mem_Vt hy hCE h1
  have h3 : S.cl e ∈ Vt S g t := by
    rw [← K.timmesfeld_11_3 hy]
    exact S.cl_mem_clSub he he.1
  have h4 := mem_Wt.mp h2 _ h3
  rw [S.polar_cl_eq_zero_iff he.1 hh] at h4
  exact h4.symm

omit hy K in
theorem conj_mem_Qa_inv_of_mem_QG {u x : G} (hx : x ∈ S.QG) : u⁻¹ * x * u ∈ S.Qa u⁻¹ := by
  have := conj_mem_Qa_inv_mul (S := S) (w := u) (k := 1) (by rw [S.Qa_one]; exact hx)
  simpa using this

theorem Conf.dual_commutator_commute {h' : G} (hh' : h' ∈ S.Qa u) :
    S.z * h' * S.z⁻¹ * h'⁻¹ * S.z = S.z * (S.z * h' * S.z⁻¹ * h'⁻¹) := by
  obtain ⟨hM, Kd⟩ := K.dual hy
  have hyd := hy.of_conj (K.dual_base hy).1 (K.dual_base hy).2
  have key := Kd.commutator_commute hyd (h := u⁻¹ * h' * u) ((S11.mem_Qa_iff S u _).mp hh')
  change u⁻¹ * S.z * u * (u⁻¹ * h' * u) * (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹ *
      (u⁻¹ * S.z * u) = (u⁻¹ * S.z * u) * (u⁻¹ * S.z * u * (u⁻¹ * h' * u) *
      (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹) at key
  calc S.z * h' * S.z⁻¹ * h'⁻¹ * S.z = u * (u⁻¹ * S.z * u * (u⁻¹ * h' * u) *
        (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹ * (u⁻¹ * S.z * u)) * u⁻¹ := by group
    _ = u * ((u⁻¹ * S.z * u) * (u⁻¹ * S.z * u * (u⁻¹ * h' * u) *
        (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹)) * u⁻¹ := by rw [key]
    _ = S.z * (S.z * h' * S.z⁻¹ * h'⁻¹) := by group

theorem Conf.dual_commutator_commute_of_mem {h' x : G} (hh' : h' ∈ S.Qa u)
    (hx : x ∈ S.Qa u ⊓ S.M) :
    S.z * h' * S.z⁻¹ * h'⁻¹ * x = x * (S.z * h' * S.z⁻¹ * h'⁻¹) := by
  obtain ⟨hM, Kd⟩ := K.dual hy
  have hxz : x * S.z = S.z * x := S.z_comm (mem_inf.mp hx).2
  have hxd : u⁻¹ * x * u ∈ S.QG ⊓ centralizer ({u⁻¹ * S.z * u} : Set G) := by
    refine mem_inf.mpr ⟨(S11.mem_Qa_iff S u _).mp (mem_inf.mp hx).1, ?_⟩
    rw [mem_centralizer_singleton_iff]
    calc u⁻¹ * x * u * (u⁻¹ * S.z * u) = u⁻¹ * (x * S.z) * u := by group
      _ = u⁻¹ * (S.z * x) * u := by rw [hxz]
      _ = u⁻¹ * S.z * u * (u⁻¹ * x * u) := by group
  have key := Kd.commutator_commute_of_mem (h := u⁻¹ * h' * u)
    ((S11.mem_Qa_iff S u _).mp hh') hxd
  change u⁻¹ * S.z * u * (u⁻¹ * h' * u) * (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹ *
      (u⁻¹ * x * u) = (u⁻¹ * x * u) * (u⁻¹ * S.z * u * (u⁻¹ * h' * u) *
      (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹) at key
  calc S.z * h' * S.z⁻¹ * h'⁻¹ * x = u * (u⁻¹ * S.z * u * (u⁻¹ * h' * u) *
        (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹ * (u⁻¹ * x * u)) * u⁻¹ := by group
    _ = u * ((u⁻¹ * x * u) * (u⁻¹ * S.z * u * (u⁻¹ * h' * u) *
        (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹)) * u⁻¹ := by rw [key]
    _ = x * (S.z * h' * S.z⁻¹ * h'⁻¹) := by group

theorem Conf.dual_commute_of_commutator_mem (hCE : CentralExtInput.{u_G}) {h' : G}
    (hh' : h' ∈ S.Qa u) {e : G} (he : e ∈ S.QG ⊓ S.Qa u)
    (hc : S.z * h' * S.z⁻¹ * h'⁻¹ = e ∨ S.z * h' * S.z⁻¹ * h'⁻¹ = e * τ) {e' : G}
    (he' : e' ∈ S.QG ⊓ S.Qa u) : h' * e' = e' * h' := by
  obtain ⟨hM, Kd⟩ := K.dual hy
  have hyd := hy.of_conj (K.dual_base hy).1 (K.dual_base hy).2
  have hE : ∀ x ∈ S.QG ⊓ S.Qa u, u⁻¹ * x * u ∈ S.QG ⊓ S.Qa u⁻¹ := fun x hx =>
    mem_inf.mpr ⟨(S11.mem_Qa_iff S u _).mp (mem_inf.mp hx).2,
      conj_mem_Qa_inv_of_mem_QG (mem_inf.mp hx).1⟩
  have hcd : u⁻¹ * S.z * u * (u⁻¹ * h' * u) * (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹ ∈
      V S (u⁻¹ * g) (S.ρ ⟨u⁻¹ * S.z * u, hM⟩) := by
    have he1 := hE e he
    have heQ : u⁻¹ * e * u ∈ S.QG := (mem_inf.mp he1).1
    have hcl : S.cl (u⁻¹ * e * u) ∈ Vt S (u⁻¹ * g) (S.ρ ⟨u⁻¹ * S.z * u, hM⟩) := by
      rw [← Kd.timmesfeld_11_3 hyd]
      exact S.cl_mem_clSub he1 heQ
    have hcalc : u⁻¹ * S.z * u * (u⁻¹ * h' * u) * (u⁻¹ * S.z * u)⁻¹ * (u⁻¹ * h' * u)⁻¹ =
        u⁻¹ * (S.z * h' * S.z⁻¹ * h'⁻¹) * u := by group
    rw [hcalc]
    rcases hc with hc | hc
    · rw [hc]
      exact S.mem_clPre.mpr ⟨heQ, hcl⟩
    · rw [hc, K.conj_eq, show u⁻¹ * (e * (u * S.z * u⁻¹)) * u = u⁻¹ * e * u * S.z by group]
      refine S.mem_clPre.mpr ⟨S.QG.mul_mem heQ S.z_mem_QG, ?_⟩
      rw [S.cl_mul heQ S.z_mem_QG, S.cl_z, add_zero]
      exact hcl
  have key := Kd.commute_of_commutator_mem_V hyd hCE (h := u⁻¹ * h' * u)
    ((S11.mem_Qa_iff S u _).mp hh') hcd (hE e' he')
  calc h' * e' = u * ((u⁻¹ * h' * u) * (u⁻¹ * e' * u)) * u⁻¹ := by group
    _ = u * ((u⁻¹ * e' * u) * (u⁻¹ * h' * u)) * u⁻¹ := by rw [key]
    _ = e' * h' := by group

end CFSG.LargeExtraspecial.S11
