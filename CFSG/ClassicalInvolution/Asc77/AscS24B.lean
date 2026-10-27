module

public import CFSG.ClassicalInvolution.Asc77.AscS24Ctx
public import CFSG.ClassicalInvolution.Asc77.AscS24Elem
public import CFSG.ClassicalInvolution.Asc77.AscT7K7

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

namespace Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}
  (C : Ctx p f Ω K K' W S R R' z u g)

include C

theorem u_sq : u * u = 1 := C.hd.hu.2.2.1

theorem z_sq : z * z = 1 := C.hs.hz.sq

theorem u_ne_one : u ≠ 1 := C.hd.hu.2.2.2.1

theorem u_ne_z : u ≠ z := C.hd.hu.2.2.2.2

theorem comm_uz : u * z = z * u := C.comm_W C.u_mem_W C.z_mem_W

theorem comm_ue : u * C.e0 = C.e0 * u := C.comm_W C.u_mem_W C.e0_mem

theorem comm_ze : z * C.e0 = C.e0 * z := C.comm_W C.z_mem_W C.e0_mem

theorem B_isElemAbelian (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    IsElemAbelian 2 C.B :=
  B_isElemAbelian_of C.u_sq C.z_sq (C.e0_sq hZ) C.comm_uz C.comm_ue C.comm_ze

theorem B_le_W : C.B ≤ W := by
  rw [B, Subgroup.closure_le]
  rintro x (rfl | rfl | rfl)
  · exact W.mul_mem C.u_mem_W C.e0_mem
  · exact C.u_mem_W
  · exact C.z_mem_W

theorem z_mem_B : z ∈ C.B := Subgroup.subset_closure (by simp)

theorem u_mem_B : u ∈ C.B := Subgroup.subset_closure (by simp)

theorem e0_mem_B : C.e0 ∈ C.B := by
  have h1 : u * C.e0 ∈ C.B := Subgroup.subset_closure (by simp)
  have : C.e0 = u⁻¹ * (u * C.e0) := by group
  rw [this]
  exact C.B.mul_mem (C.B.inv_mem C.u_mem_B) h1

theorem conj_r_uz : C.D.F.ρ.r * (u * z) * C.D.F.ρ.r⁻¹ = u := by
  have h1 := C.conj_r_u
  have h2 := conj_r_z C.D
  rw [C.hz] at h2
  calc C.D.F.ρ.r * (u * z) * C.D.F.ρ.r⁻¹
      = (C.D.F.ρ.r * u * C.D.F.ρ.r⁻¹) * (C.D.F.ρ.r * z * C.D.F.ρ.r⁻¹) := by group
    _ = u * (z * z) := by rw [h1, h2]; group
    _ = u := by rw [C.z_sq, mul_one]

theorem e0_not_mem : C.e0 ∉ Subgroup.closure ({u, z} : Set G) := by
  intro h
  have h' : C.e0 ∈ Subgroup.closure ({u * z, u, z} : Set G) :=
    Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp) h
  have hz1 : z ≠ 1 := C.hs.hz.ne_one
  have hr := C.conj_r_e0
  have hs := C.conj_s_e0
  rcases T7K.mem_cases_of_commuting_involutions C.u_sq C.z_sq C.z_sq C.comm_uz C.comm_uz
      rfl h' with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact C.e0_ne_one h1
  · rw [h1, C.conj_s_z] at hs
    exact C.u_ne_one (by simpa using hs)
  · rw [h1, C.conj_r_u] at hr
    exact hz1 (by simpa using hr)
  · rw [h1, C.conj_r_uz] at hr
    exact hz1 (by simpa using hr.symm)
  · rw [h1, C.conj_s_z] at hs
    exact C.u_ne_one (by simpa using hs)
  · rw [C.z_sq] at h1
    exact C.e0_ne_one h1
  · rw [h1, C.conj_r_uz] at hr
    exact hz1 (by simpa using hr.symm)
  · rw [mul_assoc, C.z_sq, mul_one] at h1
    rw [h1, C.conj_r_u] at hr
    exact hz1 (by simpa using hr)

theorem B_natCard (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    Nat.card ↥C.B = 8 :=
  B_natCard_of C.u_sq C.z_sq (C.e0_sq hZ) C.u_ne_one C.hs.hz.ne_one C.u_ne_z C.comm_uz
    C.comm_ue C.comm_ze C.e0_not_mem

theorem mem_normalizer_B (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) : n ∈ Subgroup.normalizer (C.B : Set G) :=
  mem_normalizer_of_card_eq_eight (fun _ hx _ hy => C.comm_W hx hy) C.D.x₁_mem C.D.x₂_mem
    C.D.x₃_mem C.D.hgen C.B_le_W (C.B_isElemAbelian hZ) (C.B_natCard hZ) hn

theorem orbit_cover (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) :
    ∀ x ∈ C.B, x ≠ 1 → ∃ y ∈ ({z, C.e0} : Set G), ∃ n ∈ Subgroup.normalizer (C.B : Set G),
      x = n * y * n⁻¹ := by
  intro x hx hx1
  have hr : C.D.F.ρ.r ∈ Subgroup.normalizer (C.B : Set G) :=
    C.mem_normalizer_B hZ C.D.F.ρ.r_mem_normalizer
  have ht : C.D.F.ρ'.r ∈ Subgroup.normalizer (C.B : Set G) :=
    C.mem_normalizer_B hZ C.D.F.ρ'.r_mem_normalizer
  have hs : C.D.F.ρ₃.r ∈ Subgroup.normalizer (C.B : Set G) :=
    C.mem_normalizer_B hZ C.D.F.ρ₃.r_mem_normalizer
  have hze : C.e0 * z = z * C.e0 := C.comm_ze.symm
  rcases T7K.mem_cases_of_commuting_involutions C.u_sq C.z_sq (C.e0_sq hZ) C.comm_uz C.comm_ue
      C.comm_ze hx with h | h | h | h | h | h | h | h
  · exact absurd h hx1
  · exact ⟨z, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
  · refine ⟨z, by simp, C.D.F.ρ.r * C.D.F.ρ₃.r, Subgroup.mul_mem _ hr hs, ?_⟩
    rw [h]
    calc u = C.D.F.ρ.r * (u * z) * C.D.F.ρ.r⁻¹ := C.conj_r_uz.symm
      _ = C.D.F.ρ.r * (C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹) * C.D.F.ρ.r⁻¹ := by rw [C.conj_s_z]
      _ = C.D.F.ρ.r * C.D.F.ρ₃.r * z * (C.D.F.ρ.r * C.D.F.ρ₃.r)⁻¹ := by group
  · exact ⟨z, by simp, C.D.F.ρ₃.r, hs, by rw [h, C.conj_s_z]⟩
  · exact ⟨C.e0, by simp, 1, Subgroup.one_mem _, by rw [h]; group⟩
  · refine ⟨C.e0, by simp, C.D.F.ρ'.r, ht, ?_⟩
    rw [h, C.conj_t_e0, hze]
  · refine ⟨C.e0, by simp, C.D.F.ρ.r * C.D.F.ρ₃.r * C.D.F.ρ'.r,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hr hs) ht, ?_⟩
    rw [h]
    have e1 : C.D.F.ρ₃.r * (C.e0 * z) * C.D.F.ρ₃.r⁻¹ = C.e0 * (u * z) := by
      calc C.D.F.ρ₃.r * (C.e0 * z) * C.D.F.ρ₃.r⁻¹
          = (C.D.F.ρ₃.r * C.e0 * C.D.F.ρ₃.r⁻¹) * (C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹) := by group
        _ = C.e0 * (u * z) := by rw [C.conj_s_e0, C.conj_s_z]
    have e2 : C.D.F.ρ.r * (C.e0 * (u * z)) * C.D.F.ρ.r⁻¹ = C.e0 * u := by
      calc C.D.F.ρ.r * (C.e0 * (u * z)) * C.D.F.ρ.r⁻¹
          = (C.D.F.ρ.r * C.e0 * C.D.F.ρ.r⁻¹) * (C.D.F.ρ.r * (u * z) * C.D.F.ρ.r⁻¹) := by group
        _ = C.e0 * u := by rw [C.conj_r_e0, C.conj_r_uz]
    calc u * C.e0 = C.e0 * u := C.comm_ue
      _ = C.D.F.ρ.r * (C.D.F.ρ₃.r * (C.D.F.ρ'.r * C.e0 * C.D.F.ρ'.r⁻¹) * C.D.F.ρ₃.r⁻¹) *
          C.D.F.ρ.r⁻¹ := by rw [C.conj_t_e0, e1, e2]
      _ = C.D.F.ρ.r * C.D.F.ρ₃.r * C.D.F.ρ'.r * C.e0 *
          (C.D.F.ρ.r * C.D.F.ρ₃.r * C.D.F.ρ'.r)⁻¹ := by group
  · refine ⟨C.e0, by simp, C.D.F.ρ₃.r * C.D.F.ρ'.r, Subgroup.mul_mem _ hs ht, ?_⟩
    rw [h]
    have e1 : C.D.F.ρ₃.r * (C.e0 * z) * C.D.F.ρ₃.r⁻¹ = C.e0 * (u * z) := by
      calc C.D.F.ρ₃.r * (C.e0 * z) * C.D.F.ρ₃.r⁻¹
          = (C.D.F.ρ₃.r * C.e0 * C.D.F.ρ₃.r⁻¹) * (C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹) := by group
        _ = C.e0 * (u * z) := by rw [C.conj_s_e0, C.conj_s_z]
    have hc : u * z * C.e0 = C.e0 * (u * z) := C.comm_W (W.mul_mem C.u_mem_W C.z_mem_W) C.e0_mem
    calc u * z * C.e0 = C.e0 * (u * z) := hc
      _ = C.D.F.ρ₃.r * (C.D.F.ρ'.r * C.e0 * C.D.F.ρ'.r⁻¹) * C.D.F.ρ₃.r⁻¹ := by
          rw [C.conj_t_e0, e1]
      _ = C.D.F.ρ₃.r * C.D.F.ρ'.r * C.e0 * (C.D.F.ρ₃.r * C.D.F.ρ'.r)⁻¹ := by group

theorem e0u_cent_R' : R' ≤ Subgroup.centralizer ({C.e0 * u} : Set G) := by
  have hfix : C.D.F.ρ'.r * (C.e0 * u) * C.D.F.ρ'.r⁻¹ = C.e0 * u := by
    have hzu : z * u = u * z := C.comm_uz.symm
    calc C.D.F.ρ'.r * (C.e0 * u) * C.D.F.ρ'.r⁻¹
        = (C.D.F.ρ'.r * C.e0 * C.D.F.ρ'.r⁻¹) * (C.D.F.ρ'.r * u * C.D.F.ρ'.r⁻¹) := by group
      _ = C.e0 * (z * u) * z := by rw [C.conj_t_e0, C.conj_t_u]; group
      _ = C.e0 * u * (z * z) := by rw [hzu]; group
      _ = C.e0 * u := by rw [C.z_sq, mul_one]
  have h := T7X.rep_le_centralizer C.D.c C.D.F.ρ' (W.mul_mem C.e0_mem C.u_mem_W) hfix
  rwa [C.hR'] at h

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
