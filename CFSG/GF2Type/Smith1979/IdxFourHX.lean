module

public import CFSG.GF2Type.Smith1979.IdxFourHFacts
public import CFSG.GF2Type.Smith1979.IdxFourHLift
public import CFSG.GF2Type.Smith1979.IdxFourHLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem mem_orthogonal_span_singleton {a v : S.Qt} :
    v ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {a}) ↔
      polar S.q a v = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    have := h a (Submodule.subset_span rfl)
    simpa [LinearMap.BilinForm.IsOrtho, polarBilin_apply_apply] using this
  · intro h w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [LinearMap.BilinForm.IsOrtho, polarBilin_apply_apply, polar_smul_left, h]

theorem exists_x_data {g : G} {K : Subgroup S.O} {θ xb : S.O} (hF : IdxFourFacts S g K θ xb)
    (hw : S.width = 6) :
    ∃ x : G, ∃ hxM : x ∈ S.M, x * x = 1 ∧ S.ρ ⟨x, hxM⟩ = xb ∧
      ∃ U : Submodule (ZMod 2) S.Qt, 9 ≤ finrank (ZMod 2) U ∧ U ≤ fixO S xb ∧
        (∀ y ∈ S.clPre U, y * x = x * y) ∧
        (∀ y : S.Qt, (∀ v ∈ U, polar S.q y v = 0) → S.q y = 0 → y ∈ commO S xb) := by
  have hq12 : finrank (ZMod 2) S.Qt = 12 := by rw [S.finrank_Qt_eq_two_mul_width, hw]
  obtain ⟨c, hc3, hcρ⟩ := exists_pow3_lift hF.θ_mem hF.θ_cube
  have hfpf : ∀ v : S.Qt, (S.ρ c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0 := by
    rw [hcρ]
    exact hF.θ_fpf
  obtain ⟨s, hsρ, hcs⟩ := exists_comm_lift hc3 hF.x_mem (by rw [hcρ]; exact hF.x_comm.symm)
  have hs2 : S.ρ s * S.ρ s = 1 := by rw [hsρ]; exact hF.x_sq
  have hsq := sq_eq_one_or_z_of_comm hc3 hfpf hcs hs2
  have hFdim : finrank (ZMod 2) (fixO S xb) = 10 := by
    have := finrank_commO_add_fixO xb
    rw [hF.x_dim, hq12] at this
    omega
  have hFperp := fixO_eq_orthogonal hF.x_sq
  obtain ⟨r, hrQ, hrF, hr0, hrsq⟩ : ∃ r : G, r ∈ S.QG ∧ S.cl r ∈ fixO S xb ∧
      (S.cl r = 0 ∨ S.q (S.cl r) = 1) ∧ r * r = (s : G) * s := by
    rcases hsq with h1 | h1
    · refine ⟨1, S.QG.one_mem, ?_, Or.inl S.cl_one, by rw [h1]; simp⟩
      rw [S.cl_one]
      exact Submodule.zero_mem _
    · obtain ⟨r0, hr0F, hr0q⟩ := exists_q_eq_one hq12 (F := fixO S xb) (by omega)
      obtain ⟨r, hrQ, rfl⟩ := S.exists_cl r0
      refine ⟨r, hrQ, hr0F, Or.inr hr0q, ?_⟩
      have hne : r ^ 2 ≠ 1 := (S.q_cl_eq_one_iff hrQ).mp hr0q
      rcases S.sq_eq_one_or_z hrQ with h | h
      · exact absurd h hne
      · rw [h1, ← h, pow_two]
  have hsr : (s : G) * r = r * s := by
    have h := conj_eq_of_fixed hc3 hfpf hcs hrQ (by rw [hsρ]; exact mem_fixO.mp hrF)
    calc (s : G) * r = (s : G) * r * (s : G)⁻¹ * s := by group
      _ = r * s := by rw [h]
  have hxM : (s : G) * r ∈ S.M := S.M.mul_mem s.2 (S.QG_le_M hrQ)
  have hxx : ((s : G) * r) * ((s : G) * r) = 1 := by
    have hss : ((s : G) * s) * ((s : G) * s) = 1 := by
      rcases hsq with h | h
      · rw [h]; simp
      · rw [h]; exact S.z_mul_z
    calc ((s : G) * r) * ((s : G) * r) = (s : G) * (r * s) * r := by group
      _ = (s : G) * (s * r) * r := by rw [hsr]
      _ = ((s : G) * s) * (r * r) := by group
      _ = ((s : G) * s) * ((s : G) * s) := by rw [hrsq]
      _ = 1 := hss
  have hρx : S.ρ ⟨(s : G) * r, hxM⟩ = xb := by
    have : (⟨(s : G) * r, hxM⟩ : S.M) = s * ⟨r, S.QG_le_M hrQ⟩ := rfl
    rw [this, map_mul, hsρ, (S.ρ_eq_one_iff ⟨r, S.QG_le_M hrQ⟩).mpr hrQ, mul_one]
  set U : Submodule (ZMod 2) S.Qt := fixO S xb ⊓
    LinearMap.BilinForm.orthogonal S.q.polarBilin (Submodule.span (ZMod 2) {S.cl r}) with hU
  refine ⟨(s : G) * r, hxM, hxx, hρx, U, nine_le_finrank_inf_orthogonal hFdim hq12 _, inf_le_left,
    ?_, ?_⟩
  · intro y hy
    have hyQ : y ∈ S.QG := hy.1
    have hyU : S.cl y ∈ U := hy.2
    have h1 : (s : G) * y = y * s := by
      have h := conj_eq_of_fixed hc3 hfpf hcs hyQ (by rw [hsρ]; exact mem_fixO.mp hyU.1)
      calc (s : G) * y = (s : G) * y * (s : G)⁻¹ * s := by group
        _ = y * s := by rw [h]
    have h2 : r * y = y * r := by
      have h0 : polar S.q (S.cl r) (S.cl y) = 0 := mem_orthogonal_span_singleton.mp hyU.2
      exact (S.polar_cl_eq_zero_iff hrQ hyQ).mp h0
    calc y * ((s : G) * r) = (y * s) * r := by group
      _ = ((s : G) * y) * r := by rw [h1]
      _ = (s : G) * (y * r) := by group
      _ = (s : G) * (r * y) := by rw [h2]
      _ = ((s : G) * r) * y := by group
  · intro y hy hyq
    refine mem_of_perp_singular hFperp hF.x_sing hrF hr0 (fun v hv hrv => hy v ?_) hyq
    exact ⟨hv, mem_orthogonal_span_singleton.mpr hrv⟩

end CFSG.GF2Type.Smith1979.IdxFour
