module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22CaseBOdd

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace BCtx_F4

variable {T M L V : Subgroup G} {g : G} {D : Subgroup G} (c : BCtx_F4 T M L V g D)

include c in
theorem Vg_comm {x y : G} (hx : x ∈ conjSubgroup V g) (hy : y ∈ conjSubgroup V g) :
    x * y = y * x := by
  apply (MulAut.conj g).injective
  simp only [map_mul, MulAut.conj_apply]
  exact B2F.isElemAbelian_comm c.h.toHyp611.isElemAbelian (mem_conjSubgroup_iff.mp hx)
    (mem_conjSubgroup_iff.mp hy)

include c in
theorem Vg_sq {x : G} (hx : x ∈ conjSubgroup V g) : x ^ 2 = 1 := by
  have h2 := c.h.toHyp611.isElemAbelian.2 _ (mem_conjSubgroup_iff.mp hx)
  rw [conj_pow] at h2
  simpa using h2

include c in
theorem exists_y : ∃ y ∈ L, y ∈ conjSubgroup V g ∧ y ^ 2 = 1 ∧ c.ρ y * c.ρ y = 1 ∧
    c.ρ y ≠ 1 ∧ Equiv.Perm.sign (c.ρ y) = 1 := by
  obtain ⟨a, haV1, haN, has, ha2⟩ := c.exists_a₁
  have haD : a ∈ D := c.hk.kData.V1_le_D haV1
  have haT : a ∈ T := c.D_le_T haD
  have haa : c.ρ a * c.ρ a = 1 := by
    rw [← PermRho.apply_mul haN haN, ← pow_two, ha2, PermRho.apply_one]
  obtain ⟨t, htTL, hnc⟩ := c.exists_noncomm haT has haa
  obtain ⟨htT, htL⟩ := Subgroup.mem_inf.mp htTL
  have htN : t ∈ Subgroup.normalizer (V : Set G) := c.T_le_N htT
  obtain ⟨u, hu, w, hw, huw⟩ := c.hk.kData.exists_mul_V0_V1_F4 c.h c.hZ c.hl.h6211 _
    (c.T_conj_D htT haD)
  have hwVg : w ∈ conjSubgroup V g := (Subgroup.mem_inf.mp hw).1
  have hwN : w ∈ Subgroup.normalizer (V : Set G) :=
    CHU_le_normalizer_V_F4 c.h c.hl.h6210 (Subgroup.mem_inf.mp hw).2
  have huV : u ∈ V := (Subgroup.mem_inf.mp hu).1
  have huQ : u ∈ Subgroup.centralizer (V : Set G) := V_le_centralizer_V c.h huV
  have huN : u ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ huQ
  have hρu : c.ρ u = 1 := (c.ρ.eq_one_iff huN).mpr huQ
  have hρw : c.ρ w = c.ρ t * c.ρ a * (c.ρ t)⁻¹ := by
    have h1 := congrArg c.ρ huw
    rw [PermRho.apply_conj htN haN, PermRho.apply_mul huN hwN, hρu, one_mul] at h1
    exact h1.symm
  have haVg : a ∈ conjSubgroup V g := (Subgroup.mem_inf.mp haV1).1
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
  have hyN : a * w ∈ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normalizer (V : Set G)).mul_mem haN hwN
  have hy2 : (a * w) ^ 2 = 1 := by
    have hcomm := c.Vg_comm haVg hwVg
    calc (a * w) ^ 2 = (a * w) * (a * w) := pow_two _
      _ = a * (w * a) * w := by group
      _ = a * (a * w) * w := by rw [hcomm]
      _ = a ^ 2 * w ^ 2 := by simp only [pow_two, mul_assoc]
      _ = 1 := by rw [ha2, c.Vg_sq hwVg, one_mul]
  refine ⟨a * w, ?_, (conjSubgroup V g).mul_mem haVg hwVg, hy2, ?_, ?_, ?_⟩
  ·
    have h1 : a * t * a⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (c.N_le_normalizer_L haN) t).mp htL
    have h2 : a * (t * a * t⁻¹) ∈ L := by
      have : a * (t * a * t⁻¹) = (a * t * a⁻¹) * t⁻¹ := by rw [ha1]; group
      rw [this]
      exact L.mul_mem h1 (L.inv_mem htL)
    have h3 : a * u * a⁻¹ ∈ L := c.V_le_L (conj_mem haN huV)
    have : a * w = (a * u * a⁻¹)⁻¹ * (a * (t * a * t⁻¹)) := by rw [huw]; group
    rw [this]
    exact L.mul_mem (L.inv_mem h3) h2
  · rw [← PermRho.apply_mul hyN hyN, ← pow_two, hy2, PermRho.apply_one]
  · intro h1
    rw [PermRho.apply_mul haN hwN, hρw] at h1
    apply hnc
    have h3 : c.ρ t * c.ρ a * (c.ρ t)⁻¹ = c.ρ a := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact inv_eq_of_mul_eq_one_right haa
    exact mul_inv_eq_iff_eq_mul.mp h3
  · rw [PermRho.apply_mul haN hwN, hρw, map_mul, map_mul, map_mul, map_inv, has]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (c.ρ t)) with h | h <;> simp [h]

end BCtx_F4

end CFSG.Quasithin.H13.GM22
