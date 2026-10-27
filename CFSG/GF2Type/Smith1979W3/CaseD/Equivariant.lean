module

public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.CaseD

open CFSG.LargeExtraspecial Subgroup

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem clSub_inf_Qa_mul (m : S.M) (g : G) :
    S.clSub (S.QG ⊓ S.Qa ((m : G) * g)) =
      (S.clSub (S.QG ⊓ S.Qa g)).map
        (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
  ext v
  rw [S.mem_clSub_iff, Submodule.mem_map]
  constructor
  · rintro ⟨x, ⟨hxQ, hxQa⟩, -, rfl⟩
    have hyQ : (m : G)⁻¹ * x * (m : G) ∈ S.QG := by
      simpa using S.conj_mem_QG (S.M.inv_mem m.2) hxQ
    have hyQa : (m : G)⁻¹ * x * (m : G) ∈ S.Qa g := S.mem_Qa_mul_iff.mp hxQa
    refine ⟨S.cl ((m : G)⁻¹ * x * (m : G)), S.cl_mem_clSub ⟨hyQ, hyQa⟩ hyQ, ?_⟩
    change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
        (S.cl ((m : G)⁻¹ * x * (m : G))) = S.cl x
    rw [S.ρ_cl m hyQ]
    congr 1
    group
  · rintro ⟨y, hy, hyv⟩
    obtain ⟨z, ⟨hzQ, hzQa⟩, -, hzy⟩ := S.mem_clSub_iff.mp hy
    rw [← hzy] at hyv
    have hxQ : (m : G) * z * (m : G)⁻¹ ∈ S.QG := by
      simpa using S.conj_mem_QG m.2 hzQ
    have hxQa : (m : G) * z * (m : G)⁻¹ ∈ S.Qa ((m : G) * g) := by
      rw [S.mem_Qa_mul_iff]
      have hz' : (m : G)⁻¹ * ((m : G) * z * (m : G)⁻¹) * (m : G) = z := by group
      rwa [hz']
    refine ⟨(m : G) * z * (m : G)⁻¹, ⟨hxQ, hxQa⟩, hxQ, ?_⟩
    rw [← S.ρ_cl m hzQ]
    exact hyv

theorem QG_inf_Qa_mul_eq_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (m : S.M)
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)) :
    S.QG ⊓ S.Qa ((m : G) * g) = S.QG ⊓ S.Qa g := by
  have hxM : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG := by
    have h := S.conj_mem_QG m.2 haQ
    rwa [show (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ =
      ((m : G) * g) * S.z * ((m : G) * g)⁻¹ by group] at h
  have hcl : S.cl (((m : G) * g) * S.z * ((m : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹) := by
    rw [← S.ρ_cl_conj_z (h := (m : G)) m.2 haQ]
    exact hm
  rcases (S.cl_eq_cl_iff hxM haQ).mp hcl with heq | heq
  · rw [S.Qa_eq_of_conj_eq heq.symm]
  · have hb : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ = (g * S.z * g⁻¹) * S.z := by
      rw [heq]
      simp only [mul_assoc, S.z_mul_z, mul_one]
    exact S.QG_inf_Qa_eq_of_conj_eq_mul_z haQ hne hb

theorem map_clSub_eq_of_fix {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (m : S.M)
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹)) :
    (S.clSub (S.QG ⊓ S.Qa g)).map
        (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      S.clSub (S.QG ⊓ S.Qa g) := by
  rw [← clSub_inf_Qa_mul S m g]
  exact congrArg S.clSub (QG_inf_Qa_mul_eq_of_fix S haQ hne m hm)

end CFSG.GF2Type.Smith1979W3.CaseD
