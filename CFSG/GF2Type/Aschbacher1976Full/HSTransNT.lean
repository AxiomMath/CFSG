module

public import CFSG.GF2Type.Aschbacher1976Full.HSTransNTConj
public import CFSG.GF2Type.Aschbacher1976Full.HSTransInterfaces

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem comm_Fz_of_isConj {z : G} (hset : HSSetting G z) {p : G} (hp : IsConj z p) {x y : G}
    (hx : x ∈ Fz p) (hy : y ∈ Fz p) : ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = p := by
  obtain ⟨g, rfl⟩ := Transport.exists_eq_of_isConj hp
  obtain ⟨⟨-, -, hz, -⟩, hZ4⟩ := hset
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  rw [Transport.Fz_eq, Width.mem_conjugate_iff] at hx hy
  have e : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  have e' : ⁅x, y⁆ = g⁻¹ * (g * ⁅x, y⁆ * g⁻¹) * g := by group
  rcases Width.comm_F hD hz hx hy with h | h
  · left
    rw [e] at h
    rw [e', h]
    group
  · right
    rw [e] at h
    rw [e', h]

theorem twoBasesStmt_holds : TwoBasesStmt := by
  intro G _ _ z hset hti p q a c hp hq hpq ha hc hap haq hcp hcq hapH haqH hcpH hcqH
  have hz : orderOf z = 2 := hset.1.2.2.1
  have hne1 : ∀ {r : G}, IsConj z r → r ≠ 1 := by
    intro r hr h1
    rw [h1] at hr
    rw [isConj_one_left.mp hr, orderOf_one] at hz
    omega
  have hmem : ∀ {r u : G}, IsConj z r → IsConj z u → u ≠ r → ZF u ≤ Hz r → u ∈ Fz r :=
    fun {r u} hr hu hne hle =>
      ((Transport.hsTI_of_isConj hti hr).2 u ⟨hr.symm.trans hu, hne, hle⟩).1
  have hP := comm_Fz_of_isConj hset hp (hmem hp ha hap hapH) (hmem hp hc hcp hcpH)
  have hQ := comm_Fz_of_isConj hset hq (hmem hq ha haq haqH) (hmem hq hc hcq hcqH)
  refine commutatorElement_eq_one_iff_mul_comm.mp ?_
  rcases hP with hP | hP
  · exact hP
  · rcases hQ with hQ | hQ
    · exact absurd (hP.symm.trans hQ) (hne1 hp)
    · exact absurd (hP.symm.trans hQ) hpq

end CFSG.GF2Type.Aschbacher1976Full.HS
