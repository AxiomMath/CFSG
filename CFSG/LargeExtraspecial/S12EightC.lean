module

public import CFSG.LargeExtraspecial.S12Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem s12_Lbar_fix_inf {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hbQ : g' * S.z * g'⁻¹ ∈ S.QG)
    (hab : S.cl (g * S.z * g⁻¹) ≠ S.cl (g' * S.z * g'⁻¹)) {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g)
    (hℓ' : ℓ ∈ S.Lbar g') {w : G} (hw : w ∈ S.QG ⊓ S.Qa g ⊓ S.Qa g') :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) = S.cl w := by
  obtain ⟨⟨hwQ, hwa⟩, hwb⟩ := hw
  have ha0 := S.s12_cl_ne_zero_of_conj haQ hne
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp hℓ
  obtain ⟨y', hy', hyy'⟩ := S.s12_mem_Lbar.mp hℓ'
  have he : S.cl (y * w * y⁻¹) = S.cl (y' * w * y'⁻¹) := by
    have e1 := S.ρ_cl ⟨y, S.L0_le_M g hy⟩ hwQ
    have e2 := S.ρ_cl ⟨y', S.L0_le_M g' hy'⟩ hwQ
    rw [hyy'] at e2
    exact e1.symm.trans e2
  rw [S.ρ_cl _ hwQ]
  change S.cl (y * w * y⁻¹) = S.cl w
  rcases S.s12_conj_L0_eq_or hy hwa with h1 | h1
  · rw [h1]
  · exfalso
    rw [h1, S.cl_mul haQ hwQ] at he
    rcases S.s12_conj_L0_eq_or hy' hwb with h2 | h2
    · rw [h2] at he
      exact ha0 (by simpa using he)
    · rw [h2, S.cl_mul hbQ hwQ] at he
      exact hab (add_right_cancel he)

theorem s12_Lbar_apply_sub_mem_inf {g g' : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {ℓ : S.O} (hℓ : ℓ ∈ S.Lbar g) (hℓ' : ℓ ∈ S.Lbar g') {x : G}
    (hxQ : x ∈ S.QG) (hxa : x * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * x)
    (hxb : x * (g' * S.z * g'⁻¹) = (g' * S.z * g'⁻¹) * x) :
    (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) - S.cl x ∈ S.clSub (S.QG ⊓ S.Qa g ⊓ S.Qa g') := by
  obtain ⟨y, hy, rfl⟩ := S.s12_mem_Lbar.mp hℓ
  obtain ⟨y', hy', hyy'⟩ := S.s12_mem_Lbar.mp hℓ'
  have hc := S.s12_commutator_L0_mem hxQ hxa hy
  have hc' := S.s12_commutator_L0_mem hxQ hxb hy'
  have he : S.cl (y * x * y⁻¹ * x⁻¹) = S.cl (y' * x * y'⁻¹ * x⁻¹) := by
    rw [S.cl_commutator (S.L0_le_M g hy) hxQ, S.cl_commutator (S.L0_le_M g' hy') hxQ, hyy']
  have hc'a : y' * x * y'⁻¹ * x⁻¹ ∈ S.Qa g := by
    rcases (S.cl_eq_cl_iff hc.1 hc'.1).mp he with h | h
    · rw [h]
      exact hc.2
    · rw [h]
      exact (S.Qa g).mul_mem hc.2 (S.z_mem_Qa_of_mem_QG rfl haQ hne)
  rw [← S.cl_commutator (S.L0_le_M g hy) hxQ, he]
  exact S.cl_mem_clSub ⟨⟨hc'.1, hc'a⟩, hc'.2⟩ hc'.1

theorem s12_polar_clSub_QG_inf_Qa {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) {v w : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) (hw : w ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    polar S.q v w = 0 := by
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  obtain ⟨y, hyX, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw
  exact (S.polar_cl_eq_zero_iff hxQ hyQ).mpr (S.QG_inf_Qa_comm hne hxX hyX)

theorem s12_q_clSub_QG_inf_Qa {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) : S.q v = 0 := by
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  exact (S.q_cl_eq_zero_iff hxQ).mpr (S.QG_inf_Qa_sq hne hxX)

omit [Finite G] in
theorem s12_cl_a_mem_clSub {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    S.cl (g * S.z * g⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g) :=
  S.cl_mem_clSub ⟨haQ, (S.conjBy g).z_mem_QG⟩ haQ

end Setting

end CFSG.LargeExtraspecial
