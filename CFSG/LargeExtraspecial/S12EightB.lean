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

theorem s12_rho_mem_clSub {g : G} (h : S.M) {v : S.Qt} (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    ((S.ρ h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub (S.QG ⊓ S.Qa ((h : G) * g)) := by
  obtain ⟨x, hxX, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl h hxQ]
  refine S.cl_mem_clSub ⟨S.conj_mem_QG h.2 hxQ, ?_⟩ (S.conj_mem_QG h.2 hxQ)
  rw [S.s12_Qa_mul]
  exact ⟨x, hxX.2, rfl⟩

theorem s12_Qa_conjBy_eq (g h : G) : (S.conjBy g).Qa h = S.Qa (h * g) :=
  QG_eq_of_z_eq _ _ (by simp only [conjBy_z]; group)

theorem s12_mem_Qa_symm {g : G} (h : G) (hb : (h * g) * S.z * (h * g)⁻¹ ∈ S.Qa g)
    (hab : (h * g) * S.z * (h * g)⁻¹ ≠ g * S.z * g⁻¹) :
    g * S.z * g⁻¹ ∈ S.Qa (h * g) := by
  have e : h * (S.conjBy g).z * h⁻¹ = (h * g) * S.z * (h * g)⁻¹ := by
    simp only [conjBy_z]; group
  have := (S.conjBy g).z_mem_Qa_of_mem_QG e hb hab
  rw [s12_Qa_conjBy_eq] at this
  exact this

theorem s12_card_QG_inf_Qa {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.QG ⊓ S.Qa g : Subgroup G) =
      2 ^ (finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) + 1) := by
  have hz : S.z ∈ S.QG ⊓ S.Qa g := ⟨S.z_mem_QG, S.z_mem_Qa_of_mem_QG rfl haQ hne⟩
  have h1 := S.card_clPre (S.clSub (S.QG ⊓ S.Qa g))
  rw [S.clPre_clSub inf_le_left hz, S.card_submodule] at h1
  rw [h1, pow_succ]
  ring

theorem s12_finrank_clSub_le {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) ≤ S.width := by
  have h := S.card_QG_inf_Qa_le hne
  rw [S.s12_card_QG_inf_Qa haQ hne] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  omega

theorem s12_mem_of_centralizes {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hdim : finrank (ZMod 2) (S.clSub (S.QG ⊓ S.Qa g)) = S.width)
    {y : G} (hy : y ∈ S.Qa g) (hyc : ∀ x ∈ S.QG ⊓ S.Qa g, y * x = x * y) :
    y ∈ S.QG ⊓ S.Qa g := by
  set T := S.conjBy g
  set A := S.QG ⊓ S.Qa g
  have hAT : A ≤ T.QG := inf_le_right
  have haA : T.z ∈ A := ⟨haQ, T.z_mem_QG⟩
  have hcardA : Nat.card A = 2 ^ (S.width + 1) := by
    rw [S.s12_card_QG_inf_Qa haQ hne, hdim]
  have hcardT := T.card_clPre (T.clSub A)
  rw [T.clPre_clSub hAT haA, T.card_submodule, hcardA] at hcardT
  have hdimT : finrank (ZMod 2) (T.clSub A) = T.width := by
    rw [S.width_conjBy]
    have := Nat.pow_right_injective le_rfl (show 2 ^ (S.width + 1) =
      2 ^ (finrank (ZMod 2) (T.clSub A) + 1) by rw [hcardT, pow_succ]; ring)
    omega
  have hiso : T.clSub A ≤ LinearMap.BilinForm.orthogonal T.q.polarBilin (T.clSub A) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨x, hxA, hxQ, rfl⟩ := T.mem_clSub_iff.mp hv
    obtain ⟨x', hx'A, hx'Q, rfl⟩ := T.mem_clSub_iff.mp hw
    change polar T.q (T.cl x') (T.cl x) = 0
    rw [T.polar_cl_eq_zero_iff hx'Q hxQ]
    exact S.QG_inf_Qa_comm hne hx'A hxA
  have horth : LinearMap.BilinForm.orthogonal T.q.polarBilin (T.clSub A) = T.clSub A := by
    refine (Submodule.eq_of_le_of_finrank_eq hiso ?_).symm
    rw [LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate, hdimT,
      T.finrank_Qt_eq_two_mul_width]
    omega
  have hmem : y ∈ T.QG ⊓ centralizer (A : Set G) :=
    ⟨hy, mem_centralizer_iff.mpr fun x hx => (hyc x hx).symm⟩
  rw [T.centralizer_inf_QG_eq_clPre hAT, horth, T.clPre_clSub hAT haA] at hmem
  exact hmem

end Setting

end CFSG.LargeExtraspecial
