module

public import CFSG.LargeExtraspecial.DWTransBNorm
public import CFSG.LargeExtraspecial.DWModelMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup CFSG.GroupTheory.GLnTwoSplitting
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem nonempty_centralizer_mulEquiv_of_not_mem (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G)) {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG)
    (hxA : h * S.z * h⁻¹ ∉ A) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) := by
  have := S.isElementaryAbelian_QG_inf_Qa (hA.conj_ne_z hxA)
  exact (hA.maxEA_inf hM hxQ hxA).nonempty_centralizer_mulEquiv_of_conj h5
    (hA.M_le_normalizer_inf hM hxQ hxA (by omega)) (hA.inf_le_closure hM hxQ hxA (by omega))
    fun g hg => hA.inf_le_Qa hM hxQ hxA (by omega) hg

theorem resAt_bijective_of_not_mem (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) :
    Function.Bijective (resAt S A hM) :=
  ⟨hA.resAt_injective hM, hA.resAt_surjective_of_mem hM hxQ hxA⟩

theorem nonempty_Mbar_mulEquiv_of_not_mem (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) :
    Nonempty (S.Mbar ≃* GL (Fin S.width) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_mulEquiv_GL hA.finrank_clSub
  exact ⟨(MulEquiv.ofBijective _ (hA.resAt_bijective_of_not_mem hM hxQ hxA)).trans e⟩

theorem nonempty_centralizer_mulEquiv_of_caseII (hA : MaxEA S A) (h5 : 5 ≤ S.width)
    (hM : S.M ≤ normalizer (A : Set G))
    (hII : (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) →
      (A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d}) ∧
        ∀ g : G, g * S.z * g⁻¹ ∈ A → A ≤ S.Qa g) :
    Nonempty (centralizer ({S.z} : Set G) ≃*
      centralizer ({cornerTransvection (N := S.width + 2) (by omega)} :
        Set (SL(S.width + 2, ZMod 2)))) := by
  by_cases hI : ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ∉ A
  · obtain ⟨h, hxQ, hxA⟩ := hI
    exact hA.nonempty_centralizer_mulEquiv_of_not_mem h5 hM hxQ hxA
  · push Not at hI
    obtain ⟨hi, hii⟩ := hII hI
    exact hA.nonempty_centralizer_mulEquiv_of_conj h5 hM hi hii

omit [IsElementaryAbelian 2 A] in
theorem conj_hyp_of_resAt_surjective (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    (hsurj : Function.Surjective (resAt S A hM)) {g : G} (hgA : g * S.z * g⁻¹ ∈ A)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hQa : A ≤ S.Qa g) :
    (A ≤ closure {d : G | d ∈ A ∧ ∃ g : G, g * S.z * g⁻¹ = d}) ∧
      ∀ g' : G, g' * S.z * g'⁻¹ ∈ A → A ≤ S.Qa g' := by
  have hdQ := hA.le_QG hgA
  have hd1 : g * S.z * g⁻¹ ≠ 1 := fun e => S.z_ne_one (by
    simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) e)
  have key : ∀ c ∈ A, c ≠ 1 → c ≠ S.z → ∃ n ∈ S.M, n * (g * S.z * g⁻¹) * n⁻¹ = c := by
    intro c hc hc1 hcz
    have hcQ := hA.le_QG hc
    have hc0 : (⟨S.cl c, S.cl_mem_clSub hc hcQ⟩ : S.clSub A) ≠ 0 := fun e => by
      rcases (S.cl_eq_zero_iff hcQ).mp (congrArg Subtype.val e) with h | h
      · exact hc1 h
      · exact hcz h
    have hd0 : (⟨S.cl (g * S.z * g⁻¹), S.cl_mem_clSub hgA hdQ⟩ : S.clSub A) ≠ 0 := fun e => by
      rcases (S.cl_eq_zero_iff hdQ).mp (congrArg Subtype.val e) with h | h
      · exact hd1 h
      · exact hne h
    obtain ⟨f, w, hfw, ht⟩ := exists_transvection_apply_eq hd0 hc0
    obtain ⟨y, hy⟩ := hsurj (LinearEquiv.transvection hfw)
    obtain ⟨m, hmy⟩ := y.2
    have hcl : S.cl (m * (g * S.z * g⁻¹) * (m : G)⁻¹) = S.cl c := by
      have h1 := congrArg Subtype.val (congrArg (fun e => e ⟨S.cl (g * S.z * g⁻¹),
        S.cl_mem_clSub hgA hdQ⟩) hy)
      simp only [coe_resAt_apply] at h1
      rw [ht] at h1
      rw [← S.ρ_cl m hdQ, hmy]
      exact h1
    rcases (S.cl_eq_cl_iff (S.conj_mem_QG m.2 hdQ) hcQ).mp hcl with e | e
    · exact ⟨m, m.2, e.symm⟩
    · obtain ⟨q, hq, hqc⟩ := S.exists_conj_eq_mul_z hcQ hc1 hcz
      refine ⟨q * m, S.M.mul_mem (S.QG_le_M hq) m.2, ?_⟩
      have hcz' : c * S.z * S.z = c := by rw [mul_assoc, S.z_mul_z, mul_one]
      have e' : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ = c * S.z := by
        rw [e, mul_assoc _ S.z S.z, S.z_mul_z, mul_one]
      calc q * m * (g * S.z * g⁻¹) * (q * m)⁻¹
          = q * (m * (g * S.z * g⁻¹) * (m : G)⁻¹) * q⁻¹ := by group
        _ = q * (c * S.z) * q⁻¹ := by rw [e']
        _ = q * c * q⁻¹ * (q * S.z * q⁻¹) := by group
        _ = c := by rw [hqc, show q * S.z * q⁻¹ = S.z by
              rw [S.z_comm (S.QG_le_M hq), mul_inv_cancel_right], hcz']
  refine ⟨fun b hb => ?_, fun g' hg' => ?_⟩
  · by_cases hb1 : b = 1
    · rw [hb1]
      exact one_mem _
    by_cases hbz : b = S.z
    · exact subset_closure ⟨hb, 1, by rw [hbz]; group⟩
    obtain ⟨n, -, hn⟩ := key b hb hb1 hbz
    exact subset_closure ⟨hb, n * g, by rw [← hn]; group⟩
  · by_cases hz' : g' * S.z * g'⁻¹ = S.z
    · rw [S.Qa_eq_of_conj_eq (g := g') (h := 1) (by rw [hz']; group), S.Qa_one]
      exact hA.le_QG
    have h1' : g' * S.z * g'⁻¹ ≠ 1 := fun e => S.z_ne_one (by
      simpa [mul_assoc] using congrArg (fun t => g'⁻¹ * t * g') e)
    obtain ⟨n, hn, hnd⟩ := key _ hg' h1' hz'
    rw [S.Qa_eq_of_conj_eq (g := g') (h := n * g) (by rw [← hnd]; group), Qa_mul_eq_map]
    intro b hb
    have := (mem_normalizer_iff.mp (hM (S.M.inv_mem hn)) b).mp hb
    exact ⟨n⁻¹ * b * n⁻¹⁻¹, hQa this, by simp [mul_assoc]⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
