module

public import CFSG.GH74.GLS.C3.Layer1.Thm1GlueAut
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma118

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.GH74.GLS.IVK.Proofs2

section Classification

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K]

private theorem exists_eps_of_l2Field' (hF : L2Field F) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F : ℤ) ≡ ε [ZMOD 4] := by
  obtain ⟨t, ht⟩ := hF.1
  by_cases h : t % 2 = 0
  · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
  · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩

theorem solvable_fixedSubgroup_of_mem_innDiag (hF : L2Field F) (e : K ≃* L2 F) {y : MulAut K}
    (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hyD : y ∈ innDiagSub e) :
    Group.IsSolvable ↥(CFSG.GH74.GLS.fixedSubgroup K y) := by
  have hinj := conj_injective_of_L2 e
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨ε, hε1, hε⟩ := exists_eps_of_l2Field' hF
  by_cases hyInn : y ∈ innAut K
  · obtain ⟨u, rfl⟩ := hyInn
    have hu2 : u ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hy2, map_one]
    have hu1 : u ≠ 1 := fun h => hy1 (by rw [h, map_one])
    have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F - ε :=
      ⟨(Nat.card F - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
    have hdih := (ivk_1_3a F hF K e ε hε1 hε d hd u hu).2.1
    rw [Lemma118.fixedSubgroup_conj]
    exact CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_isDihedralOrder hdih
  · obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F + ε :=
      ⟨(Nat.card F + ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
    have hdih := (ivk_1_3b F hF K e ε hε1 hε d hd y hyD hyInn hyo).2.1
    exact CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_isDihedralOrder hdih

theorem exists_fieldAut_of_not_mem_innDiag (hF : L2Field F) (e : K ≃* L2 F) {ρ : MulAut K}
    (hdiag : ρ ∉ innDiagSub e) (hρ2 : ρ ^ 2 = 1) : ∃ e' : K ≃* L2 F, ρ ∈ fieldAutSub e' := by
  have : (innDiagSub e).Normal := innDiagSub_normal e
  have htop := innDiagSub_sup_fieldAutSub e
  have hρtop : ρ ∈ innDiagSub e ⊔ fieldAutSub e := htop ▸ Subgroup.mem_top ρ
  obtain ⟨d, hd, g, hg, hdg⟩ := Subgroup.mem_sup_of_normal_left.1 hρtop
  have hg1 : g ≠ 1 := by
    intro h1
    apply hdiag
    rw [← hdg, h1, mul_one]
    exact hd
  have hρ1 : ρ ≠ 1 := fun h => hdiag (h ▸ Subgroup.one_mem _)
  have hg2' : g ^ 2 = 1 := by
    have hmem : g ^ 2 ∈ innDiagSub e := by
      have h1 : (d * (g * d * g⁻¹)) * g ^ 2 = 1 := by
        have : ρ ^ 2 = d * (g * d * g⁻¹) * g ^ 2 := by
          rw [← hdg]; simp only [sq]; group
        rw [← this, hρ2]
      have h2 : g ^ 2 = (d * (g * d * g⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hd (Subgroup.Normal.conj_mem this d hd g))
    have hmem2 : g ^ 2 ∈ fieldAutSub e := Subgroup.pow_mem _ hg 2
    have : g ^ 2 ∈ innDiagSub e ⊓ fieldAutSub e := ⟨hmem, hmem2⟩
    rwa [innDiagSub_inf_fieldAutSub e, Subgroup.mem_bot] at this
  have hg2 : orderOf g = 2 := orderOf_eq_prime hg2' hg1
  obtain ⟨N⟩ := exists_notation hF e
  have hgT : g ∈ (N.T : Subgroup (MulAut K)) := by
    have hzp : IsPGroup 2 ↥(zpowers g) :=
      Thm1.isPGroup_zpowers_of_pow_eq_one ⟨1, by simpa using hg2'⟩
    have hle : zpowers g ≤ normalizer ((N.T : Subgroup (MulAut K)) : Set (MulAut K)) :=
      (zpowers_le.2 (N.T_inv hg))
    exact Thm1.le_sylow_of_le_normalizer N.T hzp hle (mem_zpowers g)
  have hgR : g ∈ (N.T : Subgroup (MulAut K)) ⊓ fieldAutSub e := ⟨hgT, hg⟩
  have hdg2 : orderOf (d * g) = 2 := by rw [hdg]; exact orderOf_eq_prime hρ2 hρ1
  obtain ⟨a, -, hconj⟩ := ivk_1_2h_c F hF K e N g hgR hg2 d hd hdg2
  have hmem : a⁻¹⁻¹ * ρ * a⁻¹ ∈ fieldAutSub e := by
    rw [← hdg, inv_inv, hconj]
    exact hg
  exact ⟨twistEquiv e a⁻¹⁻¹, (mem_fieldAutSub_twist_iff e a⁻¹ ρ).2 hmem⟩

theorem exists_fieldAut_of_not_solvable_fixed (hF : L2Field F) (e : K ≃* L2 F) {y : MulAut K}
    (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hns : ¬ Group.IsSolvable ↥(CFSG.GH74.GLS.fixedSubgroup K y)) :
    ∃ e' : K ≃* L2 F, y ∈ fieldAutSub e' := by
  by_cases hD : y ∈ innDiagSub e
  · exact absurd (solvable_fixedSubgroup_of_mem_innDiag hF e hy2 hy1 hD) hns
  · exact exists_fieldAut_of_not_mem_innDiag hF e hD hy2

end Classification

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R
