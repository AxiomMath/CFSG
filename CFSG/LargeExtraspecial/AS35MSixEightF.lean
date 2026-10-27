module

public import CFSG.LargeExtraspecial.AS35MSixEightE
public import CFSG.LargeExtraspecial.AS35HSixEightF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem sixEightTwoE (ih : S14.AschbacherBelow (Nat.card G)) (hS : S.SixHyp)
    (h65 : S.SixFiveConcl) (hT : S14.SixFiveTransvectionStmt)
    (h67 : S14.AschbacherSixSevenMbarStmt) (h59 : S14.AschbacherFiveNineOneStmt)
    (hU : S14.AschTwoAutStmt) {k d : G} (hd : d * S.z * d⁻¹ ∈ S.DSet)
    (hdk : d * S.z * d⁻¹ ∈ S.DAt k) (h3 : orderOf (S.z * (k * S.z * k⁻¹)) = 3) :
    closure S.DSet ≤ closure (S.DSet ∩ S.DAt k) ⊔ S.QG := by
  have hS4 := hS.sixFour
  obtain ⟨a, haeq⟩ : ∃ a : G, d⁻¹ * S.z * d⁻¹⁻¹ = a := ⟨_, rfl⟩
  obtain ⟨b, hbeq⟩ : ∃ b : G, d⁻¹ * k * S.z * (d⁻¹ * k)⁻¹ = b := ⟨_, rfl⟩
  have ha : a ∈ S.DSet := by
    rw [← haeq, inv_inv]
    exact S.mem_DAt.mp (S.z_mem_DAt hS4 hd rfl)
  have hb : b ∈ S.DSet := by
    have := S.mem_DAt.mp (S.mem_DAt_symm hS4 hdk)
    rwa [← hbeq, show d⁻¹ * k * S.z * (d⁻¹ * k)⁻¹ = d⁻¹ * (k * S.z * k⁻¹) * d by group]
  have haM := S.mem_M_of_mem_ESet hS4 ha.1
  have hbM := S.mem_M_of_mem_ESet hS4 hb.1
  have haa : a * a = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet ha.1)
  have hbb : b * b = 1 := S.mul_self_of_isConj (S.isConj_of_mem_ESet hb.1)
  have hab3 : orderOf (a * b) = 3 := by
    rw [← haeq, ← hbeq, show d⁻¹ * S.z * d⁻¹⁻¹ * (d⁻¹ * k * S.z * (d⁻¹ * k)⁻¹) =
      d⁻¹ * (S.z * (k * S.z * k⁻¹)) * d⁻¹⁻¹ by group, orderOf_conj_eq]
    exact h3
  have hinv : b * a = (a * b)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb]
  have hba3 : orderOf (b * a) = 3 := by
    rw [hinv, orderOf_inv]
    exact hab3
  obtain ⟨_, ⟨s, hs, hsM, rfl⟩, hsa, hsb⟩ := (hT G S hS h65).2 _ (S.ρ_mem_DbarAsc ha haM) _
    (S.ρ_mem_DbarAsc hb hbM) (S.orderOf_rho_mul_eq_three haM hbM hab3)
  have hρ3 := S.orderOf_rho_mul_eq_three haM hbM hab3
  have hρa := S.ρ_mul_self_eq_one haM haa
  have hρb := S.ρ_mul_self_eq_one hbM hbb
  have hsa' : S.ρ ⟨s, hsM⟩ ≠ S.ρ ⟨a, haM⟩ := by
    intro h
    rw [h] at hsb
    exact not_orderOf_eq_three_of_commute hρa hρb hsb hρ3
  have hsb' : S.ρ ⟨s, hsM⟩ ≠ S.ρ ⟨b, hbM⟩ := by
    intro h
    rw [h] at hsa
    exact not_orderOf_eq_three_of_commute hρa hρb hsa.symm hρ3
  obtain ⟨hE, hfixne, hcent, hO2, hbE, hbE', hwidth, hA2⟩ := S.sixSeven_dataE ih hS h65 h67
    ha hb hs haM hbM hsM hab3 hsa.symm (Ne.symm hsa') hsb.symm (Ne.symm hsb')
  obtain ⟨hE', hfixne', hcent', hO2', haE, haE', hwidth', hA2'⟩ := S.sixSeven_dataE ih hS h65
    h67 hb ha hs hbM haM hsM hba3 hsb.symm (Ne.symm hsb') hsa.symm (Ne.symm hsa')
  have hn4 := h65.four_le_width
  have hEeq : S.EOdd (b * a) = S.EOdd (a * b) := by rw [hinv, S.EOdd_inv]
  have hbX := S.commute_conj_z_of_sixEightE hS h65 h59 hU ha hb hbeq haM hbM hab3 hE hbE hbE'
    hfixne hcent hO2 (by omega) hA2
  have haX' := S.commute_conj_z_of_sixEightE hS h65 h59 hU hb ha haeq hbM haM hba3 hE' haE
    haE' hfixne' hcent' hO2' (by omega) hA2'
  have haX : ∀ c : Cx (S.EOdd (a * b) : Set G),
      a * ((c : G) * S.z * (c : G)⁻¹) = (c : G) * S.z * (c : G)⁻¹ * a := by
    intro c
    exact haX' ⟨c, by rw [hEeq]; exact c.2⟩
  have hXa : ∀ w ∈ S.XCxE hE, (w : G) * a = a * w := fun w hw =>
    S.XCxE_le_centralizer hE haX hw
  have hXb : ∀ w ∈ S.XCxE hE, (w : G) * b = b * w := fun w hw =>
    S.XCxE_le_centralizer hE hbX hw
  have hza : S.z ∈ S.DAt d⁻¹ := S.z_mem_DAt hS4 ha haeq
  have hzb : S.z ∈ S.DAt (d⁻¹ * k) := S.z_mem_DAt hS4 hb hbeq
  have hgen : ∀ c : Cx (S.EOdd (a * b) : Set G),
      d * ((c : G) * S.z * (c : G)⁻¹) * d⁻¹ ∈ S.DSet ∩ S.DAt k := by
    intro c
    obtain ⟨l, hlX, hl⟩ := S.exists_XCxE_conj_eq hU hE hab3 hfixne hcent hO2 (by omega) hA2 c
    have hl' : (c : G) * S.z * (c : G)⁻¹ = (l : G) * S.z * (l : G)⁻¹ := by
      have := congrArg (fun w : Cx (S.EOdd (a * b) : Set G) => (w : G)) hl
      simp only [coe_mul, coe_inv] at this
      exact this
    have hla : (l : G) * (d⁻¹ * S.z * d⁻¹⁻¹) = d⁻¹ * S.z * d⁻¹⁻¹ * l := by
      rw [haeq]
      exact hXa l hlX
    have hlb : (l : G) * (d⁻¹ * k * S.z * (d⁻¹ * k)⁻¹) = d⁻¹ * k * S.z * (d⁻¹ * k)⁻¹ * l := by
      rw [hbeq]
      exact hXb l hlX
    have h1 := S.conj_mem_DAt_mul (c := d) (S.conj_mem_DAt_of_commute hla hza)
    have h2 := S.conj_mem_DAt_mul (c := d) (S.conj_mem_DAt_of_commute hlb hzb)
    rw [mul_inv_cancel, DAt_one] at h1
    rw [show d * (d⁻¹ * k) = k by group] at h2
    rw [hl']
    exact ⟨h1, h2⟩
  have hYD : ∀ w ∈ S.XCxE hE, d * (w : G) * d⁻¹ ∈ closure (S.DSet ∩ S.DAt k) := by
    have hle : S.XCxE hE ≤ (closure (S.DSet ∩ S.DAt k)).comap
        ((MulAut.conj d).toMonoidHom.comp (Cx (S.EOdd (a * b) : Set G)).subtype) := by
      rw [XCxE, closure_le]
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, mem_comap]
      exact subset_closure (hgen c)
    intro w hw
    exact hle hw
  have hXa' : ∀ w ∈ S.XCxE hE, (w : G) * (d⁻¹ * S.z * d) = d⁻¹ * S.z * d * w := by
    intro w hw
    rw [show d⁻¹ * S.z * d = a by rw [← haeq, inv_inv]]
    exact hXa w hw
  rw [closure_le]
  intro e he
  obtain ⟨w, hwX, hwM, hρ⟩ := S.exists_rho_eq_of_sixEightTwoE hS h65 hU hE hab3 hfixne hcent hO2
    hwidth hA2 hXa' (fun w hw => closure_mono Set.inter_subset_left (hYD w hw)) hd he
  have heM := S.mem_M_of_mem_ESet hS4 he.1
  have hq : (d * (w : G) * d⁻¹)⁻¹ * e ∈ S.QG := by
    rw [← S.ρ_eq_one_iff ⟨(d * (w : G) * d⁻¹)⁻¹ * e, S.M.mul_mem (S.M.inv_mem hwM) heM⟩]
    change S.ρ ((⟨d * (w : G) * d⁻¹, hwM⟩ : S.M)⁻¹ * ⟨e, heM⟩) = 1
    rw [map_mul, map_inv, hρ, inv_mul_cancel]
  rw [SetLike.mem_coe, show e = d * (w : G) * d⁻¹ * ((d * (w : G) * d⁻¹)⁻¹ * e) by group]
  exact mul_mem_sup (hYD w hwX) hq

end Setting

namespace S14

theorem aschbacherSixEightTwoStmt_of' (hT : SixFiveTransvectionStmt)
    (h67 : AschbacherSixSevenMbarStmt) (h59 : AschbacherFiveNineOneStmt)
    (hU : AschTwoAutStmt) : AschbacherSixEightTwoStmt :=
  fun _ _ _ S ih hS h65 _ _ hd hdk h3 => S.sixEightTwoE ih hS h65 hT h67 h59 hU hd hdk h3

end S14

end CFSG.LargeExtraspecial
