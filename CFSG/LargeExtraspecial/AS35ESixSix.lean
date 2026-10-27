module

public import CFSG.LargeExtraspecial.AS35EFiveOne
public import CFSG.LargeExtraspecial.AS35EResid

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Asc77

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem ρ_mem_DbarAsc {t : G} (ht : t ∈ S.DSet) (htM : t ∈ S.M) : S.ρ ⟨t, htM⟩ ∈ S.DbarAsc :=
  ⟨t, ht, htM, rfl⟩

theorem pow_mem_QG_iff {s t : G} (hsM : s ∈ S.M) (htM : t ∈ S.M) (k : ℕ) :
    (s * t) ^ k ∈ S.QG ↔ (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩) ^ k = 1 := by
  rw [← map_mul, ← map_pow, S.ρ_eq_one_iff]
  simp

theorem commute_of_mem_closure_zConj (hS : S.SixFourConcl) {t h : G} (ht : t ∈ S.ESet)
    (hh : h * S.z * h⁻¹ = t) {x : G} (hx : x ∈ closure (S.zConj (S.HAt h))) : x * t = t * x := by
  have htH := S.mem_zConj_of_mem_ESet ht hh
  obtain ⟨⟨_, _, -, hcomm, -⟩, -⟩ := (hS _ (S.isHStar_of_mem_ESet ht hh).1).1
  have hle : closure (S.zConj (S.HAt h)) ≤ centralizer ({t} : Set G) := by
    rw [closure_le]
    intro p hp
    exact mem_centralizer_singleton_iff.mpr (hcomm t htH p hp).symm
  exact mem_centralizer_singleton_iff.mp (hle hx)

theorem commute_of_ρ_eq (hS : S.SixHyp) {s t : G} (hs : s ∈ S.DSet) (ht : t ∈ S.DSet)
    (hsM : s ∈ S.M) (htM : t ∈ S.M) (heq : S.ρ ⟨s, hsM⟩ = S.ρ ⟨t, htM⟩) : s * t = t * s := by
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hxQ : s * t ∈ S.QG := by
    rw [← pow_one (s * t), S.pow_mem_QG_iff hsM htM, pow_one, heq, ← map_mul]
    exact (S.ρ_eq_one_iff _).mpr (by simp [htt])
  have hcx : S.cl (s * t) ∈ commSpace (S.rhoL htM) := by
    refine S.cl_mem_commSpace_of_commute hS.sixFour hS.weak ht htM hxQ fun y hy => ?_
    obtain ⟨hyQ, hyc⟩ := S.mem_inf_centralizer_iff_conj.mp hy
    have h1 : S.cl (s * y * s⁻¹) = S.cl y := by
      rw [← S.rhoL_cl hsM hyQ]
      change ((S.ρ ⟨s, hsM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) = S.cl y
      rw [heq]
      change S.rhoL htM (S.cl y) = S.cl y
      rw [S.rhoL_cl htM hyQ, hyc]
    have h2 := S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak hs hsM hyQ h1
    calc y * (s * t) = s * t * (t⁻¹ * (s⁻¹ * y * s) * t) := by group
      _ = s * t * (t⁻¹ * y * t) := by
          rw [show s⁻¹ * y * s = y by
            calc s⁻¹ * y * s = s⁻¹ * (s * y * s⁻¹) * s := by rw [h2]
              _ = y := by group]
      _ = s * t * y := by
          rw [show t⁻¹ * y * t = y by
            calc t⁻¹ * y * t = t⁻¹ * (t * y * t⁻¹) * t := by rw [hyc]
              _ = y := by group]
  obtain ⟨h, hh, -⟩ := id ht.1
  have hxV := S.mem_closure_zConj_of_cl_mem_commSpace ht.1 hh htM hxQ hcx
  have hsV : s ∈ closure (S.zConj (S.HAt h)) := by
    have := mul_mem hxV (subset_closure (S.mem_zConj_of_mem_ESet ht.1 hh))
    rwa [mul_assoc, htt, mul_one] at this
  exact S.commute_of_mem_closure_zConj hS.sixFour ht.1 hh hsV

theorem ρ_mul_self_eq_one {s : G} (hsM : s ∈ S.M) (hss : s * s = 1) :
    S.ρ ⟨s, hsM⟩ * S.ρ ⟨s, hsM⟩ = 1 := by
  rw [← map_mul, S.ρ_eq_one_iff]
  change s * s ∈ S.QG
  rw [hss]
  exact one_mem _

theorem fiveThirteen (hS : S.SixHyp) (h65 : S.SixFiveConcl) {s t : G} (hs : s ∈ S.DSet)
    (ht : t ∈ S.DSet) (hsM : s ∈ S.M) (htM : t ∈ S.M)
    (hc : S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * S.ρ ⟨s, hsM⟩)
    (hne : S.ρ ⟨s, hsM⟩ ≠ S.ρ ⟨t, htM⟩) : s * t = t * s := by
  have hss := S.mul_self_of_isConj (S.isConj_of_mem_ESet hs.1)
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hσσ := S.ρ_mul_self_eq_one hsM hss
  have hττ := S.ρ_mul_self_eq_one htM htt
  have hcQ : (s * t) ^ 2 ∈ S.QG := by
    rw [S.pow_mem_QG_iff hsM htM]
    calc (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩) ^ 2 =
        S.ρ ⟨s, hsM⟩ * (S.ρ ⟨t, htM⟩ * S.ρ ⟨s, hsM⟩) * S.ρ ⟨t, htM⟩ := by
          rw [pow_two]; group
      _ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨s, hsM⟩ * (S.ρ ⟨t, htM⟩ * S.ρ ⟨t, htM⟩) := by rw [← hc]; group
      _ = 1 := by rw [hσσ, hττ, one_mul]
  have hct : (s * t) ^ 2 * t = s * t * s⁻¹ := by
    rw [pow_two, hsinv]
    calc s * t * (s * t) * t = s * t * s * (t * t) := by group
      _ = s * t * s := by rw [htt, mul_one]
  have hctD : (s * t) ^ 2 * t ∈ S.DSet := hct ▸ S.conj_mem_DSet hsM ht
  have h1 := S.cl_mem_commSpace_of_mul_mem hS.sixFour hS.weak ht htM hcQ hctD
  have hcs : ((s * t) ^ 2)⁻¹ * s = t * s * t⁻¹ := by
    rw [pow_two, htinv]
    calc (s * t * (s * t))⁻¹ * s = t⁻¹ * s⁻¹ * t⁻¹ * (s⁻¹ * s) := by group
      _ = t * s * t := by rw [inv_mul_cancel, mul_one, hsinv, htinv]
  have hcsD : ((s * t) ^ 2)⁻¹ * s ∈ S.DSet := hcs ▸ S.conj_mem_DSet htM hs
  have h2 := S.cl_mem_commSpace_of_mul_mem hS.sixFour hS.weak hs hsM (S.QG.inv_mem hcQ) hcsD
  rw [S.cl_inv hcQ] at h2
  have hbot := h65.disjoint _ (S.ρ_mem_DbarAsc hs hsM) _ (S.ρ_mem_DbarAsc ht htM) hc hne
  have h3 : S.cl ((s * t) ^ 2) ∈ commSpace ((S.ρ ⟨s, hsM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      commSpace ((S.ρ ⟨t, htM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := Submodule.mem_inf.mpr ⟨h2, h1⟩
  rw [hbot, Submodule.mem_bot] at h3
  rcases (S.cl_eq_zero_iff hcQ).mp h3 with h5 | h5
  · have h6 : s * t * (s * t) = 1 := by rw [← pow_two]; exact h5
    calc s * t = (s * t)⁻¹ := eq_inv_of_mul_eq_one_left h6
      _ = t * s := by rw [mul_inv_rev, hsinv, htinv]
  · exfalso
    apply ht.2
    have := S.isConj_of_mem_ESet hctD.1
    rwa [h5] at this

theorem fiveSix (hS : S.SixHyp) {s t : G} (hs : s ∈ S.DSet) (ht : t ∈ S.DSet) (hsM : s ∈ S.M)
    (htM : t ∈ S.M) (h3 : orderOf (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩) = 3) : orderOf (s * t) = 3 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hss := S.mul_self_of_isConj (S.isConj_of_mem_ESet hs.1)
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hxQ : (s * t) ^ 3 ∈ S.QG := (S.pow_mem_QG_iff hsM htM 3).mpr (h3 ▸ pow_orderOf_eq_one _)
  have hxt : (s * t) ^ 3 * t = (s * t) * s * (s * t)⁻¹ := by
    rw [mul_inv_rev, hsinv, htinv]
    calc (s * t) ^ 3 * t = s * t * s * t * s * (t * t) := by rw [pow_three]; group
      _ = s * t * s * (t * s) := by rw [htt, mul_one]; group
  have hxtD : (s * t) ^ 3 * t ∈ S.DSet := hxt ▸ S.conj_mem_DSet (mul_mem hsM htM) hs
  have h1 := S.cl_mem_commSpace_of_mul_mem hS.sixFour hS.weak ht htM hxQ hxtD
  have hxs : ((s * t) ^ 3)⁻¹ * s = (t * s) * t * (t * s)⁻¹ := by
    rw [mul_inv_rev, hsinv, htinv]
    calc ((s * t) ^ 3)⁻¹ * s = t⁻¹ * s⁻¹ * t⁻¹ * s⁻¹ * t⁻¹ * (s⁻¹ * s) := by
          rw [pow_three]; group
      _ = t * s * t * (s * t) := by rw [inv_mul_cancel, mul_one, hsinv, htinv]; group
  have hxsD : ((s * t) ^ 3)⁻¹ * s ∈ S.DSet := hxs ▸ S.conj_mem_DSet (mul_mem htM hsM) ht
  have h2 := S.cl_mem_commSpace_of_mul_mem hS.sixFour hS.weak hs hsM (S.QG.inv_mem hxQ) hxsD
  rw [S.cl_inv hxQ] at h2
  have hA1 := (S.fiveOne_two hS.sixFour hS.weak hs hsM).1
  have hA2 := (S.fiveOne_two hS.sixFour hS.weak ht htM).1
  have h3' : orderOf (S.rhoL hsM * S.rhoL htM) = 3 := by
    rw [← h3, ← Subgroup.orderOf_coe]
    rfl
  have hbot := (commSpace_mul_of_orderOf_eq_three S.q_nondegenerate hA1 hA2 h3').1
  have h4 : S.cl ((s * t) ^ 3) ∈ commSpace (S.rhoL hsM) ⊓ commSpace (S.rhoL htM) :=
    Submodule.mem_inf.mpr ⟨h2, h1⟩
  rw [hbot, Submodule.mem_bot] at h4
  rcases (S.cl_eq_zero_iff hxQ).mp h4 with h5 | h5
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime h5 fun h6 => ?_
    have h7 : S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ = 1 := by
      rw [← pow_one (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩), ← S.pow_mem_QG_iff hsM htM, pow_one, h6]
      exact one_mem _
    rw [h7, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  · exfalso
    apply ht.2
    have := S.isConj_of_mem_ESet hxtD.1
    rwa [h5] at this

theorem sixSix (hS : S.SixHyp) (h65 : S.SixFiveConcl) {s t : G} (hs : s ∈ S.DSet)
    (ht : t ∈ S.DSet) : orderOf (s * t) ∈ ({1, 2, 3} : Set ℕ) := by
  have hsM := S.mem_M_of_mem_ESet hS.sixFour hs.1
  have htM := S.mem_M_of_mem_ESet hS.sixFour ht.1
  have hss := S.mul_self_of_isConj (S.isConj_of_mem_ESet hs.1)
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have hσσ := S.ρ_mul_self_eq_one hsM hss
  have hττ := S.ρ_mul_self_eq_one htM htt
  have hcomm : s * t = t * s → orderOf (s * t) ∈ ({1, 2, 3} : Set ℕ) := by
    intro hc
    have h2 : (s * t) ^ 2 = 1 := by
      calc (s * t) ^ 2 = s * (t * s) * t := by rw [pow_two]; group
        _ = (s * s) * (t * t) := by rw [← hc]; group
        _ = 1 := by rw [hss, htt, one_mul]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · rw [h]
      simp
    · rw [h]
      simp
  rcases h65.three _ (S.ρ_mem_DbarAsc hs hsM) _ (S.ρ_mem_DbarAsc ht htM) with h1 | h2 | h3
  · apply hcomm
    have hστ : S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ = 1 := orderOf_eq_one_iff.mp h1
    refine S.commute_of_ρ_eq hS hs ht hsM htM ?_
    calc S.ρ ⟨s, hsM⟩ = S.ρ ⟨s, hsM⟩ * (S.ρ ⟨t, htM⟩ * S.ρ ⟨t, htM⟩) := by rw [hττ, mul_one]
      _ = S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ * S.ρ ⟨t, htM⟩ := by group
      _ = S.ρ ⟨t, htM⟩ := by rw [hστ, one_mul]
  · apply hcomm
    have hpow : (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩)
      rwa [h2] at this
    have hσinv : (S.ρ ⟨s, hsM⟩)⁻¹ = S.ρ ⟨s, hsM⟩ := inv_eq_of_mul_eq_one_right hσσ
    have hτinv : (S.ρ ⟨t, htM⟩)⁻¹ = S.ρ ⟨t, htM⟩ := inv_eq_of_mul_eq_one_right hττ
    have hc : S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ = S.ρ ⟨t, htM⟩ * S.ρ ⟨s, hsM⟩ := by
      have h6 : S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ * (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩) = 1 := by
        rw [← pow_two]
        exact hpow
      calc S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩ = (S.ρ ⟨s, hsM⟩ * S.ρ ⟨t, htM⟩)⁻¹ :=
            eq_inv_of_mul_eq_one_left h6
        _ = S.ρ ⟨t, htM⟩ * S.ρ ⟨s, hsM⟩ := by rw [mul_inv_rev, hσinv, hτinv]
    have hne : S.ρ ⟨s, hsM⟩ ≠ S.ρ ⟨t, htM⟩ := by
      intro h
      rw [h, hττ, orderOf_one] at h2
      exact absurd h2 (by norm_num)
    exact S.fiveThirteen hS h65 hs ht hsM htM hc hne
  · rw [S.fiveSix hS hs ht hsM htM h3]
    simp

end Setting

namespace S14

theorem aschbacherSixSixStmt :
    ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.SixFiveConcl →
      ∀ s ∈ S.DSet, ∀ t ∈ S.DSet, orderOf (s * t) ∈ ({1, 2, 3} : Set ℕ) :=
  fun _ _ _ S hS h65 _ hs _ ht => S.sixSix hS h65 hs ht

end S14

end CFSG.LargeExtraspecial
