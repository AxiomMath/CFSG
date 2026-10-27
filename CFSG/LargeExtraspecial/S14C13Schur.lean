module

public import CFSG.LargeExtraspecial.S14C13Data
public import CFSG.LargeExtraspecial.S14C13Conj
public import CFSG.LargeExtraspecial.S2Six

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_Nbar_of_cLin_eq_smul {t : S.O} [NQHyp S g t] (h7 : Concl14_7 S g t) {z : S.O}
    (hz : z ∈ Ct S t) (hne : ∃ n ∈ Nbar S g t, n ∉ zpowers t) {c : ZMod 2}
    (hc : cLin (g := g) hz = c • LinearMap.id) : z ∈ Nbar S g t := by
  have hc1 : c = 1 := by
    rcases OrthoF2.zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exfalso
      obtain ⟨n, hn, hnt⟩ := hne
      have h1 := LinearMap.congr_fun hc (nqMk ⟨n, hn⟩)
      rw [zero_smul, LinearMap.zero_apply, cLin_mk, nqMk_eq_zero_iff, coe_cConj] at h1
      exact hnt ((conj_mem_zpowers_iff
        (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hz).2)).mp h1)
    · rfl
  subst hc1
  refine h7.1 z (Subgroup.mem_inf.mp hz).1 fun n hn => ?_
  have h1 := LinearMap.congr_fun hc (nqMk ⟨n, hn⟩)
  rw [one_smul, LinearMap.id_apply, cLin_mk, nqMk_eq_iff, coe_cConj] at h1
  have hnt : n * t = t * n :=
    commute_of_mem_Rbar (NQHyp.conj_mem (S := S) (g := g) (t := t)) (Nbar_le_Rbar hn)
  have h2 := (conj_mem_zpowers_iff hnt).mpr (inv_mem h1)
  rwa [show n * ((z * n * z⁻¹)⁻¹ * n)⁻¹ * n⁻¹ = z * n * z⁻¹ * n⁻¹ by group] at h2

theorem exists_mem_Nbar_not_mem_zpowers {t : S.O} (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (htN : t ∈ Nbar S g t) (ht1 : t ≠ 1) (htc : ∀ y ∈ Nbar S g t, t * y = y * t) :
    ∃ n ∈ Nbar S g t, n ∉ zpowers t := by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN ht1 htc
  by_contra hcon
  push Not at hcon
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hcon a ha)
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp (hcon b hb)
  apply ht1
  rw [← hab, (Commute.zpow_zpow_self t i j).eq]
  group

theorem mem_Nbar_of_comm_Rbar (hCE : CentralExtInput.{0}) {t : S.O} {c : Config}
    (hSt : Stage S g t) (hocc : c.Occurs S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (hc : c = .sp6 ∨ c = .omegaPlus8a ∨ c = .omegaPlus12) (h7 : Concl14_7 S g t)
    {z : S.O} (hz : z ∈ Ct S t) (hzR : ∀ r ∈ Rbar S g t, z * r * z⁻¹ * r⁻¹ ∈ Nbar S g t) :
    z ∈ Nbar S g t := by
  have : NQHyp S g t := nqHyp_of_occurs hCE hSt hocc
  have haQ := hSt.hyp4.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ hSt.mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have hne := exists_mem_Nbar_not_mem_zpowers hext htN hSt.ne_one fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  have hΩc : ∀ m : ℕ, 2 ≤ m → RNOmega S g t (2 * m) →
      finrank (ZMod 2) (NQ S g t) = 2 ^ (m - 1) → z ∈ Nbar S g t := by
    intro m hm hΩ' hdimM
    obtain ⟨Q, hQ, hX, p, p₁, hdimV, hp0, hp, hp₁, hpp, -, hcomp⟩ :=
      omega_data hCE hSt hocc hΩ'
    obtain ⟨c, hc⟩ := S2.timmesfeld_2_6_1_omegaGroup (nqRep S g t hX) hm hdimV hp0 hp hp₁ hpp
      hcomp hdimM (φ := cLin hz) (fun e v => cLin_comm_nqRep hz hzR hX e v)
    exact mem_Nbar_of_cLin_eq_smul h7 hz hne hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨H, C, ht, ht1, hVQ, hSp, p₁, hdimV, hβ, hcomp⟩ := sp_data hCE hSt hocc hocc.1
    have hdimM : finrank (ZMod 2) (NQ S g t) = 2 ^ 3 :=
      finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 8) hocc.2.2
    obtain ⟨c, hc⟩ := S2.timmesfeld_2_6_1_spGroup (nqRep S g t hSp.eq_sp)
      (beta_isAlt H C ht ht1 hVQ) (beta_nondegenerate H C ht ht1 hVQ) (m := 3) (by norm_num)
      (by rw [hdimV]) hβ hcomp hdimM (φ := cLin hz)
      (fun e v => cLin_comm_nqRep hz hzR hSp.eq_sp e v)
    exact mem_Nbar_of_cLin_eq_smul h7 hz hne hc
  · exact hΩc 4 (by norm_num) hocc.1.1
      (finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 8) hocc.2.2)
  · exact hΩc 6 (by norm_num) hocc.1.1
      (finrank_NQ_eq_of_card hSt.ne_one htt htN (e := 32) hocc.2.2)

end CFSG.LargeExtraspecial.S14
