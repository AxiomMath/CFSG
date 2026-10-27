module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem m11_two_A_of_fusion1 (hI : TwoHSInterface) (hM : M11Facts) {G : Type} [Group G]
    {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) :
    ∀ M : Subgroup G, M ≤ Gx a → IsSporadic ↥M .M11 → ∀ t ∈ M, t ^ 2 = 1 → t ≠ 1 →
      IsConj a t := by
  intro M hMle hM11 t htM ht2 ht1
  by_contra hnot
  have hF1self : Fusion1Facts a z := hF1.self
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hnot_a_mem : a ∉ M := by
    intro haM
    have hcomm : ∀ s : ↥M, s * (⟨a, haM⟩ : ↥M) = (⟨a, haM⟩ : ↥M) * s := by
      intro s
      apply Subtype.ext
      show (s : G) * a = a * (s : G)
      exact (mem_Gx.mp (hMle s.2)).symm
    have h1 := hM.center_trivial ↥M hM11 (⟨a, haM⟩ : ↥M) hcomm
    have ha1 : a = 1 := congrArg Subtype.val h1
    have h2 := h.orderOf_a
    rw [ha1, orderOf_one] at h2
    norm_num at h2
  have hMder : M ≤ derivedOf (Gx a) :=
    le_derivedOf_of_commutator_eq_top hMle (hM.perfect ↥M hM11)
  have typeB : ∀ s : G, s ∈ M → s ^ 2 = 1 → s ≠ 1 →
      IsConj z s ∧ IsConj a (a * s) ∧ a ∈ Qz s := by
    intro s hsM hs2 hs1
    have hs_conj_t : IsConj s t := by
      have hs2' : (⟨s, hsM⟩ : ↥M) ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hs2
      have ht2' : (⟨t, htM⟩ : ↥M) ^ 2 = 1 := by
        apply Subtype.ext
        simpa using ht2
      have hs1' : (⟨s, hsM⟩ : ↥M) ≠ 1 := by
        intro h1; exact hs1 (by simpa using congrArg Subtype.val h1)
      have ht1' : (⟨t, htM⟩ : ↥M) ≠ 1 := by
        intro h1; exact ht1 (by simpa using congrArg Subtype.val h1)
      exact MonoidHom.map_isConj M.subtype
        (hM.one_class ↥M hM11 ⟨s, hsM⟩ ⟨t, htM⟩ hs2' ht2' hs1' ht1')
    have hnot_as : ¬ IsConj a s := fun has => hnot (has.trans hs_conj_t)
    have hs_ord : orderOf s = 2 := orderOf_eq_prime hs2 hs1
    rcases inv_mem_derivedOf_cases hI h hF1self (hMder hsM) hs_ord with hsa | htypeB | htypeA
    · exact absurd (by rwa [hsa] at hsM) hnot_a_mem
    · exact htypeB
    · exact absurd htypeA.1 hnot_as
  let zM : ↥M := ⟨t, htM⟩
  have hzM2 : zM ^ 2 = 1 := by
    apply Subtype.ext
    simpa [zM] using ht2
  have hzM1 : zM ≠ 1 := by
    intro h1; exact ht1 (by simpa [zM] using congrArg Subtype.val h1)
  let C : Subgroup ↥M := Subgroup.centralizer ({zM} : Set ↥M)
  have hC : ↥C ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
    (hM.centralizer_GL23 ↥M hM11 zM hzM2 hzM1).some
  have htB : IsConj z t ∧ IsConj a (a * t) ∧ a ∈ Qz t := typeB t htM ht2 ht1
  have hcomm_at : a * t = t * a := mem_Gx.mp (hMle htM)
  have hstep4 : ∀ c : ↥C, c ^ 2 = 1 → ((c : ↥M) : G) ∈ Qz t := by
    intro c hc2
    by_cases hc1 : c = 1
    · have hγ1 : ((c : ↥M) : G) = 1 := by rw [hc1]; rfl
      rw [hγ1]
      exact Subgroup.one_mem _
    · have hγM : ((c : ↥M) : G) ∈ M := (c : ↥M).2
      have hγ2 : (((c : ↥M) : G)) ^ 2 = 1 := by
        have h := congrArg (fun x : ↥C => (((x : ↥M) : G))) hc2
        simpa using h
      have hγ1 : ((c : ↥M) : G) ≠ 1 := by
        intro h1
        exact hc1 (Subtype.ext (Subtype.ext h1))
      have hγB := typeB ((c : ↥M) : G) hγM hγ2 hγ1
      have hcomm_gt : Commute (((c : ↥M) : G)) t := by
        have hcC := Subgroup.mem_centralizer_singleton_iff.mp c.2
        exact congrArg Subtype.val hcC
      have hclaim : IsConj a (a * ((c : ↥M) : G) * t) := by
        by_cases hγt : ((c : ↥M) : G) = t
        · have ht_sq : t * t = 1 := by rw [← pow_two]; exact ht2
          have hgoal : a * ((c : ↥M) : G) * t = a := by
            rw [hγt, mul_assoc, ht_sq, mul_one]
          simpa [hgoal] using IsConj.refl a
        · have hγt_sq : (((c : ↥M) : G) * t) ^ 2 = 1 := by
            rw [hcomm_gt.mul_pow 2, hγ2, ht2, mul_one]
          have hγt_ne : ((c : ↥M) : G) * t ≠ 1 := by
            intro h1
            apply hγt
            have hγinv : ((c : ↥M) : G) = t⁻¹ := mul_eq_one_iff_eq_inv.mp h1
            have htinv : t⁻¹ = t := by
              apply inv_eq_of_mul_eq_one_right
              rw [← pow_two]; exact ht2
            rw [hγinv, htinv]
          have hγtB := typeB (((c : ↥M) : G) * t) (M.mul_mem hγM htM) hγt_sq hγt_ne
          rw [mul_assoc]
          exact hγtB.2.1
      have hcomm_xt : (a * ((c : ↥M) : G)) * t = t * (a * ((c : ↥M) : G)) := by
        rw [mul_assoc, hcomm_gt, ← mul_assoc, hcomm_at, mul_assoc]
      have hmem_x : a * ((c : ↥M) : G) ∈ Qz t :=
        mem_Qz_of_isConj_mul hI h hF1 hγB.2.1 htB.1 hcomm_xt hclaim
      have hmem_a : a ∈ Qz t :=
        mem_Qz_of_isConj_mul hI h hF1 (IsConj.refl a) htB.1 hcomm_at htB.2.1
      have hγ_eq : ((c : ↥M) : G) = a * (a * ((c : ↥M) : G)) := by
        rw [← mul_assoc, haa, one_mul]
      rw [hγ_eq]
      exact (Qz t).mul_mem hmem_a hmem_x
  let θ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) →* G :=
    M.subtype.comp (C.subtype.comp hC.symm.toMonoidHom)
  have hθinj : Function.Injective θ := by
    intro x y hxy
    apply hC.symm.injective
    apply Subtype.ext
    apply Subtype.ext
    simpa [θ] using hxy
  have hθmem : ∀ g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3), g ^ 2 = 1 → θ g ∈ Qz t := by
    intro g hg2
    have hg2' : (hC.symm g) ^ 2 = 1 := by
      have h := congrArg hC.symm hg2
      simpa using h
    have h := hstep4 (hC.symm g) hg2'
    simpa [θ] using h
  have hQzpg : IsPGroup 2 (Qz t) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx t))).map (Gx t).subtype
  have hcomap_pg : IsPGroup 2 ((Qz t).comap θ) :=
    hQzpg.comap_of_injective θ hθinj
  have hclosure_le :
      Subgroup.closure {g : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) | g ^ 2 = 1} ≤
        (Qz t).comap θ :=
    (Subgroup.closure_le _).mpr (fun g hg => hθmem g hg)
  exact hM.inv_not_two_group (hcomap_pg.to_le hclosure_le)

end CFSG.EvenSporadicStandard.HNRecog.Section3
