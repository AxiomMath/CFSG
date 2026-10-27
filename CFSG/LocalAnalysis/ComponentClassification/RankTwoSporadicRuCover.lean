module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEnd175
public import CFSG.Sporadic.Recognition.RuMultiplier
public import CFSG.Sporadic.Recognition.HeMultiplier
public import CFSG.Sporadic.Schreier.RuInvClasses

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Ru

open Subgroup CFSG.Open CFSG.CosetTable CFSG.Sporadic.RuSchreier CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Recognition.RuMultiplier

theorem ruCentralTwoGroupOrderBound_of_checks
    (hTab : RuTabFact)
    (hL0 : RuIndexK) :
    RuCentralTwoGroupOrderBound := by
  intro L _ _ hLq _ ⟨e⟩
  have hperf : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  obtain ⟨hpos, hle⟩ := card_griessHopfMultiplier_J_le hTab hL0
  have f := CFSG.Sporadic.Bridge.Ru.nativeEquiv
  have e' : L ⧸ center L ≃* J ruVec := e.trans f
  have h := CFSG.Sporadic.Recognition.HeMultiplier.card_center_dvd_griess (S := J ruVec) hperf e'
  exact (Nat.le_of_dvd hpos h).trans hle

theorem ruJEquivP_a :
    ruJEquivP (a ruD) = ⟨ruA0, ruA0_mem⟩ :=
  Subtype.ext ruJtoP_a

theorem ruDoubleCoverTwoBLift_of_checks
    (hTab : RuTabFact)
    (hRho : ruRhoCheck = true)
    (hL0 : RuIndexK) :
    RuDoubleCoverTwoBLift := by
  intro L _ _ hLq t ht hZ π hπ hker v hv2 hfpf
  have : Group.IsPerfect L := (Group.isPerfect_def).2 hLq.1
  have hinv : ((π v : ruP) : Equiv.Perm (Fin 4060)) ∈
      {x | x ∈ ruP ∧ orderOf x = 2} := ⟨(π v).2, by rw [Subgroup.orderOf_coe]; exact hv2⟩
  rw [ruInvolutions_eq] at hinv
  have hA : ((π v : ruP) : Equiv.Perm (Fin 4060)) ∈ ruAP := by
    rcases hinv with hZ' | hA
    · exfalso
      obtain ⟨g, -, hg⟩ := hZ'
      have h92 := conj_ruZ_ncard (g := g)
      rw [hg, show fixSet ((π v : ruP) : Equiv.Perm (Fin 4060)) = ∅ from
        Set.eq_empty_iff_forall_notMem.2 fun p hp => hfpf p hp, Set.ncard_empty] at h92
      norm_num at h92
    · exact hA
  obtain ⟨g, hg, hgv⟩ := hA
  obtain ⟨e, he⟩ : ∃ e : ↥ruP ≃* J ruVec, ∀ x, (e x : J ruD) = ruJEquivP.symm x :=
    ⟨ruJEquivP.symm, fun _ => rfl⟩
  obtain ⟨q, hqx⟩ : ∃ q : L →* J ruVec, ∀ x, q x = e (π x) :=
    ⟨MonoidHom.comp (MulEquiv.toMonoidHom e) π, fun _ => rfl⟩
  have hq : Function.Surjective q := fun y => by
    obtain ⟨x, hx⟩ := hπ (e.symm y)
    exact ⟨x, by rw [hqx, hx, MulEquiv.apply_symm_apply]⟩
  have hqker : q.ker = zpowers t := by
    rw [← hker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hqx, MulEquiv.map_eq_one_iff]
  have hcen : zpowers t ≤ center L := hZ ▸ le_rfl
  have hA0 : e ⟨ruA0, ruA0_mem⟩ = a ruVec := by
    show (e ⟨ruA0, ruA0_mem⟩ : J ruD) = a ruD
    rw [he, MulEquiv.symm_apply_eq, ruJEquivP_a]
  have hπv : π v = ⟨g, hg⟩ * ⟨ruA0, ruA0_mem⟩ * (⟨g, hg⟩ : ↥ruP)⁻¹ := Subtype.ext hgv.symm
  have hv : q v = e ⟨g, hg⟩ * a ruVec * (e ⟨g, hg⟩)⁻¹ := by
    rw [hqx, hπv, map_mul, map_mul, map_inv, hA0]
  exact sq_eq_of_lift_conj_a hTab hRho hL0 q hq ht hqker hcen hv

end CFSG.ComponentClassification.RankTwoSporadic.Ru
