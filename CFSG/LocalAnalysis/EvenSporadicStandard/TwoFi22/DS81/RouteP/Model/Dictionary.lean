module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Y332Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Transport

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.EvenSporadicStandard.TwoFi22 (nonempty_mulEquiv_of_unique unique_double_cover_R332)
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.YGroups (YGroup yGen yModelHom yModelHom_yGen range_yModelHom evalWord_congr
  closure_yGen injective_and_card_of_model)
open CFSG.Sporadic.Recognition.Fi22Multiplier (R332 F332 F332_eq f332Word card_R332_le)
open CFSG.Sporadic.Recognition.YCover (quotMk quotMk_surjective map_evalWord')
open CFSG.Sporadic.Fi23 (J d Cd center_C card_center_C commutator_C quotCenterEquiv d_zpow)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

@[expose] noncomputable def y332Hom :
    YGroup 3 3 2 →* Perm Ω :=
  yModelHom y332Perm fun w hw => y332_rels w (List.mem_append_left _ hw)

theorem y332Hom_yGen {c : ℕ}
    (hc : c < 9) : y332Hom (yGen 3 3 2 c) = y332Perm c :=
  yModelHom_yGen hc

theorem y332Hom_evalWord
    (w : List ℕ) (hw : ∀ c ∈ w, c < 9) :
    y332Hom (evalWord (yGen 3 3 2) w) = evalWord y332Perm w := by
  rw [map_evalWord' y332Hom]
  exact evalWord_congr fun c hc => y332Hom_yGen (hw c hc)

theorem y332Hom_F332 :
    y332Hom F332 = 1 := by
  rw [F332_eq, y332Hom_evalWord _ (by decide)]
  exact y332_rels f332Word (List.mem_append_right _ (List.mem_singleton_self _))

@[expose] noncomputable def y332HomR :
    R332 →* Perm Ω :=
  QuotientGroup.lift _ y332Hom (Subgroup.normalClosure_le_normal (by
    simpa [MonoidHom.mem_ker] using y332Hom_F332))

theorem range_y332HomR :
    y332HomR.range = Subgroup.closure (y332Perm '' Set.Iio 9) := by
  have h1 : y332HomR.range = y332Hom.range := by
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      obtain ⟨y, rfl⟩ := quotMk_surjective F332 r
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨quotMk F332 y, rfl⟩
  rw [h1]
  unfold y332Hom
  exact range_yModelHom

theorem card_y332HomR_range_ge :
    129123503308800 ≤ Nat.card y332HomR.range := by
  rw [range_y332HomR]
  exact card_closure_nine_ge

theorem y332HomR_injective :
    Function.Injective y332HomR := by
  obtain ⟨hfin, hcard⟩ := card_R332_le
  have hcard' : Nat.card R332 ≤ 129123503308800 := by omega
  exact (injective_and_card_of_model y332HomR hcard' card_y332HomR_range_ge).1

@[expose] noncomputable def rhoL : ↥L0 →* Perm Ω :=
  rho.comp L0.subtype

theorem finite_L0 :
    Finite ↥L0 := by
  obtain ⟨hfin, -⟩ := card_Zp_le
  exact Finite.of_injective (Subgroup.inclusion L0_le_Zp) (Subgroup.inclusion_injective _)

theorem card_L0_le :
    Nat.card ↥L0 ≤ 129123503308800 := by
  have h := card_L0
  have hz := card_Zp_le.2
  omega

theorem range_y332HomR_le_rhoL :
    y332HomR.range ≤ rhoL.range := by
  rw [range_y332HomR, Subgroup.closure_le]
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨⟨y332Gen c, y332Gen_mem_L0 hc⟩, rfl⟩

theorem rhoL_injective_and_card :
    Function.Injective rhoL ∧ Nat.card ↥L0 = 129123503308800 := by
  haveI := finite_L0
  exact injective_and_card_of_model rhoL card_L0_le
    (card_y332HomR_range_ge.trans (Subgroup.card_le_of_le range_y332HomR_le_rhoL))

theorem card_L0_eq :
    Nat.card ↥L0 = 129123503308800 :=
  rhoL_injective_and_card.2

theorem range_y332HomR_eq_rhoL :
    y332HomR.range = rhoL.range := by
  haveI := finite_L0
  refine Subgroup.eq_of_le_of_card_ge range_y332HomR_le_rhoL ?_
  have h1 : Nat.card rhoL.range ≤ Nat.card ↥L0 :=
    Nat.card_le_card_of_surjective _ rhoL.rangeRestrict_surjective
  rw [card_L0_eq] at h1
  exact h1.trans card_y332HomR_range_ge

noncomputable def R332EquivL0 :
    R332 ≃* ↥L0 :=
  (MonoidHom.ofInjective y332HomR_injective).trans
    ((MulEquiv.subgroupCongr range_y332HomR_eq_rhoL).trans
      (MonoidHom.ofInjective rhoL_injective_and_card.1).symm)

theorem L0_equiv_R332 :
    Nonempty (↥L0 ≃* R332) :=
  ⟨R332EquivL0.symm⟩

theorem Cd_equiv_R332 :
    Nonempty (Cd ≃* R332) := by
  obtain ⟨f⟩ := nonempty_mulEquiv_of_unique unique_double_cover_R332 commutator_C card_center_C
    (quotCenterEquiv.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm)
  exact ⟨f⟩

theorem L0_equiv_Cd :
    Nonempty (↥L0 ≃* Cd) := by
  obtain ⟨e1⟩ := L0_equiv_R332
  obtain ⟨e2⟩ := Cd_equiv_R332
  exact ⟨e1.trans e2.symm⟩

theorem card_center_eq_two_of_equiv_Cd
    {Λ : Type} [Group Λ] (ψ : Λ ≃* Cd) :
    Nat.card (Subgroup.center Λ) = 2 := by
  have hmem : ∀ z : Λ, z ∈ Subgroup.center Λ ↔ ψ z ∈ Subgroup.center Cd := by
    intro z
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hz c
      have := hz (ψ.symm c)
      calc c * ψ z = ψ (ψ.symm c * z) := by simp
        _ = ψ (z * ψ.symm c) := by rw [this]
        _ = ψ z * c := by simp
    · intro hz g
      apply ψ.injective
      rw [map_mul, map_mul]
      exact hz (ψ g)
  let e : Subgroup.center Λ ≃ Subgroup.center Cd :=
    { toFun := fun z => ⟨ψ z, (hmem z).1 z.2⟩
      invFun := fun c => ⟨ψ.symm c, (hmem _).2 (by simpa using c.2)⟩
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  exact (Nat.card_congr e).trans card_center_C

theorem card_center_L0 :
    Nat.card (Subgroup.center ↥L0) = 2 := by
  obtain ⟨ψ⟩ := L0_equiv_Cd
  exact card_center_eq_two_of_equiv_Cd ψ

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
