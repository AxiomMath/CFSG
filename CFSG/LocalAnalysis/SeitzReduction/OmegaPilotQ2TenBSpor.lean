module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadicResidual
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAll

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv exists_conj_or_not_mem_range)
open CFSG.Sporadic.Schreier (fixSub)

section Fi22

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore

theorem fi22P_outer_card_fixSub_of_component_omega (β : MulAut fi22P) (hβ2 : β * β = 1)
    (hβn : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner fi22P)
    {B : Subgroup (fixSub β)} (hB : IsComponent B)
    (hcard : Nat.card (B ⧸ Subgroup.center B) = 174182400) :
    Nat.card (fixSub β) = 1045094400 := by
  obtain ⟨r, rfl⟩ := fi22RAut.surjective β
  have hr2 : r * r = 1 := fi22RAut.injective (by rw [map_mul, hβ2, map_one])
  have hrP : (r : Equiv.Perm (Fin 3510)) ∉ fi22P := by
    intro h
    apply hβn
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, ← fi22RAut_inn]
    exact ⟨r, Subgroup.mem_subgroupOf.2 h, rfl⟩
  obtain ⟨hB2, hc2⟩ := component_quotient_mulEquiv (fixSubRAutEquiv r) hB
  rw [hc2] at hcard
  rw [Nat.card_congr (fixSubRAutEquiv r).toEquiv]
  set τ := (r : Equiv.Perm (Fin 3510))
  have hτ1 : τ ≠ 1 := fun h => hrP (h ▸ fi22P.one_mem)
  have hτ2 : τ * τ = 1 := congrArg Subtype.val hr2
  have hτo : orderOf τ = 2 := orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
  obtain ⟨k, hk, c, hc, hck⟩ := fi22R_involution_conj r.2 hτo
  have hcn := fi22R_le_normalizer hc
  have hk3 : 3 ≤ k := by
    by_contra h
    apply hrP
    have hkP : fi22ExtRep k ∈ fi22P := CTUC_Fi22_all_extension_involutions_covered.1 k (by omega)
    rw [← hck] at hkP
    exact (Subgroup.mem_normalizer_iff.1 hcn τ).2 hkP
  have e1 := (fi22CP_conj_equiv hcn τ).trans (MulEquiv.subgroupCongr (by rw [hck]))
  obtain ⟨hB1, hc1⟩ := component_quotient_mulEquiv e1 hB2
  rw [hc1] at hcard
  rw [Nat.card_congr e1.toEquiv]
  obtain ⟨-, -, h3, h4, h5, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · exfalso
    obtain ⟨hB3, -⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h3) hB1
    exact fo22H2_no_component _ hB3
  · rw [Nat.card_congr (MulEquiv.subgroupCongr h4).toEquiv, card_fi22H (c := 3) (by norm_num)]
    rfl
  · exfalso
    obtain ⟨hB3, hc3⟩ := component_quotient_mulEquiv (MulEquiv.subgroupCongr h5) hB1
    rw [hc3, fo22H4_component hB3] at hcard
    norm_num at hcard

theorem fi22_outer_card_fixedSubgroup_omega {S : Type} [Group S] (e : S ≃* NativeSporadic.Fi22)
    {σ : MulAut S} (hσ2 : σ * σ = 1) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 174182400) :
    Nat.card (fixedSubgroup σ) = 1045094400 := by
  set θ : S ≃* fi22P := e.trans fi22PermEquiv
  let φ := MulEquiv.subgroupCongr (SporadicRefine.fixedSubgroup_eq_fixSub σ)
  obtain ⟨hD1, hc1⟩ := component_quotient_mulEquiv φ hD
  obtain ⟨hD2, hc2⟩ := component_quotient_mulEquiv (fixSubCongr θ σ) hD1
  rw [hc1, hc2] at hcard
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr (fixSubCongr θ σ).toEquiv]
  exact fi22P_outer_card_fixSub_of_component_omega _ (congr_mul_self θ σ hσ2)
    (fun h => hout ((congr_mem_inner_iff θ σ).1 h)) hD2 hcard

end Fi22

section Main

theorem card_quotient_center_omegaEight {X : Type} [Group X] {D : Subgroup X}
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (hDm : LieModel (D ⧸ center D) t 4 2 1) :
    (t = .POmegaPlus ∧ Nat.card (D ⧸ center D) = 174182400) ∨
      (t = .POmegaMinus ∧ Nat.card (D ⧸ center D) = 197406720) := by
  have h := card_of_lieModel_POmega_two ht hDm
  rcases ht with rfl | rfl
  · exact .inl ⟨rfl, h.trans (by decide)⟩
  · exact .inr ⟨rfl, h.trans (by decide)⟩

theorem false_of_omegaEight_dvd {N M : ℕ} (hN : N = 174182400 ∨ N = 197406720) (hdvd : N ∣ M)
    (h1 : ¬ 174182400 ∣ M) (h2 : ¬ 197406720 ∣ M) : False := by
  rcases hN with rfl | rfl
  · exact h1 hdvd
  · exact h2 hdvd

theorem sporadic_omegaEight_four_one (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) t 4 2 1) :
    σ ∉ (MulAut.conj : S →* MulAut S).range ∧ t = .POmegaPlus ∧
      Nonempty (S ≃* NativeSporadic.Fi22) ∧ Nat.card (fixedSubgroup σ) = 1045094400 := by
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hcases := card_quotient_center_omegaEight ht hDm
  have hN : Nat.card (D ⧸ center D) = 174182400 ∨ Nat.card (D ⧸ center D) = 197406720 := by
    rcases hcases with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  have hdvd : Nat.card (D ⧸ center D) ∣ Nat.card (NativeSporadic.Carrier s) :=
    (Nat.card_congr e.toEquiv) ▸ card_quotient_center_dvd_card_of_fixed D
  have gen : ∀ M : ℕ, Nat.card (NativeSporadic.Carrier s) = M → ¬ 174182400 ∣ M →
      ¬ 197406720 ∣ M → False := fun M hM h1 h2 => false_of_omegaEight_dvd hN (hM ▸ hdvd) h1 h2
  have hne : ∀ M : ℕ, Nat.card (D ⧸ center D) = M → M ≠ 174182400 → M ≠ 197406720 → False := by
    intro M hM h1 h2
    rcases hN with h | h
    · exact h1 (hM ▸ h)
    · exact h2 (hM ▸ h)
  have hfixdvd : Nat.card (D ⧸ center D) ∣ Nat.card (fixedSubgroup σ) :=
    (card_quotient_dvd_card _).trans (card_subgroup_dvd_card D)
  cases s
  case M11 => exact (gen _ Sporadic.Mathieu.card_M11 (by decide) (by decide)).elim
  case M12 => exact (gen _ Sporadic.Mathieu.card_M12 (by decide) (by decide)).elim
  case M22 => exact (gen _ Sporadic.Mathieu.card_M22 (by decide) (by decide)).elim
  case M23 => exact (gen _ EvenSmallLie.CatalogOrders.card_M23 (by decide) (by decide)).elim
  case M24 => exact (gen _ Sporadic.Mathieu.card_M24 (by decide) (by decide)).elim
  case J1 => exact (gen _ Sporadic.J1.card_J1 (by decide) (by decide)).elim
  case J2 => exact (gen _ Sporadic.J2.card_J2 (by decide) (by decide)).elim
  case J3 => exact (gen _ Sporadic.J3.card_J3 (by decide) (by decide)).elim
  case J4 => exact (gen _ Sporadic.J4.card_J4 (by decide) (by decide)).elim
  case HS => exact (gen _ Sporadic.HS.card_HS (by decide) (by decide)).elim
  case McL => exact (gen _ Sporadic.McL.card_McL (by decide) (by decide)).elim
  case He => exact (gen _ Sporadic.He.fam_he_order.1 (by decide) (by decide)).elim
  case Ru => exact (gen _ Sporadic.Ru.card_Ru (by decide) (by decide)).elim
  case Ly => exact (gen _ Sporadic.Ly.card_Ly (by decide) (by decide)).elim
  case ONan => exact (gen _ Sporadic.ON.card_ON (by decide) (by decide)).elim
  case Co3 => exact (gen _ Sporadic.Co3.card_Co3 (by decide) (by decide)).elim
  case Co2 => exact (SporadicRefine.false_of_co2_component hS hna e hσ hD).elim
  case Th => exact (SporadicRefine.false_of_th_component hS hna e hσ hD).elim
  case M => exact (false_of_monster_POmega hMinn hMcomp hS hna e hσ ht hD hDm).elim
  case Fi23 =>
    have h := fi23_eleven_dvd_card_quotient_center hS hna e hσ hD
    exfalso
    rcases hN with h' | h' <;> rw [h'] at h <;> norm_num at h
  case Fi24Prime =>
    have h := fi24_card_quotient_center hS hna e hσ hD
    exfalso
    rcases h with h | h | h <;> exact hne _ h (by norm_num) (by norm_num)
  case B =>
    have h := baby_card_quotient_center hS hna e hσ hD
    exfalso
    rcases h with h | h <;> exact hne _ h (by norm_num) (by norm_num)
  case Co1 =>
    exfalso
    obtain ⟨u, rfl⟩ :=
      ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co1 σ
    obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
    have h := (ComponentClassification.RestrictedStd.Spor.co1LocalComponentsInput_holds S e u
      (orderOf_eq_two_of_conj hS hna hσ) B hB).1
    exact hne _ (hcard.symm.trans h) (by norm_num) (by norm_num)
  case HN =>
    exfalso
    rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
    · obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
      have h := ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds S e u
        (orderOf_eq_two_of_conj hS hna hσ) B hB
      exact hne _ (hcard.symm.trans h) (by norm_num) (by norm_num)
    · obtain ⟨φ⟩ := ComponentClassification.RestrictedStd.Spor.hnOuterFixInput S e σ hσ hout
      have hfix : Nat.card (fixedSubgroup σ) = 3628800 := by
        rw [Nat.card_congr (MulEquiv.subgroupCongr
            (SporadicRefine.fixedSubgroup_eq_fixSub σ)).toEquiv,
          Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
        rfl
      rw [hfix] at hfixdvd
      rcases hN with h' | h' <;> rw [h'] at hfixdvd <;> norm_num at hfixdvd
  case Suz =>
    exfalso
    rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
    · obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
      have h := Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u
        (orderOf_eq_two_of_conj hS hna hσ) B hB
      exact hne _ (hcard.symm.trans h) (by norm_num) (by norm_num)
    · rcases SporadicRefine.suz_outer_card_fixedSubgroup e hσ hout with h | h <;>
        rw [h] at hfixdvd <;> rcases hN with h' | h' <;> rw [h'] at hfixdvd <;>
          norm_num at hfixdvd
  case Fi22 =>
    rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
    · exfalso
      obtain ⟨B, hB, hcard⟩ := exists_component_centralizer_of_conj u hD
      have h := Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
        e u (orderOf_eq_two_of_conj hS hna hσ) B hB
      exact hne _ (hcard.symm.trans h) (by norm_num) (by norm_num)
    · obtain ⟨B, hB, hcard⟩ := exists_component_fixSub σ hD
      have h := Sporadic.FischerOddCore.fi22OuterComponentsInput_holds S ⟨e⟩ σ hσ2 hout B hB
      rw [hcard] at h
      rcases hcases with ⟨rfl, h1⟩ | ⟨rfl, h1⟩
      · exact ⟨hout, rfl, ⟨e⟩, fi22_outer_card_fixedSubgroup_omega e hσ2 hout hD h1⟩
      · exfalso
        rw [h1] at h
        norm_num at h

@[expose] def OmegaEightSporadicStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    NativeSporadic.SporadicRep S → ∀ σ : MulAut S, orderOf σ = 2 → ∀ (t : StatedLieTag)
      (D : Subgroup (fixedSubgroup σ)), (t = .POmegaPlus ∨ t = .POmegaMinus) → IsComponent D →
      LieModel (D ⧸ center D) t 4 2 1 →
        σ ∉ (MulAut.conj : S →* MulAut S).range ∧ t = .POmegaPlus ∧
          Nonempty (S ≃* NativeSporadic.Fi22) ∧ Nat.card (fixedSubgroup σ) = 1045094400

theorem omegaEightSporadicStatement_holds (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : OmegaEightSporadicStatement :=
  fun _ _ _ hS hna hsp _ hσ _ _ ht hD hDm =>
    sporadic_omegaEight_four_one hMinn hMcomp hS hna hsp hσ ht hD hDm

end Main

end CFSG.SeitzReduction.OmegaPilot
