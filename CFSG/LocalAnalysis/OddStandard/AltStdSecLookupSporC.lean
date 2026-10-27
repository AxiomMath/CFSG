module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupSporBase
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal
public import CFSG.Monster.B.CTIB.ComponentsSeventeen
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.RestrictedStd.Spor
  CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatLeaf
open CFSG.Sporadic.Schreier (fixSub)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem noLargeAlt_B :
    NoLargeAltComponents .B := by
  refine ⟨fun G _ _ _ ⟨e⟩ t ht K hK => ?_, fun G _ _ _ _ ⟨e⟩ α hα2 hα K hK => ?_⟩
  · obtain ⟨-, hiso, -⟩ :=
      Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t ht
        K hK
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · refine not_isLargeAlt_of_card_quotient (c := 76532479683774853939200)
        (fun m _ => lookup_factorial_div_two_ne (k := 23) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) ?_
      rw [Nat.card_congr φ.toEquiv, LieType.Chevalley.C2E6Std.card_stdGroup]
    · obtain ⟨ψ⟩ := Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      refine not_isLargeAlt_of_card_quotient (c := 3311126603366400)
        (fun m _ => lookup_factorial_div_two_ne (k := 18) (by norm_num [Nat.factorial])
          (by norm_num [Nat.factorial]) m) ?_
      rw [Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        Monster.B.E6.FieldInvF4.card_groupJ]
  · exact (hα (CFSG.ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB G ⟨e⟩ α)).elim

theorem false_of_monster_arith {m : ℕ} (hm : 9 ≤ m) (h41 : 2 ^ 41 ∣ m.factorial / 2)
    (hM : m.factorial / 2 ∣ Open.monsterOrder) : False := by
  have hm37 : 37 ≤ m := by
    by_contra hlt
    have h1 : m.factorial ∣ (36 : ℕ).factorial := Nat.factorial_dvd_factorial (by omega)
    have h2 : 2 ^ 41 ∣ (36 : ℕ).factorial :=
      h41.trans ((Nat.div_dvd_of_dvd (Nat.dvd_factorial (by norm_num) (by omega))).trans h1)
    revert h2
    norm_num [Nat.factorial]
  have hp : Nat.Prime 37 := by norm_num
  have h37 : 37 ∣ m.factorial / 2 := by
    have h1 : 37 ∣ m.factorial := (Nat.Prime.dvd_factorial hp).2 hm37
    have h2 : m.factorial = 2 * (m.factorial / 2) :=
      (Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))).symm
    rw [h2] at h1
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have := h37.trans hM
  revert this
  norm_num [Open.monsterOrder]

theorem noLargeAlt_M
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput) :
    NoLargeAltComponents .M := by
  refine ⟨fun G _ _ hG ⟨e⟩ t ht B hB => ?_, fun G _ _ hG _ ⟨e⟩ α hα2 hα B hB => ?_⟩
  · rintro ⟨m, hm, ⟨eB⟩⟩
    obtain ⟨h41, -⟩ := hMcomp G hG ⟨e⟩ t ht B hB
    have hz : center B = ⊥ := center_eq_bot_of_alt (by omega) eB
    have hq : Nat.card (B ⧸ center B) = Nat.card B :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).toEquiv
    rw [hq, card_eq_of_equiv_alt (by omega) eB] at h41
    obtain ⟨eG⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
    have hM : Nat.card B ∣ Open.monsterOrder := by
      rw [← YGroups.Y443.natCard_Gmat_eq_monsterOrder, ← Nat.card_congr eG.toEquiv]
      exact (Subgroup.card_subgroup_dvd_card B).trans (Subgroup.card_subgroup_dvd_card _)
    rw [card_eq_of_equiv_alt (by omega) eB] at hM
    exact false_of_monster_arith hm h41 hM
  · exact (hα (hMinn G hG ⟨e⟩ α)).elim

theorem fixed_lookup_HN (hHN : HNLocalComponentsInput) (hFour : FourExactOuterInput) {S : Type}
    [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x)
    (e : S ≃* NativeSporadic.HN) {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1)
    {B : Subgroup (fixedSubgroup σ)} (hB : IsComponent B) {m : ℕ} (hm : 9 ≤ m)
    (hBm : Nonempty (B ≃* alternatingGroup (Fin m))) :
    m = 10 ∧ Nonempty (S ≃* NativeSporadic.HN) := by
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · exfalso
    obtain ⟨B', hB', ⟨φ⟩⟩ := isComponent_map_fixedSubgroup_conj ht hB
    obtain ⟨eB⟩ := hBm
    exact not_isLargeAlt_of_card_quotient (c := 44352000)
      (fun m' _ => lookup_factorial_div_two_ne (k := 11) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) m')
      (hHN S e t (lookup_orderOf_eq_two_of_conj hna hσ2 hσ1 ht) B' hB') ⟨m, hm, ⟨φ.trans eB⟩⟩
  · have hσ : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
    obtain ⟨hS, -, -, -, ⟨eS⟩, -⟩ := hFour S inferInstance hna (Or.inr (Or.inl ⟨e⟩)) σ hσ hout
    refine ⟨?_, hS⟩
    have hfix : fixedSubgroup σ = fixSub σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix
    have hB'' : IsComponent (B.map φ.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv φ hB
    have h1 : Nat.card ((B.map φ.toMonoidHom) ⧸ center (B.map φ.toMonoidHom)) ∈
        ({1814400} : Set ℕ) :=
      CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center {1814400}) eS
        compsSatisfy_perm_ten _ hB''
    obtain ⟨eB⟩ := hBm
    have hz : center (B.map φ.toMonoidHom) = ⊥ :=
      center_eq_bot_of_alt (by omega)
        ((B.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eB)
    have hq : Nat.card ((B.map φ.toMonoidHom) ⧸ center (B.map φ.toMonoidHom)) =
        Nat.card (B.map φ.toMonoidHom) :=
      Nat.card_congr
        ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).toEquiv
    rw [hq, Set.mem_singleton_iff, card_eq_of_equiv_alt (by omega)
      ((B.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eB)] at h1
    have h2 : m.factorial = (10 : ℕ).factorial :=
      (Nat.div_left_inj (d := 2) (Nat.dvd_factorial (by norm_num) (by omega))
        (Nat.dvd_factorial (by norm_num) (by norm_num))).1
        (h1.trans (by norm_num [Nat.factorial]))
    exact (Nat.factorial_inj (by omega)).1 h2

end CFSG.OddStandard.AltStdSec
