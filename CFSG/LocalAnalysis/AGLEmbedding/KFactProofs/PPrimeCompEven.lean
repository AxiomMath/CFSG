module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Final
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Chevalley
public import CFSG.RankThree.PartOne.TCB.Final
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief.NearFixed
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.AGLEmbedding.KFactProofs.PPrimeComp

open CFSG.Open CFSG.SignalizerFunctorTheorem.CatalogBridge

@[expose] def EvenFixedOrderP : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card S →
    ∀ f : MulAut S, orderOf f = p → 2 ∣ Nat.card (signalizerFixedSubgroup f)

@[expose] def CatalogCyclicP : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsCatalogGroup S → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card S → PSubgroupsCyclic p S

theorem two_dvd_card_psl2_zmod_two :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) := by
  let a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![1, 1; 0, 1], by decide⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![1, 0; 1, 1], by decide⟩
  let x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) := a
  have hx2 : x ^ 2 = 1 := by
    have : a ^ 2 = 1 := Subtype.ext (by decide)
    change ((a ^ 2 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) = 1
    rw [this]; rfl
  have hx1 : x ≠ 1 := by
    intro h
    have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
      (QuotientGroup.eq_one_iff a).mp h
    have hab := Subgroup.mem_center_iff.mp ha b
    have : b * a ≠ a * b := by
      intro h'
      have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) =>
        (z : Matrix (Fin 2) (Fin 2) (ZMod 2)) 0 0) h'
      revert this; decide
    exact this hab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_dvd_natCard x
  rwa [orderOf_eq_prime hx2 hx1] at h

theorem two_dvd_card_psl2_zmod_three :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) := by
  let a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨!![1, 1; 0, 1], by decide⟩
  let s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) := ⟨!![0, 1; -1, 0], by decide⟩
  let x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3) := s
  have hx2 : x ^ 2 = 1 := by
    have hc : s ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
      have : s ^ 2 = -1 := Subtype.ext (by decide)
      rw [this, Subgroup.mem_center_iff]
      intro g
      ext i j
      simp
    change ((s ^ 2 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) = 1
    exact (QuotientGroup.eq_one_iff _).mpr hc
  have hx1 : x ≠ 1 := by
    intro h
    have hs : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
      (QuotientGroup.eq_one_iff s).mp h
    have hsa := Subgroup.mem_center_iff.mp hs a
    have : a * s ≠ s * a := by
      intro h'
      have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) =>
        (z : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0) h'
      revert this; decide
    exact this hsa
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_dvd_natCard x
  rwa [orderOf_eq_prime hx2 hx1] at h

theorem two_dvd_card_of_fStarSimple {X : Type*} [Group X] [Finite X] (C : Subgroup X)
    (h : IsSimpleGroup (signalizerGeneralizedFitting C) ∧
      ∃ a b : signalizerGeneralizedFitting C, a * b ≠ b * a) :
    2 ∣ Nat.card C := by
  by_contra h2
  have hodd : Odd (Nat.card C) := Nat.odd_iff.mpr (by omega)
  have hsolv : Group.IsSolvable C := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨hs, a, b, hab⟩ := h
  have hFs : Group.IsSolvable (signalizerGeneralizedFitting C) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hFs) a b)

theorem two_dvd_card_fixed_of_model {p : ℕ} (hp : p.Prime)
    {X : Type*} [Group X] [Finite X] (hX : signalizerNearSimpleModel p X)
    (hcop : Nat.Coprime p (Nat.card X)) (f : MulAut X) (hf : orderOf f = p) :
    2 ∣ Nat.card (signalizerFixedSubgroup f) := by
  open CFSG.SignalizerFunctorTheorem.NearModels in
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 2 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    rw [Nat.card_congr ((fixedSubgroupCongr e f).trans φ).toEquiv]
    exact two_dvd_card_psl2_zmod_two
  · obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 3 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    rw [Nat.card_congr ((fixedSubgroupCongr e f).trans φ).toEquiv]
    exact two_dvd_card_psl2_zmod_three
  · obtain ⟨φ⟩ := sz_fixedSubgroup_mulEquiv n hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    rw [Nat.card_congr ((fixedSubgroupCongr e f).trans φ).toEquiv]
    obtain ⟨E⟩ := Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
    rw [← Nat.card_congr E.toEquiv, CFSG.LieType.Ree.suzuki_order (by simp)]
    norm_num
  · obtain ⟨φ⟩ := psu3_fixedSubgroup_mulEquiv hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    have h72 : Nat.card (PSU3 2 1) = 72 :=
      CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one
    rw [Nat.card_congr ((fixedSubgroupCongr e f).trans φ).toEquiv, h72]
    norm_num

section


theorem hypA_of_catalog {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hn : ∃ a b : S, a * b ≠ b * a) (hcat : IsCatalogGroup S) {p : ℕ} (hp : p.Prime)
    (hpS : ¬ p ∣ Nat.card S) : signalizerMcBrideHypothesisA p S :=
  catalog_hypothesisA ⟨CFSG.RankThree.PartOne.SPOR.sporadicHS_outer_le_two,
      CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds,
      CFSG.SignalizerFunctorTheorem.NonLocalExc.subfieldNonLocalizedChevalley⟩ hp S hs hn
    (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge S hn hcat)
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpS)

theorem catalogCyclicP : CatalogCyclicP := fun _ _ _ hs hn hcat _ hp _ hpS =>
  (hypA_of_catalog hs hn hcat hp hpS).2.2.2.2.1

theorem evenFixedOrderP : EvenFixedOrderP := by
  intro S _ _ hs hn hcat p hp _ hpS f hf
  have hA := hypA_of_catalog hs hn hcat hp hpS
  rcases hA.2.2.2.2.2 with hnear | hfield
  · open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief in
    exact two_dvd_card_fixed_of_model hp (signalizerNearSimpleModel_of_nearPSolvable hs hn hnear)
      ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpS) f hf
  · exact two_dvd_card_of_fStarSimple _ (hfield f hf).2.1

end

end CFSG.AGLEmbedding.KFactProofs.PPrimeComp
