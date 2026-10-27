module

public import CFSG.CGT.PushingUpLit.CGT6K1.Defs
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.Blueprint Subgroup CFSG.LocalAnalysis.EvenBN.GMSK CFSG.CGT.PushingUpLit.CGT6

section Sylow

variable {G : Type*} [Group G] [Finite G] {C : Subgroup G}

theorem card_le_two_of_sylow_two (hC : ∀ S : Sylow 2 C, Nat.card S = 2) {P : Subgroup G}
    (hPC : P ≤ C) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP.of_equiv (subgroupOfEquivOfLe hPC).symm
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  calc Nat.card P = Nat.card (P.subgroupOf C) :=
        Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv.symm
    _ ≤ Nat.card S := card_le_of_le hS
    _ = 2 := hC S

theorem exists_involution_of_sylow_two (hC : ∀ S : Sylow 2 C, Nat.card S = 2) :
    ∃ t ∈ C, orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 C))
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hC S])
  exact ⟨((s : C) : G), (s : C).2, by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hs]⟩

end Sylow

theorem gmsVList_congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : GMSVList Q) :
    GMSVList Q' := by
  rcases h with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩ | h | h | h
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr (Or.inl ⟨e.symm.trans e'⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans e'⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inl ⟨by decide, stated_psl_congr e (stated_psl_of_lieModel (by norm_num) h)⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (Or.inl ⟨by decide, stated_psl_congr e (stated_psl_of_lieModel (by norm_num) h)⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨by decide, stated_psu_congr e (stated_psu_of_lieModel (by norm_num) h)⟩)))))))

theorem inner_outcome (hSel : CatSelector) (hInner : InnerSurvivorsInV) {D : Type} [Group D]
    [Finite D] (hD : IsSimpleGroup D) (hK : CFSG.SectionRank.IsKGroupCat D) {n : ℕ}
    {A : Subgroup D} (hA : StdLinearData D A n)
    (hS : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set D)), Nat.card S = 2) :
    n = 2 ∧ GMSVList D := by
  obtain ⟨t, htA, ht⟩ := exists_involution_of_sylow_two hS
  obtain ⟨hCt, -⟩ := CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    (hA.2.1 : CFSG.Assembly.ComponentType.IsStandardSubgroup A) htA ht
  obtain ⟨a, haA, b, hbA, hab⟩ :=
    CFSG.ComponentClassification.AS76b.Lemma34.exists_not_commute hA.2.1.1
  obtain ⟨hn, -, -, K, _, _, hK2, ⟨φ⟩⟩ := hA
  have hnt : ∃ d ∈ (⊤ : Subgroup D), t⁻¹ * d * t ≠ d := by
    by_contra hcon
    push Not at hcon
    have hzt : t ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro d
      have h1 := hcon d (Subgroup.mem_top d)
      calc d * t = t * (t⁻¹ * d * t) := by group
        _ = t * d := by rw [h1]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center D) with h | h
    · rw [h, Subgroup.mem_bot] at hzt
      rw [hzt, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · have hc : ∀ x y : D, x * y = y * x := fun x y => by
        have hy : y ∈ Subgroup.center D := by rw [h]; exact Subgroup.mem_top y
        exact Subgroup.mem_center_iff.mp hy x
      exact hab (hc a b)
  have hDtop : IsSimpleGroup ↥(⊤ : Subgroup D) := Subgroup.topEquiv.isSimpleGroup
  have hcat : Catalog ↥(⊤ : Subgroup D) :=
    CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK (⊤ : Subgroup D)
      (MonoidHom.id ↥(⊤ : Subgroup D)) Function.surjective_id
  have hdat := fixedRootDatum_of_normal (D := (⊤ : Subgroup D)) (le_top : A ≤ ⊤) ht htA hCt hnt
    (fun P hPC hP => card_le_two_of_sylow_two hS hPC hP) hn hK2 φ
  have hsurv := hSel.survivors_of_datum hDtop hcat hdat
  have hin := conjNormal_mem_range_of_mem (D := (⊤ : Subgroup D)) (t := t) (Subgroup.mem_top t)
  obtain ⟨h2, hv⟩ := hInner ↥(⊤ : Subgroup D) hDtop n K _ _ hdat hin hsurv
  exact ⟨h2, gmsVList_congr Subgroup.topEquiv hv⟩

theorem simpleStd_of_inputs (hSel : CatSelector) (hInner : InnerSurvivorsInV) (hR2 : Rank2Std)
    (hK : StdKernelTwo) : SimpleStd := by
  intro D _ _ hD hKD n A hA
  by_cases h2 : 2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (A : Set D))
  · exact hR2 D hD hKD n A hA h2
  · exact inner_outcome hSel hInner hD hKD hA (hK D hD hKD n A hA (by omega))

end CFSG.CGT.PushingUpLit.CGT6K1
