module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRankR
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeInheritance
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
import CFSG.LocalAnalysis.PreuniquenessRankFour.CharacteristicAbelian
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenComp

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup
open CFSG.PreuniquenessRankFour.Helpers

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem closure_orderOf_normal (p : ℕ) : (closure {x : X | orderOf x = p}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  refine Subgroup.closure_induction (k := {x : X | orderOf x = p})
    (p := fun x _ => g * x * g⁻¹ ∈ closure {x : X | orderOf x = p})
    (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) hn
  · rw [Set.mem_setOf_eq] at hx
    refine Subgroup.subset_closure ?_
    rw [Set.mem_setOf_eq]
    have hconj : SemiconjBy g x (g * x * g⁻¹) := by
      show g * x = (g * x * g⁻¹) * g
      group
    rw [← SemiconjBy.orderOf_eq g hconj]
    exact hx
  · simpa using Subgroup.one_mem (closure {x : X | orderOf x = p})
  · rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ ihx ihy
  · rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ihx

theorem closure_orderOf_subtype_eq_top (p : ℕ) :
    closure {x : ↥(closure {x : X | orderOf x = p}) | orderOf x = p} = ⊤ := by
  have h : ((↑) : ↥(closure {x : X | orderOf x = p}) → X) ⁻¹'
      {x : X | orderOf x = p} =
      {x : ↥(closure {x : X | orderOf x = p}) | orderOf x = p} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [Subgroup.orderOf_coe]
  rw [← h]
  exact Subgroup.closure_closure_coe_preimage

theorem isPGroup_of_isCyclic_pCore (hp : p.Prime)
    (hgen : closure {x : X | orderOf x = p} = ⊤)
    (hX : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hcyc : IsCyclic ↥(CFSG.pCore p X)) : IsPGroup p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup X := CFSG.pCore p X
  haveI hPnorm : P.Normal := CFSG.pCore_normal (p := p) (G := X)
  have hmem_norm : ∀ g : X, g ∈ Subgroup.normalizer (P : Set X) := by
    intro g
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hcomm : ∀ g₁ g₂ : X, g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ P := by
    intro g₁ g₂
    exact hX (commutator_mem_centralizer_of_isCyclic (R := P) hcyc
      (hmem_norm g₁) (hmem_norm g₂))
  have hquot_comm : ∀ a b : X ⧸ P, a * b = b * a := by
    intro a b
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective P a
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk'_surjective P b
    have h1 : QuotientGroup.mk' P (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)).mpr (hcomm g₁ g₂)
    have key : QuotientGroup.mk' P g₁ * QuotientGroup.mk' P g₂ *
        (QuotientGroup.mk' P g₁)⁻¹ * (QuotientGroup.mk' P g₂)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    calc QuotientGroup.mk' P g₁ * QuotientGroup.mk' P g₂
        = (QuotientGroup.mk' P g₁ * QuotientGroup.mk' P g₂ *
            (QuotientGroup.mk' P g₁)⁻¹ * (QuotientGroup.mk' P g₂)⁻¹) *
            (QuotientGroup.mk' P g₂ * QuotientGroup.mk' P g₁) := by group
      _ = 1 * (QuotientGroup.mk' P g₂ * QuotientGroup.mk' P g₁) := by rw [key]
      _ = QuotientGroup.mk' P g₂ * QuotientGroup.mk' P g₁ := one_mul _
  have hpow : ∀ x : X, x ^ p ∈ P := by
    intro x
    have hx : x ∈ closure {x : X | orderOf x = p} := by
      rw [hgen]
      exact Subgroup.mem_top x
    refine Subgroup.closure_induction (k := {x : X | orderOf x = p})
      (p := fun x _ => x ^ p ∈ P) (fun y hy => ?_) ?_
      (fun y z _ _ ihy ihz => ?_) (fun y _ ihy => ?_) hx
    · rw [Set.mem_setOf_eq] at hy
      rw [← hy, pow_orderOf_eq_one]
      exact P.one_mem
    · simpa using P.one_mem
    · have hiy : QuotientGroup.mk' P (y ^ p) = 1 := (QuotientGroup.eq_one_iff _).mpr ihy
      have hiz : QuotientGroup.mk' P (z ^ p) = 1 := (QuotientGroup.eq_one_iff _).mpr ihz
      have h2 : QuotientGroup.mk' P ((y * z) ^ p) =
          (QuotientGroup.mk' P y) ^ p * (QuotientGroup.mk' P z) ^ p := by
        rw [map_pow, map_mul, Commute.mul_pow (hquot_comm _ _)]
      have h3 : QuotientGroup.mk' P ((y * z) ^ p) = 1 := by
        rw [h2, ← map_pow, ← map_pow, hiy, hiz, one_mul]
      exact (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using h3)
    · have hiy : QuotientGroup.mk' P (y ^ p) = 1 := (QuotientGroup.eq_one_iff _).mpr ihy
      have h3 : QuotientGroup.mk' P ((y⁻¹) ^ p) = 1 := by
        rw [map_pow, map_inv, inv_pow, ← map_pow, hiy, inv_one]
      exact (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using h3)
  intro x
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := p) (G := X) ⟨x ^ p, hpow x⟩
  refine ⟨k + 1, ?_⟩
  have hk' : (x ^ p) ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [show x ^ p ^ (k + 1) = (x ^ p) ^ (p ^ k) by rw [pow_succ', pow_mul]]
  exact hk'

theorem two_le_pRank_pCore_of_not_isPGroup (hp : p.Prime) (hp2 : p ≠ 2)
    (hgen : closure {x : X | orderOf x = p} = ⊤)
    (hX : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hnp : ¬ IsPGroup p X) : 2 ≤ CFSG.Open.pRank p (CFSG.pCore p X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnc : ¬ IsCyclic ↥(CFSG.pCore p X) := fun hcyc =>
    hnp (isPGroup_of_isCyclic_pCore hp hgen hX hcyc)
  haveI : Fact (IsPGroup p ↥(CFSG.pCore p X)) := ⟨CFSG.pCore_isPGroup⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := ↥(CFSG.pCore p X)) hp2 hnc
  have hSab : CFSG.Open.IsElemAbelian p (S.map (CFSG.pCore p X).subtype) :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian).mpr
      (CFSG.IsElementaryAbelian.subgroup_map hSel (CFSG.pCore p X).subtype)
  have hSR : S.map (CFSG.pCore p X).subtype ≤ CFSG.pCore p X := Subgroup.map_subtype_le _
  have hcard : Nat.card (S.map (CFSG.pCore p X).subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (CFSG.pCore p X).subtype_injective, hScard]
  have h2 := CFSG.SectionRank.le_pRank hp.one_lt hSR hSab hcard
  omega

theorem exists_characteristic_elemAbelian_of_not_isSymplecticType {P : Type} [Group P]
    [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup P) ≤ 2)
    (hS : ¬ CFSG.RankThree.PartTwo.IsSymplecticType P) :
    ∃ A : Subgroup P, A.Characteristic ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  rw [CFSG.RankThree.PartTwo.IsSymplecticType] at hS
  push Not at hS
  obtain ⟨B, hBc, hBab, hBnc⟩ := hS
  haveI : B.Characteristic := hBc
  obtain ⟨A, hAc, -, hAe, hA2⟩ :=
    noncyclic_characteristic_abelian_pGroup_has_characteristic_elementary
      p hp hP B hBab hBnc
  have hArank_le : CFSG.Open.pRank p A ≤ 2 :=
    (CFSG.SectionRank.pRank_mono hp.one_lt (le_top : A ≤ (⊤ : Subgroup P))).trans hrk
  have hArank : CFSG.Open.pRank p A = 2 := le_antisymm hArank_le hA2
  have hAp : IsPGroup p A := hP.to_subgroup A
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
  have hn_le : n ≤ 2 := by
    have h := CFSG.SectionRank.le_pRank hp.one_lt (le_refl A) hAe hn
    omega
  have h2_le_n : 2 ≤ n := by
    obtain ⟨E, hEA, hEe, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
    have hcard_le : Nat.card E ≤ Nat.card A := Subgroup.card_le_of_le hEA
    rw [hEcard, hn, hArank] at hcard_le
    exact (Nat.pow_le_pow_iff_right hp.two_le).mp hcard_le
  have hn2 : n = 2 := le_antisymm hn_le h2_le_n
  exact ⟨A, hAc, hAe, by rw [hn, hn2]⟩

theorem exists_normal_elemAbelian_of_sixSixOne (h661 : SixSixOneRank) (hp : p.Prime)
    (hp3 : 3 < p) (hX : centralizer (CFSG.pCore p X : Set X) ≤ CFSG.pCore p X)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2)
    (hV : ¬ IsPGroup p ↥(closure {x : X | orderOf x = p})) :
    ∃ A : Subgroup X, A.Normal ∧ CFSG.Open.IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let V : Subgroup X := closure {x : X | orderOf x = p}
  have hVn : V.Normal := closure_orderOf_normal (X := X) p
  haveI : V.Normal := hVn
  have hgen : closure {x : ↥V | orderOf x = p} = ⊤ := closure_orderOf_subtype_eq_top (X := X) p
  have hCV : centralizer (CFSG.pCore p ↥V : Set ↥V) ≤ CFSG.pCore p ↥V :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_self_centralizing_pCore p hp hX V hVn
  have hne : CFSG.pCore p ↥V ≠ ⊤ := by
    intro htop
    apply hV
    have htopP : IsPGroup p (⊤ : Subgroup ↥V) := by
      rw [← htop]
      exact CFSG.pCore_isPGroup (p := p) (G := ↥V)
    exact htopP.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup ↥V) ≃* ↥V)
  have hrkV : CFSG.Open.pRank p (⊤ : Subgroup ↥V) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt V.subtype
      V.subtype_injective).trans hrk
  have h2 : CFSG.Open.pRank p (CFSG.pCore p ↥V) = 2 := by
    apply le_antisymm
    · exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hrkV
    · exact two_le_pRank_pCore_of_not_isPGroup hp hp2 hgen hCV hV
  have hns : ¬ CFSG.RankThree.PartTwo.IsSymplecticType ↥(CFSG.pCore p ↥V) := by
    intro hsym
    have h3 := h661 p ↥V hp hp3 hgen hCV hne hsym h2
    omega
  have hrkP : CFSG.Open.pRank p (⊤ : Subgroup ↥(CFSG.pCore p ↥V)) ≤ 2 :=
    (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt
      (CFSG.pCore p ↥V).subtype (CFSG.pCore p ↥V).subtype_injective).trans hrkV
  obtain ⟨A₀, hA₀c, hA₀e, hA₀card⟩ :=
    exists_characteristic_elemAbelian_of_not_isSymplecticType hp CFSG.pCore_isPGroup hrkP hns
  let Psub : Subgroup ↥V := CFSG.pCore p ↥V
  haveI hPsub_char : Psub.Characteristic := CFSG.pCore_characteristic (p := p) (G := ↥V)
  haveI hA₀_char : A₀.Characteristic := hA₀c
  let A₁ : Subgroup ↥V := A₀.map Psub.subtype
  haveI hA₁_char : A₁.Characteristic := inferInstance
  have hA₁e : CFSG.Open.IsElemAbelian p A₁ :=
    CFSG.SectionRank.isElemAbelian_map hA₀e Psub.subtype
  have hA₁card : Nat.card A₁ = p ^ 2 := by
    rw [Subgroup.card_map_of_injective Psub.subtype_injective, hA₀card]
  let A : Subgroup X := A₁.map V.subtype
  have hAnorm : A.Normal := inferInstance
  have hAe : CFSG.Open.IsElemAbelian p A :=
    CFSG.SectionRank.isElemAbelian_map hA₁e V.subtype
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hA₁card]
  exact ⟨A, hAnorm, hAe, hAcard⟩

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
