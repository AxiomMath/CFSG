module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedReps
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81ExTransport
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedCent

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
  CFSG.ComponentClassification.RankTwoExceptional.Exc
  CFSG.LieType.Chevalley.E6GraphHighestRoot

set_option linter.unusedSectionVars false


theorem prod_zpow_eq_zpow_sum_ex {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

variable {K : Type} [Field K]

theorem frameTorusElt_highRoot_E6_eq (ε : Kˣ) :
    frameTorusElt TwistTag.E6.tag K (highRoot TwistTag.E6.tag) ε =
      rootDiagUnit TwistTag.E6.tag (fun i => ε ^ (Pi.single (e6Idx 1) (1 : ℤ) :
        Fin TwistTag.E6.tag.rank → ℤ) i) := by
  rw [frameTorusElt_E6_eq_rootDiagUnit]
  congr 1
  funext l
  simp only [cartanChar, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum_ex]
  congr 1
  revert l
  decide

theorem twe6_exists_order_eightynine_commute [Finite K] [CharP K 2] {f : ℕ}
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hσσ : ∀ c, σ.toRingHom (σ.toRingHom c) = c) {ε : Kˣ} (hε : orderOf ε = 89)
    (h89 : 89 ∣ 2 ^ f - 1) :
    ∀ y ∈ twReps σ.toRingHom hσσ, ∃ z : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      orderOf z = 89 ∧ Commute z y := by
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  have hεq : ε ^ (2 ^ f - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hε ▸ h89)
  have ha : Units.map σ.toRingHom.toMonoidHom ε = ε := by
    refine Units.ext ?_
    have h1 : (ε : K) ^ (2 ^ f - 1) = 1 := by
      have := congrArg Units.val hεq
      simpa using this
    have h2 : 2 ^ f - 1 + 1 = 2 ^ f := Nat.sub_add_cancel Nat.one_le_two_pow
    calc σ.toRingHom (ε : K) = (ε : K) ^ 2 ^ f := hσ _
      _ = (ε : K) ^ (2 ^ f - 1) * ε := by rw [← pow_succ, h2]
      _ = ε := by rw [h1, one_mul]
  have hγ : permLattice TwistTag.E6.perm (highRoot TwistTag.E6.tag) = highRoot TwistTag.E6.tag := by
    decide +kernel
  have hmem := frameTorusElt_mem_graphFixedRootGroup σ.toRingHom hγ ha
  have h0 : ∀ β ∈ frT ++ frU ++ frV, β (e6Idx 1) = 0 := by decide
  have hroots : ∀ β ∈ frT ++ frU ++ frV, IsRoot TwistTag.E6.tag β := by
    intro β hβ
    simp only [frT, frU, frV, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hβ
    rcases hβ with (rfl | rfl | rfl) | rfl | rfl | rfl <;> exact isRoot_single _ _
  have key : ∀ F : List (Fin TwistTag.E6.tag.rank → ℤ), (∀ β ∈ F, β ∈ frT ++ frU ++ frV) →
      ∀ (y : graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        (y : ModGL TwistTag.E6.tag K) = (F.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod →
      ∃ z : graphFixedRootGroup TwistTag.E6 K σ.toRingHom, orderOf z = 89 ∧ Commute z y := by
    intro F hF y hy
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk, frameTorusElt_highRoot_E6_eq]
      exact orderOf_rootDiagUnit_eq_prime hε _ (e6Idx 1) (by decide)
    · have hc := (commute_rootDiagUnit_single_framePt (e6Idx 1) F
        (fun β hβ => hroots β (hF β hβ)) (fun β hβ => h0 β (hF β hβ)) ε).eq
      rw [← hy, ← frameTorusElt_highRoot_E6_eq] at hc
      exact Subtype.ext hc
  intro y hy
  simp only [twReps, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · exact key frT (fun β hβ => List.mem_append_left _ (List.mem_append_left _ hβ)) _ rfl
  · exact key frU (fun β hβ => List.mem_append_left _ (List.mem_append_right _ hβ)) _ rfl
  · exact key frV (fun β hβ => List.mem_append_right _ hβ) _ rfl

theorem lie23To89At_twistedE6 : Lie23To89At .twistedE6 := by
  intro X _ _ n f hadm hM τ hτ h23
  have hn : n = 0 := hadm.2.2
  subst hn
  have h11 : 11 ∣ f := eleven_dvd_of_twentythree_dvd_card (by simp) hadm hM
    (dvd_trans h23 (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨-, K, _, _, hcard, σ, hσ, ⟨e⟩⟩ := hM.chevalleyExceptionalModel (by decide)
  have hcard1 : Nat.card K = (2 ^ f) ^ 2 := hcard
  have hcard2 : Nat.card K = 2 ^ (f * 2) := by rw [hcard1, ← pow_mul]
  have hK2 : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two (by have := hadm.2.1; omega)
      hcard2
  haveI : CharP K 2 := ringChar.of_eq hK2
  obtain ⟨σE, rfl⟩ : ∃ σE : K ≃+* K, σE.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
      RingHom.ext fun _ => rfl⟩
  obtain ⟨E⟩ := nonempty_derivedCentralQuotient_equiv .E6 Nat.prime_two hadm.2.1 K hcard
    σE.toRingHom hσ
  have hσσ : ∀ c, σE.toRingHom (σE.toRingHom c) = c := by
    intro c
    haveI : Fintype K := Fintype.ofFinite K
    have hc : Fintype.card K = 2 ^ f * 2 ^ f := by
      rw [← Nat.card_eq_fintype_card, hcard1, sq]
    rw [hσ, hσ, ← pow_mul, ← hc]
    exact FiniteField.pow_card c
  have h89 : 89 ∣ 2 ^ f - 1 := (eightynine_dvd_two_pow_sub_one_iff f).2 h11
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_eightynine (K := K) (by
    rw [hcard1]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
    rw [one_pow] at this
    exact h89.trans this)
  haveI : Fact (Nat.Prime 89) := ⟨by norm_num⟩
  exact prime_dvd_card_centralizer_of_classesCover (e.trans E)
    (classesCover_twReps hadm.2.1 hcard1 hσ hσσ)
    (twe6_exists_order_eightynine_commute σE hσ hσσ hε h89) hτ

end CFSG.ComponentClassification.CatFC.DS81.Ex
