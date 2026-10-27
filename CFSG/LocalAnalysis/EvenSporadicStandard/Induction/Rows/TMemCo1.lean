module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Stage3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Lemma36

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard.Induction.TMem


theorem co1_isConj_a₁_of_centralizes {X : Type} [Group X] [Finite X] (f : X ≃* GA)
    {K' : Subgroup X} (hKcard : Nat.card K' = 251596800) {s : X} (hs2 : orderOf s = 2)
    (hKs : K' ≤ Subgroup.centralizer ({s} : Set X)) : IsConj (f s) a₁ := by
  have hdvd : 251596800 ∣ Nat.card (Subgroup.centralizer ({s} : Set X)) := by
    have := Subgroup.card_dvd_of_le hKs
    rwa [hKcard] at this
  have hs2' : orderOf (f s) = 2 := by rw [MulEquiv.orderOf_eq, hs2]
  have hdvd' : 251596800 ∣ Nat.card (Subgroup.centralizer ({f s} : Set GA)) := by
    rw [← card_centralizer_eq_of_mulEquiv_sub GA f]
    exact hdvd
  exact co1_isConj_a₁ hs2' hdvd'

theorem co1_conj_u {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Co1) (hQ : Co1Pair H L K u) :
    ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) → ∃ x ∈ L, x * u * x⁻¹ = w := by
  intro w hwL hw2 hwK
  obtain ⟨f⟩ := co1_equiv_GA hL
  have hcard : Nat.card (K.subgroupOf L) = 251596800 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv).trans hQ.2.2.2.2.2
  have hu2 : orderOf (⟨u, hQ.1⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hQ.2.1
  have hw2' : orderOf (⟨w, hwL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hw2
  have hKu : K.subgroupOf L ≤ Subgroup.centralizer ({(⟨u, hQ.1⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hQ.2.2.2.1 k (Subgroup.mem_subgroupOf.1 hk))
  have hKw : K.subgroupOf L ≤ Subgroup.centralizer ({(⟨w, hwL⟩ : ↥L)} : Set ↥L) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (hwK k (Subgroup.mem_subgroupOf.1 hk))
  have h1 := co1_isConj_a₁_of_centralizes f hcard hu2 hKu
  have h2 := co1_isConj_a₁_of_centralizes f hcard hw2' hKw
  obtain ⟨c, hc⟩ := isConj_iff.1 (h1.trans h2.symm)
  refine ⟨((f.symm c : ↥L) : H), (f.symm c).2, ?_⟩
  have h4 : f ((f.symm c) * ⟨u, hQ.1⟩ * (f.symm c)⁻¹) = f ⟨w, hwL⟩ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  exact congrArg Subtype.val (f.injective h4)

theorem co1_small {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Co1) (hQ : Co1Pair H L K u) :
    ∀ S : Subgroup H, S ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥S →
      Nat.card ↥S < 2 ^ twoAdic K := by
  intro S hS hS2
  obtain ⟨f⟩ := co1_equiv_GA hL
  have hperf : Group.IsPerfect ↥K := hQ.2.2.2.2.1
  have hKperf' : Group.IsPerfect ↥(K.subgroupOf L) := isPerfect_subgroupOf hQ.2.2.1
  have hcard : Nat.card (K.subgroupOf L) = 251596800 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ.2.2.1).toEquiv).trans hQ.2.2.2.2.2
  have hSL : S ≤ L := hS.trans inf_le_left
  have hSp : IsPGroup 2 ↥(S.subgroupOf L) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  have hSK : ∀ s ∈ S.subgroupOf L, ∀ k ∈ K.subgroupOf L, s * k = k * s := by
    intro s hs k hk
    have := mem_centralizer_iff.1 (hS (mem_subgroupOf.1 hs)).2 (k : H) (mem_subgroupOf.1 hk)
    exact Subtype.ext this.symm
  have h4 := co1_two_subgroup_le f hKperf' hcard hSp hSK
  have h5 : Nat.card ↥S = Nat.card ↥(S.subgroupOf L) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv).symm
  refine lt_two_pow_twoAdic (m := 3) ?_ (by omega)
  rw [hQ.2.2.2.2.2]
  norm_num

theorem tMemOfNotMax_co1_proved (hmult : OddMultTrivial .Co1) :
    TMemOfNotMax [.Co1] (fun _ => Co1Pair) := by
  intro s hs H _ _ N L K t u hcov hhyp hQ hnm
  rcases List.mem_singleton.1 hs with rfl
  by_contra htN
  have hL : IsSporadic ↥L .Co1 := hcov.isSporadic_of_mult hmult
  have hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l := fun α =>
    TwoCo1.HypOne.allInner_of_isSporadic hL α
  have hKq : CFSG.Open.IsQuasisimple ↥K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1).1
      (co1_rowIsK hmult .Co1 (List.mem_singleton_self _) H L K u hcov hQ).1
  have D : TMemData H N L K u :=
    TMemData.of_inner hhyp htN hQ.1 hinn hQ.2.2.2.2.1 hQ.2.2.2.1 (co1_conj_u hL hQ)
      (fun _ hK''L hK''u hperf hcard => co1_perfect_unique hL hQ hK''L hK''u hperf hcard)
  exact hnm (D.maximal hKq (co1_small hL hQ))

end CFSG.EvenSporadicStandard.Induction
