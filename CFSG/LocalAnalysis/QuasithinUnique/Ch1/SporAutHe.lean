module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterClass
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.ComponentClassification.OuterAutomorphisms

theorem he_outer_fixSub_card
    (α : MulAut heP) (hα2 : α * α = 1) (hα : α ∉ inner heP) :
    Nat.card (CFSG.Sporadic.Schreier.fixSub α) ∈ ({15120} : Set ℕ) := by
  have hα1 : α ≠ 1 := fun h => hα (h ▸ (inner heP).one_mem)
  have hord : orderOf α = 2 := orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  obtain ⟨x, hx, hxP, hx2⟩ :=
    exists_heConjR_eq ctbh_full_automorphism_permutation_model.1 α hord hα
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  have e1 := fixedSubgroupEquivOfConj x hg heAutU hxg
  have hfix : CFSG.Sporadic.Schreier.fixSub α =
      CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup (heConjR x) := by
    rw [hx]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [Set.mem_singleton_iff, hfix, Nat.card_congr e1.toEquiv]
  exact card_heP_centralizer_heAutU

theorem heAutInner
    (K : Type) [Group K] [Finite K] (hK : Nonempty (K ≃* NativeSporadic.He))
    (β : K ≃* K) (hβ : ∀ x, β (β x) = x)
    (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  obtain ⟨e⟩ := hK
  refine autInner_of_equiv_of_outer_card (e.trans heEquivP) (m := 4030387200)
    (by rw [Nat.card_congr (e.trans heEquivP).toEquiv, card_heP]) (S := {15120}) ?_
    (fun α hα2 hα => he_outer_fixSub_card α hα2 hα) β hβ hP
  intro c hc k i hk hki
  rw [Set.mem_singleton_iff] at hc
  subst hc
  have hk4 : k ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ∣ 15120 := dvd_trans (pow_dvd_pow 2 (by omega)) hk
    omega
  interval_cases k <;> omega

end CFSG.QuasithinUnique.Ch1
