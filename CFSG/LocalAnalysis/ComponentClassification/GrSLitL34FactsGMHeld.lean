module

public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.ComponentClassification.GrSLit.L34GM

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.FixedCommutingProduct


theorem card_fixedSubgroup_le_of_heP {S : Type*} [Group S] (θ : S ≃* heP) (α : MulAut S)
    (hα : orderOf α = 2) : Nat.card (fixedSubgroup α) ≤ 161280 := by
  have hβ : orderOf (MulAut.congr θ α) = 2 := by rw [orderOf_congr, hα]
  by_cases hinn : MulAut.congr θ α ∈ (MulAut.conj : heP →* MulAut heP).range
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center heP_center_eq_bot) t, ht, hβ]
    let f : fixedSubgroup α ≃* centralizer ({t} : Set heP) :=
      (fixedSubgroupCongr θ α).trans (MulEquiv.subgroupCongr (by rw [← ht, fixedSubgroup_conj]))
    rw [Nat.card_congr (f.trans (heCentralizerEquiv t)).toEquiv]
    rcases involution_conj_cases t.2 (by rw [Subgroup.orderOf_coe]; exact ht2) with
      ⟨c, hc, hct⟩ | ⟨c, hc, hct⟩
    · have e : ↥(centralizerIn heP (t : Equiv.Perm (Fin 8330))) ≃*
          ↥(centralizerIn heP (heGenPerm 0)) :=
        (MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans (infCentralizerConjEquiv hc _)
      rw [Nat.card_congr e.toEquiv, card_heP_cent0]
    · have e : ↥(centralizerIn heP (t : Equiv.Perm (Fin 8330))) ≃*
          ↥(centralizerIn heP heT1P) :=
        (MulEquiv.subgroupCongr (by rw [hct]; rfl)).trans (infCentralizerConjEquiv hc _)
      rw [Nat.card_congr e.toEquiv, card_heP_cent1]
      norm_num
  · obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq ctbh_full_automorphism_permutation_model.1
      (MulAut.congr θ α) hβ hinn
    obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
    have e : fixedSubgroup α ≃* (heP ⊓ centralizer {heAutU} : Subgroup (Equiv.Perm (Fin 8330))) :=
      ((fixedSubgroupCongr θ α).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
        (fixedSubgroupEquivOfConj x hg heAutU hxg)
    rw [Nat.card_congr e.toEquiv, card_heP_centralizer_heAutU]
    norm_num

theorem card_fixedSubgroup_le_of_he {S : Type*} [Group S]
    (e : S ≃* Blueprint.NativeSporadic.He) (α : MulAut S) (hα : orderOf α = 2) :
    Nat.card (fixedSubgroup α) ≤ 161280 :=
  card_fixedSubgroup_le_of_heP (e.trans heEquivP) α hα

theorem index_le_of_he {S : Type*} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.He)
    {α : MulAut S} (hα : orderOf α = 2) {P : Subgroup S} (hP : P ≤ fixedSubgroup α) :
    (pPrimeCore 2 ↥P).index ≤ 161280 := by
  have h1 := (pPrimeCore 2 ↥P).index_mul_card
  have h2 : Nat.card ↥P ≤ Nat.card ↥(fixedSubgroup α) := Subgroup.card_le_of_le hP
  have h3 := card_fixedSubgroup_le_of_he e α hα
  have h4 : 0 < Nat.card ↥(pPrimeCore 2 ↥P) := Nat.card_pos
  nlinarith

end CFSG.ComponentClassification.GrSLit.L34GM
