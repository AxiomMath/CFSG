module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b
open CFSG.Quasithin (perfectCore)

variable {G : Type} [Group G]

@[expose] def RigidCore (A : Subgroup G) (p : G) (Y : Subgroup G) : Prop :=
  ∀ k : G, rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) k =
      perfectCore (A ⊓ centralizer ({p} : Set G)) →
    rightConjugate Y k ≤ normalizer (A : Set G) →
    rightConjugate Y k ≤ centralizer ({p} : Set G) →
      NoNormalTwo (A ⊓ centralizer (rightConjugate Y k : Set G))

theorem rightConjugate_normalizer_eq_normalizer (H : Subgroup G) (k : G) :
    rightConjugate (normalizer (H : Set G)) k = normalizer (rightConjugate H k : Set G) :=
  map_equiv_normalizer_eq H (MulAut.conj k⁻¹)

theorem noNormalTwo_rightConjugate {H : Subgroup G} (h : NoNormalTwo H) (k : G) :
    NoNormalTwo (rightConjugate H k) := by
  intro Q hQ h2 hN
  have hQ' : rightConjugate Q k⁻¹ ≤ H := by
    rw [← rightConjugate_rightConjugate_inv H k]
    exact rightConjugate_le_rightConjugate_iff.mpr hQ
  have hN' : H ≤ normalizer (rightConjugate Q k⁻¹ : Set G) := by
    rw [← rightConjugate_normalizer_eq_normalizer, ← rightConjugate_rightConjugate_inv H k]
    exact rightConjugate_le_rightConjugate_iff.mpr hN
  have h := h _ hQ' (h2.map _) hN'
  rw [← rightConjugate_inv_rightConjugate Q k, h]
  exact map_bot _

variable [Finite G]

theorem isSylowOf_of_le_of_card_eq {S A B : Subgroup G} (hS : IsSylowOf 2 S A) (hSB : S ≤ B)
    (hAB : Nat.card B = Nat.card A) : IsSylowOf 2 S B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_card hSB (by rw [hS.card_eq, hAB])

theorem isSylowOf_rightConjugate_two {S B : Subgroup G} (hS : IsSylowOf 2 S B) (g : G) :
    IsSylowOf 2 (rightConjugate S g) (rightConjugate B g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_card (rightConjugate_le_rightConjugate_iff.mpr hS.le)
    (by rw [rightConjugate_card, rightConjugate_card, hS.card_eq])

theorem mem_of_le_centralizer_of_isSylowOf {S B : Subgroup G} (hS : IsSylowOf 2 S B) {z : G}
    (hzB : z ∈ B) (hz : orderOf z = 2) (hSz : S ≤ centralizer ({z} : Set G)) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz,
    pow_one])
  have hzC : z ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hSz hs)
  have hzN : zpowers z ≤ normalizer (S : Set G) :=
    (zpowers_le.mpr hzC).trans (centralizer_le_normalizer S)
  have hQ := hS.isPGroup.to_sup_of_normal_left' hZ hzN
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le (zpowers_le.mpr hzB)) hQ
  rw [← heq]
  exact mem_sup_right (mem_zpowers z)

theorem leviRigid_of_rigidCore {A : Subgroup G} {p : G} {Y : Subgroup G}
    (hS : ∃ S : Subgroup G, IsSylowOf 2 S A ∧
      S ≤ perfectCore (A ⊓ centralizer ({p} : Set G)))
    (hconj : ∀ z ∈ A, orderOf z = 2 →
      (∃ S : Subgroup G, IsSylowOf 2 S A ∧ S ≤ centralizer ({z} : Set G)) →
        ∃ a ∈ A, a * z * a⁻¹ = p)
    (hcen : ∀ z ∈ A, orderOf z = 2 →
      z ∈ centralizer (perfectCore (A ⊓ centralizer ({p} : Set G)) : Set G) →
        Y ≤ centralizer ({z} : Set G))
    (hcore : RigidCore A p Y) : LeviRigid A p Y := by
  intro h p' hp' hp'2 hYN heq
  obtain ⟨S, hSA, hSX⟩ := hS
  have hXB : perfectCore (A ⊓ centralizer ({p} : Set G)) ≤
      rightConjugate A h ⊓ centralizer ({p'} : Set G) := by
    rw [heq]
    exact CFSG.Quasithin.perfectCore_le _
  have hSC : S ≤ centralizer ({p'} : Set G) := (hSX.trans hXB).trans inf_le_right
  have hSB : IsSylowOf 2 S (rightConjugate A h) :=
    isSylowOf_of_le_of_card_eq hSA ((hSX.trans hXB).trans inf_le_left) (rightConjugate_card A h)
  have hp'S : p' ∈ S := mem_of_le_centralizer_of_isSylowOf hSB hp' hp'2 hSC
  have hp'X : p' ∈ centralizer (perfectCore (A ⊓ centralizer ({p} : Set G)) : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hXB hx).2
  have hYp' := hcen p' (hSA.le hp'S) hp'2 hp'X
  have hp₂ : h * p' * h⁻¹ ∈ A := (mem_rightConjugate_iff A h p').mp hp'
  have hp₂2 : orderOf (h * p' * h⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hp'2
  have hS₂ : IsSylowOf 2 (rightConjugate S h⁻¹) A := by
    have := isSylowOf_rightConjugate_two hSB h⁻¹
    rwa [rightConjugate_rightConjugate_inv] at this
  have hS₂C : rightConjugate S h⁻¹ ≤ centralizer ({h * p' * h⁻¹} : Set G) := by
    have := rightConjugate_le_rightConjugate_iff (x := h⁻¹).mpr hSC
    rwa [rightConjugate_centralizer_singleton, inv_inv] at this
  obtain ⟨a, haA, hap⟩ := hconj _ hp₂ hp₂2 ⟨_, hS₂, hS₂C⟩
  have hBk : rightConjugate (rightConjugate A h) (a * h)⁻¹ = A := by
    rw [rightConjugate_mul, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul,
      rightConjugate_eq_self_iff]
    exact Subgroup.le_normalizer (inv_mem haA)
  have hpk : ((a * h)⁻¹)⁻¹ * p' * (a * h)⁻¹ = p := by
    rw [inv_inv, ← hap]
    group
  have hXk : rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) (a * h)⁻¹ =
      perfectCore (A ⊓ centralizer ({p} : Set G)) := by
    conv_lhs => rw [heq]
    rw [rightConjugate_perfectCore, rightConjugate_inf, hBk,
      rightConjugate_centralizer_singleton, hpk]
  have hYk₁ : rightConjugate Y (a * h)⁻¹ ≤ normalizer (A : Set G) := by
    rw [← hBk, ← rightConjugate_normalizer_eq_normalizer]
    exact rightConjugate_le_rightConjugate_iff.mpr hYN
  have hYk₂ : rightConjugate Y (a * h)⁻¹ ≤ centralizer ({p} : Set G) := by
    rw [← hpk, ← rightConjugate_centralizer_singleton]
    exact rightConjugate_le_rightConjugate_iff.mpr hYp'
  have hNN := noNormalTwo_rightConjugate (hcore _ hXk hYk₁ hYk₂) (a * h)⁻¹⁻¹
  rw [rightConjugate_inf, centralizer_rightConjugate, rightConjugate_rightConjugate_inv] at hNN
  rwa [← hBk, rightConjugate_rightConjugate_inv] at hNN

end CFSG.ComponentClassification.RankTwoClassical
