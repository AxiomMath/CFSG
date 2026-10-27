module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Omega
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup
open scoped commutatorElement Pointwise

namespace P812Hyp

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {L₁ L₂ : Subgroup G}

private theorem commute_of_pow_three (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) :
    u * v = v * u :=
  h.commute_of_pow_three_eq_one hSch hK h714 hSM hS3 hC hu hv hu3 hv3

private theorem pow_three_of_mem_card_three {A : Subgroup G} (hA3 : Nat.card A = 3)
    {a : G} (ha : a ∈ A) : a ^ 3 = 1 := by
  have hdvd : orderOf a ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard A ha
    rwa [hA3] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · rw [orderOf_eq_one_iff.mp h1]
    exact one_pow 3
  · rw [← h3]
    exact pow_orderOf_eq_one a

private theorem inf_eq_bot_of_card_three (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    {A₁ A₂ : Subgroup G} (hA₁ : A₁ ≤ L₁) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) : A₁ ⊓ A₂ = ⊥ := by
  by_contra hne
  have hdvd : Nat.card ↥(A₁ ⊓ A₂) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : A₁ ⊓ A₂ ≤ A₁)
    rwa [hA₁3] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact hne (Subgroup.eq_bot_of_card_eq (H := A₁ ⊓ A₂) h1)
  · have heq : A₁ ⊓ A₂ = A₁ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hA₁3])
    have hleA₂ : A₁ ≤ A₂ := by
      rw [← heq]
      exact inf_le_right
    exact h.not_le_two (A := A₁) hSch hA₁ hA₁3 (hleA₂.trans hA₂)

private theorem inf_zpowers_eq_bot {x : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {E : Subgroup G} (hxE : x ∉ E) : Subgroup.zpowers x ⊓ E = ⊥ := by
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  by_contra hne
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ E) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ E ≤ Subgroup.zpowers x)
    rwa [Nat.card_zpowers, hxord] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact hne (Subgroup.eq_bot_of_card_eq (H := Subgroup.zpowers x ⊓ E) h1)
  · have heq : Subgroup.zpowers x ⊓ E = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hxord])
    apply hxE
    have hxmem : x ∈ Subgroup.zpowers x ⊓ E := by
      rw [heq]
      exact Subgroup.mem_zpowers x
    exact (Subgroup.mem_inf.mp hxmem).2

private theorem isElemAbelian_card_sup (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1) :
    CFSG.Open.IsElemAbelian 3 (A₁ ⊔ A₂) ∧ Nat.card ↥(A₁ ⊔ A₂) = 9 := by
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    exact commute_of_pow_three h hSch hK h714 hSM hS3 hC (hA₁S ha) (hA₂S hb)
      (pow_three_of_mem_card_three hA₁3 ha) (pow_three_of_mem_card_three hA₂3 hb)
  have hbot : A₁ ⊓ A₂ = ⊥ := inf_eq_bot_of_card_three h hSch hA₁ hA₁3 hA₂
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A₁ A₂ hcomm).1
  rw [hbot, hA₁3, hA₂3] at hcard
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₁3)
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₂3) hcomm, ?_⟩
  simpa using hcard

theorem isElemAbelian_zpowers_sup (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1) (hx : x ∉ A₁ ⊔ A₂) :
    CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x ⊔ A₁ ⊔ A₂) ∧
      Nat.card ↥(Subgroup.zpowers x ⊔ A₁ ⊔ A₂) = 27 := by
  have hx1 : x ≠ 1 := by
    intro h1
    apply hx
    rw [h1]
    exact Subgroup.mem_sup_left A₁.one_mem
  have hmemA₁3 : ∀ a ∈ A₁, a ^ 3 = 1 := fun a ha => pow_three_of_mem_card_three hA₁3 ha
  have hmemA₂3 : ∀ a ∈ A₂, a ^ 3 = 1 := fun a ha => pow_three_of_mem_card_three hA₂3 ha
  obtain ⟨hA₁A₂ele, hA₁A₂card⟩ :=
    isElemAbelian_card_sup h hSch hK h714 hSM hS3 hA₁ hA₁S hA₁3 hA₂ hA₂S hA₂3 hC
  have hA₁centx : A₁ ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact commute_of_pow_three h hSch hK h714 hSM hS3 hC hxS (hA₁S hb) hx3
      (hmemA₁3 b hb)
  have hA₂centx : A₂ ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact commute_of_pow_three h hSch hK h714 hSM hS3 hC hxS (hA₂S hb) hx3
      (hmemA₂3 b hb)
  have hcentSup : A₁ ⊔ A₂ ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le hA₁centx hA₂centx
  have hxcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ A₁ ⊔ A₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbx : Commute x b := Subgroup.mem_centralizer_iff.mp (hcentSup hb) x (by simp)
    exact (hbx.zpow_left n).eq
  have hbot : Subgroup.zpowers x ⊓ (A₁ ⊔ A₂) = ⊥ := by
    apply inf_zpowers_eq_bot hx3 hx1
    exact hx
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) (A₁ ⊔ A₂) hxcomm).1
  rw [hbot, Nat.card_zpowers, orderOf_eq_prime hx3 hx1, hA₁A₂card] at hcard
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  refine ⟨?_, ?_⟩
  · rw [sup_assoc]
    exact CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hx3)
      hA₁A₂ele hxcomm
  · rw [sup_assoc]
    simpa [hxord] using hcard

private theorem sup_zpowers_sup_le_centralizer
    {S A₁ A₂ : Subgroup G}
    (hcomm : ∀ u ∈ S, ∀ v ∈ S, u ^ 3 = 1 → v ^ 3 = 1 → u * v = v * u)
    (hA₁S : A₁ ≤ S) (hA₂S : A₂ ≤ S)
    (hA₁3 : Nat.card A₁ = 3) (hA₂3 : Nat.card A₂ = 3)
    {x y : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1) (hyS : y ∈ S) (hy3 : y ^ 3 = 1) :
    (Subgroup.zpowers x ⊔ A₁ ⊔ A₂) ≤ Subgroup.centralizer ({y} : Set G) := by
  have hxcent : Subgroup.zpowers x ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact (hcomm x hxS y hyS hx3 hy3).symm
  have hA₁cent : A₁ ≤ Subgroup.centralizer ({y} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact (hcomm a (hA₁S ha) y hyS (pow_three_of_mem_card_three hA₁3 ha) hy3).symm
  have hA₂cent : A₂ ≤ Subgroup.centralizer ({y} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact (hcomm a (hA₂S ha) y hyS (pow_three_of_mem_card_three hA₂3 ha) hy3).symm
  exact sup_le (sup_le hxcent hA₁cent) hA₂cent

theorem mem_sup_of_pow_three_eq_one (h : P812Hyp G M p L₁ L₂)
    (hSch : CFSG.ComponentClassification.LBalance.SchreierSections ↥M)
    (hK : CFSG.Open.IsKGroup ↥M)
    (h714 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneFourCover)
    {S A₁ A₂ : Subgroup G} (hSM : S ≤ M) (hS3 : IsPGroup 3 S)
    (hA₁ : A₁ ≤ L₁) (hA₁S : A₁ ≤ S) (hA₁3 : Nat.card A₁ = 3)
    (hA₂ : A₂ ≤ L₂) (hA₂S : A₂ ≤ S) (hA₂3 : Nat.card A₂ = 3)
    (hC : ∀ x ∈ S, ⁅Subgroup.zpowers x, L₁⁆ ≤ (CFSG.pPrimeCore p ↥L₁).map L₁.subtype →
      ⁅Subgroup.zpowers x, L₂⁆ ≤ (CFSG.pPrimeCore p ↥L₂).map L₂.subtype → x = 1)
    {x : G} (hxS : x ∈ S) (hx3 : x ^ 3 = 1) (hx : x ∉ A₁ ⊔ A₂)
    {y : G} (hyS : y ∈ S) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers x ⊔ A₁ ⊔ A₂ := by
  let E : Subgroup G := Subgroup.zpowers x ⊔ A₁ ⊔ A₂
  let E' : Subgroup G := E ⊔ Subgroup.zpowers y
  have hE := isElemAbelian_zpowers_sup h hSch hK h714 hSM hS3 hA₁ hA₁S hA₁3
    hA₂ hA₂S hA₂3 hC hxS hx3 hx
  have hEele : CFSG.Open.IsElemAbelian 3 E := hE.1
  have hEcard : Nat.card E = 27 := hE.2
  have hEE' : E ≤ E' := le_sup_left
  have hEcenty : E ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_zpowers_sup_le_centralizer
      (fun u hu v hv hu3 hv3 => commute_of_pow_three h hSch hK h714 hSM hS3 hC hu hv hu3 hv3)
      hA₁S hA₂S hA₁3 hA₂3 hxS hx3 hyS hy3
  have hE'ele : CFSG.Open.IsElemAbelian 3 E' := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hEele
      (CFSG.Open.isElemAbelian_zpowers hy3) ?_
    intro a ha b hb
    have hay : a * y = y * a :=
      ((Subgroup.mem_centralizer_iff.mp (hEcenty ha)) y (by simp)).symm
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (show Commute a y from hay) n).eq
  have hE_leM : E ≤ M := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr (hSM hxS)
    · exact hA₁.trans h.le₁
    · exact hA₂.trans h.le₂
  have hE'leM : E' ≤ M :=
    sup_le hE_leM (Subgroup.zpowers_le.mpr (hSM hyS))
  have hE'card : Nat.card E' = 3 ^ CFSG.Open.pRank 3 E' :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hE'ele
  have hE'rank : CFSG.Open.pRank 3 E' ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.pRank_mono (by norm_num) hE'leM
  have hE'cardle : Nat.card E' ≤ 27 := by
    rw [hE'card]
    calc 3 ^ CFSG.Open.pRank 3 E'
        ≤ 3 ^ CFSG.Open.pRank 3 M := Nat.pow_le_pow_right (by norm_num) hE'rank
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) h.rank_three
      _ = 27 := by norm_num
  have hEcard_le : Nat.card E ≤ Nat.card E' := Subgroup.card_le_of_le hEE'
  have hE'cardeq : Nat.card E' = 27 :=
    le_antisymm hE'cardle (by rw [← hEcard]; exact hEcard_le)
  have hEEq : E = E' :=
    Subgroup.eq_of_le_of_card_ge hEE' (by rw [hE'cardeq, hEcard])
  have hyE' : y ∈ E' := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rwa [← hEEq] at hyE'


end P812Hyp
end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
