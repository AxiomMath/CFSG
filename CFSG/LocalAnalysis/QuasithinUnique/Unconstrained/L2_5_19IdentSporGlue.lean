module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open scoped commutatorElement

section Commutators

variable {M : Type*} [Group M]

theorem commutator_closure_le (S : Set M) (A : Subgroup M)
    (hn : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A ∧ s⁻¹ * a * s ∈ A)
    (hc : ∀ s ∈ S, ∀ s' ∈ S, ⁅s, s'⁆ ∈ A) :
    ⁅Subgroup.closure S, Subgroup.closure S⁆ ≤ A := by
  have hN : Subgroup.closure S ≤ Subgroup.normalizer (A : Set M) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => (hn s hs h hh).1, fun hh => ?_⟩
    have := (hn s hs _ hh).2
    simpa [mul_assoc] using this
  have hconj : ∀ g ∈ Subgroup.closure S, ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
    fun g hg a ha => ((Subgroup.mem_normalizer_iff.1 (hN hg)) a).1 ha
  have h1 : ∀ s ∈ S, ∀ h ∈ Subgroup.closure S, ⁅s, h⁆ ∈ A := by
    intro s hs h hh
    induction hh using Subgroup.closure_induction with
    | mem x hx => exact hc s hs x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : ⁅s, x * y⁆ = ⁅s, x⁆ * (x * ⁅s, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact A.mul_mem ihx (hconj x hx _ ihy)
    | inv x hx ihx =>
      have e : ⁅s, x⁻¹⁆ = x⁻¹ * (⁅s, x⁆)⁻¹ * (x⁻¹)⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact hconj x⁻¹ (Subgroup.inv_mem _ hx) _ (A.inv_mem ihx)
  rw [Subgroup.commutator_le]
  intro g hg h hh
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx h hh
  | one => simp
  | mul x y hx hy ihx ihy =>
    have e : ⁅x * y, h⁆ = x * ⁅y, h⁆ * x⁻¹ * ⁅x, h⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact A.mul_mem (hconj x hx _ ihy) ihx
  | inv x hx ihx =>
    have e : ⁅x⁻¹, h⁆ = x⁻¹ * (⁅x, h⁆)⁻¹ * (x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hconj x⁻¹ (Subgroup.inv_mem _ hx) _ (A.inv_mem ihx)

end Commutators

section Components

theorem normal_le_center_or_eq_top' {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  have := hperf
  have := hs
  let quotient := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map quotient).Normal :=
    Subgroup.Normal.map inferInstance quotient (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ quotient.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq quotient N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact top_unique hderived

theorem subnormal_le_center_or_eq_top' {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) (hN : N.IsSubnormal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  rcases Subgroup.IsSubnormal.lt_normal hN with htop | ⟨K, hKnorm, hNK, hKlt⟩
  · exact Or.inr htop
  · left
    rcases normal_le_center_or_eq_top' hperf hs K with hKc | hKtop
    · exact hNK.trans hKc
    · exact absurd hKtop hKlt.ne

theorem not_hasKComponent_of_commutator_quasisimple {Q : Type*} [Group Q]
    (hq : CFSG.IsQuasisimple ↥(commutator Q)) (h : ¬ KOrder (Nat.card ↥(commutator Q))) :
    ¬ HasKComponent Q := by
  rintro ⟨B, hB, hK⟩
  have hBle : B ≤ commutator Q := le_commutator_of_isQuasisimple hB.1
  have hcomp := CFSG.LocalCores.component_overgroup hB hBle
  rcases subnormal_le_center_or_eq_top' hq.1 hq.2.1 (B.subgroupOf (commutator Q)) hcomp.2 with
    hc | htop
  · exfalso
    have hperf : Group.IsPerfect ↥(B.subgroupOf (commutator Q)) := hcomp.1.1
    have hbot := CFSG.ComponentClassification.Quasisimple.perfect_le_center_eq_bot
      (B.subgroupOf (commutator Q)) hc
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hcomp.1
    obtain ⟨⟨x, hx⟩, hx1⟩ := (nontrivial_iff_exists_ne (1 : ↥(B.subgroupOf (commutator Q)))).mp hnt
    exact hx1 (Subtype.ext (by simpa [hbot] using hx))
  · have hBeq : B = commutator Q := le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
    rw [hBeq] at hK
    exact h hK

end Components

section Orders

theorem KOrder.eq_of_dvd_2880 {n : ℕ} (hn : KOrder n) (hd : n ∣ 2880) : n = 360 := by
  rcases hn with rfl | rfl | ⟨p, hp, h7, hpn⟩
  · exfalso
    norm_num at hd
  · rfl
  · exfalso
    have h17 := seventeen_le_of_isFermatOrMersenne hp h7
    have h1 : p ∣ 2 * 2880 := by
      have : p ∣ p * (p * p - 1) := dvd_mul_right p _
      rw [hpn] at this
      exact this.trans (Nat.mul_dvd_mul_left 2 hd)
    have e : 2 * 2880 = 2 ^ 7 * (3 ^ 2 * 5) := by norm_num
    rw [e] at h1
    have hpp := hp.1
    rcases (Nat.Prime.dvd_mul hpp).1 h1 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h)
      omega
    · rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 (hpp.dvd_of_dvd_pow h)
        omega
      · have := Nat.le_of_dvd (by norm_num) h
        omega

theorem KOrder.false_of_dvd {n N : ℕ} (hn : KOrder n) (hd : n ∣ N) (h168 : ¬ 168 ∣ N)
    (h360 : ¬ 360 ∣ N) (hp : ∀ p : ℕ, p.Prime → 17 ≤ p → ¬ p ∣ 2 * N) : False := by
  rcases hn with rfl | rfl | ⟨p, hFM, h7, hpn⟩
  · exact h168 hd
  · exact h360 hd
  · refine hp p hFM.1 (seventeen_le_of_isFermatOrMersenne hFM h7) ?_
    have h1 : p ∣ p * (p * p - 1) := dvd_mul_right p _
    rw [hpn] at h1
    exact h1.trans (Nat.mul_dvd_mul_left 2 hd)

end Orders

end CFSG.QuasithinUnique.Id2519
