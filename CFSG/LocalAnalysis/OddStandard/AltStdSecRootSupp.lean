module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecDichP2

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

theorem rootSupp_support_card_of_involution {α : Type*} [Fintype α] [DecidableEq α] {t : Perm α}
    (ht : orderOf t = 2) (hs : Perm.sign t = 1) : t.support.card = 4 ∨ 8 ≤ t.support.card := by
  have hcyc : ∀ n ∈ t.cycleType, n = 2 := fun n hn => by
    have h1 := Perm.dvd_of_mem_cycleType hn
    have h2 := Perm.two_le_of_mem_cycleType hn
    rw [ht] at h1
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2
  obtain ⟨c, hrep⟩ : ∃ c, t.cycleType = Multiset.replicate c 2 :=
    ⟨_, Multiset.eq_replicate_card.2 hcyc⟩
  have hsum : t.support.card = 2 * c := by
    rw [← Perm.sum_cycleType, hrep, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hne : t ≠ 1 := by
    rintro rfl
    simp at ht
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (Perm.cycleType_eq_zero.1 (by rw [hrep]; rfl))
  have hsign := Perm.sign_of_cycleType t
  rw [hrep, hs, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hpow : (-1 : ℤˣ) ^ c = 1 := by
    have h2 : (-1 : ℤˣ) ^ (c * 2 + c) = (-1 : ℤˣ) ^ c := by
      rw [pow_add, pow_mul]; simp
    rw [← h2]; exact hsign.symm
  have heven : Even c := (neg_one_pow_eq_one_iff_even (by decide)).1 hpow
  obtain ⟨k, hk⟩ := heven
  omega

section Aux

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem rootSupp_dvd_support_card_of_orderOf_prime {σ : Perm α} {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) : p ∣ σ.support.card := by
  rw [← Perm.sum_cycleType]
  refine Multiset.dvd_sum fun n hn => ?_
  have h1 := Perm.dvd_of_mem_cycleType hn
  have h2 := Perm.two_le_of_mem_cycleType hn
  rw [hσ] at h1
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · omega
  · rw [h]

theorem rootSupp_comm_of_mem_altSub_compl {t w : Perm α}
    (hw : w ∈ altSub (t.support)ᶜ) : w * t = t * w := by
  have hfix := (mem_altSub.1 hw).2
  refine Perm.Disjoint.commute (fun x => ?_)
  by_cases hx : t x = x
  · exact Or.inr hx
  · exact Or.inl (hfix x (by simpa using hx))

theorem rootSupp_mem_normalizer_of_comm {t σ : Perm α} (h : σ * t = t * σ) :
    σ ∈ normalizer ((altSub (t.support)ᶜ : Subgroup (Perm α)) : Set (Perm α)) := by
  refine mem_normalizer_altSub fun i => ?_
  simp only [Finset.mem_compl, Perm.mem_support]
  exact not_congr (comm_apply_ne_iff h i).symm

theorem rootSupp_twelve_lt_card_altSub {S : Finset α} (hS : 8 ≤ S.card) :
    12 < Nat.card (altSub S) := by
  have h := Nat.card_congr (altSubEquiv S).toEquiv
  have : Nontrivial (Fin S.card) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [h, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h8 : (8 : ℕ).factorial ≤ S.card.factorial := Nat.factorial_le hS
  have h40 : (8 : ℕ).factorial = 40320 := by decide
  omega

theorem rootSupp_false_of_order_three {t σ : Perm α} (ht : t * t = 1)
    (hsupp : t.support.card = 4) (hσ3 : orderOf σ = 3) (hcomm : σ * t = t * σ)
    (hfix : ∀ i, i ∉ t.support → σ i = i) : False := by
  have hsub : σ.support ⊆ t.support := fun i hi => by
    by_contra hit
    exact (Perm.mem_support.1 hi) (hfix i hit)
  have hdvd : 3 ∣ σ.support.card := rootSupp_dvd_support_card_of_orderOf_prime Nat.prime_three hσ3
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    simp at hσ3
  have hpos : σ.support.card ≠ 0 := fun h => hσ1 (Perm.card_support_eq_zero.1 h)
  have hle : σ.support.card ≤ 4 := hsupp ▸ Finset.card_le_card hsub
  have h3 : σ.support.card = 3 := by omega
  have hdiff : (t.support \ σ.support).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hsupp, h3]
  obtain ⟨q, hq⟩ := Finset.card_eq_one.1 hdiff
  have hqmem : q ∈ t.support \ σ.support := by rw [hq]; exact Finset.mem_singleton_self q
  obtain ⟨hqt, hqσ⟩ := Finset.mem_sdiff.1 hqmem
  have hσq : σ q = q := by simpa using hqσ
  have htq : t q ≠ q := Perm.mem_support.1 hqt
  have htt : t (t q) = q := by simpa using congrArg (fun f : Perm α => f q) ht
  have hmem : t q ∈ t.support \ σ.support := by
    refine Finset.mem_sdiff.2 ⟨Perm.mem_support.2 ?_, ?_⟩
    · rw [htt]; exact htq.symm
    · have h1 : σ (t q) = t (σ q) := by simpa using congrArg (fun f : Perm α => f q) hcomm
      rw [Perm.mem_support, not_not, h1, hσq]
  rw [hq, Finset.mem_singleton] at hmem
  exact htq hmem

end Aux

section Normal

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem rootSupp_inf_altSub_eq_bot {t : Perm α} (hZ : 8 ≤ (t.support)ᶜ.card)
    {X : Subgroup (Perm α)}
    (hXn : ∀ c ∈ centralizer ({t} : Set (Perm α)), c ∈ alternatingGroup α →
      ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hX12 : Nat.card X ≤ 12) : X ⊓ altSub (t.support)ᶜ = ⊥ := by
  set W : Subgroup (Perm α) := altSub (t.support)ᶜ with hW
  have hWC : ∀ w ∈ W, w ∈ centralizer ({t} : Set (Perm α)) := fun w hw =>
    mem_centralizer_singleton_iff.2 (rootSupp_comm_of_mem_altSub_compl hw)
  have hWA : ∀ w ∈ W, w ∈ alternatingGroup α := fun w hw => altSub_le_alternatingGroup _ hw
  have hnormal : ((X ⊓ W).subgroupOf W).Normal := by
    refine ⟨fun k hk w => ?_⟩
    have hk' : (k : Perm α) ∈ X ⊓ W := hk
    obtain ⟨hkX, -⟩ := Subgroup.mem_inf.1 hk'
    exact Subgroup.mem_inf.2 ⟨hXn _ (hWC _ w.2) (hWA _ w.2) _ hkX, (w * k * w⁻¹).2⟩
  have hsimple : IsSimpleGroup W := isSimpleGroup_of_alt (by omega) (altSubEquiv (t.support)ᶜ)
  rcases hsimple.eq_bot_or_eq_top_of_normal ((X ⊓ W).subgroupOf W) with hD | hD
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨-, hxW⟩ := Subgroup.mem_inf.1 hx
    have h1 : (⟨x, hxW⟩ : W) ∈ (X ⊓ W).subgroupOf W := hx
    rw [hD] at h1
    have h2 : (⟨x, hxW⟩ : W) = 1 := h1
    simpa using congrArg Subtype.val h2
  · exfalso
    have hWX : W ≤ X := fun w hw => by
      have h1 : (⟨w, hw⟩ : W) ∈ (X ⊓ W).subgroupOf W := by rw [hD]; trivial
      exact (Subgroup.mem_inf.1 h1).1
    have h1 := Subgroup.card_le_of_le hWX
    have h2 : 12 < Nat.card W := rootSupp_twelve_lt_card_altSub hZ
    omega

theorem rootSupp_fixes_compl_of_inf_eq_bot {t : Perm α} (hZ : 4 ≤ (t.support)ᶜ.card)
    {X : Subgroup (Perm α)} (hX : X ≤ centralizer ({t} : Set (Perm α)))
    (hXn : ∀ c ∈ centralizer ({t} : Set (Perm α)), c ∈ alternatingGroup α →
      ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hbot : X ⊓ altSub (t.support)ᶜ = ⊥) : ∀ x ∈ X, ∀ i ∈ (t.support)ᶜ, x i = i := by
  intro x hx
  rw [← mem_centralizer_altSub_iff hZ, mem_centralizer_iff]
  intro w hw
  have hw' : w ∈ altSub (t.support)ᶜ := hw
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hX hx)
  have hxN := rootSupp_mem_normalizer_of_comm hxt
  have h1 : x * w * x⁻¹ ∈ altSub (t.support)ᶜ := (mem_normalizer_iff.1 hxN w).1 hw'
  have hwC : w ∈ centralizer ({t} : Set (Perm α)) :=
    mem_centralizer_singleton_iff.2 (rootSupp_comm_of_mem_altSub_compl hw')
  have h2 : w * x⁻¹ * w⁻¹ ∈ X :=
    hXn w hwC (altSub_le_alternatingGroup _ hw') x⁻¹ (inv_mem hx)
  have h3 : x * w * x⁻¹ * w⁻¹ ∈ X ⊓ altSub (t.support)ᶜ := by
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem h1 (inv_mem hw')⟩
    simpa [mul_assoc] using mul_mem hx h2
  rw [hbot] at h3
  have h4 : x * w * x⁻¹ * w⁻¹ = 1 := h3
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h4)).symm

end Normal

theorem rootSupp_false_of_normal_alt_four_of_support_four {n : ℕ} (hn : 12 ≤ n)
    {t : Perm (Fin n)} (ht : t * t = 1) (hsupp : t.support.card = 4)
    {X : Subgroup (Perm (Fin n))} (hX : X ≤ centralizer {t})
    (hXn : ∀ c ∈ centralizer {t}, c ∈ alternatingGroup (Fin n) → ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (he : Nonempty (X ≃* alternatingGroup (Fin 4))) : False := by
  obtain ⟨e⟩ := he
  have hZ : (t.support)ᶜ.card = n - 4 := by
    rw [Finset.card_compl, Fintype.card_fin, hsupp]
  have hX12 : Nat.card X ≤ 12 := by
    have : Nat.card X = 12 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    omega
  have hbot := rootSupp_inf_altSub_eq_bot (by omega) hXn hX12
  have hfixed := rootSupp_fixes_compl_of_inf_eq_bot (by omega) hX hXn hbot
  obtain ⟨y, hy⟩ := exists_orderOf_three (m := 4) (by norm_num)
  have hx3 : orderOf ((e.symm y : X) : Perm (Fin n)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  refine rootSupp_false_of_order_three ht hsupp hx3 ?_ fun i hi => ?_
  · exact mem_centralizer_singleton_iff.1 (hX (e.symm y).2)
  · exact hfixed _ (e.symm y).2 i (by simpa using hi)

end CFSG.OddStandard.AltStdSec
