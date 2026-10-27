module

public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.KC.Th.Spec.SylowPc

@[expose] def pcSub {G : Type*} [Group G] (g : ℕ → G) (n i : ℕ) : Subgroup G :=
  Subgroup.closure (g '' Set.Ico i n)

theorem pcSub_succ_le {G : Type*} [Group G] (g : ℕ → G) (n i : ℕ) :
    pcSub g n (i + 1) ≤ pcSub g n i :=
  Subgroup.closure_mono (Set.image_mono (Set.Ico_subset_Ico_left (Nat.le_succ i)))

theorem mem_pcSub {G : Type*} [Group G] {g : ℕ → G} {n i k : ℕ} (h1 : i ≤ k) (h2 : k < n) :
    g k ∈ pcSub g n i :=
  Subgroup.subset_closure (Set.mem_image_of_mem g (Set.mem_Ico.mpr ⟨h1, h2⟩))

private theorem pcSub_conj_mem {G : Type*} [Group G] (g : ℕ → G) (n i : ℕ)
    (hconj : ∀ j, i < j → j < n → (g i)⁻¹ * g j * g i ∈ pcSub g n (i + 1)) :
    ∀ a ∈ pcSub g n (i + 1), (g i)⁻¹ * a * g i ∈ pcSub g n (i + 1) := by
  intro a ha
  have ha' : a ∈ Subgroup.closure (g '' Set.Ico (i + 1) n) := ha
  clear ha
  induction ha' using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    exact hconj j (by have := hj.1; omega) hj.2
  | one => simp
  | mul a b ha hb iha ihb =>
    have e : (g i)⁻¹ * (a * b) * g i = ((g i)⁻¹ * a * g i) * ((g i)⁻¹ * b * g i) := by
      group
    rw [e]
    exact mul_mem iha ihb
  | inv a ha iha =>
    have e : (g i)⁻¹ * a⁻¹ * g i = ((g i)⁻¹ * a * g i)⁻¹ := by group
    rw [e]
    exact inv_mem iha

private theorem pcSub_normalizes {G : Type*} [Group G] [Finite G] (g : ℕ → G) (n i : ℕ)
    (hconj : ∀ j, i < j → j < n → (g i)⁻¹ * g j * g i ∈ pcSub g n (i + 1)) :
    g i ∈ Subgroup.normalizer (pcSub g n (i + 1)) := by
  have hb := pcSub_conj_mem g n i hconj
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    let f : pcSub g n (i + 1) → pcSub g n (i + 1) :=
      fun a => ⟨(g i)⁻¹ * (a : G) * g i, hb (a : G) a.2⟩
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h2 : (g i)⁻¹ * (a : G) * g i = (g i)⁻¹ * (b : G) * g i :=
        congrArg Subtype.val hab
      exact mul_left_cancel (mul_right_cancel h2)
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨h, hh⟩
    have hae : (g i)⁻¹ * (a : G) * g i = h := congrArg Subtype.val ha
    have hh' : g i * h * (g i)⁻¹ = (a : G) := by
      rw [← hae]
      group
    rw [hh']
    exact a.2
  · intro hh
    have h3 := hb _ hh
    have e : (g i)⁻¹ * (g i * h * (g i)⁻¹) * g i = h := by group
    rwa [e] at h3

private theorem card_dvd_mul_of_normalizes {G : Type*} [Group G] [Finite G] (p : ℕ) (x : G)
    (K N : Subgroup G) (hNK : N ≤ K) (hxK : x ∈ K) (hKle : K ≤ Subgroup.normalizer N)
    (hgen : ∀ k ∈ K, ∃ m : ℤ, (x ^ m)⁻¹ * k ∈ N) (hxp : x ^ p ∈ N) :
    Nat.card K ∣ p * Nat.card N := by
  haveI : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKle
  let x' : K := ⟨x, hxK⟩
  have hy : ∀ q : K ⧸ N.subgroupOf K,
      q ∈ Subgroup.zpowers (QuotientGroup.mk x' : K ⧸ N.subgroupOf K) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm⟩ := hgen k k.2
    have hwK : (x ^ m)⁻¹ * (k : G) ∈ K := hNK hm
    let w : K := ⟨(x ^ m)⁻¹ * (k : G), hwK⟩
    have hwN : w ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.mpr hm
    have hw1 : (QuotientGroup.mk w : K ⧸ N.subgroupOf K) = 1 :=
      (QuotientGroup.eq_one_iff w).mpr hwN
    have hkeq : k = x' ^ m * w := by
      apply Subtype.ext
      simp [x', w]
    rw [hkeq, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hw1, mul_one]
    exact zpow_mem (Subgroup.mem_zpowers _) m
  have hyp : (QuotientGroup.mk x' : K ⧸ N.subgroupOf K) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hpx : ((x' ^ p : K) : G) = x ^ p := by simp [x']
    rw [hpx]
    exact hxp
  have hdvd : (N.subgroupOf K).index ∣ p := by
    rw [Subgroup.index_eq_card, ← orderOf_eq_card_of_forall_mem_zpowers hy]
    exact orderOf_dvd_of_pow_eq_one hyp
  have hcard : Nat.card (N.subgroupOf K) * (N.subgroupOf K).index = Nat.card K :=
    Subgroup.card_mul_index (N.subgroupOf K)
  have hNcard : Nat.card (N.subgroupOf K) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
  rw [← hcard, hNcard, mul_comm p]
  exact mul_dvd_mul_left (Nat.card N) hdvd

private theorem card_step {G : Type*} [Group G] [Finite G] (p n : ℕ) (g : ℕ → G)
    (hpow : ∀ i < n, g i ^ p ∈ pcSub g n (i + 1))
    (hconj : ∀ i j, i < j → j < n → (g i)⁻¹ * g j * g i ∈ pcSub g n (i + 1))
    (i : ℕ) (hi : i < n) :
    Nat.card (pcSub g n i) ∣ p * Nat.card (pcSub g n (i + 1)) := by
  have hNK : pcSub g n (i + 1) ≤ pcSub g n i := by
    unfold pcSub
    apply Subgroup.closure_mono
    apply Set.image_mono
    exact Set.Ico_subset_Ico_left (by omega)
  have hxK : g i ∈ pcSub g n i :=
    Subgroup.subset_closure (Set.mem_image_of_mem g (show i ∈ Set.Ico i n from ⟨le_rfl, hi⟩))
  have hxN : g i ∈ Subgroup.normalizer (pcSub g n (i + 1)) :=
    pcSub_normalizes g n i (fun j h1 h2 => hconj i j h1 h2)
  have hKle : pcSub g n i ≤ Subgroup.normalizer (pcSub g n (i + 1)) := by
    show Subgroup.closure (g '' Set.Ico i n) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge i j with hij | hij
    · exact Subgroup.le_normalizer
        (Subgroup.subset_closure (Set.mem_image_of_mem g (show j ∈ Set.Ico (i + 1) n from ⟨hij, hj.2⟩)))
    · obtain rfl : j = i := le_antisymm hij hj.1
      exact hxN
  have hgen : ∀ k ∈ pcSub g n i, ∃ m : ℤ, (g i ^ m)⁻¹ * k ∈ pcSub g n (i + 1) := by
    intro k hk
    have hk' : k ∈ Subgroup.closure (g '' Set.Ico i n) := hk
    clear hk
    induction hk' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      rcases Nat.lt_or_ge i j with hij | hij
      · refine ⟨0, ?_⟩
        rw [zpow_zero, inv_one, one_mul]
        exact Subgroup.subset_closure
          (Set.mem_image_of_mem g (show j ∈ Set.Ico (i + 1) n from ⟨hij, hj.2⟩))
      · obtain rfl : j = i := le_antisymm hij hj.1
        exact ⟨1, by simp⟩
    | one => exact ⟨0, by simp⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨m1, h1⟩ := iha
      obtain ⟨m2, h2⟩ := ihb
      refine ⟨m1 + m2, ?_⟩
      have hz : (g i ^ m2)⁻¹ * ((g i ^ m1)⁻¹ * a) * ((g i ^ m2)⁻¹)⁻¹ ∈ pcSub g n (i + 1) :=
        (Subgroup.mem_normalizer_iff.mp (inv_mem (zpow_mem hxN m2)) _).mp h1
      have e : (g i ^ (m1 + m2))⁻¹ * (a * b)
          = ((g i ^ m2)⁻¹ * ((g i ^ m1)⁻¹ * a) * ((g i ^ m2)⁻¹)⁻¹) * ((g i ^ m2)⁻¹ * b) := by
        rw [zpow_add]
        group
      rw [e]
      exact mul_mem hz h2
    | inv a ha iha =>
      obtain ⟨m, h⟩ := iha
      refine ⟨-m, ?_⟩
      have hz : g i ^ m * ((g i ^ m)⁻¹ * a)⁻¹ * (g i ^ m)⁻¹ ∈ pcSub g n (i + 1) :=
        (Subgroup.mem_normalizer_iff.mp (zpow_mem hxN m) _).mp (inv_mem h)
      have e : (g i ^ (-m))⁻¹ * a⁻¹ = g i ^ m * ((g i ^ m)⁻¹ * a)⁻¹ * (g i ^ m)⁻¹ := by
        rw [zpow_neg]
        group
      rw [e]
      exact hz
  exact card_dvd_mul_of_normalizes p (g i) (pcSub g n i) (pcSub g n (i + 1)) hNK hxK hKle
    hgen (hpow i hi)

private theorem pcSub_self_eq_bot {G : Type*} [Group G] (g : ℕ → G) (n : ℕ) :
    pcSub g n n = ⊥ := by
  unfold pcSub
  rw [Set.Ico_self, Set.image_empty, Subgroup.closure_empty]

theorem card_pcSub_dvd {G : Type*} [Group G] [Finite G] (p n : ℕ) (g : ℕ → G)
    (hpow : ∀ i < n, g i ^ p ∈ pcSub g n (i + 1))
    (hconj : ∀ i j, i < j → j < n → (g i)⁻¹ * g j * g i ∈ pcSub g n (i + 1)) :
    Nat.card (pcSub g n 0) ∣ p ^ n := by
  have key : ∀ d i, i + d = n → Nat.card (pcSub g n i) ∣ p ^ d := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hin : i = n := by omega
      subst hin
      simp only [pcSub_self_eq_bot, Subgroup.card_bot, pow_zero, one_dvd]
    | succ d ih =>
      intro i hi
      have hlt : i < n := by omega
      have h1 : Nat.card (pcSub g n (i + 1)) ∣ p ^ d := ih (i + 1) (by omega)
      have h2 : Nat.card (pcSub g n i) ∣ p * Nat.card (pcSub g n (i + 1)) :=
        card_step p n g hpow hconj i hlt
      have h3 : p * Nat.card (pcSub g n (i + 1)) ∣ p ^ (d + 1) := by
        rw [pow_succ']
        exact mul_dvd_mul_left p h1
      exact h2.trans h3
  exact key n 0 (Nat.zero_add n)

end CFSG.KC.Th.Spec.SylowPc

end
