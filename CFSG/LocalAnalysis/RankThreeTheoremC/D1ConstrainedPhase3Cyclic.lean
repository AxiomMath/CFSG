module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

lemma dvd_sub_one_of_dvd_pow_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} {s : ℤ}
    (h : (p : ℤ) ^ k ∣ s ^ p - 1) : (p : ℤ) ^ (k - 1) ∣ s - 1 := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have : k - 1 = 0 := by omega
    rw [this, pow_zero]
    exact one_dvd _
  · have hp_odd : Odd p := hp.odd_of_ne_two hp2
    have h1 : (p : ℤ) ∣ s ^ p - 1 := (dvd_pow_self (p : ℤ) (by omega : k ≠ 0)).trans h
    have := Fact.mk hp
    have h2 : (p : ℤ) ∣ s - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 ⊢
      push_cast at h1 ⊢
      rwa [ZMod.pow_card] at h1
    have h3 : ¬ (p : ℤ) ∣ s := by
      intro hs
      have h4 : (p : ℤ) ∣ 1 := by simpa using dvd_sub hs h2
      exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast h4))
    have key := emultiplicity_pow_prime_sub_pow_prime (Nat.prime_iff_prime_int.mp hp) hp_odd
      (x := s) (y := 1) (by simpa using h2) h3
    rw [one_pow] at key
    have h5 := pow_dvd_iff_le_emultiplicity.mp h
    rw [key] at h5
    apply pow_dvd_iff_le_emultiplicity.mpr
    generalize emultiplicity (p : ℤ) (s - 1) = e at h5 ⊢
    induction e using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      norm_cast at h5 ⊢
      omega

theorem commutator_pow_prime_eq_one_of_cyclic {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Z : Subgroup G} (hZc : IsCyclic Z) (hZp : IsPGroup p Z)
    {r : G} (hr : ∀ y ∈ Z, r * y * r⁻¹ ∈ Z) (hrp : ∀ y ∈ Z, r ^ p * y * (r ^ p)⁻¹ = y) :
    ∀ y ∈ Z, (r * y * r⁻¹ * y⁻¹) ^ p = 1 := by
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := hZc.exists_generator
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hZp g
  have hgZ : (g : G) ∈ Z := g.2
  have hord : orderOf (g : G) = p ^ k := by rw [Subgroup.orderOf_coe]; exact hk
  have hgen : ∀ y ∈ Z, ∃ m : ℤ, (g : G) ^ m = y := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨s, hs⟩ := hgen _ (hr _ hgZ)
  have hconj : ∀ m : ℤ, r * (g : G) ^ m * r⁻¹ = (g : G) ^ (s * m) := by
    intro m
    rw [zpow_mul, hs, conj_zpow]
  have hiter : ∀ i : ℕ, r ^ i * (g : G) * (r ^ i)⁻¹ = (g : G) ^ (s ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : r ^ (i + 1) * (g : G) * (r ^ (i + 1))⁻¹
          = r * (r ^ i * (g : G) * (r ^ i)⁻¹) * r⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [this, ih, hconj, pow_succ']
  have hspow : (g : G) ^ (s ^ p) = g := by
    rw [← hiter p]
    exact hrp _ hgZ
  have hdvd : ((p : ℤ)) ^ k ∣ s ^ p - 1 := by
    have h1 : (g : G) ^ (s ^ p - 1) = 1 := by
      rw [zpow_sub_one, hspow, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hord] at h2
    exact_mod_cast h2
  have hs1 := dvd_sub_one_of_dvd_pow_sub_one hp hp2 hdvd
  intro y hy
  obtain ⟨m, rfl⟩ := hgen y hy
  rw [hconj, ← zpow_sub, ← zpow_natCast, ← zpow_mul]
  apply orderOf_dvd_iff_zpow_eq_one.mp
  rw [hord]
  obtain ⟨c, hc⟩ := hs1
  have h3 : s * m - m = (s - 1) * m := by ring
  rw [h3, hc]
  push_cast
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel] at *
    exact ⟨c * m, by ring⟩

section Normalizer

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mem_of_relIndex_eq {N P : Subgroup G} (hN : (N.subgroupOf P).Normal) {p : ℕ}
    (hidx : N.relIndex P = p) {g : G} (hg : g ∈ P) : g ^ p ∈ N := by
  have := hN
  have hcard : Nat.card (P ⧸ N.subgroupOf P) = p := by
    rw [← hidx]
    rfl
  have h1 : (QuotientGroup.mk (⟨g, hg⟩ : P) : P ⧸ N.subgroupOf P) ^ p = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mul_mem_of_mem_centralizer_of_relIndex_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P F R Z : Subgroup G} (hFR : F ≤ R) (hRP : R ≤ P) (hFP : F ≤ P)
    (hFn : (F.subgroupOf P).Normal) (hZ : Z = P ⊓ Subgroup.centralizer (F : Set G))
    (hcyc : IsCyclic Z) (hZp : IsPGroup p Z) (hΩ : ∀ y ∈ Z, y ^ p = 1 → y ∈ F)
    (hidx : (F ⊔ Z).relIndex P = p) :
    ∀ y ∈ Z, ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
  have hZP : Z ≤ P := hZ ▸ inf_le_left
  have hZF : ∀ y ∈ Z, ∀ f ∈ F, f * y = y * f := fun y hy f hf =>
    Subgroup.mem_centralizer_iff.mp (hZ ▸ hy : y ∈ P ⊓ Subgroup.centralizer (F : Set G)).2 f hf
  have hFconj : ∀ g ∈ P, ∀ f ∈ F, g * f * g⁻¹ ∈ F := fun g hg f hf =>
    hFn.conj_mem ⟨f, hFP hf⟩ hf ⟨g, hg⟩
  have hZn : ∀ g ∈ P, ∀ y ∈ Z, g * y * g⁻¹ ∈ Z := by
    intro g hg y hy
    rw [hZ]
    refine ⟨P.mul_mem (P.mul_mem hg (hZP hy)) (P.inv_mem hg), Subgroup.mem_centralizer_iff.mpr
      fun f hf => ?_⟩
    have h1 := hFconj g⁻¹ (P.inv_mem hg) f hf
    simp only [inv_inv] at h1
    have h2 := hZF y hy _ h1
    calc f * (g * y * g⁻¹) = g * ((g⁻¹ * f * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * f * g)) * g⁻¹ := by rw [h2]
      _ = (g * y * g⁻¹) * f := by group
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    have := hcyc
    let _ : CommGroup Z := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : Z) ⟨b, hb⟩)
  have hFnorm : F ≤ Subgroup.normalizer (Z : Set G) := by
    intro f hf
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · have := hZF h hh f hf
      rw [this]
      simpa using hh
    · have h3 := hZn f⁻¹ (hFP (F.inv_mem hf)) _ hh
      have h4 : f⁻¹ * (f * h * f⁻¹) * f⁻¹⁻¹ = h := by group
      rwa [h4] at h3
  have hQn : ((F ⊔ Z).subgroupOf P).Normal := by
    rw [Subgroup.subgroupOf_sup hFP hZP]
    have : (Z.subgroupOf P).Normal :=
      ⟨fun n hn g => by
        have := hZn g g.2 n hn
        exact this⟩
    infer_instance
  intro y hy r hr
  have hrP := hRP hr
  have hr1 : ∀ w ∈ Z, r * w * r⁻¹ ∈ Z := fun w hw => hZn r hrP w hw
  have hpow : r ^ p ∈ F ⊔ Z := pow_mem_of_relIndex_eq hQn hidx hrP
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right F Z hFnorm] at hpow
  obtain ⟨f, hf, y₁, hy₁, hfy⟩ := hpow
  have hrp : ∀ w ∈ Z, r ^ p * w * (r ^ p)⁻¹ = w := by
    intro w hw
    rw [← hfy]
    have h1 : y₁ * w * y₁⁻¹ = w := by
      rw [hZcomm y₁ hy₁ w hw]
      group
    calc f * y₁ * w * (f * y₁)⁻¹ = f * (y₁ * w * y₁⁻¹) * f⁻¹ := by group
      _ = f * w * f⁻¹ := by rw [h1]
      _ = w := by rw [hZF w hw f hf]; group
  have hc := commutator_pow_prime_eq_one_of_cyclic hp hp2 hcyc hZp hr1 hrp y hy
  have hwZ : r * y * r⁻¹ * y⁻¹ ∈ Z := Z.mul_mem (hr1 y hy) (Z.inv_mem hy)
  have hwF : r * y * r⁻¹ * y⁻¹ ∈ F := hΩ _ hwZ hc
  have : y * r * y⁻¹ = (r * y * r⁻¹ * y⁻¹)⁻¹ * r := by group
  rw [this]
  exact R.mul_mem (R.inv_mem (hFR hwF)) hr

end Normalizer

end CFSG.LocalAnalysis.RankThreeTheoremC
