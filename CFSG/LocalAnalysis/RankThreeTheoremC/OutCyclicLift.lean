module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne.OutStructure (OutPChain Inn)

theorem card_le_of_outPChain {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : OutPChain p K) {E : Subgroup (Outer K)} (hE : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨D, F, hID, hD2, hF1, hF3⟩ := h
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpow : ∀ x ∈ E, x ^ p = 1 := hE.2
  obtain ⟨β, hβE, hβ1⟩ : ∃ β ∈ E, β ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card E = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (by rw [hcon a a.2, hcon b b.2])⟩, ⟨1⟩⟩
    have := hp.one_lt
    omega
  have hβord : orderOf β = p := orderOf_eq_prime (hpow β hβE) hβ1
  obtain ⟨α, hαE, hαβ⟩ : ∃ α ∈ E, α ∉ Subgroup.zpowers β := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers β := fun x hx => hcon x hx
    have hcard : Nat.card E ≤ Nat.card (Subgroup.zpowers β) := Nat.card_le_card_of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [Nat.card_zpowers, hβord] at hcard
    omega
  have hα1 : α ≠ 1 := fun h1 => hαβ (h1 ▸ Subgroup.one_mem _)
  have hαord : orderOf α = p := orderOf_eq_prime (hpow α hαE) hα1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective α
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective β
  have hpI : ∀ x : MulAut K, (QuotientGroup.mk x : Outer K) ^ p = 1 → x ^ p ∈ Inn K := by
    intro x hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hx
    exact hx
  have haI : a ^ p ∈ Inn K := hpI a (hpow _ hαE)
  have hbI : b ^ p ∈ Inn K := hpI b (hpow _ hβE)
  have hpD : ∀ x : MulAut K, x ^ p ∈ Inn K → ∃ k : ℕ, x ^ (p ^ k) ∈ D := fun x hx =>
    ⟨1, by rw [pow_one]; exact hID hx⟩
  have haF : a ∈ F := hF1 a (hpD a haI)
  have hbF : b ∈ F := hF1 b (hpD b hbI)
  have hinn : ∀ x : MulAut K, x ∈ D → (QuotientGroup.mk x : Outer K) ^ p = 1 → x ∈ Inn K := by
    intro x hxD hx
    exact hD2 x hxD 1 (by rw [pow_one]; exact hpI x hx)
  rcases hF3 a haF b hbF (hpD a haI) (hpD b hbI) with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hmE : (QuotientGroup.mk (a * b ^ m) : Outer K) ∈ E := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      exact E.mul_mem hαE (E.zpow_mem hβE m)
    have hpm : (QuotientGroup.mk (a * b ^ m) : Outer K) ^ p = 1 := hpow _ hmE
    have hI := hinn _ hm hpm
    have h1 : (QuotientGroup.mk (a * b ^ m) : Outer K) = 1 := (QuotientGroup.eq_one_iff _).mpr hI
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h1
    exact hαβ (h1 ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
  ·
    have hmE : (QuotientGroup.mk (b * a ^ m) : Outer K) ∈ E := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
      exact E.mul_mem hβE (E.zpow_mem hαE m)
    have hpm : (QuotientGroup.mk (b * a ^ m) : Outer K) ^ p = 1 := hpow _ hmE
    have hI := hinn _ hm hpm
    have h1 : (QuotientGroup.mk (b * a ^ m) : Outer K) = 1 := (QuotientGroup.eq_one_iff _).mpr hI
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, mul_eq_one_iff_eq_inv, ← zpow_neg] at h1
    have hβα : (QuotientGroup.mk b : Outer K) ∈ Subgroup.zpowers (QuotientGroup.mk a : Outer K) :=
      h1 ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    have hle : Subgroup.zpowers (QuotientGroup.mk b : Outer K) ≤
        Subgroup.zpowers (QuotientGroup.mk a : Outer K) := Subgroup.zpowers_le.mpr hβα
    have hcα : Nat.card (Subgroup.zpowers (QuotientGroup.mk a : Outer K)) = p := by
      rw [Nat.card_zpowers, hαord]
    have hcβ : Nat.card (Subgroup.zpowers (QuotientGroup.mk b : Outer K)) = p := by
      rw [Nat.card_zpowers, hβord]
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcα, hcβ])
    exact hαβ (heq ▸ Subgroup.mem_zpowers _)

theorem pRank_outer_le_one_of_outPChain {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : OutPChain p K) : CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1 :=
  CFSG.SectionRank.pRank_le hp.one_lt fun _ _ hE => by
    rw [pow_one]
    exact card_le_of_outPChain hp h hE

theorem card_le_of_outer_small {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : Nat.card (Outer K) < p ^ 2 ∨ ¬ p ∣ Nat.card (Outer K))
    {E : Subgroup (Outer K)} (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  have hEp : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    have := hp.two_le
    interval_cases k
    · rw [pow_zero] at hk
      omega
    · rw [pow_one] at hk
      omega
  have hdvd : p ^ 2 ∣ Nat.card (Outer K) :=
    (pow_dvd_pow p hk2).trans (hk ▸ Subgroup.card_subgroup_dvd_card E)
  rcases h with hlt' | hnd
  · have := Nat.le_of_dvd Nat.card_pos hdvd
    omega
  · exact hnd ((dvd_pow_self p two_ne_zero).trans hdvd)

theorem pRank_outer_le_one_of_outer_small {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (h : Nat.card (Outer K) < p ^ 2 ∨ ¬ p ∣ Nat.card (Outer K)) :
    CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1 :=
  CFSG.SectionRank.pRank_le hp.one_lt fun _ _ hE => by
    rw [pow_one]
    exact card_le_of_outer_small hp h hE

theorem card_inn_dvd_card {K : Type} [Group K] : Nat.card (Inn K) ∣ Nat.card K :=
  Subgroup.card_range_dvd (MulAut.conj : K →* MulAut K)

theorem card_le_of_outer_of_mulAut {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K)
    (h : ∀ A : Subgroup (MulAut K), CFSG.Open.IsElemAbelian p A → Nat.card A ≤ p)
    {E : Subgroup (Outer K)} (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let π : MulAut K →* Outer K := QuotientGroup.mk' (Inn K)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : ∀ x : MulAut K, π x = 1 ↔ x ∈ Inn K := fun x => QuotientGroup.eq_one_iff x
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEp : IsPGroup p E := fun y => ⟨1, Subtype.ext (by simpa using hE.2 y y.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  let F : Subgroup (MulAut K) := E.comap π
  have hEF : Nat.card E ∣ Nat.card F := by
    have h1 := Subgroup.card_map_dvd (H := F) π
    rwa [Subgroup.map_comap_eq_self_of_surjective hπs] at h1
  let P : Sylow p F := default
  let A : Subgroup (MulAut K) := (P : Subgroup F).map F.subtype
  have hpA : IsPGroup p A := P.isPGroup'.map F.subtype
  have hAF : ∀ x ∈ A, π x ∈ E := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hAcard : Nat.card A = Nat.card P := Subgroup.card_subtype F (P : Subgroup F)
  have hinj1 : ∀ x ∈ A, x ∈ Inn K → x = 1 := by
    intro x hxA hxI
    obtain ⟨j, hj⟩ := hpA ⟨x, hxA⟩
    have hj' : x ^ (p ^ j) = 1 := congrArg Subtype.val hj
    obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hj')
    have hdvd : orderOf x ∣ Nat.card K :=
      (Subgroup.orderOf_dvd_natCard (Inn K) hxI).trans card_inn_dvd_card
    by_contra hx1
    have hi1 : i ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.mp (by simpa using hi'))
    exact hpK ((dvd_pow_self p hi1).trans (hi' ▸ hdvd))
  have hinj : ∀ a ∈ A, ∀ b ∈ A, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ Inn K := by
      rw [← hπk, map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.mp (hinj1 _ (A.mul_mem (A.inv_mem ha) hb) h1)
  have hAel : CFSG.Open.IsElemAbelian p A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · show (a : MulAut K) * b = b * a
      refine hinj _ (A.mul_mem a.2 b.2) _ (A.mul_mem b.2 a.2) ?_
      rw [map_mul, map_mul]
      exact hEcomm _ (hAF _ a.2) _ (hAF _ b.2)
    · refine hinj _ (A.pow_mem hx p) _ A.one_mem ?_
      rw [map_pow, map_one]
      exact hE.2 _ (hAF _ hx)
  have hcop : Nat.Coprime (Nat.card E) (P : Subgroup F).index := by
    rw [hk]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr P.not_dvd_index).pow_left k
  have hEP : Nat.card E ∣ Nat.card P := by
    have h2 : Nat.card E ∣ Nat.card P * (P : Subgroup F).index :=
      (Subgroup.card_mul_index (P : Subgroup F)) ▸ hEF
    exact hcop.dvd_of_dvd_mul_right h2
  calc Nat.card E ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hEP
    _ = Nat.card A := hAcard.symm
    _ ≤ p := h A hAel

end CFSG.LocalAnalysis.RankThreeTheoremC
