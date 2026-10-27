module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseProd

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem exists_inner_of_odd {G : Type*} [Group G] {H : Subgroup G}
    (hH : IsPGroup 2 (Outer ↥H)) {g : G} (hg : g ∈ normalizer (H : Set G))
    (hodd : Odd (orderOf g)) :
    ∃ h ∈ H, ∀ x ∈ H, g * x * g⁻¹ = h * x * h⁻¹ := by
  let φ : MulAut H := H.normalizerMonoidHom ⟨g, hg⟩
  have hφ : orderOf φ ∣ orderOf g := by
    have := orderOf_map_dvd H.normalizerMonoidHom (⟨g, hg⟩ : normalizer (H : Set G))
    rwa [Subgroup.orderOf_mk] at this
  have hq : orderOf (QuotientGroup.mk' (inner H) φ) ∣ orderOf g :=
    (orderOf_map_dvd _ φ).trans hφ
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hH (QuotientGroup.mk' (inner H) φ)
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ orderOf g := by
      have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
      rw [← hk] at this
      exact this.trans hq
    obtain ⟨m, hm⟩ := hodd
    omega
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  obtain ⟨h, hh⟩ := (QuotientGroup.eq_one_iff _).1 hk
  refine ⟨h, h.2, fun x hx => ?_⟩
  have h1 : ((φ ⟨x, hx⟩ : H) : G) = g * x * g⁻¹ := rfl
  have h2 : (((MulAut.conj h) ⟨x, hx⟩ : H) : G) = (h : G) * x * (h : G)⁻¹ := rfl
  rw [← h1, ← hh, h2]

theorem mem_of_odd_of_outer {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : IsPGroup 2 (Outer ↥N)) (hC : ∀ x : G, (∀ n ∈ N, x * n = n * x) → x = 1) {g : G}
    (hg : Odd (orderOf g)) : g ∈ N := by
  have hnorm : g ∈ normalizer (N : Set G) := by
    rw [normalizer_eq_top]
    exact mem_top g
  obtain ⟨n, hn, hx⟩ := exists_inner_of_odd hN hnorm hg
  have hc : g * n⁻¹ = 1 := by
    refine hC _ fun x hx' => ?_
    have h1 : n⁻¹ * x * n ∈ N := by simpa using ‹N.Normal›.conj_mem x hx' n⁻¹
    have h2 := hx _ h1
    have h3 : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [h3] at h2
    calc g * n⁻¹ * x = g * (n⁻¹ * x * n) * g⁻¹ * (g * n⁻¹) := by group
      _ = x * (g * n⁻¹) := by rw [h2]
  rw [mul_inv_eq_one.1 hc]
  exact hn

theorem mem_of_odd_orderOf_u43 (hOut : OutU43TwoGroup) {G : Type*} [Group G]
    {N : Subgroup G} [N.Normal] (e : ↥N ≃* U43)
    (hC : ∀ x : G, (∀ n ∈ N, x * n = n * x) → x = 1) {g : G} (hg : Odd (orderOf g)) : g ∈ N :=
  mem_of_odd_of_outer
    (IsPGroup.of_equiv (show IsPGroup 2 (Outer U43) from hOut)
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e.symm)) hC hg

section Conj

variable {G : Type*} [Group G]

@[expose] def conjSub (g : G) (A : Subgroup G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g x : G} {A : Subgroup G} : x ∈ conjSub g A ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    change g⁻¹ * (g * y * g⁻¹) * g ∈ A
    rw [e]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem card_conjSub (g : G) (A : Subgroup G) : Nat.card (conjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_le {g : G} {A N : Subgroup G} [N.Normal] (h : A ≤ N) : conjSub g A ≤ N := by
  intro x hx
  have h1 : g⁻¹ * x * g ∈ N := h (mem_conjSub.1 hx)
  have h2 := ‹N.Normal›.conj_mem _ h1 g
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h2

theorem conjSub_normalized {g : G} {A N : Subgroup G} [N.Normal]
    (hA : ∀ n ∈ N, ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    ∀ n ∈ N, ∀ s ∈ conjSub g A, n * s * n⁻¹ ∈ conjSub g A := by
  intro n hn s hs
  rw [mem_conjSub] at hs ⊢
  have hn' : g⁻¹ * n * g ∈ N := by simpa using ‹N.Normal›.conj_mem n hn g⁻¹
  have h1 := hA _ hn' _ hs
  have e : g⁻¹ * n * g * (g⁻¹ * s * g) * (g⁻¹ * n * g)⁻¹ = g⁻¹ * (n * s * n⁻¹) * g := by group
  rwa [e] at h1

theorem conjSub_injective {g : G} {A B : Subgroup G} (h : conjSub g A = conjSub g B) :
    A = B := by
  ext x
  have h1 := Subgroup.ext_iff.1 h (g * x * g⁻¹)
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rwa [mem_conjSub, mem_conjSub, e] at h1

theorem conjSub_mul (g h : G) (A : Subgroup G) :
    conjSub (g * h) A = conjSub g (conjSub h A) := by
  ext x
  rw [mem_conjSub, mem_conjSub, mem_conjSub]
  have e : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [e]

theorem conjSub_eq_self_iff {g : G} {A : Subgroup G} :
    conjSub g A = A ↔ g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff'', Subgroup.ext_iff]
  exact forall_congr' fun x => by rw [mem_conjSub]; exact Iff.comm

namespace ProdSplit

variable {N A B : Subgroup G}

theorem eq_or_eq_of_card (h : ProdSplit N A B) {S : Subgroup G} (hS : S ≤ N)
    (hSn : ∀ n ∈ N, ∀ s ∈ S, n * s * n⁻¹ ∈ S) (hcard : Nat.card S = 360) :
    S = A ∨ S = B := by
  have hSfin : Finite S := Nat.finite_of_card_ne_zero (by omega)
  have hAcard : Nat.card A = 360 := h.isA.card
  have hBcard : Nat.card B = 360 := h.isB.card
  rcases h.isA.nonabSimple.eq_bot_or_eq_self (A ⊓ S) inf_le_left fun a ha s hs =>
    mem_inf.2 ⟨mul_mem (mul_mem ha (mem_inf.1 hs).1) (inv_mem ha),
      hSn a (h.le_A ha) s (mem_inf.1 hs).2⟩ with h0 | h0
  · right
    have hcen : ∀ s ∈ S, ∀ a ∈ A, s * a = a * s :=
      h.centralizes_of_inf_eq_bot hS hSn (by rw [inf_comm]; exact h0)
    have hSB : S ≤ B := fun s hs => h.centralizes_eq s (hS hs) fun a ha => hcen s hs a ha
    have : Finite B := Nat.finite_of_card_ne_zero (by omega)
    exact Subgroup.eq_of_le_of_card_ge hSB (by omega)
  · left
    exact (Subgroup.eq_of_le_of_card_ge (inf_eq_left.1 h0) (by omega)).symm

theorem ne (h : ProdSplit N A B) : A ≠ B := by
  intro hAB
  have h0 := h.inf_eq_bot
  rw [hAB, inf_idem] at h0
  have h1 : Nat.card B = 1 := by rw [h0]; exact Subgroup.card_bot
  have h2 := h.isB.card
  omega

theorem conjSub_cases (h : ProdSplit N A B) [N.Normal] (g : G) :
    (conjSub g A = A ∨ conjSub g A = B) ∧ (conjSub g B = A ∨ conjSub g B = B) :=
  ⟨h.eq_or_eq_of_card (conjSub_le h.le_A) (conjSub_normalized h.conj_A)
      ((card_conjSub g A).trans h.isA.card),
    h.eq_or_eq_of_card (conjSub_le h.le_B) (conjSub_normalized h.conj_B)
      ((card_conjSub g B).trans h.isB.card)⟩

theorem conjSub_mul_self (h : ProdSplit N A B) [N.Normal] (g : G) :
    conjSub (g * g) A = A ∧ conjSub (g * g) B = B := by
  obtain ⟨hA, hB⟩ := h.conjSub_cases g
  rw [conjSub_mul, conjSub_mul]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (conjSub_injective (hA.trans hB.symm)) h.ne
  · simp only [hA, hB, and_self]
  · simp only [hA, hB, and_self]
  · exact absurd (conjSub_injective (hA.trans hB.symm)) h.ne

theorem mem_normalizer_of_odd (h : ProdSplit N A B) [N.Normal] {g : G}
    (hg : Odd (orderOf g)) : g ∈ normalizer (A : Set G) ∧ g ∈ normalizer (B : Set G) := by
  obtain ⟨hA, hB⟩ := h.conjSub_mul_self g
  have hK : g * g ∈ normalizer (A : Set G) ⊓ normalizer (B : Set G) :=
    mem_inf.2 ⟨conjSub_eq_self_iff.1 hA, conjSub_eq_self_iff.1 hB⟩
  obtain ⟨k, hk⟩ := hg
  have hgk : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have hpow : g = (g * g) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hgk, one_mul]
  have hmem := pow_mem hK (k + 1)
  rw [← hpow] at hmem
  exact mem_inf.1 hmem

theorem centralizes_of_centralizes (h : ProdSplit N A B) {c : G}
    (hA : ∀ a ∈ A, c * a = a * c) (hB : ∀ b ∈ B, c * b = b * c) :
    ∀ n ∈ N, c * n = n * c := by
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := h.prod n hn
  rw [← mul_assoc, hA a ha, mul_assoc, hB b hb, ← mul_assoc]

theorem centralizes_of_acts_inner (h : ProdSplit N A B) {g a₀ b₀ : G} (ha₀ : a₀ ∈ A)
    (hb₀ : b₀ ∈ B) (hg : ∀ x ∈ A, g * x * g⁻¹ = a₀ * x * a₀⁻¹) :
    ∀ a ∈ A, g * (a₀ * b₀)⁻¹ * a = a * (g * (a₀ * b₀)⁻¹) := by
  intro a ha
  have hy : a₀⁻¹ * a * a₀ ∈ A := mul_mem (mul_mem (inv_mem ha₀) ha) ha₀
  have hyb : (a₀⁻¹ * a * a₀) * b₀⁻¹ = b₀⁻¹ * (a₀⁻¹ * a * a₀) :=
    (Commute.inv_right (h.comm _ hy b₀ hb₀ : Commute (a₀⁻¹ * a * a₀) b₀)).eq
  have h1 : g * (a₀⁻¹ * a * a₀) * g⁻¹ = a := by rw [hg _ hy]; group
  have h2 : (a₀ * b₀)⁻¹ * a = (a₀⁻¹ * a * a₀) * (a₀ * b₀)⁻¹ := by
    have e : (a₀ * b₀)⁻¹ * a = b₀⁻¹ * (a₀⁻¹ * a * a₀) * a₀⁻¹ := by group
    rw [e, ← hyb]
    group
  calc g * (a₀ * b₀)⁻¹ * a = g * ((a₀ * b₀)⁻¹ * a) := mul_assoc _ _ _
    _ = g * ((a₀⁻¹ * a * a₀) * (a₀ * b₀)⁻¹) := by rw [h2]
    _ = (g * (a₀⁻¹ * a * a₀) * g⁻¹) * (g * (a₀ * b₀)⁻¹) := by group
    _ = a * (g * (a₀ * b₀)⁻¹) := by rw [h1]

end ProdSplit

end Conj

theorem mem_of_odd_orderOf_prod {G : Type*} [Group G] {N A B : Subgroup G} [N.Normal]
    (hP : ProdSplit N A B) (hC : ∀ x : G, (∀ n ∈ N, x * n = n * x) → x = 1) {g : G}
    (hg : Odd (orderOf g)) : g ∈ N := by
  obtain ⟨hgA, hgB⟩ := hP.mem_normalizer_of_odd hg
  obtain ⟨a₀, ha₀, hA⟩ := exists_inner_of_odd hP.isA.outer hgA hg
  obtain ⟨b₀, hb₀, hB⟩ := exists_inner_of_odd hP.isB.outer hgB hg
  have hcA := hP.centralizes_of_acts_inner ha₀ hb₀ hA
  have hcB := hP.swap.centralizes_of_acts_inner hb₀ ha₀ hB
  rw [(hP.comm a₀ ha₀ b₀ hb₀).symm] at hcB
  have hc : g * (a₀ * b₀)⁻¹ = 1 := hC _ (hP.centralizes_of_centralizes hcA hcB)
  rw [mul_inv_eq_one.1 hc]
  exact mul_mem (hP.le_A ha₀) (hP.le_B hb₀)

end CFSG.EvenSporadicStandard.RuStd.S2.Close
