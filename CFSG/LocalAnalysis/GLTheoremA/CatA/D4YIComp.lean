module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YECore
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.D4T

section Three

variable {H : Type} [Group H] [Finite H] {K B : Subgroup H}

theorem sup_Bo_le_inner {E : Subgroup H} (hEK : E ≤ K) :
    E ⊔ Bo K B ≤ ((innerAut ↥K).comap (conjHom K)).map (Subgroup.normalizer (K : Set H)).subtype := by
  refine sup_le (fun e he => ?_) (fun s hs => ?_)
  · refine ⟨⟨e, Subgroup.le_normalizer (hEK he)⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    refine ⟨⟨e, hEK he⟩, ?_⟩
    ext k
    rfl
  · have hsN : s ∈ Subgroup.normalizer (K : Set H) :=
      mem_normalizer_of_centralizes fun k hk => Bo_cent hs k hk
    refine ⟨⟨s, hsN⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    have : conjHom K ⟨s, hsN⟩ = 1 := by
      ext k
      have h1 := Bo_cent hs k k.2
      change s * (k : H) * s⁻¹ = k
      rw [h1]
      group
    rw [this]
    exact Subgroup.one_mem _

theorem big_sup3 (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) (hB : IsElemAbelian 3 B)
    {E : Subgroup H} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) {c : H} (hcB : c ∈ B)
    (hcN : c ∈ Subgroup.normalizer (K : Set H)) (hcout : conjAut K c hcN ∉ innerAut ↥K)
    (hcE : ∀ y ∈ E, c * y = y * c) :
    IsElemAbelian 3 (E ⊔ Bo K B ⊔ Subgroup.zpowers c) ∧
      Nat.card ↥(E ⊔ Bo K B ⊔ Subgroup.zpowers c) = 3 * (Nat.card E * Nat.card (Bo K B)) := by
  classical
  obtain ⟨hP₀el, hP₀c⟩ := big_sup hKc hB hEK hE
  set P₀ : Subgroup H := E ⊔ Bo K B with hP₀
  have hc3 : c ^ 3 = 1 := hB.2 c hcB
  have hc1 : c ≠ 1 := by
    intro h
    apply hcout
    have : conjAut K c hcN = 1 := by
      ext k
      simp [conjAut, h]
    rw [this]
    exact Subgroup.one_mem _
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hZel : IsElemAbelian 3 (Subgroup.zpowers c) :=
    isElemAbelian_mono hB (Subgroup.zpowers_le.2 hcB)
  have hcBo : ∀ s ∈ Bo K B, c * s = s * c := fun s hs =>
    isElemAbelian_commute hB hcB (Subgroup.mem_inf.1 hs).1
  have hcP₀ : ∀ y ∈ P₀, c * y = y * c := by
    intro y hy
    have hcent : P₀ ≤ Subgroup.centralizer ({c} : Set H) := by
      refine sup_le (fun e he => ?_) (fun s hs => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcE e he
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcBo s hs
    exact Subgroup.mem_centralizer_iff.1 (hcent hy) c (Set.mem_singleton c)
  have hel : IsElemAbelian 3 (P₀ ⊔ Subgroup.zpowers c) :=
    hP₀el.sup_of_commute hZel fun a ha b hb => by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a c from (hcP₀ a ha).symm) i).eq
  refine ⟨hel, ?_⟩
  have hZnorm : Subgroup.zpowers c ≤ Subgroup.normalizer (P₀ : Set H) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_centralizes fun y hy => hcP₀ y hy
  have h1 := card_sup_mul_card_inf_of_le_normalizer hZnorm
  have hcP : c ∉ P₀ := by
    intro hc
    obtain ⟨x, hx, hxc⟩ := sup_Bo_le_inner (B := B) hEK hc
    apply hcout
    have : x = ⟨c, hcN⟩ := Subtype.ext hxc
    rw [this] at hx
    exact Subgroup.mem_comap.1 hx
  have hZcard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact hord
  have hinf : P₀ ⊓ Subgroup.zpowers c = ⊥ := by
    have hdvd : Nat.card ↥(P₀ ⊓ Subgroup.zpowers c) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : P₀ ⊓ Subgroup.zpowers c = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZcard])
      apply hcP
      have : c ∈ P₀ ⊓ Subgroup.zpowers c := by
        rw [heq]
        exact Subgroup.mem_zpowers c
      exact this.1
  rw [hinf, Subgroup.card_bot, mul_one, hZcard, hP₀c] at h1
  omega

theorem core3_all (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) (hB : IsElemAbelian 3 B)
    {E : Subgroup H} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) {c : H} (hcB : c ∈ B)
    (hcN : c ∈ Subgroup.normalizer (K : Set H)) (hcout : conjAut K c hcN ∉ innerAut ↥K)
    (hcE : ∀ y ∈ E, c * y = y * c)
    (hlt : Nat.card B < 3 * (Nat.card E * Nat.card (Bo K B)))
    (hall : ∀ P : Subgroup H, IsElemAbelian 3 P → Nat.card P ≤ Nat.card B) : False := by
  obtain ⟨hPel, hPc⟩ := big_sup3 hKc hB hEK hE hcB hcN hcout hcE
  have := hall _ hPel
  omega

theorem core3_two (hKc : ∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) (hB : IsElemAbelian 3 B)
    {E : Subgroup H} (hEK : E ≤ K) (hE : IsElemAbelian 3 E) {c : H} (hcB : c ∈ B)
    (hcN : c ∈ Subgroup.normalizer (K : Set H)) (hcout : conjAut K c hcN ∉ innerAut ↥K)
    (hcE : ∀ y ∈ E, c * y = y * c) {W : Subgroup H} (hW2 : IsPGroup 2 W) (hWne : W ≠ ⊥)
    (hEW : E ≤ Subgroup.normalizer (W : Set H)) (hcW : c ∈ Subgroup.normalizer (W : Set H))
    (hBoW : Bo K B ≤ Subgroup.normalizer (W : Set H))
    (hlt : Nat.card B < 3 * (Nat.card E * Nat.card (Bo K B)))
    (hmax : ∀ P W' : Subgroup H, IsElemAbelian 3 P → IsPGroup 2 W' → W' ≠ ⊥ →
      P ≤ Subgroup.normalizer (W' : Set H) → Nat.card P ≤ Nat.card B) : False := by
  obtain ⟨hPel, hPc⟩ := big_sup3 hKc hB hEK hE hcB hcN hcout hcE
  have hPW : E ⊔ Bo K B ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set H) :=
    sup_le (sup_le hEW hBoW) ((Subgroup.zpowers_le).2 hcW)
  have := hmax _ W hPel hW2 hWne hPW
  omega

end Three

end CFSG.LocalAnalysis.GLTheoremA.D4Y
