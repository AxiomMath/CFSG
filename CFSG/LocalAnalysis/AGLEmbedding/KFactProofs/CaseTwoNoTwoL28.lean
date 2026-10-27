module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoNoTwoSplit
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28Model

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.L28Local

open CFSG.Quasithin.F6.L28Res

set_option synthInstance.maxSize 1024

theorem finite_checks_T0 :
    (∀ x : G8, x * x * (x * x) * (x * x * (x * x)) = 1 → x * x = 1) ∧
    (∀ s ∈ T0list, s * s * s = 1 → s ≠ 1 → ∀ u : G8, u ≠ 1 → u * u = 1 →
      s * u * s⁻¹ * u = u * (s * u * s⁻¹) → False) := by
  decide +kernel

theorem not_commute_conj : ∀ t u : G8, t * t * t = 1 → t ≠ 1 → u ≠ 1 → u * u = 1 →
    t * u * t⁻¹ * u = u * (t * u * t⁻¹) → False := by
  intro t u h3 ht1 hu1 huu hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht3 : t ^ 3 = 1 := by simpa [pow_succ, mul_assoc] using h3
  have hp : IsPGroup 3 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime ht3 ht1]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_of_card_nine card_G8 (card_sylow_three (MulEquiv.refl G8) Q)
    card_T0
  have hs : g * t * g⁻¹ ∈ T0list := mem_T0_iff.1 ((hg t).1 (hQ (Subgroup.mem_zpowers t)))
  have hconj : ∀ z : G8, z = 1 ↔ g * z * g⁻¹ = 1 := fun z => by
    constructor
    · rintro rfl
      group
    · intro h
      simpa [mul_assoc] using congrArg (fun w => g⁻¹ * w * g) h
  refine finite_checks_T0.2 (g * t * g⁻¹) hs ?_ ?_ (g * u * g⁻¹) ?_ ?_ ?_
  · calc g * t * g⁻¹ * (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t * t) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  · exact fun h => ht1 ((hconj t).2 h)
  · exact fun h => hu1 ((hconj u).2 h)
  · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [huu]; group
  · calc g * t * g⁻¹ * (g * u * g⁻¹) * (g * t * g⁻¹)⁻¹ * (g * u * g⁻¹)
        = g * (t * u * t⁻¹ * u) * g⁻¹ := by group
      _ = g * (u * (t * u * t⁻¹)) * g⁻¹ := by rw [hc]
      _ = g * u * g⁻¹ * (g * t * g⁻¹ * (g * u * g⁻¹) * (g * t * g⁻¹)⁻¹) := by group

theorem eq_bot_of_normalizes {G : Type} [Group G] [Finite G]
    (hG : Nat.card G = 504) (hA : Nat.card (MulAut G) = 1512)
    (hZ : ∀ g : G, (∀ x, g * x = x * g) → g = 1)
    (hexp : ∀ x : G, x * x * (x * x) * (x * x * (x * x)) = 1 → x * x = 1)
    (hkey : ∀ t u : G, t * t * t = 1 → t ≠ 1 → u ≠ 1 → u * u = 1 →
      t * u * t⁻¹ * u = u * (t * u * t⁻¹) → False)
    {t : G} (ht : orderOf t = 3) {U : Subgroup (MulAut G)} (hU : IsPGroup 2 U)
    (hN : MulAut.conj t ∈ Subgroup.normalizer (U : Set (MulAut G))) : U = ⊥ := by
  set I : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range with hI
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    refine Subgroup.mem_bot.2 (hZ g fun x => ?_)
    have := congrArg (fun α : MulAut G => α x) (MonoidHom.mem_ker.mp hg)
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [this]
  have hIcard : Nat.card I = 504 := by
    rw [← hG]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hIidx : I.index = 3 := by
    have h1 := I.card_mul_index
    rw [hIcard, hA] at h1
    omega
  have := L28Data.normal_range_conj G
  have hUI : U ≤ I := by
    intro f hf
    obtain ⟨k, hk⟩ := hU ⟨f, hf⟩
    have hfk : f ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hf3 : f ^ 3 ∈ I := by simpa [hIidx] using Subgroup.pow_index_mem I f
    have hcop : Nat.Coprime 3 (orderOf f) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hfk)
        (Nat.Coprime.pow_right k (by norm_num))
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact I.pow_mem hf3 m
  have hsq : ∀ g : G, MulAut.conj g ∈ U → g * g = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hU ⟨MulAut.conj g, hg⟩
    have hgk : g ^ (2 ^ k) = 1 := by
      apply hinj
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val hk
    have h2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hgk
    have h504 : orderOf g ∣ 504 := hG ▸ orderOf_dvd_natCard g
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    have hj3 : j ≤ 3 := by
      by_contra hcon
      have : 2 ^ 4 ∣ 504 := (pow_dvd_pow 2 (by omega)).trans (hj ▸ h504)
      omega
    have h8 : g ^ 8 = 1 := by
      have : orderOf g ∣ 8 := by
        rw [hj]
        exact pow_dvd_pow 2 hj3
      exact orderOf_dvd_iff_pow_eq_one.1 this
    apply hexp
    rw [← h8]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  by_contra hne
  obtain ⟨⟨f, hfU⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨u, rfl⟩ := hUI hfU
  have hu1 : u ≠ 1 := fun h => hf1 (Subtype.ext (by simp [h]))
  have huu : u * u = 1 := hsq u hfU
  have hv : MulAut.conj (t * u * t⁻¹) ∈ U := by
    have := (Subgroup.mem_normalizer_iff.1 hN (MulAut.conj u)).1 hfU
    simpa using this
  have hvv : (t * u * t⁻¹) * (t * u * t⁻¹) = 1 := hsq _ hv
  have huv : (u * (t * u * t⁻¹)) * (u * (t * u * t⁻¹)) = 1 := by
    apply hsq
    rw [map_mul]
    exact U.mul_mem hfU hv
  have ht3 : t * t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa [pow_succ, mul_assoc] using this
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  apply hkey t u ht3 ht1 hu1 huu
  set v := t * u * t⁻¹ with hvdef
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have h1 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huv
  rw [mul_inv_rev, hui, hvi] at h1
  exact h1

end KFactProofs.L28Local

open CFSG.Open KFactProofs.L28Local CFSG.Quasithin.F6.L28Res

theorem kFactCaseTwoNoTwoL28 : KFactCaseTwoNoTwoL28 := by
  rintro p K _ _ ⟨rfl, d, hd, he⟩ t ht U hU hN
  have hK : IsCaseTwoGroup 3 K := ⟨d, Or.inl ⟨rfl, hd⟩, he⟩
  obtain ⟨ε⟩ := nonempty_equiv_G8 hK
  refine eq_bot_of_normalizes (G := K) ?_ ?_ ?_ ?_ ?_ ht hU hN
  · rw [Nat.card_congr ε.toEquiv, card_G8]
  · rw [Nat.card_congr (MulAut.congr ε).toEquiv]
    exact card_mulAut
  · intro g hg
    have hc : ∀ y : G8, ε g * y = y * ε g := fun y => by
      obtain ⟨x, rfl⟩ := ε.surjective y
      rw [← map_mul, ← map_mul, hg x]
    exact ε.injective (by rw [map_one]; exact eq_one_of_commute _ (hc ga) (hc gb))
  · intro x hx
    have h : ε x * ε x * (ε x * ε x) * (ε x * ε x * (ε x * ε x)) = 1 := by
      simpa only [map_mul, map_one] using congrArg ε hx
    exact ε.injective (by simpa only [map_mul, map_one] using finite_checks_T0.1 (ε x) h)
  · intro t u h3 ht1 hu1 huu hc
    refine not_commute_conj (ε t) (ε u) ?_ ?_ ?_ ?_ ?_
    · simpa only [map_mul, map_one] using congrArg ε h3
    · exact fun h => ht1 (ε.injective (by rw [h, map_one]))
    · exact fun h => hu1 (ε.injective (by rw [h, map_one]))
    · simpa only [map_mul, map_one] using congrArg ε huu
    · simpa only [map_mul, map_inv] using congrArg ε hc

end CFSG.AGLEmbedding
