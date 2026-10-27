module

public import CFSG.HardMathSupport.Solomon.Coordinator.LpUpper
public import CFSG.HardMathSupport.Solomon.Proving.LowerFixed
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLower

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.Balance.Alt

@[expose] def HasCentTorus (p r : ℕ) (K : Type*) [Group K] : Prop :=
  ∃ E U : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ Subgroup.center K = ⊥ ∧
    U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.centralizer (U : Set K)

@[expose] def HasTorusFixed (p r : ℕ) (K : Type*) [Group K] (β : MulAut K) : Prop :=
  ∃ E U : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ Subgroup.center K = ⊥ ∧
    U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set K) ∧ (∀ x ∈ E, β x = x) ∧
      ∀ u ∈ U, β u ∈ U

theorem isElemAbelian_of_le_sub {p : ℕ} {M : Type*} [Group M] {A B : Subgroup M} (hAB : A ≤ B)
    (hB : IsElemAbelian p B) : IsElemAbelian p A := CFSG.Open.IsElemAbelian.mono hB hAB

variable {G : Type} [Group G] [Finite G]

theorem five_count_basic {X B : Subgroup G} (hBX : B ≤ X) (hB : IsElemAbelian 5 B)
    (hrank : GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B) {L : Subgroup G}
    (hL : GLAPComponent 5 X L) (hA2 : HasCentTorus 5 2 (barOf 5 L))
    (hAcard : Nat.card (autBar 5 B L) ≤ 5 ^ 3) :
    B ≤ Subgroup.normalizer (L : Set G) ∧
      CFSG.Open.pRank 5 B = CFSG.Open.pRank 5 (centB 5 B L) +
        CFSG.Open.pRank 5 (autBar 5 B L) := by
  classical
  have hp : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  obtain ⟨E, U, hE, hEc, hEZ, hU1, hU2, hEU⟩ := hA2
  have hZ : ∀ x ∈ E, (∀ y, x * y = y * x) → x = 1 := by
    intro x hx hc
    have : x ∈ E ⊓ Subgroup.center (barOf 5 L) :=
      ⟨hx, Subgroup.mem_center_iff.2 fun g => (hc g).symm⟩
    rw [hEZ, Subgroup.mem_bot] at this
    exact this
  obtain ⟨P, S, hPc, hPe, hPcard, hS, hS2, hPS⟩ := exists_twoLocal_lower_central hp
    (by norm_num) hBX hB hL E U 2 hZ ⟨hE.1, hE.2, hEc⟩ ⟨hU1, hU2⟩ hEU
  have hpgB : IsPGroup 5 B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card B = 5 ^ m := IsPGroup.iff_card.1 hpgB
  have hAe := isElemAbelian_autBar hB L
  have hpgA : IsPGroup 5 (autBar 5 B L) := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hAe.2 _ g.2)⟩
  obtain ⟨β, hβ⟩ : ∃ β, Nat.card (autBar 5 B L) = 5 ^ β := IsPGroup.iff_card.1 hpgA
  have hpgC : IsPGroup 5 (centB 5 B L) := hpgB.to_le (centB_le 5 B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB 5 B L) = 5 ^ γ := IsPGroup.iff_card.1 hpgC
  have hcardB := card_B_eq 5 B L
  rw [hm, hβ, hγ] at hcardB
  have hdvd : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B ∣ 5 ^ m :=
    ⟨5 ^ β * 5 ^ γ, hcardB.trans rfl⟩
  obtain ⟨a, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvd |>.imp fun a h => h.2
  have hmaβγ : m = a + (β + γ) := by
    rw [ha, ← pow_add, ← pow_add] at hcardB
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) hcardB
  have hPcard' : Nat.card P = 5 ^ (γ + 2 * 5 ^ a) := by
    rw [hPcard, hγ, ha, ← pow_add]
  have hrkP : CFSG.Open.pRank 5 P = γ + 2 * 5 ^ a := pRank_eq_of_card hp ⟨hPc, hPe⟩ hPcard'
  have hrkB : CFSG.Open.pRank 5 B = m := pRank_eq_of_card hp hB hm
  have h1 : CFSG.Open.pRank 5 P ≤ GLATwoLocalRank 5 ↥X :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
  have h2 : γ + 2 * 5 ^ a ≤ a + (β + γ) := by
    rw [← hrkP, ← hmaβγ, ← hrkB]
    exact h1.trans hrank
  have hβ3 : β ≤ 3 := by
    rw [hβ] at hAcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hAcard
  have hpa := two_mul_add_one_le_pow (by norm_num : 3 ≤ 5) a
  have ha0 : a = 0 := by
    by_contra ha0
    have h5a : 5 ≤ 5 ^ a := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ a := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 ha0)
    nlinarith
  subst ha0
  refine ⟨?_, ?_⟩
  · have h1' : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B = 1 := by rw [ha, pow_zero]
    rw [Subgroup.relIndex_eq_one] at h1'
    exact fun b hb => (h1' hb).2
  · rw [hrkB, pRank_eq_of_card hp (isElemAbelian_of_le_sub (centB_le 5 B L) hB) hγ,
      pRank_eq_of_card hp hAe hβ]
    omega

omit [Finite G] in
theorem centB_le_normalizer (p : ℕ) (B L : Subgroup G) :
    centB p B L ≤ Subgroup.normalizer (L : Set G) := fun _ hb => (mem_centB.1 hb).choose

theorem isCompLocallyBalanced_five_of_data {X B : Subgroup G} (hBX : B ≤ X)
    (hB : IsElemAbelian 5 B) (hrank : GLATwoLocalRank 5 ↥X ≤ CFSG.Open.pRank 5 B)
    {L : Subgroup G} (hL : GLAPComponent 5 X L) (R : Subgroup (MulAut (barOf 5 L)))
    (hinn : innerAut (barOf 5 L) ≤ R) (hU : HeisUpper 5 (barOf 5 L) R)
    (hA2 : HasCentTorus 5 2 (barOf 5 L)) (hB3 : HasTorusFixed 5 3 (barOf 5 L) 1)
    (hC3 : ∀ β : MulAut (barOf 5 L), β ∉ R → β ^ 5 = 1 → HasTorusFixed 5 3 (barOf 5 L) β) :
    IsCompLocallyBalanced 5 2 B L := by
  classical
  have hp : Nat.Prime 5 := Nat.prime_five
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  intro D hD H hH hDH
  by_contra hΔ
  obtain ⟨hDA, hDe, hD2⟩ := hD
  have hAe := isElemAbelian_autBar hB L
  obtain ⟨hAcard, hAR⟩ := hU D hDe hD2 H hH hDH hΔ _ hDA hAe
  obtain ⟨hBN, hm⟩ := five_count_basic hBX hB hrank hL hA2 hAcard
  have hpgA : IsPGroup 5 (autBar 5 B L) := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hAe.2 _ g.2)⟩
  obtain ⟨β, hβ⟩ : ∃ β, Nat.card (autBar 5 B L) = 5 ^ β := IsPGroup.iff_card.1 hpgA
  have hβ3 : β ≤ 3 := by
    rw [hβ] at hAcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hAcard
  have hβ2 : 2 ≤ β := by
    have hdvd : 5 ^ 2 ∣ 5 ^ β := by rw [← hD2, ← hβ]; exact Subgroup.card_dvd_of_le hDA
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
  have hpgB : IsPGroup 5 B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  have hpgC : IsPGroup 5 (centB 5 B L) := hpgB.to_le (centB_le 5 B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB 5 B L) = 5 ^ γ := IsPGroup.iff_card.1 hpgC
  have hmB : CFSG.Open.pRank 5 B = γ + β := by
    rw [hm, pRank_eq_of_card hp (isElemAbelian_of_le_sub (centB_le 5 B L) hB) hγ,
      pRank_eq_of_card hp hAe hβ]
  have hcN := centB_le_normalizer 5 B L
  have hlow : ∀ (C : Subgroup G) (hCB : C ≤ B) (hCN : C ≤ Subgroup.normalizer (L : Set G))
      (c : ℕ), Nat.card C = 5 ^ c → ∀ E U : Subgroup (barOf 5 L), IsElemAbelian 5 E →
      Nat.card E = 5 ^ 3 → E ⊓ Subgroup.center (barOf 5 L) = ⊥ → U ≠ ⊥ → IsPGroup 2 U →
      E ≤ Subgroup.normalizer (U : Set (barOf 5 L)) →
      (∀ x (hx : x ∈ C), ∀ e ∈ E, barAut 5 L ⟨x, hCN hx⟩ e = e) →
      (∀ x (hx : x ∈ C), ∀ u ∈ U, barAut 5 L ⟨x, hCN hx⟩ u ∈ U) →
      (∀ x (hx : x ∈ C), barAut 5 L ⟨x, hCN hx⟩ ∈ innerAut (barOf 5 L) →
        barAut 5 L ⟨x, hCN hx⟩ = 1) → c + 3 ≤ γ + β := by
    intro C hCB hCN c hc E U hE hEc hEZ hU1 hU2 hEU hCE hCU hCinn
    obtain ⟨P, S, hPc, hPe, hPcard, hS, hS2, hPS⟩ :=
      CFSG.HardMathSupport.Solomon.Proving.exists_twoLocal_lower_fixed hp (by norm_num) hBX hB
        hL C hCB hCN E U hE hEZ ⟨hU1, hU2⟩ hEU hCE hCU hCinn
    have hPcard' : Nat.card P = 5 ^ (c + 3) := by rw [hPcard, hc, hEc, ← pow_add]
    have hrkP : CFSG.Open.pRank 5 P = c + 3 := pRank_eq_of_card hp ⟨hPc, hPe⟩ hPcard'
    have h1 : CFSG.Open.pRank 5 P ≤ GLATwoLocalRank 5 ↥X :=
      pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
    rw [← hrkP, ← hmB]
    exact h1.trans hrank
  have hcentB1 : ∀ x (hx : x ∈ centB 5 B L), barAut 5 L ⟨x, hcN hx⟩ = 1 := by
    intro x hx
    obtain ⟨hx', -, h1⟩ := mem_centB.1 hx
    exact h1
  interval_cases β
  ·
    obtain ⟨E, U, hE, hEc, hEZ, hU1, hU2, hEU, -, -⟩ := hB3
    have := hlow (centB 5 B L) (centB_le 5 B L) hcN γ hγ E U hE hEc hEZ hU1 hU2 hEU
      (fun x hx e _ => by rw [hcentB1 x hx]; rfl) (fun x hx u hu => by rw [hcentB1 x hx]; exact hu)
      (fun x hx _ => hcentB1 x hx)
    omega
  ·
    obtain ⟨z, hzA, hzD⟩ : ∃ z ∈ autBar 5 B L, z ∉ D := by
      by_contra hc
      push Not at hc
      have := Subgroup.card_le_of_le (show autBar 5 B L ≤ D from hc)
      rw [hβ, hD2] at this
      norm_num at this
    have hzR : z ∉ R := fun h => hzD (hAR z hzA h)
    have hz5 : z ^ 5 = 1 := hAe.2 z hzA
    obtain ⟨E, U, hE, hEc, hEZ, hU1, hU2, hEU, hzE, hzU⟩ := hC3 z hzR hz5
    obtain ⟨⟨n, hnN⟩, hnB, hnz⟩ := hzA
    have hnB' : n ∈ B := (Subgroup.mem_inf.1 ((Subgroup.mem_subgroupOf).1 hnB)).1
    set C : Subgroup G := ((Subgroup.zpowers z).comap (barAut 5 L)).map
      (Subgroup.normalizer (L : Set G)).subtype ⊓ B with hCdef
    have hCB : C ≤ B := inf_le_right
    have hCN : C ≤ Subgroup.normalizer (L : Set G) := by
      rintro _ ⟨⟨x, -, rfl⟩, -⟩
      exact x.2
    have hCz : ∀ x (hx : x ∈ C), barAut 5 L ⟨x, hCN hx⟩ ∈ Subgroup.zpowers z := by
      rintro _ ⟨⟨x, hx, rfl⟩, -⟩
      exact hx
    have hzpow : ∀ y ∈ Subgroup.zpowers z, ∃ k : ℕ, y = z ^ k := by
      intro y hy
      obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 hy : y ∈ Submonoid.powers z)
      exact ⟨k, hk.symm⟩
    have hzk_fix : ∀ k : ℕ, ∀ e ∈ E, (z ^ k) e = e := by
      intro k
      induction k with
      | zero => intro e _; rfl
      | succ k ih =>
        intro e he
        rw [pow_succ, MulAut.mul_apply, hzE e he, ih e he]
    have hzk_U : ∀ k : ℕ, ∀ u ∈ U, (z ^ k) u ∈ U := by
      intro k
      induction k with
      | zero => intro u hu; exact hu
      | succ k ih =>
        intro u hu
        rw [pow_succ, MulAut.mul_apply]
        exact ih _ (hzU u hu)
    have hcentC : centB 5 B L ≤ C := by
      intro x hx
      obtain ⟨hx', hxB, h1⟩ := mem_centB.1 hx
      refine ⟨⟨⟨x, hx'⟩, ?_, rfl⟩, hxB⟩
      show barAut 5 L ⟨x, hx'⟩ ∈ Subgroup.zpowers z
      rw [h1]
      exact Subgroup.one_mem _
    have hnC : n ∈ C := ⟨⟨⟨n, hnN⟩, by
      show barAut 5 L ⟨n, hnN⟩ ∈ Subgroup.zpowers z
      rw [hnz]
      exact Subgroup.mem_zpowers z, rfl⟩, hnB'⟩
    have hnc : n ∉ centB 5 B L := by
      intro h
      obtain ⟨hn', -, h1⟩ := mem_centB.1 h
      have : z = 1 := by rw [← hnz]; exact h1
      apply hzR
      rw [this]
      exact Subgroup.one_mem _
    have hpgCC : IsPGroup 5 C := hpgB.to_le hCB
    obtain ⟨c, hc⟩ : ∃ c, Nat.card C = 5 ^ c := IsPGroup.iff_card.1 hpgCC
    have hcγ : γ + 1 ≤ c := by
      have hlt : Nat.card (centB 5 B L) < Nat.card C := by
        refine Subgroup.card_lt_of_lt (lt_of_le_of_ne hcentC fun h => hnc ?_)
        rw [h]
        exact hnC
      rw [hγ, hc] at hlt
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 5)).1 hlt
      omega
    have hCinn : ∀ x (hx : x ∈ C), barAut 5 L ⟨x, hCN hx⟩ ∈ innerAut (barOf 5 L) →
        barAut 5 L ⟨x, hCN hx⟩ = 1 := by
      intro x hx hinner
      obtain ⟨k, hk⟩ := hzpow _ (hCz x hx)
      rw [hk] at hinner ⊢
      by_contra hk1
      apply hzR
      have hkR : z ^ k ∈ R := hinn hinner
      have hko : orderOf (z ^ k) = 5 := orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul,
        hz5, one_pow]) hk1
      have hz1 : z ≠ 1 := fun h => hk1 (by rw [h, one_pow])
      have hzo : orderOf z = 5 := orderOf_eq_prime hz5 hz1
      have hcop : Nat.Coprime k 5 := by
        by_contra hnc'
        have h5k : 5 ∣ k := (Nat.Prime.coprime_iff_not_dvd hp |>.not_left).1 (by
          rwa [Nat.coprime_comm] at hnc')
        obtain ⟨j, rfl⟩ := h5k
        exact hk1 (by rw [pow_mul, hz5, one_pow])
      obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime
        (show Nat.Coprime k (orderOf z) by rw [hzo]; exact hcop)
      have hmemR : (z ^ k) ^ j ∈ R := Subgroup.pow_mem _ hkR j
      rwa [hj] at hmemR
    have := hlow C hCB hCN c hc E U hE hEc hEZ hU1 hU2 hEU
      (fun x hx e he => by
        obtain ⟨k, hk⟩ := hzpow _ (hCz x hx)
        rw [hk]
        exact hzk_fix k e he)
      (fun x hx u hu => by
        obtain ⟨k, hk⟩ := hzpow _ (hCz x hx)
        rw [hk]
        exact hzk_U k u hu)
      hCinn
    omega

end CFSG.HardMathSupport.Solomon.Coordinator
