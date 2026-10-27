module

public import CFSG.GH74.GLS.Stage4.T6Defs
public import CFSG.GH74.GLS.IVK.Statements.Sec4b
public import CFSG.GH74.GLS.Stage4.T2Steps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem t5_prime_aux {q : ℕ} (hq3 : 3 ≤ q) (hqodd : Odd q) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ r ∣ q ^ 3 - 1 ∧ ¬ r ∣ q - 1 := by
  have hc0 : q ^ 2 + q + 1 ≠ 0 := by positivity
  have hcodd : Odd (q ^ 2 + q + 1) := by
    have h2 : Odd (q ^ 2) := hqodd.pow
    have h3 : Even (q ^ 2 + q) := h2.add_odd hqodd
    exact h3.add_one
  obtain ⟨j, c', hc3, hcj⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 3 (by norm_num)
  have h9 : (q ^ 2 + q + 1) % 9 ≠ 0 := by
    have h := Nat.mod_lt q (by norm_num : 9 > 0)
    have : q % 9 < 9 := h
    have e : (q ^ 2 + q + 1) % 9 = ((q % 9) ^ 2 + q % 9 + 1) % 9 := by
      simp [Nat.add_mod, Nat.pow_mod]
    rw [e]
    interval_cases (q % 9) <;> decide
  have hc13 : 13 ≤ q ^ 2 + q + 1 := by nlinarith
  have hj : j ≤ 1 := by
    by_contra hj
    push Not at hj
    have : 9 ∣ q ^ 2 + q + 1 := by
      rw [hcj]
      exact Dvd.dvd.mul_right (by
        have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj
        simpa using this) c'
    omega
  have hc'1 : c' ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hcj
    interval_cases j <;> omega
  have hrp : (Nat.minFac c').Prime := Nat.minFac_prime hc'1
  have hrc : Nat.minFac c' ∣ q ^ 2 + q + 1 := by
    rw [hcj]
    exact Dvd.dvd.mul_left (Nat.minFac_dvd c') _
  have hr3 : Nat.minFac c' ≠ 3 := by
    intro h
    apply hc3
    rw [← h]
    exact Nat.minFac_dvd c'
  refine ⟨Nat.minFac c', hrp, ?_, ?_, ?_⟩
  · exact Odd.of_dvd_nat hcodd hrc
  · have hq1 : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have : (k + 1) ^ 3 = k * ((k + 1) ^ 2 + (k + 1) + 1) + 1 := by ring
      omega
    rw [hq1]
    exact Dvd.dvd.mul_left hrc _
  · intro hdvd
    have hq2 : q ^ 2 + q + 1 = (q - 1) * (q + 2) + 3 := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    have h3 : Nat.minFac c' ∣ 3 := by
      have h4 : Nat.minFac c' ∣ (q - 1) * (q + 2) := Dvd.dvd.mul_right hdvd _
      rw [hq2] at hrc
      exact (Nat.dvd_add_right h4).1 hrc
    have := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).1 h3
    exact hr3 this

theorem t5_singular {G : Type} [Group G] [Finite G] (N : T2N3 G) (u : G) (h : Ch6Sec5 N u)
    (hq : N.q₁ = N.q₂ ^ 3) :
    ∃ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z ∧ (orderOf y).Prime ∧ Odd (orderOf y) ∧
      orderOf y ∣ N.q₁ - 1 ∧ N.a * y * N.a⁻¹ = y := by
  have hloc := h.loc
  have hW := h.weyl
  obtain ⟨r, hr, hrodd, hr1, hr2⟩ := t5_prime_aux hloc.q₂_ge hloc.q₂_odd
  rw [← hq] at hr1
  have hHc := hloc.H_comm
  have hc1 : Nat.card ↥(N.H ⊓ N.K₁) = N.q₁ - 1 := hloc.card_H_K₁
  have hc2 : Nat.card ↥(N.H ⊓ N.K₂) = N.q₂ - 1 := hloc.card_H_K₂
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N.H ⊓ N.K₁)) r (by rw [hc1]; exact hr1)
  set y : G := (x : G) with hy
  have hyH₁ : y ∈ N.H ⊓ N.K₁ := x.2
  have hyord : orderOf y = r := by rw [hy, Subgroup.orderOf_coe]; exact hx
  have hyH : y ∈ N.H := hyH₁.1
  have hyr : y ^ r = 1 := by rw [← hyord]; exact pow_orderOf_eq_one y
  have key : ∀ g ∈ N.H, g ^ r = 1 → g ∈ N.H ⊓ N.K₁ := by
    intro g hg hgr
    set L : Subgroup G := (N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂) with hL
    have hcomm' : ∀ a b : ↥N.H, a * b = b * a := fun a b => Subtype.ext (hHc a a.2 b b.2)
    have : (L.subgroupOf N.H).Normal := ⟨fun n hn g' => by
      have h1 : g' * n * g'⁻¹ = n := by rw [hcomm' g' n]; group
      rw [h1]; exact hn⟩
    have hidx : (L.subgroupOf N.H).index = 2 := hloc.H_idx
    have hg2 : g ^ 2 ∈ L := by
      have h1 := Subgroup.pow_index_mem (L.subgroupOf N.H) (⟨g, hg⟩ : ↥N.H)
      rw [hidx] at h1
      exact Subgroup.mem_subgroupOf.1 h1
    have hgL : g ∈ L := by
      obtain ⟨k, hk⟩ := hrodd
      have h1 : g = (g ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        have h2 : 2 * (k + 1) = r + 1 := by omega
        rw [h2, pow_succ, hgr, one_mul]
      rw [h1]
      exact Subgroup.pow_mem L hg2 (k + 1)
    have hcomm12 : ∀ a ∈ N.H ⊓ N.K₁, ∀ b ∈ N.H ⊓ N.K₂, a * b = b * a :=
      fun a ha b hb => hHc a ha.1 b hb.1
    obtain ⟨a, ha, b, hb, hgab⟩ := (mem_sup_iff_of_comm hcomm12 g).1 hgL
    have hb1 : b ^ (N.q₂ - 1) = 1 := by
      have h1 := pow_card_eq_one' (G := ↥(N.H ⊓ N.K₂)) (x := ⟨b, hb⟩)
      rw [hc2] at h1
      exact congrArg Subtype.val h1
    have hgm : g ^ (N.q₂ - 1) = a ^ (N.q₂ - 1) := by
      have hc : Commute a b := hcomm12 a ha b hb
      rw [hgab, hc.mul_pow, hb1, mul_one]
    have hcop : Nat.Coprime (N.q₂ - 1) (orderOf g) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hgr)
        (((Nat.Prime.coprime_iff_not_dvd hr).2 hr2).symm)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm, hgm]
    exact Subgroup.pow_mem _ (Subgroup.pow_mem _ ha _) m
  have hy1 : N.a * y * N.a⁻¹ ∈ N.H := (Subgroup.mem_normalizer_iff.1 hW.a_normH y).1 hyH
  have hy1r : (N.a * y * N.a⁻¹) ^ r = 1 := by rw [conj_pow, hyr]; group
  have hy1H₁ : N.a * y * N.a⁻¹ ∈ N.H ⊓ N.K₁ := key _ hy1 hy1r
  have hw1 : N.w₁ * (N.a * y * N.a⁻¹) * N.w₁⁻¹ = (N.a * y * N.a⁻¹)⁻¹ := hloc.w₁_inv _ hy1H₁
  have hw2 : N.w₁ * y * N.w₁⁻¹ = y⁻¹ := hloc.w₁_inv _ hyH₁
  obtain ⟨h₀, hh₀, hw3⟩ := hW.w₁_a
  have hh₀y : h₀ * y⁻¹ = y⁻¹ * h₀ := hHc h₀ hh₀ y⁻¹ (N.H.inv_mem hyH)
  have hcalc : N.w₁ * (N.a * y * N.a⁻¹) * N.w₁⁻¹ = N.a⁻¹ * y⁻¹ * N.a := by
    calc N.w₁ * (N.a * y * N.a⁻¹) * N.w₁⁻¹
        = (N.w₁ * N.a * N.w₁⁻¹) * (N.w₁ * y * N.w₁⁻¹) * (N.w₁ * N.a * N.w₁⁻¹)⁻¹ := by group
      _ = (N.a⁻¹ * h₀) * y⁻¹ * (N.a⁻¹ * h₀)⁻¹ := by rw [hw3, hw2]
      _ = N.a⁻¹ * (h₀ * y⁻¹) * h₀⁻¹ * N.a := by group
      _ = N.a⁻¹ * (y⁻¹ * h₀) * h₀⁻¹ * N.a := by rw [hh₀y]
      _ = N.a⁻¹ * y⁻¹ * N.a := by group
  have hrel : N.a * y⁻¹ * N.a⁻¹ = N.a⁻¹ * y⁻¹ * N.a := by
    rw [← hcalc, hw1]; group
  have h2 : N.a ^ 2 * y⁻¹ * (N.a ^ 2)⁻¹ = y⁻¹ := by
    calc N.a ^ 2 * y⁻¹ * (N.a ^ 2)⁻¹ = N.a * (N.a * y⁻¹ * N.a⁻¹) * N.a⁻¹ := by
          rw [pow_two]; group
      _ = N.a * (N.a⁻¹ * y⁻¹ * N.a) * N.a⁻¹ := by rw [hrel]
      _ = y⁻¹ := by group
  have h3 : N.a * y⁻¹ * N.a⁻¹ = y⁻¹ := by
    have hc : N.a ^ 3 * y⁻¹ * (N.a ^ 3)⁻¹ = y⁻¹ := by
      rw [hHc (N.a ^ 3) hW.a_cube y⁻¹ (N.H.inv_mem hyH)]; group
    calc N.a * y⁻¹ * N.a⁻¹ = N.a * (N.a ^ 2 * y⁻¹ * (N.a ^ 2)⁻¹) * N.a⁻¹ := by rw [h2]
      _ = N.a ^ 3 * y⁻¹ * (N.a ^ 3)⁻¹ := by rw [pow_two, pow_succ, pow_two]; group
      _ = y⁻¹ := hc
  have h4 : N.a * y * N.a⁻¹ = y := by
    calc N.a * y * N.a⁻¹ = (N.a * y⁻¹ * N.a⁻¹)⁻¹ := by group
      _ = (y⁻¹)⁻¹ := by rw [h3]
      _ = y := inv_inv y
  have hyz : y ∉ Subgroup.zpowers N.z := by
    intro hmem
    have h5 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Nat.card_zpowers, hloc.z_ord, hyord] at h5
    have h6 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h5
    exact (Nat.not_even_iff_odd.2 hrodd) (by rw [h6]; exact even_two)
  exact ⟨y, hyH₁, hyz, hyord ▸ hr, hyord ▸ hrodd, hyord ▸ hr1, h4⟩

theorem t5_transport {G : Type} [Group G] [Finite G] (hIVK : IVK_4_1_R_L3) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {z y : G} {K₂ J : Subgroup G}
    (hJy : J ≤ centralizer ({y} : Set G)) (hKJ : K₂ ≤ J)
    (hJ : IsSLnEps 3 ↥J 1 (p ^ n) ∨ IsLnEps 3 ↥J 1 (p ^ n))
    (hz2 : orderOf z = 2) (hzK : z ∈ K₂) (hzc : ∀ x ∈ K₂, z * x = x * z)
    {X : Subgroup G} (hXK : X ≤ K₂) (hXp : IsPGroup p ↥X) (hXc : Nat.card ↥X = p ^ n) :
    ∃ R : Subgroup G, IsPGroup p ↥R ∧ X ≤ R ∧ R ≤ centralizer (X : Set G) ∧
      Nat.card ↥R = (p ^ n) ^ 3 ∧ (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧
      (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧ (∀ r ∈ R, z * r * z⁻¹ * r ∈ X) ∧
      (∀ r ∈ R, y * r = r * y) := by
  have hXJ : X ≤ J := hXK.trans hKJ
  have hzJ : z ∈ J := hKJ hzK
  let z' : ↥J := ⟨z, hzJ⟩
  have hz'2 : orderOf z' = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk z hzJ
  have hX'c : X.subgroupOf J ≤ centralizer ({z'} : Set ↥J) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply Subtype.ext
    exact hzc x (hXK (Subgroup.mem_subgroupOf.1 hx))
  have hX'p : IsPGroup p ↥(X.subgroupOf J) := hXp.comap_subtype (K := J)
  have hX'card : Nat.card ↥(X.subgroupOf J) = p ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, hXc]
  obtain ⟨R', -, hR'p, hXR', hR'c, hR'card, hZ, hcom1, hcom2, hinv⟩ :=
    hIVK ↥J p n hp hp2 hJ z' hz'2 (X.subgroupOf J) hX'c hX'p hX'card
  have hmapX : (X.subgroupOf J).map J.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXJ
  have hinj : Function.Injective J.subtype := J.subtype_injective
  refine ⟨R'.map J.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 3 * n) ?_
    rw [Subgroup.card_map_of_injective hinj, hR'card, ← pow_mul, mul_comm]
  · rw [← hmapX]
    exact Subgroup.map_mono hXR'
  · rintro _ ⟨r', hr', rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [← hmapX] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have := (Subgroup.mem_centralizer_iff.1 (hR'c hr')) x' hx'
    exact congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective hinj, hR'card]
  · rintro _ ⟨r', hr', rfl⟩ hcomm
    have : r' ∈ X.subgroupOf J := by
      refine hZ r' hr' (fun s' hs' => ?_)
      exact Subtype.ext (hcomm _ ⟨s', hs', rfl⟩)
    exact Subgroup.mem_subgroupOf.1 this
  · rw [← hmapX, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcom1
  · rintro _ ⟨r', hr', rfl⟩ _ ⟨s', hs', rfl⟩
    have := hcom2 r' hr' s' hs'
    exact Subgroup.mem_subgroupOf.1 this
  · rintro _ ⟨r', hr', rfl⟩
    have := hinv r' hr'
    exact Subgroup.mem_subgroupOf.1 this
  · rintro _ ⟨r', hr', rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hJy r'.2)).symm

@[expose] def Ch6T2Prop56Gt : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q₁ q₂ : ℕ), IsTwoCentralG2TypeG2At G Gs q₁ q₂ →
      ¬ (q₁ = 9 ∧ q₂ = 9) → (¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n ∧ q₂ = 3 ^ n) → q₂ < q₁ →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ p : ℕ, Ch6NumD p q₁ q₂ →
              ∀ (N : T2N3 G) (u : G), N.z = z → N.K₁ = K₁ → N.K₂ = K₂ → N.q₁ = q₁ → N.q₂ = q₂ →
                Ch6Sec5 N u →
                  ∀ y ∈ N.H ⊓ N.K₁, y ∉ Subgroup.zpowers N.z → (orderOf y).Prime → Odd (orderOf y) →
                    N.a * y * N.a⁻¹ = y →
                      ∃ J : Subgroup G, J ≤ centralizer ({y} : Set G) ∧ K₂ ≤ J ∧
                        (IsSLnEps 3 ↥J 1 q₂ ∨ IsLnEps 3 ↥J 1 q₂)

@[expose] def Ch6T2TSingEq : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs] (q : ℕ), IsTwoCentralG2TypeG2At G Gs q q →
      q ≠ 9 → (¬ ∃ n : ℕ, 3 ≤ n ∧ q = 3 ^ n) →
        ∀ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
          Ch6Setup G Gs q q z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t →
            ∀ p : ℕ, Ch6NumD p q q → Ch6TSing p q z K₁ K₂ ∨ Ch6TSing p q z K₂ K₁

theorem ch6T2TSing_of_leaves (h3 : Ch6T2P51) (h4 : Ch6T2P52) (h5 : Ch6T2P53)
    (hP56 : Ch6T2Prop56Gt) (hEq : Ch6T2TSingEq) (h41 : IVK_4_1_R_L3) : Ch6T2TSing := by
  intro G _ _ hStd hr Gs _ q₁ q₂ hAt h99 hn z K₁ K₂ F₁ F₂ _ _ t hSet hRem p hNum
  by_cases hlt : q₂ < q₁
  · left
    have hq : q₁ = q₂ ^ 3 := by
      rcases hNum.q_rel with h | h
      · omega
      · exact h
    have hmod : q₁ % 4 = q₂ % 4 := by rw [hq]; exact pow_three_mod_four_of_odd hSet.odd₂
    obtain ⟨N₁, u, hz, hK₁, hK₂, hq₁, hq₂, hLoc, hCoord⟩ :=
      h3 G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem hmod
    obtain ⟨F, hF5⟩ :=
      h4 G Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem N₁ u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
    obtain ⟨a, hau, hWeyl⟩ :=
      h5 G hr Gs q₁ q₂ z K₁ K₂ F₁ F₂ t hSet hRem (⟨N₁, F⟩ : T2N2 G) u hz hK₁ hK₂ hq₁ hq₂ hLoc
        hCoord hF5
    let N₃ : T2N3 G := ⟨⟨N₁, F⟩, a⟩
    have hSec : Ch6Sec5 N₃ u := ⟨hLoc, hF5, hWeyl, hau⟩
    have hq₃ : N₃.q₁ = N₃.q₂ ^ 3 := by
      show N₁.q₁ = N₁.q₂ ^ 3
      rw [hq₁, hq₂]
      exact hq
    obtain ⟨y, hyH, hyz, hyp, hyodd, hyq, hya⟩ := t5_singular N₃ u hSec hq₃
    obtain ⟨J, hJy, hKJ, hJ⟩ :=
      hP56 G hStd hr Gs q₁ q₂ hAt h99 hn hlt z K₁ K₂ F₁ F₂ t hSet hRem p hNum N₃ u hz hK₁ hK₂ hq₁ hq₂
        hSec y hyH hyz hyp hyodd hya
    obtain ⟨n, hn₂⟩ := hNum.q₂_pow
    have hyK₁ : y ∈ K₁ := by
      have : y ∈ N₃.K₁ := hyH.2
      rw [show N₃.K₁ = K₁ from hK₁] at this
      exact this
    have hyz' : y ∉ Subgroup.zpowers z := by
      have : y ∉ Subgroup.zpowers N₃.z := hyz
      rwa [show N₃.z = z from hz] at this
    have hz2 : orderOf z = 2 := hSet.central.1
    have hzc : ∀ x ∈ K₂, z * x = x * z := by
      intro x hx
      have : x ∈ centralizer ({z} : Set G) := hSet.le_centralizer (Subgroup.mem_sup_right hx)
      exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm
    refine ⟨y, hyK₁, hyz', ?_, ?_⟩
    ·
      intro hpy
      have hyq' : orderOf y ∣ q₁ - 1 := by
        have : N₃.q₁ = q₁ := hq₁
        rw [this] at hyq
        exact hyq
      have h1 : p ∣ q₁ - 1 := dvd_trans hpy hyq'
      obtain ⟨m, hm⟩ := hNum.q₁_pow
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := hSet.five
        simp [hm] at this
      have h2 : p ∣ q₁ := by rw [hm]; exact dvd_pow_self p hm0
      have h3' : p ∣ q₁ - (q₁ - 1) := Nat.dvd_sub h2 h1
      have h4' : q₁ - (q₁ - 1) = 1 := by have := hSet.five; omega
      rw [h4'] at h3'
      exact hNum.prime.one_lt.ne' (Nat.dvd_one.1 h3')
    · intro X hXK hXp hXc
      have hJ' : IsSLnEps 3 ↥J 1 (p ^ n) ∨ IsLnEps 3 ↥J 1 (p ^ n) := by rw [← hn₂]; exact hJ
      have hXc' : Nat.card ↥X = p ^ n := by rw [hXc, hn₂]
      obtain ⟨R, hRp, hXR, hRc, hRcard, hRZ, hRcom1, hRcom2, hRinv, hRy⟩ :=
        t5_transport h41 hNum.prime hNum.p_ne_two hJy hKJ hJ' hz2 hSet.z_mem₂ hzc hXK hXp hXc'
      exact ⟨R, hRp, hXR, hRc, by rw [hRcard, hn₂], hRZ, hRcom1, hRcom2, hRinv, hRy⟩
  · have heq : q₁ = q₂ := le_antisymm (not_lt.1 hlt) hSet.le
    subst heq
    have h99' : q₁ ≠ 9 := fun h => h99 ⟨h, h⟩
    have hn' : ¬ ∃ n : ℕ, 3 ≤ n ∧ q₁ = 3 ^ n := by
      rintro ⟨n, hn3, hqn⟩
      exact hn ⟨n, hn3, hqn, hqn⟩
    rcases hEq G hStd hr Gs q₁ hAt h99' hn' z K₁ K₂ F₁ F₂ t hSet hRem p hNum with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

end CFSG.GH74.GLS.Stage4.Rest
