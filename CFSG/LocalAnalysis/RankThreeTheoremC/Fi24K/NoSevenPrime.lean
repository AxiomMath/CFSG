module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
public import CFSG.RankThree.PartOne.KE8F.HyperGen
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.HardMathSupport.Dickson.I271 Subgroup

theorem inf_centralizer_eq_bot_of_le_normalizer {G : Type} [Group G] [Finite G] {c : G}
    {F H N : Subgroup G} (hL : SevenLine 7 c F) (hFH : F ≤ H)
    (hN : ¬ 7 ∣ Nat.card N) (hHN : H ≤ normalizer (N : Set G)) :
    N ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hNF : N ⊓ F = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hL.card_eq]
    exact Nat.prime_seven.coprime_pow_of_not_dvd hN
  have hcent : ∀ d ∈ N ⊓ Subgroup.centralizer ({c} : Set G),
      d ∈ Subgroup.centralizer (F : Set G) := by
    intro d hd
    obtain ⟨hdN, hdc⟩ := Subgroup.mem_inf.1 hd
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hdf : d * f * d⁻¹ ∈ F := hL.norm d hdc f hf
    have hfn : f * d⁻¹ * f⁻¹ ∈ N := by
      have := (Subgroup.mem_normalizer_iff.1 (hHN (hFH hf))) d⁻¹
      exact this.1 (N.inv_mem hdN)
    have hmem : d * f * d⁻¹ * f⁻¹ ∈ N ⊓ F := by
      refine Subgroup.mem_inf.2 ⟨?_, F.mul_mem hdf (F.inv_mem hf)⟩
      have h1 : d * (f * d⁻¹ * f⁻¹) ∈ N := N.mul_mem hdN hfn
      simpa only [mul_assoc] using h1
    rw [hNF, Subgroup.mem_bot] at hmem
    have hcomm : d * f = f * d := by
      calc d * f = (d * f * d⁻¹ * f⁻¹) * (f * d) := by group
        _ = f * d := by rw [hmem, one_mul]
    exact hcomm.symm
  rw [← le_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  obtain ⟨hxN, hxc⟩ := Subgroup.mem_inf.1 hx
  have hxz : x ∈ Subgroup.zpowers c :=
    hL.cent x hxc fun f hf => (Subgroup.mem_centralizer_iff.1 (hcent x hx) f hf).symm
  have hc7z : c ^ (7 : ℤ) = 1 := by simpa using hL.pow_eq
  have hx7z : x ^ (7 : ℤ) = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxz
    rw [← hk]
    calc (c ^ k) ^ (7 : ℤ) = c ^ (k * 7) := (zpow_mul c k 7).symm
      _ = c ^ (7 * k) := by rw [mul_comm]
      _ = (c ^ 7) ^ k := zpow_mul c 7 k
      _ = 1 := by rw [hc7z, one_zpow]
  have hx7 : x ^ 7 = 1 := by simpa using hx7z
  have hxdvd : orderOf x ∣ 7 := orderOf_dvd_of_pow_eq_one hx7
  have hxdvdN : orderOf x ∣ Nat.card N := by
    rw [← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hxN)
  rcases (Nat.dvd_prime Nat.prime_seven).1 hxdvd with h1 | h7
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h7 ▸ hxdvdN) hN

theorem inf_centralizer_eq_bot_of_mem_zpowers {G : Type} [Group G] [Finite G] {c : G}
    {F N : Subgroup G} (hL : SevenLine 7 c F) (hD : N ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    {e : G} (he : e ∈ Subgroup.zpowers c) (he1 : e ≠ 1) :
    N ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : orderOf e ∣ 7 := by
    rw [← Nat.card_zpowers, ← hL.orderOf_w, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr he)
  have he_ord : orderOf e = 7 := by
    rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) he1
    · exact h7
  have hce : Subgroup.zpowers e = Subgroup.zpowers c := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr he) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, he_ord, hL.orderOf_w]
  have hle : Subgroup.centralizer ({e} : Set G) ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hc : c ∈ Subgroup.zpowers e := by rw [hce]; exact Subgroup.mem_zpowers c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [← hk]
    exact (Commute.zpow_right hx k).eq
  exact le_bot_iff.mp (hD ▸ inf_le_inf_left N hle)

theorem inf_centralizer_eq_bot_of_conj_zpow {G : Type} [Group G] [Finite G] {c w h : G}
    {F H N : Subgroup G} (hL : SevenLine 7 c F) (hFH : F ≤ H) (hwF : w ∈ F)
    (hwc : w ∉ Subgroup.zpowers c) (hhH : h ∈ H) (hhw : h * w * h⁻¹ = c)
    (hHN : H ≤ normalizer (N : Set G))
    (hD : N ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) (m : ℤ) :
    N ⊓ Subgroup.centralizer ({w * c ^ m} : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc7 : c ^ (7 : ℤ) = 1 := by simpa using hL.pow_eq
  have hNw : N ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
    rw [← le_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    obtain ⟨hzN, hzw⟩ := Subgroup.mem_inf.1 hz
    have hcw : h⁻¹ * c = w * h⁻¹ := by rw [← hhw]; group
    have hhw' : h * w = c * h := by rw [← hhw]; group
    have hmem : h * z * h⁻¹ ∈ N ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hHN hhH) z).1 hzN
      · rw [Subgroup.mem_centralizer_singleton_iff] at hzw ⊢
        calc (h * z * h⁻¹) * c = h * z * (h⁻¹ * c) := by group
          _ = h * z * (w * h⁻¹) := by rw [hcw]
          _ = h * (z * w) * h⁻¹ := by group
          _ = h * (w * z) * h⁻¹ := by rw [hzw]
          _ = h * w * z * h⁻¹ := by group
          _ = (c * h) * z * h⁻¹ := by rw [hhw']
          _ = c * (h * z * h⁻¹) := by group
    rw [hD, Subgroup.mem_bot] at hmem
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = 1 := by rw [hmem]; group
  have hex : ∃ f ∈ F, ∃ x ∈ Subgroup.zpowers c, x ≠ 1 ∧ f * w * f⁻¹ = w * x := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ f ∈ F, f * w = w * f := by
      intro f hf
      obtain ⟨x, hx, hfx⟩ := hL.comm_mem hf hwF
      by_cases hx1 : x = 1
      · rw [hx1, mul_one] at hfx
        have := congrArg (fun t => t * f) hfx
        simpa [mul_assoc] using this
      · exact absurd hfx (hcon f hf x hx hx1)
    exact hwc (hL.center_le hwF fun q hq => (hcomm q hq).symm)
  obtain ⟨f, hfF, x, hx, hx1, hfw⟩ := hex
  obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hr : ¬ (7 : ℤ) ∣ r := by
    intro hdvd
    apply hx1
    obtain ⟨k, rfl⟩ := hdvd
    calc c ^ (7 * k) = (c ^ 7) ^ k := zpow_mul c 7 k
      _ = 1 := by rw [hc7]; exact one_zpow k
  have hfc : ∀ k : ℤ, f * c ^ k * f⁻¹ = c ^ k := by
    intro k
    have hcomm : Commute f c := (hL.comm_w hfF).symm
    calc f * c ^ k * f⁻¹ = c ^ k * f * f⁻¹ := by rw [(hcomm.zpow_right k).eq]
      _ = c ^ k := by group
  have hpow : ∀ n : ℕ, f ^ n * w * (f ^ n)⁻¹ = w * c ^ (r * (n : ℤ)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 : f ^ (n + 1) * w * (f ^ (n + 1))⁻¹
            = f * (f ^ n * w * (f ^ n)⁻¹) * f⁻¹ := by
          rw [pow_succ']
          group
        rw [h1, ih]
        rw [show f * (w * c ^ (r * (n : ℤ))) * f⁻¹
              = (f * w * f⁻¹) * (f * c ^ (r * (n : ℤ)) * f⁻¹) by group]
        rw [hfw, hfc]
        rw [show w * c ^ r * c ^ (r * (n : ℤ)) = w * (c ^ r * c ^ (r * (n : ℤ))) by group]
        rw [← zpow_add]
        congr 1
        push_cast
        ring_nf
  set R : ZMod 7 := (r : ZMod 7) with hRdef
  have hR : R ≠ 0 := by
    intro h0
    exact hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r 7).1 (hRdef ▸ h0))
  set s : ℕ := ((m : ZMod 7) / R).val with hsdef
  have hdvd : (7 : ℤ) ∣ r * (s : ℤ) - m := by
    have h0 : ((r * (s : ℤ) - m : ℤ) : ZMod 7) = 0 := by
      push_cast
      rw [hsdef, ZMod.natCast_zmod_val, ← hRdef]
      rw [mul_div_cancel₀ (m : ZMod 7) hR, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (r * (s : ℤ) - m) 7).1 h0
  have hcs : c ^ (r * (s : ℤ)) = c ^ m := by
    rw [zpow_eq_zpow_iff_modEq]
    have h7 : ((orderOf c : ℕ) : ℤ) = 7 := by rw [hL.orderOf_w]; norm_num
    rw [h7]
    have hdvd' : (7 : ℤ) ∣ m - r * (s : ℤ) := by
      have := dvd_neg.mpr hdvd
      rwa [neg_sub] at this
    exact Int.modEq_iff_dvd.2 hdvd'
  have hfs : f ^ s * w * (f ^ s)⁻¹ = w * c ^ m := by rw [hpow s, hcs]
  have hfsH : f ^ s ∈ H := hFH (F.pow_mem hfF s)
  have hfsinv : (f ^ s)⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
    Subgroup.inv_mem _ (hHN hfsH)
  rw [← le_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨hzN, hzc⟩ := Subgroup.mem_inf.1 hz
  rw [Subgroup.mem_centralizer_singleton_iff] at hzc
  have hz'N : (f ^ s)⁻¹ * z * f ^ s ∈ N := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hfsinv z).1 hzN
    simpa using h1
  have hz'w : (f ^ s)⁻¹ * z * f ^ s ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (f ^ s)⁻¹ * z * f ^ s * w
        = (f ^ s)⁻¹ * z * (f ^ s * w * (f ^ s)⁻¹) * f ^ s := by group
      _ = (f ^ s)⁻¹ * z * (w * c ^ m) * f ^ s := by rw [hfs]
      _ = (f ^ s)⁻¹ * (z * (w * c ^ m)) * f ^ s := by group
      _ = (f ^ s)⁻¹ * ((w * c ^ m) * z) * f ^ s := by rw [hzc]
      _ = w * ((f ^ s)⁻¹ * z * f ^ s) := by
            rw [← hfs]
            group
  have hz'bot : (f ^ s)⁻¹ * z * f ^ s ∈ (⊥ : Subgroup G) := by
    rw [← hNw]
    exact Subgroup.mem_inf.2 ⟨hz'N, hz'w⟩
  rw [Subgroup.mem_bot] at hz'bot
  calc z = f ^ s * ((f ^ s)⁻¹ * z * f ^ s) * (f ^ s)⁻¹ := by group
    _ = 1 := by rw [hz'bot]; group

theorem inf_centralizer_eq_bot_of_mem_sup {G : Type} [Group G] [Finite G] {c w h : G}
    {F H N : Subgroup G} (hL : SevenLine 7 c F) (hFH : F ≤ H) (hwF : w ∈ F)
    (hwc : w ∉ Subgroup.zpowers c) (hhH : h ∈ H) (hhw : h * w * h⁻¹ = c)
    (hHN : H ≤ normalizer (N : Set G))
    (hD : N ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) {e : G}
    (he : e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers w) (he1 : e ≠ 1) :
    N ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcw : Commute c w := hL.comm_w hwF
  have hc7z : c ^ (7 : ℤ) = 1 := by simpa using hL.pow_eq
  have hw7z : w ^ (7 : ℤ) = 1 := by
    have hw_eq : w = h⁻¹ * c * h := by
      calc w = h⁻¹ * (h * w * h⁻¹) * h := by group
        _ = h⁻¹ * c * h := by rw [hhw]
    rw [hw_eq]
    calc (h⁻¹ * c * h) ^ (7 : ℤ) = h⁻¹ * c ^ (7 : ℤ) * h := by
          simpa using conj_pow (a := h⁻¹) (b := c) (i := 7)
      _ = 1 := by rw [hc7z]; group
  have hw7 : w ^ 7 = 1 := by simpa using hw7z
  have hwne : w ≠ 1 := by
    intro h1
    apply hL.ne_one
    rw [← hhw, h1]
    simp
  have hEle : CFSG.Open.IsElemAbelian 7 (Subgroup.zpowers c ⊔ Subgroup.zpowers w) := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute ?_ ?_ ?_
    · exact CFSG.Open.isElemAbelian_zpowers hL.pow_eq
    · exact CFSG.Open.isElemAbelian_zpowers hw7
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (hcw.zpow_zpow m n).eq
  obtain ⟨a, ha, b, hb, hab⟩ := (CFSG.mem_sup_of_commute (fun x hx y hy => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hcw.zpow_zpow m n) (x := e)).1 he
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  obtain rfl : e = c ^ i * w ^ j := hab.symm
  have he_ord : orderOf (c ^ i * w ^ j) = 7 := by
    have hdvd : orderOf (c ^ i * w ^ j) ∣ 7 :=
      orderOf_dvd_of_pow_eq_one (hEle.2 _ he)
    rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h1 | h7
    · exact absurd (orderOf_eq_one_iff.mp h1) he1
    · exact h7
  by_cases hj : (7 : ℤ) ∣ j
  · obtain ⟨k, rfl⟩ := hj
    have hwzero : w ^ (7 * k) = 1 := by rw [zpow_mul, hw7z, one_zpow]
    refine inf_centralizer_eq_bot_of_mem_zpowers hL hD ?_ he1
    rw [hwzero, mul_one]
    exact Subgroup.zpow_mem_zpowers c i
  ·
    set J : ZMod 7 := (j : ZMod 7) with hJdef
    have hJ : J ≠ 0 := by
      intro h0
      exact hj ((ZMod.intCast_zmod_eq_zero_iff_dvd j 7).1 (hJdef ▸ h0))
    set j' : ℤ := (((J⁻¹).val : ℕ) : ℤ) with hj'def
    have hjj' : (7 : ℤ) ∣ j * j' - 1 := by
      have h0 : (((j * j' - 1 : ℤ)) : ZMod 7) = 0 := by
        rw [hj'def]
        push_cast
        rw [ZMod.natCast_zmod_val, ← hJdef, mul_inv_cancel₀ hJ, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (j * j' - 1) 7).1 h0
    have hj'7 : ¬ (7 : ℤ) ∣ j' := by
      intro hd
      have h1 : (7 : ℤ) ∣ j * j' := dvd_mul_of_dvd_right hd j
      have h2 : (7 : ℤ) ∣ j * j' - (j * j' - 1) := dvd_sub h1 hjj'
      rw [sub_sub_cancel] at h2
      exact absurd h2 (by norm_num)
    have hj'mod : j * j' ≡ 1 [ZMOD (7 : ℤ)] := by
      have h : (7 : ℤ) ∣ 1 - j * j' := by
        have h' := dvd_neg.mpr hjj'
        rwa [neg_sub] at h'
      exact Int.modEq_iff_dvd.2 h
    have hw_ord : orderOf w = 7 := orderOf_eq_prime hw7 hwne
    have hwjj : w ^ (j * j') = w := by
      have h1 : w ^ (j * j') = w ^ (1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq]
        have h7 : ((orderOf w : ℕ) : ℤ) = 7 := by rw [hw_ord]; norm_num
        rw [h7]
        exact hj'mod
      simpa using h1
    have hej' : (c ^ i * w ^ j) ^ j' = w * c ^ (i * j') := by
      rw [(hcw.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul, hwjj]
      simpa using (hcw.zpow_zpow (i * j') 1).eq
    have hej'1 : (c ^ i * w ^ j) ^ j' ≠ 1 := by
      intro h1
      have hdvd : ((orderOf (c ^ i * w ^ j) : ℕ) : ℤ) ∣ j' :=
        (orderOf_dvd_iff_zpow_eq_one).mpr h1
      rw [show ((orderOf (c ^ i * w ^ j) : ℕ) : ℤ) = 7 from by rw [he_ord]; norm_num] at hdvd
      exact hj'7 hdvd
    have hej'_ord : orderOf ((c ^ i * w ^ j) ^ j') = 7 := by
      have hmem : (c ^ i * w ^ j) ^ j' ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers w :=
        Subgroup.zpow_mem _ he j'
      have hdvd : orderOf ((c ^ i * w ^ j) ^ j') ∣ 7 :=
        orderOf_dvd_of_pow_eq_one (hEle.2 _ hmem)
      rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h1 | h7
      · exact absurd (orderOf_eq_one_iff.mp h1) hej'1
      · exact h7
    have hzp : Subgroup.zpowers (c ^ i * w ^ j)
        = Subgroup.zpowers ((c ^ i * w ^ j) ^ j') := by
      refine (Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers _ _)) ?_).symm
      rw [Nat.card_zpowers, Nat.card_zpowers, he_ord, hej'_ord]
    have hCeq : Subgroup.centralizer ({c ^ i * w ^ j} : Set G)
        = Subgroup.centralizer ({w * c ^ (i * j')} : Set G) := by
      have h2 : Subgroup.centralizer (Subgroup.zpowers (c ^ i * w ^ j) : Set G)
          = Subgroup.centralizer ({c ^ i * w ^ j} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      have h3 : Subgroup.centralizer (Subgroup.zpowers (w * c ^ (i * j')) : Set G)
          = Subgroup.centralizer ({w * c ^ (i * j')} : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      calc Subgroup.centralizer ({c ^ i * w ^ j} : Set G)
          = Subgroup.centralizer (Subgroup.zpowers (c ^ i * w ^ j) : Set G) := h2.symm
        _ = Subgroup.centralizer (Subgroup.zpowers ((c ^ i * w ^ j) ^ j') : Set G) := by rw [hzp]
        _ = Subgroup.centralizer (Subgroup.zpowers (w * c ^ (i * j')) : Set G) := by rw [hej']
        _ = Subgroup.centralizer ({w * c ^ (i * j')} : Set G) := h3
    rw [hCeq]
    exact inf_centralizer_eq_bot_of_conj_zpow hL hFH hwF hwc hhH hhw hHN hD (i * j')

theorem eq_bot_of_le_normalizer {G : Type} [Group G] [Finite G] {c w h : G} {F H N : Subgroup G}
    (hL : SevenLine 7 c F) (hFH : F ≤ H) (hwF : w ∈ F) (hwc : w ∉ zpowers c) (hhH : h ∈ H)
    (hhw : h * w * h⁻¹ = c) (hN : ¬ 7 ∣ Nat.card N) (hHN : H ≤ normalizer (N : Set G)) :
    N = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hD : N ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_le_normalizer hL hFH hN hHN
  have hcw : Commute c w := hL.comm_w hwF
  have hc7z : c ^ (7 : ℤ) = 1 := by simpa using hL.pow_eq
  have hw7z : w ^ (7 : ℤ) = 1 := by
    have hw_eq : w = h⁻¹ * c * h := by
      calc w = h⁻¹ * (h * w * h⁻¹) * h := by group
        _ = h⁻¹ * c * h := by rw [hhw]
    rw [hw_eq]
    calc (h⁻¹ * c * h) ^ (7 : ℤ) = h⁻¹ * c ^ (7 : ℤ) * h := by
          simpa using conj_pow (a := h⁻¹) (b := c) (i := 7)
      _ = 1 := by rw [hc7z]; group
  have hw7 : w ^ 7 = 1 := by simpa using hw7z
  have hwne : w ≠ 1 := by
    intro h1
    apply hL.ne_one
    rw [← hhw, h1]
    simp
  set E : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers w with hE
  have hEle : CFSG.Open.IsElemAbelian 7 E := by
    rw [hE]
    refine CFSG.Open.IsElemAbelian.sup_of_commute ?_ ?_ ?_
    · exact CFSG.Open.isElemAbelian_zpowers hL.pow_eq
    · exact CFSG.Open.isElemAbelian_zpowers hw7
    · intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (hcw.zpow_zpow m n).eq
  haveI : CFSG.IsElementaryAbelian 7 E :=
    CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hEle
  have hc_card : Nat.card (Subgroup.zpowers c) = 7 := by
    rw [Nat.card_zpowers, hL.orderOf_w]
  have hw_card : Nat.card (Subgroup.zpowers w) = 7 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hw7 hwne]
  have hinf : Subgroup.zpowers c ⊓ Subgroup.zpowers w = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers c ⊓ Subgroup.zpowers w) ∣ 7 := by
      rw [← hc_card]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_seven).1 hdvd with h1 | h7
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have hcle : Subgroup.zpowers c ⊓ Subgroup.zpowers w = Subgroup.zpowers w :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h7, hw_card])
      exact hwc ((Subgroup.zpowers_le).mp (hcle ▸ inf_le_left))
  have hcardE : Nat.card E = 49 := by
    rw [hE]
    have hcomm : ∀ a ∈ Subgroup.zpowers c, ∀ b ∈ Subgroup.zpowers w, Commute a b := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact hcw.zpow_zpow m n
    rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hinf, hc_card, hw_card]
  haveI : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardE]
    norm_num
  have hAE : E ≤ Subgroup.normalizer (N : Set G) := by
    rw [hE]
    exact (sup_le (Subgroup.zpowers_le.mpr hL.mem) (Subgroup.zpowers_le.mpr hwF)).trans
      (hFH.trans hHN)
  have hgen : N ≤ ⨆ (B : Subgroup E), ⨆ (_ : B.index = 7),
      N ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) :=
    CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hAE hN
  have hterm : ∀ (B : Subgroup E), B.index = 7 →
      N ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) = ⊥ := by
    intro B hB
    have hBcard : Nat.card B = 7 := by
      have h := Subgroup.card_mul_index B
      rw [hB, hcardE] at h
      omega
    have hB'card : Nat.card (B.map E.subtype : Subgroup G) = 7 := by
      rw [Subgroup.card_map_of_injective E.subtype_injective, hBcard]
    haveI : Nontrivial ↥(B.map E.subtype) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hB'card]
      norm_num
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥(B.map E.subtype))
    have hxmem : (x : G) ∈ B.map E.subtype := x.2
    have hxE : (x : G) ∈ E := Subgroup.map_subtype_le B hxmem
    have hxne : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hxbot : N ⊓ Subgroup.centralizer ({(x : G)} : Set G) = ⊥ := by
      refine inf_centralizer_eq_bot_of_mem_sup hL hFH hwF hwc hhH hhw hHN hD ?_ hxne
      exact hxE
    have hle : Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) ≤
        Subgroup.centralizer ({(x : G)} : Set G) := by
      refine Subgroup.centralizer_le ?_
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      exact hy ▸ hxmem
    have hfin : N ⊓ Subgroup.centralizer ((B.map E.subtype : Subgroup G) : Set G) ≤ ⊥ := by
      rw [← hxbot]
      exact inf_le_inf_left N hle
    exact le_bot_iff.mp hfin
  have hNbot : N ≤ ⊥ :=
    hgen.trans (iSup_le fun B => iSup_le fun hB => le_of_eq (hterm B hB))
  exact le_bot_iff.mp hNbot

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
