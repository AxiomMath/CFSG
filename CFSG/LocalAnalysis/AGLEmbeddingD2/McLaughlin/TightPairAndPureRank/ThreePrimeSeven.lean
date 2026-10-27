module

public import Mathlib.GroupTheory.Transfer
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open Subgroup

section Seven

variable {G : Type*} [Group G] [Finite G]

theorem card_centralizer_seven (hcard : Nat.card G = 6048)
    (h14 : ∀ g : G, orderOf g ≠ 14) (h21 : ∀ g : G, orderOf g ≠ 21)
    {x : G} (hx : orderOf x = 7) : Nat.card (centralizer {x}) = 7 := by
  set C : Subgroup G := centralizer {x} with hC
  have hxC : x ∈ C := by
    rw [hC, mem_centralizer_iff]; intro h hh; rw [Set.mem_singleton_iff] at hh; rw [hh]
  have h7 : 7 ∣ Nat.card C := by
    have := orderOf_dvd_natCard (⟨x, hxC⟩ : C)
    have e : orderOf (⟨x, hxC⟩ : C) = 7 := by
      rw [← hx]; exact orderOf_submonoid ⟨x, hxC⟩ |>.symm ▸ rfl
    rwa [e] at this
  have hdvd : Nat.card C ∣ 6048 := hcard ▸ Subgroup.card_subgroup_dvd_card C
  by_contra hne
  obtain ⟨k, hk⟩ := h7
  have hk1 : k ≠ 1 := by rintro rfl; apply hne; omega
  obtain ⟨r, hr, hrk⟩ := Nat.exists_prime_and_dvd hk1
  have hrC : r ∣ Nat.card C := hk ▸ Dvd.dvd.mul_left hrk 7
  have hr6048 : r ∣ 2 ^ 5 * 3 ^ 3 * 7 := by
    have := hrC.trans hdvd; simpa using this
  have hr_cases : r = 2 ∨ r = 3 ∨ r = 7 := by
    rcases (Nat.Prime.dvd_mul hr).mp hr6048 with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h)
      · right; left; exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h)
    · right; right; exact (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) r hrC
  have hcomm : Commute x (y : G) := by
    exact mem_centralizer_iff.mp y.2 x (Set.mem_singleton x)
  have hyo : orderOf (y : G) = r := by rw [← hy]; exact orderOf_submonoid y
  rcases hr_cases with rfl | rfl | rfl
  · have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hyo]; norm_num)
    rw [hx, hyo] at this; exact h14 _ (by simpa using this)
  · have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hyo]; norm_num)
    rw [hx, hyo] at this; exact h21 _ (by simpa using this)
  · have : 7 * 7 ∣ Nat.card C := by rw [hk]; exact Nat.mul_dvd_mul_left 7 hrk
    have := this.trans hdvd
    omega

theorem card_normalizer_seven (hcard : Nat.card G = 6048)
    (h14 : ∀ g : G, orderOf g ≠ 14) (h21 : ∀ g : G, orderOf g ≠ 21)
    {x : G} (hx : orderOf x = 7) : Nat.card (normalizer ((zpowers x : Subgroup G) : Set G)) = 21 := by
  have hC := card_centralizer_seven hcard h14 h21 hx
  set P : Subgroup G := zpowers x with hPdef
  have hP7 : Nat.card P = 7 := by rw [hPdef, Nat.card_zpowers, hx]
  set N := normalizer (P : Set G) with hN
  have hcyc : IsCyclic P := by rw [hPdef]; infer_instance
  have hmul : Nat.card N = Nat.card (N ⧸ (normalizerMonoidHom P).ker) *
      Nat.card (normalizerMonoidHom P).ker := Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hquot : Nat.card (N ⧸ (normalizerMonoidHom P).ker) =
      Nat.card (normalizerMonoidHom P).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  have hrange : Nat.card (normalizerMonoidHom P).range ∣ 6 := by
    have h1 : Nat.card (normalizerMonoidHom P).range ∣ Nat.card (MulAut P) :=
      Subgroup.card_subgroup_dvd_card _
    rw [IsCyclic.card_mulAut, hP7, Nat.totient_prime (by norm_num)] at h1
    simpa using h1
  have hker : Nat.card (normalizerMonoidHom P).ker ∣ 7 := by
    rw [← hC]
    let f : (normalizerMonoidHom P).ker →* centralizer ({x} : Set G) :=
      { toFun := fun g => ⟨g.1.1, by
          have hg : g.1 ∈ (centralizer (P : Set G)).subgroupOf N := by
            rw [← normalizerMonoidHom_ker]; exact g.2
          have hg' : (g.1 : G) ∈ centralizer (P : Set G) := mem_subgroupOf.mp hg
          rw [mem_centralizer_iff]; intro h hh
          rw [Set.mem_singleton_iff] at hh; subst hh
          exact mem_centralizer_iff.mp hg' _ (mem_zpowers _)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective f (fun a b h => by
      have h' := congrArg (fun z : centralizer ({x} : Set G) => (z : G)) h
      exact Subtype.ext (Subtype.ext h'))
  have h7N : 7 ∣ Nat.card N := by
    rw [← hP7]; exact Subgroup.card_dvd_of_le (le_normalizer (H := P))
  have hb0 : 0 < Nat.card (normalizerMonoidHom P).range := Nat.card_pos
  have hb6 := Nat.le_of_dvd (by norm_num) hrange
  have ha : Nat.card (normalizerMonoidHom P).ker = 7 := by
    rw [hmul, hquot] at h7N
    have h7a : 7 ∣ Nat.card (normalizerMonoidHom P).ker := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp h7N with h | h
      · exact absurd (Nat.le_of_dvd hb0 h) (by omega)
      · exact h
    exact Nat.dvd_antisymm hker h7a
  have hNb : Nat.card N = 7 * Nat.card (normalizerMonoidHom P).range := by
    rw [hmul, hquot, ha]; ring
  have hP1 : IsPGroup 7 P := IsPGroup.of_card (n := 1) (by rw [hP7]; simp)
  have hindex : ¬ 7 ∣ P.index := by
    have := Subgroup.card_mul_index P
    rw [hP7, hcard] at this
    have h864 : P.index = 864 := by omega
    rw [h864]; norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 G := hP1.toSylow hindex
  have hmod := card_sylow_modEq_one 7 G
  rw [Sylow.card_eq_index_normalizer S] at hmod
  have hSN : (normalizer (S : Set G)).index = N.index := rfl
  rw [hSN] at hmod
  have hidx := Subgroup.index_mul_card N
  rw [hcard, hNb] at hidx
  unfold Nat.ModEq at hmod
  have hb3 : Nat.card (normalizerMonoidHom P).range = 3 := by
    generalize Nat.card (normalizerMonoidHom P).range = b at *
    generalize N.index = n at *
    interval_cases b <;> simp at hrange <;> omega
  rw [hNb, hb3]

theorem seven_dvd_ncard_of_free {x : G} (hx : x ^ 7 = 1) (T : Set G)
    (hT : ∀ t ∈ T, x * t * x⁻¹ ∈ T) (hfree : ∀ t ∈ T, x * t * x⁻¹ ≠ t) :
    7 ∣ T.ncard := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let f : Function.End T := fun t => ⟨x * t * x⁻¹, hT t t.2⟩
  have hf : f ^ 7 ^ 1 = 1 := by
    have hit : ∀ n : ℕ, ∀ t : T, ((f ^ n) t : G) = x ^ n * t * (x ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro t; show ((id t : T) : G) = _; simp
      | succ n ih =>
        intro t
        have : (f ^ (n + 1)) t = (f ^ n) (f t) := by rw [pow_succ]; rfl
        rw [this, ih]
        simp [f, pow_succ, mul_assoc]
    funext t
    apply Subtype.ext
    rw [pow_one, hit]
    simp [hx]
    rfl
  have hfp : Function.fixedPoints f = ∅ := by
    ext t
    simp only [Function.mem_fixedPoints, Function.IsFixedPt, Set.mem_empty_iff_false, iff_false]
    intro ht
    exact hfree t t.2 (congrArg Subtype.val ht)
  have : Fintype T := Fintype.ofFinite T
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  have hc : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨a, ha⟩ => by rw [hfp] at ha; exact ha⟩
  rw [hc] at h
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd.mp h)

theorem burnside_seven {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx : orderOf x = 7)
    {m : ℕ} (hHm : Nat.card H = 7 * m) (hm7 : ¬ 7 ∣ m)
    (hN : ∀ g ∈ H, g ∈ normalizer ((zpowers x : Subgroup G) : Set G) → x * g = g * x) :
    ∃ K : Subgroup G, K ≤ H ∧ Nat.card K = m ∧ ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set y : H := ⟨x, hxH⟩ with hy
  have hyo : orderOf y = 7 := by rw [← hx]; exact orderOf_submonoid y |>.symm ▸ rfl
  set PH : Subgroup H := zpowers y with hPH
  have hPH7 : Nat.card PH = 7 := by rw [hPH, Nat.card_zpowers, hyo]
  have hmem : ∀ z : H, z ∈ PH ↔ (z : G) ∈ zpowers x := by
    intro z
    simp only [hPH, mem_zpowers_iff]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, by simp [hy]⟩
    · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext (by simpa [hy] using hi)⟩
  have hPHidx : ¬ 7 ∣ PH.index := by
    have := Subgroup.card_mul_index PH
    rw [hPH7, hHm] at this
    have : PH.index = m := by omega
    rwa [this]
  have hP1 : IsPGroup 7 PH := IsPGroup.of_card (n := 1) (by rw [hPH7]; simp)
  let S : Sylow 7 H := hP1.toSylow hPHidx
  have hcent : normalizer (S : Set H) ≤ centralizer (S : Set H) := by
    intro g hg
    have hg' : (g : G) ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro h
      have hzH : ∀ h : G, h ∈ zpowers x → h ∈ H := fun h hh => zpowers_le.mpr hxH hh
      constructor
      · intro hh
        have h1 := (mem_normalizer_iff.mp hg) ⟨h, hzH h hh⟩
        have := (hmem ⟨h, hzH h hh⟩).mpr hh
        have h2 := h1.mp this
        exact (hmem _).mp h2
      · intro hh
        have hgh : g * h * g⁻¹ ∈ H := zpowers_le.mpr hxH hh
        have hhH : h ∈ H := by
          have := H.mul_mem (H.mul_mem (H.inv_mem g.2) hgh) g.2
          simpa [mul_assoc] using this
        have h1 := (mem_normalizer_iff.mp hg) ⟨h, hhH⟩
        have h3 : (⟨g * h * g⁻¹, hgh⟩ : H) ∈ PH := (hmem _).mpr hh
        have e : (g * ⟨h, hhH⟩ * g⁻¹ : H) = ⟨g * h * g⁻¹, hgh⟩ := Subtype.ext (by simp)
        have h4 : (g * ⟨h, hhH⟩ * g⁻¹ : H) ∈ PH := by rw [e]; exact h3
        exact (hmem _).mp (h1.mpr h4)
    have hc := hN g g.2 hg'
    rw [mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ PH := hz
    simp only [hPH, mem_zpowers_iff] at hz'
    obtain ⟨i, rfl⟩ := hz'
    have : Commute (g : H) y := Subtype.ext (by simpa [hy] using hc.symm)
    exact (this.zpow_right i).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hcent
  refine ⟨(MonoidHom.transferSylow S hcent).ker.map H.subtype, ?_, ?_, ?_⟩
  · intro z hz; obtain ⟨w, -, rfl⟩ := hz; exact w.2
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    have := hcomp.card_mul_card
    have h2 : Nat.card (S : Subgroup H) = 7 := hPH7
    rw [h2, hHm] at this
    omega
  · intro k hk
    obtain ⟨w, hw, rfl⟩ := hk
    refine ⟨y * w * y⁻¹, ?_, by simp [hy]⟩
    exact (MonoidHom.transferSylow S hcent).normal_ker.conj_mem w hw y

theorem card_le_of_not_three_dvd (hcard : Nat.card G = 6048)
    (h14 : ∀ g : G, orderOf g ≠ 14) (h21 : ∀ g : G, orderOf g ≠ 21)
    (h8 : ∀ E : Subgroup G, (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 2 = 1) →
      Nat.card E ≤ 4)
    (H : Subgroup G) (hH : ¬ 3 ∣ Nat.card H) : Nat.card H ≤ 32 := by
  have hHd : Nat.card H ∣ 6048 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hcop3 : Nat.Coprime (Nat.card H) 3 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hH |>.symm
  by_cases h7 : 7 ∣ Nat.card H
  swap
  · have hcop7 : Nat.Coprime (Nat.card H) 7 :=
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7 |>.symm
    have hc : Nat.Coprime (Nat.card H) 189 := by
      have : (189 : ℕ) = 3 ^ 3 * 7 := by norm_num
      rw [this]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 hcop3) hcop7
    have : Nat.card H ∣ 32 := hc.dvd_of_dvd_mul_right (by simpa using hHd)
    exact Nat.le_of_dvd (by norm_num) this
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := H) 7 h7
  set x : G := (y : G) with hxdef
  have hxH : x ∈ H := y.2
  have hx : orderOf x = 7 := by rw [hxdef]; rw [← hy]; exact orderOf_submonoid y |>.symm ▸ rfl
  obtain ⟨m, hm⟩ := h7
  have hm32 : m ∣ 32 := by
    have h1 : m ∣ 864 := by
      have : 7 * m ∣ 7 * 864 := by rw [← hm]; simpa using hHd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
    have hcm : Nat.Coprime m 27 := by
      have : Nat.Coprime (Nat.card H) 3 := hcop3
      rw [hm] at this
      exact Nat.Coprime.pow_right 3 (Nat.Coprime.coprime_dvd_left (Dvd.intro_left 7 rfl) this)
    have : (864 : ℕ) = 32 * 27 := by norm_num
    rw [this] at h1
    exact hcm.dvd_of_dvd_mul_right h1
  have hm7 : ¬ 7 ∣ m := by
    intro h
    have := Nat.le_of_dvd (by norm_num) (h.trans hm32)
    have := Nat.le_of_dvd (by norm_num) (h.trans hm32)
    have h7' : 7 ∣ 32 := h.trans hm32
    omega
  have hN21 := card_normalizer_seven hcard h14 h21 hx
  set Px : Subgroup G := zpowers x with hPx
  set N : Subgroup G := normalizer (Px : Set G) with hNdef
  have hPx7 : Nat.card Px = 7 := by rw [hPx, Nat.card_zpowers, hx]
  have hPxN : Px ≤ N := le_normalizer
  have hPxH : Px ≤ H := zpowers_le.mpr hxH
  have hNH7 : Nat.card (N ⊓ H : Subgroup G) = 7 := by
    have d1 : Nat.card (N ⊓ H : Subgroup G) ∣ 21 := hN21 ▸ Subgroup.card_dvd_of_le inf_le_left
    have d2 : Nat.card (N ⊓ H : Subgroup G) ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_right
    have d3 : Nat.card (N ⊓ H : Subgroup G) ∣ 7 := by
      have hc : Nat.Coprime (Nat.card (N ⊓ H : Subgroup G)) 3 :=
        Nat.Coprime.coprime_dvd_left d2 hcop3
      have : (21 : ℕ) = 7 * 3 := by norm_num
      rw [this] at d1
      exact hc.dvd_of_dvd_mul_right d1
    have d4 : 7 ∣ Nat.card (N ⊓ H : Subgroup G) := by
      rw [← hPx7]; exact Subgroup.card_dvd_of_le (le_inf hPxN hPxH)
    exact Nat.dvd_antisymm d3 d4
  have hNHeq : (N ⊓ H : Subgroup G) = Px :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hPxN hPxH) (by rw [hNH7, hPx7])).symm
  have hNcomm : ∀ g ∈ H, g ∈ normalizer (Px : Set G) → x * g = g * x := by
    intro g hg hgN
    have : g ∈ Px := by rw [← hNHeq]; exact ⟨hgN, hg⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp this
    exact (Commute.refl x).zpow_right i |>.eq
  obtain ⟨K, hKH, hKm, hKx⟩ := burnside_seven hxH hx hm hm7 hNcomm
  have hC7 := card_centralizer_seven hcard h14 h21 hx
  have hKfree : ∀ k ∈ K, x * k * x⁻¹ = k → k = 1 := by
    intro k hk hfix
    have hkC : k ∈ centralizer ({x} : Set G) := by
      rw [mem_centralizer_iff]; intro h hh; rw [Set.mem_singleton_iff] at hh; rw [hh]
      calc x * k = (x * k * x⁻¹) * x := by group
        _ = k * x := by rw [hfix]
    have o1 : orderOf k ∣ 7 := hC7 ▸ Subgroup.orderOf_dvd_natCard _ hkC
    have o2 : orderOf k ∣ m := hKm ▸ Subgroup.orderOf_dvd_natCard _ hk
    have o3 : orderOf k ∣ Nat.gcd 7 m := Nat.dvd_gcd o1 o2
    have : Nat.gcd 7 m = 1 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm7) |>.symm
    rw [this] at o3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp o3)
  have hx7 : x ^ 7 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hT1 : 7 ∣ ({t : G | t ∈ K ∧ t ≠ 1} : Set G).ncard := by
    refine seven_dvd_ncard_of_free hx7 _ ?_ ?_
    · rintro t ⟨htK, ht1⟩
      refine ⟨hKx t htK, fun h => ht1 ?_⟩
      have : t = x⁻¹ * 1 * x := by rw [← h]; group
      simpa using this
    · rintro t ⟨htK, ht1⟩ hfix
      exact ht1 (hKfree t htK hfix)
  have hKcard : (K : Set G).ncard = m := by rw [← Nat.card_coe_set_eq]; exact hKm
  have hT1card : ({t : G | t ∈ K ∧ t ≠ 1} : Set G).ncard = m - 1 := by
    have : ({t : G | t ∈ K ∧ t ≠ 1} : Set G) = (K : Set G) \ {1} := by
      ext t; simp
    rw [this, Set.ncard_sdiff_singleton_of_mem K.one_mem, hKcard]
  rw [hT1card] at hT1
  have hmpos : 0 < m := by
    have := Nat.card_pos (α := K); omega
  have hmle := Nat.le_of_dvd (by norm_num) hm32
  have hcases : m = 1 ∨ m = 8 := by
    interval_cases m <;> omega
  rcases hcases with rfl | rfl
  · omega
  exfalso
  have hT2 : 7 ∣ ({t : G | t ∈ K ∧ t ≠ 1 ∧ t ^ 2 = 1} : Set G).ncard := by
    refine seven_dvd_ncard_of_free hx7 _ ?_ ?_
    · rintro t ⟨htK, ht1, ht2⟩
      refine ⟨hKx t htK, fun h => ht1 ?_, ?_⟩
      · have : t = x⁻¹ * 1 * x := by rw [← h]; group
        simpa using this
      · rw [conj_pow, ht2]; group
    · rintro t ⟨htK, ht1, -⟩ hfix
      exact ht1 (hKfree t htK hfix)
  have hsub : ({t : G | t ∈ K ∧ t ≠ 1 ∧ t ^ 2 = 1} : Set G) ⊆ {t : G | t ∈ K ∧ t ≠ 1} :=
    fun t ht => ⟨ht.1, ht.2.1⟩
  have hfin : ({t : G | t ∈ K ∧ t ≠ 1} : Set G).Finite := Set.toFinite _
  have hne : ({t : G | t ∈ K ∧ t ≠ 1 ∧ t ^ 2 = 1} : Set G).Nonempty := by
    have h2 : 2 ∣ Nat.card K := by rw [hKm]; norm_num
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
    have hzo : orderOf (z : G) = 2 := by rw [← hz]; exact orderOf_submonoid z
    refine ⟨z, z.2, ?_, ?_⟩
    · intro h1; rw [h1, orderOf_one] at hzo; omega
    · rw [← hzo]; exact pow_orderOf_eq_one _
  have hpos := (Set.ncard_pos (Set.toFinite _)).mpr hne
  have hle := Set.ncard_le_ncard hsub hfin
  have heq : ({t : G | t ∈ K ∧ t ≠ 1 ∧ t ^ 2 = 1} : Set G).ncard = 7 := by
    have := Nat.le_of_dvd hpos hT2
    omega
  have hset := Set.eq_of_subset_of_ncard_le hsub (by omega) hfin
  have hsq : ∀ a ∈ K, a ^ 2 = 1 := by
    intro a ha
    by_cases h1 : a = 1
    · rw [h1]; simp
    · have : a ∈ ({t : G | t ∈ K ∧ t ≠ 1} : Set G) := ⟨ha, h1⟩
      rw [← hset] at this
      exact this.2.2
  have hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq b hb)
    have hab : (a * b)⁻¹ = a * b :=
      inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq _ (K.mul_mem ha hb))
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha', hb']
  have := h8 K hcomm hsq
  omega
end Seven

end CFSG.AGLEmbeddingD2.McLaughlin
