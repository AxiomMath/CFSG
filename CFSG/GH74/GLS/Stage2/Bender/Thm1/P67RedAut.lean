module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67N2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG

theorem N2Cfg.map_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (f : MulAut Y ≃* MulAut Y')
    {r : ℕ} {V Z : Subgroup (MulAut Y)} (h : N2Cfg Y r V Z) :
    N2Cfg Y' r (V.map f.toMonoidHom) (Z.map f.toMonoidHom) := by
  obtain ⟨hr, hr2, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := h
  have : Fact r.Prime := ⟨hr⟩
  have := hVe
  have hVcard : Nat.card ↥(V.map f.toMonoidHom) = Nat.card ↥V :=
    Subgroup.card_map_of_injective f.injective
  have hZcard : Nat.card ↥(Z.map f.toMonoidHom) = Nat.card ↥Z :=
    Subgroup.card_map_of_injective f.injective
  refine ⟨hr, hr2, IsElementaryAbelian.map f.toMonoidHom, hVcard.trans hVc, ?_,
    hZcard ▸ hZodd, hZcard ▸ hZcop, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg f (hZab a ha b hb)
  · exact fun hbot => hZbot ((Subgroup.map_eq_bot_iff_of_injective Z f.injective).mp hbot)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    exact congrArg f (hcomm a ha b hb)

theorem NoN2.of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (h : NoN2 Y') :
    NoN2 Y :=
  fun r _ _ hcfg => h r _ _ (hcfg.map_mulEquiv (MulAut.congr e))

theorem N2Cfg.exists_triple {Y : Type} [Group Y] [Finite Y] {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (h : N2Cfg Y r V Z) :
    ∃ (s : ℕ) (a b y : MulAut Y), r.Prime ∧ s.Prime ∧ Odd r ∧ Odd s ∧ r ≠ s ∧ a ^ r = 1 ∧
      b ^ r = 1 ∧ y ^ s = 1 ∧ a ≠ 1 ∧ b ∉ Subgroup.zpowers a ∧ y ≠ 1 ∧ a * b = b * a ∧
      a * y = y * a ∧ b * y = y * b := by
  obtain ⟨hr, hr2, hVe, hVc, hZab, hZodd, hZcop, hZbot, hcomm⟩ := h
  have : Fact r.Prime := ⟨hr⟩
  have := hVe
  have hVnt : Nontrivial ↥V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hVc]
    exact Nat.one_lt_pow two_ne_zero hr.one_lt
  obtain ⟨⟨a, ha⟩, ha1⟩ := exists_ne (1 : ↥V)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have har : a ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  have hord : orderOf a = r := orderOf_eq_prime har ha1'
  have hnle : ¬ V ≤ Subgroup.zpowers a := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [hVc, Nat.card_zpowers, hord] at this
    have h2 : r < r ^ 2 := by
      calc r = r ^ 1 := (pow_one r).symm
        _ < r ^ 2 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
    omega
  obtain ⟨b, hbV, hbnot⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hbr : b ^ r = 1 := elemPow_eq_one_of_isElementaryAbelian b hbV
  have hab : a * b = b * a := setLike_mul_comm ha hbV
  have hZcard1 : Nat.card ↥Z ≠ 1 := fun h => hZbot (Subgroup.card_eq_one.mp h)
  have hs : (Nat.card ↥Z).minFac.Prime := Nat.minFac_prime hZcard1
  have hsdvd : (Nat.card ↥Z).minFac ∣ Nat.card ↥Z := Nat.minFac_dvd _
  have : Fact (Nat.card ↥Z).minFac.Prime := ⟨hs⟩
  have hZfin : Finite ↥Z := Nat.finite_of_card_ne_zero (Odd.pos hZodd).ne'
  obtain ⟨⟨y, hyZ⟩, hyord⟩ := exists_prime_orderOf_dvd_card' (Nat.card ↥Z).minFac hsdvd
  have hyord' : orderOf y = (Nat.card ↥Z).minFac := by
    rw [← hyord]; exact (Subgroup.orderOf_mk y hyZ).symm
  refine ⟨(Nat.card ↥Z).minFac, a, b, y, hr, hs, hr2, Odd.of_dvd_nat hZodd hsdvd, ?_, har, hbr,
    ?_, ha1', hbnot, ?_, hab, hcomm a ha y hyZ, hcomm b hbV y hyZ⟩
  · intro hrs
    have hcop : Nat.Coprime r (Nat.card ↥Z) := hZcop.symm
    have := hcop.eq_one_of_dvd (hrs ▸ hsdvd)
    exact hr.one_lt.ne' this
  · rw [← hyord']; exact pow_orderOf_eq_one y
  · intro hy1
    rw [hy1, orderOf_one] at hyord'
    exact hs.one_lt.ne hyord'

theorem noN2_of_triples {Y : Type} [Group Y] [Finite Y]
    (h : ∀ (r s : ℕ) (a b y : MulAut Y), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
      a * b = b * a → a * y = y * a → b * y = y * b → False) : NoN2 Y := by
  rintro r V Z hcfg
  obtain ⟨s, a, b, y, hr, hs, hr2, hs2, hrs, har, hbr, hys, ha1, hbnot, hy1, hab, hay, hby⟩ :=
    hcfg.exists_triple
  exact h r s a b y hr hs hr2 hs2 hrs har hbr hys ha1 hbnot hy1 hab hay hby

theorem mulAut_conj_injective_of_center_bot {Y : Type*} [Group Y]
    (hcenter : Subgroup.center Y = ⊥) : Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun φ : MulAut Y => φ x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  rw [hcenter] at hmem
  exact Subgroup.mem_bot.mp hmem

theorem mulAut_odd_order_inner {Y : Type} [Group Y] [Finite Y] (hcenter : Subgroup.center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y) (φ : MulAut Y) (hφ : Odd (orderOf φ)) :
    ∃ g : Y, φ = MulAut.conj g := by
  have hinj := mulAut_conj_injective_of_center_bot hcenter
  set I : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hI
  have hIcard : Nat.card ↥I = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hmul := Subgroup.card_mul_index I
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hidx : I.index ≤ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ hYpos
    rw [← hIcard, hmul]
    omega
  have hmem : φ ∈ I := by
    by_cases h1 : I.index = 1
    · rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top φ
    · have hne0 : I.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : I.index = 2 := by omega
      have := Subgroup.normal_of_index_eq_two h2
      have hsq : φ ^ 2 ∈ I := h2 ▸ Subgroup.pow_index_mem I φ
      obtain ⟨k, hk⟩ := hφ
      have hφk : φ ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one φ
      have : φ = (φ ^ 2) ^ (k + 1) := by
        calc φ = φ ^ (2 * k + 1) * φ := by rw [hφk, one_mul]
          _ = (φ ^ 2) ^ (k + 1) := by rw [← pow_succ, ← pow_mul]; congr 1
      rw [this]
      exact Subgroup.pow_mem I hsq (k + 1)
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩

theorem noN2_of_inner_triples {Y : Type} [Group Y] [Finite Y] (hcenter : Subgroup.center Y = ⊥)
    (hout : ∀ φ : MulAut Y, Odd (orderOf φ) → ∃ g : Y, φ = MulAut.conj g)
    (h : ∀ (r s : ℕ) (a b y : Y), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
      a * b = b * a → a * y = y * a → b * y = y * b → False) : NoN2 Y := by
  have hinj := mulAut_conj_injective_of_center_bot hcenter
  refine noN2_of_triples ?_
  intro r s a b y hr hs hr2 hs2 hrs har hbr hys ha1 hbnot hy1 hab hay hby
  have hodd : ∀ (φ : MulAut Y) (n : ℕ), Odd n → φ ^ n = 1 → ∃ g : Y, φ = MulAut.conj g :=
    fun φ n hn hφ => hout φ (Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one hφ))
  obtain ⟨a', rfl⟩ := hodd a r hr2 har
  obtain ⟨b', rfl⟩ := hodd b r hr2 hbr
  obtain ⟨y', rfl⟩ := hodd y s hs2 hys
  refine h r s a' b' y' hr hs hr2 hs2 hrs ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · apply hinj
    rw [map_pow, har, map_one]
  · apply hinj
    rw [map_pow, hbr, map_one]
  · apply hinj
    rw [map_pow, hys, map_one]
  · rintro rfl
    exact ha1 (map_one _)
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact hbnot (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩)
  · rintro rfl
    exact hy1 (map_one _)
  · apply hinj
    rw [map_mul, map_mul, hab]
  · apply hinj
    rw [map_mul, map_mul, hay]
  · apply hinj
    rw [map_mul, map_mul, hby]

theorem noN2_of_outer_card {Y : Type} [Group Y] [Finite Y] (hcenter : Subgroup.center Y = ⊥)
    (hcard : Nat.card (MulAut Y) ≤ 2 * Nat.card Y)
    (h : ∀ (r s : ℕ) (a b y : Y), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
      a * b = b * a → a * y = y * a → b * y = y * b → False) : NoN2 Y :=
  noN2_of_inner_triples hcenter (mulAut_odd_order_inner hcenter hcard) h

end CFSG.GH74.GLS.Stage2.Bender.Thm1
