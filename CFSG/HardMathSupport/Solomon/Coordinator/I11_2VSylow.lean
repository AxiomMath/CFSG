module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open scoped commutatorElement

section Small

variable {R : Type*} [Group R] [Finite R]

theorem i112v_card_center_eq_three (hR : Nat.card R = 27) (hna : ∃ r s : R, r * s ≠ s * r) :
    Nat.card (Subgroup.center R) = 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by rw [hR]; norm_num)
  have : Nontrivial R := by
    obtain ⟨r, s, h⟩ := hna
    exact ⟨⟨r * s, s * r, h⟩⟩
  have hnt := hRp.center_nontrivial
  have hdvd : Nat.card (Subgroup.center R) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hR]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases k
  · exfalso
    rw [pow_zero] at hk
    exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt (Subgroup.eq_bot_of_card_eq _ hk)
  · simpa using hk
  · exfalso
    have hq : Nat.card (R ⧸ Subgroup.center R) = 3 := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
      rw [hR, hk] at this
      omega
    have : IsCyclic (R ⧸ Subgroup.center R) := isCyclic_of_prime_card hq
    obtain ⟨r, s, h⟩ := hna
    have hc := (QuotientGroup.mk' (Subgroup.center R)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
    exact h (hc.is_comm.comm r s)
  · exfalso
    have htop : Subgroup.center R = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hk, hR]; norm_num)
    obtain ⟨r, s, h⟩ := hna
    exact h (Subgroup.mem_center_iff.1 (htop ▸ Subgroup.mem_top s) r)

theorem i112v_commutator_eq_center (hR : Nat.card R = 27) (hna : ∃ r s : R, r * s ≠ s * r) :
    commutator R = Subgroup.center R := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hZ := i112v_card_center_eq_three hR hna
  have hq : Nat.card (R ⧸ Subgroup.center R) = 3 ^ 2 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center R)
    rw [hR, hZ] at this
    norm_num
    omega
  have hcommQ := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hq).is_comm.comm
  have hle : commutator R ≤ Subgroup.center R := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.ker_mk' (Subgroup.center R), MonoidHom.mem_ker, commutatorElement_def,
      map_mul, map_mul, map_mul, map_inv, map_inv, hcommQ ((QuotientGroup.mk' _) a)]
    group
  have hne : commutator R ≠ ⊥ := by
    intro h
    obtain ⟨r, s, hrs⟩ := hna
    apply hrs
    have hc : ⁅r, s⁆ ∈ ⁅(⊤ : Subgroup R), ⊤⁆ := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top r) (Subgroup.mem_top s)
    rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hdvd : Nat.card (commutator R) ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hne
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, h3])

end Small

section Sylow

variable {K : Type*} [Group K] [Finite K]

theorem i112v_sylow_center (hZ3 : Nat.card (Subgroup.center K) = 3) (R : Sylow 3 K)
    (hR : Nat.card ↥(R : Subgroup K) = 27)
    (hna : ∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) :
    Subgroup.center K ≤ R ∧
      (Subgroup.center ↥(R : Subgroup K)).map (R : Subgroup K).subtype = Subgroup.center K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center K) := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  have hZR : Subgroup.center K ≤ R := hZp.le_sylow_of_normal R
  refine ⟨hZR, ?_⟩
  have hna' : ∃ r s : ↥(R : Subgroup K), r * s ≠ s * r := by
    obtain ⟨r, hr, s, hs, h⟩ := hna
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, fun h' => h (congrArg Subtype.val h')⟩
  have hcR := i112v_card_center_eq_three hR hna'
  have hle : Subgroup.center K ≤
      (Subgroup.center ↥(R : Subgroup K)).map (R : Subgroup K).subtype := by
    intro z hz
    refine ⟨⟨z, hZR hz⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_center_iff.1 hz g)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Subgroup.card_map_of_injective (R : Subgroup K).subtype_injective, hcR, hZ3]

theorem i112v_sylow_facts_of_mulEquiv {K' : Type*} [Group K'] [Finite K'] (e : K ≃* K')
    (h : ∀ R : Sylow 3 K', Nat.card ↥(R : Subgroup K') = 27 ∧
      (∃ r ∈ (R : Subgroup K'), ∃ s ∈ (R : Subgroup K'), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K'), r ^ 3 = 1) :
    ∀ R : Sylow 3 K, Nat.card ↥(R : Subgroup K) = 27 ∧
      (∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r) ∧
      ∀ r ∈ (R : Subgroup K), r ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R
  set R' : Sylow 3 K' := R.mapSurjective (f := e.toMonoidHom) e.surjective with hR'
  have hR'c : (R' : Subgroup K') = (R : Subgroup K).map e.toMonoidHom := rfl
  obtain ⟨hc, ⟨r, hr, s, hs, hrs⟩, hexp⟩ := h R'
  rw [hR'c] at hc hr hs hexp
  refine ⟨?_, ?_, ?_⟩
  · rw [← hc, Subgroup.card_map_of_injective e.injective]
  · obtain ⟨r₀, hr₀, rfl⟩ := hr
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    refine ⟨r₀, hr₀, s₀, hs₀, fun h' => hrs ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, h']
  · intro r₀ hr₀
    have h3 := hexp (e r₀) ⟨r₀, hr₀, rfl⟩
    rw [← map_pow] at h3
    exact (map_eq_one_iff e e.injective).1 h3

theorem i112v_two_le_pRank_of_sylow (R : Sylow 3 K) (hR : Nat.card ↥(R : Subgroup K) = 27)
    (hna : ∃ r ∈ (R : Subgroup K), ∃ s ∈ (R : Subgroup K), r * s ≠ s * r)
    (hexp : ∀ r ∈ (R : Subgroup K), r ^ 3 = 1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) := by
  have hna' : ∃ r s : ↥(R : Subgroup K), r * s ≠ s * r := by
    obtain ⟨r, hr, s, hs, h⟩ := hna
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, fun h' => h (congrArg Subtype.val h')⟩
  have hcR := i112v_card_center_eq_three hR hna'
  set Z : Subgroup K := (Subgroup.center ↥(R : Subgroup K)).map (R : Subgroup K).subtype with hZ
  have hZ3 : Nat.card Z = 3 := by
    rw [hZ, Subgroup.card_map_of_injective (R : Subgroup K).subtype_injective, hcR]
  obtain ⟨r, hr, s, hs, hrs⟩ := hna
  refine i112v_two_le_pRank_aux (Z := Z) (x := r) hZ3 ?_ ?_ (hexp r hr)
  · rintro _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨r, hr⟩).symm
  · rintro ⟨z, hz, hzr⟩
    apply hrs
    have := Subgroup.mem_center_iff.1 hz ⟨s, hs⟩
    have h2 : (z : K) = r := hzr
    rw [← h2]
    exact (congrArg Subtype.val this).symm

end Sylow

section Kernel

variable {K K' : Type*} [Group K] [Group K'] [Finite K]

omit [Finite K] in
theorem i112v_eq_one_of_mem_ker (f : K →* K') (hker : Nat.Coprime 3 (Nat.card f.ker))
    {R : Subgroup K} (hR : IsPGroup 3 R) {r : K} (hr : r ∈ R) (h1 : f r = 1) : r = 1 := by
  obtain ⟨n, hn⟩ := hR ⟨r, hr⟩
  have hrk : r ∈ f.ker := h1
  have hd1 : orderOf (⟨r, hrk⟩ : ↥f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
  have hd2 : orderOf (⟨r, hrk⟩ : ↥f.ker) ∣ 3 ^ n := by
    rw [Subgroup.orderOf_mk]
    have : orderOf (⟨r, hr⟩ : ↥R) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
    rwa [Subgroup.orderOf_mk] at this
  have hcop : Nat.Coprime (3 ^ n) (Nat.card f.ker) := Nat.Coprime.pow_left n hker
  have := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  have h2 : (⟨r, hrk⟩ : ↥f.ker) = 1 := orderOf_eq_one_iff.1 this
  exact congrArg Subtype.val h2

omit [Finite K] in
theorem i112v_card_map_eq (f : K →* K') (hker : Nat.Coprime 3 (Nat.card f.ker))
    {R : Subgroup K} (hR : IsPGroup 3 R) : Nat.card (R.map f) = Nat.card R := by
  have hinj : Function.Injective (f.comp R.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have := i112v_eq_one_of_mem_ker f hker hR x.2 hx
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hr : (f.comp R.subtype).range = R.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Kernel

end CFSG.HardMathSupport.Solomon.Coordinator
