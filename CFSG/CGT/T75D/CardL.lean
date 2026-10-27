module

public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.CGT.Timmesfeld75.Sec4TwoSix
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.CGT.T75D

open CFSG.Open CFSG.Timmesfeld CFSG.CGT.Timmesfeld75
open scoped commutatorElement Pointwise
open CFSG.BenderSuzuki (PSU3Model)

section Aux

variable {Y : Type*} [Group Y] [Finite Y]

theorem sylow_centralizes_of_ppd (N : Subgroup Y) [N.Normal] {m k r : ℕ}
    (hNcard : Nat.card N = 2 ^ m) (hr : IsPrimitivePrimeDivisor r k) (hmk : m < k)
    (P : Sylow r Y) : ∀ p ∈ (P : Subgroup Y), ∀ n ∈ N, p * n = n * p := by
  have : Fact r.Prime := ⟨hr.prime⟩
  let ρ : ↥(P : Subgroup Y) →* MulAut ↥N :=
    (MulAut.conjNormal : Y →* MulAut N).comp (P : Subgroup Y).subtype
  have hρr : IsPGroup r ρ.range := P.isPGroup'.of_surjective ρ.rangeRestrict
    (MonoidHom.rangeRestrict_surjective ρ)
  have hk : 0 < k := by
    by_contra h0
    have h0' : k = 0 := by omega
    omega
  have hrange : Nat.card ρ.range = 1 := by
    rcases hρr.card_eq_or_dvd with h1 | hdvd
    · exact h1
    · exact absurd (faithful_le_of_primitive ρ.range.subtype (Subgroup.subtype_injective _) hk
        hNcard hr hdvd) (by omega)
  have hbot : ρ.range = ⊥ := (Subgroup.card_eq_one).1 hrange
  intro p hp n hn
  have h1 : ρ ⟨p, hp⟩ = 1 := by
    have : ρ ⟨p, hp⟩ ∈ ρ.range := ⟨⟨p, hp⟩, rfl⟩
    rw [hbot] at this
    exact (Subgroup.mem_bot).1 this
  have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : Y)) h1
  simp only [ρ, MonoidHom.comp_apply, Subgroup.subtype_apply, MulAut.conjNormal_apply,
    MulAut.one_apply] at h2
  calc p * n = (p * n * p⁻¹) * p := by group
    _ = n * p := by rw [h2]

theorem normal_le_center_of_perfect_quotient_ppd (N : Subgroup Y) [N.Normal]
    (hNab : ∀ n ∈ N, ∀ n' ∈ N, n * n' = n' * n) {m k r : ℕ} (hNcard : Nat.card N = 2 ^ m)
    (hr : IsPrimitivePrimeDivisor r k) (hmk : m < k) (hperf : commutator (Y ⧸ N) = ⊤)
    (hsimple : IsSimpleGroup ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)))
    (hrB : r ∣ Nat.card ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N))) : N ≤ Subgroup.center Y := by
  have hrp : r.Prime := hr.prime
  have : Fact r.Prime := ⟨hrp⟩
  have := hsimple
  let π : Y →* (Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N) :=
    (QuotientGroup.mk' (Subgroup.center (Y ⧸ N))).comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P⟩ : Nonempty (Sylow r Y) := inferInstance
  have hPC := sylow_centralizes_of_ppd N hNcard hr hmk P
  have hPπ : ∃ p ∈ (P : Subgroup Y), π p ≠ 1 := by
    by_contra hcon
    have hall : ∀ p ∈ (P : Subgroup Y), π p = 1 := fun p hp => by
      by_contra h1
      exact hcon ⟨p, hp, h1⟩
    have hle : (P : Subgroup Y) ≤ π.ker := fun p hp => MonoidHom.mem_ker.2 (hall p hp)
    have h1 := Subgroup.index_dvd_of_le hle
    have h2 : π.ker.index = Nat.card ((Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top]
    exact P.not_dvd_index ((h2 ▸ hrB).trans h1)
  obtain ⟨p, hpP, hpπ⟩ := hPπ
  let C : Subgroup Y := Subgroup.centralizer (N : Set Y)
  have hCnormal : C.Normal := Subgroup.normal_centralizer
  have hpC : p ∈ C := Subgroup.mem_centralizer_iff.2 fun n hn => (hPC p hpP n hn).symm
  have hCπ : C.map π = ⊤ := by
    have : (C.map π).Normal := hCnormal.map π hπ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map π) with h | h
    · exfalso
      have hmem : π p ∈ C.map π := Subgroup.mem_map_of_mem π hpC
      rw [h, Subgroup.mem_bot] at hmem
      exact hpπ hmem
    · exact h
  have hdecomp : ∀ yb : Y ⧸ N, ∃ c ∈ C,
      (QuotientGroup.mk c : Y ⧸ N)⁻¹ * yb ∈ Subgroup.center (Y ⧸ N) := by
    intro yb
    have hb : (QuotientGroup.mk yb : (Y ⧸ N) ⧸ Subgroup.center (Y ⧸ N)) ∈ C.map π := by
      rw [hCπ]
      trivial
    obtain ⟨c, hc, hcb⟩ := hb
    exact ⟨c, hc, QuotientGroup.eq.1 hcb⟩
  let Cb : Subgroup (Y ⧸ N) := C.map (QuotientGroup.mk' N)
  have hCb : Cb.Normal := hCnormal.map _ (QuotientGroup.mk'_surjective N)
  have hcomm : ∀ y₁ y₂ : Y ⧸ N, ⁅y₁, y₂⁆ ∈ Cb := by
    intro y₁ y₂
    obtain ⟨c₁, hc₁, hz₁⟩ := hdecomp y₁
    obtain ⟨c₂, hc₂, hz₂⟩ := hdecomp y₂
    let ρ : (Y ⧸ N) →* (Y ⧸ N) ⧸ Cb := QuotientGroup.mk' Cb
    have hρ : ∀ c ∈ C, ρ (QuotientGroup.mk c) = 1 := fun c hc =>
      (QuotientGroup.eq_one_iff _).2 ⟨c, hc, rfl⟩
    have e1 : ρ y₁ = ρ ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) :=
      calc ρ y₁ = ρ (QuotientGroup.mk c₁) * ρ ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) := by
            rw [← map_mul]
            group
        _ = ρ ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) := by rw [hρ c₁ hc₁, one_mul]
    have e2 : ρ y₂ = ρ ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) :=
      calc ρ y₂ = ρ (QuotientGroup.mk c₂) * ρ ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) := by
            rw [← map_mul]
            group
        _ = ρ ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) := by rw [hρ c₂ hc₂, one_mul]
    have hzz : (QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂ * ((QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁) =
        (QuotientGroup.mk c₁ : Y ⧸ N)⁻¹ * y₁ * ((QuotientGroup.mk c₂ : Y ⧸ N)⁻¹ * y₂) :=
      Subgroup.mem_center_iff.1 hz₁ _
    have hρcomm : ρ y₁ * ρ y₂ = ρ y₂ * ρ y₁ := by
      rw [e1, e2, ← map_mul, ← map_mul, hzz]
    have h1 : ρ ⁅y₁, y₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hρcomm
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hCbtop : Cb = ⊤ := by
    have : (⊤ : Subgroup (Y ⧸ N)) ≤ Cb := by
      rw [← hperf]
      exact Subgroup.commutator_le.2 fun g₁ _ g₂ _ => hcomm g₁ g₂
    exact top_le_iff.1 this
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : (QuotientGroup.mk y : Y ⧸ N) ∈ Cb := by
    rw [hCbtop]
    trivial
  obtain ⟨c, hc, hcy⟩ := hy
  have hn' : c⁻¹ * y ∈ N := QuotientGroup.eq.1 hcy
  have hnc : n * c = c * n := Subgroup.mem_centralizer_iff.1 hc n hn
  have hnn' : n * (c⁻¹ * y) = (c⁻¹ * y) * n := hNab n hn _ hn'
  have e : y = c * (c⁻¹ * y) := by group
  rw [e]
  calc c * (c⁻¹ * y) * n = c * ((c⁻¹ * y) * n) := mul_assoc _ _ _
    _ = c * (n * (c⁻¹ * y)) := by rw [hnn']
    _ = (c * n) * (c⁻¹ * y) := (mul_assoc _ _ _).symm
    _ = (n * c) * (c⁻¹ * y) := by rw [hnc]
    _ = n * (c * (c⁻¹ * y)) := mul_assoc _ _ _

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem six_mul_le (hAsc : AschbacherNoPolarInput)
    (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    ∃ f m : ℕ, 2 ≤ f ∧ Nat.card T = Nat.card (normIn T T₁) * 2 ^ f ∧
      Nat.card (sec4N T T₁ T₂) = 2 ^ m ∧ 6 * f ≤ m := by
  have hN : ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)).Normal := h.normal_sec4N
  obtain ⟨-, f, hf2, hcardT, hNormal, ⟨e⟩⟩ := h.sec4_two hAsc hq
  obtain ⟨m, hm⟩ := h.isPGroup_sec4N.exists_card_eq
  refine ⟨f, m, hf2, hcardT, hm, ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 6 * f) (by omega) (by omega)
  have hrdvd : r ∣ Nat.card (PSU3Model f) := by
    have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    rw [hmodel]
    exact primitive_dvd_card_psu3 (by omega) hr
  have hperf := h.commutator_quotient_eq_top hq
  have hBsimple : IsSimpleGroup ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup
      (CFSG.BenderSuzuki.IsBenderGroup.isPSU3 f hf2 e)
  have hrB : r ∣ Nat.card ((↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) ⧸
      Subgroup.center (↥(sec4Y T T₁ T₂) ⧸ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂))) := by
    rw [Nat.card_congr e.toEquiv]
    exact hrdvd
  have hNab : ∀ n ∈ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂),
      ∀ n' ∈ (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂), n * n' = n' * n := fun n hn n' hn' =>
    Subtype.ext (elemAbelian_mul_comm h.isElemAbelian_sec4N (Subgroup.mem_subgroupOf.1 hn)
      (Subgroup.mem_subgroupOf.1 hn'))
  have hNcard : Nat.card ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) = 2 ^ m := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec4N_le_sec4Y).toEquiv, hm]
  have hcen := normal_le_center_of_perfect_quotient_ppd
    ((sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂)) hNab hNcard hr hlt hperf hBsimple hrB
  obtain ⟨x, hxT, hxL⟩ := IsConcreteLE.exists_of_lt (h.sec3.cfg.normIn_lt h.pair.conj)
  have hxN : x ∉ sec4N T T₁ T₂ := fun hx => hxL (h.inf_sec4N_eq ▸ ⟨hxT, hx⟩)
  have hxM : x ∉ cfgM T T₁ := fun hx => hxN (cfgM_le_sec4N hx)
  obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.sec3.cfg.ne₁
  have hlN : l ∈ sec4N T T₁ T₂ := normIn_le_sec4N_mid hl
  have hl' : (⟨l, sec4N_le_sec4Y hlN⟩ : ↥(sec4Y T T₁ T₂)) ∈
      (sec4N T T₁ T₂).subgroupOf (sec4Y T T₁ T₂) := Subgroup.mem_subgroupOf.2 hlN
  have hxl : x * l = l * x :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (hcen hl')
      (⟨x, left_le_sec4Y hxT⟩ : ↥(sec4Y T T₁ T₂)))
  have hlM : l ∈ cfgM T T₁ ⊓ Subgroup.centralizer ({x} : Set G) :=
    ⟨Cfg.normIn_le_cfgM_right T T₁ hl, Subgroup.mem_centralizer_singleton_iff.2 hxl.symm⟩
  rw [h.sec3.cfg.cfgM_inf_centralizer hxT hxM] at hlM
  have hlT : l ∈ T ⊓ T₁ := ⟨normIn_le _ _ hlM, normIn_le _ _ hl⟩
  rw [h.sec3.cfg.inf, Subgroup.mem_bot] at hlT
  exact hl1 (Subtype.ext hlT)

theorem exists_sq_le_card_normIn
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card T = Nat.card (normIn T T₁) * 2 ^ f ∧
      (2 ^ f) ^ 2 ≤ Nat.card (normIn T T₁) := by
  obtain ⟨f, m, hf2, hcardT, hm, h6⟩ := six_mul_le hAsc h hq
  refine ⟨f, hf2, hcardT, ?_⟩
  have h1 := h.card_sec4N_le
  rw [hm] at h1
  have h2 : (2 ^ (2 * f)) ^ 3 ≤ Nat.card (normIn T T₁) ^ 3 := by
    calc (2 ^ (2 * f)) ^ 3 = 2 ^ (6 * f) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h6
      _ ≤ Nat.card (normIn T T₁) ^ 3 := h1
  have h3 : 2 ^ (2 * f) ≤ Nat.card (normIn T T₁) :=
    (Nat.pow_le_pow_iff_left (by norm_num)).1 h2
  calc (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
    _ ≤ Nat.card (normIn T T₁) := h3

theorem card_lt_sq_card_normIn
    (hAsc : AschbacherNoPolarInput) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) :
    Nat.card T < Nat.card (normIn T T₁) ^ 2 ∧ 16 ≤ Nat.card (normIn T T₁) := by
  obtain ⟨f, hf2, hcardT, hsq⟩ := exists_sq_le_card_normIn hAsc h hq
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hLpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hlt : 2 ^ f < Nat.card (normIn T T₁) := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [hcardT, pow_two]
    exact Nat.mul_lt_mul_of_pos_left hlt hLpos
  · calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left h4 2
      _ ≤ Nat.card (normIn T T₁) := hsq

end Main

end CFSG.CGT.T75D
