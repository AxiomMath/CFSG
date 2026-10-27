module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.SectionRank.Ccomm

open Subgroup
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [hp : Fact p.Prime]

theorem normal_and_index_eq_of_isCoatom (hP : IsPGroup p P) {M : Subgroup P}
    (hM : IsCoatom M) : M.Normal ∧ M.index = p := by
  have := hP.isNilpotent
  refine ⟨NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM, ?_⟩
  obtain ⟨k, hk⟩ := (hP.to_subgroup M).exists_card_eq
  obtain ⟨i, hi⟩ := hP.index M
  have hcard := M.card_mul_index
  rw [hk, hi, ← pow_add] at hcard
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one] at hi
    exact hM.1 hi
  have hdvd : p ^ (k + 1) ∣ Nat.card P := by
    rw [← hcard]
    exact pow_dvd_pow p (by omega)
  obtain ⟨K, hK, hMK⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hk
  have hKM : K ≠ M := by
    rintro rfl
    rw [hk] at hK
    exact absurd (Nat.pow_right_injective hp.out.two_le hK) (by omega)
  have hKtop : K = ⊤ := hM.2 K (lt_of_le_of_ne hMK hKM.symm)
  rw [hKtop, card_top, ← hcard] at hK
  have := Nat.pow_right_injective hp.out.two_le hK
  rw [hi, show i = 1 by omega, pow_one]

theorem frattini_quotient_elementary (hP : IsPGroup p P) :
    (frattini P).Characteristic ∧ (∀ a b : P ⧸ frattini P, a * b = b * a) ∧
      ∀ a : P ⧸ frattini P, a ^ p = 1 := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  have h := CFSG.isElementaryAbelian_quotient_frattini (R := P) (p := p)
  have := h.toIsMulCommutative
  exact ⟨inferInstance, fun a b => mul_comm' a b, fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p (P ⧸ frattini P)) a⟩

theorem commutator_mem_frattini (hP : IsPGroup p P) (x y : P) : ⁅x, y⁆ ∈ frattini P := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  exact CFSG.commutator_le_frattini_of_isPGroup (R := P) (p := p)
    (Subgroup.commutator_mem_commutator (mem_top x) (mem_top y))

theorem pow_mem_frattini (hP : IsPGroup p P) (x : P) : x ^ p ∈ frattini P := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  exact CFSG.pth_power_mem_frattini_of_isPGroup (R := P) (p := p) x

theorem frattini_eq_bot_iff (hP : IsPGroup p P) :
    frattini P = ⊥ ↔ (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  have : Fact (IsPGroup p P) := ⟨hP⟩
  rw [CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := P) (p := p)]
  constructor
  · intro h
    have := h.toIsMulCommutative
    exact ⟨fun a b => mul_comm' a b, fun a => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (CFSG.IsElementaryAbelian.exponent_dvd_p p P) a⟩
  · rintro ⟨hcomm, hpow⟩
    exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩,
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }

section Kernel

variable {G : Type*} [Group G] [Finite G]

theorem frattini_le_of_quotient_elementary (N : Subgroup G) [N.Normal]
    (hcomm : ∀ a b : G ⧸ N, a * b = b * a) (hpow : ∀ a : G ⧸ N, a ^ p = 1) :
    frattini G ≤ N := by
  have hQ : IsPGroup p (G ⧸ N) := fun a => ⟨1, by rw [pow_one]; exact hpow a⟩
  have : Fact (IsPGroup p (G ⧸ N)) := ⟨hQ⟩
  have : CFSG.IsElementaryAbelian p (G ⧸ N) :=
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩,
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }
  have hbot := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := G ⧸ N) (p := p)
  have h := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective N)
  rw [hbot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h
  exact h

theorem frattini_le_ker_of_elementary {A : Type*} [Group A] (f : G →* A)
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) : frattini G ≤ f.ker := by
  refine frattini_le_of_quotient_elementary (p := p) f.ker (fun a b => ?_) (fun a => ?_)
  · apply QuotientGroup.kerLift_injective f
    rw [map_mul, map_mul, hcomm]
  · apply QuotientGroup.kerLift_injective f
    rw [map_pow, hpow, map_one]

theorem frattini_le_of_commutator_pow_mem (N : Subgroup G) [N.Normal]
    (hcomm : ∀ a b : G, ⁅a, b⁆ ∈ N) (hpow : ∀ a : G, a ^ p ∈ N) : frattini G ≤ N := by
  refine frattini_le_of_quotient_elementary (p := p) N (fun a b => ?_) (fun a => ?_)
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := hcomm b⁻¹ a⁻¹
    rw [commutatorElement_def, inv_inv, inv_inv] at h
    simpa [mul_assoc] using h
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hpow a

end Kernel

theorem normal_inf_center_card (hP : IsPGroup p P) {N : Subgroup P} [N.Normal] (hN : N ≠ ⊥) :
    p ∣ Nat.card (N ⊓ center P : Subgroup P) ∧ p ≤ Nat.card (N ⊓ center P : Subgroup P) := by
  have := hP.isNilpotent
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  obtain ⟨k, hk⟩ := (hP.to_subgroup (N ⊓ center P)).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, card_eq_one] at hk
    exact hne hk
  rw [hk]
  exact ⟨dvd_pow_self p hk0, Nat.le_self_pow hk0 p⟩

theorem exists_central_extension (hP : IsPGroup p P) {A C : Subgroup P} [A.Normal] [C.Normal]
    (hAC : A < C) :
    ∃ b ∈ C, b ∉ A ∧ b ^ p ∈ A ∧ ∃ B : Subgroup P, B.Normal ∧ A < B ∧ B ≤ C ∧ b ∈ B ∧
      (∀ x ∈ B, ∃ k : ℤ, ∃ a ∈ A, x = b ^ k * a) ∧ ∀ x ∈ B, ∀ g : P, ⁅x, g⁆ ∈ A := by
  set π := QuotientGroup.mk' A
  have hQ : IsPGroup p (P ⧸ A) := hP.to_quotient A
  have : (C.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective A)
  have hCne : C.map π ≠ ⊥ := by
    intro h
    obtain ⟨c, hcC, hcA⟩ := IsConcreteLE.exists_of_lt hAC
    have : π c ∈ C.map π := mem_map_of_mem π hcC
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hcA this
  have hpdvd := (normal_inf_center_card hQ hCne).1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (C.map π ⊓ center (P ⧸ A) :
    Subgroup (P ⧸ A))) p hpdvd
  have hyC : (y : P ⧸ A) ∈ C.map π := y.2.1
  have hyZ : (y : P ⧸ A) ∈ center (P ⧸ A) := y.2.2
  have hyord : orderOf (y : P ⧸ A) = p := by rw [Subgroup.orderOf_coe]; exact hy
  obtain ⟨b, hbC, hby⟩ := mem_map.1 hyC
  have hb1 : π b ≠ 1 := by
    rw [hby]
    intro h
    rw [h, orderOf_one] at hyord
    exact hp.out.one_lt.ne' hyord.symm
  have hbA : b ∉ A := by
    intro h
    exact hb1 ((QuotientGroup.eq_one_iff b).2 h)
  have hbp : b ^ p ∈ A := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    change π b ^ p = 1
    rw [hby, ← hyord]
    exact pow_orderOf_eq_one _
  have hbZ : π b ∈ center (P ⧸ A) := hby ▸ hyZ
  set B : Subgroup P := (zpowers (π b)).comap π with hB
  have hzle : zpowers (π b) ≤ center (P ⧸ A) := (zpowers_le).2 hbZ
  have hBn : B.Normal := (normal_of_le_center hzle).comap π
  have hAB : A ≤ B := fun a ha => by
    have h1 : π a = 1 := (QuotientGroup.eq_one_iff a).2 ha
    change π a ∈ zpowers (π b)
    rw [h1]
    exact one_mem _
  have hbB : b ∈ B := mem_zpowers (π b)
  have hform : ∀ x ∈ B, ∃ k : ℤ, ∃ a ∈ A, x = b ^ k * a := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_comap.1 hx)
    refine ⟨k, (b ^ k)⁻¹ * x, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_zpow]
    change (π b ^ k)⁻¹ * π x = 1
    rw [hk, inv_mul_cancel]
  refine ⟨b, hbC, hbA, hbp, B, hBn, lt_of_le_of_ne hAB (fun h => hbA (h ▸ hbB)), ?_, hbB,
    hform, ?_⟩
  · intro x hx
    obtain ⟨k, a, ha, rfl⟩ := hform x hx
    exact mul_mem (zpow_mem hbC k) (hAC.le ha)
  · intro x hx g
    rw [← QuotientGroup.eq_one_iff]
    have hxZ : π x ∈ center (P ⧸ A) := hzle hx
    change π ⁅x, g⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.1 hxZ (π g)).symm

end CFSG.SectionRank.Ccomm
