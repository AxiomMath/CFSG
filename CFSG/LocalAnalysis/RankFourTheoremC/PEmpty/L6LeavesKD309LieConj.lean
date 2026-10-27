module

public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

open Subgroup CFSG.SignalizerFunctor.Helpers

variable {Y : Type} [Group Y] [Finite Y]

theorem inj_of_pgroup {p : ℕ} [hp : Fact p.Prime] (O : Subgroup Y) [O.Normal]
    (hO : ¬ p ∣ Nat.card O) {Q : Subgroup Y} (hQ : IsPGroup p Q) :
    ∀ a ∈ Q, ∀ b ∈ Q, QuotientGroup.mk' O a = QuotientGroup.mk' O b → a = b := by
  intro a ha b hb hab
  have hO' : a⁻¹ * b ∈ O := QuotientGroup.eq.mp hab
  have hQ' : a⁻¹ * b ∈ Q := Q.mul_mem (Q.inv_mem ha) hb
  obtain ⟨k, hk⟩ := hQ ⟨a⁻¹ * b, hQ'⟩
  have hk' : (a⁻¹ * b) ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hdvd1 : orderOf (a⁻¹ * b) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (a⁻¹ * b) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hO'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd1
  have hi0 : i = 0 := by
    by_contra hne
    apply hO
    rw [hi] at hdvd2
    exact (dvd_pow_self p hne).trans hdvd2
  have h1 : orderOf (a⁻¹ * b) = 1 := by rw [hi, hi0, pow_zero]
  exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h1)

theorem isConj_of_mk_isConj {p : ℕ} [hp : Fact p.Prime] (O : Subgroup Y) [O.Normal]
    (hO : ¬ p ∣ Nat.card O) {a b : Y} (ha : orderOf a = p) (hb : orderOf b = p)
    (h : IsConj (QuotientGroup.mk' O a) (QuotientGroup.mk' O b)) : IsConj a b := by
  classical
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective O c
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  set a' : Y := y * a * y⁻¹ with ha'
  have ha'o : orderOf a' = p := by
    have := MulEquiv.orderOf_eq (MulAut.conj y) a
    rw [MulAut.conj_apply] at this
    rw [ha', this, ha]
  have hπa' : π a' = π b := by
    rw [ha', map_mul, map_mul, map_inv]
    exact hc
  have hcop : Nat.Coprime p (Nat.card O) := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hO
  have hpg : ∀ {x : Y}, orderOf x = p → IsPGroup p (zpowers x) := fun {x} hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S1, hS1⟩ := pgroup_sylow_in_normal_sup p hp.out O (zpowers b) hcop (hpg hb)
  have hbO : b⁻¹ * a' ∈ O := QuotientGroup.eq.mp hπa'.symm
  have ha'K : a' ∈ O ⊔ zpowers b := by
    have : a' = b * (b⁻¹ * a') := by group
    rw [this]
    exact (O ⊔ zpowers b).mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left hbO)
  have hQ2 : IsPGroup p ((zpowers a').subgroupOf (O ⊔ zpowers b)) :=
    (hpg ha'o).of_equiv (Subgroup.subgroupOfEquivOfLe (zpowers_le.mpr ha'K)).symm
  have hcard : Nat.card ((zpowers a').subgroupOf (O ⊔ zpowers b)) =
      Nat.card (S1 : Subgroup ↥(O ⊔ zpowers b)) := by
    rw [hS1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.mpr ha'K)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_right : zpowers b ≤ O ⊔ zpowers b)).toEquiv, Nat.card_zpowers, Nat.card_zpowers,
      ha'o, hb]
  obtain ⟨S2, hS2⟩ := pgroup_sylow_of_card_eq p hp.out _ hQ2 S1 hcard
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (↥(O ⊔ zpowers b)) S2 S1
  have hbS1 : (⟨b, mem_sup_right (mem_zpowers b)⟩ : ↥(O ⊔ zpowers b)) ∈ (S1 : Subgroup _) := by
    rw [hS1]
    exact Subgroup.mem_subgroupOf.mpr (mem_zpowers b)
  have hbk : (⟨b, mem_sup_right (mem_zpowers b)⟩ : ↥(O ⊔ zpowers b)) ∈
      ((k • S2 : Sylow p ↥(O ⊔ zpowers b)) : Subgroup _) := by rw [hk]; exact hbS1
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hS2] at hbk
  have hmem : k.val⁻¹ * b * k.val ∈ zpowers a' := by
    have := Subgroup.mem_subgroupOf.mp hbk
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using this
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  have hkO : (k.val) ∈ O ⊔ zpowers b := k.2
  obtain ⟨o, ho, b', hb', hkob⟩ := Subgroup.mem_sup_of_normal_left.mp hkO
  have hπo1 : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hπk : π k.val ∈ zpowers (π b) := by
    rw [← hkob, map_mul, hπo1, one_mul]
    exact (MonoidHom.map_zpowers π b) ▸ Subgroup.mem_map_of_mem π hb'
  have hcomm : Commute (π k.val) (π b) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hπk
    rw [← hm]
    exact (Commute.refl (π b)).zpow_left m
  have hπj : (π b) ^ j = π b := by
    have h1 : π ((a') ^ j) = π (k.val⁻¹ * b * k.val) := by rw [hj]
    rw [map_pow, hπa', map_mul, map_mul, map_inv] at h1
    have h2 : (π k.val)⁻¹ * π b * π k.val = π b := by
      rw [mul_assoc, ← hcomm.eq, inv_mul_cancel_left]
    rw [h2] at h1
    exact h1
  have hπo : orderOf (π b) = p := by
    have hinj : Function.Injective (π.comp (zpowers b).subtype) := by
      intro u v huv
      exact Subtype.ext (inj_of_pgroup O hO (hpg hb) u u.2 v v.2 huv)
    have := orderOf_injective _ hinj ⟨b, mem_zpowers b⟩
    rw [Subgroup.orderOf_mk] at this
    rw [← hb]
    simpa using this
  have hj1 : j % p = 1 := by
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hπj
      have := orderOf_eq_one_iff.mpr hπj.symm
      rw [hπo] at this
      exact hp.out.one_lt.ne' this
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    have h3 : (π b) ^ j' = 1 := by
      have : π b * (π b) ^ j' = π b * 1 := by rw [← pow_succ', hπj, mul_one]
      exact mul_left_cancel this
    have h4 : p ∣ j' := hπo ▸ orderOf_dvd_of_pow_eq_one h3
    obtain ⟨m, rfl⟩ := h4
    rw [Nat.succ_eq_add_one, show p * m + 1 = 1 + p * m by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hp.out.one_lt]
  have haj : a' ^ j = a' := by
    have : a' ^ j = a' ^ (j % p) := by
      conv_lhs => rw [← Nat.mod_add_div j p, pow_add, pow_mul, ← ha'o, pow_orderOf_eq_one, one_pow,
        mul_one]
      rw [ha'o]
    rw [this, hj1, pow_one]
  rw [haj] at hj
  have hb2 : IsConj a' b := isConj_iff.mpr ⟨k.val, by
    rw [hj]; group⟩
  exact (isConj_iff.mpr ⟨y, rfl⟩ : IsConj a a').trans hb2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
