module

public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.GroupTheory.QuasiDihedralFusion.OddKernel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ABGTheoremB.IV9DGroups

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools

variable {K : Type*} [Group K]

theorem odd_card_of_forall_odd_orderOf [Finite K] {X : Subgroup K}
    (h : ∀ x ∈ X, Odd (orderOf x)) : Odd (Nat.card X) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy' : orderOf (y : K) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have := h y y.2
  rw [hy'] at this
  exact absurd this (by decide)

@[expose] def oddElements (N : Subgroup K)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, Odd (orderOf a) → Odd (orderOf b) → a * b = b * a) :
    Subgroup K where
  carrier := {g | g ∈ N ∧ Odd (orderOf g)}
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨N.mul_mem haN hbN, ?_⟩
    have hc : Commute a b := hcomm a haN b hbN ha hb
    exact (ha.mul hb).of_dvd_nat hc.orderOf_mul_dvd_mul_orderOf
  one_mem' := ⟨N.one_mem, by rw [orderOf_one]; decide⟩
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    exact ⟨N.inv_mem haN, by rwa [orderOf_inv]⟩

section OddElements

variable {N : Subgroup K}
  {hcomm : ∀ a ∈ N, ∀ b ∈ N, Odd (orderOf a) → Odd (orderOf b) → a * b = b * a}

theorem mem_oddElements {g : K} : g ∈ oddElements N hcomm ↔ g ∈ N ∧ Odd (orderOf g) :=
  Iff.rfl

theorem oddElements_le : oddElements N hcomm ≤ N := fun _ hg => hg.1

theorem odd_card_oddElements [Finite K] : Odd (Nat.card (oddElements N hcomm)) :=
  odd_card_of_forall_odd_orderOf fun _ hg => hg.2

theorem oddElements_normal (hN : N.Normal) : (oddElements N hcomm).Normal := by
  constructor
  rintro g ⟨hgN, hg⟩ k
  refine ⟨hN.conj_mem g hgN k, ?_⟩
  have e : k * g * k⁻¹ = (MulAut.conj k).toMonoidHom g := rfl
  rw [e, orderOf_injective _ (MulAut.conj k).injective g]
  exact hg

theorem exists_pow_two_pow_mem_oddElements [Finite K] {n : K} (hn : n ∈ N) :
    ∃ k : ℕ, n ^ 2 ^ k ∈ oddElements N hcomm := by
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  refine ⟨k, N.pow_mem hn _, ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) ⟨m, hnm⟩, hnm,
    Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
  exact hm

end OddElements

theorem mem_normalizer_sup [Finite K] {A B : Subgroup K} {g : K}
    (hA : g ∈ Subgroup.normalizer (A : Set K)) (hB : g ∈ Subgroup.normalizer (B : Set K)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup K) : Set K) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb)
  exact hle hn

theorem normal_odd_of_centralizes_sylow [Finite K] {N E Ω : Subgroup K} [hNn : N.Normal]
    [hΩn : Ω.Normal] (hNE : N ⊔ E = ⊤) (hdisj : Disjoint N E) (hE : Odd (Nat.card E))
    (hΩN : Ω ≤ N) (hΩ : Odd (Nat.card Ω)) (h2 : ∀ n ∈ N, ∃ k : ℕ, n ^ 2 ^ k ∈ Ω)
    (P : Sylow 2 K) (hEP : E ≤ Subgroup.centralizer ((P : Subgroup K) : Set K)) :
    (Ω ⊔ E).Normal ∧ Odd (Nat.card (Ω ⊔ E : Subgroup K)) ∧
      ∀ Z : Subgroup K, Odd (Nat.card Z) → Z ≤ Ω ⊔ E := by
  set W := Ω ⊔ E with hWdef
  have hNP : ∀ n ∈ N, ∃ p ∈ (P : Subgroup K), p⁻¹ * n ∈ Ω := by
    set f := QuotientGroup.mk' Ω
    have hf : Function.Surjective f := QuotientGroup.mk'_surjective Ω
    have hN2 : IsPGroup 2 (N.map f) := by
      rintro ⟨_, n, hn, rfl⟩
      obtain ⟨k, hk⟩ := h2 n hn
      refine ⟨k, Subtype.ext ?_⟩
      change f n ^ 2 ^ k = 1
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hk
    have : (N.map f).Normal := hNn.map f hf
    have hle := hN2.le_sylow_of_normal (P.mapSurjective hf)
    rw [Sylow.coe_mapSurjective] at hle
    intro n hn
    obtain ⟨p, hp, hpn⟩ := hle ⟨n, hn, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change (f p)⁻¹ * f n = 1
    rw [hpn, inv_mul_cancel]
  have hWN : ∀ w ∈ W, w ∈ Subgroup.normalizer (W : Set K) := fun w hw =>
    Subgroup.le_normalizer hw
  have hPN : (P : Subgroup K) ≤ Subgroup.normalizer (W : Set K) := by
    intro p hp
    refine mem_normalizer_sup ?_ ?_
    · rw [Subgroup.normalizer_eq_top_iff.mpr hΩn]
      exact Subgroup.mem_top p
    · refine Subgroup.mem_normalizer_fintype fun e he => ?_
      have hpe := Subgroup.mem_centralizer_iff.mp (hEP he) p hp
      rw [hpe, mul_inv_cancel_right]
      exact he
  have hWnorm : W.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hNE]
    refine sup_le (fun n hn => ?_) (fun e he => hWN e (Subgroup.mem_sup_right he))
    obtain ⟨p, hp, hpn⟩ := hNP n hn
    have e1 : n = p * (p⁻¹ * n) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (hPN hp) (hWN _ (Subgroup.mem_sup_left hpn))
  refine ⟨hWnorm, ?_, ?_⟩
  · have hdisj' : Disjoint Ω E := hdisj.mono_left hΩN
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Ω E
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hΩn]; exact le_top) hdisj']
    exact hΩ.mul hE
  · intro Z hZ
    refine le_of_odd_of_isPGroup_quotient W ?_ Z hZ
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hk : k ∈ N ⊔ E := hNE ▸ Subgroup.mem_top k
    have hk' : k ∈ ((N ⊔ E : Subgroup K) : Set K) := hk
    rw [Subgroup.normal_mul] at hk'
    obtain ⟨n, hn, e, he, rfl⟩ := hk'
    obtain ⟨j, hj⟩ := h2 n hn
    refine ⟨j, ?_⟩
    have he' : ((e : K) : K ⧸ W) = 1 := (QuotientGroup.eq_one_iff e).mpr (Subgroup.mem_sup_right he)
    rw [QuotientGroup.mk_mul, he', mul_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_sup_left hj

theorem le_centralizer_of_kleinFour {T D Z : Subgroup K} [IsKleinFour T]
    (hDN : D ≤ Subgroup.normalizer (T : Set K)) {x : K} (hxT : x ∈ T) (hx1 : x ≠ 1)
    (hxD : D ≤ Subgroup.centralizer ({x} : Set K))
    (hDT : ¬ D ≤ Subgroup.centralizer (T : Set K))
    (hZD : D ≤ Subgroup.normalizer (Z : Set K)) {t : K} (htT : t ∈ T) (ht1 : t ≠ 1)
    (hZt : Z ≤ Subgroup.centralizer ({t} : Set K)) :
    Z ≤ Subgroup.centralizer ({x} : Set K) := by
  by_cases htx : t = x
  · rwa [← htx]
  obtain ⟨d, hdD, hdC⟩ := IsConcreteLE.not_le_iff_exists.mp hDT
  have hdx : d * x * d⁻¹ = x := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hxD hdD), mul_inv_cancel_right]
  have hdtT : d * t * d⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hDN hdD) t).mp htT
  have hdt : d * t * d⁻¹ ≠ t := by
    intro hdt
    apply hdC
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hconj : d * u * d⁻¹ = u := by
      rcases kleinFour_mem_cases hxT htT hu hx1 ht1 (Ne.symm htx) with rfl | rfl | rfl | rfl
      · group
      · exact hdx
      · exact hdt
      · calc d * (x * t) * d⁻¹ = (d * x * d⁻¹) * (d * t * d⁻¹) := by group
          _ = x * t := by rw [hdx, hdt]
    calc u * d = d * u * d⁻¹ * d := by rw [hconj]
      _ = d * u := by group
  have hdt' : d * t * d⁻¹ = x * t := by
    refine kleinFour_eq_mul hxT htT hdtT hx1 ht1 (Ne.symm htx) ?_ ?_ hdt
    · intro h
      apply ht1
      calc t = d⁻¹ * (d * t * d⁻¹) * d := by group
        _ = 1 := by rw [h]; group
    · intro h
      apply htx
      calc t = d⁻¹ * (d * t * d⁻¹) * d := by group
        _ = d⁻¹ * (d * x * d⁻¹) * d := by rw [h, hdx]
        _ = x := by group
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzt : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.mp (hZt hz)
  have hz' : d⁻¹ * z * d ∈ Z := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hZD hdD)) z).mp hz
    simpa using h
  have hz't : d⁻¹ * z * d * t = t * (d⁻¹ * z * d) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hZt hz')
  have hzxt : z * (x * t) = x * t * z := by
    rw [← hdt']
    calc z * (d * t * d⁻¹) = d * (d⁻¹ * z * d * t) * d⁻¹ := by group
      _ = d * (t * (d⁻¹ * z * d)) * d⁻¹ := by rw [hz't]
      _ = d * t * d⁻¹ * z := by group
  have htt : t * t = 1 := kleinFour_mul_self htT
  calc z * x = z * (x * t) * t := by rw [mul_assoc z, mul_assoc x, htt, mul_one]
    _ = x * t * z * t := by rw [hzxt]
    _ = x * t * (z * t) := by group
    _ = x * t * (t * z) := by rw [hzt]
    _ = x * z := by rw [mul_assoc x, ← mul_assoc t, htt, one_mul]

end CFSG.ABGTheoremB.IV9DGroups
