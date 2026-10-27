module

public import CFSG.GH74.GLS.C3.Layer1.Th2P64Cop
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Act

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem orderOf_mk_eq_two {K : Subgroup G} {x : G} (hx : x ∈ K) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥K) : kBar K) = 2 := by
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  refine orderOf_eq_prime ?_ ?_
  · rw [sq, ← QuotientGroup.mk_mul]
    have : (⟨x, hx⟩ : ↥K) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, QuotientGroup.mk_one]
  · intro h1
    have h2 : (⟨x, hx⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : x ∈ pPrimeCoreOf 2 K := ⟨_, h2, rfl⟩
    have h4 : orderOf x ∣ Nat.card (pPrimeCoreOf 2 K) := Subgroup.orderOf_dvd_natCard _ h3
    rw [hxo] at h4
    have hodd := TwoThin.card_pPrimeCoreOf_odd K
    exact absurd (hodd.of_dvd_nat h4) (by decide)

theorem exists_conj_of_isConj_kBar {K : Subgroup G} {a a' : G} (ha : a ∈ K) (ha' : a' ∈ K)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha'2 : a' * a' = 1) (ha'1 : a' ≠ 1)
    (hconj : IsConj (QuotientGroup.mk (⟨a, ha⟩ : ↥K) : kBar K) (QuotientGroup.mk ⟨a', ha'⟩)) :
    ∃ k ∈ K, a' = k * a * k⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
  have hxK : (c' : G) * a * (c' : G)⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem c'.2 ha) (K.inv_mem c'.2)
  have hx2 : ((c' : G) * a * (c' : G)⁻¹) * ((c' : G) * a * (c' : G)⁻¹) = 1 := by
    calc ((c' : G) * a * (c' : G)⁻¹) * ((c' : G) * a * (c' : G)⁻¹)
        = (c' : G) * (a * a) * (c' : G)⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hx1 : (c' : G) * a * (c' : G)⁻¹ ≠ 1 := by
    intro h1
    apply ha1
    calc a = (c' : G)⁻¹ * ((c' : G) * a * (c' : G)⁻¹) * (c' : G) := by group
      _ = 1 := by rw [h1]; group
  have hcoset : ((⟨(c' : G) * a * (c' : G)⁻¹, hxK⟩ : ↥K))⁻¹ * ⟨a', ha'⟩ ∈ pPrimeCore 2 ↥K := by
    have : (QuotientGroup.mk (⟨(c' : G) * a * (c' : G)⁻¹, hxK⟩ : ↥K) : kBar K) = QuotientGroup.mk ⟨a', ha'⟩ := by
      rw [← hc]
      rfl
    exact QuotientGroup.eq.1 this
  have hO : (((c' : G) * a * (c' : G)⁻¹)⁻¹ * a') ∈ pPrimeCoreOf 2 K :=
    ⟨_, hcoset, rfl⟩
  have hn : ∀ o ∈ pPrimeCoreOf 2 K,
      ((c' : G) * a * (c' : G)⁻¹) * o * ((c' : G) * a * (c' : G)⁻¹)⁻¹ ∈ pPrimeCoreOf 2 K := by
    intro o ho
    have := TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hxK)
    exact (Subgroup.mem_normalizer_iff.1 this o).1 ho
  obtain ⟨o, ho, hoeq⟩ := exists_conj_of_inv_mul_mem (TwoThin.card_pPrimeCoreOf_odd K) hx2 hx1 ha'2
    ha'1 hn hO
  have hoK : o ∈ K := TwoThin.pPrimeCoreOf_le K ho
  refine ⟨o * c', K.mul_mem hoK c'.2, ?_⟩
  rw [hoeq]
  group


theorem card_inf_pPrimeCoreOf_eq {K P' : Subgroup G} (hP' : IsPGroup 2 ↥P') {g : G} (hg : g ∈ P')
    (hgO : g ∈ pPrimeCoreOf 2 K) : g = 1 := by
  have h1 : orderOf g ∣ Nat.card (pPrimeCoreOf 2 K) := Subgroup.orderOf_dvd_natCard _ hgO
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP') ⟨g, hg⟩
  have hk' : orderOf g = 2 ^ k := by rw [← Subgroup.orderOf_mk g hg]; exact hk
  rw [hk'] at h1
  have hodd := TwoThin.card_pPrimeCoreOf_odd K
  by_contra hne
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.1 (by rw [hk']; simp))
  have h2 : 2 ∣ Nat.card (pPrimeCoreOf 2 K) := (dvd_pow_self 2 hk0).trans h1
  exact absurd (hodd.of_dvd_nat h2) (by decide)

theorem twoPartCard_le_inf_centralizer {K : Subgroup G} {b a : G}
    (hbK : b ∈ normalizer (K : Set G)) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (ha : a ∈ K) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hact : ∀ k ∈ K, (b * k * b⁻¹) * (a * k * a⁻¹)⁻¹ ∈ pPrimeCoreOf 2 K)
    (hclass : ∀ u v : kBar K, orderOf u = 2 → orderOf v = 2 → IsConj u v) :
    twoPartCard K ≤ twoPartCard (K ⊓ centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 K
  have hPcard : Nat.card P = twoPartCard K := hP.card_eq
  by_cases hPbot : P = ⊥
  · rw [hPbot, Subgroup.card_bot] at hPcard
    rw [← hPcard]
    exact Nat.one_le_two_pow
  obtain ⟨z, hzP, hz2, hzc⟩ := Th2.L627.exists_central_involution_of_normal hP.isPGroup
    (fun h hh w hw => P.mul_mem (P.mul_mem hh hw) (P.inv_mem hh)) le_rfl hPbot
  have hzK : z ∈ K := hP.le hzP
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hz1 : z ≠ 1 := fun h => by rw [h] at hz2; simp at hz2
  have hmk_a := orderOf_mk_eq_two ha ha2 ha1
  have hmk_z := orderOf_mk_eq_two hzK hz2' hz1
  obtain ⟨k, hkK, hk⟩ := exists_conj_of_isConj_kBar hzK ha hz2' hz1 ha2 ha1
    (hclass _ _ hmk_z hmk_a)
  set P' : Subgroup G := P.map (MulAut.conj k).toMonoidHom with hP'
  have hP'K : P' ≤ K := by
    rintro _ ⟨q, hq, rfl⟩
    exact K.mul_mem (K.mul_mem hkK (hP.le hq)) (K.inv_mem hkK)
  have hP'card : Nat.card P' = Nat.card P := Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hP'2 : IsPGroup 2 ↥P' := hP.isPGroup.map (MulAut.conj k).toMonoidHom
  have hacomm : ∀ p ∈ P', a * p * a⁻¹ = p := by
    rintro _ ⟨q, hq, rfl⟩
    show a * (k * q * k⁻¹) * a⁻¹ = k * q * k⁻¹
    have hzq : z * q = q * z := (hzc q hq).symm
    rw [hk]
    calc k * z * k⁻¹ * (k * q * k⁻¹) * (k * z * k⁻¹)⁻¹ = k * (z * q * z⁻¹) * k⁻¹ := by group
      _ = k * q * k⁻¹ := by rw [hzq]; group
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hlift : ∀ p ∈ P', ∃ y ∈ K ⊓ centralizer ({b} : Set G), p * y⁻¹ ∈ pPrimeCoreOf 2 K := by
    intro p hp
    have hpK : p ∈ K := hP'K hp
    have h1 : b⁻¹ * (p * b * p⁻¹) ∈ pPrimeCoreOf 2 K := by
      have h2 := hact p hpK
      rw [hacomm p hp] at h2
      rw [hbinv]
      have : b * (p * b * p⁻¹) = b * p * b⁻¹ * p⁻¹ := by rw [hbinv]; group
      rw [this]
      simpa using h2
    obtain ⟨y, hyK, hyb, hyp⟩ := exists_centralizer_lift hbK hb2 hb1 hpK h1
    exact ⟨y, ⟨hyK, mem_centralizer_singleton_iff.2 hyb.symm⟩, hyp⟩
  set ρ : ↥(K ⊓ centralizer ({b} : Set G)) →* kBar K :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) with hρ
  set ι : ↥P' →* kBar K := (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion hP'K)
    with hι
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have h1 : (⟨(p : G), hP'K p.2⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 hp
    have h2 : (p : G) ∈ pPrimeCoreOf 2 K := ⟨_, h1, rfl⟩
    exact Subtype.ext (card_inf_pPrimeCoreOf_eq hP'2 p.2 h2)
  have hrange : ι.range ≤ ρ.range := by
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨y, hy, hpy⟩ := hlift p hp
    refine ⟨⟨y, hy⟩, ?_⟩
    show (QuotientGroup.mk' (pPrimeCore 2 ↥K)) ⟨y, hy.1⟩ = (QuotientGroup.mk' (pPrimeCore 2 ↥K)) ⟨p, hP'K hp⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hyK : y ∈ K := hy.1
    have hO : y⁻¹ * (p * y⁻¹) * y ∈ pPrimeCoreOf 2 K := by
      have := TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (K.inv_mem hyK))
      have h5 := (Subgroup.mem_normalizer_iff.1 this (p * y⁻¹)).1 hpy
      simpa using h5
    obtain ⟨o, ho, hoeq⟩ := hO
    have : (⟨y, hyK⟩ : ↥K)⁻¹ * ⟨p, hP'K hp⟩ = o := by
      apply Subtype.ext
      have : ((⟨y, hyK⟩ : ↥K)⁻¹ * ⟨p, hP'K hp⟩ : ↥K).1 = y⁻¹ * p := rfl
      rw [this]
      have h6 : (o : G) = y⁻¹ * (p * y⁻¹) * y := hoeq
      rw [h6]; group
    rw [this]; exact ho
  have hdvd1 : Nat.card ι.range ∣ Nat.card ρ.range := Subgroup.card_dvd_of_le hrange
  have hdvd2 : Nat.card ρ.range ∣ Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by
    have := Subgroup.card_ker_mul_card_range ρ
    exact Dvd.intro_left _ this
  have hιcard : Nat.card ι.range = Nat.card P' :=
    Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv.symm
  have hdvd : Nat.card P' ∣ Nat.card ↥(K ⊓ centralizer ({b} : Set G)) := by
    rw [← hιcard]; exact hdvd1.trans hdvd2
  obtain ⟨m, hm⟩ := hP'2.exists_card_eq
  rw [hm] at hdvd
  have hle : m ≤ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  calc twoPartCard K = Nat.card P := hPcard.symm
    _ = Nat.card P' := hP'card.symm
    _ = 2 ^ m := hm
    _ ≤ 2 ^ (Nat.card ↥(K ⊓ centralizer ({b} : Set G))).factorization 2 :=
        Nat.pow_le_pow_right (by norm_num) hle

omit [Finite G] in
theorem card_mul_card_inf_eq {M K D : Subgroup G} (hKM : K ≤ M) (hDM : D ≤ M)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hMKD : ∀ m ∈ M, ∃ k ∈ K, ∃ d ∈ D, m = k * d) :
    Nat.card M * Nat.card ↥(K ⊓ D) = Nat.card K * Nat.card D := by
  have hnorm : M ≤ normalizer (K : Set G) := fun m hm => C3.Layer1.U1a.mem_normalizer_of_norm hKn hm
  have : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).2 hnorm
  set K' := K.subgroupOf M with hK'
  let ψ : ↥D →* ↥M ⧸ K' := (QuotientGroup.mk' K').comp (Subgroup.inclusion hDM)
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, d, hd, rfl⟩ := hMKD m hm
    refine ⟨⟨d, hd⟩, ?_⟩
    show (QuotientGroup.mk (⟨d, hDM hd⟩ : ↥M) : ↥M ⧸ K') = QuotientGroup.mk ⟨k * d, hm⟩
    rw [QuotientGroup.eq]
    have : (⟨d, hDM hd⟩ : ↥M)⁻¹ * ⟨k * d, hm⟩ = ⟨d⁻¹ * k * d, by
      exact M.mul_mem (M.mul_mem (M.inv_mem (hDM hd)) (hKM hk)) (hDM hd)⟩ := by
      apply Subtype.ext; show d⁻¹ * (k * d) = d⁻¹ * k * d; group
    rw [this]
    show d⁻¹ * k * d ∈ K
    have := hKn d⁻¹ (M.inv_mem (hDM hd)) k hk
    simpa using this
  have hker : Nat.card ψ.ker = Nat.card ↥(K ⊓ D) := by
    have : ψ.ker.map D.subtype = K ⊓ D := by
      ext g
      constructor
      · rintro ⟨⟨d, hd⟩, hdk, rfl⟩
        have : (⟨d, hDM hd⟩ : ↥M) ∈ K' := (QuotientGroup.eq_one_iff _).1 hdk
        exact ⟨this, hd⟩
      · rintro ⟨hgK, hgD⟩
        refine ⟨⟨g, hgD⟩, ?_, rfl⟩
        exact (QuotientGroup.eq_one_iff _).2 hgK
    rw [← this, Subgroup.card_map_of_injective D.subtype_injective]
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.range = Nat.card (↥M ⧸ K') := by
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top]
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
  have h4 : Nat.card K' = Nat.card K := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  rw [hker, h2] at h1
  calc Nat.card M * Nat.card ↥(K ⊓ D) = Nat.card K * (Nat.card (↥M ⧸ K') * Nat.card ↥(K ⊓ D)) := by
        rw [h3, h4]; ring
    _ = Nat.card K * Nat.card D := by rw [mul_comm (Nat.card (↥M ⧸ K')), h1]

theorem isSylowOf_of_factor {M K D V : Subgroup G} (hKM : K ≤ M) (hDM : D ≤ M)
    (hKn : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hMKD : ∀ m ∈ M, ∃ k ∈ K, ∃ d ∈ D, m = k * d)
    (hV : IsSylowOf 2 V D) (hP : twoPartCard K ≤ twoPartCard (K ⊓ D)) : IsSylowOf 2 V M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := card_mul_card_inf_eq hKM hDM hKn hMKD
  have hfac : (Nat.card M * Nat.card ↥(K ⊓ D)).factorization 2 =
      (Nat.card K * Nat.card D).factorization 2 := by rw [h]
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
  simp only [Finsupp.add_apply] at hfac
  have hP' : (Nat.card K).factorization 2 ≤ (Nat.card ↥(K ⊓ D)).factorization 2 := by
    unfold twoPartCard at hP
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hP
  have hdvd : Nat.card ↥(K ⊓ D) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
  have hP'' : (Nat.card ↥(K ⊓ D)).factorization 2 ≤ (Nat.card K).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 2
  have hMD : (Nat.card M).factorization 2 = (Nat.card D).factorization 2 := by omega
  refine isSylowOf_of_card (hV.le.trans hDM) ?_
  rw [hMD]
  exact hV.card_eq


theorem isConj_of_hasL2Model_odd {H : Type} [Group H] (h : HasL2Model H Odd) :
    ∀ u v : H, orderOf u = 2 → orderOf v = 2 → IsConj u v := by
  intro u v hu hv
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := C3.Layer1.Thm1.exists_l2_model_of_hasL2Model h
  let e' : H ≃* PSL(2, F) := e.trans (IVK.L2.equivPSL F)
  obtain ⟨p, hpc⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have := Fintype.ofFinite F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hpodd : Odd p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h2 | h2
    · exfalso
      have hev : Even (p ^ (n : ℕ)) := by
        rw [h2]; exact Nat.even_pow.2 ⟨even_two, n.ne_zero⟩
      exact (Nat.not_even_iff_odd.2 (hcard' ▸ hF.1)) hev
    · exact h2
  have h1 := Walter.psl2_isConj_of_orderOf_eq_two (K := F) hcard' hpodd n.pos
    (x := e' u) (y := e' v) (by rwa [MulEquiv.orderOf_eq]) (by rwa [MulEquiv.orderOf_eq])
  obtain ⟨c, hc⟩ := isConj_iff.1 h1
  refine isConj_iff.2 ⟨e'.symm c, e'.injective ?_⟩
  simpa using hc

end CFSG.GH74.GLS.Th2.Obs
