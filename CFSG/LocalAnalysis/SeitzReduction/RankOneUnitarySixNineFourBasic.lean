module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIGDich
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 odd_card_goldschmidtOddCore)

namespace SixNineFour

theorem eq_one_of_mem_of_odd {H : Type*} [Group H] {O : Subgroup H} (hO : Odd (Nat.card O))
    {y : H} (hy : y ∈ O) {k : ℕ} (hk : y ^ 2 ^ k = 1) : y = 1 := by
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf y ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hy
  have hcop : Nat.Coprime (2 ^ k) (Nat.card O) := (Nat.coprime_two_left.2 hO).pow_left _
  have h3 : orderOf y ∣ 1 := hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem isSylowOf_top {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X) :
    IsSylowOf p (S : Subgroup X) ⊤ :=
  isSylowOf_iff.mpr ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩

theorem exists_conj_mem_of_isSylowOf' {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {K S P : Subgroup X} (hS : IsSylowOf p S K) (hPK : P ≤ K) (hP : IsPGroup p P) :
    ∃ a ∈ K, ∀ x ∈ P, a⁻¹ * x * a ∈ S := by
  have hP' : IsPGroup p (P.subgroupOf K) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hR : IsSylowOf p ((Q : Subgroup K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨a, haK, ha⟩ := hS.exists_mem_conj hR
  exact ⟨a, haK, fun x hx => (ha x).mp ⟨⟨x, hPK hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩⟩

theorem layer_comm_pCore {H : Type*} [Group H] [Finite H] {e o : H}
    (he : e ∈ CFSG.Open.goldschmidtLayer H) (ho : o ∈ CFSG.pCore 2 H) : o * e = e * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (CFSG.pCore 2 H) := (CFSG.pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have hc := CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal (CFSG.pCore 2 H)
    (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal
      (CFSG.pCore_normal (p := 2) (G := H)).isSubnormal)
  have hle := commutator_eq_bot_iff_le_centralizer.mp hc
  exact mem_centralizer_iff.mp (hle he) o ho

theorem mem_of_sq_eq_one_of_mem_normalClosure (hG : Goldschmidt1974) {X : Type} [Group X]
    [Finite X] (S : Sylow 2 X) {A : Subgroup X} (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hcl : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    {x : X} (hxS : x ∈ (S : Subgroup X)) (hxM : x ∈ normalClosure (A : Set X))
    (hx2 : x ^ 2 = 1) : x ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ha, hb, -⟩ := hG X S A hAS hAab hcl
  set M : Subgroup X := normalClosure (A : Set X) with hMdef
  have hMn : M.Normal := normalClosure_normal
  set O := CFSG.Open.goldschmidtOddCore M with hOdef
  set π := QuotientGroup.mk' O with hπdef
  set P := CFSG.pCore 2 (M ⧸ O) with hPdef
  have hPn : P.Normal := CFSG.pCore_normal
  set E := CFSG.Open.goldschmidtLayer (M ⧸ O) with hEdef
  have hSM : IsSylowOf 2 ((S : Subgroup X) ⊓ M) M :=
    (isSylowOf_top S).inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hMn])
  obtain ⟨Q, hQ⟩ := hSM.exists_sylow_eq_subgroupOf
  rw [inf_subgroupOf_right] at hQ
  have hPS : P ≤ ((S : Subgroup X).subgroupOf M).map π := by
    have := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := M ⧸ O))
      (Q.mapSurjective (QuotientGroup.mk'_surjective O))
    rwa [Sylow.coe_mapSurjective, hQ] at this
  have hPA : P ≤ (A.subgroupOf M).map π := by rw [hb]; exact le_sup_left
  have hπA2 : ∀ y ∈ (A.subgroupOf M).map π, y ^ 2 = 1 := by
    rintro _ ⟨a, haA, rfl⟩
    rw [← map_pow, show a ^ 2 = 1 from Subtype.ext (by simpa using hA2 _ (mem_subgroupOf.mp haA)),
      map_one]
  set x' : M := ⟨x, hxM⟩ with hx'
  have hxtop : π x' ∈ P ⊔ E := by rw [ha]; exact mem_top _
  obtain ⟨o, ho, e, he, hoe⟩ := mem_sup_of_normal_left.mp hxtop
  have hoS := hPS ho
  have hxS' : π x' ∈ ((S : Subgroup X).subgroupOf M).map π :=
    ⟨x', mem_subgroupOf.mpr hxS, rfl⟩
  have heS : e ∈ ((S : Subgroup X).subgroupOf M).map π := by
    have := mul_mem (inv_mem hoS) hxS'
    rwa [← hoe, inv_mul_cancel_left] at this
  have hoe' : o * e = e * o := layer_comm_pCore he ho
  have ho2 : o ^ 2 = 1 := hπA2 o (hPA ho)
  have hx'2 : (π x') ^ 2 = 1 := by
    rw [← map_pow, show x' ^ 2 = 1 from Subtype.ext (by simpa [hx'] using hx2), map_one]
  have he2 : e ^ 2 = 1 := by
    have h1 : (π x') ^ 2 = o ^ 2 * e ^ 2 := by rw [← hoe, (Commute.mul_pow hoe' 2)]
    rwa [hx'2, ho2, one_mul, eq_comm] at h1
  have heA : e ∈ (A.subgroupOf M).map π := by
    rw [hb]
    exact mem_sup_right (subset_closure ⟨mem_inf.mpr ⟨heS, he⟩, he2⟩)
  have hxA : π x' ∈ (A.subgroupOf M).map π := by
    rw [← hoe]
    exact mul_mem (hPA ho) heA
  obtain ⟨a, haA, hax⟩ := hxA
  have hy : a⁻¹ * x' ∈ O := QuotientGroup.eq.mp hax
  have haA' : (a : X) ∈ A := mem_subgroupOf.mp haA
  obtain ⟨k, hk⟩ := (S.isPGroup') ⟨(a : X)⁻¹ * x, mul_mem (inv_mem (hAS haA')) hxS⟩
  have hk' : (a⁻¹ * x') ^ 2 ^ k = 1 := Subtype.ext (by simpa [hx'] using congrArg Subtype.val hk)
  have h1 := eq_one_of_mem_of_odd (odd_card_goldschmidtOddCore M) hy hk'
  have hxa : x' = a := by rw [← mul_inv_cancel_left a x', h1, mul_one]
  have : x = (a : X) := congrArg Subtype.val hxa
  rw [this]
  exact haA'

theorem le_normalizer_inf {X : Type*} [Group X] {S M : Subgroup X} (hM : M.Normal) :
    S ≤ normalizer ((S ⊓ M : Subgroup X) : Set X) := by
  intro s hs
  refine mem_normalizer_iff.mpr fun h => ?_
  simp only [mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem (mul_mem hs h1) (inv_mem hs), hM.conj_mem h h2 s⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := mul_mem (mul_mem (inv_mem hs) h1) hs
      simpa [mul_assoc] using this
    · have := hM.conj_mem _ h2 s⁻¹
      simpa [mul_assoc] using this

theorem exists_mem_normalizer_conj_of_inf_eq {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    {M A : Subgroup X} (hM : M.Normal) (hSM : (S : Subgroup X) ⊓ M = A)
    (hcomm : ∀ x ∈ (S : Subgroup X), ∀ y ∈ (S : Subgroup X), x * y * x⁻¹ * y⁻¹ ∈ A)
    {t : X} (htS : t ∈ (S : Subgroup X)) (ht2 : t ^ 2 = 1)
    (hfree : ∀ a ∈ A, (a * t) ^ 2 = 1 → ∃ b ∈ A, b⁻¹ * t * b = a * t)
    {x : X} (hx : x⁻¹ * t * x ∈ normalizer (A : Set X)) :
    ∃ n ∈ normalizer (A : Set X), n⁻¹ * t * n = x⁻¹ * t * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAMle : A ≤ M := by rw [← hSM]; exact inf_le_right
  have hSA : (S : Subgroup X) ≤ normalizer (A : Set X) := by
    rw [← hSM]; exact le_normalizer_inf hM
  have hAM : IsSylowOf 2 A M := by
    rw [← hSM]
    exact (isSylowOf_top S).inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hM])
  obtain ⟨P, hP⟩ := hAM
  have hfr := Sylow.normalizer_sup_eq_top P
  rw [hP] at hfr
  have hxmem : x ∈ M ⊔ normalizer (A : Set X) := by rw [sup_comm, hfr]; exact mem_top x
  obtain ⟨m, hm, n, hn, hmn⟩ := mem_sup_of_normal_left.mp hxmem
  set w := m⁻¹ * t * m with hwdef
  have hxw : x⁻¹ * t * x = n⁻¹ * w * n := by rw [← hmn, hwdef]; group
  have hw : w ∈ normalizer (A : Set X) := by
    have e : w = n * (x⁻¹ * t * x) * n⁻¹ := by rw [hxw]; group
    rw [e]
    exact mul_mem (mul_mem hn hx) (inv_mem hn)
  have hw2 : w ^ 2 = 1 := by
    rw [hwdef, show (m⁻¹ * t * m) ^ 2 = m⁻¹ * t ^ 2 * m by rw [sq, sq]; group, ht2, mul_one,
      inv_mul_cancel]
  set K := normalizer (A : Set X) ⊓ (M ⊔ (S : Subgroup X)) with hK
  have hSK : (S : Subgroup X) ≤ K := le_inf hSA le_sup_right
  have hSylK : IsSylowOf 2 (S : Subgroup X) K := (isSylowOf_top S).of_le hSK le_top
  have hwK : w ∈ K := mem_inf.mpr ⟨hw, mul_mem (mul_mem (mem_sup_left (inv_mem hm))
    (mem_sup_right htS)) (mem_sup_left hm)⟩
  have hZ : IsPGroup 2 (zpowers w) := by
    have hdvd : orderOf w ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rwa [pow_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨y, hyK, hy⟩ := exists_conj_mem_of_isSylowOf' hSylK (zpowers_le.mpr hwK) hZ
  have hyw : y⁻¹ * w * y ∈ (S : Subgroup X) := hy w (mem_zpowers w)
  obtain ⟨hyN, hyMS⟩ := mem_inf.mp hyK
  obtain ⟨m', hm', s', hs', hms'⟩ := mem_sup_of_normal_left.mp hyMS
  have hywM : y⁻¹ * w * y * t⁻¹ ∈ M := by
    have h1 : t * (m * m') * t⁻¹ ∈ M := hM.conj_mem _ (mul_mem hm hm') t
    have h2 : m'⁻¹ * m⁻¹ * (t * (m * m') * t⁻¹) ∈ M :=
      mul_mem (mul_mem (inv_mem hm') (inv_mem hm)) h1
    have h3 : s'⁻¹ * (m'⁻¹ * m⁻¹ * (t * (m * m') * t⁻¹)) * s'⁻¹⁻¹ ∈ M :=
      hM.conj_mem _ h2 s'⁻¹
    have h4 : s'⁻¹ * t * s'⁻¹⁻¹ * t⁻¹ ∈ M := hAMle (hcomm _ (inv_mem hs') _ htS)
    have e : y⁻¹ * w * y * t⁻¹ =
        (s'⁻¹ * (m'⁻¹ * m⁻¹ * (t * (m * m') * t⁻¹)) * s'⁻¹⁻¹) * (s'⁻¹ * t * s'⁻¹⁻¹ * t⁻¹) := by
      rw [← hms', hwdef]; group
    rw [e]
    exact mul_mem h3 h4
  have haA : y⁻¹ * w * y * t⁻¹ ∈ A := by
    rw [← hSM]
    exact mem_inf.mpr ⟨mul_mem hyw (inv_mem htS), hywM⟩
  have hat2 : (y⁻¹ * w * y * t⁻¹ * t) ^ 2 = 1 := by
    rw [inv_mul_cancel_right, show (y⁻¹ * w * y) ^ 2 = y⁻¹ * w ^ 2 * y by rw [sq, sq]; group,
      hw2, mul_one, inv_mul_cancel]
  obtain ⟨b, hb, hbt⟩ := hfree _ haA hat2
  rw [inv_mul_cancel_right] at hbt
  refine ⟨b * y⁻¹ * n, mul_mem (mul_mem (le_normalizer hb) (inv_mem hyN)) hn, ?_⟩
  have e : w = y * (b⁻¹ * t * b) * y⁻¹ := by rw [hbt]; group
  rw [hxw, e]
  group

end SixNineFour

end CFSG.SeitzReduction.RankOne
