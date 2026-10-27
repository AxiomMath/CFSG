module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76

variable {G : Type*} [Group G]

theorem exists_fourGroup_le [Finite G] {R : Subgroup G} (h : 1 < Open.pRank 2 R) :
    ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s : Set ℕ := {k | ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}
    with hs
  have hne : s.Nonempty := ⟨0, ⊥, bot_le,
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [(mem_bot).mp hx, one_pow]⟩,
    by simp⟩
  have hbdd : BddAbove s := by
    refine ⟨Nat.card G, fun k hk => ?_⟩
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  obtain ⟨E, hER, hE, hEcard⟩ := Nat.sSup_mem hne hbdd
  have hk : 2 ≤ sSup s := h
  have hdvd : 2 ^ 2 ∣ Nat.card E := by
    rw [hEcard]
    exact pow_dvd_pow 2 hk
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨F.map E.subtype, (map_subtype_le F).trans hER, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨a, -, hae⟩ := a.2
    obtain ⟨b, -, hbe⟩ := b.2
    apply Subtype.ext
    simp only [coe_mul]
    rw [← hae, ← hbe]
    exact congrArg Subtype.val (hE.1.is_comm.comm a b)
  · rintro x ⟨y, -, rfl⟩
    exact hE.2 _ y.2
  · rw [card_map_of_injective E.subtype_injective, hF]
    norm_num

theorem one_lt_pRank_of_fourGroup {H : Type*} [Group H] [Finite H] {A E : Subgroup H}
    (hEA : E ≤ A) (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) : 1 < Open.pRank 2 A := by
  have hbdd : BddAbove {k | ∃ F : Subgroup H, F ≤ A ∧ IsElemAbelian 2 F ∧
      Nat.card F = 2 ^ k} := by
    refine ⟨Nat.card H, fun k hk => ?_⟩
    obtain ⟨F, -, -, hF⟩ := hk
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : Nat.card F ≤ Nat.card H := Subgroup.card_le_card_group F
    omega
  have hmem : 2 ∈ {k | ∃ F : Subgroup H, F ≤ A ∧ IsElemAbelian 2 F ∧ Nat.card F = 2 ^ k} :=
    ⟨E, hEA, hE, by rw [hE4]; norm_num⟩
  exact lt_of_lt_of_le (by norm_num) (le_csSup hbdd hmem)

theorem mem_of_two_element [Finite G] {L O : Subgroup G} (hOL : O ≤ normalizer (L : Set G))
    (hO : Odd (Nat.card O)) {x : G} (hx : x ∈ L ⊔ O) {k : ℕ} (hxk : x ^ (2 ^ k) = 1) :
    x ∈ L := by
  set M : Subgroup G := L ⊔ O with hM
  have hMN : M ≤ normalizer (L : Set G) := sup_le le_normalizer hOL
  have : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMN
  have hprod : Nat.card (O ⊔ L : Subgroup G) * Nat.card (O ⊓ L : Subgroup G) =
      Nat.card O * Nat.card L := by
    have : (L.subgroupOf (O ⊔ L)).Normal :=
      normal_subgroupOf_sup_of_le_normalizer hOL
    have : (L.subgroupOf O).Normal := normal_subgroupOf_of_le_normalizer hOL
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient O L hOL
    have h1 := card_eq_card_quotient_mul_card_subgroup (L.subgroupOf O)
    have h2 := card_eq_card_quotient_mul_card_subgroup (L.subgroupOf (O ⊔ L))
    have h3 : Nat.card (L.subgroupOf O) = Nat.card (O ⊓ L : Subgroup G) := by
      rw [← card_map_of_injective O.subtype_injective, subgroupOf_map_subtype, inf_comm]
    have h4 : Nat.card (L.subgroupOf (O ⊔ L)) = Nat.card L :=
      Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
    rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
    ring
  have hidx : (L.subgroupOf M).index * Nat.card (O ⊓ L : Subgroup G) = Nat.card O := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (L.subgroupOf M)
    have h2 : Nat.card (L.subgroupOf M) = Nat.card L :=
      Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [h2, ← index_eq_card] at h1
    have hMc : Nat.card M = Nat.card (O ⊔ L : Subgroup G) := by rw [hM, sup_comm]
    have hL : 0 < Nat.card L := Nat.card_pos
    have h3 : (L.subgroupOf M).index * Nat.card (O ⊓ L : Subgroup G) * Nat.card L =
        Nat.card O * Nat.card L := by
      rw [← hprod, ← hMc, h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hL h3
  have hodd : Odd (L.subgroupOf M).index := hO.of_dvd_nat ⟨_, hidx.symm⟩
  set y : M := ⟨x, hx⟩
  have hdvd1 : orderOf (QuotientGroup.mk' (L.subgroupOf M) y) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow]
      have : y ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hxk)
      rw [this, map_one])
  have hdvd2 : orderOf (QuotientGroup.mk' (L.subgroupOf M) y) ∣ (L.subgroupOf M).index := by
    rw [index]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (L.subgroupOf M).index :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h1 : orderOf (QuotientGroup.mk' (L.subgroupOf M) y) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.Asc76.Sec3Setting

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_mem_of_mem (hΩ : Sec3Setting Ω) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    {x : G} (hxK : x ∈ K) (hxJ : x ∈ J) (hx : orderOf x = 2) : K = J := by
  by_contra hne
  have hodd := (hΩ.twoPart K hK J hJ hne).2
  have h2 : 2 ∣ Nat.card (K ⊓ J : Subgroup G) := by
    rw [← hx]
    exact orderOf_dvd_natCard (K ⊓ J) (mem_inf.mpr ⟨hxK, hxJ⟩)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem _root_.CFSG.ComponentClassification.Asc76X.exists_involution {G : Type*} [Group G]
    {P : Subgroup G} [Finite P] (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    ∃ x ∈ P, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hP1 (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 h2
  exact ⟨x, x.2, by rw [← orderOf_coe] at hx; exact hx⟩

theorem eq_of_pGroup_le (hΩ : Sec3Setting Ω) {K J P : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (hPK : P ≤ K) (hPJ : P ≤ J) : K = J := by
  obtain ⟨x, hxP, hx⟩ := exists_involution hP hP1
  exact hΩ.eq_of_mem_of_mem hK hJ (hPK hxP) (hPJ hxP) hx

theorem mem_normalizer_of_mem (hΩ : Sec3Setting Ω) {K : Subgroup G} (hK : K ∈ Ω) {g x : G}
    (hxK : x ∈ K) (hxg : x ∈ rightConjugate K g) (hx : orderOf x = 2) :
    g ∈ normalizer (K : Set G) := by
  have h := hΩ.eq_of_mem_of_mem hK (hΩ.conj_mem K hK g) hxK hxg hx
  exact (rightConjugate_eq_self_iff K g).mp h.symm

theorem centralizer_le_normalizer (hΩ : Sec3Setting Ω) {K : Subgroup G} (hK : K ∈ Ω) {a : G}
    (haK : a ∈ K) (ha : orderOf a = 2) :
    centralizer ({a} : Set G) ≤ normalizer (K : Set G) := by
  intro c hc
  refine hΩ.mem_normalizer_of_mem hK haK ?_ ha
  rw [mem_rightConjugate_iff]
  have h := mem_centralizer_singleton_iff.mp hc
  rw [h, mul_inv_cancel_right]
  exact haK

theorem normalizer_le_normalizer (hΩ : Sec3Setting Ω) {K P : Subgroup G} (hK : K ∈ Ω)
    (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (hPK : P ≤ K) :
    normalizer (P : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  have h := hΩ.eq_of_pGroup_le hK (hΩ.conj_mem K hK g) hP hP1 hPK (fun x hx => by
    rw [mem_rightConjugate_iff]
    exact hPK ((mem_normalizer_iff.mp hg x).mp hx))
  exact (rightConjugate_eq_self_iff K g).mp h.symm

omit [Finite G] in
theorem exists_sylow (K : Subgroup G) : ∃ R : Subgroup G, IsSylowOf 2 R K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 K))
  exact ⟨_, Q, rfl⟩

theorem exists_fourGroup (hΩ : Sec3Setting Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨R, hR⟩ := exists_sylow K
  obtain ⟨E, hER, hE, hE4⟩ := exists_fourGroup_le (hΩ.rank K hK R hR).1
  obtain ⟨Q, rfl⟩ := hR
  exact ⟨E, hER.trans (map_subtype_le _), hE, hE4⟩

theorem exists_involution_mem (hΩ : Sec3Setting Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    ∃ x ∈ K, orderOf x = 2 := by
  obtain ⟨E, hEK, hE, hE4⟩ := hΩ.exists_fourGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  have hE1 : E ≠ ⊥ := fun h => by
    rw [h, card_bot] at hE4
    norm_num at hE4
  obtain ⟨x, hx, hx2⟩ := exists_involution hE2 hE1
  exact ⟨x, hEK hx, hx2⟩

theorem tightlyEmbedded (hΩ : Sec3Setting Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    TightlyEmbedded K := by
  refine ⟨?_, fun g hg => ?_⟩
  · obtain ⟨x, hxK, hx⟩ := hΩ.exists_involution_mem hK
    rw [even_iff_two_dvd, ← hx]
    exact orderOf_dvd_natCard K hxK
  · have hne : K ≠ rightConjugate K g := fun h => hg ((rightConjugate_eq_self_iff K g).mp h.symm)
    exact (hΩ.twoPart K hK _ (hΩ.conj_mem K hK g) hne).2

theorem le_normalizer_of_odd (hΩ : Sec3Setting Ω) {L O : Subgroup G} (hL : L ∈ Ω)
    (hO : Odd (Nat.card O)) (hLO : L ≤ normalizer (O : Set G)) :
    O ≤ normalizer (L : Set G) := by
  obtain ⟨E, hEL, hE, hE4⟩ := hΩ.exists_fourGroup hL
  have hpow : ∀ e : E, e ^ 2 = 1 := fun e => Subtype.ext (by simpa using hE.2 _ e.2)
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two E O hpow (by rw [hE4]; norm_num) hO.not_two_dvd_nat (hEL.trans hLO)
  rw [hgen]
  refine iSup_le fun e => iSup_le fun he1 => ?_
  have he2 : orderOf (e : G) = 2 := by
    rw [orderOf_coe]
    refine orderOf_eq_prime (hpow e) he1
  exact inf_le_right.trans (hΩ.centralizer_le_normalizer hL (hEL e.2) he2)

end CFSG.ComponentClassification.Asc76.Sec3Setting
