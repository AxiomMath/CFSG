module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormal
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Prelim
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6KFacts
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6MainC

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_commutator_mem_center {P : Subgroup G} (hP : ⁅P, P⁆ = P) {h : G}
    (hN : h ∈ normalizer (P : Set G))
    (hc : ∀ p ∈ P, ∀ q ∈ P, h * p * h⁻¹ * p⁻¹ * q = q * (h * p * h⁻¹ * p⁻¹)) :
    h ∈ centralizer (P : Set G) := by
  have hmem : ∀ p ∈ P, h * p * h⁻¹ * p⁻¹ ∈ P := fun p hp =>
    mul_mem ((mem_normalizer_iff.mp hN p).mp hp) (inv_mem hp)
  have key : ⁅P, P⁆ ≤ centralizer ({h} : Set G) := by
    refine commutator_le.mpr fun p hp q hq => ?_
    obtain ⟨a, ha⟩ : ∃ a, a = h * p * h⁻¹ * p⁻¹ := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = h * q * h⁻¹ * q⁻¹ := ⟨_, rfl⟩
    have hbP : b ∈ P := hb ▸ hmem q hq
    have hpa : h * p * h⁻¹ = a * p := by rw [ha]; group
    have hqb : h * q * h⁻¹ = b * q := by rw [hb]; group
    have e2 : a * (p * b * q * p⁻¹) = (p * b * q * p⁻¹) * a := by
      rw [ha]
      exact hc p hp _ (mul_mem (mul_mem (mul_mem hp hbP) hq) (inv_mem hp))
    have e3 : p * b = b * p := by
      rw [hb]
      exact (hc q hq p hp).symm
    have e4 : b * (p * q * p⁻¹ * q⁻¹) = (p * q * p⁻¹ * q⁻¹) * b := by
      rw [hb]
      exact hc q hq _ (mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq))
    have hconj : h * (p * q * p⁻¹ * q⁻¹) * h⁻¹ = p * q * p⁻¹ * q⁻¹ := by
      calc h * (p * q * p⁻¹ * q⁻¹) * h⁻¹
          = (h * p * h⁻¹) * (h * q * h⁻¹) * (h * p * h⁻¹)⁻¹ * (h * q * h⁻¹)⁻¹ := by group
        _ = (a * p) * (b * q) * (a * p)⁻¹ * (b * q)⁻¹ := by rw [hpa, hqb]
        _ = a * (p * b * q * p⁻¹) * a⁻¹ * (q⁻¹ * b⁻¹) := by group
        _ = (p * b * q * p⁻¹) * a * a⁻¹ * (q⁻¹ * b⁻¹) := by rw [e2]
        _ = (p * b) * (q * p⁻¹ * q⁻¹) * b⁻¹ := by group
        _ = (b * p) * (q * p⁻¹ * q⁻¹) * b⁻¹ := by rw [e3]
        _ = b * (p * q * p⁻¹ * q⁻¹) * b⁻¹ := by group
        _ = (p * q * p⁻¹ * q⁻¹) * b * b⁻¹ := by rw [e4]
        _ = p * q * p⁻¹ * q⁻¹ := by group
    rw [mem_centralizer_singleton_iff]
    calc p * q * p⁻¹ * q⁻¹ * h = h * (p * q * p⁻¹ * q⁻¹) * h⁻¹ * h := by rw [hconj]
      _ = h * (p * q * p⁻¹ * q⁻¹) := by group
  rw [hP] at key
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (key hx)

omit [Finite G] in
theorem mem_center_of_mem_of_odd {Y O : Subgroup G} (hYO : Y ≤ normalizer (O : Set G))
    (hO : Odd (Nat.card O)) (hYs : IsSimpleGroup (rankTwoQuot Y))
    (hYe : Even (Nat.card (rankTwoQuot Y))) {y : Y} (hy : (y : G) ∈ O) : y ∈ center Y := by
  set OY : Subgroup Y := O.subgroupOf Y
  have : OY.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYO
  set πY := QuotientGroup.mk' (center Y)
  have hn : (OY.map πY).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (OY.map πY) with hb | ht
  · have h1 : πY y ∈ OY.map πY := ⟨y, hy, rfl⟩
    rw [hb, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff y).mp h1
  · exfalso
    have h1 : Nat.card (OY.map πY) ∣ Nat.card OY := OY.card_map_dvd πY
    have h2 : Nat.card OY ∣ Nat.card O := by
      have h3 := Subgroup.card_dvd_of_le (show OY.map Y.subtype ≤ O from fun _ ⟨c, hc, hce⟩ =>
        hce ▸ hc)
      rwa [Subgroup.card_map_of_injective Y.subtype_injective] at h3
    rw [ht, Subgroup.card_top] at h1
    exact (Nat.not_even_iff_odd.mpr (hO.of_dvd_nat (h1.trans h2))) hYe

omit [Finite G] in
theorem eq_one_of_conj_eq_mul {k t c : G} (hkt : k * t * k⁻¹ = t * c) (hkc : k * c = c * k)
    (hc : c ^ 2 = 1) (hk : Odd (orderOf k)) : c = 1 := by
  have key : ∀ m : ℕ, k ^ m * t * (k ^ m)⁻¹ = t * c ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hkc' : k * c ^ m * k⁻¹ = c ^ m := by
        rw [(Commute.pow_right hkc m).eq, mul_inv_cancel_right]
      calc k ^ (m + 1) * t * (k ^ (m + 1))⁻¹ = k * (k ^ m * t * (k ^ m)⁻¹) * k⁻¹ := by group
        _ = k * (t * c ^ m) * k⁻¹ := by rw [ih]
        _ = (k * t * k⁻¹) * (k * c ^ m * k⁻¹) := by group
        _ = t * c * c ^ m := by rw [hkt, hkc']
        _ = t * c ^ (m + 1) := by group
  have h1 := key (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hcm : c ^ orderOf k = 1 := mul_left_cancel (h1.symm.trans (mul_one t).symm)
  have h2 : orderOf c ∣ Nat.gcd (orderOf k) 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcm) (orderOf_dvd_of_pow_eq_one hc)
  rw [Nat.coprime_two_right.mpr hk] at h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2)

omit [Finite G] in
theorem exists_conj_mul_inv_mem {P Z : Subgroup G} {y : G}
    (hZc : ∀ z ∈ Z, ∀ p ∈ P, z * p = p * z) (hsq : ∀ p ∈ P, p ^ 2 ∈ Z)
    (hyP : ∀ p ∈ P, y * p * y⁻¹ ∈ P) (hy2 : ∀ p ∈ P, y ^ 2 * p = p * y ^ 2)
    {t₀ : G} (ht₀ : t₀ ∈ P) (ht₀Z : t₀ ∉ Z) :
    ∃ t ∈ P, t ∉ Z ∧ y * t * y⁻¹ * t⁻¹ ∈ Z := by
  have hcomm : ∀ s ∈ P, ∀ t ∈ P, s * t * s⁻¹ * t⁻¹ ∈ Z := by
    intro s hs t ht
    have h1 : t⁻¹ * (s ^ 2)⁻¹ = (s ^ 2)⁻¹ * t⁻¹ :=
      (hZc _ (inv_mem (hsq s hs)) _ (inv_mem ht)).symm
    have h2 : s * t * s⁻¹ * t⁻¹ = s * t * (s * t) * (s ^ 2)⁻¹ * (t ^ 2)⁻¹ := by
      calc s * t * s⁻¹ * t⁻¹ = s * t * (s * t) * (t⁻¹ * (s ^ 2)⁻¹) * t⁻¹ := by group
        _ = s * t * (s * t) * ((s ^ 2)⁻¹ * t⁻¹) * t⁻¹ := by rw [h1]
        _ = s * t * (s * t) * (s ^ 2)⁻¹ * (t ^ 2)⁻¹ := by group
    have hst : s * t * (s * t) ∈ Z := by
      rw [← pow_two]
      exact hsq _ (mul_mem hs ht)
    rw [h2]
    exact mul_mem (mul_mem hst (inv_mem (hsq s hs))) (inv_mem (hsq t ht))
  have hs : y * t₀ * y⁻¹ ∈ P := hyP t₀ ht₀
  by_cases h : t₀ * (y * t₀ * y⁻¹) ∈ Z
  · refine ⟨t₀, ht₀, ht₀Z, ?_⟩
    have h1 : t₀⁻¹ * (t₀ * (y * t₀ * y⁻¹)) = t₀ * (y * t₀ * y⁻¹) * t₀⁻¹ :=
      (hZc _ h _ (inv_mem ht₀)).symm
    have h2 : y * t₀ * y⁻¹ * t₀⁻¹ = t₀ * (y * t₀ * y⁻¹) * (t₀ ^ 2)⁻¹ := by
      calc y * t₀ * y⁻¹ * t₀⁻¹ = t₀⁻¹ * (t₀ * (y * t₀ * y⁻¹)) * t₀⁻¹ := by group
        _ = t₀ * (y * t₀ * y⁻¹) * t₀⁻¹ * t₀⁻¹ := by rw [h1]
        _ = t₀ * (y * t₀ * y⁻¹) * (t₀ ^ 2)⁻¹ := by group
    rw [h2]
    exact mul_mem h (inv_mem (hsq t₀ ht₀))
  · refine ⟨t₀ * (y * t₀ * y⁻¹), mul_mem ht₀ hs, h, ?_⟩
    have h1 : y ^ 2 * t₀ * (y ^ 2)⁻¹ = t₀ := by rw [hy2 t₀ ht₀, mul_inv_cancel_right]
    have h2 : y * (t₀ * (y * t₀ * y⁻¹)) * y⁻¹ * (t₀ * (y * t₀ * y⁻¹))⁻¹ =
        (y * t₀ * y⁻¹) * t₀ * (y * t₀ * y⁻¹)⁻¹ * t₀⁻¹ := by
      calc y * (t₀ * (y * t₀ * y⁻¹)) * y⁻¹ * (t₀ * (y * t₀ * y⁻¹))⁻¹
          = (y * t₀ * y⁻¹) * (y ^ 2 * t₀ * (y ^ 2)⁻¹) * (y * t₀ * y⁻¹)⁻¹ * t₀⁻¹ := by group
        _ = (y * t₀ * y⁻¹) * t₀ * (y * t₀ * y⁻¹)⁻¹ * t₀⁻¹ := by rw [h1]
    rw [h2]
    exact hcomm _ hs _ ht₀

omit [Finite G] in
theorem mem_of_pow_two_pow_mem {S : Subgroup G} {l : G} {n : ℕ} (hl : l ^ 2 ^ n ∈ S)
    (hlo : Odd (orderOf l)) : l ∈ S := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    ((Nat.coprime_two_left.mpr hlo).pow_left n : Nat.Coprime (2 ^ n) (orderOf l))
  rw [← hm]
  exact pow_mem hl m

omit [Finite G] in
theorem mul_commutator_mul_eq {c c' z z' : G} (h1 : z * c' = c' * z) (h2 : z * z' = z' * z)
    (h3 : z' * c⁻¹ = c⁻¹ * z') :
    c * z * (c' * z') * (c * z)⁻¹ * (c' * z')⁻¹ = c * c' * c⁻¹ * c'⁻¹ := by
  calc c * z * (c' * z') * (c * z)⁻¹ * (c' * z')⁻¹
      = c * (z * c') * z' * z⁻¹ * c⁻¹ * z'⁻¹ * c'⁻¹ := by group
    _ = c * (c' * z) * z' * z⁻¹ * c⁻¹ * z'⁻¹ * c'⁻¹ := by rw [h1]
    _ = c * c' * (z * z') * z⁻¹ * c⁻¹ * z'⁻¹ * c'⁻¹ := by group
    _ = c * c' * (z' * z) * z⁻¹ * c⁻¹ * z'⁻¹ * c'⁻¹ := by rw [h2]
    _ = c * c' * (z' * c⁻¹) * z'⁻¹ * c'⁻¹ := by group
    _ = c * c' * (c⁻¹ * z') * z'⁻¹ * c'⁻¹ := by rw [h3]
    _ = c * c' * c⁻¹ * c'⁻¹ := by group

omit [Finite G] in
theorem mem_normalizer_u3X₀ {L K : Subgroup G} {g : G} (hgL : g ∈ normalizer (L : Set G))
    (hgK : g ∈ centralizer (K : Set G)) :
    g ∈ normalizer (u3X₀ L K : Set G) ∧
      g ∈ normalizer ((⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G) : Set G) := by
  have h1 : L.map (MulAut.conj g).toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp hgL
  have h2 : K.map (MulAut.conj g).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ hgK)
  have h3 : (u3X₀ L K).map (MulAut.conj g).toMonoidHom = u3X₀ L K := by
    rw [u3X₀_map_conj, h1, h2]
  refine ⟨mem_normalizer_iff_map_conj_eq.mpr h3, mem_normalizer_iff_map_conj_eq.mpr ?_⟩
  show (⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom = _
  rw [map_commutator, h3]

abbrev u3X₀CentralizerPre (L K : Subgroup G) : Subgroup G :=
  ((u3X₀CentralizerC L K).comap
    (QuotientGroup.mk' (standardComponentOddCore (centralizer (K : Set G))))).map
    (centralizer (K : Set G)).subtype

namespace Sec3

variable {L T : Subgroup G}

theorem normalizer_inf_centralizer_le_normalizer_T₁ (h : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) :
    normalizer (L : Set G) ⊓ centralizer (gmsA L T : Set G) ≤
      normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := Asc76X.fusionBenderBorel_of_mulEquiv_psu3 hf e
  have hZ := odd_card_center_of_psu3 h.hyp.standard.1.1 hf e
  have hP := h.isSylowOf_T₁
  obtain ⟨-, hA₁card, -⟩ := sylow_of_psu3 hZ hf e hP
  obtain ⟨a, ha1⟩ : ∃ a : gmsA L T, a ≠ 1 := by
    refine Subgroup.ne_bot_iff_exists_ne_one.mp fun hbot => ?_
    have h1 : Nat.card (gmsA L T) = 1 := by rw [hbot, card_bot]
    have h2 : Nat.card (gmsA L T) = 2 ^ f := hA₁card
    have h3 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    omega
  have ha1' : (a : G) ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  intro c hc
  obtain ⟨hcN, hcA⟩ := mem_inf.mp hc
  have hP' : IsSylowOf 2 ((T ⊓ L).map (MulAut.conj c).toMonoidHom) L := by
    refine isSylowOf_of_card ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.mp hcN x).mp (hP.le hx)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective, hP.card_eq]
  have haP : (a : G) ∈ T ⊓ L := (mem_inf.mp a.2).1
  have haP' : (a : G) ∈ (T ⊓ L).map (MulAut.conj c).toMonoidHom := by
    refine ⟨a, haP, ?_⟩
    have hca := (mem_centralizer_iff.mp hcA) (a : G) a.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hca, mul_inv_cancel_right]
  have heq := eq_of_mem_of_mem hZ hP hP' hB haP haP' ha1'
  rw [mem_normalizer_iff_map_conj_eq]
  exact heq.symm

theorem commutator_commutator_u3X₀ (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    ⁅(⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G), ⁅u3X₀ L K, u3X₀ L K⁆⁆ = ⁅u3X₀ L K, u3X₀ L K⁆ := by
  obtain ⟨-, hdec, -, -, -, -, -, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  have hX₀'X₀ : (⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G) ≤ u3X₀ L K :=
    commutator_le.mpr fun x hx y hy => mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hX₀L : u3X₀ L K ≤ L := by
    show ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ ≤ L
    exact (commutator_le.mpr fun x hx y hy =>
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans inf_le_left
  refine le_antisymm (Subgroup.commutator_mono hX₀'X₀ hX₀'X₀) ?_
  refine commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨c, hc, z, hz, rfl⟩ := hdec x hx
  obtain ⟨c', hc', z', hz', rfl⟩ := hdec y hy
  have hzL : ∀ w ∈ L, (z : G) * w = w * z := fun w hw =>
    (congrArg Subtype.val (mem_center_iff.mp hz ⟨w, hw⟩)).symm
  have hz'L : ∀ w ∈ L, (z' : G) * w = w * z' := fun w hw =>
    (congrArg Subtype.val (mem_center_iff.mp hz' ⟨w, hw⟩)).symm
  have hcL : c ∈ L := hX₀L (hX₀'X₀ hc)
  have hc'L : c' ∈ L := hX₀L (hX₀'X₀ hc')
  have e1 : (z : G) * c' = c' * z := hzL c' hc'L
  have e2 : (z : G) * z' = z' * z := hzL z' z'.2
  have e3 : (z' : G) * c⁻¹ = c⁻¹ * z' := hz'L _ (inv_mem hcL)
  show c * z * (c' * z') * (c * z)⁻¹ * (c' * z')⁻¹ ∈ _
  rw [mul_commutator_mul_eq e1 e2 e3]
  exact commutator_mem_commutator hc hc'

theorem mem_centralizer_of_mem_sup (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) {y : G}
    (hyLC : y ∈ L ⊔ centralizer (L : Set G)) (hyK : y ∈ centralizer (K : Set G))
    (hyX : y ∈ centralizer ((⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G) : Set G))
    (hyT₁ : y ∈ normalizer ((T ⊓ L : Subgroup G) : Set G)) {n : ℕ} (hyn : y ^ 2 ^ n = 1) :
    y ∈ centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  obtain ⟨-, -, hAX', hT₁K, -, hZX', -, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  have hP := h3.isSylowOf_T₁
  set C := centralizer (L : Set G)
  set X₀' : Subgroup G := ⁅u3X₀ L K, u3X₀ L K⁆
  have hX₀'L : X₀' ≤ L := (commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans
    ((commutator_le.mpr fun x hx y hy =>
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans inf_le_left)
  have hLC : L ≤ normalizer (C : Set G) :=
    le_normalizer.trans h3.normalizer_le_normalizer_centralizer
  obtain ⟨l, hl, k, hk, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hLC hyLC
  have hlk : l * k = k * l := mem_centralizer_iff.mp hk l hl
  have hlK : l ∈ centralizer (K : Set G) := by
    have := mul_mem hyK (inv_mem (Subgroup.centralizer_le hKL hk))
    rwa [mul_inv_cancel_right] at this
  have hlX : l ∈ centralizer (X₀' : Set G) := by
    have := mul_mem hyX (inv_mem (Subgroup.centralizer_le hX₀'L hk))
    rwa [mul_inv_cancel_right] at this
  have hlT : l ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    have hkT : k ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le inf_le_right hk)
    have := mul_mem hyT₁ (inv_mem hkT)
    rwa [mul_inv_cancel_right] at this
  have hw : l ^ 2 ^ n ∈ C := by
    have h1 : (l * k) ^ 2 ^ n = l ^ 2 ^ n * k ^ 2 ^ n := (Commute.mul_pow hlk _)
    rw [h1] at hyn
    rw [eq_inv_of_mul_eq_one_left hyn]
    exact inv_mem (pow_mem hk _)
  have hwr : (l ^ 2 ^ n) ^ Nat.card (center L) = 1 := by
    have hwZ : (⟨l ^ 2 ^ n, pow_mem hl _⟩ : L) ∈ center L :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hw g g.2)
    have h1 : (⟨_, hwZ⟩ : center L) ^ Nat.card (center L) = 1 := pow_card_eq_one'
    have h2 := congrArg (fun x : center L => ((x : L) : G)) h1
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
  obtain ⟨u, hu⟩ : ∃ u, u = l ^ Nat.card (center L) := ⟨_, rfl⟩
  have hun : u ^ 2 ^ n = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul]
    exact hwr
  have hu2 : IsPGroup 2 (zpowers u) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hun)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
  have huL : u ∈ L := hu ▸ pow_mem hl _
  have huT : u ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := hu ▸ pow_mem hlT _
  have huK : u ∈ centralizer (K : Set G) := hu ▸ pow_mem hlK _
  have huX : u ∈ centralizer (X₀' : Set G) := hu ▸ pow_mem hlX _
  have huT₁ : u ∈ T ⊓ L := by
    have hle : zpowers u ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := (zpowers_le).mpr huT
    have hsup := hu2.to_sup_of_normal_right' hP.isPGroup hle
    have heq := hP.eq_of_le le_sup_right (sup_le ((zpowers_le).mpr huL) hP.le) hsup
    rw [← heq]
    exact mem_sup_left (mem_zpowers u)
  have huA : u ∈ gmsA L T := hT₁K (mem_inf.mpr ⟨huT₁, huK⟩)
  have huX' : u ∈ X₀' := hAX' huA
  have huZ : (⟨u, huX'⟩ : X₀') ∈ center X₀' :=
    mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp huX g g.2)
  have hu1 : (⟨u, huX'⟩ : X₀') = 1 := eq_one_of_pow_two_pow_of_mem_odd hZX' huZ
    (Subtype.ext (by simpa using hun))
  have hlr : l ^ Nat.card (center L) = 1 := hu ▸ congrArg Subtype.val hu1
  have hlo : Odd (orderOf l) := hZ.of_dvd_nat (orderOf_dvd_of_pow_eq_one hlr)
  exact mul_mem (mem_of_pow_two_pow_mem hw hlo) hk

theorem false_of_not_mem_sup (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) {y : G}
    (hyN : y ∈ normalizer (L : Set G)) (hyT₁ : y ∈ normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hyA : y ∈ centralizer (gmsA L T : Set G)) (hyK : y ∈ centralizer (K : Set G))
    {n : ℕ} (hyn : y ^ 2 ^ n = 1) (hyLC : y ∉ L ⊔ centralizer (L : Set G))
    (hy2 : y ^ 2 ∈ centralizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  have hP := h3.isSylowOf_T₁
  obtain ⟨hT₁card, hA₁card, hA₁sq, -, hsq, -⟩ := sylow_of_psu3 hZ hf e hP
  obtain ⟨-, -, -, hT₁K, -, -, -, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  set T₁ := T ⊓ L with hT₁def
  set A₁ := gmsA L T with hA₁def
  have hKH' : T₁ ⊔ K = L ⊓ normalizer (T₁ : Set G) ⊓ centralizer (A₁ : Set G) := hKH
  have hKN : K ≤ normalizer (T₁ : Set G) := fun k hk =>
    (mem_inf.mp (mem_inf.mp ((hKH' ▸ (le_sup_right : K ≤ T₁ ⊔ K)) hk)).1).2
  have hKA : K ≤ centralizer (A₁ : Set G) := fun k hk =>
    (mem_inf.mp ((hKH' ▸ (le_sup_right : K ≤ T₁ ⊔ K)) hk)).2
  have hyP : ∀ p ∈ T₁, y * p * y⁻¹ ∈ T₁ := fun p hp => (mem_normalizer_iff.mp hyT₁ p).mp hp
  have hctr := centralizer_le_of_psu3 h3.hyp.standard.1.1 hZ hf e hP hyN hyP hyn
    (fun a ha => (mem_centralizer_iff.mp hyA a ha).symm) hyLC
    ⟨1, one_mem _, y ^ 2, hy2, by rw [one_mul]⟩
  have hA₁c : ∀ z ∈ A₁, ∀ p ∈ T₁, z * p = p * z := fun z hz p hp =>
    (mem_centralizer_iff.mp (mem_inf.mp hz).2 p hp).symm
  have hnle : ¬ T₁ ≤ A₁ := by
    intro hcon
    have h1 := Subgroup.card_le_of_le hcon
    rw [hT₁card, hA₁card] at h1
    have h2 : 2 ^ f < (2 ^ f) ^ 3 := by
      have h3 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
      calc 2 ^ f = 2 ^ f * 1 * 1 := by ring
        _ < 2 ^ f * 2 ^ f * 2 ^ f := by
          apply Nat.mul_lt_mul_of_lt_of_le (Nat.mul_lt_mul_of_pos_left h3 (by omega)) h3.le
            (by omega)
        _ = (2 ^ f) ^ 3 := by ring
    omega
  obtain ⟨t₀, ht₀, ht₀A⟩ := Set.not_subset.mp hnle
  obtain ⟨t, htT₁, htA, hd⟩ := exists_conj_mul_inv_mem hA₁c hsq hyP
    (fun p hp => (mem_centralizer_iff.mp hy2 p (hP.le hp)).symm) ht₀ ht₀A
  have htK : t ∈ centralizer (K : Set G) := by
    refine mem_centralizer_iff.mpr fun k hk => ?_
    have hkA := hKA hk
    have hyk : y * k = k * y := (mem_centralizer_iff.mp hyK k hk).symm
    have ht' : k * t * k⁻¹ ∈ T₁ := (mem_normalizer_iff.mp (hKN hk) t).mp htT₁
    have hkd : k * (y * t * y⁻¹ * t⁻¹) * k⁻¹ = y * t * y⁻¹ * t⁻¹ := by
      rw [← (mem_centralizer_iff.mp hkA _ hd), mul_inv_cancel_right]
    have hd' : y * (k * t * k⁻¹) * y⁻¹ * (k * t * k⁻¹)⁻¹ = y * t * y⁻¹ * t⁻¹ := by
      calc y * (k * t * k⁻¹) * y⁻¹ * (k * t * k⁻¹)⁻¹
          = (y * k) * t * (y * k)⁻¹ * k * t⁻¹ * k⁻¹ := by group
        _ = (k * y) * t * (k * y)⁻¹ * k * t⁻¹ * k⁻¹ := by rw [hyk]
        _ = k * (y * t * y⁻¹ * t⁻¹) * k⁻¹ := by group
        _ = y * t * y⁻¹ * t⁻¹ := hkd
    have hs : y * (t⁻¹ * (k * t * k⁻¹)) = t⁻¹ * (k * t * k⁻¹) * y := by
      have e1 : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
      have e2 : y * (k * t * k⁻¹) * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * (k * t * k⁻¹) := by
        rw [← hd']
        group
      calc y * (t⁻¹ * (k * t * k⁻¹))
          = (y * t * y⁻¹)⁻¹ * (y * (k * t * k⁻¹) * y⁻¹) * y := by group
        _ = ((y * t * y⁻¹ * t⁻¹) * t)⁻¹ * ((y * t * y⁻¹ * t⁻¹) * (k * t * k⁻¹)) * y := by
          rw [e2, ← e1]
        _ = t⁻¹ * (k * t * k⁻¹) * y := by group
    have hsA : t⁻¹ * (k * t * k⁻¹) ∈ A₁ := hctr _ (mul_mem (inv_mem htT₁) ht') hs
    have hkt : k * t * k⁻¹ = t * (t⁻¹ * (k * t * k⁻¹)) := by group
    have hkc : k * (t⁻¹ * (k * t * k⁻¹)) = (t⁻¹ * (k * t * k⁻¹)) * k :=
      (mem_centralizer_iff.mp hkA _ hsA).symm
    have hko : Odd (orderOf k) := hKo.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hk)
    have h1 := eq_one_of_conj_eq_mul hkt hkc (hA₁sq _ hsA) hko
    have h2 : k * t * k⁻¹ = t := by rw [hkt, h1, mul_one]
    calc k * t = k * t * k⁻¹ * k := by group
      _ = t * k := by rw [h2]
  exact htA (hT₁K (mem_inf.mpr ⟨htT₁, htK⟩))

theorem mem_T₀_of_mem_normalizer
    (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G}
    (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) {x : G}
    (hxK : x ∈ centralizer (K : Set G))
    (hxX : x ∈ centralizer ((⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G) : Set G))
    (hxT₀ : x ∈ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G)) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1) : x ∈ T ⊓ centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hAX', -, -, -, -, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  by_contra hx
  have hex : ∃ j : ℕ, x ^ 2 ^ j ∈ T₀ := ⟨n, by rw [hxn]; exact one_mem _⟩
  classical
  set j := Nat.find hex with hj
  have hj0 : j ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hj, h0, pow_zero, pow_one] at this
    exact hx this
  set y := x ^ 2 ^ (j - 1) with hy
  have hyT₀ : y ∉ T₀ := Nat.find_min hex (by omega)
  have hy2 : y ^ 2 ∈ T₀ := by
    have h1 : y ^ 2 = x ^ 2 ^ j := by
      rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
    rw [h1]
    exact Nat.find_spec hex
  have hyK : y ∈ centralizer (K : Set G) := pow_mem hxK _
  have hyX : y ∈ centralizer ((⁅u3X₀ L K, u3X₀ L K⁆ : Subgroup G) : Set G) := pow_mem hxX _
  have hyN₀ : y ∈ normalizer (T₀ : Set G) := pow_mem hxT₀ _
  have hyn : y ^ 2 ^ n = 1 := by
    rw [hy, ← pow_mul, mul_comm, pow_mul, hxn, one_pow]
  have hyM : y ∈ normalizer (L : Set G) := h3.normalizer_T₀_le hyN₀
  have hyA : y ∈ centralizer (gmsA L T : Set G) := Subgroup.centralizer_le hAX' hyX
  have hyT₁ := h3.normalizer_inf_centralizer_le_normalizer_T₁ hf e (mem_inf.mpr ⟨hyM, hyA⟩)
  by_cases hLC : y ∈ L ⊔ centralizer (L : Set G)
  · have hyC := h3.mem_centralizer_of_mem_sup hf e hKL hKo hKH hLC hyK hyX hyT₁ hyn
    apply hyT₀
    have hy2' : IsPGroup 2 (zpowers y) := by
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyn)
      exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])
    have hsyl := h3.isSylowOf_T₀
    have hsup := hy2'.to_sup_of_normal_right' hsyl.isPGroup ((zpowers_le).mpr hyN₀)
    have heq := hsyl.eq_of_le le_sup_right (sup_le ((zpowers_le).mpr hyC) hsyl.le) hsup
    have hmem : y ∈ zpowers y ⊔ (T ⊓ centralizer (L : Set G)) := mem_sup_left (mem_zpowers y)
    rw [heq] at hmem
    exact hmem
  · exact h3.false_of_not_mem_sup hf e hKL hKo hKH hyM hyT₁ hyA hyK hyn hLC (mem_inf.mp hy2).2

theorem isSylowOf_T₀_centralizerPre
    (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f) (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G}
    (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    IsSylowOf 2 (T ⊓ centralizer (L : Set G)) (u3X₀CentralizerPre L K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hZX', -, ⟨eX'⟩⟩ := u3K_facts h3 hf e hKL hKo hKH
  set G₁ := centralizer (K : Set G)
  set O := standardComponentOddCore G₁
  set π := QuotientGroup.mk' O
  set OG : Subgroup G := O.map G₁.subtype
  set T₀ := T ⊓ centralizer (L : Set G) with hT₀def
  set X₀ := u3X₀ L K with hX₀def
  set X₀' : Subgroup G := ⁅X₀, X₀⁆ with hX₀'def
  set Ŷ := u3X₀CentralizerPre L K
  have hX₀L : X₀ ≤ L := by
    show ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆ ≤ L
    exact (commutator_le.mpr fun x hx y hy =>
      mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)).trans inf_le_left
  have hX₀G₁ : X₀ ≤ G₁ := by
    refine (commutator_le).mpr fun x hx y hy => ?_
    exact mul_mem (mul_mem (mul_mem (mem_inf.mp hx).2 (mem_inf.mp hy).2)
      (inv_mem (mem_inf.mp hx).2)) (inv_mem (mem_inf.mp hy).2)
  have hX₀'X₀ : X₀' ≤ X₀ := commutator_le.mpr fun x hx y hy =>
    mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hT₀G₁ : T₀ ≤ G₁ := inf_le_right.trans (Subgroup.centralizer_le hKL)
  have hT₀Ŷ : T₀ ≤ Ŷ := by
    intro t ht
    refine ⟨⟨t, hT₀G₁ ht⟩, ?_, rfl⟩
    show π ⟨t, hT₀G₁ ht⟩ ∈ u3X₀CentralizerC L K
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp (mem_inf.mp ht).2 _ (hX₀L hx))
  have hG₁N : G₁ ≤ normalizer (OG : Set G) := by
    have h := Subgroup.le_normalizer_map (H := O) G₁.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  have hOGo : Odd (Nat.card OG) := by
    rw [Subgroup.card_map_of_injective G₁.subtype_injective]
    exact odd_card_standardComponentOddCore'
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    have hc : 4 ≤ (Finset.univ : Finset (GaloisField 2 f)).card := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
      exact le_trans (by norm_num) (Nat.pow_le_pow_right two_pos hf)
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hc
    exact ⟨s, hs⟩
  have hYs : IsSimpleGroup (rankTwoQuot X₀') := by
    have := u3_isSimpleGroup_SL2 (GaloisField 2 f) h4
    exact eX'.isSimpleGroup
  have hYe : Even (Nat.card (rankTwoQuot X₀')) := by
    rw [Nat.card_congr eX'.toEquiv]
    exact u3_even_card_SL2 _
  have hperf := h3.commutator_commutator_u3X₀ hf e hKL hKo hKH
  have hT₀2 : IsPGroup 2 (T₀.subgroupOf Ŷ) := h3.isSylowOf_T₀.isPGroup.comap_subtype
  obtain ⟨P, hP⟩ := hT₀2.exists_le_sylow
  set S : Subgroup G := (P : Subgroup Ŷ).map Ŷ.subtype with hSdef
  have hSsyl : IsSylowOf 2 S Ŷ := ⟨P, rfl⟩
  have hT₀S : T₀ ≤ S := fun t ht => ⟨⟨t, hT₀Ŷ ht⟩, hP (mem_subgroupOf.mpr ht), rfl⟩
  suffices hST₀ : S ≤ T₀ by
    have heq : T₀ = S := le_antisymm hT₀S hST₀
    rw [heq]
    exact hSsyl
  by_contra hST₀
  obtain ⟨x, hxS, hxN, hxT₀⟩ := exists_mem_normalizer_of_lt hSsyl.isPGroup hT₀S hST₀
  obtain ⟨x₁, hx₁, hx₁e⟩ := hSsyl.le hxS
  have hxG₁ : x ∈ G₁ := hx₁e ▸ x₁.2
  obtain ⟨n, hn⟩ := hSsyl.isPGroup ⟨x, hxS⟩
  have hxn : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxM : x ∈ normalizer (L : Set G) := h3.normalizer_T₀_le hxN
  have hxX'N : x ∈ normalizer (X₀' : Set G) := (mem_normalizer_u3X₀ hxM hxG₁).2
  have hxX' : x ∈ centralizer (X₀' : Set G) := by
    refine mem_centralizer_of_commutator_mem_center hperf hxX'N fun p hp q hq => ?_
    have hpG₁ : p ∈ G₁ := hX₀G₁ (hX₀'X₀ hp)
    have hO : x * p * x⁻¹ * p⁻¹ ∈ OG := by
      have h1 : π x₁ * π ⟨p, hpG₁⟩ = π ⟨p, hpG₁⟩ * π x₁ :=
        ((mem_centralizer_iff.mp hx₁) _ ⟨⟨p, hpG₁⟩, hX₀'X₀ hp, rfl⟩).symm
      have h2 : π (x₁ * ⟨p, hpG₁⟩ * x₁⁻¹ * (⟨p, hpG₁⟩ : G₁)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
        group
      refine ⟨_, (QuotientGroup.eq_one_iff _).mp h2, ?_⟩
      rw [← hx₁e]
      rfl
    have hX : x * p * x⁻¹ * p⁻¹ ∈ X₀' :=
      mul_mem ((mem_normalizer_iff.mp hxX'N p).mp hp) (inv_mem hp)
    have hZ' := mem_center_of_mem_of_odd ((hX₀'X₀.trans hX₀G₁).trans hG₁N) hOGo hYs hYe
      (y := ⟨_, hX⟩) hO
    exact (congrArg Subtype.val ((mem_center_iff.mp hZ') ⟨q, hq⟩)).symm
  exact hxT₀ (h3.mem_T₀_of_mem_normalizer hf e hKL hKo hKH hxG₁ hxX' hxN hxn)

end Sec3

end CFSG.ComponentClassification.GMS78
