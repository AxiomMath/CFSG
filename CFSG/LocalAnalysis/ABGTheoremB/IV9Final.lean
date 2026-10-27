module

public import CFSG.LocalAnalysis.ABGTheoremB.IV9Defs
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G]

private theorem mem_of_mul_self_mem_of_odd {K : Subgroup G} {y : G} (hy : Odd (orderOf y))
    (h : y * y ∈ K) : y ∈ K := by
  obtain ⟨m, hm⟩ := hy
  have : y = (y * y) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [this]
  exact K.pow_mem h _

private theorem odd_card_of_isPGroup' [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup G} (hX : IsPGroup r X) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

private theorem odd_orderOf_of_mem {X : Subgroup G} (hX : Odd (Nat.card X)) {y : G} (hy : y ∈ X) :
    Odd (orderOf y) :=
  hX.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hy)

private theorem eq_one_of_fixed_inverted {t y : G} (hy : Odd (orderOf y))
    (hinv : t * y * t⁻¹ = y⁻¹) (hfix : t * y * t⁻¹ = y) : y = 1 := by
  have hyy : y * y ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot]
    calc y * y = y⁻¹ * y := by rw [← hinv, hfix]
      _ = 1 := inv_mul_cancel y
  exact (Subgroup.mem_bot).mp (mem_of_mul_self_mem_of_odd hy hyy)

private theorem le_normalizer_closure_of_conj_mem' {A : Subgroup G} {s : Set G}
    (h : ∀ a ∈ A, ∀ y ∈ s, a * y * a⁻¹ ∈ s) :
    A ≤ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  have key : ∀ a ∈ A, ∀ y ∈ Subgroup.closure s, a * y * a⁻¹ ∈ Subgroup.closure s := by
    intro a ha y hy
    have hle : Subgroup.closure s ≤ (Subgroup.closure s).comap (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro z hz
      exact Subgroup.subset_closure (h a ha z hz)
    exact hle hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

private theorem mem_normalizer_of_conj_mem' [Finite G] {K : Subgroup G} {x : G}
    (h : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private theorem isKleinFour_of_subgroupOf {T H : Subgroup G} (hTH : T ≤ H)
    (h : IsKleinFour (T.subgroupOf H)) : IsKleinFour T := by
  set e := Subgroup.subgroupOfEquivOfLe hTH
  exact ⟨by rw [← Nat.card_congr e.toEquiv]; exact h.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact h.exponent_two⟩

private theorem exists_zpow_eq_zpow_of_isCyclic' {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q]
    {p : ℕ} [Fact p.Prime] (hQ : IsPGroup p Q) {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ m n : ℤ, a ^ m = b ^ n ∧ a ^ m ≠ 1 := by
  have hdvd : ∀ c : Q, c ≠ 1 → p ∣ Nat.card (Subgroup.zpowers c) := by
    intro c hc
    rcases (hQ.to_subgroup (Subgroup.zpowers c)).card_eq_or_dvd with h | h
    · exfalso
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h
      exact hc h
    · exact h
  obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers a) p (hdvd a ha)
  obtain ⟨b', hb'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers b) p (hdvd b hb)
  have heq : Subgroup.zpowers (a' : Q) = Subgroup.zpowers (b' : Q) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_coe, Subgroup.orderOf_coe, ha', hb']
  have hmem : (a' : Q) ∈ Subgroup.zpowers (b' : Q) := heq ▸ Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a'.2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b'.2
  refine ⟨m, n * j, ?_, ?_⟩
  · rw [hm, zpow_mul, hn, hj]
  · rw [hm]
    intro h
    have : orderOf (a' : Q) = 1 := by rw [h, orderOf_one]
    rw [Subgroup.orderOf_coe, ha'] at this
    exact (Fact.out : p.Prime).one_lt.ne' this

private theorem false_of_isCyclic_mod' [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {F O : Subgroup G} (hF : IsPGroup r F) (hFO : F ≤ Subgroup.normalizer (O : Set G))
    (hcyc : ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ O) {s : G}
    (hsO : s ∈ Subgroup.normalizer (O : Set G)) {a b : G} (haF : a ∈ F) (hbF : b ∈ F)
    (has : s * a * s⁻¹ = a) (hbs : s * b * s⁻¹ = b⁻¹) (haO : a ∉ O) (hbO : b ∉ O) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hN : (O.subgroupOf F).Normal :=
    ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hFO g.2) n).mp hn⟩
  have hQp : IsPGroup r (F ⧸ O.subgroupOf F) := (hF.to_quotient (O.subgroupOf F))
  obtain ⟨g, hgF, hg⟩ := hcyc
  have hQc : IsCyclic (F ⧸ O.subgroupOf F) := by
    refine isCyclic_iff_exists_zpowers_eq_top.mpr ⟨((⟨g, hgF⟩ : F) : F ⧸ O.subgroupOf F), ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨f, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hg f f.2
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow, eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hk
  have hne : ∀ y : F, (y : G) ∉ O → (y : F ⧸ O.subgroupOf F) ≠ 1 := by
    intro y hy h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hy h
  obtain ⟨m, n, hmn, hm1⟩ := exists_zpow_eq_zpow_of_isCyclic' hQp
    (hne ⟨a, haF⟩ haO) (hne ⟨b, hbF⟩ hbO)
  rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_zpow, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hmn
  have hmO : a ^ m ∉ O := by
    intro h
    apply hm1
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using h
  have h1 : (a ^ m)⁻¹ * b ^ n ∈ O := by simpa using hmn
  have hsa : s * a ^ m * s⁻¹ = a ^ m := by rw [← conj_zpow, has]
  have hsb : s * b ^ n * s⁻¹ = (b ^ n)⁻¹ := by rw [← conj_zpow, hbs, inv_zpow]
  have h2 : (a ^ m)⁻¹ * (b ^ n)⁻¹ ∈ O := by
    have := (Subgroup.mem_normalizer_iff.mp hsO _).mp h1
    have e : s * ((a ^ m)⁻¹ * b ^ n) * s⁻¹ = (s * a ^ m * s⁻¹)⁻¹ * (s * b ^ n * s⁻¹) := by group
    rwa [e, hsa, hsb] at this
  have h3 : b ^ n * b ^ n ∈ O := by
    have := O.mul_mem (O.inv_mem h2) h1
    simpa [mul_assoc] using this
  have hodd : Odd (orderOf (b ^ n)) :=
    odd_orderOf_of_mem (odd_card_of_isPGroup' hr hr2 hF) (F.zpow_mem hbF n)
  have h4 : b ^ n ∈ O := mem_of_mul_self_mem_of_odd hodd h3
  apply hmO
  have := O.mul_mem h4 (O.inv_mem h1)
  simpa using this

private theorem le_zpowers_of_inf_eq_bot {F O : Subgroup G}
    (hcyc : ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ O) (hFO : F ⊓ O = ⊥) :
    ∃ g ∈ F, F ≤ Subgroup.zpowers g := by
  obtain ⟨g, hgF, hg⟩ := hcyc
  refine ⟨g, hgF, fun f hf => ?_⟩
  obtain ⟨k, hk⟩ := hg f hf
  have hmem : f⁻¹ * g ^ k ∈ F ⊓ O := ⟨F.mul_mem (F.inv_mem hf) (F.zpow_mem hgF k), hk⟩
  rw [hFO, Subgroup.mem_bot] at hmem
  have : f = g ^ k := by
    calc f = f * (f⁻¹ * g ^ k) := by rw [hmem, mul_one]
      _ = g ^ k := by group
  rw [this]
  exact Subgroup.zpow_mem_zpowers g k

private theorem card_eq_one_or_of_le_zpowers {F : Subgroup G} {g : G} {r : ℕ} (hr : r.Prime)
    (hF : F ≤ Subgroup.zpowers g) (hg : g ^ r = 1) : Nat.card F = 1 ∨ Nat.card F = r := by
  have h1 : Nat.card F ∣ Nat.card (Subgroup.zpowers g) := Subgroup.card_dvd_of_le hF
  rw [Nat.card_zpowers] at h1
  exact (Nat.dvd_prime hr).mp (h1.trans (orderOf_dvd_of_pow_eq_one hg))

private theorem normalizer_le_normalizer_centralizer' (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    have hy' : g⁻¹ * y * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
      simpa using this
    have h := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * y := by group
  · intro hc y hy
    have hy' : g * y * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    have h := hc _ hy'
    calc y * c = g⁻¹ * ((g * y * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = c * y := by group

private theorem exists_of_three_dvd_automizerIndex' {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer' T)
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, ?_, ?_⟩
  · have : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hg
    have : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem three_dvd_automizerIndex_of' {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    {g : K} (hg : g ∈ Subgroup.normalizer (T : Set K))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set K))
    (h1 : g ∉ Subgroup.centralizer (T : Set K)) : 3 ∣ automizerIndex T := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer' T)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h3
    · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h1
  have := orderOf_dvd_natCard ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt)
  rw [hord, ← Subgroup.index_eq_card] at this
  exact this

private theorem mem_normalizer_subgroupOf_iff' {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem mem_centralizer_subgroupOf_iff' {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem exists_of_three_dvd_automizerIndex_subgroupOf' [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex' h
  refine ⟨g, g.2, (mem_normalizer_subgroupOf_iff' hTH).mp hgN, ?_, ?_⟩
  · simpa using (mem_centralizer_subgroupOf_iff' hTH).mp hg3
  · exact fun h' => hg1 ((mem_centralizer_subgroupOf_iff' hTH).mpr h')

private theorem three_dvd_automizerIndex_subgroupOf_of' [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) {g : G} (hgH : g ∈ H) (hg : g ∈ Subgroup.normalizer (T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G)) (h1 : g ∉ Subgroup.centralizer (T : Set G)) :
    3 ∣ automizerIndex (T.subgroupOf H) :=
  three_dvd_automizerIndex_of' (g := ⟨g, hgH⟩) ((mem_normalizer_subgroupOf_iff' hTH).mpr hg)
    ((mem_centralizer_subgroupOf_iff' hTH).mpr (by simpa using h3))
    (fun h' => h1 ((mem_centralizer_subgroupOf_iff' hTH).mp h'))

private theorem three_dvd_automizerIndex_mono' [Finite G] {T H₁ H₂ : Subgroup G}
    (hTH : T ≤ H₁) (hH : H₁ ≤ H₂) (h : 3 ∣ automizerIndex (T.subgroupOf H₁)) :
    3 ∣ automizerIndex (T.subgroupOf H₂) := by
  obtain ⟨g, hg, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex_subgroupOf' hTH h
  exact three_dvd_automizerIndex_subgroupOf_of' (hTH.trans hH) (hH hg) hgN hg3 hg1

private theorem conj_mem_of_mem_normalizer' {X : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ X) : g * x * g⁻¹ ∈ X :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

private theorem exists_conj_eq_of_three {T : Subgroup G} [IsKleinFour T] {g : G}
    (hgN : g ∈ Subgroup.normalizer (T : Set G)) (hg3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G))
    (hg1 : g ∉ Subgroup.centralizer (T : Set G)) {a b : G} (ha : a ∈ T) (hb : b ∈ T)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ h : G, (h = 1 ∨ h = g ∨ h = g * g) ∧ h * a * h⁻¹ = b := by
  set φ : G → G := fun t => g * t * g⁻¹ with hφ
  have hφT : ∀ t ∈ T, φ t ∈ T := fun t ht => conj_mem_of_mem_normalizer' hgN ht
  have hφ1 : ∀ t, φ t = 1 → t = 1 := by
    intro t h
    simp only [hφ] at h
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hφinj : ∀ s t, φ s = φ t → s = t := by
    intro s t h
    simp only [hφ] at h
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = t := by rw [h]; group
  have hφmul : ∀ s t, φ (s * t) = φ s * φ t := by
    intro s t
    simp only [hφ]
    group
  have hφ3 : ∀ t ∈ T, φ (φ (φ t)) = t := by
    intro t ht
    have hc := Subgroup.mem_centralizer_iff.mp hg3 t ht
    simp only [hφ]
    calc g * (g * (g * t * g⁻¹) * g⁻¹) * g⁻¹ = g ^ 3 * t * (g ^ 3)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      _ = t := by rw [← hc]; group
  have hfix : ∀ c ∈ T, c ≠ 1 → φ c ≠ c := by
    intro c hc hc1 hφc
    apply hg1
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    by_contra hne
    have hφt : φ t ≠ t := by
      intro h
      apply hne
      simp only [hφ] at h
      calc t * g = g * t * g⁻¹ * g := by rw [h]
        _ = g * t := by group
    have ht1 : t ≠ 1 := by
      rintro rfl
      exact hne (by group)
    have htc : t ≠ c := by
      rintro rfl
      exact hφt hφc
    have hφt1 : φ t ≠ 1 := fun h => ht1 (hφ1 t h)
    have hφtc : φ t ≠ c := fun h => htc (hφinj t c (h.trans hφc.symm))
    have hφt' : φ t = c * t :=
      kleinFour_eq_mul hc ht (hφT t ht) hc1 ht1 htc.symm hφt1 hφtc hφt
    have h2 : φ (φ t) = t := by
      rw [hφt', hφmul, hφc, hφt', ← mul_assoc, kleinFour_mul_self hc, one_mul]
    have h3 := hφ3 t ht
    rw [h2] at h3
    exact hφt h3
  have hφa := hfix a ha ha1
  have hφa1 : φ a ≠ 1 := fun h => ha1 (hφ1 a h)
  have hφφa1 : φ (φ a) ≠ 1 := fun h => hφa1 (hφ1 _ h)
  have hφφa : φ (φ a) ≠ φ a := hfix (φ a) (hφT a ha) hφa1
  have hφφa' : φ (φ a) ≠ a := by
    intro h
    have h3 := hφ3 a ha
    rw [h] at h3
    exact hφa h3
  by_cases h1 : b = a
  · exact ⟨1, Or.inl rfl, by rw [h1]; group⟩
  by_cases h2 : b = φ a
  · exact ⟨g, Or.inr (Or.inl rfl), h2.symm⟩
  have h3 : b = φ (φ a) := by
    have e1 : b = a * φ a := kleinFour_eq_mul ha (hφT a ha) hb ha1 hφa1 hφa.symm hb1 h1 h2
    have e2 : φ (φ a) = a * φ a := kleinFour_eq_mul ha (hφT a ha) (hφT _ (hφT a ha)) ha1 hφa1
      hφa.symm hφφa1 hφφa' hφφa
    rw [e1, e2]
  refine ⟨g * g, Or.inr (Or.inr rfl), ?_⟩
  rw [h3]
  simp only [hφ]
  group

private theorem conj_mem_fourInverted_of_comm {Y : Subgroup G} {t s u k : G}
    (htY : t ∈ Subgroup.normalizer (Y : Set G)) (hts : t * s = s * t) (htu : t * u = u * t)
    (hk : k ∈ fourInverted Y s u) : t * k * t⁻¹ ∈ fourInverted Y s u := by
  obtain ⟨hkY, hks, hku⟩ := hk
  refine ⟨conj_mem_of_mem_normalizer' htY hkY, ?_, ?_⟩
  · calc s * (t * k * t⁻¹) * s⁻¹ = t * (s * k * s⁻¹) * t⁻¹ := by
          rw [show s * (t * k * t⁻¹) * s⁻¹ = (s * t) * k * (s * t)⁻¹ by group, ← hts]
          group
      _ = t * k * t⁻¹ := by rw [hks]
  · calc u * (t * k * t⁻¹) * u⁻¹ = t * (u * k * u⁻¹) * t⁻¹ := by
          rw [show u * (t * k * t⁻¹) * u⁻¹ = (u * t) * k * (u * t)⁻¹ by group, ← htu]
          group
      _ = (t * k * t⁻¹)⁻¹ := by rw [hku]; group

private theorem mem_centralizer_of_decomp {Y K₀ : Subgroup G} {S₁ S₂ S₃ : Set G} {a : G}
    (hdec : (Y : Set G) = (K₀ : Set G) * S₁ * S₂ * S₃) (h₀ : ∀ k ∈ K₀, Commute a k)
    (h₁ : ∀ k ∈ S₁, Commute a k) (h₂ : ∀ k ∈ S₂, Commute a k) (h₃ : ∀ k ∈ S₃, Commute a k) :
    a ∈ Subgroup.centralizer (Y : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy' : y ∈ (Y : Set G) := hy
  rw [hdec] at hy'
  obtain ⟨v, hv, k₃, hk₃, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨w, hw, k₂, hk₂, rfl⟩ := Set.mem_mul.mp hv
  obtain ⟨k₀, hk₀, k₁, hk₁, rfl⟩ := Set.mem_mul.mp hw
  have hc : Commute a (k₀ * k₁ * k₂ * k₃) :=
    (((h₀ k₀ hk₀).mul_right (h₁ k₁ hk₁)).mul_right (h₂ k₂ hk₂)).mul_right (h₃ k₃ hk₃)
  exact hc.eq.symm

private theorem eq_one_of_mem_of_coprime {r : ℕ} (hr : r.Prime) {V : Subgroup G}
    (hV : IsPGroup r V) {v : G} (hv : v ∈ V) {n : ℕ} (hn : Nat.Coprime r n) (hvn : v ^ n = 1) :
    v = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hV ⟨v, hv⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : orderOf v ∣ n := orderOf_dvd_of_pow_eq_one hvn
  have h2 : Nat.Coprime (orderOf v) n := by
    rw [hk]
    exact Nat.Coprime.pow_left k hn
  have : orderOf v = 1 := Nat.Coprime.eq_one_of_dvd h2 h1
  exact orderOf_eq_one_iff.mp this

private theorem commutator_eq_self_of_inverted {F T : Subgroup G} (hF : Odd (Nat.card F))
    (hTF : T ≤ Subgroup.normalizer (F : Set G))
    (hinv : ∀ f ∈ F, ∃ c ∈ T, c * f * c⁻¹ = f⁻¹) : ⁅F, T⁆ = F := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro f hf t ht
    rw [commutatorElement_def]
    have h1 : t * f⁻¹ * t⁻¹ ∈ F := conj_mem_of_mem_normalizer' (hTF ht) (F.inv_mem hf)
    have e : f * t * f⁻¹ * t⁻¹ = f * (t * f⁻¹ * t⁻¹) := by group
    rw [e]
    exact F.mul_mem hf h1
  · intro f hf
    obtain ⟨c, hc, hcf⟩ := hinv f hf
    have hmem := Subgroup.commutator_mem_commutator hf hc
    rw [commutatorElement_def] at hmem
    have e : f * c * f⁻¹ * c⁻¹ = f * f := by
      calc f * c * f⁻¹ * c⁻¹ = f * (c * f * c⁻¹)⁻¹ := by group
        _ = f * f := by rw [hcf, inv_inv]
    rw [e] at hmem
    exact mem_of_mul_self_mem_of_odd (odd_orderOf_of_mem hF hf) hmem

private theorem inverts_of_fixed_eq_bot {F : Subgroup G} (hF : Odd (Nat.card F)) {t : G}
    (ht : orderOf t = 2) (htF : t ∈ Subgroup.normalizer (F : Set G))
    (hfix : F ⊓ Subgroup.centralizer {t} = ⊥) : ∀ f ∈ F, t * f * t⁻¹ = f⁻¹ := by
  intro f hf
  have hdec := (odd_fixed_mul_inverted hF ht htF).1
  have hf' : f ∈ (F : Set G) := hf
  rw [hdec, hfix] at hf'
  obtain ⟨c, hc, i, hi, rfl⟩ := Set.mem_mul.mp hf'
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hc
  rw [hc, one_mul]
  exact (OddInversion.mem_invertedSet.mp hi).2

private theorem commutator_inv_inv_of_central {V : Subgroup G} {a b : G}
    (hab : ⁅a, b⁆ ∈ V) (hV : ∀ v ∈ V, ∀ g : G, g ∈ ({a, b} : Set G) → v * g = g * v) :
    ⁅a⁻¹, b⁻¹⁆ = ⁅a, b⁆ := by
  have ha := hV _ hab a (Set.mem_insert _ _)
  have hb := hV _ hab b (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  obtain ⟨c, hc⟩ : ∃ c, c = ⁅a, b⁆ := ⟨_, rfl⟩
  rw [← hc] at ha hb ⊢
  rw [commutatorElement_def] at hc ⊢
  have e1 : a * b = c * b * a := by rw [hc]; group
  calc a⁻¹ * b⁻¹ * a⁻¹⁻¹ * b⁻¹⁻¹ = a⁻¹ * b⁻¹ * (a * b) := by group
    _ = a⁻¹ * b⁻¹ * (c * b * a) := by rw [e1]
    _ = a⁻¹ * (b⁻¹ * (c * b)) * a := by group
    _ = a⁻¹ * (b⁻¹ * (b * c)) * a := by rw [hb]
    _ = a⁻¹ * (c * a) := by group
    _ = a⁻¹ * (a * c) := by rw [ha]
    _ = c := by group

private theorem normalizer_inf_le_sup_of_inverts {U V : Subgroup G} (hU : Odd (Nat.card U))
    {t : G} (ht : orderOf t = 2) (htU : t ∈ Subgroup.normalizer (U : Set G))
    (hUU : ⁅U, U⁆ ≤ V) (hVU : V ≤ U) (hVc : V ≤ Subgroup.centralizer (U : Set G))
    (hcen : U ⊓ Subgroup.centralizer (U : Set G) ≤ V) (hVinv : ∀ v ∈ V, t * v * t⁻¹ = v⁻¹)
    (hAV : (U ⊓ Subgroup.centralizer {t}) ⊓ V = ⊥) :
    U ⊓ Subgroup.normalizer ((U ⊓ Subgroup.centralizer {t} : Subgroup G) : Set G) ≤
      (U ⊓ Subgroup.centralizer {t}) ⊔ V := by
  set A : Subgroup G := U ⊓ Subgroup.centralizer {t} with hA
  have hdec := (odd_fixed_mul_inverted hU ht htU).1
  have hcomm : ∀ v ∈ V, ∀ g ∈ U, v * g = g * v := fun v hv g hg =>
    (Subgroup.mem_centralizer_iff.mp (hVc hv) g hg).symm
  intro n hn
  obtain ⟨hnU, hnN⟩ := hn
  have hn' : n ∈ (U : Set G) := hnU
  rw [hdec] at hn'
  obtain ⟨a, ha, i, hi, rfl⟩ := Set.mem_mul.mp hn'
  obtain ⟨hiU, hit⟩ := OddInversion.mem_invertedSet.mp hi
  have hiN : i ∈ Subgroup.normalizer (A : Set G) := by
    have : i = a⁻¹ * (a * i) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer ha)) hnN
  have hiC : i ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ (U : Set G) := hu
    rw [hdec] at hu'
    obtain ⟨b, hb, j, hj, rfl⟩ := Set.mem_mul.mp hu'
    obtain ⟨hjU, hjt⟩ := OddInversion.mem_invertedSet.mp hj
    have hib : i * b = b * i := by
      have h1 : ⁅i, b⁆ ∈ A := by
        rw [commutatorElement_def]
        exact A.mul_mem (conj_mem_of_mem_normalizer' hiN hb) (A.inv_mem hb)
      have h2 : ⁅i, b⁆ ∈ V := hUU (Subgroup.commutator_mem_commutator hiU hb.1)
      have h3 : ⁅i, b⁆ = 1 := by
        have : ⁅i, b⁆ ∈ A ⊓ V := ⟨h1, h2⟩
        rwa [hAV, Subgroup.mem_bot] at this
      rw [commutatorElement_def] at h3
      calc i * b = (i * b * i⁻¹ * b⁻¹) * b * i := by group
        _ = b * i := by rw [h3, one_mul]
    have hij : i * j = j * i := by
      have hV' : ⁅i, j⁆ ∈ V := hUU (Subgroup.commutator_mem_commutator hiU hjU)
      have h1 : t * ⁅i, j⁆ * t⁻¹ = ⁅i, j⁆⁻¹ := hVinv _ hV'
      have h2 : t * ⁅i, j⁆ * t⁻¹ = ⁅i⁻¹, j⁻¹⁆ := by
        have e : t * ⁅i, j⁆ * t⁻¹ = ⁅t * i * t⁻¹, t * j * t⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, hit, hjt]
      have h3 : ⁅i⁻¹, j⁻¹⁆ = ⁅i, j⁆ := by
        apply commutator_inv_inv_of_central hV'
        intro v hv g hg
        rcases hg with rfl | rfl
        · exact hcomm v hv _ hiU
        · exact hcomm v hv _ hjU
      have h4 : ⁅i, j⁆ = 1 := by
        apply eq_one_of_fixed_inverted (odd_orderOf_of_mem hU (hVU hV')) h1
        rw [h2, h3]
      rw [commutatorElement_def] at h4
      calc i * j = (i * j * i⁻¹ * j⁻¹) * j * i := by group
        _ = j * i := by rw [h4, one_mul]
    calc b * j * i = b * (i * j) := by rw [mul_assoc, ← hij]
      _ = i * (b * j) := by rw [← mul_assoc, ← hib, mul_assoc]
  have hiV : i ∈ V := hcen ⟨hiU, hiC⟩
  exact Subgroup.mul_mem_sup ha hiV

private def invertedSubgroup (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (t : G) :
    Subgroup G where
  carrier := {u | u ∈ U ∧ t * u * t⁻¹ = u⁻¹}
  mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨U.mul_mem ha hb, by
    calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
      _ = (a * b)⁻¹ := by rw [mul_inv_rev]; exact hU _ (U.inv_mem ha) _ (U.inv_mem hb)⟩
  one_mem' := ⟨U.one_mem, by group⟩
  inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨U.inv_mem ha, by
    rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group, ha']⟩

private theorem mem_invertedSubgroup {U : Subgroup G} {hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a}
    {t u : G} : u ∈ invertedSubgroup U hU t ↔ u ∈ U ∧ t * u * t⁻¹ = u⁻¹ :=
  Iff.rfl

private def trivOn (K U V : Subgroup G) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {k | k ∈ K ∧ ∀ u ∈ U, k * u * k⁻¹ * u⁻¹ ∈ V}
  mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨K.mul_mem ha hb, fun u hu => by
    have e : a * b * u * (a * b)⁻¹ * u⁻¹ =
        a * (b * u * b⁻¹ * u⁻¹) * a⁻¹ * (a * u * a⁻¹ * u⁻¹) := by group
    rw [e]
    exact V.mul_mem (conj_mem_of_mem_normalizer' (hKV ha) (hb' u hu)) (ha' u hu)⟩
  one_mem' := ⟨K.one_mem, fun u _ => by simp⟩
  inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨K.inv_mem ha, fun u hu => by
    have hu' : a⁻¹ * u * a ∈ U := by
      have := conj_mem_of_mem_normalizer' (hKU (K.inv_mem ha)) hu
      simpa using this
    have h := V.inv_mem (ha' _ hu')
    have e : (a * (a⁻¹ * u * a) * a⁻¹ * (a⁻¹ * u * a)⁻¹)⁻¹ = a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ := by group
    rw [e] at h
    exact h⟩

private theorem le_normalizer_trivOn {K U V : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.normalizer ((trivOn K U V hKU hKV : Subgroup G) : Set G) := by
  have key : ∀ g ∈ K, ∀ k ∈ trivOn K U V hKU hKV, g * k * g⁻¹ ∈ trivOn K U V hKU hKV := by
    intro g hg k hk
    obtain ⟨hkK, hk'⟩ := hk
    refine ⟨K.mul_mem (K.mul_mem hg hkK) (K.inv_mem hg), fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g ∈ U := by
      have := conj_mem_of_mem_normalizer' (hKU (K.inv_mem hg)) hu
      simpa using this
    have h := conj_mem_of_mem_normalizer' (hKV hg) (hk' _ hu')
    have e : g * (k * (g⁻¹ * u * g) * k⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ =
        g * k * g⁻¹ * u * (g * k * g⁻¹)⁻¹ * u⁻¹ := by group
    rwa [e] at h
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨key g hg k, fun hk => ?_⟩
  have := key g⁻¹ (K.inv_mem hg) _ hk
  simpa [mul_assoc] using this

private theorem isSolvable_solvRadIn' [Finite G] (H : Subgroup G) :
    Group.IsSolvable (solvRadIn H) := by
  have : Group.IsSolvable (CFSG.solvableRadical H) := solvableRadical_isSolvable
  exact Group.isSolvable_of_surjective
    (f := ((CFSG.solvableRadical H).equivMapOfInjective H.subtype
      H.subtype_injective).toMonoidHom)
    ((CFSG.solvableRadical H).equivMapOfInjective H.subtype H.subtype_injective).surjective

private theorem le_solvRadIn' {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hK : Group.IsSolvable K) :
    K ≤ solvRadIn H := by
  have hnormal : (K.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hsolv : Group.IsSolvable (K.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).injective
  have hle : K.subgroupOf H ≤ CFSG.solvableRadical H := le_sSup ⟨hnormal, hsolv⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

private theorem le_normalizer_solvRadIn (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((solvRadIn H : Subgroup G) : Set G) :=
  have : (CFSG.solvableRadical H).Normal := solvableRadical_normal
  le_normalizer_map_subtype H (CFSG.solvableRadical H)

private theorem le_solvRadIn_of_pow_mem [Finite G] {r : ℕ} (hr : r.Prime) {H Z : Subgroup G}
    (hZH : Z ≤ H) (hHZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hpow : ∀ g ∈ Z, g ^ r ∈ solvRadIn H) : Z ≤ solvRadIn H := by
  have : Fact r.Prime := ⟨hr⟩
  apply le_solvRadIn' hZH hHZ
  set S := solvRadIn H with hS
  have hHS := le_normalizer_solvRadIn H
  set N : Subgroup Z := (Z ⊓ S).subgroupOf Z with hN
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnZ, hnS⟩ := hn
    refine ⟨Z.mul_mem (Z.mul_mem g.2 hnZ) (Z.inv_mem g.2), ?_⟩
    exact conj_mem_of_mem_normalizer' (hHS (hZH g.2)) hnS
  have hNs : Group.IsSolvable N := by
    have hle : Z ⊓ S ≤ S := inf_le_right
    have : Group.IsSolvable S := isSolvable_solvRadIn' H
    have : Group.IsSolvable (Z ⊓ S : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ⊓ S ≤ Z)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ⊓ S ≤ Z)).injective
  have hQp : IsPGroup r (Z ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf]
    exact ⟨Z.pow_mem g.2 r, by simpa using hpow g g.2⟩
  have : Group.IsNilpotent (Z ⧸ N) := hQp.isNilpotent
  exact Group.isSolvable_of_subgroup_quotient N

private theorem eq_one_of_isPGroup_two_of_mem_odd' [Finite G] {A B : Subgroup G}
    (hA : IsPGroup 2 A) (hB : Odd (Nat.card B)) {a : G} (haA : a ∈ A) (haB : a ∈ B) : a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨a, haA⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf a ∣ Nat.card B := Subgroup.orderOf_dvd_natCard B haB
  rw [hk] at hdvd
  have hodd : Odd (2 ^ k) := hB.of_dvd_nat hdvd
  have hk0 : k = 0 := by
    by_contra h
    exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' h).mpr even_two)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

private theorem pow_mem_centralizer_of_stabilizes {r : ℕ} {U V : Subgroup G} {g : G}
    (hgU : ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ V) (hgV : g ∈ Subgroup.centralizer (V : Set G))
    (hV : ∀ v ∈ V, v ^ r = 1) : g ^ r ∈ Subgroup.centralizer (U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨v, hv⟩ : ∃ v, v = g * u * g⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hvV : v ∈ V := hv ▸ hgU u hu
  have hgv : g * v * g⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp hgV v hvV
    rw [← this]
    group
  have hgu : g * u * g⁻¹ = v * u := by rw [hv]; group
  have key : ∀ n : ℕ, g ^ n * u * (g ^ n)⁻¹ = v ^ n * u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hvn : g * v ^ n * g⁻¹ = v ^ n := by rw [← conj_pow, hgv]
      calc g ^ (n + 1) * u * (g ^ (n + 1))⁻¹ = g * (g ^ n * u * (g ^ n)⁻¹) * g⁻¹ := by group
        _ = g * (v ^ n * u) * g⁻¹ := by rw [ih]
        _ = (g * v ^ n * g⁻¹) * (g * u * g⁻¹) := by group
        _ = v ^ (n + 1) * u := by rw [hvn, hgu, pow_succ]; simp only [mul_assoc]
  have h := key r
  rw [hV v hvV, one_mul] at h
  calc u * g ^ r = g ^ r * u * (g ^ r)⁻¹ * g ^ r := by rw [h]
    _ = g ^ r * u := by group

private theorem mem_map_conj_iff' {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hw
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem isSylowOf_map_conj' [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) K := by
  refine isSylowOf_of_card (fun y hy => ?_) ?_
  · rw [mem_map_conj_iff'] at hy
    have h := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * y * g)).mp (hP.le hy)
    rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at h
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]

private theorem exists_mem_normalizer_mul_of_isSylowOf' [Finite G] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup G} (hP : IsSylowOf p P K) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), ∃ k ∈ K, x = n * k := by
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj (isSylowOf_map_conj' hP (inv_mem hx))
  refine ⟨x * k, ?_, k⁻¹, inv_mem hk, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h := hconj (k * y * k⁻¹)
  rw [mem_map_conj_iff', inv_inv, show k⁻¹ * (k * y * k⁻¹) * k = y by group] at h
  rw [show x * k * y * (x * k)⁻¹ = x * (k * y * k⁻¹) * x⁻¹ by group]
  exact h.symm

private theorem conj_commutator_of_involution {t u : G} (ht : t * t = 1) :
    t * (t * u * t⁻¹ * u⁻¹) * t⁻¹ = (t * u * t⁻¹ * u⁻¹)⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : t * (t * u * t⁻¹ * u⁻¹) * t⁻¹ = (t * t) * u * t⁻¹ * u⁻¹ * t⁻¹ := by group
  have e2 : (t * u * t⁻¹ * u⁻¹)⁻¹ = u * t * u⁻¹ * t⁻¹ := by group
  rw [e1, e2, ht, one_mul, hti]

private theorem mem_centralizer_map_conj_iff {X : Subgroup G} {b c : G} (hbc : c * b = b * c) :
    b ∈ Subgroup.centralizer ((X.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) ↔
      b ∈ Subgroup.centralizer (X : Set G) := by
  have hbc' : c⁻¹ * b = b * c⁻¹ := by
    calc c⁻¹ * b = c⁻¹ * (b * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * b) * c⁻¹ := by rw [hbc]
      _ = b * c⁻¹ := by group
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff] at h ⊢
    intro y hy
    have hz : c * y * c⁻¹ ∈ X.map (MulAut.conj c).toMonoidHom := by
      rw [mem_map_conj_iff']
      simpa [mul_assoc] using hy
    have h1 := h _ hz
    calc y * b = c⁻¹ * (c * y * c⁻¹ * b) * c := by
          rw [show c * y * c⁻¹ * b = c * y * (c⁻¹ * b) by group, hbc']
          group
      _ = c⁻¹ * (b * (c * y * c⁻¹)) * c := by rw [h1]
      _ = b * y := by
          rw [show b * (c * y * c⁻¹) = (b * c) * y * c⁻¹ by group, ← hbc]
          group
  · intro h
    rw [Subgroup.mem_centralizer_iff] at h ⊢
    intro z hz
    rw [SetLike.mem_coe, mem_map_conj_iff'] at hz
    have h1 := h _ hz
    calc z * b = c * (c⁻¹ * z * c * b) * c⁻¹ := by
          rw [show c⁻¹ * z * c * b = c⁻¹ * z * (c * b) by group, hbc]
          group
      _ = c * (b * (c⁻¹ * z * c)) * c⁻¹ := by rw [h1]
      _ = b * z := by
          rw [show b * (c⁻¹ * z * c) = (b * c⁻¹) * z * c by group, ← hbc']
          group

private theorem conj_mem_centralizer_map_conj {X : Subgroup G} {a h : G}
    (ha : a ∈ Subgroup.centralizer (X : Set G)) :
    h * a * h⁻¹ ∈
      Subgroup.centralizer ((X.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro z hz
  rw [SetLike.mem_coe, mem_map_conj_iff'] at hz
  have h1 := ha _ hz
  calc z * (h * a * h⁻¹) = h * ((h⁻¹ * z * h) * a) * h⁻¹ := by group
    _ = h * (a * (h⁻¹ * z * h)) * h⁻¹ := by rw [h1]
    _ = h * a * h⁻¹ * z := by group

private theorem le_normalizer_map_conj [Finite G] {T X : Subgroup G} {h : G}
    (hT : h ∈ Subgroup.normalizer (T : Set G)) (hTX : T ≤ Subgroup.normalizer (X : Set G)) :
    T ≤ Subgroup.normalizer ((X.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  intro t ht
  apply mem_normalizer_of_conj_mem'
  intro z hz
  rw [mem_map_conj_iff'] at hz ⊢
  have ht' : h⁻¹ * t * h ∈ T := by
    have := conj_mem_of_mem_normalizer' (Subgroup.inv_mem _ hT) ht
    simpa using this
  have h1 := conj_mem_of_mem_normalizer' (hTX ht') hz
  have e : h⁻¹ * t * h * (h⁻¹ * z * h) * (h⁻¹ * t * h)⁻¹ = h⁻¹ * (t * z * t⁻¹) * h := by group
  rwa [e] at h1

private def commLeftHom (U : Subgroup G)
    (hc : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, ⁅a, b⁆ * c = c * ⁅a, b⁆) {y : G} (hy : y ∈ U) : U →* G where
  toFun x := ⁅(x : G), y⁆
  map_one' := by simp [commutatorElement_def]
  map_mul' x z := by
    have hk : ⁅(z : G), y⁆ * x = x * ⁅(z : G), y⁆ := hc z z.2 y hy x x.2
    have hxy : ⁅(x : G), y⁆ ∈ U := by
      rw [commutatorElement_def]
      exact U.mul_mem (U.mul_mem (U.mul_mem x.2 hy) (U.inv_mem x.2)) (U.inv_mem hy)
    have hk' : ⁅(z : G), y⁆ * ⁅(x : G), y⁆ = ⁅(x : G), y⁆ * ⁅(z : G), y⁆ :=
      hc z z.2 y hy _ hxy
    simp only [Subgroup.coe_mul]
    simp only [commutatorElement_def] at hk hk' ⊢
    calc (x : G) * z * y * ((x : G) * z)⁻¹ * y⁻¹ =
        x * (z * y * (z : G)⁻¹ * y⁻¹) * y * (x : G)⁻¹ * y⁻¹ := by group
      _ = (z * y * (z : G)⁻¹ * y⁻¹) * x * y * (x : G)⁻¹ * y⁻¹ := by rw [← hk]
      _ = (z * y * (z : G)⁻¹ * y⁻¹) * (x * y * (x : G)⁻¹ * y⁻¹) := by group
      _ = (x * y * (x : G)⁻¹ * y⁻¹) * (z * y * (z : G)⁻¹ * y⁻¹) := hk'

private theorem commLeftHom_apply {U : Subgroup G}
    {hc : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, ⁅a, b⁆ * c = c * ⁅a, b⁆} {y : G} {hy : y ∈ U} (x : U) :
    commLeftHom U hc hy x = ⁅(x : G), y⁆ :=
  rfl

private theorem exists_zpow_eq_of_card_prime {V : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hV : Nat.card V = r) {c : G} (hc : c ∈ V) (hc1 : c ≠ 1) :
    ∀ v ∈ V, ∃ k : ℤ, c ^ k = v := by
  have : Fact r.Prime := ⟨hr⟩
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact hr.ne_zero)
  have hle : Subgroup.zpowers c ≤ V := Subgroup.zpowers_le.mpr hc
  have hord : orderOf c = r := by
    have h := Subgroup.orderOf_dvd_natCard V hc
    rw [hV] at h
    rcases (Nat.dvd_prime hr).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have heq : Subgroup.zpowers c = V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hV])
  intro v hv
  rw [← heq] at hv
  exact Subgroup.mem_zpowers_iff.mp hv

private theorem exists_le_closure_pair_sup {U V A : Subgroup G} {r : ℕ} (hr : r.Prime)
    (hUUV : ⁅U, U⁆ = V) (hVc : V = U ⊓ Subgroup.centralizer (U : Set G)) (hcard : Nat.card V = r)
    (hAU : A ≤ U) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAV : A ⊓ V = ⊥)
    {p₀ : G} (hp₀A : p₀ ∈ A) (hp₀1 : p₀ ≠ 1)
    (hC : ∀ w ∈ U, w * p₀ = p₀ * w → w ∈ A ⊔ V) :
    ∃ a ∈ U, ∃ b ∈ U, U ≤ Subgroup.closure {a, b} ⊔ ⁅U, U⁆ := by
  have hVC : V ≤ Subgroup.centralizer (U : Set G) := hVc ▸ inf_le_right
  have hcomm_mem : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ V := fun a ha b hb =>
    hUUV ▸ Subgroup.commutator_mem_commutator ha hb
  have hcent : ∀ a ∈ U, ∀ b ∈ U, ∀ c ∈ U, ⁅a, b⁆ * c = c * ⁅a, b⁆ := fun a ha b hb c hc =>
    (Subgroup.mem_centralizer_iff.mp (hVC (hcomm_mem a ha b hb)) c hc).symm
  have hp₀U : p₀ ∈ U := hAU hp₀A
  have hp₀C : p₀ ∉ Subgroup.centralizer (U : Set G) := by
    intro h
    have : p₀ ∈ A ⊓ V := ⟨hp₀A, hVc ▸ ⟨hp₀U, h⟩⟩
    rw [hAV, Subgroup.mem_bot] at this
    exact hp₀1 this
  obtain ⟨f₀, hf₀U, hf₀⟩ : ∃ f₀ ∈ U, f₀ * p₀ ≠ p₀ * f₀ := by
    by_contra hcon
    push Not at hcon
    exact hp₀C (Subgroup.mem_centralizer_iff.mpr fun h hh => hcon h hh)
  have hne : ∀ {a b : G}, a * b ≠ b * a → ⁅a, b⁆ ≠ 1 := by
    intro a b hab h
    rw [commutatorElement_def] at h
    apply hab
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [h, one_mul]
  have heq1 : ∀ {a b : G}, ⁅a, b⁆ = 1 → a * b = b * a := by
    intro a b h
    rw [commutatorElement_def] at h
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [h, one_mul]
  set φ := commLeftHom U hcent hp₀U with hφ
  set ψ := commLeftHom U hcent hf₀U with hψ
  have hdec : ∀ u ∈ U, ∃ k : ℤ, (f₀ ^ k)⁻¹ * u ∈ A ⊔ V := by
    intro u hu
    obtain ⟨k, hk⟩ := exists_zpow_eq_of_card_prime hr hcard (hcomm_mem f₀ hf₀U p₀ hp₀U)
      (hne hf₀) _ (hcomm_mem u hu p₀ hp₀U)
    refine ⟨k, hC _ (U.mul_mem (U.inv_mem (U.zpow_mem hf₀U k)) hu) (heq1 ?_)⟩
    have h1 : φ (⟨f₀, hf₀U⟩ ^ k)⁻¹ * φ ⟨u, hu⟩ = 1 := by
      rw [map_inv, map_zpow, commLeftHom_apply, commLeftHom_apply, hk, inv_mul_cancel]
    rw [← map_mul, commLeftHom_apply] at h1
    simpa using h1
  have hAp : A ≤ Subgroup.zpowers p₀ := by
    intro a ha
    have hc0 : ⁅p₀, f₀⁆ ≠ 1 := hne fun h => hf₀ h.symm
    obtain ⟨k, hk⟩ := exists_zpow_eq_of_card_prime hr hcard (hcomm_mem p₀ hp₀U f₀ hf₀U) hc0 _
      (hcomm_mem a (hAU ha) f₀ hf₀U)
    set b := (p₀ ^ k)⁻¹ * a with hb
    have hbA : b ∈ A := A.mul_mem (A.inv_mem (A.zpow_mem hp₀A k)) ha
    have hbf : b * f₀ = f₀ * b := by
      apply heq1
      have h1 : ψ (⟨p₀, hp₀U⟩ ^ k)⁻¹ * ψ ⟨a, hAU ha⟩ = 1 := by
        rw [map_inv, map_zpow, commLeftHom_apply, commLeftHom_apply, hk, inv_mul_cancel]
      rw [← map_mul, commLeftHom_apply] at h1
      simpa [hb] using h1
    have hbC : b ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k', hk'⟩ := hdec u hu
      have hAVb : A ⊔ V ≤ Subgroup.centralizer ({b} : Set G) := by
        refine sup_le (fun a' ha' => ?_) (fun v hv => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hAab a' ha' b hbA)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr
            (Subgroup.mem_centralizer_iff.mp (hVC hv) b (hAU hbA)).symm
      have hw := Subgroup.mem_centralizer_singleton_iff.mp (hAVb hk')
      have hf : (f₀ ^ k') * b = b * (f₀ ^ k') := by
        have : Commute f₀ b := hbf.symm
        exact (this.zpow_left k').eq
      have e1 : u = f₀ ^ k' * ((f₀ ^ k')⁻¹ * u) := by group
      rw [e1, mul_assoc, hw, ← mul_assoc, hf, mul_assoc]
    have hbV : b ∈ A ⊓ V := ⟨hbA, hVc ▸ ⟨hAU hbA, hbC⟩⟩
    rw [hAV, Subgroup.mem_bot] at hbV
    have : a = p₀ ^ k := by
      calc a = p₀ ^ k * b := by rw [hb]; group
        _ = p₀ ^ k := by rw [hbV, mul_one]
    rw [this]
    exact Subgroup.zpow_mem_zpowers p₀ k
  refine ⟨f₀, hf₀U, p₀, hp₀U, fun u hu => ?_⟩
  obtain ⟨k, hk⟩ := hdec u hu
  have hAVn : A ≤ Subgroup.normalizer (V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hVC hv) a (hAU ha)).symm)
  have hk' : (f₀ ^ k)⁻¹ * u ∈ ((A ⊔ V : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A V hAVn] at hk'
  obtain ⟨a, ha, v, hv, hav⟩ := Set.mem_mul.mp hk'
  have hf₀mem : f₀ ∈ Subgroup.closure ({f₀, p₀} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hp₀mem : p₀ ∈ Subgroup.closure ({f₀, p₀} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have haC : a ∈ Subgroup.closure ({f₀, p₀} : Set G) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hAp ha)
    rw [← hj]
    exact Subgroup.zpow_mem _ hp₀mem j
  have e1 : u = (f₀ ^ k * a) * v := by
    rw [mul_assoc, hav]
    group
  rw [e1, hUUV]
  exact Subgroup.mul_mem_sup (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hf₀mem k) haC) hv

private theorem mem_normalizer_closure_of_conj_mem [Finite G] {s : Set G} {g : G}
    (h : ∀ y ∈ s, g * y * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  apply mem_normalizer_of_conj_mem'
  intro k hk
  have hle : Subgroup.closure s ≤ (Subgroup.closure s).comap (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    exact h y hy
  exact hle hk

private theorem eq_one_or_eq_of_mem_zpowers' [Finite G] {a y : G} (ha : orderOf a = 2)
    (hy : y ∈ Subgroup.zpowers a) : y = 1 ∨ y = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, ha] at hy
  simp only [Finset.mem_image, Finset.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  interval_cases k <;> simp

private theorem isKleinFour_closure_pair' [Finite G] {a t : G} (ha : orderOf a = 2)
    (ht : orderOf t = 2) (hcomm : a * t = t * a) (hne : a ≠ t) :
    IsKleinFour (Subgroup.closure ({a, t} : Set G)) := by
  have hcl : Subgroup.closure ({a, t} : Set G) = Subgroup.zpowers a ⊔ Subgroup.zpowers t := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left hcomm k)).eq
  have hbot : Subgroup.zpowers a ⊓ Subgroup.zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    rcases eq_one_or_eq_of_mem_zpowers' ha hy.1 with h | rfl
    · exact h
    · rcases eq_one_or_eq_of_mem_zpowers' ht hy.2 with h | h
      · exact h
      · exact absurd h hne
  have hcard : Nat.card (Subgroup.closure ({a, t} : Set G)) = 4 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnorm
    rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha, ht] at h
    rw [hcl, h]
  have hsq : ∀ y : Subgroup.closure ({a, t} : Set G), y ^ 2 = 1 := by
    rintro ⟨y, hy⟩
    apply Subtype.ext
    have hy' : y ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers t : Subgroup G) : Set G) := by
      rw [← hcl]
      exact hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hy'
    obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_mul.mp hy'
    have hbc : Commute b c := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact (Commute.zpow_left hcomm i).zpow_right j
    have hb2 : b ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers' ha hb with rfl | rfl
      · exact one_pow 2
      · rw [← ha]; exact pow_orderOf_eq_one _
    have hc2 : c ^ 2 = 1 := by
      rcases eq_one_or_eq_of_mem_zpowers' ht hc with rfl | rfl
      · exact one_pow 2
      · rw [← ht]; exact pow_orderOf_eq_one _
    change (b * c) ^ 2 = 1
    rw [hbc.mul_pow, hb2, hc2, one_mul]
  refine ⟨hcard, ?_⟩
  have hdvd : Monoid.exponent (Subgroup.closure ({a, t} : Set G)) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exfalso
    have hsub := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : Subgroup.closure ({a, t} : Set G))
    omega
  · exact h

private def commImage (U : Subgroup G) (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {v : G}
    (hv : v ∈ Subgroup.normalizer (U : Set G)) : Subgroup G where
  carrier := {c | ∃ w ∈ U, v * w * v⁻¹ * w⁻¹ = c}
  mul_mem' := fun {c₁ c₂} ⟨w₁, hw₁, h₁⟩ ⟨w₂, hw₂, h₂⟩ => ⟨w₁ * w₂, U.mul_mem hw₁ hw₂, by
    rw [← h₁, ← h₂]
    have hb : v * w₂ * v⁻¹ ∈ U := conj_mem_of_mem_normalizer' hv hw₂
    have hcomm := hU _ (U.mul_mem hb (U.inv_mem hw₂)) _ (U.inv_mem hw₁)
    calc v * (w₁ * w₂) * v⁻¹ * (w₁ * w₂)⁻¹ =
        v * w₁ * v⁻¹ * ((v * w₂ * v⁻¹ * w₂⁻¹) * w₁⁻¹) := by group
      _ = v * w₁ * v⁻¹ * (w₁⁻¹ * (v * w₂ * v⁻¹ * w₂⁻¹)) := by rw [hcomm]
      _ = v * w₁ * v⁻¹ * w₁⁻¹ * (v * w₂ * v⁻¹ * w₂⁻¹) := by group⟩
  one_mem' := ⟨1, U.one_mem, by group⟩
  inv_mem' := fun {c} ⟨w, hw, h⟩ => ⟨w⁻¹, U.inv_mem hw, by
    rw [← h]
    have hb : v * w⁻¹ * v⁻¹ ∈ U := conj_mem_of_mem_normalizer' hv (U.inv_mem hw)
    have hcomm := hU _ hw _ hb
    calc v * w⁻¹ * v⁻¹ * w⁻¹⁻¹ = (v * w⁻¹ * v⁻¹) * w := by group
      _ = w * (v * w⁻¹ * v⁻¹) := hcomm.symm
      _ = (v * w * v⁻¹ * w⁻¹)⁻¹ := by group⟩

private theorem commImage_le {U : Subgroup G} {hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a} {v : G}
    {hv : v ∈ Subgroup.normalizer (U : Set G)} : commImage U hU hv ≤ U := by
  rintro c ⟨w, hw, rfl⟩
  exact U.mul_mem (conj_mem_of_mem_normalizer' hv hw) (U.inv_mem hw)

private theorem eq_one_of_conj_commutator {r n : ℕ} (hr : r.Prime) {U : Subgroup G}
    (hU : IsPGroup r U) {v w : G} (hw : w ∈ U) (hcop : Nat.Coprime r n)
    (hvn : v ^ n ∈ Subgroup.centralizer (U : Set G)) (heU : v * w * v⁻¹ * w⁻¹ ∈ U)
    (he : v * (v * w * v⁻¹ * w⁻¹) * v⁻¹ = v * w * v⁻¹ * w⁻¹) : v * w * v⁻¹ * w⁻¹ = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, c = v * w * v⁻¹ * w⁻¹ := ⟨_, rfl⟩
  rw [← hc] at heU he ⊢
  have hvw : v * w * v⁻¹ = c * w := by rw [hc]; group
  have key : ∀ m : ℕ, v ^ m * w * (v ^ m)⁻¹ = c ^ m * w := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hcm : v * c ^ m * v⁻¹ = c ^ m := by rw [← conj_pow, he]
      calc v ^ (m + 1) * w * (v ^ (m + 1))⁻¹ = v * (v ^ m * w * (v ^ m)⁻¹) * v⁻¹ := by group
        _ = v * (c ^ m * w) * v⁻¹ := by rw [ih]
        _ = (v * c ^ m * v⁻¹) * (v * w * v⁻¹) := by group
        _ = c ^ (m + 1) * w := by rw [hcm, hvw, pow_succ]; simp only [mul_assoc]
  have h := key n
  have hfix : v ^ n * w * (v ^ n)⁻¹ = w := by
    have := Subgroup.mem_centralizer_iff.mp hvn w hw
    rw [← this]
    group
  rw [hfix] at h
  have hcn : c ^ n = 1 := by
    have := congrArg (· * w⁻¹) h
    simpa using this.symm
  exact eq_one_of_mem_of_coprime hr hU heU hcop hcn

private theorem commImage_le_commutator [Finite G] {r n : ℕ} (hr : r.Prime) {U : Subgroup G}
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUr : IsPGroup r U) {v : G}
    (hv : v ∈ Subgroup.normalizer (U : Set G)) (hcop : Nat.Coprime r n)
    (hvn : v ^ n ∈ Subgroup.centralizer (U : Set G)) :
    commImage U hU hv ≤ ⁅commImage U hU hv, Subgroup.zpowers v⁆ := by
  set U₁ := commImage U hU hv with hU₁
  have hU₁U : U₁ ≤ U := commImage_le
  have hφmem : ∀ c ∈ U₁, v * c * v⁻¹ * c⁻¹ ∈ U₁ := fun c hc => ⟨c, hU₁U hc, rfl⟩
  let φ : U₁ → U₁ := fun c => ⟨v * c * v⁻¹ * (c : G)⁻¹, hφmem c c.2⟩
  have hinj : Function.Injective φ := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h' : v * c * v⁻¹ * c⁻¹ = v * c' * v⁻¹ * c'⁻¹ := congrArg Subtype.val h
    have hcU := hU₁U hc
    have hc'U := hU₁U hc'
    set e := c * c'⁻¹ with he
    have heU₁ : e ∈ U₁ := U₁.mul_mem hc (U₁.inv_mem hc')
    have hve : v * e * v⁻¹ = e := by
      have h2 : v * c' * v⁻¹ ∈ U := conj_mem_of_mem_normalizer' hv hc'U
      calc v * e * v⁻¹ = (v * c * v⁻¹) * (v * c' * v⁻¹)⁻¹ := by rw [he]; group
        _ = (v * c * v⁻¹ * c⁻¹) * c * (v * c' * v⁻¹)⁻¹ := by group
        _ = (v * c' * v⁻¹ * c'⁻¹) * c * (v * c' * v⁻¹)⁻¹ := by rw [h']
        _ = e := by
            rw [he]
            have hw : c'⁻¹ * c * (v * c' * v⁻¹)⁻¹ = (v * c' * v⁻¹)⁻¹ * c * c'⁻¹ := by
              have hcomm1 := hU _ hcU _ (U.inv_mem h2)
              have hcomm2 := hU _ (U.inv_mem hc'U) _ (U.inv_mem h2)
              calc c'⁻¹ * c * (v * c' * v⁻¹)⁻¹ = c'⁻¹ * (c * (v * c' * v⁻¹)⁻¹) := by group
                _ = c'⁻¹ * ((v * c' * v⁻¹)⁻¹ * c) := by rw [hcomm1]
                _ = (c'⁻¹ * (v * c' * v⁻¹)⁻¹) * c := by group
                _ = ((v * c' * v⁻¹)⁻¹ * c'⁻¹) * c := by rw [hcomm2]
                _ = (v * c' * v⁻¹)⁻¹ * (c'⁻¹ * c) := by group
                _ = (v * c' * v⁻¹)⁻¹ * (c * c'⁻¹) := by rw [hU _ (U.inv_mem hc'U) _ hcU]
                _ = (v * c' * v⁻¹)⁻¹ * c * c'⁻¹ := by group
            calc v * c' * v⁻¹ * c'⁻¹ * c * (v * c' * v⁻¹)⁻¹ =
                (v * c' * v⁻¹) * (c'⁻¹ * c * (v * c' * v⁻¹)⁻¹) := by group
              _ = (v * c' * v⁻¹) * ((v * c' * v⁻¹)⁻¹ * c * c'⁻¹) := by rw [hw]
              _ = c * c'⁻¹ := by group
    have heU : e ∈ U := hU₁U heU₁
    obtain ⟨w, hw, hwe⟩ := heU₁
    have he1 : e = 1 := by
      rw [← hwe] at hve heU ⊢
      exact eq_one_of_conj_commutator hr hUr hw hcop hvn heU hve
    have : c = c' := by
      calc c = e * c' := by rw [he]; group
        _ = c' := by rw [he1, one_mul]
    exact Subtype.ext this
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro c hc
  obtain ⟨⟨c', hc'⟩, h⟩ := hsurj ⟨c, hc⟩
  have h' : v * c' * v⁻¹ * c'⁻¹ = c := congrArg Subtype.val h
  rw [Subgroup.commutator_comm, ← h']
  have := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers v) hc'
  rwa [commutatorElement_def] at this

private theorem mem_normalizer_sup_zpowers [Finite G] {A : Subgroup G} {g y : G}
    (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hg : y * g * y⁻¹ ∈ A ⊔ Subgroup.zpowers g) :
    y ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem'
  have hle : A ⊔ Subgroup.zpowers g ≤
      (A ⊔ Subgroup.zpowers g).comap (MulAut.conj y).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact (le_sup_left : A ≤ A ⊔ Subgroup.zpowers g) (hA a ha)
    · exact hg
  exact fun k hk => hle hk

private theorem pow_mul_pow_mem {O : Subgroup G} {c f : G} (hc : c ∈ O)
    (hf : f ∈ Subgroup.normalizer (O : Set G)) : ∀ j : ℕ, (c * f⁻¹) ^ j * f ^ j ∈ O := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (f ^ j)⁻¹ * c * ((f ^ j)⁻¹)⁻¹ ∈ O :=
      conj_mem_of_mem_normalizer' (Subgroup.inv_mem _ (Subgroup.pow_mem _ hf j)) hc
    have e : (c * f⁻¹) ^ (j + 1) * f ^ (j + 1) =
        ((c * f⁻¹) ^ j * f ^ j) * ((f ^ j)⁻¹ * c * ((f ^ j)⁻¹)⁻¹) := by
      rw [pow_succ, pow_succ']
      group
    rw [e]
    exact O.mul_mem ih h1

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem isPGroup_two_T' (hσ : σ.IsValid) : IsPGroup 2 σ.T :=
  σ.S.isPGroup'.to_le (σ.T_le_S hσ)

private theorem T_comm (hσ : σ.IsValid) {s t : G} (hs : s ∈ σ.T) (ht : t ∈ σ.T) :
    s * t = t * s :=
  Subgroup.mem_centralizer_iff.mp (σ.T_le_C hσ ht) s hs

omit [Finite G] in
private theorem T_le_of_mem {X : Subgroup G} (hx : σ.x ∈ X) (hx₂ : σ.x₂ ∈ X) : σ.T ≤ X := by
  rw [T, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact hx
  · exact hx₂

omit [Finite G] in
private theorem T_le_centralizer_of_mem {X : Subgroup G}
    (hx : σ.x ∈ Subgroup.centralizer (X : Set G))
    (hx₂ : σ.x₂ ∈ Subgroup.centralizer (X : Set G)) :
    σ.T ≤ Subgroup.centralizer (X : Set G) :=
  σ.T_le_of_mem hx hx₂

private theorem x_ne_one' (hσ : σ.IsValid) : σ.x ≠ 1 := by
  intro h
  have := hσ.x_order
  rw [h, orderOf_one] at this
  norm_num at this

private theorem x₂_ne_one' (hσ : σ.IsValid) : σ.x₂ ≠ 1 := by
  intro h
  have := hσ.x₂_order
  rw [h, orderOf_one] at this
  norm_num at this

private theorem x_inv' (hσ : σ.IsValid) : σ.x⁻¹ = σ.x :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one])

private theorem x₂_inv' (hσ : σ.IsValid) : σ.x₂⁻¹ = σ.x₂ :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one])

omit [Finite G] in
private theorem centerOf_eq_map_center' (X : Subgroup G) :
    centerOf X = (Subgroup.center X).map X.subtype := by
  ext g
  constructor
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hgX⟩, Subgroup.mem_center_iff.mpr fun h => Subtype.ext ?_, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp hgC) h h.2)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

private theorem centerOf_D_le_zpowers_x' (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hqd : σ.height = 1) : centerOf σ.D ≤ Subgroup.zpowers σ.x := by
  rw [← hII.center_S_eq_center_D]
  have hsyl := hσ.sylow
  rw [hqd] at hsyl
  obtain ⟨n, hn, hSD⟩ : ∃ n, 4 ≤ n ∧ ∀ S : Sylow 2 G,
      Nonempty (CFSG.Open.SemidihedralGroup n ≃* S) := by
    rcases hsyl with ⟨-, n, hn, hSD⟩ | ⟨h2, -⟩
    · exact ⟨n, hn, hSD⟩
    · omega
  obtain ⟨f⟩ := hSD σ.S
  have hcard : Nat.card (centerOf (σ.S : Subgroup G)) = 2 := by
    rw [centerOf_eq_map_center', Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      ← Nat.card_congr (Subgroup.centerCongr f).toEquiv, CFSG.Semidihedral.center_card n hn]
  have hle : Subgroup.zpowers σ.x ≤ centerOf (σ.S : Subgroup G) :=
    Subgroup.zpowers_le.mpr hσ.x_mem_center
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hσ.x_order])
  exact heq.symm.le

variable {σ}

private theorem T_le_centralizer_of_not_constrained' (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    {H : Subgroup G} (hTH : σ.T ≤ H)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn H) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r H (CFSG.oddCore H))
    (h1 : ¬ PConstrainedWithin r H (CFSG.oddCore H)) {Y : Subgroup G}
    (hYO : Y ≤ oddCoreIn H) (hY : IsPGroup r Y) (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) :
    σ.T ≤ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨X, hX, hYX, hTX⟩ := exists_isSylowOf_normalized_ge_of_odd hr
    (σ.isPGroup_two_T' hσ) (hTH.trans (le_normalizer_oddCoreIn H)) (odd_card_oddCoreIn H) hYO
    hY hTY
  have hTC : σ.T ≤ Subgroup.centralizer (X : Set G) := by
    by_contra hC
    exact h1 (h92 ⟨X, hX, hTX, hC⟩)
  exact hTC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hYX))

private theorem exists_mem_T_mem_centralizer (hσ : σ.IsValid) [IsKleinFour σ.T] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    {H : Subgroup G} (hDH : σ.D ≤ H) (hHw : IsDGroupWrt (σ.T.subgroupOf H))
    (hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn H → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G))
    {Y : Subgroup G} (hYH : Y ≤ H) (hY : IsPGroup r Y)
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ a ∈ σ.T, a ≠ 1 ∧ a ∈ Subgroup.centralizer (Y : Set G) := by
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hHO : H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  have hYodd : Odd (Nat.card Y) := odd_card_of_isPGroup' hr hr2 hY
  have horder : ∀ y ∈ Y, Odd (orderOf y) := fun y hy => odd_orderOf_of_mem hYodd hy
  set x := σ.x
  set x₂ := σ.x₂
  have hx := σ.x_mem_T
  have hx₂ := σ.x₂_mem_T
  have hx1 := σ.x_ne_one' hσ
  have hx₂1 := σ.x₂_ne_one' hσ
  have hxx₂ := hσ.x_ne_x₂
  have hx3 : x * x₂ ∈ σ.T := σ.T.mul_mem hx hx₂
  have hxinv : x⁻¹ = x := σ.x_inv' hσ
  set S₁ := fourInverted Y x x₂
  set S₂ := fourInverted Y x₂ x
  set S₃ := fourInverted Y (x * x₂) x
  have inv₁ : ∀ k ∈ S₁, x₂ * k * x₂⁻¹ = k⁻¹ ∧ (x * x₂) * k * (x * x₂)⁻¹ = k⁻¹ := by
    intro k hk
    refine ⟨hk.2.2, ?_⟩
    calc (x * x₂) * k * (x * x₂)⁻¹ = x * (x₂ * k * x₂⁻¹) * x⁻¹ := by group
      _ = (x * k * x⁻¹)⁻¹ := by rw [hk.2.2]; group
      _ = k⁻¹ := by rw [hk.2.1]
  have inv₂ : ∀ k ∈ S₂, x * k * x⁻¹ = k⁻¹ ∧ (x * x₂) * k * (x * x₂)⁻¹ = k⁻¹ := by
    intro k hk
    refine ⟨hk.2.2, ?_⟩
    calc (x * x₂) * k * (x * x₂)⁻¹ = x * (x₂ * k * x₂⁻¹) * x⁻¹ := by group
      _ = k⁻¹ := by rw [hk.2.1, hk.2.2]
  have inv₃ : ∀ k ∈ S₃, x * k * x⁻¹ = k⁻¹ ∧ x₂ * k * x₂⁻¹ = k⁻¹ := by
    intro k hk
    refine ⟨hk.2.2, ?_⟩
    have e : x₂ = x * (x * x₂) := by rw [← mul_assoc, ← pow_two, ← hσ.x_order,
      pow_orderOf_eq_one, one_mul]
    calc x₂ * k * x₂⁻¹ = x * ((x * x₂) * k * (x * x₂)⁻¹) * x⁻¹ := by
          conv_lhs => rw [e]
          group
      _ = k⁻¹ := by rw [hk.2.1, hk.2.2]
  have hZ : σ.T ≤ Subgroup.centralizer ((Y ⊓ oddCoreIn H : Subgroup G) : Set G) :=
    hcen _ inf_le_right (hY.to_le inf_le_left) fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hTY ht, hHO (hTH ht)⟩
  have hout : ∀ k ∈ Y, ∀ c ∈ σ.T, c * k * c⁻¹ = k⁻¹ → k ≠ 1 → k ∉ oddCoreIn H := by
    intro k hkY c hc hck hk1 hkO
    apply hk1
    refine eq_one_of_fixed_inverted (horder k hkY) hck ?_
    have := Subgroup.mem_centralizer_iff.mp (hZ hc) k ⟨hkY, hkO⟩
    rw [← this]
    group
  set S : Set G := S₁ ∪ S₂ ∪ S₃ with hS
  set Ys : Subgroup G := Subgroup.closure S with hYs
  have hSY : S ⊆ Y := Set.union_subset (Set.union_subset (fun k hk => hk.1) (fun k hk => hk.1))
    (fun k hk => hk.1)
  have hYsY : Ys ≤ Y := (Subgroup.closure_le Y).mpr hSY
  have hYsp : IsPGroup r Ys := hY.to_le hYsY
  have hYsodd : Odd (Nat.card Ys) := odd_card_of_isPGroup' hr hr2 hYsp
  have hTc : ∀ t ∈ σ.T, ∀ s ∈ σ.T, t * s = s * t := fun t ht s hs => σ.T_comm hσ ht hs
  have hconjS : ∀ t ∈ σ.T, ∀ k ∈ S, t * k * t⁻¹ ∈ S := by
    intro t ht k hk
    rcases hk with (hk | hk) | hk
    · exact Or.inl (Or.inl (conj_mem_fourInverted_of_comm (hTY ht) (hTc t ht x hx)
        (hTc t ht x₂ hx₂) hk))
    · exact Or.inl (Or.inr (conj_mem_fourInverted_of_comm (hTY ht) (hTc t ht x₂ hx₂)
        (hTc t ht x hx) hk))
    · exact Or.inr (conj_mem_fourInverted_of_comm (hTY ht) (hTc t ht _ hx3) (hTc t ht x hx) hk)
  have hTYs : σ.T ≤ Subgroup.normalizer (Ys : Set G) := le_normalizer_closure_of_conj_mem' hconjS
  have hYsT : ⁅Ys, σ.T⁆ = Ys := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro f hf t ht
      rw [commutatorElement_def]
      have h1 : t * f⁻¹ * t⁻¹ ∈ Ys := conj_mem_of_mem_normalizer' (hTYs ht) (Ys.inv_mem hf)
      have e : f * t * f⁻¹ * t⁻¹ = f * (t * f⁻¹ * t⁻¹) := by group
      rw [e]
      exact Ys.mul_mem hf h1
    · rw [Subgroup.closure_le]
      intro k hk
      have hkYs : k ∈ Ys := Subgroup.subset_closure hk
      have hsq : ∀ c ∈ σ.T, c * k * c⁻¹ = k⁻¹ → k ∈ ⁅Ys, σ.T⁆ := by
        intro c hc hck
        have hmem := Subgroup.commutator_mem_commutator hkYs hc
        rw [commutatorElement_def] at hmem
        have e : k * c * k⁻¹ * c⁻¹ = k * k := by
          calc k * c * k⁻¹ * c⁻¹ = k * (c * k * c⁻¹)⁻¹ := by group
            _ = k * k := by rw [hck, inv_inv]
        rw [e] at hmem
        exact mem_of_mul_self_mem_of_odd (horder k (hSY hk)) hmem
      rcases hk with (hk | hk) | hk
      · exact hsq x₂ hx₂ hk.2.2
      · exact hsq x hx hk.2.2
      · exact hsq x hx hk.2.2
  have hcyc := h_II54 H hDH hHw Ys (hYsY.trans hYH) hYsodd hTYs hYsT
  have hYsO : Ys ≤ Subgroup.normalizer (oddCoreIn H : Set G) := (hYsY.trans hYH).trans hHO
  have hpair : ∀ {s c : G}, s ∈ σ.T → c ∈ σ.T → ∀ {a b : G}, a ∈ S → b ∈ S →
      s * a * s⁻¹ = a → s * b * s⁻¹ = b⁻¹ → c * a * c⁻¹ = a⁻¹ → a ≠ 1 → b ≠ 1 → False := by
    intro s c hs hc a b ha hb hsa hsb hca ha1 hb1
    exact false_of_isCyclic_mod' hr hr2 hYsp hYsO hcyc (hHO (hTH hs))
      (Subgroup.subset_closure ha) (Subgroup.subset_closure hb) hsa hsb
      (hout a (hSY ha) c hc hca ha1) (hout b (hSY hb) s hs hsb hb1)
  obtain ⟨-, hdec⟩ := four_group_T_decomposition hYodd hTY hx hx₂ hx1 hx₂1 hxx₂
  have hK₀ : ∀ a ∈ σ.T, ∀ k ∈ Y ⊓ Subgroup.centralizer (σ.T : Set G), Commute a k :=
    fun a ha k hk => Subgroup.mem_centralizer_iff.mp hk.2 a ha
  have hfix : ∀ {a k : G}, a * k * a⁻¹ = k → Commute a k := fun {a k} h => by
    show a * k = k * a
    calc a * k = a * k * a⁻¹ * a := by group
      _ = k * a := by rw [h]
  have htriv : ∀ {a : G} {P : Set G}, (∀ k ∈ P, k = 1) → ∀ k ∈ P, Commute a k :=
    fun {a P} h k hk => by rw [h k hk]; exact Commute.one_right a
  by_cases h₁ : ∃ k ∈ S₁, k ≠ 1
  · obtain ⟨k₁, hk₁, hk₁1⟩ := h₁
    have t₂ : ∀ k ∈ S₂, k = 1 := fun k hk => by_contra fun hk1 =>
      hpair hx hx₂ (Or.inl (Or.inl hk₁)) (Or.inl (Or.inr hk)) hk₁.2.1 (inv₂ k hk).1
        (inv₁ k₁ hk₁).1 hk₁1 hk1
    have t₃ : ∀ k ∈ S₃, k = 1 := fun k hk => by_contra fun hk1 =>
      hpair hx hx₂ (Or.inl (Or.inl hk₁)) (Or.inr hk) hk₁.2.1 (inv₃ k hk).1
        (inv₁ k₁ hk₁).1 hk₁1 hk1
    exact ⟨x, hx, hx1, mem_centralizer_of_decomp hdec (hK₀ x hx) (fun k hk => hfix hk.2.1)
      (htriv t₂) (htriv t₃)⟩
  · have t₁ : ∀ k ∈ S₁, k = 1 := fun k hk => by_contra fun hk1 => h₁ ⟨k, hk, hk1⟩
    by_cases h₂ : ∃ k ∈ S₂, k ≠ 1
    · obtain ⟨k₂, hk₂, hk₂1⟩ := h₂
      have t₃ : ∀ k ∈ S₃, k = 1 := fun k hk => by_contra fun hk1 =>
        hpair hx₂ hx (Or.inl (Or.inr hk₂)) (Or.inr hk) hk₂.2.1 (inv₃ k hk).2
          (inv₂ k₂ hk₂).1 hk₂1 hk1
      exact ⟨x₂, hx₂, hx₂1, mem_centralizer_of_decomp hdec (hK₀ x₂ hx₂) (htriv t₁)
        (fun k hk => hfix hk.2.1) (htriv t₃)⟩
    · have t₂ : ∀ k ∈ S₂, k = 1 := fun k hk => by_contra fun hk1 => h₂ ⟨k, hk, hk1⟩
      refine ⟨x * x₂, hx3, fun h => hxx₂ ((eq_inv_of_mul_eq_one_right h).trans hxinv).symm,
        mem_centralizer_of_decomp hdec (hK₀ _ hx3) (htriv t₁) (htriv t₂)
          (fun k hk => hfix hk.2.1)⟩

section UV

variable {r : ℕ} (d : σ.IV7Data r) (e : IV9UV d)

private theorem T_le_K (hσ : σ.IsValid) : σ.T ≤ Subgroup.normalizer (d.R : Set G) :=
  (σ.T_le_D hσ).trans d.R_D

private theorem U_le_ON : e.U ≤ σ.ON :=
  e.U_le.trans d.R_sylow.le

private theorem U_le_N : e.U ≤ σ.N :=
  (U_le_ON d e).trans σ.ON_le_N

private theorem isPGroup_U : IsPGroup r e.U :=
  d.R_sylow.isPGroup.to_le e.U_le

private theorem x_mem_centralizer_U : σ.x ∈ Subgroup.centralizer (e.U : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (σ.mem_N_iff u).mp (U_le_N d e hu)

private theorem T_le_normalizer_U (hσ : σ.IsValid) : σ.T ≤ Subgroup.normalizer (e.U : Set G) :=
  (T_le_K d hσ).trans e.U_normal

private theorem T_le_normalizer_V (hσ : σ.IsValid) : σ.T ≤ Subgroup.normalizer (e.V : Set G) :=
  (T_le_K d hσ).trans e.V_normal

private theorem T_le_normalizer_P (hσ : σ.IsValid) : σ.T ≤ Subgroup.normalizer (d.P : Set G) :=
  (σ.T_le_D hσ).trans d.P_D

private theorem T_le_normalizer_PU (hσ : σ.IsValid) :
    σ.T ≤ Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨T_le_normalizer_P d hσ ht, T_le_normalizer_U d e hσ ht⟩

private theorem T_le_H₁ (hσ : σ.IsValid) : σ.T ≤ e.H₁ :=
  T_le_normalizer_PU d e hσ

private theorem P_le_centralizer_T : d.P ≤ Subgroup.centralizer (σ.T : Set G) :=
  d.P_sylow.le

private theorem C_inf_U_eq : σ.C ⊓ e.U = e.U ⊓ Subgroup.centralizer {σ.x₂} := by
  ext u
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨huC, huU⟩
    refine ⟨huU, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp huC σ.x₂ σ.x₂_mem_T).symm
  · rintro ⟨huU, hu⟩
    refine ⟨?_, huU⟩
    have hx : σ.x ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((σ.mem_N_iff u).mp (U_le_N d e huU)).symm
    have hx₂ : σ.x₂ ∈ Subgroup.centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hu).symm
    have hT := σ.T_le_of_mem hx hx₂
    rw [C, Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hT ht)

private theorem R_ne_bot (hr : σ.HypIV7 r) : d.R ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr.prime⟩
  intro h
  have hcard := d.R_sylow.card_eq
  rw [h, Subgroup.card_bot] at hcard
  have hpos := hr.prime.factorization_pos_of_dvd Nat.card_pos.ne' hr.dvd_ON
  exact (Nat.one_lt_pow hpos.ne' hr.prime.one_lt).ne' hcard.symm

private theorem R_le_oddCoreIn_K (hr : σ.HypIV7 r) :
    d.R ≤ oddCoreIn (Subgroup.normalizer (d.R : Set G)) :=
  le_oddCoreIn Subgroup.le_normalizer le_rfl
    (odd_card_of_isPGroup' hr.prime (σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON)
      d.R_sylow.isPGroup)

private theorem L₀_subset_K_mul_ON (hσ : σ.IsValid) (hr : σ.HypIV7 r) :
    (σ.L₀ : Set G) ⊆ (Subgroup.normalizer (d.R : Set G) : Set G) * (σ.ON : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  intro l hl
  obtain ⟨n, hn, k, hk, rfl⟩ := exists_mem_normalizer_mul_of_isSylowOf' d.R_sylow
    (σ.N_le_normalizer_ON (hσ.L₀_le_N hl))
  exact Set.mul_mem_mul hn hk

private theorem solvRadIn_K (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r) :
    solvRadIn (Subgroup.normalizer (d.R : Set G)) =
      oddCoreIn (Subgroup.normalizer (d.R : Set G)) ⊔ centerOf σ.D := by
  refine hII.qgroup_solvRad _ d.R_D (fun h => R_ne_bot d hr ?_) (L₀_subset_K_mul_ON d hσ hr)
  rw [eq_bot_iff, ← h]
  exact R_le_oddCoreIn_K d hr

private theorem x₂_not_mem_solvRadIn_K (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (hr : σ.HypIV7 r) : σ.x₂ ∉ solvRadIn (Subgroup.normalizer (d.R : Set G)) := by
  rw [solvRadIn_K d hσ hII hr]
  intro h
  have hZK : centerOf σ.D ≤
      Subgroup.normalizer (oddCoreIn (Subgroup.normalizer (d.R : Set G)) : Set G) :=
    (inf_le_left.trans d.R_D).trans (le_normalizer_oddCoreIn _)
  have h' : σ.x₂ ∈ ((oddCoreIn (Subgroup.normalizer (d.R : Set G)) ⊔ centerOf σ.D :
      Subgroup G) : Set G) := h
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZK] at h'
  obtain ⟨o, ho, z, hz, hoz⟩ := Set.mem_mul.mp h'
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hx₂D : σ.x₂ ∈ σ.D := σ.T_le_D hσ σ.x₂_mem_T
  have hoD : o ∈ σ.D := by
    have : o = σ.x₂ * z⁻¹ := by rw [← hoz]; group
    rw [this]
    exact σ.D.mul_mem hx₂D (σ.D.inv_mem hz.1)
  have ho1 : o = 1 := eq_one_of_isPGroup_two_of_mem_odd' hD2 (odd_card_oddCoreIn _) hoD ho
  rw [ho1, one_mul] at hoz
  have hx₂Z : σ.x₂ ∈ centerOf σ.D := hoz ▸ hz
  rw [← hII.center_S_eq_center_D] at hx₂Z
  exact hσ.x_ne_x₂ (hσ.center_involution σ.x₂ hx₂Z hσ.x₂_order).symm

private theorem V_le_centralizer_U : e.V ≤ Subgroup.centralizer (e.U : Set G) := by
  intro v hv
  by_cases hab : ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a
  · exact Subgroup.mem_centralizer_iff.mpr fun u hu => hab u hu v (e.V_lt.le hv)
  · have : v ∈ centerOf e.U := by rw [← e.V_center hab]; exact hv
    exact this.2

private theorem V_le_H₁ : e.V ≤ e.H₁ := fun _ hv =>
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
    Subgroup.mem_centralizer_iff.mp (V_le_centralizer_U d e hv) w hw.2)

private theorem odd_card_V (hr : σ.HypIV7 r) : Odd (Nat.card e.V) :=
  odd_card_of_isPGroup' hr.prime (σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON)
    ((isPGroup_U d e).to_le e.V_lt.le)

private theorem V_inf_centralizer_x₂ (hCV : σ.C ⊓ e.V = ⊥) :
    e.V ⊓ Subgroup.centralizer {σ.x₂} = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvC : v ∈ σ.C ⊓ e.U := by
    rw [C_inf_U_eq d e]
    exact ⟨e.V_lt.le hv.1, hv.2⟩
  have : v ∈ σ.C ⊓ e.V := ⟨hvC.1, hv.1⟩
  rwa [hCV] at this

private theorem x₂_inverts_V (hσ : σ.IsValid) (hr : σ.HypIV7 r) (hCV : σ.C ⊓ e.V = ⊥) :
    ∀ v ∈ e.V, σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ :=
  inverts_of_fixed_eq_bot (odd_card_V d e hr) hσ.x₂_order
    (T_le_normalizer_V d e hσ σ.x₂_mem_T) (V_inf_centralizer_x₂ d e hCV)

private theorem V_inf_oddCore (hσ : σ.IsValid) (hCV : σ.C ⊓ e.V = ⊥)
    (hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G)) :
    e.V ⊓ oddCoreIn e.H₁ = ⊥ := by
  have hT := hcen _ inf_le_right (((isPGroup_U d e).to_le e.V_lt.le).to_le inf_le_left)
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨T_le_normalizer_V d e hσ ht, le_normalizer_oddCoreIn _ (T_le_H₁ d e hσ ht)⟩
  rw [eq_bot_iff, ← V_inf_centralizer_x₂ d e hCV]
  intro v hv
  exact ⟨hv.1, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (hT σ.x₂_mem_T) v hv)⟩

private theorem card_V (hσ : σ.IsValid) (hr : σ.HypIV7 r) (hCV : σ.C ⊓ e.V = ⊥)
    (hexp : ∀ u ∈ e.U, u ^ r = 1) (hDH₁ : σ.D ≤ e.H₁)
    (hH₁w : IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G)) :
    Nat.card e.V = 1 ∨ Nat.card e.V = r := by
  have hTV := T_le_normalizer_V d e hσ
  have hcomm : ⁅e.V, σ.T⁆ = e.V := commutator_eq_self_of_inverted (odd_card_V d e hr) hTV
    fun v hv => ⟨σ.x₂, σ.x₂_mem_T, x₂_inverts_V d e hσ hr hCV v hv⟩
  obtain ⟨g, hgV, hle⟩ := le_zpowers_of_inf_eq_bot
    (h_II54 e.H₁ hDH₁ hH₁w e.V (V_le_H₁ d e) (odd_card_V d e hr) hTV hcomm)
    (V_inf_oddCore d e hσ hCV hcen)
  exact card_eq_one_or_of_le_zpowers hr.prime hle (hexp g (e.V_lt.le hgV))

private theorem iv910_nonabelian (hσ : σ.IsValid) (hr : σ.HypIV7 r)
    (hcl : ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥) (hPU : d.P ⊓ e.U = σ.C ⊓ e.U) (hCV : σ.C ⊓ e.V = ⊥)
    (hcardV : Nat.card e.V = 1 ∨ Nat.card e.V = r)
    (hab : ¬ ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a) :
    ⁅e.U, e.U⁆ = e.V ∧ e.V = centerOf e.U ∧ Nat.card e.V = r ∧
      (∀ a ∈ d.P ⊓ e.U, ∀ b ∈ d.P ⊓ e.U, a * b = b * a) ∧
      e.U ⊓ Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G) = (d.P ⊓ e.U) ⊔ e.V := by
  have hr2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hVc : e.V = centerOf e.U := e.V_center hab
  have hUodd : Odd (Nat.card e.U) := odd_card_of_isPGroup' hr.prime hr2 (isPGroup_U d e)
  have hUUU : ⁅e.U, e.U⁆ ≤ e.U := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact e.U.mul_mem (e.U.mul_mem (e.U.mul_mem ha hb) (e.U.inv_mem ha)) (e.U.inv_mem hb)
  have hUUC : ⁅e.U, e.U⁆ ≤ Subgroup.centralizer (e.U : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl
  have hUUV : ⁅e.U, e.U⁆ ≤ e.V := by rw [hVc]; exact le_inf hUUU hUUC
  have hUU1 : ⁅e.U, e.U⁆ ≠ ⊥ := by
    intro h
    apply hab
    intro a ha b hb
    have hc : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := h ▸ Subgroup.commutator_mem_commutator ha hb
    rw [Subgroup.mem_bot, commutatorElement_def] at hc
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [hc, one_mul]
  have hV1 : e.V ≠ ⊥ := fun h => hUU1 (le_bot_iff.mp (h ▸ hUUV))
  have hcard : Nat.card e.V = r :=
    hcardV.resolve_left fun h => hV1 (Subgroup.card_eq_one.mp h)
  have hUUeq : ⁅e.U, e.U⁆ = e.V := by
    apply Subgroup.eq_of_le_of_card_ge hUUV
    have hdvd : Nat.card (⁅e.U, e.U⁆ : Subgroup G) ∣ r :=
      (Subgroup.card_dvd_of_le hUUV).trans (dvd_of_eq hcard)
    rcases (Nat.dvd_prime hr.prime).mp hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hUU1
    · exact (hcard.trans h.symm).le
  have hA : d.P ⊓ e.U = e.U ⊓ Subgroup.centralizer {σ.x₂} := hPU.trans (C_inf_U_eq d e)
  have hAV : (d.P ⊓ e.U) ⊓ e.V = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    rintro a ⟨ha, haV⟩
    rw [hPU] at ha
    exact ⟨ha.1, haV⟩
  have hAab : ∀ a ∈ d.P ⊓ e.U, ∀ b ∈ d.P ⊓ e.U, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ d.P ⊓ e.U := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    have h2 : ⁅a, b⁆ ∈ e.V := hUUV (Subgroup.commutator_mem_commutator ha.2 hb.2)
    have h3 : ⁅a, b⁆ = 1 := by
      have : ⁅a, b⁆ ∈ (d.P ⊓ e.U) ⊓ e.V := ⟨h1, h2⟩
      rwa [hAV, Subgroup.mem_bot] at this
    rw [commutatorElement_def] at h3
    calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
      _ = b * a := by rw [h3, one_mul]
  refine ⟨hUUeq, hVc, hcard, hAab, le_antisymm ?_ ?_⟩
  · rw [hA] at hAV ⊢
    exact normalizer_inf_le_sup_of_inverts hUodd hσ.x₂_order
      (T_le_normalizer_U d e hσ σ.x₂_mem_T) hUUV e.V_lt.le (V_le_centralizer_U d e)
      (by rw [hVc]; exact le_rfl) (x₂_inverts_V d e hσ hr hCV) hAV
  · refine sup_le (le_inf inf_le_right Subgroup.le_normalizer) (le_inf e.V_lt.le ?_)
    intro v hv
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_iff.mp (V_le_centralizer_U d e hv) w hw.2)

private theorem iv910_abelian (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hexp : ∀ u ∈ e.U, u ^ r = 1) (hPU : d.P ⊓ e.U = σ.C ⊓ e.U) (hCV : σ.C ⊓ e.V = ⊥)
    (hDH₁ : σ.D ≤ e.H₁) (hH₁w : IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G))
    (hcardV : Nat.card e.V = 1 ∨ Nat.card e.V = r)
    (hab : ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a) :
    (d.P ⊓ e.U).relIndex e.U = r ∧
      ((∀ X Y : Subgroup G, X ≤ Subgroup.normalizer (d.R : Set G) →
        Y ≤ Subgroup.normalizer (d.R : Set G) →
        Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (X : Set G) →
        Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (Y : Set G) →
        ¬ X ≤ solvRadIn (Subgroup.normalizer (d.R : Set G)) →
        ¬ Y ≤ solvRadIn (Subgroup.normalizer (d.R : Set G)) →
        ¬ ⁅X, Y⁆ ≤ solvRadIn (Subgroup.normalizer (d.R : Set G))) → e.V = ⊥) := by
  have hr2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hUodd := odd_card_of_isPGroup' hr.prime hr2 (isPGroup_U d e)
  have hA : d.P ⊓ e.U = e.U ⊓ Subgroup.centralizer {σ.x₂} := hPU.trans (C_inf_U_eq d e)
  set I := invertedSubgroup e.U hab σ.x₂ with hI
  have hIU : I ≤ e.U := fun i hi => hi.1
  have hx₂U : σ.x₂ ∈ Subgroup.normalizer (e.U : Set G) := T_le_normalizer_U d e hσ σ.x₂_mem_T
  have hdec := (odd_fixed_mul_inverted hUodd hσ.x₂_order hx₂U).1
  have hx₂C : σ.x₂ ∉ Subgroup.centralizer (e.U : Set G) := fun h =>
    x₂_not_mem_solvRadIn_K d hσ hII hr (e.U_centralizer ⟨T_le_K d hσ σ.x₂_mem_T, h⟩)
  have hI1 : ∃ i ∈ I, i ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hx₂C
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : u ∈ (e.U : Set G) := hu
    rw [hdec] at hu'
    obtain ⟨a, ha, i, hi, rfl⟩ := Set.mem_mul.mp hu'
    rw [hcon i (mem_invertedSubgroup.mpr (OddInversion.mem_invertedSet.mp hi)), mul_one]
    exact Subgroup.mem_centralizer_singleton_iff.mp ha.2
  have hTI : σ.T ≤ Subgroup.normalizer (I : Set G) := by
    apply σ.T_le_of_mem
    · apply mem_normalizer_of_conj_mem'
      intro i hi
      have hxi : σ.x * i * σ.x⁻¹ = i := by
        have := Subgroup.mem_centralizer_iff.mp (x_mem_centralizer_U d e) i hi.1
        rw [← this]
        group
      rw [hxi]
      exact hi
    · apply mem_normalizer_of_conj_mem'
      intro i hi
      rw [hi.2]
      exact I.inv_mem hi
  have hIodd : Odd (Nat.card I) :=
    odd_card_of_isPGroup' hr.prime hr2 ((isPGroup_U d e).to_le hIU)
  have hIcomm : ⁅I, σ.T⁆ = I :=
    commutator_eq_self_of_inverted hIodd hTI fun i hi => ⟨σ.x₂, σ.x₂_mem_T, hi.2⟩
  have hUH₁ : e.U ≤ e.H₁ := fun u hu => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun w hw => hab w hw.2 u hu)
  have hIO : I ⊓ oddCoreIn e.H₁ = ⊥ := by
    have hT' := hcen _ inf_le_right (((isPGroup_U d e).to_le hIU).to_le inf_le_left)
      fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hTI ht, le_normalizer_oddCoreIn _ (T_le_H₁ d e hσ ht)⟩
    rw [eq_bot_iff]
    intro i hi
    rw [Subgroup.mem_bot]
    apply eq_one_of_fixed_inverted (odd_orderOf_of_mem hIodd hi.1) hi.1.2
    have := Subgroup.mem_centralizer_iff.mp (hT' σ.x₂_mem_T) i hi
    rw [← this]
    group
  obtain ⟨g, hgI, hle⟩ := le_zpowers_of_inf_eq_bot
    (h_II54 e.H₁ hDH₁ hH₁w I (hIU.trans hUH₁) hIodd hTI hIcomm) hIO
  have hcardI : Nat.card I = r := by
    rcases card_eq_one_or_of_le_zpowers hr.prime hle (hexp g (hIU hgI)) with h | h
    · obtain ⟨i, hi, hi1⟩ := hI1
      exact absurd ((Subgroup.mem_bot).mp ((Subgroup.card_eq_one.mp h) ▸ hi)) hi1
    · exact h
  have hAI : d.P ⊓ e.U ⊔ I = e.U := by
    apply le_antisymm (sup_le inf_le_right hIU)
    intro u hu
    have hu' : u ∈ (e.U : Set G) := hu
    rw [hdec] at hu'
    obtain ⟨a, ha, i, hi, rfl⟩ := Set.mem_mul.mp hu'
    rw [← hA] at ha
    exact Subgroup.mul_mem_sup ha (mem_invertedSubgroup.mpr (OddInversion.mem_invertedSet.mp hi))
  have hAI' : d.P ⊓ e.U ⊓ I = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    have hu1 : u ∈ e.U ⊓ Subgroup.centralizer {σ.x₂} := hA ▸ hu.1
    apply eq_one_of_fixed_inverted (odd_orderOf_of_mem hUodd hu1.1) hu.2.2
    have := Subgroup.mem_centralizer_singleton_iff.mp hu1.2
    rw [← this]
    group
  have hInA : I ≤ Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G) := fun i hi =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun w hw => hab w hw.2 i hi.1)
  have hcardU := card_sup_mul_card_inf_of_le_normalizer hInA
  rw [hAI, hAI', Subgroup.card_bot, mul_one, hcardI] at hcardU
  have hrel := Subgroup.relIndex_mul_card (d.P ⊓ e.U) e.U
  rw [inf_eq_left.mpr (inf_le_right : d.P ⊓ e.U ≤ e.U), hcardU, mul_comm _ r] at hrel
  have hindex : (d.P ⊓ e.U).relIndex e.U = r := Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  refine ⟨hindex, fun h_II415 => ?_⟩
  by_contra hV
  have hcardV' : Nat.card e.V = r := hcardV.resolve_left fun h => hV (Subgroup.card_eq_one.mp h)
  have hVI : e.V ≤ I := fun v hv => ⟨e.V_lt.le hv, x₂_inverts_V d e hσ hr hCV v hv⟩
  have hVeq : e.V = I := Subgroup.eq_of_le_of_card_ge hVI (by rw [hcardI, hcardV'])
  set K := Subgroup.normalizer (d.R : Set G) with hK
  set K₀ := trivOn K e.U e.V e.U_normal e.V_normal with hK₀
  have hxx : σ.x₂ * σ.x₂ = 1 := by rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]
  have hx₂K₀ : σ.x₂ ∈ K₀ := by
    refine ⟨T_le_K d hσ σ.x₂_mem_T, fun u hu => ?_⟩
    rw [hVeq]
    refine ⟨e.U.mul_mem (conj_mem_of_mem_normalizer' hx₂U hu) (e.U.inv_mem hu), ?_⟩
    exact conj_commutator_of_involution hxx
  have hK₀S : ¬ K₀ ≤ solvRadIn K := fun h => x₂_not_mem_solvRadIn_K d hσ hII hr (h hx₂K₀)
  have hYS : ¬ K ⊓ Subgroup.centralizer (e.V : Set G) ≤ solvRadIn K :=
    e.U_minimal e.V e.V_normal e.V_lt
  have hKY : K ≤ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer (e.V : Set G) : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, normalizer_le_normalizer_centralizer' e.V (e.V_normal hk)⟩
  have hKK₀ : K ≤ Subgroup.normalizer (K₀ : Set G) := le_normalizer_trivOn e.U_normal e.V_normal
  have hK₀K : K₀ ≤ K := fun k hk => hk.1
  apply h_II415 K₀ (K ⊓ Subgroup.centralizer (e.V : Set G)) hK₀K inf_le_left hKK₀ hKY hK₀S hYS
  have hZ : K₀ ⊓ (K ⊓ Subgroup.centralizer (e.V : Set G)) ≤ solvRadIn K := by
    apply le_solvRadIn_of_pow_mem hr.prime (inf_le_left.trans hK₀K) fun k hk =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hKK₀ hk, hKY hk⟩
    intro g hg
    apply e.U_centralizer
    exact ⟨K.pow_mem hg.2.1 r, pow_mem_centralizer_of_stabilizes hg.1.2 hg.2.2
      fun v hv => hexp v (e.V_lt.le hv)⟩
  refine le_trans ?_ hZ
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    have h' : g₂ * g₁⁻¹ * g₂⁻¹ ∈ K₀ := conj_mem_of_mem_normalizer' (hKK₀ hg₂.1) (K₀.inv_mem hg₁)
    have e' : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by group
    rw [e']
    exact K₀.mul_mem hg₁ h'
  · rw [commutatorElement_def]
    have h' : g₁ * g₂ * g₁⁻¹ ∈ K ⊓ Subgroup.centralizer (e.V : Set G) :=
      conj_mem_of_mem_normalizer' (hKY (hK₀K hg₁)) hg₂
    exact Subgroup.mul_mem _ h' (Subgroup.inv_mem _ hg₂)

private theorem PU_comm (hσ : σ.IsValid) (hr : σ.HypIV7 r) (hcl : ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥)
    (hPU : d.P ⊓ e.U = σ.C ⊓ e.U) (hCV : σ.C ⊓ e.V = ⊥)
    (hcardV : Nat.card e.V = 1 ∨ Nat.card e.V = r) :
    ∀ a ∈ d.P ⊓ e.U, ∀ b ∈ d.P ⊓ e.U, a * b = b * a := by
  by_cases hab : ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a
  · exact fun a ha b hb => hab a ha.2 b hb.2
  · exact (iv910_nonabelian d e hσ hr hcl hPU hCV hcardV hab).2.2.2.1

private theorem iv911_iii (hσ : σ.IsValid) [IsKleinFour σ.T] (hr : σ.HypIV7 r)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (hDH₁ : σ.D ≤ e.H₁) (hH₁w : IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (hcen₁ : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G))
    {H₀ : Subgroup G} (hTH₀ : σ.T ≤ H₀) (hAH₀ : d.P ⊓ e.U ≤ H₀)
    (h3 : 3 ∣ automizerIndex (σ.T.subgroupOf H₀)) :
    ∀ Y : Subgroup G, Y ≤ oddCoreIn H₀ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G) := by
  have hr2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have : Fact r.Prime := ⟨hr.prime⟩
  have hT2 := σ.isPGroup_two_T' hσ
  have hO₀odd := odd_card_oddCoreIn H₀
  have hH₀O : H₀ ≤ Subgroup.normalizer (oddCoreIn H₀ : Set G) := le_normalizer_oddCoreIn H₀
  have hTO₀ : σ.T ≤ Subgroup.normalizer (oddCoreIn H₀ : Set G) := hTH₀.trans hH₀O
  intro Y₀ hY₀O hY₀ hTY₀
  by_contra hnot
  obtain ⟨X₀, hX₀, hY₀X₀, hTX₀⟩ :=
    exists_isSylowOf_normalized_ge_of_odd hr.prime hT2 hTO₀ hO₀odd hY₀O hY₀ hTY₀
  have hnotX₀ : ¬ σ.T ≤ Subgroup.centralizer (X₀ : Set G) := fun h =>
    hnot (h.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hY₀X₀)))
  obtain ⟨g, hgH₀, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex_subgroupOf' hTH₀ h3
  have hstep : ∀ X : Subgroup G, IsSylowOf r X (oddCoreIn H₀) →
      σ.T ≤ Subgroup.normalizer (X : Set G) → ∀ a ∈ σ.T, a ≠ 1 →
        a ∉ Subgroup.centralizer (X : Set G) := by
    intro X hX hTX a ha ha1 haX
    have hall : ∀ b ∈ σ.T, b ≠ 1 → b ∈ Subgroup.centralizer (X : Set G) := by
      intro b hb hb1
      obtain ⟨h, hh, hab⟩ := exists_conj_eq_of_three hgN hg3 hg1 ha hb ha1 hb1
      have hhH₀ : h ∈ H₀ := by
        rcases hh with rfl | rfl | rfl
        · exact H₀.one_mem
        · exact hgH₀
        · exact H₀.mul_mem hgH₀ hgH₀
      have hhN : h ∈ Subgroup.normalizer (σ.T : Set G) := by
        rcases hh with rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact hgN
        · exact Subgroup.mul_mem _ hgN hgN
      have hX' := isSylowOf_map_conj' hX (hH₀O hhH₀)
      have hTX' := le_normalizer_map_conj hhN hTX
      obtain ⟨c, hc, hcX⟩ :=
        exists_conj_eq_of_isSylowOf_normalized_of_odd hr.prime hT2 hTO₀ hO₀odd hX hX' hTX hTX'
      have hbX' := conj_mem_centralizer_map_conj (h := h) haX
      rw [hab, ← hcX] at hbX'
      exact (mem_centralizer_map_conj_iff
        (Subgroup.mem_centralizer_iff.mp hc.2 b hb).symm).mp hbX'
    have hTX₁ : σ.T ≤ Subgroup.centralizer (X : Set G) :=
      σ.T_le_centralizer_of_mem (hall σ.x σ.x_mem_T (σ.x_ne_one' hσ))
        (hall σ.x₂ σ.x₂_mem_T (σ.x₂_ne_one' hσ))
    obtain ⟨c, hc, hcX⟩ :=
      exists_conj_eq_of_isSylowOf_normalized_of_odd hr.prime hT2 hTO₀ hO₀odd hX hX₀ hTX hTX₀
    apply hnotX₀
    intro t ht
    rw [← hcX]
    exact (mem_centralizer_map_conj_iff (Subgroup.mem_centralizer_iff.mp hc.2 t ht).symm).mpr
      (hTX₁ ht)
  set A := d.P ⊓ e.U with hAdef
  have hA : IsPGroup r A := d.P_sylow.isPGroup.to_le inf_le_left
  have hAodd : Odd (Nat.card A) := odd_card_of_isPGroup' hr.prime hr2 hA
  have hTA : σ.T ≤ Subgroup.normalizer (A : Set G) := T_le_normalizer_PU d e hσ
  have hAO : A ≤ Subgroup.normalizer (oddCoreIn H₀ : Set G) := hAH₀.trans hH₀O
  set M := oddCoreIn H₀ ⊔ A with hM
  have hModd : Odd (Nat.card M) := odd_card_sup_of_le_normalizer_of_odd hAO hO₀odd hAodd
  have hTM : σ.T ≤ Subgroup.normalizer (M : Set G) := fun t ht =>
    normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hTO₀ ht, hTA ht⟩
  obtain ⟨X₁, hX₁, hAX₁, hTX₁⟩ :=
    exists_isSylowOf_normalized_ge_of_odd hr.prime hT2 hTM hModd le_sup_right hA hTA
  have hMO : M ≤ Subgroup.normalizer (oddCoreIn H₀ : Set G) := sup_le Subgroup.le_normalizer hAO
  set X := X₁ ⊓ oddCoreIn H₀ with hXdef
  have hX : IsSylowOf r X (oddCoreIn H₀) := hX₁.inf_of_le_normalizer le_sup_left hMO
  have hTX : σ.T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTX₁ ht, hTO₀ ht⟩
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a ha =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hAX₁ ha), hAO ha⟩
  set Y := X ⊓ Subgroup.normalizer (A : Set G) with hYdef
  have hTY : σ.T ≤ Subgroup.normalizer (Y : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTX ht, mem_normalizer_normalizer (hTA ht)⟩
  obtain ⟨a, haT, ha1, haY⟩ := exists_mem_T_mem_centralizer hσ hr.prime hr2 h_II54 hDH₁ hH₁w
    hcen₁ (inf_le_right : Y ≤ e.H₁) (hX.isPGroup.to_le inf_le_left) hTY
  have hcop : Nat.Coprime r (Nat.card (Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers, kleinFour_orderOf haT ha1]
    exact (Nat.coprime_primes hr.prime Nat.prime_two).mpr hr2
  have haA : a ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
      (Subgroup.le_centralizer_iff.mp (P_le_centralizer_T d) haT)
  have hPQ : ⁅A, Subgroup.zpowers a⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.zpowers_le.mpr haA)
  have hfixed : X ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    intro y hy
    have hyY : y ∈ Y := ⟨hy.1, Subgroup.centralizer_le_normalizer _ hy.2⟩
    have hay : a ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp haY y hyY).symm
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr hay hz)
  have hXQ := CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q A (Subgroup.zpowers a) X hA
    hX.isPGroup hcop hAX (Subgroup.zpowers_le.mpr (hTX haT)) hPQ hfixed
  rw [Subgroup.commutator_comm] at hXQ
  exact hstep X hX hTX a haT ha1 (Subgroup.zpowers_le.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hXQ))

private theorem normalizer_zpowers_ne_top (hσ : σ.IsValid) (hr : σ.HypIV7 r) {p₀ : G}
    (hp₀ : p₀ ∈ d.P) (hp₀1 : p₀ ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers p₀ : Set G) ≠ ⊤ := by
  intro htop
  have hn : (Subgroup.zpowers p₀).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have : IsSimpleGroup G := hσ.simple
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.zpowers p₀) with h | h
  · apply hp₀1
    have := Subgroup.mem_zpowers p₀
    rwa [h, Subgroup.mem_bot] at this
  · have hx : σ.x ∈ Subgroup.zpowers p₀ := h ▸ Subgroup.mem_top _
    have hP : IsPGroup r (Subgroup.zpowers p₀) :=
      d.P_sylow.isPGroup.to_le (Subgroup.zpowers_le.mpr hp₀)
    have hcop : Nat.Coprime r 2 :=
      (Nat.coprime_primes hr.prime Nat.prime_two).mpr (σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON)
    exact σ.x_ne_one' hσ (eq_one_of_mem_of_coprime hr.prime hP hx hcop
      (by rw [← hσ.x_order, pow_orderOf_eq_one]))

private theorem ON_inf_le_oddCoreIn_inf_N (H : Subgroup G) :
    σ.ON ⊓ H ≤ oddCoreIn (H ⊓ Subgroup.centralizer ({σ.x} : Set G)) := by
  apply le_oddCoreIn (le_inf inf_le_right (inf_le_left.trans σ.ON_le_N))
  · intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨σ.N_le_normalizer_ON hg.2, Subgroup.le_normalizer hg.1⟩
  · exact σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

end UV

variable (σ) in
theorem lemmaIV910 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (e : IV9UV d)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II415 : ∀ X Y : Subgroup G, X ≤ Subgroup.normalizer (d.R : Set G) →
      Y ≤ Subgroup.normalizer (d.R : Set G) →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (X : Set G) →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (Y : Set G) →
      ¬ X ≤ solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ Y ≤ solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ⁅X, Y⁆ ≤ solvRadIn (Subgroup.normalizer (d.R : Set G)))
    (h1 : ¬ PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁)) :
    ((∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a) ∧ (∀ u ∈ e.U, u ^ r = 1) ∧ e.V = ⊥ ∧
        (d.P ⊓ e.U).relIndex e.U = r) ∨
      (⁅e.U, e.U⁆ = e.V ∧ e.V = centerOf e.U ∧ Nat.card e.V = r ∧ (∀ u ∈ e.U, u ^ r = 1) ∧
        (∀ a ∈ d.P ⊓ e.U, ∀ b ∈ d.P ⊓ e.U, a * b = b * a) ∧
        e.U ⊓ Subgroup.normalizer ((d.P ⊓ e.U : Subgroup G) : Set G) = (d.P ⊓ e.U) ⊔ e.V) := by
  obtain ⟨hexp, hcl, hPU, hCV, -⟩ := h97
  obtain ⟨hDH₁, hH₁w⟩ := h98
  have hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G) :=
    fun Y hYO hY hTY => T_le_centralizer_of_not_constrained' hσ hr.prime (T_le_H₁ d e hσ) h92 h1
      hYO hY hTY
  have hcardV := card_V d e hσ hr hCV hexp hDH₁ hH₁w h_II54 hcen
  by_cases hab : ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a
  · obtain ⟨hidx, hV⟩ := iv910_abelian d e hσ hII hr hexp hPU hCV hDH₁ hH₁w h_II54
      hcen hcardV hab
    exact Or.inl ⟨hab, hexp, hV h_II415, hidx⟩
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := iv910_nonabelian d e hσ hr hcl hPU hCV hcardV hab
    exact Or.inr ⟨h₁, h₂, h₃, hexp, h₄, h₅⟩

variable (σ) in
theorem lemmaIV911 (hσ : σ.IsValid) {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) (e : IV9UV d)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h1 : ¬ PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁)) {P₀ : Subgroup G}
    (hP₀ : P₀ ≤ d.P ⊓ e.U) :
    3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.normalizer (P₀ : Set G))) ∧
      (d.P ⊓ e.U) ⊔ e.V ⊔ σ.T ≤ Subgroup.normalizer (P₀ : Set G) ∧
      ∀ Y : Subgroup G, Y ≤ oddCoreIn (Subgroup.normalizer (P₀ : Set G)) → IsPGroup r Y →
        σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G) := by
  obtain ⟨hexp, hcl, hPU, hCV, -⟩ := h97
  obtain ⟨hDH₁, hH₁w⟩ := h98
  have : IsKleinFour σ.T := isKleinFour_of_subgroupOf (T_le_H₁ d e hσ) hH₁w.2.1
  have hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G) :=
    fun Y hYO hY hTY => T_le_centralizer_of_not_constrained' hσ hr.prime (T_le_H₁ d e hσ) h92 h1
      hYO hY hTY
  have hcardV := card_V d e hσ hr hCV hexp hDH₁ hH₁w h_II54 hcen
  have hAcomm := PU_comm d e hσ hr hcl hPU hCV hcardV
  have hTP : σ.T ≤ Subgroup.centralizer (d.P : Set G) :=
    Subgroup.le_centralizer_iff.mp (P_le_centralizer_T d)
  have hCP : Subgroup.centralizer (d.P : Set G) ≤ Subgroup.normalizer (P₀ : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (hP₀.trans inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hii : (d.P ⊓ e.U) ⊔ e.V ⊔ σ.T ≤ Subgroup.normalizer (P₀ : Set G) := by
    refine sup_le (sup_le ?_ ?_) (hTP.trans hCP)
    · intro a ha
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun w hw => hAcomm w (hP₀ hw) a ha)
    · intro v hv
      exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_iff.mp (V_le_centralizer_U d e hv) w (hP₀ hw).2)
  have hi : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.normalizer (P₀ : Set G))) :=
    three_dvd_automizerIndex_mono' hTP hCP h95iii
  exact ⟨hi, hii, iv911_iii d e hσ hr h_II54 hDH₁ hH₁w hcen (le_sup_right.trans hii)
    (le_sup_left.trans (le_sup_left.trans hii)) hi⟩

section UV2

variable {r : ℕ} (d : σ.IV7Data r) (e : IV9UV d)

private theorem iv912_false (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hqd : σ.height = 1)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II417 : ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆)
    (h_II34a : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → IsPGroup r W → (∀ w ∈ W, w ^ r = 1) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ⁅W, W⁆ ≤ oddCoreIn H)
    (h1 : ¬ PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (hab : ¬ ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a) : False := by
  have h97' := h97
  have h98' := h98
  obtain ⟨hexp, hcl, hPU, hCV, hA1⟩ := h97
  obtain ⟨hDH₁, hH₁w⟩ := h98
  have hr2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have : Fact r.Prime := ⟨hr.prime⟩
  have : IsKleinFour σ.T := isKleinFour_of_subgroupOf (T_le_H₁ d e hσ) hH₁w.2.1
  have hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G) :=
    fun Y hYO hY hTY => T_le_centralizer_of_not_constrained' hσ hr.prime (T_le_H₁ d e hσ) h92 h1
      hYO hY hTY
  have hcardV := card_V d e hσ hr hCV hexp hDH₁ hH₁w h_II54 hcen
  obtain ⟨hUUV, hVc, hcard, hAab, hNA⟩ := iv910_nonabelian d e hσ hr hcl hPU hCV hcardV hab
  have hVinv := x₂_inverts_V d e hσ hr hCV
  have hA : d.P ⊓ e.U = e.U ⊓ Subgroup.centralizer {σ.x₂} := hPU.trans (C_inf_U_eq d e)
  have hAV : (d.P ⊓ e.U) ⊓ e.V = ⊥ := by
    rw [eq_bot_iff, ← hCV]
    rintro a ⟨ha, haV⟩
    rw [hPU] at ha
    exact ⟨ha.1, haV⟩
  obtain ⟨p₀, hp₀A, hp₀1⟩ : ∃ p₀ ∈ d.P ⊓ e.U, p₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA1 ((Subgroup.eq_bot_iff_forall _).mpr hcon)
  have hP₀A : Subgroup.zpowers p₀ ≤ d.P ⊓ e.U := Subgroup.zpowers_le.mpr hp₀A
  obtain ⟨hi, hii, hiii⟩ := σ.lemmaIV911 hσ hr d e h92 h95iii h97' h98' h_II54 h1 hP₀A
  have hTH₀ : σ.T ≤ Subgroup.normalizer (Subgroup.zpowers p₀ : Set G) := le_sup_right.trans hii
  have hVH₀ : e.V ≤ Subgroup.normalizer (Subgroup.zpowers p₀ : Set G) :=
    (le_sup_right.trans le_sup_left).trans hii
  obtain ⟨w, hwU, hwp, hwAV⟩ : ∃ w ∈ e.U, w * p₀ = p₀ * w ∧ w ∉ d.P ⊓ e.U ⊔ e.V := by
    by_contra hcon
    push Not at hcon
    exact h_II417 e.U e.U_le e.U_normal hexp e.U_centralizer
      (exists_le_closure_pair_sup hr.prime hUUV hVc hcard inf_le_right hAab hAV hp₀A hp₀1 hcon)
  have hUodd := odd_card_of_isPGroup' hr.prime hr2 (isPGroup_U d e)
  have hdec := (odd_fixed_mul_inverted hUodd hσ.x₂_order
    (T_le_normalizer_U d e hσ σ.x₂_mem_T)).1
  have hw' : w ∈ (e.U : Set G) := hwU
  rw [hdec] at hw'
  obtain ⟨a, ha, f, hf, rfl⟩ := Set.mem_mul.mp hw'
  obtain ⟨hfU, hfx⟩ := OddInversion.mem_invertedSet.mp hf
  have haA : a ∈ d.P ⊓ e.U := hA ▸ ha
  have hfp : f * p₀ = p₀ * f := by
    have hap := hAab a haA p₀ hp₀A
    apply mul_left_cancel (a := a)
    calc a * (f * p₀) = a * f * p₀ := (mul_assoc _ _ _).symm
      _ = p₀ * (a * f) := hwp
      _ = (a * p₀) * f := by rw [← mul_assoc, hap]
      _ = a * (p₀ * f) := mul_assoc _ _ _
  have hfAV : f ∉ d.P ⊓ e.U ⊔ e.V := fun h =>
    hwAV (Subgroup.mul_mem _ (le_sup_left (a := d.P ⊓ e.U) (b := e.V) haA) h)
  obtain ⟨a₁, ha₁A, ha₁f⟩ : ∃ a₁ ∈ d.P ⊓ e.U, f * a₁ ≠ a₁ * f := by
    by_contra hcon
    push Not at hcon
    apply hfAV
    rw [← hNA]
    exact ⟨hfU, Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcon b hb).symm)⟩
  set U₀ := Subgroup.closure ({f, a₁} : Set G) with hU₀
  have hfU₀ : f ∈ U₀ := Subgroup.subset_closure (Set.mem_insert _ _)
  have ha₁U₀ : a₁ ∈ U₀ := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hU₀U : U₀ ≤ e.U := (Subgroup.closure_le _).mpr
    (Set.insert_subset_iff.mpr ⟨hfU, Set.singleton_subset_iff.mpr ha₁A.2⟩)
  have key : ∀ y : G, y * p₀ = p₀ * y →
      y ∈ Subgroup.centralizer (Subgroup.zpowers p₀ : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have : p₀ ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hy.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr this hh)
  have hU₀C : U₀ ≤ Subgroup.centralizer (Subgroup.zpowers p₀ : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact key _ hfp
    · exact key _ (hAab _ ha₁A p₀ hp₀A)
  have hU₀H₀ : U₀ ≤ Subgroup.normalizer (Subgroup.zpowers p₀ : Set G) :=
    hU₀C.trans (Subgroup.centralizer_le_normalizer _)
  have hTU₀ : σ.T ≤ Subgroup.normalizer (U₀ : Set G) := by
    apply σ.T_le_of_mem
    · exact Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU₀U) (x_mem_centralizer_U d e))
    · apply mem_normalizer_closure_of_conj_mem
      intro y hy
      rcases hy with rfl | rfl
      · rw [hfx]
        exact Subgroup.inv_mem _ hfU₀
      · have hx₂a : y * σ.x₂ = σ.x₂ * y := by
          have := ha₁A
          rw [hA] at this
          exact Subgroup.mem_centralizer_singleton_iff.mp this.2
        have : σ.x₂ * y * σ.x₂⁻¹ = y := by rw [← hx₂a]; group
        rw [this]
        exact ha₁U₀
  have hc1 : ⁅f, a₁⁆ ≠ 1 := by
    intro h
    rw [commutatorElement_def] at h
    apply ha₁f
    calc f * a₁ = (f * a₁ * f⁻¹ * a₁⁻¹) * a₁ * f := by group
      _ = a₁ * f := by rw [h, one_mul]
  have hcV : ⁅f, a₁⁆ ∈ e.V := hUUV ▸ Subgroup.commutator_mem_commutator hfU ha₁A.2
  have hVU₀ : e.V ≤ ⁅U₀, U₀⁆ := by
    intro v hv
    obtain ⟨k, hk⟩ := exists_zpow_eq_of_card_prime hr.prime hcard hcV hc1 v hv
    rw [← hk]
    exact Subgroup.zpow_mem _ (Subgroup.commutator_mem_commutator hfU₀ ha₁U₀) k
  have hVO : e.V ≤ oddCoreIn (Subgroup.normalizer (Subgroup.zpowers p₀ : Set G)) := by
    rcases hII.qd_or_d_of_three _ hTH₀ (Or.inr hqd) hi with hQD | hDw
    · have hne := normalizer_zpowers_ne_top d hσ hr hp₀A.1 hp₀1
      have hWI := hII.workingI _ hne hQD σ.x (hTH₀ σ.x_mem_T) hσ.x_order σ.T hTH₀
        ‹IsKleinFour σ.T› σ.x_mem_T
      intro v hv
      have hvON : v ∈ σ.ON ⊓ Subgroup.normalizer (Subgroup.zpowers p₀ : Set G) :=
        ⟨U_le_ON d e (e.V_lt.le hv), hVH₀ hv⟩
      have hmem := hWI (Subgroup.commutator_mem_commutator σ.x₂_mem_T
        (ON_inf_le_oddCoreIn_inf_N _ hvON))
      rw [commutatorElement_def, hVinv v hv] at hmem
      have hvo : Odd (orderOf v⁻¹) := by
        rw [orderOf_inv]
        exact odd_orderOf_of_mem (odd_card_V d e hr) hv
      have := mem_of_mul_self_mem_of_odd hvo hmem
      simpa using this
    · exact hVU₀.trans (h_II34a _ hTH₀ hDw U₀ (le_inf hU₀H₀ (hU₀U.trans (U_le_N d e)))
        ((isPGroup_U d e).to_le hU₀U) (fun w hw => hexp w (hU₀U hw)) hTU₀)
  have hTV := hiii e.V hVO ((isPGroup_U d e).to_le e.V_lt.le) (T_le_normalizer_V d e hσ)
  have hV1 : e.V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro v hv
    apply eq_one_of_fixed_inverted (odd_orderOf_of_mem (odd_card_V d e hr) hv) (hVinv v hv)
    have := Subgroup.mem_centralizer_iff.mp (hTV σ.x₂_mem_T) v hv
    rw [← this]
    group
  rw [hV1, Subgroup.card_bot] at hcard
  exact hr.prime.one_lt.ne hcard

private theorem exists_lift (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hqd : σ.height = 1) {u : G} (huK : u ∈ Subgroup.normalizer (d.R : Set G)) {m : ℕ}
    (hm : Odd m) (hum : u ^ m ∈ Subgroup.centralizer (e.U : Set G))
    (hinv : σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (e.U : Set G)) :
    ∃ v ∈ Subgroup.normalizer (d.R : Set G), σ.x * v = v * σ.x ∧
      σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ ∧ Odd (orderOf v) ∧
      ∀ w ∈ e.U, v * w * v⁻¹ = (u * u) * w * (u * u)⁻¹ := by
  set K := Subgroup.normalizer (d.R : Set G) with hK
  set O := oddCoreIn K with hO
  set C₀ := K ⊓ Subgroup.centralizer (e.U : Set G) with hC₀
  set O₁ := C₀ ⊓ O with hO₁
  have hxK : σ.x ∈ K := T_le_K d hσ σ.x_mem_T
  have hx₂K : σ.x₂ ∈ K := T_le_K d hσ σ.x₂_mem_T
  have hxC₀ : σ.x ∈ C₀ := ⟨hxK, x_mem_centralizer_U d e⟩
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hKC₀ : K ≤ Subgroup.normalizer (C₀ : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, normalizer_le_normalizer_centralizer' e.U (e.U_normal hk)⟩
  have hKO₁ : K ≤ Subgroup.normalizer (O₁ : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKC₀ hk, hKO hk⟩
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn K
  have hO₁odd : Odd (Nat.card O₁) := hOodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hO₁K : O₁ ≤ K := inf_le_left.trans inf_le_left
  have hO₁C : O₁ ≤ Subgroup.centralizer (e.U : Set G) := inf_le_left.trans inf_le_right
  have hxx : σ.x * σ.x = 1 := by rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]
  have hfac : O ⊔ (K ⊓ σ.N) = K := by
    refine (hII.cover_qgroup K (T_le_K d hσ) (fun h => R_ne_bot d hr ?_)
      (L₀_subset_K_mul_ON d hσ hr)).2
    rw [eq_bot_iff, ← h]
    exact R_le_oddCoreIn_K d hr
  have hxk : ∀ k ∈ K, σ.x * k * σ.x⁻¹ * k⁻¹ ∈ O₁ := by
    intro k hk
    refine ⟨?_, ?_⟩
    · have h1 : k * σ.x⁻¹ * k⁻¹ ∈ C₀ := conj_mem_of_mem_normalizer' (hKC₀ hk) (C₀.inv_mem hxC₀)
      have e1 : σ.x * k * σ.x⁻¹ * k⁻¹ = σ.x * (k * σ.x⁻¹ * k⁻¹) := by group
      rw [e1]
      exact C₀.mul_mem hxC₀ h1
    · have hKN : K ⊓ σ.N ≤ Subgroup.normalizer (O : Set G) := inf_le_left.trans hKO
      have hk' : k ∈ ((O ⊔ (K ⊓ σ.N) : Subgroup G) : Set G) := by rw [hfac]; exact hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKN] at hk'
      obtain ⟨o, ho, n', hn', rfl⟩ := Set.mem_mul.mp hk'
      have hn'x : n' * σ.x = σ.x * n' := (σ.mem_N_iff n').mp hn'.2
      have e1 : σ.x * (o * n') * σ.x⁻¹ * (o * n')⁻¹ = (σ.x * o * σ.x⁻¹) * o⁻¹ := by
        calc σ.x * (o * n') * σ.x⁻¹ * (o * n')⁻¹ =
            σ.x * o * (σ.x⁻¹ * (σ.x * n') * σ.x⁻¹) * n'⁻¹ * o⁻¹ := by group
          _ = σ.x * o * (σ.x⁻¹ * (n' * σ.x) * σ.x⁻¹) * n'⁻¹ * o⁻¹ := by rw [hn'x]
          _ = (σ.x * o * σ.x⁻¹) * o⁻¹ := by group
      rw [e1]
      exact O.mul_mem (conj_mem_of_mem_normalizer' (hKO hxK) ho) (O.inv_mem ho)
  have hZx : centerOf σ.D ≤ Subgroup.zpowers σ.x := σ.centerOf_D_le_zpowers_x' hσ hII hqd
  have hxO : Subgroup.zpowers σ.x ≤ Subgroup.normalizer (O : Set G) :=
    Subgroup.zpowers_le.mpr (hKO hxK)
  have hC₀O : ∀ c ∈ C₀, ∃ o ∈ O, c = o ∨ c = o * σ.x := by
    intro c hc
    have h1 : c ∈ solvRadIn K := e.U_centralizer hc
    rw [solvRadIn_K d hσ hII hr] at h1
    have h2 : c ∈ ((O ⊔ Subgroup.zpowers σ.x : Subgroup G) : Set G) :=
      (sup_le_sup_left hZx O) h1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hxO] at h2
    obtain ⟨o, ho, y, hy, rfl⟩ := Set.mem_mul.mp h2
    rcases eq_one_or_eq_of_mem_zpowers' hσ.x_order hy with rfl | rfl
    · exact ⟨o, ho, Or.inl (mul_one o)⟩
    · exact ⟨o, ho, Or.inr rfl⟩
  have hsqO : ∀ c ∈ C₀, c * c ∈ O := by
    intro c hc
    obtain ⟨o, ho, rfl | rfl⟩ := hC₀O c hc
    · exact O.mul_mem ho ho
    · have e1 : o * σ.x * (o * σ.x) = o * (σ.x * o * σ.x⁻¹) * (σ.x * σ.x) := by group
      rw [e1, hxx, mul_one]
      exact O.mul_mem ho (conj_mem_of_mem_normalizer' (hKO hxK) ho)
  obtain ⟨u₂, hu₂⟩ : ∃ u₂, u₂ = u * u := ⟨_, rfl⟩
  have hu₂K : u₂ ∈ K := hu₂ ▸ K.mul_mem huK huK
  have humC₀ : u ^ m ∈ C₀ := ⟨K.pow_mem huK m, hum⟩
  have hu₂m : u₂ ^ m ∈ O := by
    rw [hu₂, (Commute.refl u).mul_pow]
    exact hsqO _ humC₀
  have hu₂odd : Odd (orderOf u₂) := by
    have h1 : Odd (orderOf (u₂ ^ m)) := odd_orderOf_of_mem hOodd hu₂m
    have h2 : orderOf u₂ ∣ m * orderOf (u₂ ^ m) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, pow_orderOf_eq_one]
    exact (hm.mul h1).of_dvd_nat h2
  set M := O₁ ⊔ Subgroup.zpowers u₂ with hM
  have hModd : Odd (Nat.card M) := odd_card_sup_of_le_normalizer_of_odd
    (Subgroup.zpowers_le.mpr (hKO₁ hu₂K)) hO₁odd (by rw [Nat.card_zpowers]; exact hu₂odd)
  have hMK : M ≤ K := sup_le hO₁K (Subgroup.zpowers_le.mpr hu₂K)
  have hxM : σ.x ∈ Subgroup.normalizer (M : Set G) := by
    apply mem_normalizer_sup_zpowers
    · exact fun a ha => conj_mem_of_mem_normalizer' (hKO₁ hxK) ha
    · have e1 : σ.x * u₂ * σ.x⁻¹ = (σ.x * u₂ * σ.x⁻¹ * u₂⁻¹) * u₂ := by group
      rw [e1]
      exact Subgroup.mul_mem_sup (hxk u₂ hu₂K) (Subgroup.mem_zpowers u₂)
  have hdecA := (odd_fixed_mul_inverted hModd hσ.x_order hxM).1
  have hu₂M : u₂ ∈ (M : Set G) := (le_sup_right : Subgroup.zpowers u₂ ≤ M)
    (Subgroup.mem_zpowers u₂)
  rw [hdecA] at hu₂M
  obtain ⟨f, hf, i, hi, hfi⟩ := Set.mem_mul.mp hu₂M
  obtain ⟨hiM, hix⟩ := OddInversion.mem_invertedSet.mp hi
  have hiO₁ : i ∈ O₁ := by
    have h1 := hxk i (hMK hiM)
    rw [hix] at h1
    have h2 : i⁻¹ ∈ O₁ := mem_of_mul_self_mem_of_odd
      (by rw [orderOf_inv]; exact odd_orderOf_of_mem hModd hiM) h1
    simpa using O₁.inv_mem h2
  have hfM : f ∈ M := hf.1
  have hfx : f * σ.x = σ.x * f := Subgroup.mem_centralizer_singleton_iff.mp hf.2
  have hfK : f ∈ K := hMK hfM
  have hfodd : Odd (orderOf f) := odd_orderOf_of_mem hModd hfM
  have hfeq : f = u₂ * i⁻¹ := by rw [← hfi]; group
  set O₂ := O₁ ⊓ Subgroup.centralizer ({σ.x} : Set G) with hO₂
  have hO₂O₁ : O₂ ≤ O₁ := inf_le_left
  have hO₂odd : Odd (Nat.card O₂) := hO₁odd.of_dvd_nat (Subgroup.card_dvd_of_le hO₂O₁)
  have hCx : ∀ g, g * σ.x = σ.x * g → g ∈ Subgroup.normalizer
      (Subgroup.centralizer ({σ.x} : Set G) : Set G) := fun g hg =>
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  have hfO₂ : f ∈ Subgroup.normalizer (O₂ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKO₁ hfK, hCx f hfx⟩
  have hx₂x : σ.x₂ * σ.x = σ.x * σ.x₂ := hσ.commute.symm
  have hx₂O₂ : σ.x₂ ∈ Subgroup.normalizer (O₂ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKO₁ hx₂K, hCx σ.x₂ hx₂x⟩
  obtain ⟨c, hc⟩ : ∃ c, c = σ.x₂ * f * σ.x₂⁻¹ * f := ⟨_, rfl⟩
  have hcC₀ : c ∈ C₀ := by
    have hc₀ : σ.x₂ * u * σ.x₂⁻¹ * u ∈ C₀ :=
      ⟨K.mul_mem (K.mul_mem (K.mul_mem hx₂K huK) (K.inv_mem hx₂K)) huK, hinv⟩
    have hc₂ : σ.x₂ * u₂ * σ.x₂⁻¹ * u₂ ∈ C₀ := by
      have e1 : σ.x₂ * u₂ * σ.x₂⁻¹ * u₂ =
          (σ.x₂ * u * σ.x₂⁻¹ * u) * (u⁻¹ * (σ.x₂ * u * σ.x₂⁻¹ * u) * u) := by
        rw [hu₂]
        simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
      rw [e1]
      exact C₀.mul_mem hc₀
        (by simpa using conj_mem_of_mem_normalizer' (hKC₀ (K.inv_mem huK)) hc₀)
    have hj : σ.x₂ * i⁻¹ * σ.x₂⁻¹ ∈ C₀ :=
      conj_mem_of_mem_normalizer' (hKC₀ hx₂K) (C₀.inv_mem hiO₁.1)
    have e2 : c = (σ.x₂ * u₂ * σ.x₂⁻¹ * u₂) * (u₂⁻¹ * (σ.x₂ * i⁻¹ * σ.x₂⁻¹) * u₂) * i⁻¹ := by
      rw [hc, hfeq]
      group
    rw [e2]
    exact C₀.mul_mem (C₀.mul_mem hc₂
      (by simpa using conj_mem_of_mem_normalizer' (hKC₀ (K.inv_mem hu₂K)) hj))
      (C₀.inv_mem hiO₁.1)
  have hcx : c * σ.x = σ.x * c := by
    have hx₂x' : σ.x₂⁻¹ * σ.x = σ.x * σ.x₂⁻¹ := by
      rw [σ.x₂_inv' hσ]; exact hx₂x
    calc c * σ.x = σ.x₂ * f * σ.x₂⁻¹ * (f * σ.x) := by rw [hc]; group
      _ = σ.x₂ * f * (σ.x₂⁻¹ * σ.x) * f := by rw [hfx]; group
      _ = σ.x₂ * (f * σ.x) * σ.x₂⁻¹ * f := by rw [hx₂x']; group
      _ = (σ.x₂ * σ.x) * f * σ.x₂⁻¹ * f := by rw [hfx]; group
      _ = σ.x * c := by rw [hx₂x, hc]; group
  have hcO : c ∈ O := by
    obtain ⟨o, ho, hco | hco⟩ := hC₀O c hcC₀
    · exact hco ▸ ho
    · exfalso
      have hoC₀ : o ∈ C₀ := by
        have : o = c * σ.x⁻¹ := by rw [hco]; group
        rw [this]
        exact C₀.mul_mem hcC₀ (C₀.inv_mem hxC₀)
      have hox : o * σ.x = σ.x * o := by
        have ho' : o = c * σ.x⁻¹ := by rw [hco]; group
        calc o * σ.x = c := hco.symm
          _ = σ.x * c * σ.x⁻¹ := by rw [← hcx]; group
          _ = σ.x * o := by rw [ho']; group
      have hoM : o ∈ M := (le_sup_left : O₁ ≤ M) ⟨hoC₀, ho⟩
      have hf1 : (σ.x₂ * f * σ.x₂⁻¹) ^ orderOf f = 1 := by
        rw [conj_pow, pow_orderOf_eq_one]
        group
      have hfx' : σ.x₂ * f * σ.x₂⁻¹ = σ.x * (o * f⁻¹) := by
        have : σ.x₂ * f * σ.x₂⁻¹ = c * f⁻¹ := by rw [hc]; group
        rw [this, hco, mul_assoc, ← mul_assoc σ.x, ← hox, mul_assoc]
      have hcomm : Commute σ.x (o * f⁻¹) := by
        show σ.x * (o * f⁻¹) = o * f⁻¹ * σ.x
        have hfx'' : f⁻¹ * σ.x = σ.x * f⁻¹ := by
          calc f⁻¹ * σ.x = f⁻¹ * (σ.x * f) * f⁻¹ := by group
            _ = f⁻¹ * (f * σ.x) * f⁻¹ := by rw [hfx]
            _ = σ.x * f⁻¹ := by group
        rw [← mul_assoc, ← hox, mul_assoc, ← hfx'', mul_assoc]
      have hxp : σ.x ^ orderOf f = σ.x := by
        obtain ⟨k, hk⟩ := hfodd
        rw [hk, pow_succ, pow_mul, pow_two, hxx, one_pow, one_mul]
      rw [hfx', hcomm.mul_pow, hxp] at hf1
      have hxM : σ.x ∈ M := by
        have : σ.x = ((o * f⁻¹) ^ orderOf f)⁻¹ := eq_inv_of_mul_eq_one_left hf1
        rw [this]
        exact M.inv_mem (M.pow_mem (M.mul_mem hoM (M.inv_mem hfM)) _)
      exact σ.x_ne_one' hσ (eq_one_of_isPGroup_two_of_mem_odd'
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ.x_order, pow_one]))
        hModd (Subgroup.mem_zpowers σ.x) hxM)
  have hcO₂ : c ∈ O₂ := ⟨⟨hcC₀, hcO⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcx⟩
  set M' := O₂ ⊔ Subgroup.zpowers f with hM'
  have hM'odd : Odd (Nat.card M') := odd_card_sup_of_le_normalizer_of_odd
    (Subgroup.zpowers_le.mpr hfO₂) hO₂odd (by rw [Nat.card_zpowers]; exact hfodd)
  have hx₂M' : σ.x₂ ∈ Subgroup.normalizer (M' : Set G) := by
    apply mem_normalizer_sup_zpowers
    · exact fun a ha => conj_mem_of_mem_normalizer' hx₂O₂ ha
    · have e1 : σ.x₂ * f * σ.x₂⁻¹ = c * f⁻¹ := by rw [hc]; group
      rw [e1]
      exact Subgroup.mul_mem_sup hcO₂ (Subgroup.inv_mem _ (Subgroup.mem_zpowers f))
  have hdecB := (odd_fixed_mul_inverted hM'odd hσ.x₂_order hx₂M').1
  have hfM' : f ∈ (M' : Set G) := (le_sup_right : Subgroup.zpowers f ≤ M')
    (Subgroup.mem_zpowers f)
  rw [hdecB] at hfM'
  obtain ⟨c', hc', v, hv, hcv⟩ := Set.mem_mul.mp hfM'
  obtain ⟨hvM', hvx₂⟩ := OddInversion.mem_invertedSet.mp hv
  have hc'O₂ : c' ∈ O₂ := by
    have hc'M : c' ∈ ((O₂ ⊔ Subgroup.zpowers f : Subgroup G) : Set G) := hc'.1
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr hfO₂)] at hc'M
    obtain ⟨o₂, ho₂, y, hy, rfl⟩ := Set.mem_mul.mp hc'M
    have hy' : y ∈ Submonoid.powers f := mem_powers_iff_mem_zpowers.mpr hy
    obtain ⟨j, rfl⟩ := hy'
    have hfix : σ.x₂ * (o₂ * f ^ j) * σ.x₂⁻¹ = o₂ * f ^ j := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc'.2
      rw [← this]
      group
    have e1 : σ.x₂ * (o₂ * f ^ j) * σ.x₂⁻¹ =
        (σ.x₂ * o₂ * σ.x₂⁻¹) * ((c * f⁻¹) ^ j * f ^ j) * (f ^ j)⁻¹ := by
      have : σ.x₂ * f * σ.x₂⁻¹ = c * f⁻¹ := by rw [hc]; group
      rw [show σ.x₂ * (o₂ * f ^ j) * σ.x₂⁻¹ = (σ.x₂ * o₂ * σ.x₂⁻¹) * (σ.x₂ * f * σ.x₂⁻¹) ^ j by
        rw [conj_pow]; group, this]
      group
    have hq := pow_mul_pow_mem hcO₂ hfO₂ j
    have ho₂' := conj_mem_of_mem_normalizer' hx₂O₂ ho₂
    have hsq : f ^ j * f ^ j ∈ O₂ := by
      have e2 : f ^ j * f ^ j = o₂⁻¹ * ((σ.x₂ * o₂ * σ.x₂⁻¹) * ((c * f⁻¹) ^ j * f ^ j)) := by
        have h3 := hfix
        rw [e1] at h3
        calc f ^ j * f ^ j = o₂⁻¹ * (o₂ * f ^ j) * f ^ j := by group
          _ = o₂⁻¹ * ((σ.x₂ * o₂ * σ.x₂⁻¹) * ((c * f⁻¹) ^ j * f ^ j) * (f ^ j)⁻¹) * f ^ j := by
              rw [h3]
          _ = o₂⁻¹ * ((σ.x₂ * o₂ * σ.x₂⁻¹) * ((c * f⁻¹) ^ j * f ^ j)) := by group
      rw [e2]
      exact O₂.mul_mem (O₂.inv_mem ho₂) (O₂.mul_mem ho₂' hq)
    have hfj : f ^ j ∈ O₂ := mem_of_mul_self_mem_of_odd
      (odd_orderOf_of_mem hM'odd (Subgroup.pow_mem _ ((le_sup_right : Subgroup.zpowers f ≤ M')
        (Subgroup.mem_zpowers f)) j)) hsq
    exact O₂.mul_mem ho₂ hfj
  have hvK : v ∈ K := by
    have hM'K : M' ≤ K := sup_le (hO₂O₁.trans hO₁K) (Subgroup.zpowers_le.mpr hfK)
    exact hM'K hvM'
  have hvx : σ.x * v = v * σ.x := by
    have hM'C : M' ≤ Subgroup.centralizer ({σ.x} : Set G) :=
      sup_le inf_le_right (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hfx))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hM'C hvM')).symm
  refine ⟨v, hvK, hvx, hvx₂, odd_orderOf_of_mem hM'odd hvM', fun w hw => ?_⟩
  have hveq : v = c'⁻¹ * u₂ * i⁻¹ := by
    calc v = c'⁻¹ * (c' * v) := by group
      _ = c'⁻¹ * f := by rw [hcv]
      _ = c'⁻¹ * u₂ * i⁻¹ := by rw [hfeq]; group
  have hc'C : c' ∈ Subgroup.centralizer (e.U : Set G) := hO₁C (hO₂O₁ hc'O₂)
  have hiC : i ∈ Subgroup.centralizer (e.U : Set G) := hO₁C hiO₁
  have hu₂w : u₂ * w * u₂⁻¹ ∈ e.U := conj_mem_of_mem_normalizer' (e.U_normal hu₂K) hw
  have h1 : i⁻¹ * w * i = w := by
    have := Subgroup.mem_centralizer_iff.mp hiC w hw
    calc i⁻¹ * w * i = i⁻¹ * (w * i) := by group
      _ = i⁻¹ * (i * w) := by rw [this]
      _ = w := by group
  have h2 : c'⁻¹ * (u₂ * w * u₂⁻¹) * c' = u₂ * w * u₂⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hc'C _ hu₂w
    calc c'⁻¹ * (u₂ * w * u₂⁻¹) * c' = c'⁻¹ * ((u₂ * w * u₂⁻¹) * c') := by group
      _ = c'⁻¹ * (c' * (u₂ * w * u₂⁻¹)) := by rw [this]
      _ = u₂ * w * u₂⁻¹ := by group
  calc v * w * v⁻¹ = c'⁻¹ * (u₂ * (i⁻¹ * w * i) * u₂⁻¹) * c' := by rw [hveq]; group
    _ = (u * u) * w * (u * u)⁻¹ := by rw [h1, h2, hu₂]



private theorem iv913_false_of_lift (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hqd : σ.height = 1)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II34b : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → Odd (Nat.card W) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ∀ v ∈ H ⊓ σ.N, Odd (orderOf v) →
          σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ → v ∈ Subgroup.normalizer (W : Set G) →
            W ≤ ⁅W, Subgroup.zpowers v⁆ → W ≤ oddCoreIn H)
    (h1 : ¬ PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (hab : ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a)
    {v : G} (hvK : v ∈ Subgroup.normalizer (d.R : Set G)) (hxv : σ.x * v = v * σ.x)
    (hx₂v : σ.x₂ * v * σ.x₂⁻¹ = v⁻¹) (hvodd : Odd (orderOf v))
    (hvU : v ∉ Subgroup.centralizer (e.U : Set G)) {n : ℕ} (hcop : Nat.Coprime r n)
    (hvn : v ^ n ∈ Subgroup.centralizer (e.U : Set G)) {a : G} (haA : a ∈ d.P ⊓ e.U)
    (ha1 : a ≠ 1) (hva : v * a = a * v) : False := by
  have h97' := h97
  have h98' := h98
  obtain ⟨hDH₁, hH₁w⟩ := h98
  have hr2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have : Fact r.Prime := ⟨hr.prime⟩
  have : IsKleinFour σ.T := isKleinFour_of_subgroupOf (T_le_H₁ d e hσ) hH₁w.2.1
  have hP₀A : Subgroup.zpowers a ≤ d.P ⊓ e.U := Subgroup.zpowers_le.mpr haA
  obtain ⟨hi, hii, hiii⟩ := σ.lemmaIV911 hσ hr d e h92 h95iii h97' h98' h_II54 h1 hP₀A
  have hTH₀ : σ.T ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := le_sup_right.trans hii
  have key : ∀ y : G, y * a = a * y →
      y ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    intro y hy
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have : a ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hy.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.mpr this hh)
  have hUH₀ : e.U ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := fun w hw =>
    key w (hab w hw a haA.2)
  have hvH₀ := key v hva
  have hvN : v ∈ σ.N := (σ.mem_N_iff v).mpr hxv.symm
  have hvUn : v ∈ Subgroup.normalizer (e.U : Set G) := e.U_normal hvK
  set U₁ := commImage e.U hab hvUn with hU₁
  have hU₁U : U₁ ≤ e.U := commImage_le
  have hUr := isPGroup_U d e
  have hU₁r : IsPGroup r U₁ := hUr.to_le hU₁U
  have hU₁odd := odd_card_of_isPGroup' hr.prime hr2 hU₁r
  have hvinvU : ∀ w ∈ e.U, v⁻¹ * w * v ∈ e.U := fun w hw => by
    have := conj_mem_of_mem_normalizer' (Subgroup.inv_mem _ hvUn) hw
    simpa using this
  have hTU₁ : σ.T ≤ Subgroup.normalizer (U₁ : Set G) := by
    apply σ.T_le_of_mem
    · apply mem_normalizer_of_conj_mem'
      rintro c ⟨w, hw, rfl⟩
      refine ⟨σ.x * w * σ.x⁻¹,
        conj_mem_of_mem_normalizer' (T_le_normalizer_U d e hσ σ.x_mem_T) hw, ?_⟩
      have hxv' : σ.x * v * σ.x⁻¹ = v := by rw [hxv]; group
      calc v * (σ.x * w * σ.x⁻¹) * v⁻¹ * (σ.x * w * σ.x⁻¹)⁻¹ =
          (σ.x * v * σ.x⁻¹) * (σ.x * w * σ.x⁻¹) * (σ.x * v * σ.x⁻¹)⁻¹ *
            (σ.x * w * σ.x⁻¹)⁻¹ := by rw [hxv']
        _ = σ.x * (v * w * v⁻¹ * w⁻¹) * σ.x⁻¹ := by group
    · apply mem_normalizer_of_conj_mem'
      rintro c ⟨w, hw, rfl⟩
      have hw' : σ.x₂ * w * σ.x₂⁻¹ ∈ e.U :=
        conj_mem_of_mem_normalizer' (T_le_normalizer_U d e hσ σ.x₂_mem_T) hw
      refine ⟨v⁻¹ * (σ.x₂ * w * σ.x₂⁻¹)⁻¹ * v, hvinvU _ (e.U.inv_mem hw'), ?_⟩
      have hcomm := hab _ (e.U.inv_mem hw') _ (hvinvU _ hw')
      calc v * (v⁻¹ * (σ.x₂ * w * σ.x₂⁻¹)⁻¹ * v) * v⁻¹ * (v⁻¹ * (σ.x₂ * w * σ.x₂⁻¹)⁻¹ * v)⁻¹ =
          (σ.x₂ * w * σ.x₂⁻¹)⁻¹ * (v⁻¹ * (σ.x₂ * w * σ.x₂⁻¹) * v) := by group
        _ = (v⁻¹ * (σ.x₂ * w * σ.x₂⁻¹) * v) * (σ.x₂ * w * σ.x₂⁻¹)⁻¹ := hcomm
        _ = (σ.x₂ * v * σ.x₂⁻¹)⁻¹⁻¹ * (σ.x₂ * w * σ.x₂⁻¹) * (σ.x₂ * v * σ.x₂⁻¹)⁻¹ *
            (σ.x₂ * w * σ.x₂⁻¹)⁻¹ := by rw [hx₂v, inv_inv, inv_inv]
        _ = σ.x₂ * (v * w * v⁻¹ * w⁻¹) * σ.x₂⁻¹ := by group
  have hvU₁ : v ∈ Subgroup.normalizer (U₁ : Set G) := by
    apply mem_normalizer_of_conj_mem'
    rintro c ⟨w, hw, rfl⟩
    refine ⟨v * w * v⁻¹, conj_mem_of_mem_normalizer' hvUn hw, by group⟩
  have hU₁comm := commImage_le_commutator hr.prime hab hUr hvUn hcop hvn
  have hU₁O : U₁ ≤ oddCoreIn (Subgroup.normalizer (Subgroup.zpowers a : Set G)) := by
    rcases hII.qd_or_d_of_three _ hTH₀ (Or.inr hqd) hi with hQD | hDw
    · have hne := normalizer_zpowers_ne_top d hσ hr haA.1 ha1
      obtain ⟨t, ht⟩ : ∃ t, t = σ.x₂ * v := ⟨_, rfl⟩
      have hx₂inv := σ.x₂_inv' hσ
      have htH₀ : t ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) :=
        ht ▸ Subgroup.mul_mem _ (hTH₀ σ.x₂_mem_T) hvH₀
      have htN : t ∈ σ.N := ht ▸ σ.N.mul_mem (σ.x₂_mem_N hσ) hvN
      have htt : t * t = 1 := by
        calc t * t = σ.x₂ * v * σ.x₂⁻¹ * v := by rw [ht, hx₂inv]; group
          _ = 1 := by rw [hx₂v]; group
      have hv2 : ∀ y : G, y = v → orderOf y = 2 → False := by
        rintro y rfl hy
        rw [hy] at hvodd
        exact absurd hvodd (by decide)
      have ht1 : t ≠ 1 := by
        intro h
        have h' : σ.x₂ * v = 1 := ht ▸ h
        have : v = σ.x₂ := (eq_inv_of_mul_eq_one_right h').trans hx₂inv
        exact hv2 σ.x₂ this.symm hσ.x₂_order
      have hxt : σ.x * t = t * σ.x := by
        rw [ht]
        calc σ.x * (σ.x₂ * v) = σ.x₂ * (σ.x * v) := by
              rw [← mul_assoc, hσ.commute, mul_assoc]
          _ = σ.x₂ * v * σ.x := by rw [hxv, mul_assoc]
      have hxt' : σ.x ≠ t := by
        intro h
        have hv : v = σ.x₂ * σ.x := by
          calc v = σ.x₂ * (σ.x₂ * v) := by
                rw [← mul_assoc, ← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one, one_mul]
            _ = σ.x₂ * σ.x := by rw [← ht, h]
        have hsq : (σ.x₂ * σ.x) ^ 2 = 1 := by
          rw [pow_two]
          calc σ.x₂ * σ.x * (σ.x₂ * σ.x) = σ.x₂ * (σ.x * σ.x₂) * σ.x := by group
            _ = σ.x₂ * (σ.x₂ * σ.x) * σ.x := by rw [hσ.commute]
            _ = (σ.x₂ * σ.x₂) * (σ.x * σ.x) := by group
            _ = 1 := by
                have h1 : σ.x₂ * σ.x₂ = 1 := by
                  rw [← pow_two, ← hσ.x₂_order, pow_orderOf_eq_one]
                have h2 : σ.x * σ.x = 1 := by
                  rw [← pow_two, ← hσ.x_order, pow_orderOf_eq_one]
                rw [h1, h2, one_mul]
        have hne1 : σ.x₂ * σ.x ≠ 1 := by
          intro h1
          apply hσ.x_ne_x₂
          calc σ.x = σ.x₂⁻¹ := (eq_inv_of_mul_eq_one_right h1)
            _ = σ.x₂ := hx₂inv
        exact hv2 _ hv.symm (orderOf_eq_prime hsq hne1)
      have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
      have hKl := isKleinFour_closure_pair' hσ.x_order ht2 hxt hxt'
      have hT'H₀ : Subgroup.closure ({σ.x, t} : Set G) ≤
          Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
        rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact hTH₀ σ.x_mem_T
        · exact htH₀
      have hWI1 := hII.workingI _ hne hQD σ.x (hTH₀ σ.x_mem_T) hσ.x_order σ.T hTH₀
        ‹IsKleinFour σ.T› σ.x_mem_T
      have hWI2 := hII.workingI _ hne hQD σ.x (hTH₀ σ.x_mem_T) hσ.x_order _ hT'H₀ hKl
        (Subgroup.subset_closure (Set.mem_insert _ _))
      rintro c ⟨w, hw, rfl⟩
      have hwO := ON_inf_le_oddCoreIn_inf_N (σ := σ) (Subgroup.normalizer
        (Subgroup.zpowers a : Set G)) ⟨U_le_ON d e hw, hUH₀ hw⟩
      have htw := conj_mem_of_mem_normalizer' (g := t)
        (le_normalizer_oddCoreIn _ (⟨htH₀, htN⟩ : t ∈ Subgroup.normalizer
          (Subgroup.zpowers a : Set G) ⊓ Subgroup.centralizer ({σ.x} : Set G))) hwO
      have h1 := hWI1 (Subgroup.commutator_mem_commutator (σ.T.inv_mem σ.x₂_mem_T) htw)
      have h2 := hWI2 (Subgroup.commutator_mem_commutator
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hwO)
      have e' : v * w * v⁻¹ * w⁻¹ = ⁅σ.x₂⁻¹, t * w * t⁻¹⁆ * ⁅t, w⁆ := by
        rw [ht]
        simp only [commutatorElement_def]
        group
      rw [e']
      exact Subgroup.mul_mem _ h1 h2
    · exact h_II34b _ hTH₀ hDw U₁ (le_inf (hU₁U.trans hUH₀) (hU₁U.trans (U_le_N d e))) hU₁odd
        hTU₁ v ⟨hvH₀, hvN⟩ hvodd hx₂v hvU₁ hU₁comm
  have hTC := hiii U₁ hU₁O hU₁r hTU₁
  have hvC : ∀ c ∈ U₁, v * c * v⁻¹ = c := by
    intro c hc
    have hc' : v * c * v⁻¹ ∈ U₁ := conj_mem_of_mem_normalizer' hvU₁ hc
    have h1 : σ.x₂ * c * σ.x₂⁻¹ = c := by
      have := Subgroup.mem_centralizer_iff.mp (hTC σ.x₂_mem_T) c hc
      rw [← this]
      group
    have h2 : σ.x₂ * (v * c * v⁻¹) * σ.x₂⁻¹ = v * c * v⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (hTC σ.x₂_mem_T) _ hc'
      rw [← this]
      group
    have h3 : σ.x₂ * (v * c * v⁻¹) * σ.x₂⁻¹ = v⁻¹ * c * v := by
      calc σ.x₂ * (v * c * v⁻¹) * σ.x₂⁻¹ =
          (σ.x₂ * v * σ.x₂⁻¹) * (σ.x₂ * c * σ.x₂⁻¹) * (σ.x₂ * v * σ.x₂⁻¹)⁻¹ := by group
        _ = v⁻¹ * c * v := by rw [hx₂v, h1, inv_inv]
    have hsq : v * v ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h4 : v * c * v⁻¹ = v⁻¹ * c * v := h2.symm.trans h3
      calc v * v * c = v * (v * c * v⁻¹) * v := by group
        _ = v * (v⁻¹ * c * v) * v := by rw [h4]
        _ = c * (v * v) := by group
    have := Subgroup.mem_centralizer_singleton_iff.mp (mem_of_mul_self_mem_of_odd hvodd hsq)
    rw [this]
    group
  apply hvU
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have he := eq_one_of_conj_commutator hr.prime hUr hw hcop hvn
    (hU₁U ⟨w, hw, rfl⟩) (hvC _ ⟨w, hw, rfl⟩)
  calc w * v = (v * w * v⁻¹ * w⁻¹)⁻¹ * v * w := by group
    _ = v * w := by rw [he, inv_one, one_mul]

end UV2

variable (σ) in
theorem lemmaIV912 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hqd : σ.height = 1) (e : IV9UV d)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II417 : ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆)
    (h_II34a : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → IsPGroup r W → (∀ w ∈ W, w ^ r = 1) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ⁅W, W⁆ ≤ oddCoreIn H)
    (h1 : ¬ PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁)) :
    ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a := by
  by_contra hab
  exact iv912_false d e hσ hII hr hqd h92 h95iii h97 h98 h_II54 h_II417 h_II34a h1 hab

variable (σ) in
theorem lemmaIV913 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hqd : σ.height = 1) (e : IV9UV d)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II510 : ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r →
      ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
        u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
        u ∉ Subgroup.centralizer (W : Set G) ∧
        σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) ∧
        ∃ a ∈ W ⊓ Subgroup.centralizer {σ.x₂}, a ≠ 1 ∧ u * a = a * u)
    (h_II34b : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → Odd (Nat.card W) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ∀ v ∈ H ⊓ σ.N, Odd (orderOf v) →
          σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ → v ∈ Subgroup.normalizer (W : Set G) →
            W ≤ ⁅W, Subgroup.zpowers v⁆ → W ≤ oddCoreIn H)
    (h1 : ¬ PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁)) :
    ¬ ∀ a ∈ e.U, ∀ b ∈ e.U, a * b = b * a := by
  intro hab
  have h97' := h97
  have h98' := h98
  obtain ⟨hexp, -, hPU, hCV, -⟩ := h97
  obtain ⟨hDH₁, hH₁w⟩ := h98
  have hcen : ∀ Y : Subgroup G, Y ≤ oddCoreIn e.H₁ → IsPGroup r Y →
      σ.T ≤ Subgroup.normalizer (Y : Set G) → σ.T ≤ Subgroup.centralizer (Y : Set G) :=
    fun Y hYO hY hTY => T_le_centralizer_of_not_constrained' hσ hr.prime (T_le_H₁ d e hσ) h92 h1
      hYO hY hTY
  have hcardV := card_V d e hσ hr hCV hexp hDH₁ hH₁w h_II54 hcen
  obtain ⟨hidx, -⟩ := iv910_abelian d e hσ hII hr hexp hPU hCV hDH₁ hH₁w h_II54 hcen
    hcardV hab
  have hA : d.P ⊓ e.U = e.U ⊓ Subgroup.centralizer {σ.x₂} := hPU.trans (C_inf_U_eq d e)
  rw [hA] at hidx
  obtain ⟨u, huK, s, k, hs, hs2, hsr, husk, hu1, hinv, a, haW, ha1, hua⟩ :=
    h_II510 e.U e.U_le e.U_normal hab hexp e.U_centralizer hidx
  have hodd : Odd (s ^ k) := (hs.eq_two_or_odd'.resolve_left hs2).pow
  obtain ⟨v, hvK, hxv, hx₂v, hvodd, hvact⟩ := exists_lift d e hσ hII hr hqd huK hodd husk hinv
  obtain ⟨q, hq⟩ : ∃ q, q = u * u := ⟨_, rfl⟩
  rw [← hq] at hvact
  have hqK : q ∈ Subgroup.normalizer (d.R : Set G) := hq ▸ Subgroup.mul_mem _ huK huK
  have hvpow : ∀ n : ℕ, ∀ w ∈ e.U, v ^ n * w * (v ^ n)⁻¹ = q ^ n * w * (q ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      have hw' : q ^ n * w * (q ^ n)⁻¹ ∈ e.U :=
        conj_mem_of_mem_normalizer' (e.U_normal (Subgroup.pow_mem _ hqK n)) hw
      calc v ^ (n + 1) * w * (v ^ (n + 1))⁻¹ = v * (v ^ n * w * (v ^ n)⁻¹) * v⁻¹ := by
            rw [pow_succ']; group
        _ = v * (q ^ n * w * (q ^ n)⁻¹) * v⁻¹ := by rw [ih w hw]
        _ = q * (q ^ n * w * (q ^ n)⁻¹) * q⁻¹ := hvact _ hw'
        _ = q ^ (n + 1) * w * (q ^ (n + 1))⁻¹ := by rw [pow_succ']; group
  have hcentr : ∀ y : G, (∀ w ∈ e.U, y * w * y⁻¹ = w) →
      y ∈ Subgroup.centralizer (e.U : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    calc w * y = y * w * y⁻¹ * y := by rw [hy w hw]
      _ = y * w := by group
  have hconj : ∀ y : G, y ∈ Subgroup.centralizer (e.U : Set G) → ∀ w ∈ e.U, y * w * y⁻¹ = w := by
    intro y hy w hw
    rw [← Subgroup.mem_centralizer_iff.mp hy w hw]
    group
  have hvU : v ∉ Subgroup.centralizer (e.U : Set G) := by
    intro hv
    apply hu1
    have hu2 : u * u ∈ Subgroup.centralizer (e.U : Set G) := by
      rw [← hq]
      apply hcentr
      intro w hw
      rw [← hvact w hw]
      exact hconj v hv w hw
    obtain ⟨j, hj⟩ := hodd
    have e1 : u = u ^ (s ^ k) * ((u * u) ^ j)⁻¹ := by
      rw [hj, ← pow_two, ← pow_mul]
      group
    rw [e1]
    exact Subgroup.mul_mem _ husk (Subgroup.inv_mem _ (Subgroup.pow_mem _ hu2 j))
  have hvn : v ^ (s ^ k) ∈ Subgroup.centralizer (e.U : Set G) := by
    apply hcentr
    intro w hw
    rw [hvpow _ w hw, hq, (Commute.refl u).mul_pow]
    have h1 := hconj _ husk w hw
    have e1 : u ^ s ^ k * u ^ s ^ k * w * (u ^ s ^ k * u ^ s ^ k)⁻¹ =
        u ^ s ^ k * (u ^ s ^ k * w * (u ^ s ^ k)⁻¹) * (u ^ s ^ k)⁻¹ := by group
    rw [e1, h1, h1]
  have hcop : Nat.Coprime r (s ^ k) :=
    Nat.Coprime.pow_right k ((Nat.coprime_primes hr.prime hs).mpr hsr.symm)
  have haA : a ∈ d.P ⊓ e.U := hA ▸ haW
  have hva : v * a = a * v := by
    have h1 : v * a * v⁻¹ = a := by
      rw [hvact a haW.1, hq]
      calc (u * u) * a * (u * u)⁻¹ = u * (u * a) * (u * u)⁻¹ := by group
        _ = u * (a * u) * (u * u)⁻¹ := by rw [hua]
        _ = (u * a) * u * (u * u)⁻¹ := by group
        _ = (a * u) * u * (u * u)⁻¹ := by rw [hua]
        _ = a := by group
    calc v * a = v * a * v⁻¹ * v := by group
      _ = a * v := by rw [h1]
  exact iv913_false_of_lift d e hσ hII hr hqd h92 h95iii h97' h98' h_II54 h_II34b h1 hab hvK hxv
    hx₂v hvodd hvU hcop hvn haA ha1 hva

variable (σ) in
theorem lemmaIV99 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) (hqd : σ.height = 1) (e : IV9UV d)
    (h92 : (∃ X : Subgroup G, IsSylowOf r X (oddCoreIn e.H₁) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G)) →
      PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁))
    (h95iii : 3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.centralizer (d.P : Set G))))
    (h97 : (∀ u ∈ e.U, u ^ r = 1) ∧ ⁅⁅e.U, e.U⁆, e.U⁆ = ⊥ ∧ d.P ⊓ e.U = σ.C ⊓ e.U ∧
      σ.C ⊓ e.V = ⊥ ∧ d.P ⊓ e.U ≠ ⊥)
    (h98 : σ.D ≤ e.H₁ ∧ IsDGroupWrt (σ.T.subgroupOf e.H₁))
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    (h_II417 : ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆)
    (h_II34a : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → IsPGroup r W → (∀ w ∈ W, w ^ r = 1) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ⁅W, W⁆ ≤ oddCoreIn H)
    (h_II510 : ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ a ∈ W, ∀ b ∈ W, a * b = b * a) → (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      (W ⊓ Subgroup.centralizer {σ.x₂}).relIndex W = r →
      ∃ u ∈ Subgroup.normalizer (d.R : Set G), ∃ s k : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ r ∧
        u ^ (s ^ k) ∈ Subgroup.centralizer (W : Set G) ∧
        u ∉ Subgroup.centralizer (W : Set G) ∧
        σ.x₂ * u * σ.x₂⁻¹ * u ∈ Subgroup.centralizer (W : Set G) ∧
        ∃ a ∈ W ⊓ Subgroup.centralizer {σ.x₂}, a ≠ 1 ∧ u * a = a * u)
    (h_II34b : ∀ H : Subgroup G, σ.T ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ W : Subgroup G, W ≤ H ⊓ σ.N → Odd (Nat.card W) →
        σ.T ≤ Subgroup.normalizer (W : Set G) → ∀ v ∈ H ⊓ σ.N, Odd (orderOf v) →
          σ.x₂ * v * σ.x₂⁻¹ = v⁻¹ → v ∈ Subgroup.normalizer (W : Set G) →
            W ≤ ⁅W, Subgroup.zpowers v⁆ → W ≤ oddCoreIn H) :
    PConstrainedWithin r e.H₁ (CFSG.oddCore e.H₁) := by
  by_contra h1
  exact σ.lemmaIV913 hσ hII hr d hqd e h92 h95iii h97 h98 h_II54 h_II510 h_II34b h1
    (σ.lemmaIV912 hσ hII hr d hqd e h92 h95iii h97 h98 h_II54 h_II417 h_II34a h1)

end Setting

end CFSG.ABGTheoremB
