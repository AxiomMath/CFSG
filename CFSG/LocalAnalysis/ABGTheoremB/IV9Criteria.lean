module

public import CFSG.LocalAnalysis.ABGTheoremB.Statements
import CFSG.LocalAnalysis.ABGTheoremB.IV2
import CFSG.GroupTheory.ABGLocalTools.Criteria
import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem mem_of_mul_self_mem_of_odd_orderOf {K : Subgroup G} {y : G} (hy : Odd (orderOf y))
    (h : y * y ∈ K) : y ∈ K := by
  obtain ⟨m, hm⟩ := hy
  have : y = (y * y) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [this]
  exact K.pow_mem h _

private theorem odd_card_of_isPGroup_of_ne_two [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup G} (hX : IsPGroup r X) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

private theorem eq_one_of_isPGroup_two_of_mem_odd {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card B)) {a : G} (haA : a ∈ A) (haB : a ∈ B) : a = 1 := by
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

private theorem mem_map_conj_iff_mem {U : Subgroup G} {u y : G} :
    y ∈ U.map (MulAut.conj u).toMonoidHom ↔ u⁻¹ * y * u ∈ U := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hw
  · intro h
    exact ⟨u⁻¹ * y * u, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem le_normalizer_closure_of_conj_mem {A : Subgroup G} {s : Set G}
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

private theorem inv_ne_self_of_odd_orderOf {y : G} (hy : Odd (orderOf y)) (h1 : y ≠ 1) :
    y⁻¹ ≠ y := by
  intro h
  apply h1
  have h' : y * y ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel y
  exact (Subgroup.mem_bot).mp (mem_of_mul_self_mem_of_odd_orderOf hy h')

private theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    IsSylowOf p (P.map (MulAut.conj g).toMonoidHom) K := by
  apply isSylowOf_of_card
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hP.le hy)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hP.card_eq

private theorem exists_isSylowOf_ge [Finite G] {p : ℕ} [Fact p.Prime] {Q K : Subgroup G}
    (hQK : Q ≤ K) (hQ : IsPGroup p Q) : ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun q hq => ?_⟩
  exact ⟨⟨q, hQK hq⟩, hS (show (⟨q, hQK hq⟩ : K) ∈ Q.subgroupOf K from hq), rfl⟩

private theorem exists_zpow_eq_zpow_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q]
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

private theorem false_of_isCyclic_mod [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
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
  obtain ⟨m, n, hmn, hm1⟩ := exists_zpow_eq_zpow_of_isCyclic hQp
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
    (odd_card_of_isPGroup_of_ne_two hr hr2 hF).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard F (F.zpow_mem hbF n))
  have h4 : b ^ n ∈ O := mem_of_mul_self_mem_of_odd_orderOf hodd h3
  apply hmO
  have := O.mul_mem h4 (O.inv_mem h1)
  simpa using this

private theorem conj_mem_fourInverted {U : Subgroup G} {e s t k : G}
    (he : e ∈ Subgroup.normalizer (U : Set G)) (hk : k ∈ fourInverted U s t) :
    e * k * e⁻¹ ∈ fourInverted U (e * s * e⁻¹) (e * t * e⁻¹) := by
  obtain ⟨hkU, hs, ht⟩ := hk
  refine ⟨(Subgroup.mem_normalizer_iff.mp he k).mp hkU, ?_, ?_⟩
  · calc e * s * e⁻¹ * (e * k * e⁻¹) * (e * s * e⁻¹)⁻¹ = e * (s * k * s⁻¹) * e⁻¹ := by group
      _ = e * k * e⁻¹ := by rw [hs]
  · calc e * t * e⁻¹ * (e * k * e⁻¹) * (e * t * e⁻¹)⁻¹ = e * (t * k * t⁻¹) * e⁻¹ := by group
      _ = (e * k * e⁻¹)⁻¹ := by rw [ht]; group

private theorem mem_fourInverted_of_mem {T K : Subgroup G} [IsKleinFour T] {a c b k : G}
    (ha : a ∈ T) (hc : c ∈ T) (hb : b ∈ T) (ha1 : a ≠ 1) (hc1 : c ≠ 1) (hac : a ≠ c) (hb1 : b ≠ 1)
    (hba : b ≠ a) (hk : k ∈ fourInverted K a c) : k ∈ fourInverted K a b := by
  obtain ⟨hkK, hka, hkc⟩ := hk
  refine ⟨hkK, hka, ?_⟩
  rcases kleinFour_mem_cases ha hc hb ha1 hc1 hac with rfl | rfl | rfl | rfl
  · exact absurd rfl hb1
  · exact absurd rfl hba
  · exact hkc
  · calc a * c * k * (a * c)⁻¹ = a * (c * k * c⁻¹) * a⁻¹ := by group
      _ = (a * k * a⁻¹)⁻¹ := by rw [hkc]; group
      _ = k⁻¹ := by rw [hka]

private theorem exists_isSylowOf_normalized_by_two [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {A P R₀ M : Subgroup G} (hA : IsPGroup 2 A) (hM : Odd (Nat.card M))
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) (hPM : P ≤ Subgroup.normalizer (M : Set G))
    (hP : IsPGroup r P) (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hR₀M : R₀ ≤ M)
    (hR₀ : IsPGroup r R₀) (hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set G))
    (hPR₀ : P ≤ Subgroup.normalizer (R₀ : Set G)) :
    ∃ U : Subgroup G, IsSylowOf r U M ∧ R₀ ≤ U ∧ A ≤ Subgroup.normalizer (U : Set G) ∧
      P ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hYodd : Odd (Nat.card (M ⊔ P : Subgroup G)) :=
    odd_card_sup_of_le_normalizer_of_odd hPM hM (odd_card_of_isPGroup_of_ne_two hr hr2 hP)
  have hAY : A ≤ Subgroup.normalizer ((M ⊔ P : Subgroup G) : Set G) := fun a ha =>
    normalizer_inf_normalizer_le_normalizer_sup M P ⟨hAM ha, hAP ha⟩
  have hAPR : A ≤ Subgroup.normalizer ((P ⊔ R₀ : Subgroup G) : Set G) := fun a ha =>
    normalizer_inf_normalizer_le_normalizer_sup P R₀ ⟨hAP ha, hAR₀ ha⟩
  obtain ⟨W, hW, hPRW, hAW⟩ := exists_isSylowOf_normalized_ge_of_odd hr hA hAY hYodd
    (sup_le le_sup_right (hR₀M.trans le_sup_left)) (hP.to_sup_of_normal_right' hR₀ hPR₀) hAPR
  have hYM : M ⊔ P ≤ Subgroup.normalizer (M : Set G) := sup_le Subgroup.le_normalizer hPM
  refine ⟨W ⊓ M, hW.inf_of_le_normalizer le_sup_left hYM,
    le_inf (le_sup_right.trans hPRW) hR₀M,
    fun a ha => Subgroup.inf_normalizer_le_normalizer_inf ⟨hAW ha, hAM ha⟩,
    fun p hp => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ((le_sup_left.trans hPRW) hp), hPM hp⟩⟩

end General

section Transfer

variable {G : Type u} [Group G]

private theorem isSylowOf_subgroupOf_oddCore_iff [Finite G] {r : ℕ} [Fact r.Prime]
    {K X : Subgroup G} (hXK : X ≤ K) :
    IsSylowOf r (X.subgroupOf K) (CFSG.oddCore K) ↔ IsSylowOf r X (oddCoreIn K) := by
  rw [← isSylowOf_map_subtype_iff K, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK]
  rfl

private theorem subgroupOf_le_normalizer_subgroupOf_iff {A X K : Subgroup G} (hAK : A ≤ K)
    (hXK : X ≤ K) :
    A.subgroupOf K ≤ Subgroup.normalizer (X.subgroupOf K : Set K) ↔
      A ≤ Subgroup.normalizer (X : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hXK]
  constructor
  · intro h a ha
    exact h (show (⟨a, hAK ha⟩ : K) ∈ A.subgroupOf K from ha)
  · intro h a ha
    exact h ha

private theorem mem_centralizer_subgroupOf_iff {X K : Subgroup G} (hXK : X ≤ K) {a : K} :
    a ∈ Subgroup.centralizer (X.subgroupOf K : Set K) ↔
      (a : G) ∈ Subgroup.centralizer (X : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp h ⟨y, hXK hy⟩
        (show (⟨y, hXK hy⟩ : K) ∈ X.subgroupOf K from hy))
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h y hy)

private theorem subgroupOf_le_centralizer_subgroupOf_iff {A X K : Subgroup G} (hAK : A ≤ K)
    (hXK : X ≤ K) :
    A.subgroupOf K ≤ Subgroup.centralizer (X.subgroupOf K : Set K) ↔
      A ≤ Subgroup.centralizer (X : Set G) := by
  constructor
  · intro h a ha
    exact (mem_centralizer_subgroupOf_iff hXK (a := ⟨a, hAK ha⟩)).mp (h ha)
  · intro h a ha
    exact (mem_centralizer_subgroupOf_iff hXK).mpr (h ha)

end Transfer

section Constraint

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

private theorem eq_one_of_mem_centralizer_of_pConstrainedWithin
    (hcon : PConstrainedWithin p H (CFSG.oddCore H)) {A : Subgroup H} (hA : IsPGroup 2 A)
    {X : Subgroup H} (hX : IsSylowOf p X (CFSG.oddCore H)) {a : H} (haA : a ∈ A)
    (haX : a ∈ Subgroup.centralizer (X : Set H)) : a = 1 := by
  have hNK : CFSG.Op_p'p p H ≤ CFSG.oddCore H := hcon.1
  have hKN : CFSG.oddCore H ≤ Subgroup.normalizer (CFSG.Op_p'p p H : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hX₀ := hX.inf_of_le_normalizer hNK hKN
  have hC := hcon.2 _ hX₀
  have haC : a ∈ Subgroup.centralizer ((X ⊓ CFSG.Op_p'p p H : Subgroup H) : Set H) :=
    Subgroup.centralizer_le (fun y hy => hy.1) haX
  exact eq_one_of_isPGroup_two_of_mem_odd hA CFSG.ABGLocalTools.odd_card_oddCore haA
    (hNK (hC haC))

private theorem le_centralizer_of_not_pConstrainedWithin (hp : p ≠ 2) (T : Subgroup H)
    [IsKleinFour T] (S : Sylow 2 H) (hTS : T ≤ S)
    (hZT : ∀ z ∈ Subgroup.center S, (z : S) ^ 2 = 1 → ((z : S) : H) ∈ T)
    (htrans : ∀ t ∈ T, ∀ t' ∈ T, t ≠ 1 → t' ≠ 1 →
      ∃ h ∈ Subgroup.normalizer (T : Set H), h * t * h⁻¹ = t')
    (hcore : CFSG.pPrimeCore p H ≤ CFSG.oddCore H)
    (hncon : ¬ PConstrainedWithin p H (CFSG.oddCore H)) {X : Subgroup H}
    (hX : IsSylowOf p X (CFSG.oddCore H)) (hTX : T ≤ Subgroup.normalizer (X : Set H)) :
    T ≤ Subgroup.centralizer (X : Set H) := by
  have hOn : (CFSG.oddCore H).Normal := CFSG.oddCore_normal H
  set E : Subgroup H := (CFSG.Op_p'p p (CFSG.oddCore H)).map (CFSG.oddCore H).subtype with hE
  have hEn : E.Normal := ConjAct.normal_of_characteristic_of_normal
  have hEO : E ≤ CFSG.oddCore H := Subgroup.map_subtype_le _
  have hON : CFSG.oddCore H ≤ Subgroup.normalizer (E : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hX₀ : IsSylowOf p (X ⊓ E) E := hX.inf_of_le_normalizer hEO hON
  have hTX₀ : T ≤ Subgroup.normalizer ((X ⊓ E : Subgroup H) : Set H) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTX ht, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top t⟩
  have h63 := (pConstrainedWithin_oddCore_four_group_criteria hp T S hTS hZT htrans hcore hX₀
    hTX₀).2 hncon
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  have hTO : T ≤ Subgroup.normalizer (CFSG.oddCore H : Set H) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  exact (two_group_centralizes_sylow_iff CFSG.ABGLocalTools.odd_card_oddCore hT2 hTO hX
    hTX).mpr h63

end Constraint

section Automizer

variable {H : Type*} [Group H] [Finite H]

private theorem exists_conj_eq_of_three_dvd_automizerIndex {T : Subgroup H} [IsKleinFour T]
    (h3 : 3 ∣ automizerIndex T) {t t' : H} (ht : t ∈ T) (ht' : t' ∈ T) (ht1 : t ≠ 1)
    (ht'1 : t' ≠ 1) : ∃ h ∈ Subgroup.normalizer (T : Set H), h * t * h⁻¹ = t' := by
  classical
  rw [automizerIndex_eq_card_range] at h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ψ, hψ⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp ψ.2
  have hφ : orderOf (T.normalizerMonoidHom g) = 3 := by
    rw [hg, Subgroup.orderOf_coe]
    exact hψ
  set φ := T.normalizerMonoidHom g with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hφ1 : φ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hφ
    norm_num at hφ
  have hφφφ : ∀ b : T, φ (φ (φ b)) = b := by
    intro b
    have := congrArg (fun ψ : MulAut T => ψ b) hφ3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hfix : ∀ a : T, a ≠ 1 → φ a ≠ a := by
    intro a ha hφa
    obtain ⟨b, hb⟩ : ∃ b : T, φ b ≠ b := by
      by_contra hcon
      exact hφ1 (MulEquiv.ext fun b => not_not.mp fun h => hcon ⟨b, h⟩)
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hb (map_one φ)
    have hab : a ≠ b := by
      rintro rfl
      exact hb hφa
    have hφb1 : φ b ≠ 1 := fun h => hb1 (φ.injective (h.trans (map_one φ).symm))
    have hφba : φ b ≠ a := fun h => hab (φ.injective (hφa.trans h.symm))
    have hφb : φ b = a * b := IsKleinFour.eq_mul_of_ne_all ha hb1 hab hφb1 hφba hb
    have h2 : φ (φ b) = b := by
      rw [hφb, map_mul, hφa, hφb, ← mul_assoc, IsKleinFour.mul_self, one_mul]
    have h3 := hφφφ b
    rw [h2] at h3
    exact hb h3
  set a : T := ⟨t, ht⟩
  set a' : T := ⟨t', ht'⟩
  have ha1 : a ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ha'1 : a' ≠ 1 := fun h => ht'1 (congrArg Subtype.val h)
  have hφa := hfix a ha1
  have hφa1 : φ a ≠ 1 := fun h => ha1 (φ.injective (h.trans (map_one φ).symm))
  have hφφa1 : φ (φ a) ≠ 1 := fun h => hφa1 (φ.injective (h.trans (map_one φ).symm))
  have hφφa : φ (φ a) ≠ φ a := hfix (φ a) hφa1
  have hφφa' : φ (φ a) ≠ a := by
    intro h
    have h3 := hφφφ a
    rw [h] at h3
    exact hφa h3
  have hsq : φ (φ a) = a * φ a :=
    IsKleinFour.eq_mul_of_ne_all ha1 hφa1 hφa.symm hφφa1 hφφa' hφφa
  have hcoe : ∀ b : T, ((φ b : T) : H) = (g : H) * b * (g : H)⁻¹ := fun b =>
    normalizerMonoidHom_apply_coe T g b
  by_cases h1 : a' = a
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact (congrArg Subtype.val h1).symm
  by_cases h2 : a' = φ a
  · refine ⟨g, g.2, ?_⟩
    rw [← hcoe a]
    exact (congrArg Subtype.val h2).symm
  have h3 : a' = φ (φ a) := by
    rw [hsq]
    exact IsKleinFour.eq_mul_of_ne_all ha1 hφa1 hφa.symm ha'1 h1 h2
  refine ⟨(g : H) * g, Subgroup.mul_mem _ g.2 g.2, ?_⟩
  have : ((φ (φ a) : T) : H) = (g : H) * g * t * ((g : H) * g)⁻¹ := by
    rw [hcoe, hcoe]
    change (g : H) * ((g : H) * t * (g : H)⁻¹) * (g : H)⁻¹ = _
    group
  rw [← this]
  exact (congrArg Subtype.val h3).symm

end Automizer

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem mem_T_of_central_of_D_le (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {S₁ : Subgroup G}
    (hS₁ : IsPGroup 2 S₁) (hDS₁ : σ.D ≤ S₁) {w : G} (hw : w ∈ S₁)
    (hwc : ∀ s ∈ S₁, w * s = s * w) (hw2 : w ^ 2 = 1) : w ∈ σ.T := by
  have hx₂S₁ : σ.x₂ ∈ S₁ := hDS₁ ((σ.T_le_D hσ) σ.x₂_mem_T)
  rcases hσ.sylow with ⟨-, n, hn, hiso⟩ | hW
  · obtain ⟨S₂, hS₁₂⟩ := hS₁.exists_le_sylow
    have hDS₂ : σ.D ≤ S₂ := hDS₁.trans hS₁₂
    obtain ⟨f⟩ := hiso S₂
    set z' : S₂ := f (CFSG.Semidihedral.r n) ^ (2 ^ (n - 1) / 2) with hz'
    have hz'c : z' ∈ Subgroup.center S₂ := CFSG.Semidihedral.Local.image_z_mem_center hn f
    have hz'o : orderOf z' = 2 := CFSG.Semidihedral.Local.image_z_orderOf (by omega) f
    obtain ⟨-, hcent⟩ := hII.center_involution_of_sylow S₂ hDS₂
    have hcenter : ∀ y : S₂, y ∈ Subgroup.center S₂ → (y : G) ∈ centerOf (S₂ : Subgroup G) := by
      intro y hy
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have := Subgroup.mem_center_iff.mp hy ⟨h, hh⟩
      exact congrArg Subtype.val this
    have hz'x : ((z' : S₂) : G) = σ.x := by
      apply hcent _ (hcenter z' hz'c)
      rw [Subgroup.orderOf_coe]
      exact hz'o
    set x₂' : S₂ := ⟨σ.x₂, hS₁₂ hx₂S₁⟩
    have hx₂'o : orderOf x₂' = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hσ.x₂_order
    have hx₂'z : x₂' ∉ Subgroup.zpowers z' := by
      intro hmem
      have hc : x₂' ∈ Subgroup.center S₂ := (Subgroup.zpowers_le.mpr hz'c) hmem
      exact hσ.x_ne_x₂ (hcent σ.x₂ (hcenter x₂' hc) hσ.x₂_order).symm
    obtain ⟨hC, -⟩ := CFSG.Semidihedral.Local.centralizer_eq_closure hn f x₂' hx₂'o hx₂'z
    set w' : S₂ := ⟨w, hS₁₂ hw⟩
    have hw'C : w' ∈ Subgroup.centralizer {x₂'} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hwc σ.x₂ hx₂S₁)
    rw [hC] at hw'C
    have hle : Subgroup.closure {z', x₂'} ≤ σ.T.comap (SubgroupClass.subtype S₂) := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · change ((z' : S₂) : G) ∈ σ.T
        rw [hz'x]
        exact σ.x_mem_T
      · exact σ.x₂_mem_T
    exact hle hw'C
  · have hh : σ.height ≠ 1 := by
      have := hW.1
      omega
    have hDS : σ.D = σ.S := le_antisymm σ.D_le_S (le_inf le_rfl (hσ.T_normal hh))
    have hS₁S : S₁ = σ.S := σ.S.is_maximal' hS₁ (hDS ▸ hDS₁)
    by_cases hw1 : w = 1
    · rw [hw1]
      exact σ.T.one_mem
    have hwo : orderOf w = 2 := orderOf_eq_prime hw2 hw1
    have hwS : w ∈ centerOf (σ.S : Subgroup G) :=
      ⟨hS₁S ▸ hw, Subgroup.mem_centralizer_iff.mpr fun s hs => (hwc s (hS₁S ▸ hs)).symm⟩
    rw [hσ.center_involution w hwS hwo]
    exact σ.x_mem_T

private theorem isPGroup_two_T (hσ : σ.IsValid) : IsPGroup 2 σ.T :=
  σ.S.isPGroup'.to_le (σ.T_le_S hσ)

private theorem familyMstar_exists_sylow (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    {K : Subgroup G} (hK : K ∈ σ.familyMstar r) :
    ∃ S : Sylow 2 K, σ.T.subgroupOf K ≤ S ∧
      ∀ z ∈ Subgroup.center S, (z : S) ^ 2 = 1 → ((z : S) : K) ∈ σ.T.subgroupOf K := by
  have hDK : σ.D ≤ K := hK.2.1
  have hD2 : IsPGroup 2 (σ.D.subgroupOf K) := (σ.S.isPGroup'.to_le σ.D_le_S).comap_subtype
  obtain ⟨S, hS⟩ := hD2.exists_le_sylow
  refine ⟨S, (Subgroup.comap_mono (σ.T_le_D hσ)).trans hS, fun z hz hz2 => ?_⟩
  have hS₁ : IsPGroup 2 ((S : Subgroup K).map K.subtype) := S.isPGroup'.map K.subtype
  have hDS₁ : σ.D ≤ (S : Subgroup K).map K.subtype := fun d hd =>
    ⟨⟨d, hDK hd⟩, hS (show (⟨d, hDK hd⟩ : K) ∈ σ.D.subgroupOf K from hd), rfl⟩
  have hw : (((z : S) : K) : G) ∈ (S : Subgroup K).map K.subtype := ⟨(z : S), (z : S).2, rfl⟩
  have hwc : ∀ s ∈ (S : Subgroup K).map K.subtype,
      (((z : S) : K) : G) * s = s * (((z : S) : K) : G) := by
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.mem_center_iff.mp hz ⟨s, hs⟩
    exact (congrArg (fun y : S => ((y : K) : G)) this).symm
  have hw2 : (((z : S) : K) : G) ^ 2 = 1 := by
    have := congrArg (fun y : S => ((y : K) : G)) hz2
    simpa using this
  exact σ.mem_T_of_central_of_D_le hσ hII hS₁ hDS₁ hw hwc hw2

theorem constrained_iff_exists_sylow_not_centralized (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {K : Subgroup G} (hK : K ∈ σ.familyMstar r) :
    PConstrainedWithin r K (CFSG.oddCore K) ↔
      ∃ X : Subgroup G, IsSylowOf r X (oddCoreIn K) ∧
        σ.T ≤ Subgroup.normalizer (X : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (X : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hK.2.1
  have hT2 : IsPGroup 2 σ.T := σ.isPGroup_two_T hσ
  constructor
  · intro hcon
    obtain ⟨X, hX, hTX⟩ := exists_isSylowOf_normalized_of_odd hr hT2
      (hTK.trans (le_normalizer_oddCoreIn K)) (odd_card_oddCoreIn K)
    refine ⟨X, hX, hTX, fun hTC => ?_⟩
    have hXK : X ≤ K := hX.le.trans (oddCoreIn_le K)
    have hx := eq_one_of_mem_centralizer_of_pConstrainedWithin hcon
      (hT2.comap_subtype (K := K)) ((isSylowOf_subgroupOf_oddCore_iff hXK).mpr hX)
      (a := ⟨σ.x, hTK σ.x_mem_T⟩) σ.x_mem_T
      ((mem_centralizer_subgroupOf_iff hXK).mpr (hTC σ.x_mem_T))
    have hxo := hσ.x_order
    rw [show σ.x = 1 from congrArg Subtype.val hx, orderOf_one] at hxo
    norm_num at hxo
  · rintro ⟨X, hX, hTX, hnot⟩
    by_contra hncon
    apply hnot
    have hXK : X ≤ K := hX.le.trans (oddCoreIn_le K)
    obtain ⟨S, hTS, hZT⟩ := σ.familyMstar_exists_sylow hσ hII hK
    have hKw := hK.2.2.1
    have : IsKleinFour (σ.T.subgroupOf K) := hKw.2.1
    have hodd : Odd (Nat.card (CFSG.pPrimeCore r K)) := by
      have := hK.2.2.2
      rwa [pPrimeCoreIn, Subgroup.card_map_of_injective K.subtype_injective] at this
    have hcore : CFSG.pPrimeCore r K ≤ CFSG.oddCore K := le_oddCore_of_normal inferInstance hodd
    have h := le_centralizer_of_not_pConstrainedWithin hr2 (σ.T.subgroupOf K) S hTS hZT
      (fun t ht t' ht' h1 h2 => exists_conj_eq_of_three_dvd_automizerIndex hKw.2.2 ht ht' h1 h2)
      hcore hncon ((isSylowOf_subgroupOf_oddCore_iff hXK).mpr hX)
      ((subgroupOf_le_normalizer_subgroupOf_iff hTK hXK).mpr hTX)
    exact (subgroupOf_le_centralizer_subgroupOf_iff hTK hXK).mp h
private theorem isKleinFour_T_of_mem_familyMstar (hσ : σ.IsValid) {r : ℕ} {K : Subgroup G}
    (hK : K ∈ σ.familyMstar r) : IsKleinFour σ.T := by
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hK.2.1
  have h4 : IsKleinFour (σ.T.subgroupOf K) := hK.2.2.1.2.1
  have e := Subgroup.subgroupOfEquivOfLe hTK
  exact ⟨by rw [← Nat.card_congr e.toEquiv]; exact h4.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact h4.exponent_two⟩

theorem eq_one_of_mem_centralizer_of_constrained (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    {K : Subgroup G} (hK : K ∈ σ.familyMstar r)
    (hcon : PConstrainedWithin r K (CFSG.oddCore K)) {X : Subgroup G}
    (hX : IsSylowOf r X (oddCoreIn K)) {t : G} (htT : t ∈ σ.T)
    (htX : t ∈ Subgroup.centralizer (X : Set G)) : t = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hK.2.1
  have hXK : X ≤ K := hX.le.trans (oddCoreIn_le K)
  exact congrArg Subtype.val (eq_one_of_mem_centralizer_of_pConstrainedWithin hcon
    ((σ.isPGroup_two_T hσ).comap_subtype (K := K))
    ((isSylowOf_subgroupOf_oddCore_iff hXK).mpr hX) (a := ⟨t, hTK htT⟩) htT
    ((mem_centralizer_subgroupOf_iff hXK).mpr htX))

theorem le_centralizer_of_not_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {K : Subgroup G} (hK : K ∈ σ.familyMstar r)
    (hncon : ¬ PConstrainedWithin r K (CFSG.oddCore K)) {Y : Subgroup G}
    (hYO : Y ≤ oddCoreIn K) (hY : IsPGroup r Y) (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) :
    σ.T ≤ Subgroup.centralizer (Y : Set G) := by
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hK.2.1
  obtain ⟨X, hX, hYX, hTX⟩ := exists_isSylowOf_normalized_ge_of_odd hr (σ.isPGroup_two_T hσ)
    (hTK.trans (le_normalizer_oddCoreIn K)) (odd_card_oddCoreIn K) hYO hY hTY
  by_contra hTY'
  apply hncon
  refine (σ.constrained_iff_exists_sylow_not_centralized hσ hII hr hr2 hK).mpr
    ⟨X, hX, hTX, fun hTC => hTY' (hTC.trans (Subgroup.centralizer_le fun y hy => hYX hy))⟩

private theorem exists_fourInverted_of_not_mem_centralizer (hσ : σ.IsValid) [IsKleinFour σ.T]
    {U : Subgroup G} (hU : Odd (Nat.card U)) (hTU : σ.T ≤ Subgroup.normalizer (U : Set G))
    {t : G} (htT : t ∈ σ.T) (ht1 : t ≠ 1) (htU : t ∉ Subgroup.centralizer (U : Set G)) :
    ∃ s ∈ σ.T, s ≠ 1 ∧ s ≠ t ∧ ∃ k ∈ fourInverted U s t, k ≠ 1 := by
  have hx1 : σ.x ≠ 1 := fun h => by
    have := hσ.x_order
    rw [h, orderOf_one] at this
    norm_num at this
  have hx₂1 : σ.x₂ ≠ 1 := fun h => by
    have := hσ.x₂_order
    rw [h, orderOf_one] at this
    norm_num at this
  obtain ⟨s₀, hs₀T, hs₀1, hs₀t⟩ : ∃ s₀ ∈ σ.T, s₀ ≠ 1 ∧ s₀ ≠ t := by
    by_cases hxt : σ.x = t
    · exact ⟨σ.x₂, σ.x₂_mem_T, hx₂1, fun h => hσ.x_ne_x₂ (hxt.trans h.symm)⟩
    · exact ⟨σ.x, σ.x_mem_T, hx1, hxt⟩
  by_contra hcon
  have htriv : ∀ s ∈ σ.T, s ≠ 1 → s ≠ t → ∀ k ∈ fourInverted U s t, k = 1 := by
    intro s hs hs1 hst k hk
    by_contra hk1
    exact hcon ⟨s, hs, hs1, hst, k, hk, hk1⟩
  have htt : t * t = 1 := kleinFour_mul_self htT
  have hts₀1 : t * s₀ ≠ 1 := by
    intro h
    apply hs₀t
    calc s₀ = t * (t * s₀) := by rw [← mul_assoc, htt, one_mul]
      _ = t := by rw [h, mul_one]
  have hts₀t : t * s₀ ≠ t := fun h => hs₀1 (by simpa using h)
  obtain ⟨-, hdec⟩ := four_group_T_decomposition hU hTU htT hs₀T ht1 hs₀1 (Ne.symm hs₀t)
  apply htU
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : u ∈ (U : Set G) := hu
  rw [hdec] at hu'
  obtain ⟨v, hv, u₃, hu₃, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨w, hw, u₂, hu₂, rfl⟩ := Set.mem_mul.mp hv
  obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Set.mem_mul.mp hw
  rw [htriv s₀ hs₀T hs₀1 hs₀t u₂ hu₂, htriv (t * s₀) (σ.T.mul_mem htT hs₀T) hts₀1 hts₀t u₃ hu₃,
    mul_one, mul_one]
  have h0 : t * u₀ = u₀ * t := Subgroup.mem_centralizer_iff.mp hu₀.2 t htT
  have h1 : t * u₁ = u₁ * t := by
    calc t * u₁ = t * u₁ * t⁻¹ * t := by group
      _ = u₁ * t := by rw [hu₁.2.1]
  calc u₀ * u₁ * t = u₀ * (t * u₁) := by rw [mul_assoc, h1]
    _ = t * (u₀ * u₁) := by rw [← mul_assoc, ← h0, mul_assoc]

private theorem exists_fourInverted_inf_centralizer [IsKleinFour σ.T] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {P U : Subgroup G} (hPC : IsSylowOf r P σ.C)
    (hU : IsPGroup r U) (hTU : σ.T ≤ Subgroup.normalizer (U : Set G))
    (hPU : P ≤ Subgroup.normalizer (U : Set G)) {a b : G} (haT : a ∈ σ.T) (hbT : b ∈ σ.T)
    (hb1 : b ≠ 1) {u₀ : G} (hu₀ : u₀ ∈ fourInverted U a b) (hu₀1 : u₀ ≠ 1) :
    ∃ v ∈ fourInverted (U ⊓ Subgroup.centralizer (P : Set G)) a b, v ≠ 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hP : IsPGroup r P := hPC.isPGroup
  have hPT : ∀ y ∈ P, ∀ t ∈ σ.T, t * y = y * t := fun y hy t ht =>
    Subgroup.mem_centralizer_iff.mp (hPC.le hy) t ht
  have hab : a * b = b * a := kleinFour_comm haT hbT
  have hbo : orderOf b = 2 := kleinFour_orderOf hbT hb1
  have hWp : IsPGroup r (P ⊔ U : Subgroup G) := hP.to_sup_of_normal_right' hU hPU
  have hWset : ((P ⊔ U : Subgroup G) : Set G) = (P : Set G) * U :=
    Subgroup.coe_mul_of_left_le_normalizer_right P U hPU
  set Ka : Subgroup G := (P ⊔ U) ⊓ Subgroup.centralizer {a} with hKa
  have hKap : IsPGroup r Ka := hWp.to_le inf_le_left
  have hKaodd : Odd (Nat.card Ka) := odd_card_of_isPGroup_of_ne_two hr hr2 hKap
  have hbP : b ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => (hPT y hy b hbT).symm)
  have hbKa : b ∈ Subgroup.normalizer (Ka : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizer_inf_normalizer_le_normalizer_sup P U ⟨hbP, hTU hbT⟩,
        Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hab.symm)⟩
  have hodd₀ : Odd (orderOf u₀) :=
    (odd_card_of_isPGroup_of_ne_two hr hr2 hU).of_dvd_nat (Subgroup.orderOf_dvd_natCard U hu₀.1)
  have hu₀Ka : u₀ ∈ Ka := ⟨(le_sup_right : U ≤ P ⊔ U) hu₀.1,
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc u₀ * a = a * u₀ * a⁻¹ * a := by rw [hu₀.2.1]
        _ = a * u₀ := by group)⟩
  have hlt : Ka ⊓ Subgroup.centralizer {b} < Ka := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have hmem : u₀ ∈ Ka ⊓ Subgroup.centralizer {b} := by
      rw [h]
      exact hu₀Ka
    have hc : u₀ * b = b * u₀ := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
    apply inv_ne_self_of_odd_orderOf hodd₀ hu₀1
    rw [← hu₀.2.2, ← hc]
    group
  obtain ⟨y, hy, hy1, hyC⟩ := exists_inverted_centralizing_fixed hKap hKaodd hbo hbKa hlt
  obtain ⟨hyKa, hyb⟩ := OddInversion.mem_invertedSet.mp hy
  have hPle : P ≤ Ka ⊓ Subgroup.centralizer {b} := fun p hp =>
    ⟨⟨(le_sup_left : P ≤ P ⊔ U) hp,
        Subgroup.mem_centralizer_singleton_iff.mpr (hPT p hp a haT).symm⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (hPT p hp b hbT).symm⟩
  have hyP : y ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.centralizer_le (fun p hp => hPle hp) hyC
  have hyodd : Odd (orderOf y) := hKaodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard Ka hyKa)
  have hyU : y ∈ U := by
    have hyW : y ∈ ((P ⊔ U : Subgroup G) : Set G) := hyKa.1
    rw [hWset] at hyW
    obtain ⟨p, hp, w, hw, rfl⟩ := Set.mem_mul.mp hyW
    have hbp : b * p * b⁻¹ = p := by rw [hPT p hp b hbT]; group
    have hbw : b * w * b⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hTU hbT) w).mp hw
    have hsq : (p * w)⁻¹ * (p * w)⁻¹ ∈ U := by
      have e : (p * w)⁻¹ * (b * (p * w) * b⁻¹) = w⁻¹ * (b * w * b⁻¹) := by
        calc (p * w)⁻¹ * (b * (p * w) * b⁻¹) = (p * w)⁻¹ * ((b * p * b⁻¹) * (b * w * b⁻¹)) := by
              group
          _ = w⁻¹ * (b * w * b⁻¹) := by rw [hbp]; group
      have e' : (p * w)⁻¹ * (p * w)⁻¹ = (p * w)⁻¹ * (b * (p * w) * b⁻¹) := by rw [hyb]
      rw [e', e]
      exact U.mul_mem (U.inv_mem hw) hbw
    have := U.inv_mem hsq
    rw [mul_inv_rev, inv_inv] at this
    exact mem_of_mul_self_mem_of_odd_orderOf hyodd this
  refine ⟨y, ⟨⟨hyU, hyP⟩, ?_, hyb⟩, hy1⟩
  have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hyKa.2
  rw [← hya]
  group

private theorem exists_not_centralized_of_fourInverted (hσ : σ.IsValid)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {H : Subgroup G} (hDH : σ.D ≤ H)
    (hHw : IsDGroupWrt (σ.T.subgroupOf H)) {F : Subgroup G} (hFH : F ≤ H) (hF : IsPGroup r F)
    (hTF : σ.T ≤ Subgroup.normalizer (F : Set G)) {a b : G} (haT : a ∈ σ.T) (hbT : b ∈ σ.T)
    {ka kb : G} (hka : ka ∈ fourInverted F a b) (hkb : kb ∈ fourInverted F b a)
    (hka1 : ka ≠ 1) (hkb1 : kb ≠ 1) :
    ∃ Y : Subgroup G, Y ≤ oddCoreIn H ∧ IsPGroup r Y ∧
      σ.T ≤ Subgroup.normalizer (Y : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (Y : Set G) := by
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hTcomm : ∀ s ∈ σ.T, ∀ t ∈ σ.T, s * t = t * s := fun s hs t ht =>
    Subgroup.mem_centralizer_iff.mp (σ.T_le_C hσ ht) s hs
  set S : Set G := fourInverted F a b ∪ fourInverted F b a with hS
  set F₀ : Subgroup G := Subgroup.closure S with hF₀
  have hSF : S ⊆ F := Set.union_subset (fun y hy => hy.1) (fun y hy => hy.1)
  have hF₀F : F₀ ≤ F := (Subgroup.closure_le F).mpr hSF
  have hF₀p : IsPGroup r F₀ := hF.to_le hF₀F
  have hF₀odd : Odd (Nat.card F₀) := odd_card_of_isPGroup_of_ne_two hr hr2 hF₀p
  have horder : ∀ y ∈ F, Odd (orderOf y) := fun y hy =>
    (odd_card_of_isPGroup_of_ne_two hr hr2 hF).of_dvd_nat (Subgroup.orderOf_dvd_natCard F hy)
  have hconjS : ∀ t ∈ σ.T, ∀ y ∈ S, t * y * t⁻¹ ∈ S := by
    intro t ht y hy
    have hfix : ∀ s ∈ σ.T, t * s * t⁻¹ = s := fun s hs => by
      rw [hTcomm t ht s hs]
      group
    rcases hy with hy | hy
    · left
      have := conj_mem_fourInverted (hTF ht) hy
      rwa [hfix a haT, hfix b hbT] at this
    · right
      have := conj_mem_fourInverted (hTF ht) hy
      rwa [hfix a haT, hfix b hbT] at this
  have hTF₀ : σ.T ≤ Subgroup.normalizer (F₀ : Set G) := le_normalizer_closure_of_conj_mem hconjS
  have hcomm : ⁅F₀, σ.T⁆ = F₀ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro f hf t ht
      rw [commutatorElement_def]
      have h1 : t * f⁻¹ * t⁻¹ ∈ F₀ :=
        (Subgroup.mem_normalizer_iff.mp (hTF₀ ht) f⁻¹).mp (F₀.inv_mem hf)
      have e : f * t * f⁻¹ * t⁻¹ = f * (t * f⁻¹ * t⁻¹) := by group
      rw [e]
      exact F₀.mul_mem hf h1
    · rw [Subgroup.closure_le]
      intro y hy
      have hyF₀ : y ∈ F₀ := Subgroup.subset_closure hy
      have hsq : ∀ c ∈ σ.T, c * y * c⁻¹ = y⁻¹ → y ∈ ⁅F₀, σ.T⁆ := by
        intro c hc hcy
        have hmem := Subgroup.commutator_mem_commutator hyF₀ hc
        rw [commutatorElement_def] at hmem
        have e : y * c * y⁻¹ * c⁻¹ = y * y := by
          calc y * c * y⁻¹ * c⁻¹ = y * (c * y * c⁻¹)⁻¹ := by group
            _ = y * y := by rw [hcy, inv_inv]
        rw [e] at hmem
        exact mem_of_mul_self_mem_of_odd_orderOf (horder y (hSF hy)) hmem
      rcases hy with hy | hy
      · exact hsq b hbT hy.2.2
      · exact hsq a haT hy.2.2
  obtain ⟨g, hgF₀, hg⟩ := h_II54 H hDH hHw F₀ (hF₀F.trans hFH) hF₀odd hTF₀ hcomm
  have hHO : H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  have hkaF₀ : ka ∈ F₀ := Subgroup.subset_closure (Or.inl hka)
  have hkbF₀ : kb ∈ F₀ := Subgroup.subset_closure (Or.inr hkb)
  have hY : ∀ k ∈ F₀, k ∈ oddCoreIn H → ∀ c ∈ σ.T, c * k * c⁻¹ = k⁻¹ → k ≠ 1 →
      ∃ Y : Subgroup G, Y ≤ oddCoreIn H ∧ IsPGroup r Y ∧
        σ.T ≤ Subgroup.normalizer (Y : Set G) ∧ ¬ σ.T ≤ Subgroup.centralizer (Y : Set G) := by
    intro k hkF₀ hkO c hc hck hk1
    refine ⟨F₀ ⊓ oddCoreIn H, inf_le_right, hF₀p.to_le inf_le_left, fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hTF₀ ht, hHO (hTH ht)⟩, fun hTC => ?_⟩
    have hkc : k * c = c * k := Subgroup.mem_centralizer_iff.mp (hTC hc) k ⟨hkF₀, hkO⟩
    apply inv_ne_self_of_odd_orderOf (horder k (hF₀F hkF₀)) hk1
    rw [← hck, ← hkc]
    group
  by_cases hkaO : ka ∈ oddCoreIn H
  · exact hY ka hkaF₀ hkaO b hbT hka.2.2 hka1
  · have hkbO : kb ∈ oddCoreIn H := by
      by_contra hkbO
      exact false_of_isCyclic_mod hr hr2 hF₀p ((hF₀F.trans hFH).trans hHO) ⟨g, hgF₀, hg⟩
        (hHO (hTH haT)) hkaF₀ hkbF₀ hka.2.1 hkb.2.2 hkaO hkbO
    exact hY kb hkbF₀ hkbO a haT hkb.2.2 hkb1

private theorem mem_familyMstar_of_mem_familyM (h83 : σ.LemmaIV83) {r : ℕ} (hr : σ.HypIV7 r)
    (d : σ.IV7Data r) {H : Subgroup G} (hH : H ∈ d.familyM) : H ∈ σ.familyMstar r := by
  obtain ⟨hw, hodd, -⟩ := h83 r hr d H hH
  exact ⟨hH.1, hH.2.1, hw, hodd⟩

theorem constrained_of_exists_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hex : ∃ K ∈ σ.familyMstar r, PConstrainedWithin r K (CFSG.oddCore K) ∧
      ∃ P : Subgroup G, IsSylowOf r P σ.C ∧ σ.D ≤ Subgroup.normalizer (P : Set G) ∧ P ≤ K)
    {H : Subgroup G} (hH : H ∈ σ.familyMstar r) : PConstrainedWithin r H (CFSG.oddCore H) := by
  have : Fact r.Prime := ⟨hr⟩
  have : IsKleinFour σ.T := σ.isKleinFour_T_of_mem_familyMstar hσ hH
  obtain ⟨K, hK, hKc, P, hPC, -, hPK⟩ := hex
  by_contra hHc
  have hT2 := σ.isPGroup_two_T hσ
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hK.2.1
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hH.2.1
  have hP : IsPGroup r P := hPC.isPGroup
  have hTP : σ.T ≤ Subgroup.normalizer (P : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hPC.le hy) t ht).symm)
  obtain ⟨U, hU, -, hTU, hPU⟩ := exists_isSylowOf_normalized_by_two hr hr2 (R₀ := ⊥) hT2
    (odd_card_oddCoreIn K) (hTK.trans (le_normalizer_oddCoreIn K))
    (hPK.trans (le_normalizer_oddCoreIn K)) hP hTP bot_le IsPGroup.of_bot
    (fun _ _ => by rw [Subgroup.normalizer_eq_top]; trivial)
    (fun _ _ => by rw [Subgroup.normalizer_eq_top]; trivial)
  have hnc : ∀ t ∈ σ.T, t ∈ Subgroup.centralizer (U : Set G) → t = 1 := fun t ht htU =>
    σ.eq_one_of_mem_centralizer_of_constrained hσ hr hK hKc hU ht htU
  obtain ⟨Z₀, -, hZ₀, hHeq⟩ := hH.1
  have hZ₀H : Z₀ ≤ H := by
    rw [hHeq]
    exact Subgroup.le_normalizer
  have hHZ₀ : H ≤ Subgroup.normalizer (Z₀ : Set G) := hHeq.le
  have hZ₀O : Z₀ ≤ oddCoreIn H :=
    le_oddCoreIn hZ₀H hHZ₀ (odd_card_of_isPGroup_of_ne_two hr hr2 hZ₀)
  have hTZ₀ : σ.T ≤ Subgroup.centralizer (Z₀ : Set G) :=
    σ.le_centralizer_of_not_constrained hσ hII hr hr2 hH hHc hZ₀O hZ₀ (hTH.trans hHZ₀)
  have hZ₀C : Z₀ ≤ σ.C := Subgroup.le_centralizer_iff.mp hTZ₀
  obtain ⟨P₁, hP₁, hZ₀P₁⟩ := exists_isSylowOf_ge hZ₀C hZ₀
  obtain ⟨u, huC, hu⟩ := hPC.exists_mem_conj hP₁
  have hut : ∀ t ∈ σ.T, u⁻¹ * t * u = t := fun t ht => by
    rw [mul_assoc, Subgroup.mem_centralizer_iff.mp huC t ht]
    group
  set U₁ : Subgroup G := U.map (MulAut.conj u).toMonoidHom with hU₁
  have hU₁p : IsPGroup r U₁ := hU.isPGroup.map _
  have hU₁odd : Odd (Nat.card U₁) := odd_card_of_isPGroup_of_ne_two hr hr2 hU₁p
  have hTU₁ : σ.T ≤ Subgroup.normalizer (U₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_map_conj_iff_mem, mem_map_conj_iff_mem]
    have e : u⁻¹ * (t * y * t⁻¹) * u = (u⁻¹ * t * u) * (u⁻¹ * y * u) * (u⁻¹ * t * u)⁻¹ := by
      group
    rw [e, hut t ht]
    exact Subgroup.mem_normalizer_iff.mp (hTU ht) _
  have hP₁U₁ : P₁ ≤ Subgroup.normalizer (U₁ : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_map_conj_iff_mem, mem_map_conj_iff_mem]
    have e : u⁻¹ * (p * y * p⁻¹) * u = (u⁻¹ * p * u) * (u⁻¹ * y * u) * (u⁻¹ * p * u)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp (hPU ((hu p).mp hp)) _
  have hncU₁ : ∀ t ∈ σ.T, t ≠ 1 → t ∉ Subgroup.centralizer (U₁ : Set G) := by
    intro t ht ht1 htU₁
    apply ht1
    apply hnc t ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : u * w * u⁻¹ ∈ U₁ := mem_map_conj_iff_mem.mpr (by simpa [mul_assoc] using hw)
    have hc := Subgroup.mem_centralizer_iff.mp htU₁ _ hw'
    calc w * t = w * (u⁻¹ * t * u) := by rw [hut t ht]
      _ = u⁻¹ * (u * w * u⁻¹ * t) * u := by group
      _ = u⁻¹ * (t * (u * w * u⁻¹)) * u := by rw [hc]
      _ = (u⁻¹ * t * u) * w := by group
      _ = t * w := by rw [hut t ht]
  have hx1 : σ.x ≠ 1 := fun h => by
    have := hσ.x_order
    rw [h, orderOf_one] at this
    norm_num at this
  obtain ⟨s₁, hs₁T, hs₁1, hs₁x, k₁, hk₁, hk₁1⟩ := σ.exists_fourInverted_of_not_mem_centralizer hσ
    hU₁odd hTU₁ σ.x_mem_T hx1 (hncU₁ σ.x σ.x_mem_T hx1)
  obtain ⟨s₂, hs₂T, hs₂1, hs₂s₁, k₂, hk₂, hk₂1⟩ := σ.exists_fourInverted_of_not_mem_centralizer hσ
    hU₁odd hTU₁ hs₁T hs₁1 (hncU₁ s₁ hs₁T hs₁1)
  have hk₁' : k₁ ∈ fourInverted U₁ s₁ s₂ :=
    mem_fourInverted_of_mem hs₁T σ.x_mem_T hs₂T hs₁1 hx1 hs₁x hs₂1 hs₂s₁ hk₁
  obtain ⟨v₁, hv₁, hv₁1⟩ := σ.exists_fourInverted_inf_centralizer hr hr2 hP₁ hU₁p hTU₁ hP₁U₁
    hs₁T hs₂T hs₂1 hk₁' hk₁1
  obtain ⟨v₂, hv₂, hv₂1⟩ := σ.exists_fourInverted_inf_centralizer hr hr2 hP₁ hU₁p hTU₁ hP₁U₁
    hs₂T hs₁T hs₁1 hk₂ hk₂1
  have hFH : U₁ ⊓ Subgroup.centralizer (P₁ : Set G) ≤ H := by
    intro y hy
    rw [hHeq]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun z hz => hZ₀P₁ hz) hy.2)
  have hTF : σ.T ≤ Subgroup.normalizer
      ((U₁ ⊓ Subgroup.centralizer (P₁ : Set G) : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTU₁ ht, Subgroup.le_normalizer
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (hP₁.le hy) t ht).symm)⟩
  obtain ⟨Y, hYO, hYp, hTY, hTY'⟩ := σ.exists_not_centralized_of_fourInverted hσ h_II54 hr hr2
    hH.2.1 hH.2.2.1 hFH (hU₁p.to_le inf_le_left) hTF hs₁T hs₂T hv₁ hv₂ hv₁1 hv₂1
  exact hTY' (σ.le_centralizer_of_not_constrained hσ hII hr hr2 hH hHc hYO hYp hTY)

private theorem exists_mem_D_conj_x₂_ne (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    ∃ e ∈ σ.D, e * σ.x₂ * e⁻¹ ≠ σ.x₂ := by
  by_contra h
  have hx₂Z : σ.x₂ ∈ centerOf σ.D := by
    refine ⟨(σ.T_le_D hσ) σ.x₂_mem_T, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    have he' : e * σ.x₂ * e⁻¹ = σ.x₂ := not_not.mp fun h' => h ⟨e, he, h'⟩
    calc e * σ.x₂ = e * σ.x₂ * e⁻¹ * e := by group
      _ = σ.x₂ * e := by rw [he']
  rw [← hII.center_S_eq_center_D] at hx₂Z
  exact hσ.x_ne_x₂ (hσ.center_involution σ.x₂ hx₂Z hσ.x₂_order).symm

theorem normalizer_Q_constrained_of_not_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h33 : σ.LemmaIV33) (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    {r : ℕ} (hr : σ.HypIV7 r) (hnc : ¬ σ.Constrained r) (d : σ.IV7Data r) :
    PConstrainedWithin r (Subgroup.normalizer (d.Q : Set G))
      (CFSG.oddCore (Subgroup.normalizer (d.Q : Set G))) := by
  have hrp : r.Prime := hr.prime
  have : Fact r.Prime := ⟨hrp⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hrp hr.dvd_ON
  have hHMs : Subgroup.normalizer (d.Q : Set G) ∈ σ.familyMstar r :=
    σ.mem_familyMstar_of_mem_familyM h83 hr d (h81 r hr d)
  have : IsKleinFour σ.T := σ.isKleinFour_T_of_mem_familyMstar hσ hHMs
  have hx1 : σ.x ≠ 1 := fun h => by
    have := hσ.x_order
    rw [h, orderOf_one] at this
    norm_num at this
  have hns : ¬ σ.Stationary r := fun hs =>
    hr.exceptional ((σ.ordinary_iff hσ hII hrp hr.dvd_ON).mpr ⟨hs, hnc⟩)
  have hR := d.R_sylow
  have hRp : IsPGroup r d.R := hR.isPGroup
  have hRne : d.R ≠ ⊥ := by
    intro hbot
    have hcard := hR.card_eq
    rw [hbot, Subgroup.card_bot] at hcard
    have hk : (Nat.card σ.ON).factorization r ≠ 0 := by
      have := (hrp.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hr.dvd_ON
      omega
    have : 1 < r ^ (Nat.card σ.ON).factorization r := Nat.one_lt_pow hk hrp.one_lt
    omega
  have hRO : d.R ≤ oddCoreIn (Subgroup.normalizer (d.R : Set G)) :=
    le_oddCoreIn Subgroup.le_normalizer le_rfl (odd_card_of_isPGroup_of_ne_two hrp hr2 hRp)
  have hRns : ¬ IsSylowOf r d.R (oddCoreIn (Subgroup.normalizer (d.R : Set G))) :=
    fun h => hns ⟨d.R, hR, h⟩
  have hcov : (σ.L₀ : Set G) ⊆
      (Subgroup.normalizer (d.R : Set G) : Set G) * (σ.ON : Set G) := by
    intro g hg
    have hgN : g ∈ σ.N := hσ.L₀_le_N hg
    obtain ⟨o, hoON, ho⟩ := hR.exists_mem_conj (isSylowOf_map_conj hR (σ.N_le_normalizer_ON hgN))
    have hoN : o ∈ σ.N := σ.ON_le_N hoON
    have hn : o⁻¹ * g ∈ Subgroup.normalizer (d.R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := ho (g * y * g⁻¹)
      rw [mem_map_conj_iff_mem] at h1
      have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      have e2 : o⁻¹ * (g * y * g⁻¹) * o = o⁻¹ * g * y * (o⁻¹ * g)⁻¹ := by group
      rw [e1, e2] at h1
      exact h1
    have hnN : o⁻¹ * g ∈ σ.N := σ.N.mul_mem (σ.N.inv_mem hoN) hgN
    have hmem : (o⁻¹ * g)⁻¹ * o * (o⁻¹ * g)⁻¹⁻¹ ∈ σ.ON :=
      (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON (σ.N.inv_mem hnN)) o).mp hoON
    exact Set.mem_mul.mpr ⟨o⁻¹ * g, hn, (o⁻¹ * g)⁻¹ * o * (o⁻¹ * g)⁻¹⁻¹, hmem, by group⟩
  have hNRL : Subgroup.normalizer (d.R : Set G) ∈ σ.familyL r :=
    ⟨⟨d.R, hRne, hRp, rfl⟩, hcov, d.R_D, d.R, hR, Subgroup.le_normalizer⟩
  obtain ⟨U, hU, hRU, hDU, hPU⟩ := exists_isSylowOf_normalized_by_two hrp hr2
    (σ.S.isPGroup'.to_le σ.D_le_S) (odd_card_oddCoreIn _)
    (d.R_D.trans (le_normalizer_oddCoreIn _)) (d.R_P.trans (le_normalizer_oddCoreIn _))
    d.P_sylow.isPGroup d.P_D hRO hRp d.R_D d.R_P
  have hRU' : d.R < U := lt_of_le_of_ne hRU fun h => hRns (h ▸ hU)
  have hNRc := h33 r hrp hr.dvd_ON _ hNRL d.R U hR d.R_D hRO hU hDU hRU'
  have hxU : σ.x ∉ Subgroup.centralizer (U : Set G) := by
    intro hxU
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S₀, hS₀⟩ := exists_isSylowOf 2 (Subgroup.normalizer (d.R : Set G))
    obtain ⟨U₀, hU₀, hS₀U₀⟩ := exists_isSylowOf_normalized_of_odd hrp hS₀.isPGroup
      (hS₀.le.trans (le_normalizer_oddCoreIn _)) (odd_card_oddCoreIn _)
    have hO : oddCoreIn (Subgroup.normalizer (d.R : Set G)) ≠ ⊥ := fun h =>
      hRne (le_bot_iff.mp (h ▸ hRO))
    have hodd := ((hII.qgroup_constraint_criterion _ d.R_D hO hcov S₀ hS₀ r hrp hr2 U₀ hU₀
      hS₀U₀).2).mp hNRc
    obtain ⟨o, hoO, ho⟩ := hU₀.exists_mem_conj hU
    have hoNR : o ∈ Subgroup.normalizer (d.R : Set G) := oddCoreIn_le _ hoO
    have hxNR : σ.x ∈ Subgroup.normalizer (d.R : Set G) := d.R_D ((σ.T_le_D hσ) σ.x_mem_T)
    have hyC : o⁻¹ * σ.x * o ∈ Subgroup.centralizer (U₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : o * w * o⁻¹ ∈ U := (ho _).mpr (by simpa [mul_assoc] using hw)
      have hc := Subgroup.mem_centralizer_iff.mp hxU _ hw'
      calc w * (o⁻¹ * σ.x * o) = o⁻¹ * ((o * w * o⁻¹) * σ.x) * o := by group
        _ = o⁻¹ * (σ.x * (o * w * o⁻¹)) * o := by rw [hc]
        _ = o⁻¹ * σ.x * o * w := by group
    have hy : o⁻¹ * σ.x * o ∈ (Subgroup.normalizer (d.R : Set G) ⊓
        Subgroup.centralizer (U₀ : Set G) : Subgroup G) :=
      Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hoNR) hxNR) hoNR, hyC⟩
    have hxx : σ.x * σ.x = 1 := by
      rw [← pow_two, ← hσ.x_order]
      exact pow_orderOf_eq_one _
    have hy2 : o⁻¹ * σ.x * o * (o⁻¹ * σ.x * o) ∈ (⊥ : Subgroup G) := by
      rw [Subgroup.mem_bot]
      calc o⁻¹ * σ.x * o * (o⁻¹ * σ.x * o) = o⁻¹ * (σ.x * σ.x) * o := by group
        _ = 1 := by rw [hxx]; group
    have hy1 := (Subgroup.mem_bot).mp (mem_of_mul_self_mem_of_odd_orderOf
      (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy)) hy2)
    apply hx1
    calc σ.x = o * (o⁻¹ * σ.x * o) * o⁻¹ := by group
      _ = 1 := by rw [hy1]; group
  have hUodd : Odd (Nat.card U) := odd_card_of_isPGroup_of_ne_two hrp hr2 hU.isPGroup
  have hTU : σ.T ≤ Subgroup.normalizer (U : Set G) := (σ.T_le_D hσ).trans hDU
  obtain ⟨s₁, hs₁T, hs₁1, hs₁x, k₁, hk₁, hk₁1⟩ := σ.exists_fourInverted_of_not_mem_centralizer hσ
    hUodd hTU σ.x_mem_T hx1 hxU
  obtain ⟨e, heD, hex₂⟩ := σ.exists_mem_D_conj_x₂_ne hσ hII
  have hexe : e * σ.x * e⁻¹ = σ.x := by
    rw [Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2 e (σ.D_le_S heD)]
    group
  have hs₂T : e * s₁ * e⁻¹ ∈ σ.T := (Subgroup.mem_normalizer_iff.mp heD.2 s₁).mp hs₁T
  have hinj : ∀ a b : G, e * a * e⁻¹ = e * b * e⁻¹ → a = b := fun a b h => by simpa using h
  have hs₂1 : e * s₁ * e⁻¹ ≠ 1 := fun h => hs₁1 (hinj _ _ (by rw [h]; group))
  have hs₂x : e * s₁ * e⁻¹ ≠ σ.x := fun h => hs₁x (hinj _ _ (by rw [h, hexe]))
  have hs₂s₁ : e * s₁ * e⁻¹ ≠ s₁ := by
    intro h
    apply hex₂
    have hx₂1 : σ.x₂ ≠ 1 := fun h' => by
      have := hσ.x₂_order
      rw [h', orderOf_one] at this
      norm_num at this
    rcases kleinFour_mem_cases σ.x_mem_T hs₁T σ.x₂_mem_T hx1 hs₁1 (Ne.symm hs₁x) with
      h' | h' | h' | h'
    · exact absurd h' hx₂1
    · exact absurd h'.symm hσ.x_ne_x₂
    · rw [h']
      exact h
    · rw [h']
      calc e * (σ.x * s₁) * e⁻¹ = (e * σ.x * e⁻¹) * (e * s₁ * e⁻¹) := by group
        _ = σ.x * s₁ := by rw [hexe, h]
  have hk₂ : e * k₁ * e⁻¹ ∈ fourInverted U (e * s₁ * e⁻¹) σ.x := by
    have := conj_mem_fourInverted (hDU heD) hk₁
    rwa [hexe] at this
  have hk₂1 : e * k₁ * e⁻¹ ≠ 1 := fun h => hk₁1 (hinj _ _ (by rw [h]; group))
  have hk₁' : k₁ ∈ fourInverted U s₁ (e * s₁ * e⁻¹) :=
    mem_fourInverted_of_mem hs₁T σ.x_mem_T hs₂T hs₁1 hx1 hs₁x hs₂1 hs₂s₁ hk₁
  have hk₂' : e * k₁ * e⁻¹ ∈ fourInverted U (e * s₁ * e⁻¹) s₁ :=
    mem_fourInverted_of_mem hs₂T σ.x_mem_T hs₁T hs₂1 hx1 hs₂x hs₁1 (Ne.symm hs₂s₁) hk₂
  obtain ⟨v₁, hv₁, hv₁1⟩ := σ.exists_fourInverted_inf_centralizer hrp hr2 d.P_sylow
    hU.isPGroup hTU hPU hs₁T hs₂T hs₂1 hk₁' hk₁1
  obtain ⟨v₂, hv₂, hv₂1⟩ := σ.exists_fourInverted_inf_centralizer hrp hr2 d.P_sylow
    hU.isPGroup hTU hPU hs₂T hs₁T hs₁1 hk₂' hk₂1
  have hFH : U ⊓ Subgroup.centralizer (d.P : Set G) ≤ Subgroup.normalizer (d.Q : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun z hz => d.Q_le hz) hy.2)
  have hTF : σ.T ≤ Subgroup.normalizer
      ((U ⊓ Subgroup.centralizer (d.P : Set G) : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hTU ht, Subgroup.le_normalizer
      (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (Subgroup.mem_centralizer_iff.mp (d.P_sylow.le hy) t ht).symm)⟩
  obtain ⟨Y, hYO, hYp, hTY, hTY'⟩ := σ.exists_not_centralized_of_fourInverted hσ h_II54 hrp hr2
    hHMs.2.1 hHMs.2.2.1 hFH (hU.isPGroup.to_le inf_le_left) hTF hs₁T hs₂T hv₁ hv₂ hv₁1 hv₂1
  by_contra hHc
  exact hTY' (σ.le_centralizer_of_not_constrained hσ hII hrp hr2 hHMs hHc hYO hYp hTY)

theorem familyMstar_constrained_of_not_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    (h33 : σ.LemmaIV33) (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83)
    (h_II54 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ F : Subgroup G, F ≤ H → Odd (Nat.card F) → σ.T ≤ Subgroup.normalizer (F : Set G) →
        ⁅F, σ.T⁆ = F → ∃ g ∈ F, ∀ f ∈ F, ∃ k : ℤ, f⁻¹ * g ^ k ∈ oddCoreIn H)
    {r : ℕ} (hr : σ.HypIV7 r) (hnc : ¬ σ.Constrained r) (d : σ.IV7Data r) {K : Subgroup G}
    (hK : K ∈ σ.familyMstar r) : PConstrainedWithin r K (CFSG.oddCore K) := by
  have hrp : r.Prime := hr.prime
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hrp hr.dvd_ON
  have hPQ : d.P ≤ Subgroup.normalizer (d.Q : Set G) := by
    have := d.Q_characteristic
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer d.Q_le).mp inferInstance
  exact σ.constrained_of_exists_constrained hσ hII h_II54 hrp hr2
    ⟨_, σ.mem_familyMstar_of_mem_familyM h83 hr d (h81 r hr d),
      σ.normalizer_Q_constrained_of_not_constrained hσ hII h33 h81 h83 h_II54 hr hnc d,
      d.P, d.P_sylow, d.P_D, hPQ⟩ hK

end Setting

end CFSG.ABGTheoremB
