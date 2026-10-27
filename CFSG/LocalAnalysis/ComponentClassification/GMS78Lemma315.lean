module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Trans

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

theorem sup_eq_of_isSylowOf {P H K : Subgroup G} (hP : IsSylowOf 2 P H) (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set G)) (hpow : ∀ x ∈ H, ∃ k : ℕ, x ^ 2 ^ k ∈ K) :
    P ⊔ K = H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPKH : P ⊔ K ≤ H := sup_le hP.le hKH
  have : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  have hQ : IsPGroup 2 (H ⧸ K.subgroupOf H) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      simpa using hk
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ
  have hKidx : K.relIndex H = 2 ^ m := hm
  have h1 := Subgroup.relIndex_mul_relIndex K (P ⊔ K) H le_sup_right hPKH
  have h2 := Subgroup.relIndex_mul_relIndex P (P ⊔ K) H le_sup_left hPKH
  have hdvd : (P ⊔ K).relIndex H ∣ 2 ^ m := by
    rw [← hKidx, ← h1]
    exact dvd_mul_left _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd : ¬ 2 ∣ P.relIndex H := (isSylowOf_iff.mp hP).2.2
  have hj0 : j = 0 := by
    by_contra hj0
    apply hodd
    rw [← h2, hj]
    exact dvd_mul_of_dvd_right (dvd_pow_self 2 hj0) _
  rw [hj0, pow_zero] at hj
  exact le_antisymm hPKH (Subgroup.relIndex_eq_one.mp hj)

theorem exists_odd_of_conj_eq {W : Subgroup G} {g y : G} (hgW : g ∈ normalizer (W : Set G))
    (hy : Odd (orderOf y)) (hgy : ∀ w ∈ W, g * w * g⁻¹ = y * w * y⁻¹) :
    ∃ d ∈ zpowers g, Odd (orderOf d) ∧ ∀ w ∈ W, d * w * d⁻¹ = y * w * y⁻¹ := by
  have hpow : ∀ k : ℕ, ∀ w ∈ W, g ^ k * w * (g ^ k)⁻¹ = y ^ k * w * (y ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      have hkw : g ^ k * w * (g ^ k)⁻¹ ∈ W :=
        (mem_normalizer_iff.mp (pow_mem hgW k) w).mp hw
      calc g ^ (k + 1) * w * (g ^ (k + 1))⁻¹ = g * (g ^ k * w * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = y * (y ^ k * w * (y ^ k)⁻¹) * y⁻¹ := by rw [hgy _ hkw, ih w hw]
        _ = y ^ (k + 1) * w * (y ^ (k + 1))⁻¹ := by group
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ a) (orderOf y) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hy)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, y ^ (2 ^ a * c) = y := by
    rcases Nat.lt_or_ge 1 (orderOf y) with h1 | h1
    · obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
      refine ⟨c, ?_⟩
      rw [← pow_mod_orderOf, hc, pow_one]
    · have : orderOf y = 1 := le_antisymm h1 (orderOf_pos y)
      rw [orderOf_eq_one_iff] at this
      exact ⟨0, by rw [this, one_pow]⟩
  refine ⟨g ^ (2 ^ a * c), ⟨(2 ^ a * c : ℕ), zpow_natCast g _⟩, ?_, fun w hw => ?_⟩
  · apply hb.of_dvd_nat
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, mul_right_comm, pow_mul, ← hab, pow_orderOf_eq_one, one_pow]
  · rw [hpow _ w hw, hc]

namespace Sec3

variable {L T : Subgroup G} {q : ℕ}

omit [Finite G] in
theorem gmsTrans_le_normalizer : gmsTrans L T ≤ normalizer (gmsV L T : Set G) :=
  fun _ hu => (mem_inf.mp hu).1.1

omit [Finite G] in
theorem commute_of_mem_gmsTrans {u : G} (hu : u ∈ gmsTrans L T) {a : G} (ha : a ∈ gmsA L T) :
    u * a = a * u :=
  (mem_centralizer_iff.mp (mem_inf.mp hu).2 a ha).symm

omit [Finite G] in
theorem conj_mul_inv_mem {u : G} (hu : u ∈ gmsTrans L T) {v : G} (hv : v ∈ gmsV L T) :
    u * v * u⁻¹ * v⁻¹ ∈ gmsA L T :=
  (mem_inf.mp hu).1.2.2 v hv

omit [Finite G] in
theorem centralizer_le_gmsTrans : centralizer (gmsV L T : Set G) ≤ gmsTrans L T := by
  intro c hc
  have hcV : ∀ v ∈ gmsV L T, c * v = v * c := fun v hv => (mem_centralizer_iff.mp hc v hv).symm
  refine mem_inf.mpr ⟨mem_gmsN₁.mpr ⟨Subgroup.centralizer_le_normalizer _ hc, ?_, fun v hv => ?_⟩,
    mem_centralizer_iff.mpr fun a ha => (hcV a (mem_sup_left ha)).symm⟩
  · exact Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun a ha => (hcV a (mem_sup_left ha)).symm)
  · have : c * v * c⁻¹ * v⁻¹ = 1 := by rw [hcV v hv]; group
    rw [this]
    exact one_mem _

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer_gmsV :
    normalizer (gmsV L T : Set G) ≤ normalizer (centralizer (gmsV L T : Set G) : Set G) :=
  AS76b.Lemma22.normalizer_le_normalizer_centralizer _

omit [Finite G] in
theorem mem_centralizer_T₀ {c : G} (hc : c ∈ centralizer (gmsV L T : Set G)) :
    c ∈ centralizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
  mem_centralizer_iff.mpr fun t ht => mem_centralizer_iff.mp hc t (mem_sup_right ht)

theorem sq_mem_centralizer (hX : Facts L T q) (h : Sec3 G L T) {u : G}
    (hu : u ∈ gmsTrans L T) : u ^ 2 ∈ centralizer (gmsV L T : Set G) := by
  obtain ⟨-, hA₁sq, -⟩ := hX.sylow h
  rw [mem_centralizer_iff]
  intro v hv
  have ha : u * v * u⁻¹ * v⁻¹ ∈ gmsA L T := conj_mul_inv_mem hu hv
  have hua := commute_of_mem_gmsTrans hu ha
  have hsq := hA₁sq _ ha
  have key : u ^ 2 * v * (u ^ 2)⁻¹ = v := by
    rw [pow_two]
    have e1 : u * u * v * (u * u)⁻¹ =
        u * (u * v * u⁻¹ * v⁻¹) * u⁻¹ * (u * v * u⁻¹ * v⁻¹) * v := by group
    have hsq' : u * v * u⁻¹ * v⁻¹ * (u * v * u⁻¹ * v⁻¹) = 1 := by rw [← pow_two]; exact hsq
    have e2 : u * v * u⁻¹ * v⁻¹ * u * u⁻¹ * (u * v * u⁻¹ * v⁻¹) * v =
        u * v * u⁻¹ * v⁻¹ * (u * v * u⁻¹ * v⁻¹) * v := by group
    rw [e1, hua, e2, hsq', one_mul]
  calc v * u ^ 2 = u ^ 2 * v * (u ^ 2)⁻¹ * u ^ 2 := by rw [key]
    _ = u ^ 2 * v := by group

theorem mem_centralizer_of_mem_gmsTrans
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) {u : G} (hu : u ∈ gmsTrans L T) {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T)
    (huQ : u ∈ normalizer (Q : Set G)) : u ∈ centralizer (gmsV L T : Set G) := by
  rw [mem_centralizer_iff]
  intro v hv
  obtain ⟨a, ha, hav⟩ := h313.exists_mul_mem hX h hF hQ hv
  have h1 : u * (a * v) * u⁻¹ = a * v :=
    conj_eq_of_mem_gmsN₁ h313 hQ (mem_inf.mp hu).1 huQ hav
  have h2 : u * a = a * u := commute_of_mem_gmsTrans hu ha
  have h3 : u * v * u⁻¹ = v := by
    have e : u * (a * v) * u⁻¹ = a * (u * v * u⁻¹) := by
      calc u * (a * v) * u⁻¹ = u * a * v * u⁻¹ := by group
        _ = a * u * v * u⁻¹ := by rw [h2]
        _ = a * (u * v * u⁻¹) := by group
    rw [e] at h1
    exact mul_left_cancel h1
  calc v * u = u * v * u⁻¹ * u := by rw [h3]
    _ = u * v := by group

theorem mem_gmsA_of_commute
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) {u : G}
    (hu : u ∈ gmsTrans L T) (huV : u ∉ centralizer (gmsV L T : Set G)) {v : G}
    (hv : v ∈ gmsV L T) (huv : u * v = v * u) : v ∈ gmsA L T := by
  by_contra hvA
  obtain ⟨Q, hQ, hvQ, hv1⟩ := (h313.cover v hv).mp hvA
  have hQ' : rightConjugate Q u⁻¹ ∈ gmsDelta L T :=
    rightConjugate_mem_delta hQ (inv_mem (gmsTrans_le_normalizer hu))
  have hvQ' : v ∈ rightConjugate Q u⁻¹ := by
    rw [mem_rightConjugate_iff]
    have : u⁻¹ * v * u⁻¹⁻¹ = v := by
      rw [inv_inv]
      calc u⁻¹ * v * u = u⁻¹ * (u * v) := by rw [huv]; group
        _ = v := by group
    rwa [this]
  have heq : Q = rightConjugate Q u⁻¹ := by
    by_contra hne
    have h0 := h313.inf_eq_bot Q hQ _ hQ' hne
    have hv' : v ∈ Q ⊓ rightConjugate Q u⁻¹ := mem_inf.mpr ⟨hvQ, hvQ'⟩
    rw [h0, mem_bot] at hv'
    exact hv1 hv'
  have huQ : u ∈ normalizer (Q : Set G) := by
    have := inv_mem ((rightConjugate_eq_self_iff Q u⁻¹).mp heq.symm)
    rwa [inv_inv] at this
  exact huV (mem_centralizer_of_mem_gmsTrans h313 hX h hF hu hQ huQ)

theorem le_normalizer_gmsA (h : Sec3 G L T) : T ≤ normalizer (gmsA L T : Set G) := by
  intro t ht
  have h1 : t ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer ht) (h.sylow.le ht)
  exact mem_normalizer_inf h1 (AS76b.Lemma22.normalizer_le_normalizer_centralizer _ h1)

theorem le_normalizer_gmsV (h : Sec3 G L T) : T ≤ normalizer (gmsV L T : Set G) := fun _ ht =>
  mem_normalizer_sup (h.le_normalizer_gmsA ht)
    (le_normalizer_of_conj_mem (fun _ ht _ hp => h.conj_mem_T₀ ht hp) ht)

omit [Finite G] in
theorem gmsW_le : gmsW L T ≤ T := sup_le inf_le_left inf_le_left

structure IsR (L T R : Subgroup G) : Prop where
  sylow : IsSylowOf 2 R (gmsTrans L T)
  le_normalizer : T ≤ normalizer (R : Set G)
  gmsW_le : gmsW L T ≤ R

theorem exists_isR
    (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T) (hF : Foundation) :
    ∃ R, IsR L T R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hVW, -⟩ := hX.vFacts h hF
  have hWC : gmsW L T ≤ centralizer (gmsV L T : Set G) := le_centralizer_iff.mp hVW
  have hTN : T ≤ normalizer (gmsTrans L T : Set G) := le_normalizer_of_conj_mem fun t ht u hu =>
    conj_mem_gmsTrans h313 (h.le_normalizer_gmsV ht) hu
  have hHN : gmsTrans L T ⊔ T ≤ normalizer (gmsTrans L T : Set G) :=
    sup_le Subgroup.le_normalizer hTN
  obtain ⟨S, hS, hTS⟩ := AS76b.exists_isSylowOf_le (le_sup_right : T ≤ gmsTrans L T ⊔ T)
    h.sylow.isPGroup
  exact ⟨S ⊓ gmsTrans L T, hS.inf_of_le_normalizer le_sup_left hHN,
    fun t ht => mem_normalizer_inf (Subgroup.le_normalizer (hTS ht)) (hTN ht),
    le_inf (gmsW_le.trans hTS) (hWC.trans centralizer_le_gmsTrans)⟩

namespace IsR

variable {R : Subgroup G}

omit [Finite G] in
theorem le_gmsTrans (hR : IsR L T R) : R ≤ gmsTrans L T := hR.sylow.le

omit [Finite G] in
theorem isPGroup (hR : IsR L T R) : IsPGroup 2 R := hR.sylow.isPGroup

omit [Finite G] in
theorem le_normalizer_gmsV (hR : IsR L T R) : R ≤ normalizer (gmsV L T : Set G) :=
  hR.le_gmsTrans.trans gmsTrans_le_normalizer

theorem inf_centralizer_eq
    (hR : IsR L T R) (h : Sec3 G L T)
    (hW : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T) :
    R ⊓ centralizer (gmsV L T : Set G) = gmsW L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := AS76b.Lemma36.normalizer_le h.hyp.hyp31 h.isSylowOf_T₀ 1
  rw [rightConjugate_one, rightConjugate_one] at hN
  have hCM : centralizer (gmsV L T : Set G) ≤ normalizer (L : Set G) := fun c hc =>
    hN (Subgroup.centralizer_le_normalizer _ (mem_centralizer_T₀ hc))
  have hTsyl : IsSylowOf 2 T (normalizer (L : Set G) ⊓ normalizer (gmsV L T : Set G)) :=
    h.sylow.of_le (le_inf h.sylow.le h.le_normalizer_gmsV) inf_le_left
  have hCsyl : IsSylowOf 2 (T ⊓ centralizer (gmsV L T : Set G)) (centralizer (gmsV L T : Set G)) :=
    hTsyl.inf_of_le_normalizer (le_inf hCM (Subgroup.centralizer_le_normalizer _))
      (fun g hg => normalizer_le_normalizer_centralizer_gmsV (mem_inf.mp hg).2)
  rw [hW] at hCsyl
  have hWC : gmsW L T ≤ centralizer (gmsV L T : Set G) := by
    rw [← hW]
    exact inf_le_right
  exact hCsyl.eq_of_le (le_inf hR.gmsW_le hWC) inf_le_right (hR.isPGroup.to_le inf_le_left)

theorem mem_gmsW_of_mem_normalizer
    (hR : IsR L T R) (h313 : Lemma313 L T q) (hX : Facts L T q) (h : Sec3 G L T)
    (hF : Foundation) (hW : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T) {r : G} (hr : r ∈ R)
    {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) (hrQ : r ∈ normalizer (Q : Set G)) :
    r ∈ gmsW L T := by
  rw [← hR.inf_centralizer_eq h hW]
  exact mem_inf.mpr ⟨hr, mem_centralizer_of_mem_gmsTrans h313 hX h hF (hR.le_gmsTrans hr) hQ hrQ⟩

theorem le_normalizer_gmsW
    (hR : IsR L T R) (h : Sec3 G L T) (hW : T ⊓ centralizer (gmsV L T : Set G) = gmsW L T) :
    R ≤ normalizer (gmsW L T : Set G) := by
  rw [← hR.inf_centralizer_eq h hW]
  exact fun r hr => mem_normalizer_inf (Subgroup.le_normalizer hr)
    (normalizer_le_normalizer_centralizer_gmsV (hR.le_normalizer_gmsV hr))

theorem exists_conj_eq (hR : IsR L T R) (hX : Facts L T q) (h : Sec3 G L T)
    (htr : ∀ Q ∈ gmsDelta L T, ∃ u ∈ gmsTrans L T,
      rightConjugate (T ⊓ centralizer (L : Set G)) u⁻¹ = Q)
    {Q : Subgroup G} (hQ : Q ∈ gmsDelta L T) :
    ∃ r ∈ R, rightConjugate (T ⊓ centralizer (L : Set G)) r⁻¹ = Q := by
  obtain ⟨u, hu, rfl⟩ := htr Q hQ
  have hNC : gmsTrans L T ≤ normalizer (centralizer (gmsV L T : Set G) : Set G) := fun g hg =>
    normalizer_le_normalizer_centralizer_gmsV (gmsTrans_le_normalizer hg)
  have hsup : R ⊔ centralizer (gmsV L T : Set G) = gmsTrans L T :=
    sup_eq_of_isSylowOf hR.sylow centralizer_le_gmsTrans hNC
      (fun x hx => ⟨1, by simpa using sq_mem_centralizer hX h hx⟩)
  have hu' : u ∈ R ⊔ centralizer (gmsV L T : Set G) := hsup ▸ hu
  obtain ⟨r, hr, c, hc, rfl⟩ :=
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hR.le_gmsTrans.trans hNC) hu'
  refine ⟨r, hr, ?_⟩
  rw [mul_inv_rev, ← rightConjugate_mul, (rightConjugate_eq_self_iff _ c⁻¹).mpr
    (inv_mem (Subgroup.centralizer_le_normalizer _ (mem_centralizer_T₀ hc)))]

end IsR

end Sec3

end CFSG.ComponentClassification.GMS78
