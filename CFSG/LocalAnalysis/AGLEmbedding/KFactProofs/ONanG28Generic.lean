module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.GroupTheory.ElementaryAbelianTransport

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem exists_elemAbelian_27 {T : Subgroup G} (h : 3 ≤ pRank 3 T) :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨E, hET, hE, hcard⟩ := pRank_attained 3 Nat.prime_three T
  have hpow : 3 ^ 3 ∣ Nat.card E := by rw [hcard]; exact pow_dvd_pow 3 h
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 hpow
  refine ⟨F.map E.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨f, -, rfl⟩
    exact hET f.2
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      have := congrArg Subtype.val (hE.1.is_comm.comm a' b')
      show (a : G) * b = b * a
      rw [← ha, ← hb]
      exact this
    · rintro _ ⟨f, -, rfl⟩
      exact hE.2 f f.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hF]
    norm_num

theorem three_le_pRank_of_card_27 {T E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 3 E)
    (h27 : Nat.card E = 27) : 3 ≤ pRank 3 T :=
  le_csSup (pRank_bddAbove 3 Nat.prime_three T) ⟨E, hET, hE, by rw [h27]; norm_num⟩

theorem two_le_pRank_of_card_9 {T E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 3 E)
    (h9 : Nat.card E = 9) : 2 ≤ pRank 3 T :=
  le_csSup (pRank_bddAbove 3 Nat.prime_three T) ⟨E, hET, hE, by rw [h9]; norm_num⟩

theorem no_elemAbelian_27 {T A : Subgroup G} (hidx : A.relIndex T = 3)
    (S : Finset G) (hS : S.card = 9) (hΩ : ∀ x ∈ A, x ^ 3 = 1 → x ∈ S) (a0 b0 : G)
    (ha0 : a0 ∈ S) (hb0 : b0 ∈ S)
    (hcomp : ∀ c ∈ T, c ∉ A → c ^ 3 = 1 → c * a0 = a0 * c → c * b0 = b0 * c → False)
    {E : Subgroup G} (hET : E ≤ T) (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27) : False := by
  have h1 : A.relIndex E ≤ 3 := by
    have := Subgroup.relIndex_le_of_le_right hET (H := A) (by rw [hidx]; norm_num)
    rwa [hidx] at this
  have h2 : A.relIndex E * Nat.card (A ⊓ E : Subgroup G) = 27 := by
    rw [Subgroup.relIndex_mul_card, h27]
  have h9 : 9 ≤ Nat.card (A ⊓ E : Subgroup G) := by
    by_contra hlt
    push Not at hlt
    have : A.relIndex E * Nat.card (A ⊓ E : Subgroup G) ≤ 3 * 8 :=
      Nat.mul_le_mul h1 (by omega)
    omega
  have hsub : ((A ⊓ E : Subgroup G) : Set G) ⊆ (S : Set G) := by
    intro x hx
    exact hΩ x hx.1 (hE.2 x hx.2)
  have hnc : Nat.card (A ⊓ E : Subgroup G) = ((A ⊓ E : Subgroup G) : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  have hSn : (S : Set G).ncard = 9 := by rw [Set.ncard_coe_finset, hS]
  have heq : ((A ⊓ E : Subgroup G) : Set G) = (S : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hSn, ← hnc]; exact h9) (Finset.finite_toSet S)
  have ha : a0 ∈ A ⊓ E := by
    have : a0 ∈ ((A ⊓ E : Subgroup G) : Set G) := by rw [heq]; exact ha0
    exact this
  have hb : b0 ∈ A ⊓ E := by
    have : b0 ∈ ((A ⊓ E : Subgroup G) : Set G) := by rw [heq]; exact hb0
    exact this
  have hex : ∃ c ∈ E, c ∉ A := by
    by_contra hall
    push Not at hall
    have hle : E ≤ A := hall
    have : (A ⊓ E : Subgroup G) = E := inf_eq_right.mpr hle
    have hc : Nat.card (A ⊓ E : Subgroup G) ≤ 9 := by
      rw [hnc, ← hSn]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet S)
    rw [this, h27] at hc
    omega
  obtain ⟨c, hcE, hcA⟩ := hex
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  exact hcomp c (hET hcE) hcA (hE.2 c hcE) (hEc c hcE a0 ha.2) (hEc c hcE b0 hb.2)

theorem isElemAbelian_zpowers' {a : G} (ha : a ^ 3 = 1) : IsElemAbelian 3 (Subgroup.zpowers a) :=
  CFSG.Open.isElemAbelian_zpowers ha

theorem mem_normalizer_of_conj_le {Q : Subgroup G} {g : G} (h : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) :
    g ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : Q → Q := fun q => ⟨g * q * g⁻¹, h q q.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel this))
  obtain ⟨q, hq⟩ := Finite.injective_iff_surjective.mp hinj ⟨g * x * g⁻¹, hx⟩
  have : g * (q : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hq
  have hqx : (q : G) = x := mul_left_cancel (mul_right_cancel this)
  rw [← hqx]
  exact q.2

@[expose] def conjSub (x : G) (A : Subgroup G) : Subgroup G := A.map (MulAut.conj x).toMonoidHom

theorem mem_conjSub {x y : G} {A : Subgroup G} : y ∈ conjSub x A ↔ x⁻¹ * y * x ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : x⁻¹ * (MulAut.conj x).toMonoidHom a * x = a := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    rw [this]
    exact ha
  · intro h
    refine ⟨x⁻¹ * y * x, h, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    group

theorem conjSub_one (A : Subgroup G) : conjSub 1 A = A := by
  ext y
  rw [mem_conjSub]
  simp

theorem conjSub_mul (x y : G) (A : Subgroup G) : conjSub (x * y) A = conjSub x (conjSub y A) := by
  ext w
  rw [mem_conjSub, mem_conjSub, mem_conjSub]
  simp [mul_assoc]

@[expose, instance_reducible] def conjSubAction : MulAction G (Subgroup G) where
  smul := conjSub
  one_smul := conjSub_one
  mul_smul := conjSub_mul

theorem conjSub_eq_self_iff {x : G} {A : Subgroup G} :
    conjSub x A = A ↔ x ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h a
    have h1 : x * a * x⁻¹ ∈ conjSub x A ↔ x * a * x⁻¹ ∈ A := by rw [h]
    rw [mem_conjSub] at h1
    have e : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    rw [e] at h1
    exact h1
  · intro h
    ext y
    rw [mem_conjSub]
    have h1 := h (x⁻¹ * y * x)
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e] at h1
    exact h1

theorem card_eq_ncard_conj_mul (H A : Subgroup G) :
    Nat.card H = {B : Subgroup G | ∃ h ∈ H, B = conjSub h A}.ncard *
      Nat.card (Subgroup.normalizer (A : Set G) ⊓ H : Subgroup G) := by
  let _ : MulAction G (Subgroup G) := conjSubAction
  have horb : (MulAction.orbit H A : Set (Subgroup G)) = {B | ∃ h ∈ H, B = conjSub h A} := by
    ext B
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      exact ⟨h, hh, rfl⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, rfl⟩
  have hstab : MulAction.stabilizer H A = (Subgroup.normalizer (A : Set G)).subgroupOf H := by
    ext ⟨h, hh⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact conjSub_eq_self_iff
  have hcard : Nat.card (MulAction.stabilizer H A) =
      Nat.card (Subgroup.normalizer (A : Set G) ⊓ H : Subgroup G) := by
    rw [hstab, ← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h1 : Nat.card (MulAction.orbit H A) = (MulAction.stabilizer H A).index :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H A)
  rw [← Subgroup.card_mul_index (MulAction.stabilizer H A), hcard, mul_comm, ← h1, ← horb,
    Nat.card_coe_set_eq]

theorem le_ncard_conj {H A : Subgroup G} (s : Finset ℕ) (x : ℕ → G) (hx : ∀ i ∈ s, x i ∈ H)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, conjSub (x i) A = conjSub (x j) A → i = j) :
    s.card ≤ {B : Subgroup G | ∃ h ∈ H, B = conjSub h A}.ncard := by
  classical
  have hsub : (s.image fun i => conjSub (x i) A : Set (Subgroup G)) ⊆
      {B : Subgroup G | ∃ h ∈ H, B = conjSub h A} := by
    intro B hB
    rw [Finset.mem_coe, Finset.mem_image] at hB
    obtain ⟨i, hi, rfl⟩ := hB
    exact ⟨x i, hx i hi, rfl⟩
  have hcard : (s.image fun i => conjSub (x i) A).card = s.card :=
    Finset.card_image_of_injOn fun i hi j hj hij => hinj i hi j hj hij
  calc s.card = (s.image fun i => conjSub (x i) A : Set (Subgroup G)).ncard := by
        rw [Set.ncard_coe_finset, hcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem counting_conj {A P : Subgroup G} {N m : ℕ} (hP : P ≤ Subgroup.normalizer (A : Set G))
    (hG : Nat.card G = N * m) (hm : m ≤ Nat.card P) (B : ℕ → Subgroup G)
    (hB : ∀ n < N, ∃ x, B n = conjSub x A) (hinj : ∀ i < N, ∀ j < N, B i = B j → i = j) :
    P = Subgroup.normalizer (A : Set G) ∧ Nat.card (Subgroup.normalizer (A : Set G)) = m ∧
      ∀ x : G, ∃ n < N, conjSub x A = B n := by
  classical
  choose! x hx using hB
  have hΩ := card_eq_ncard_conj_mul (⊤ : Subgroup G) A
  rw [Subgroup.card_top, inf_top_eq] at hΩ
  set Ω : Set (Subgroup G) := {B | ∃ h ∈ (⊤ : Subgroup G), B = conjSub h A} with hΩdef
  have hN : N ≤ Ω.ncard := by
    have := le_ncard_conj (H := ⊤) (A := A) (Finset.range N) x (fun i _ => Subgroup.mem_top _)
      (fun i hi j hj hij => hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) (by
        rw [hx i (Finset.mem_range.mp hi), hx j (Finset.mem_range.mp hj)]
        exact hij))
    rwa [Finset.card_range] at this
  have hPN : Nat.card P ≤ Nat.card (Subgroup.normalizer (A : Set G)) := Subgroup.card_le_of_le hP
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hG
      omega
    · exact h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hG
      omega
    · exact h
  have h1 : m ≤ Nat.card (Subgroup.normalizer (A : Set G)) := le_trans hm hPN
  have h2 : N * m = Ω.ncard * Nat.card (Subgroup.normalizer (A : Set G)) := by rw [← hG]; exact hΩ
  have hΩeq : Ω.ncard = N := by
    by_contra hne
    have : N < Ω.ncard := lt_of_le_of_ne hN (Ne.symm hne)
    nlinarith
  have hNeq : Nat.card (Subgroup.normalizer (A : Set G)) = m := by
    by_contra hne
    have : m < Nat.card (Subgroup.normalizer (A : Set G)) := lt_of_le_of_ne h1 (Ne.symm hne)
    nlinarith
  refine ⟨Subgroup.eq_of_le_of_card_ge hP (by rw [hNeq]; exact hm), hNeq, ?_⟩
  have hsub : ((Finset.range N).image B : Set (Subgroup G)) ⊆ Ω := by
    intro C hC
    rw [Finset.mem_coe, Finset.mem_image] at hC
    obtain ⟨n, hn, rfl⟩ := hC
    exact ⟨x n, Subgroup.mem_top _, hx n (Finset.mem_range.mp hn)⟩
  have hcardimg : ((Finset.range N).image B).card = N := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have heq : ((Finset.range N).image B : Set (Subgroup G)) = Ω :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_coe_finset, hcardimg, hΩeq])
      (Set.toFinite _)
  intro y
  have hy : conjSub y A ∈ Ω := ⟨y, Subgroup.mem_top _, rfl⟩
  rw [← heq, Finset.mem_coe, Finset.mem_image] at hy
  obtain ⟨n, hn, hn'⟩ := hy
  exact ⟨n, Finset.mem_range.mp hn, hn'.symm⟩

theorem card_ge_chain {P Q A C : Subgroup G} (s₁ s₂ : Finset ℕ) (hQP : Q ≤ P)
    (hQA : Q ≤ Subgroup.normalizer (A : Set G)) (x : ℕ → G) (hx : ∀ i ∈ s₁, x i ∈ P)
    (hxinj : ∀ i ∈ s₁, ∀ j ∈ s₁, conjSub (x i) A = conjSub (x j) A → i = j)
    (y : ℕ → G) (hy : ∀ i ∈ s₂, y i ∈ Q)
    (hyinj : ∀ i ∈ s₂, ∀ j ∈ s₂, conjSub (y i) C = conjSub (y j) C → i = j) :
    s₁.card * s₂.card ≤ Nat.card P := by
  have h1 := le_ncard_conj (H := P) (A := A) s₁ x hx hxinj
  have h2 := le_ncard_conj (H := Q) (A := C) s₂ y hy hyinj
  have hP := card_eq_ncard_conj_mul P A
  have hQ := card_eq_ncard_conj_mul Q C
  have hQ' : s₂.card ≤ Nat.card Q := by
    rw [hQ]
    exact le_trans h2 (Nat.le_mul_of_pos_right _ Nat.card_pos)
  have hQ'' : Nat.card Q ≤ Nat.card (Subgroup.normalizer (A : Set G) ⊓ P : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf hQA hQP)
  rw [hP]
  exact Nat.mul_le_mul h1 (le_trans hQ' hQ'')

theorem maximal_of_trees {A : Subgroup G} {N m : ℕ} (hG : Nat.card G = N * m)
    (hm : Nat.card (Subgroup.normalizer (A : Set G)) = m) (hm0 : 0 < m) (B : ℕ → Subgroup G)
    (rt : ℕ → ℕ) (px : ℕ → G) (Br : ℕ → Subgroup G) (sz : ℕ → ℕ)
    (hsurj : ∀ x : G, ∃ n < N, conjSub x A = B n)
    (hinj : ∀ i < N, ∀ j < N, B i = B j → i = j)
    (hpx : ∀ n < N, px n ∈ Subgroup.normalizer (A : Set G) ∧ B n = conjSub (px n) (Br (rt n)))
    (hrt : ∀ n < N, rt n < 5) (hN0 : 0 < N) (hrt0 : rt 0 = 0) (hB0 : B 0 = A)
    (hsz : ∀ k < 5, sz k = ((Finset.range N).filter fun n => rt n = k).card) (hsz0 : sz 0 = 1)
    (hdiv : ∀ a b c d : Bool, N % (1 + (if a then sz 1 else 0) + (if b then sz 2 else 0) +
      (if c then sz 3 else 0) + (if d then sz 4 else 0)) = 0 →
      (a = false ∧ b = false ∧ c = false ∧ d = false) ∨
        (a = true ∧ b = true ∧ c = true ∧ d = true)) :
    ∀ H : Subgroup G, Subgroup.normalizer (A : Set G) ≤ H →
      H = Subgroup.normalizer (A : Set G) ∨ H = ⊤ := by
  classical
  intro H hNH
  set O : Set (Subgroup G) := {C | ∃ h ∈ H, C = conjSub h A} with hO
  have hcardH : Nat.card H = O.ncard * m := by
    have := card_eq_ncard_conj_mul H A
    rw [inf_eq_left.mpr hNH, hm] at this
    exact this
  have hdvd : O.ncard ∣ N := by
    have h1 : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
    rw [hcardH, hG] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hm0 h1
  have htree : ∀ n < N, ∀ n' < N, rt n = rt n' → B n ∈ O → B n' ∈ O := by
    intro n hn n' hn' hrr hBO
    obtain ⟨h, hh, hBn⟩ := hBO
    obtain ⟨hpn, hBn'⟩ := hpx n hn
    obtain ⟨hpn', hBn''⟩ := hpx n' hn'
    refine ⟨px n' * (px n)⁻¹ * h, H.mul_mem (H.mul_mem (hNH hpn') (H.inv_mem (hNH hpn))) hh, ?_⟩
    rw [conjSub_mul, ← hBn, hBn', ← conjSub_mul, inv_mul_cancel_right, hrr, ← hBn'']
  set a : ℕ → Prop := fun k => ∃ n < N, rt n = k ∧ B n ∈ O with ha
  have hA : A ∈ ({A} : Set (Subgroup G)) := rfl
  have hAO : A ∈ O := ⟨1, H.one_mem, (conjSub_one A).symm⟩
  have ha0 : a 0 := ⟨0, hN0, hrt0, by rw [hB0]; exact hAO⟩
  set J : Finset ℕ := (Finset.range N).filter fun n => a (rt n) with hJ
  have hOJ : O = ((J.image B : Finset (Subgroup G)) : Set (Subgroup G)) := by
    ext C
    constructor
    · intro hC
      obtain ⟨h, hh, rfl⟩ := hC
      obtain ⟨n, hn, hn'⟩ := hsurj h
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨n, ?_, hn'.symm⟩
      rw [hJ, Finset.mem_filter, Finset.mem_range]
      exact ⟨hn, n, hn, rfl, by rw [← hn']; exact ⟨h, hh, rfl⟩⟩
    · intro hC
      rw [Finset.mem_coe, Finset.mem_image] at hC
      obtain ⟨n, hn, rfl⟩ := hC
      rw [hJ, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hn, n₁, hn₁, hr, hB⟩ := hn
      exact htree n₁ hn₁ n hn hr hB
  have hOcard : O.ncard = J.card := by
    rw [hOJ, Set.ncard_coe_finset, Finset.card_image_of_injOn]
    intro i hi j hj hij
    rw [Finset.mem_coe, hJ, Finset.mem_filter, Finset.mem_range] at hi hj
    exact hinj i hi.1 j hj.1 hij
  have hsum : J.card = ∑ k ∈ Finset.range 5, (if a k then sz k else 0) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := rt) (t := Finset.range 5)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [hsz k hk]
      by_cases hak : a k
      · rw [ite_eq_left hak]
        congr 1
        ext n
        simp only [hJ, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨⟨hn, -⟩, hrn⟩
          exact ⟨hn, hrn⟩
        · rintro ⟨hn, hrn⟩
          exact ⟨⟨hn, by rw [hrn]; exact hak⟩, hrn⟩
      · rw [ite_eq_right hak, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro n hn hrn
        rw [hJ, Finset.mem_filter] at hn
        exact hak (hrn ▸ hn.2)
    · intro n hn
      rw [Finset.mem_coe, hJ, Finset.mem_filter, Finset.mem_range] at hn
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hrt n hn.1))
  have hsum' : O.ncard = 1 + (if a 1 then sz 1 else 0) + (if a 2 then sz 2 else 0) +
      (if a 3 then sz 3 else 0) + (if a 4 then sz 4 else 0) := by
    rw [hOcard, hsum]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ha0, ite_true, hsz0, zero_add]
  have hd := hdiv (decide (a 1)) (decide (a 2)) (decide (a 3)) (decide (a 4)) (by
    simp only [decide_eq_true_eq]
    rw [← hsum']
    exact Nat.mod_eq_zero_of_dvd hdvd)
  rcases hd with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · left
    simp only [decide_eq_false_iff_not] at h1 h2 h3 h4
    have hone : O.ncard = 1 := by
      rw [hsum', ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    obtain ⟨C, hC⟩ := Set.ncard_eq_one.mp hone
    refine le_antisymm (fun h hh => ?_) hNH
    rw [← Subgroup.mem_carrier] at hh
    have hmem : conjSub h A ∈ O := ⟨h, hh, rfl⟩
    rw [hC] at hmem hAO
    rw [Set.mem_singleton_iff] at hmem hAO
    exact conjSub_eq_self_iff.mp (hmem.trans hAO.symm)
  · right
    simp only [decide_eq_true_eq] at h1 h2 h3 h4
    have hJall : J = Finset.range N := by
      apply Finset.filter_true_of_mem
      intro n hn
      have hn' := hrt n (Finset.mem_range.mp hn)
      have : rt n = 0 ∨ rt n = 1 ∨ rt n = 2 ∨ rt n = 3 ∨ rt n = 4 := by omega
      rcases this with h | h | h | h | h <;> rw [h]
      · exact ha0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
    have hfull : Nat.card H = Nat.card G := by
      rw [hcardH, hOcard, hJall, Finset.card_range, hG]
    exact Subgroup.eq_top_of_card_eq H hfull

theorem simple_map {G A : Type*} [Group G] [Group A] (f : G →* A) (hf : Function.Injective f)
    {V : Subgroup G} {z : G}
    (hS : ∀ U : Subgroup G, U ≤ V → V ≤ Subgroup.normalizer (U : Set G) →
      U = ⊥ ∨ U ≤ Subgroup.zpowers z ∨ U = V) :
    ∀ U : Subgroup A, U ≤ V.map f → V.map f ≤ Subgroup.normalizer (U : Set A) →
      U = ⊥ ∨ U ≤ Subgroup.zpowers (f z) ∨ U = V.map f := by
  intro U hUV hN
  have hrange : U ≤ f.range := hUV.trans (Subgroup.map_le_range f V)
  have hmc : (U.comap f).map f = U := Subgroup.map_comap_eq_self hrange
  have hle : U.comap f ≤ V := by
    intro g hg
    obtain ⟨v, hv, hvg⟩ := hUV hg
    have : v = g := hf hvg
    exact this ▸ hv
  have hnorm : V ≤ Subgroup.normalizer ((U.comap f : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_map_of_mem f hv)) (f h)
    simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact h1
  rcases hS _ hle hnorm with h | h | h
  · left
    rw [← hmc, h, Subgroup.map_bot]
  · right
    left
    rw [← hmc]
    calc (U.comap f).map f ≤ (Subgroup.zpowers z).map f := Subgroup.map_mono h
      _ = Subgroup.zpowers (f z) := MonoidHom.map_zpowers f z
  · right
    right
    rw [← hmc, h]

theorem quasi_of_simple {A : Type*} [Group A] [Finite A] {V N W : Subgroup A} {z : A}
    (hperf : ⁅V, V⁆ = V) (hz : ∀ v ∈ V, z * v = v * z)
    (hS : ∀ U : Subgroup A, U ≤ V → V ≤ Subgroup.normalizer (U : Set A) →
      U = ⊥ ∨ U ≤ Subgroup.zpowers z ∨ U = V)
    (hVN : N ≤ Subgroup.normalizer (V : Set A)) (hW : W ≤ N)
    (hWN : V ≤ Subgroup.normalizer (W : Set A)) : V ≤ W ∨ ⁅W, V⁆ = ⊥ := by
  have hUV : ⁅W, V⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro w hw v hv
    have h1 : w * v * w⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hVN (hW hw)) v).mp hv
    show w * v * w⁻¹ * v⁻¹ ∈ V
    exact V.mul_mem h1 (V.inv_mem hv)
  have hUW : ⁅W, V⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro w hw v hv
    have h1 : v * w⁻¹ * v⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hWN hv) w⁻¹).mp (W.inv_mem hw)
    show w * v * w⁻¹ * v⁻¹ ∈ W
    have : w * v * w⁻¹ * v⁻¹ = w * (v * w⁻¹ * v⁻¹) := by group
    rw [this]
    exact W.mul_mem hw h1
  have hnormU : V ≤ Subgroup.normalizer ((⁅W, V⁆ : Subgroup A) : Set A) := by
    intro v hv
    apply mem_normalizer_of_conj_le
    intro x hx
    have hmap : (⁅W, V⁆).map (MulAut.conj v).toMonoidHom ≤ ⁅W, V⁆ := by
      rw [Subgroup.map_commutator]
      refine Subgroup.commutator_mono ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp (hWN hv) w).mp hw
        simpa [MulAut.conj_apply] using this
      · rintro _ ⟨u, hu, rfl⟩
        simpa [MulAut.conj_apply] using V.mul_mem (V.mul_mem hv hu) (V.inv_mem hv)
    have := hmap ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using this
  rcases hS _ hUV hnormU with h | h | h
  · exact Or.inr h
  · right
    have hcomm : ∀ U : Subgroup A, U ≤ Subgroup.zpowers z → ⁅U, V⁆ = ⊥ := by
      intro U hU
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro u hu v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hU hu)
      have hc : Commute z v := hz v hv
      have : Commute (z ^ k) v := hc.zpow_left k
      show z ^ k * v * (z ^ k)⁻¹ * v⁻¹ = 1
      rw [this.eq]
      group
    have h1 : ⁅⁅V, W⁆, V⁆ = ⊥ := by
      rw [Subgroup.commutator_comm V W]
      exact hcomm _ h
    have h2 : ⁅⁅W, V⁆, V⁆ = ⊥ := hcomm _ h
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hperf, Subgroup.commutator_comm] at h3
    exact h3
  · left
    calc V = ⁅W, V⁆ := h.symm
      _ ≤ W := hUW

theorem isElemAbelian_comap_injective {H : Type*} [Group H] {p : ℕ} (f : G →* H)
    (hf : Function.Injective f) {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩)
    simpa using this
  · apply hf
    rw [map_pow, map_one]
    exact hE.2 (f x) hx

end Generic

end CFSG.AGLEmbedding.KFactProofs.G28
