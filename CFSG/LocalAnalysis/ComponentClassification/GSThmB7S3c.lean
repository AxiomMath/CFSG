module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSec59
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Sec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Setup
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Seven

variable {G : Type*} [Group G] {P : Subgroup G} {p r : G}

theorem two_pow_dvd_of_dvd_mul_sub {n : ℕ} (hn : 3 ≤ n) {k : ℤ}
    (h : (2 : ℤ) ^ n ∣ ((2 : ℤ) ^ (n - 1) - 2) * k) : (2 : ℤ) ^ (n - 1) ∣ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h2 : (2 : ℤ) ^ (m + 3) = 2 * 2 ^ (m + 2) := by rw [pow_succ]; ring
  have h3 : ((2 : ℤ) ^ (m + 3 - 1) - 2) * k = 2 * ((2 ^ (m + 1) - 1) * k) := by
    rw [show m + 3 - 1 = m + 2 by omega, pow_succ, pow_succ]; ring
  rw [h2, h3] at h
  have h4 : (2 : ℤ) ^ (m + 2) ∣ (2 ^ (m + 1) - 1) * k :=
    (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h
  have hcop : IsCoprime ((2 : ℤ) ^ (m + 2)) (2 ^ (m + 1) - 1) := by
    refine IsCoprime.pow_left ?_
    refine ⟨2 ^ m, -1, ?_⟩
    rw [pow_succ]
    ring
  rw [show m + 3 - 1 = m + 2 by omega]
  exact hcop.dvd_of_dvd_mul_left h4

theorem two_pow_dvd_of_dvd_two_mul {n : ℕ} (hn : 1 ≤ n) {k : ℤ}
    (h : (2 : ℤ) ^ n ∣ 2 * k) : (2 : ℤ) ^ (n - 1) ∣ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega]
  rw [pow_succ, mul_comm] at h
  exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h

variable [Finite G]

theorem mem_zpowers_half_of_comm (hp : p ∈ P) (hrP : r ∈ P) (hcl : closure {p, r} = P)
    (hc : 2 * orderOf p = Nat.card P)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (hpow : ∃ n : ℕ, orderOf p = 2 ^ n) (h4 : 4 ≤ orderOf p) (hnab : r * p * r⁻¹ ≠ p)
    {u : G} (hu : u ∈ P) (hup : u ∉ zpowers p) {k : ℤ} (hk : u * p ^ k = p ^ k * u) :
    ∃ l : ℤ, k = (orderOf p / 2 : ℕ) * l := by
  obtain ⟨n, hn⟩ := hpow
  have hn2 : 2 ≤ n := by
    by_contra hlt
    interval_cases n <;> rw [hn] at h4 <;> norm_num at h4
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp
    ((mem_presentation_cases hp hrP hcl hc hu).resolve_left hup)
  have hu' : u = r * p ^ j := by rw [hj]; group
  have hconj : u * p ^ k * u⁻¹ = (r * p * r⁻¹) ^ k := by
    rw [hu', conj_zpow]
    have hc1 : p ^ j * p ^ k = p ^ k * p ^ j := (Commute.zpow_zpow_self p j k).eq
    calc r * p ^ j * p ^ k * (r * p ^ j)⁻¹ = r * (p ^ j * p ^ k) * p ^ (-j) * r⁻¹ := by
          rw [zpow_neg]; group
      _ = r * (p ^ k * p ^ j) * p ^ (-j) * r⁻¹ := by rw [hc1]
      _ = r * p ^ k * r⁻¹ := by rw [zpow_neg]; group
  have hfix : (r * p * r⁻¹) ^ k = p ^ k := by
    rw [← hconj, hk, mul_inv_cancel_right]
  have hhalf : (orderOf p / 2 : ℕ) = 2 ^ (n - 1) := by
    rw [hn, show n = (n - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    congr 1
  rcases hrel with h1 | h1
  · rw [h1, inv_zpow] at hfix
    have h2 : p ^ (2 * k) = 1 := by
      rw [two_mul, zpow_add]
      nth_rewrite 1 [← hfix]
      exact inv_mul_cancel _
    have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
    rw [hn, Nat.cast_pow, Nat.cast_ofNat] at h3
    obtain ⟨l, hl⟩ := two_pow_dvd_of_dvd_two_mul (by omega) h3
    exact ⟨l, by rw [hhalf, Nat.cast_pow, Nat.cast_ofNat, hl]⟩
  · rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · exfalso
      obtain rfl : n = 2 := by omega
      apply hnab
      rw [h1, hn]
      norm_num
    · rw [h1, ← zpow_natCast, ← zpow_mul] at hfix
      have h2 : p ^ (((orderOf p / 2 - 1 : ℕ) : ℤ) * k - k) = 1 := by
        rw [zpow_sub, hfix, mul_inv_cancel]
      have h3 := orderOf_dvd_iff_zpow_eq_one.mpr h2
      rw [hn] at h3
      have e : (((2 ^ n / 2 - 1 : ℕ) : ℤ) * k - k) = ((2 : ℤ) ^ (n - 1) - 2) * k := by
        have h5 : 2 ^ n / 2 = 2 ^ (n - 1) := by
          rw [show n = (n - 1) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
          congr 1
        rw [h5]
        have h6 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
        push_cast [h6]
        ring
      rw [e, Nat.cast_pow, Nat.cast_ofNat] at h3
      obtain ⟨l, hl⟩ := two_pow_dvd_of_dvd_mul_sub hn3 h3
      exact ⟨l, by rw [hhalf, Nat.cast_pow, Nat.cast_ofNat, hl]⟩

theorem card_inf_centralizer_le_four (hp : p ∈ P) (hrP : r ∈ P) (hcl : closure {p, r} = P)
    (hc : 2 * orderOf p = Nat.card P)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (hpow : ∃ n : ℕ, orderOf p = 2 ^ n) (h4 : 4 ≤ orderOf p) (hnab : r * p * r⁻¹ ≠ p)
    {w : G} (hw : w ∈ P) (hwp : w ∉ zpowers p) :
    Nat.card ↥(P ⊓ centralizer ({w} : Set G)) ≤ 4 := by
  classical
  set z := p ^ (orderOf p / 2) with hz
  have hzz : z * z = 1 := by
    obtain ⟨n, hn⟩ := hpow
    have h2 : 2 ∣ orderOf p := by
      rw [hn]
      exact dvd_pow_self 2 (by rintro rfl; rw [pow_zero] at hn; omega)
    rw [hz, ← pow_add, show orderOf p / 2 + orderOf p / 2 = orderOf p by omega,
      pow_orderOf_eq_one]
  have hcyc : ∀ c ∈ zpowers p, c * w = w * c → c = 1 ∨ c = z := by
    intro c hcp hcw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hcp
    obtain ⟨l, hl⟩ := mem_zpowers_half_of_comm hp hrP hcl hc hrel hpow h4 hnab hw hwp hcw.symm
    rw [hl, zpow_mul, zpow_natCast, ← hz]
    rcases Int.even_or_odd l with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [← two_mul, zpow_mul, zpow_two, hzz, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hzz, one_zpow, one_mul, zpow_one]
  have hsub : ((P ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) ⊆
      (({1, z, w, w * z} : Finset G) : Set G) := by
    intro c hc'
    obtain ⟨hcP, hcw⟩ := mem_inf.mp hc'
    have hcw' : c * w = w * c := mem_centralizer_singleton_iff.mp hcw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases mem_presentation_cases hp hrP hcl hc hcP with h1 | h1
    · rcases hcyc c h1 hcw' with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    ·
      have hw1 := (mem_presentation_cases hp hrP hcl hc hw).resolve_left hwp
      have h2 : w⁻¹ * c ∈ zpowers p := by
        have := mul_mem (inv_mem hw1) h1
        rwa [show (r⁻¹ * w)⁻¹ * (r⁻¹ * c) = w⁻¹ * c by group] at this
      have h3 : w⁻¹ * c * w = w * (w⁻¹ * c) := by
        rw [mul_assoc, hcw']
        group
      rcases hcyc _ h2 h3 with h4 | h4
      · right; right; left
        calc c = w * (w⁻¹ * c) := by group
          _ = w := by rw [h4, mul_one]
      · right; right; right
        calc c = w * (w⁻¹ * c) := by group
          _ = w * z := by rw [h4]
  calc Nat.card ↥(P ⊓ centralizer ({w} : Set G))
      = Set.ncard ((P ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G) :=
        (Nat.card_coe_set_eq _)
    _ ≤ Set.ncard (({1, z, w, w * z} : Finset G) : Set G) := Set.ncard_le_ncard hsub
    _ = ({1, z, w, w * z} : Finset G).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

omit [Finite G] in
theorem ncard_orbit_mul_card (S : Subgroup G) (x : ↥S) :
    (MulAction.orbit (ConjAct ↥S) x).ncard * Nat.card ↥(S ⊓ centralizer ({(x : G)} : Set G)) =
      Nat.card ↥S := by
  have h1 := MulAction.index_stabilizer (ConjAct ↥S) x
  have h2 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct ↥S) x)
  have h3 := Subgroup.nat_card_centralizer_nat_card_stabilizer x
  have h4 : (centralizer ({x} : Set ↥S)).map S.subtype = S ⊓ centralizer ({(x : G)} : Set G) := by
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine mem_inf.mpr ⟨s.2, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hs)
    · intro hg
      obtain ⟨hgS, hgc⟩ := mem_inf.mp hg
      refine ⟨⟨g, hgS⟩, mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      exact mem_centralizer_singleton_iff.mp hgc
  have h5 : Nat.card (centralizer ({x} : Set ↥S)) =
      Nat.card ↥(S ⊓ centralizer ({(x : G)} : Set G)) := by
    rw [← h4, card_map_of_injective S.subtype_injective]
  have h6 : Nat.card (ConjAct ↥S) = Nat.card ↥S := Nat.card_congr ConjAct.ofConjAct.toEquiv
  rw [← h1, ← h5, h3, mul_comm, h2, h6]

theorem card_centralizer_eq_of_maxClass {S : Subgroup G} (hPS : P ≤ S) (hp : p ∈ P)
    (hrP : r ∈ P) (hcl : closure {p, r} = P) (hc : 2 * orderOf p = Nat.card P)
    (hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1))
    (hpow : ∃ n : ℕ, orderOf p = 2 ^ n) (h4 : 4 ≤ orderOf p) (hnab : r * p * r⁻¹ ≠ p)
    (hSp : ∀ s ∈ S, s * p * s⁻¹ ∈ zpowers p) (hSP : ∀ s ∈ S, ∀ w ∈ P, s * w * s⁻¹ ∈ P)
    {u v : G} (hu : u ∈ P) (hup : u ∉ zpowers p) (hv : v ∈ P) (hvp : v ∉ zpowers p) :
    Nat.card ↥(S ⊓ centralizer ({u} : Set G)) = Nat.card ↥(S ⊓ centralizer ({v} : Set G)) := by
  classical
  set m := orderOf p with hm
  set I : Set ↥S := {w | (w : G) ∈ P ∧ (w : G) ∉ zpowers p} with hI
  have hIcard : I.ncard ≤ m := by
    have h1 : I.ncard = (Subtype.val '' I).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    have h2 : Subtype.val '' I ⊆ (P : Set G) \ (zpowers p : Set G) := by
      rintro _ ⟨w, ⟨hwP, hwp⟩, rfl⟩
      exact ⟨hwP, hwp⟩
    have h3 : ((P : Set G) \ (zpowers p : Set G)).ncard = m := by
      rw [Set.ncard_sdiff (fun x hx => (zpowers_le.mpr hp) hx), ← Nat.card_coe_set_eq,
        ← Nat.card_coe_set_eq]
      change Nat.card ↥P - Nat.card ↥(zpowers p) = m
      rw [Nat.card_zpowers, ← hc]
      omega
    rw [h1, ← h3]
    exact Set.ncard_le_ncard h2
  have hSpz : ∀ s ∈ S, ∀ x ∈ zpowers p, s * x * s⁻¹ ∈ zpowers p := by
    intro s hs x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    rw [← conj_zpow]
    exact zpow_mem (hSp s hs) k
  have horb : ∀ w ∈ I, MulAction.orbit (ConjAct ↥S) w ⊆ I := by
    rintro w ⟨hwP, hwp⟩ _ ⟨g, rfl⟩
    show g • w ∈ I
    rw [ConjAct.smul_def]
    set s := ConjAct.ofConjAct g with hs
    refine ⟨?_, fun h1 => hwp ?_⟩
    · exact hSP s s.2 w hwP
    · have h2 := hSpz s⁻¹ (inv_mem s.2) _ h1
      have h3 : ((s : G)⁻¹ * ((s * w * s⁻¹ : ↥S) : G) * (s : G)⁻¹⁻¹) = w := by
        push_cast
        group
      rwa [h3] at h2
  have hbig : ∀ w ∈ I, m ≤ 2 * (MulAction.orbit (ConjAct ↥S) w).ncard := by
    rintro w ⟨hwP, hwp⟩
    have h1 := ncard_orbit_mul_card S w
    have h2 := relIndex_mul_card (centralizer ({(w : G)} : Set G)) S
    have h3 := relIndex_mul_card (centralizer ({(w : G)} : Set G)) P
    have h4 := card_inf_centralizer_le_four hp hrP hcl hc hrel hpow h4 hnab hwP hwp
    rw [inf_comm] at h2 h3
    have hpos : 0 < Nat.card ↥(S ⊓ centralizer ({(w : G)} : Set G)) := Nat.card_pos
    have h5 : (MulAction.orbit (ConjAct ↥S) w).ncard =
        (centralizer ({(w : G)} : Set G)).relIndex S :=
      Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    have h6 : (centralizer ({(w : G)} : Set G)).relIndex P ≤
        (centralizer ({(w : G)} : Set G)).relIndex S := by
      refine relIndex_le_of_le_right hPS ?_
      intro h0
      rw [h0, zero_mul] at h2
      exact (Nat.card_pos (α := ↥S)).ne' h2.symm
    have h7 : 2 * m ≤ 4 * (centralizer ({(w : G)} : Set G)).relIndex P := by
      rw [hm, hc, ← h3, mul_comm]
      exact Nat.mul_le_mul_right _ h4
    omega
  set u' : ↥S := ⟨u, hPS hu⟩
  set v' : ↥S := ⟨v, hPS hv⟩
  have huI : u' ∈ I := ⟨hu, hup⟩
  have hvI : v' ∈ I := ⟨hv, hvp⟩
  have heq : (MulAction.orbit (ConjAct ↥S) u').ncard = (MulAction.orbit (ConjAct ↥S) v').ncard := by
    by_cases hvu : v' ∈ MulAction.orbit (ConjAct ↥S) u'
    · rw [MulAction.orbit_eq_iff.mpr hvu]
    · have hdisj :
          Disjoint (MulAction.orbit (ConjAct ↥S) u') (MulAction.orbit (ConjAct ↥S) v') := by
        rw [Set.disjoint_left]
        intro w hwu hwv
        apply hvu
        rw [← MulAction.orbit_eq_iff.mpr hwu, MulAction.orbit_eq_iff.mpr hwv]
        exact MulAction.mem_orbit_self v'
      have h1 := Set.ncard_union_eq hdisj
      have h2 : (MulAction.orbit (ConjAct ↥S) u' ∪ MulAction.orbit (ConjAct ↥S) v').ncard ≤ m :=
        (Set.ncard_le_ncard (Set.union_subset (horb u' huI) (horb v' hvI))).trans hIcard
      have h3 := hbig u' huI
      have h4 := hbig v' hvI
      omega
  have h1 := ncard_orbit_mul_card S u'
  have h2 := ncard_orbit_mul_card S v'
  have hpos : 0 < (MulAction.orbit (ConjAct ↥S) v').ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨v', MulAction.mem_orbit_self v'⟩
  rw [heq] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

end Seven

end CFSG.ComponentClassification.GSThmB
