module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J2End

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_conj_iff (Q : Subgroup G) (g x : G) :
    x ∈ normalizer (rightConjugate Q g : Set G) ↔ g * x * g⁻¹ ∈ normalizer (Q : Set G) := by
  rw [← rightConjugate_eq_self_iff, ← rightConjugate_eq_self_iff, rightConjugate_mul]
  constructor
  · intro h
    calc rightConjugate Q (g * x * g⁻¹) = rightConjugate (rightConjugate Q (g * x)) g⁻¹ := by
          rw [rightConjugate_mul]
      _ = Q := by rw [h, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  · intro h
    calc rightConjugate Q (g * x) = rightConjugate (rightConjugate Q (g * x * g⁻¹)) g := by
          rw [rightConjugate_mul, inv_mul_cancel_right]
      _ = rightConjugate Q g := by rw [h]

theorem isSylowOf_conj {T M : Subgroup G} (hT : IsSylowOf 2 T M) (x : G) :
    IsSylowOf 2 (rightConjugate T x) (rightConjugate M x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact RankTwoSporadic.IsSylowOf.map hT (MulAut.conj x⁻¹).toMonoidHom

theorem mem_normalizer_conj_of_commute (hA : AS76b.Hyp31 A) {g t c : G}
    (ht : t ∈ rightConjugate (centralizer (A : Set G)) g) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hc : c * t = t * c) : c ∈ normalizer (rightConjugate A g : Set G) := by
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have h := mem_normalizer_of_commute_of_tightlyEmbedded (tightlyEmbedded_rightConjugate' hK g)
    ht ht1 ht2 hc
  rw [mem_normalizer_conj_iff] at h ⊢
  rwa [hA.standard.2.2.2.1] at h

theorem eq_one_of_mem_inf (hA : AS76b.Hyp31 A) {y z : G} (hy : y ∉ normalizer (A : Set G))
    (hzK : z ∈ centralizer (A : Set G)) (hzy : z ∈ rightConjugate (centralizer (A : Set G)) y)
    (hz2 : z ^ 2 = 1) : z = 1 := by
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hyK : y ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.standard.2.2.2.1]
    exact hy
  have hodd := (hK.2 y hyK).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ (mem_inf.mpr ⟨hzK, hzy⟩))
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem sq_eq_one_of_isSylowOf (h32 : AS76b.Lemma32) (hA : AS76b.Hyp31 A) {g : G}
    {T : Subgroup G} (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    ∀ x ∈ T, x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := h32 G A hA
  intro x hx
  have hxK : g * x * g⁻¹ ∈ centralizer (A : Set G) :=
    (mem_rightConjugate_iff _ g x).mp (hT.le hx)
  have h2 : IsPGroup 2 (zpowers (g * x * g⁻¹)) := by
    have hx2 : IsPGroup 2 (zpowers x) := hT.isPGroup.to_le (zpowers_le.mpr hx)
    have := hx2.map (MulAut.conj g).toMonoidHom
    rwa [MonoidHom.map_zpowers] at this
  have hsq := sq_eq_one_of_isPGroup_zpowers hR hxK h2
  have hc' : (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := conj_pow
  rw [hc'] at hsq
  have := congrArg (fun y => g⁻¹ * y * g) hsq
  simpa [mul_assoc] using this

theorem four_le_card_of_isSylowOf (hA : AS76b.Hyp31 A) {g : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) : 4 ≤ Nat.card T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hT.card_eq, rightConjugate_card]
  have h4 := four_dvd_card_of_one_lt_pRank hA.rank
  have hpos : Nat.card (centralizer (A : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hle : 2 ≤ (Nat.card (centralizer (A : Set G))).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp (by simpa using h4)
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle

theorem inf_centralizer_eq_bot (hA : AS76b.Hyp31 A) {g : G} (hg : g ∉ normalizer (A : Set G))
    {T : Subgroup G} (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    T ⊓ centralizer (A : Set G) = ⊥ := by
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := by
    rw [hA.standard.2.2.2.1]
    exact hg
  exact two_subgroup_of_odd_eq_bot _ (centralizer (A : Set G) ⊓
    rightConjugate (centralizer (A : Set G)) g) hT.isPGroup.to_inf_left (hK.2 g hgK)
    (le_inf inf_le_right (inf_le_left.trans hT.le))

theorem exc_of_sylow (h32 : AS76b.Lemma32) (hA : AS76b.Hyp31 A) {W : Type*} [Group W] [Finite W]
    {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {Exc : Subgroup W → Prop} (hc : YCensus X Exc) {g : G} (hg : g ∉ normalizer (A : Set G))
    {T : Subgroup G}
    (hT1 : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g ⊓ normalizer (A : Set G)))
    (hT2 : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g)) :
    Exc ((T.subgroupOf (normalizer (A : Set G))).map ψ) := by
  by_contra hExc
  have hK := tightlyEmbedded_centralizer_of_standard hA.standard
  have hTab := sq_eq_one_of_isSylowOf h32 hA hT2
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c →
      c ∈ normalizer (rightConjugate (centralizer (A : Set G)) g : Set G) :=
    fun t ht ht1 c _ hct => mem_normalizer_of_commute_of_tightlyEmbedded
      (tightlyEmbedded_rightConjugate' hK g) (hT2.le ht) ht1 (hTab t ht) hct
  refine not_yWitness_map hψ hT1 hTab hQ (hc _ ?_ ?_ hExc)
  · refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact commute_of_sq_eq_one hTab hx hy
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab _ hx)
      rw [this, map_one]
  · have hTN : T ≤ normalizer (A : Set G) := hT1.le.trans inf_le_right
    rw [card_map_eq_of_inf_centralizer hψ (inf_centralizer_eq_bot hA hg hT2),
      Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv]
    exact four_le_card_of_isSylowOf hA hT2

theorem exc_of_sylow_conj (h32 : AS76b.Lemma32) (hA : AS76b.Hyp31 A) {W : Type*} [Group W]
    [Finite W] {X : Subgroup W} {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ)
    {Exc : Subgroup W → Prop} (hc : YCensus X Exc) {g y : G}
    (hne : rightConjugate (centralizer (A : Set G)) y ≠
      rightConjugate (centralizer (A : Set G)) g)
    {T' : Subgroup G} (hT' : IsSylowOf 2 T' (rightConjugate (centralizer (A : Set G)) y))
    (hTN : T' ≤ normalizer (rightConjugate A g : Set G)) :
    Exc (((rightConjugate T' g⁻¹).subgroupOf (normalizer (A : Set G))).map ψ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsSylowOf 2 (rightConjugate T' g⁻¹)
      (rightConjugate (centralizer (A : Set G)) (y * g⁻¹)) := by
    rw [← rightConjugate_mul]
    exact isSylowOf_conj hT' g⁻¹
  have hyg : y * g⁻¹ ∉ normalizer (A : Set G) := by
    intro h
    rw [← hA.standard.2.2.2.1, ← rightConjugate_eq_self_iff] at h
    apply hne
    rw [show y = y * g⁻¹ * g by group, ← rightConjugate_mul, h]
  have hN : rightConjugate T' g⁻¹ ≤ normalizer (A : Set G) := by
    intro x hx
    have hx' := hTN ((mem_rightConjugate_iff _ g⁻¹ x).mp hx)
    rw [mem_normalizer_conj_iff] at hx'
    simpa [mul_assoc] using hx'
  exact exc_of_sylow h32 hA hψ hc hyg (hT2.of_le (le_inf hT2.le hN) inf_le_left) hT2

omit [Finite G] in
theorem mem_center_of_mem {z : G} (hzA : z ∈ A) (hzK : z ∈ centralizer (A : Set G)) :
    (⟨z, hzA⟩ : A) ∈ center A := by
  rw [mem_center_iff]
  intro b
  apply Subtype.ext
  simp only [coe_mul]
  exact mem_centralizer_iff.mp hzK b b.2

omit [Finite G] in
theorem odd_orderOf_of_mem (hZ : Odd (Nat.card (center A))) {z : G} (hzA : z ∈ A)
    (hzK : z ∈ centralizer (A : Set G)) : Odd (orderOf z) := by
  have h1 := Subgroup.orderOf_dvd_natCard (center A) (mem_center_of_mem hzA hzK)
  rw [Subgroup.orderOf_mk] at h1
  exact hZ.of_dvd_nat h1

omit [Finite G] in
theorem eq_one_of_mem_of_sq_eq_one (hZ : Odd (Nat.card (center A))) {z : G} (hzA : z ∈ A)
    (hzK : z ∈ centralizer (A : Set G)) (h2 : z ^ 2 = 1) : z = 1 := by
  have hodd := odd_orderOf_of_mem hZ hzA hzK
  rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

omit [Finite G] in
theorem exists_pow_eq (hZ : Odd (Nat.card (center A))) {u v : G} (hu : u ∈ A) (hv : v ∈ A)
    (hk : v⁻¹ * u ∈ centralizer (A : Set G)) (hu2 : u ^ 2 = 1) : ∃ m : ℕ, v ^ m = u := by
  set z := v⁻¹ * u with hz
  have hzA : z ∈ A := A.mul_mem (A.inv_mem hv) hu
  obtain ⟨k, hk'⟩ := odd_orderOf_of_mem hZ hzA hk
  have hc : Commute u z⁻¹ := mem_centralizer_iff.mp (inv_mem hk) u hu
  refine ⟨orderOf z, ?_⟩
  have hv' : v = u * z⁻¹ := by rw [hz]; group
  rw [hv', hc.mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one, hk', pow_succ, pow_mul,
    hu2, one_pow, one_mul]

section Action

variable {W : Type*} [Group W] {X : Subgroup W} {ψ : normalizer (A : Set G) →* W}

omit [Finite G] in
theorem commutatorElement_mem_centralizer (hψ : IsActionHom A X ψ)
    {n m : normalizer (A : Set G)} (h : ψ n * ψ m = ψ m * ψ n) :
    ⁅(n : G), (m : G)⁆ ∈ centralizer (A : Set G) := by
  have h1 : ψ ⁅n, m⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have h2 := (hψ.eq_one_iff _).mp h1
  simpa [commutatorElement_def] using h2

omit [Finite G] in
theorem commutatorElement_mem_of_mem_left {n m : G} (hn : n ∈ A)
    (hm : m ∈ normalizer (A : Set G)) : ⁅n, m⁆ ∈ A := by
  have h : m * n⁻¹ * m⁻¹ ∈ A := (mem_normalizer_iff.mp hm n⁻¹).mp (A.inv_mem hn)
  have h' := A.mul_mem hn h
  rwa [commutatorElement_def, show n * m * n⁻¹ * m⁻¹ = n * (m * n⁻¹ * m⁻¹) by group]

omit [Finite G] in
theorem commute_of_map_mem (hψ : IsActionHom A X ψ) {n : normalizer (A : Set G)} (hn : ψ n ∈ X)
    {z : G} (hzA : z ∈ A) (hzK : z ∈ centralizer (A : Set G)) : (n : G) * z = z * n := by
  obtain ⟨a, ha, hae⟩ := hψ.exists_eq _ hn
  have hk : a⁻¹ * (n : G) ∈ centralizer (A : Set G) := by
    have h1 : ψ ((⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * n) = 1 := by
      rw [map_mul, map_inv, hae, inv_mul_cancel]
    simpa using (hψ.eq_one_iff _).mp h1
  have h1 : a * z = z * a := mem_centralizer_iff.mp hzK a ha
  have h2 : (a⁻¹ * n) * z = z * (a⁻¹ * n) := (mem_centralizer_iff.mp hk z hzA).symm
  calc (n : G) * z = a * ((a⁻¹ * n) * z) := by group
    _ = a * (z * (a⁻¹ * n)) := by rw [h2]
    _ = (a * z) * (a⁻¹ * n) := by group
    _ = (z * a) * (a⁻¹ * n) := by rw [h1]
    _ = z * n := by group

omit [Finite G] in
theorem commute_commutatorElement (hψ : IsActionHom A X ψ) {s : normalizer (A : Set G)}
    {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (hsa : ψ s * ψ ⟨a, le_normalizer ha⟩ = ψ ⟨a, le_normalizer ha⟩ * ψ s)
    (hsb : ψ s * ψ ⟨b, le_normalizer hb⟩ = ψ ⟨b, le_normalizer hb⟩ * ψ s) :
    (s : G) * ⁅a, b⁆ = ⁅a, b⁆ * s := by
  have hza := commutatorElement_mem_centralizer hψ hsa.symm
  have hzb := commutatorElement_mem_centralizer hψ hsb.symm
  have hzaA : ⁅a, (s : G)⁆ ∈ A := commutatorElement_mem_of_mem_left ha s.2
  have hzbA : ⁅b, (s : G)⁆ ∈ A := commutatorElement_mem_of_mem_left hb s.2
  have hcomm : ∀ {z y : G}, z ∈ centralizer (A : Set G) → y ∈ A → Commute z⁻¹ y :=
    fun hz hy => (mem_centralizer_iff.mp (inv_mem hz) _ hy).symm
  have e1 : (s : G) * a * (s : G)⁻¹ = ⁅a, (s : G)⁆⁻¹ * a := by
    rw [commutatorElement_def]
    group
  have e2 : (s : G) * b * (s : G)⁻¹ = ⁅b, (s : G)⁆⁻¹ * b := by
    rw [commutatorElement_def]
    group
  have hconj : (s : G) * ⁅a, b⁆ * (s : G)⁻¹ = ⁅a, b⁆ := by
    calc (s : G) * ⁅a, b⁆ * (s : G)⁻¹
        = ⁅(s : G) * a * (s : G)⁻¹, (s : G) * b * (s : G)⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅⁅a, (s : G)⁆⁻¹ * a, ⁅b, (s : G)⁆⁻¹ * b⁆ := by rw [e1, e2]
      _ = ⁅a, b⁆ := commutatorElement_mul_left_central (hcomm hza ha) (hcomm hza hb)
          (hcomm hzb ha) (hcomm hzb hb) (hcomm hza (A.inv_mem hzbA))
  calc (s : G) * ⁅a, b⁆ = (s : G) * ⁅a, b⁆ * (s : G)⁻¹ * s := by group
    _ = ⁅a, b⁆ * s := by rw [hconj]

omit [Finite G] in
theorem commute_conj_of_map (hψ : IsActionHom A X ψ) (hZ : Odd (Nat.card (center A)))
    {s y : normalizer (A : Set G)} {a : G} (ha : a ∈ A) {y' : normalizer (A : Set G)}
    (hy' : (y' : G) = a⁻¹ * y * a) (hsy : (s : G) * y = y * s) (hs2 : (s : G) ^ 2 = 1)
    (hy2 : (y : G) ^ 2 = 1) (hsX : ψ s ∈ X) (h : ψ s * ψ y' = ψ y' * ψ s) :
    (s : G) * y' = y' * s := by
  have hzK := commutatorElement_mem_centralizer hψ h
  set m : G := (y : G)⁻¹ * a⁻¹ * y * a with hm
  have hmA : m ∈ A := by
    have h1 : (y : G)⁻¹ * a⁻¹ * ((y : G)⁻¹)⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (inv_mem y.2) a⁻¹).mp (A.inv_mem ha)
    rw [inv_inv] at h1
    exact A.mul_mem h1 ha
  have hzA : ⁅(s : G), (y' : G)⁆ ∈ A := by
    have e : ⁅(s : G), (y' : G)⁆ = (y : G) * ⁅(s : G), m⁆ * (y : G)⁻¹ := by
      have hyy : (y' : G) = y * m := by rw [hy', hm]; group
      rw [hyy, commutatorElement_def, commutatorElement_def]
      calc (s : G) * (y * m) * (s : G)⁻¹ * (y * m)⁻¹
          = ((s : G) * y) * m * (s : G)⁻¹ * m⁻¹ * (y : G)⁻¹ := by group
        _ = ((y : G) * s) * m * (s : G)⁻¹ * m⁻¹ * (y : G)⁻¹ := by rw [hsy]
        _ = (y : G) * ((s : G) * m * (s : G)⁻¹ * m⁻¹) * (y : G)⁻¹ := by group
    have hsm : ⁅(s : G), m⁆ ∈ A := by
      rw [commutatorElement_def]
      exact A.mul_mem ((mem_normalizer_iff.mp s.2 m).mp hmA) (A.inv_mem hmA)
    rw [e]
    exact (mem_normalizer_iff.mp y.2 _).mp hsm
  have hsz := commute_of_map_mem hψ hsX hzA hzK
  have hss : (s : G) * s = 1 := by rw [← sq]; exact hs2
  have hs1 : (s : G)⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hy'2 : (y' : G) * y' = 1 := by
    rw [hy']
    calc a⁻¹ * (y : G) * a * (a⁻¹ * y * a) = a⁻¹ * ((y : G) ^ 2) * a := by rw [sq]; group
      _ = 1 := by rw [hy2]; group
  have hy1 : (y' : G)⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'2
  have hz : ⁅(s : G), (y' : G)⁆ = s * y' * s * y' := by rw [commutatorElement_def, hs1, hy1]
  have hzinv : ⁅(s : G), (y' : G)⁆⁻¹ = y' * s * y' * s := by
    rw [hz]
    simp only [mul_inv_rev, hs1, hy1, mul_assoc]
  have hsz' : (s : G) * ⁅(s : G), (y' : G)⁆ * s = ⁅(s : G), (y' : G)⁆⁻¹ := by
    rw [hzinv, hz]
    calc (s : G) * (s * y' * s * y') * s = ((s : G) * s) * (y' * s * y' * s) := by
          simp only [mul_assoc]
      _ = y' * s * y' * s := by rw [hss, one_mul]
  have hz2 : ⁅(s : G), (y' : G)⁆ ^ 2 = 1 := by
    have e : (s : G) * ⁅(s : G), (y' : G)⁆ * s = ⁅(s : G), (y' : G)⁆ := by
      rw [hsz, mul_assoc, hss, mul_one]
    rw [e] at hsz'
    rw [sq]
    nth_rewrite 2 [hsz']
    exact mul_inv_cancel _
  have hz1 := eq_one_of_mem_of_sq_eq_one hZ hzA hzK hz2
  exact commutatorElement_eq_one_iff_mul_comm.mp hz1

end Action

end CFSG.ComponentClassification.RankTwoSporadic.J2End
