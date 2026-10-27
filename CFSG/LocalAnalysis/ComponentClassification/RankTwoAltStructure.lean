module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltRegular
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoHypIIY
  CFSG.ComponentClassification.RankTwoClassical
  CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

section Parts

variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include hc h32 h4 h34

theorem exists_mul_of_mem_T {t : G} (ht : t ∈ T) : ∃ p ∈ A, ∃ r ∈ R, t = p * r := by
  obtain ⟨p, hp, hpr⟩ := hc.exists_aPart h32 h4 h34 ht
  exact ⟨p, hp, (t⁻¹ * p)⁻¹, R.inv_mem hpr, by group⟩

end Parts

omit [Finite G] in
theorem exists_mul_of_mem_sup_inf {x : G} (hRA : R ≤ normalizer (A : Set G))
    (hRK : R ≤ Subgroup.centralizer (A : Set G)) (hx : x ∈ R ⊔ A)
    (hxK : x ∈ Subgroup.centralizer (A : Set G)) :
    ∃ r ∈ R, ∃ z ∈ A ⊓ Subgroup.centralizer (A : Set G), x = r * z := by
  have h := hx
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right R A hRA] at h
  obtain ⟨r, hr, z, hz, rfl⟩ := h
  refine ⟨r, hr, z, ⟨hz, ?_⟩, rfl⟩
  show z ∈ Subgroup.centralizer (A : Set G)
  have : z = r⁻¹ * (r * z) := by group
  rw [this]
  exact mul_mem (inv_mem (hRK hr)) hxK

section Conj

variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include hc h32 h4 h34

omit h32 h4 h34 in
theorem R_le_centralizer : R ≤ Subgroup.centralizer (A : Set G) := hc.sylowR.le

omit h32 h4 h34 in
theorem R_le_normalizer : R ≤ normalizer (A : Set G) :=
  (R_le_centralizer hc).trans (centralizer_le_normalizer _)

theorem rightConjugate_le_sup {a : G} (ha : a ∈ A) : rightConjugate T a ≤ R ⊔ A := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have h1 : a * x * a⁻¹ ∈ R ⊔ A := hc.le_sup h32 h4 h34 hx
  have h2 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
  rw [h2]
  exact mul_mem (mul_mem (inv_mem (le_sup_right (a := R) ha)) h1) (le_sup_right (a := R) ha)

omit h32 h4 h34 in
theorem rightConjugate_le_centralizer {a : G} (ha : a ∈ A) :
    rightConjugate T a ≤ Subgroup.centralizer (R : Set G) := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have hxT := hc.le_centralizer hx
  have hRA := R_le_centralizer hc
  rw [mem_centralizer_iff] at hxT ⊢
  intro r hr
  have har : Commute a r := mem_centralizer_iff.mp (hRA hr) a ha
  have hxr : Commute r (a * x * a⁻¹) := hxT r hr
  have h2 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
  have : Commute r x := by
    rw [h2]
    exact ((har.symm.inv_right).mul_right hxr).mul_right har.symm
  exact this

omit h32 h4 h34 in
theorem sup_le_centralizer_of_mem {z : G} (hz : z ∈ A ⊓ Subgroup.centralizer (A : Set G)) :
    R ⊔ A ≤ Subgroup.centralizer ({z} : Set G) := by
  have hRA := R_le_centralizer hc
  refine sup_le (fun r hr => ?_) (fun b hb => ?_)
  · rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (hRA hr) z hz.1).symm
  · rw [mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.mp hz.2 b hb

end Conj

section ConjMem

variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include hc h32 h4 h34

omit h4 h34 in
theorem mul_self_of_mem_rightConjugate {a y : G} (hy : y ∈ rightConjugate T a) : y * y = 1 := by
  rw [mem_rightConjugate_iff] at hy
  have h := (hc.elemT h32).2 _ hy
  rw [sq] at h
  have h2 : y * y = a⁻¹ * ((a * y * a⁻¹) * (a * y * a⁻¹)) * a := by group
  rw [h2, h, mul_one, inv_mul_cancel]

theorem exists_conj_eq_mul {W : Type*} [Group W] {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ) {a t y y' : G} (ha : a ∈ A)
    (ht : t ∈ T) (hy : y ∈ rightConjugate T a) (hy' : y' ∈ rightConjugate T a)
    (htyN : t * y * t⁻¹ ∈ normalizer (A : Set G)) (hy'N : y' ∈ normalizer (A : Set G))
    (hψy : ψ ⟨t * y * t⁻¹, htyN⟩ = ψ ⟨y', hy'N⟩) : ∃ r ∈ R, t * y * t⁻¹ = y' * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRK := R_le_centralizer hc
  have hRN := R_le_normalizer hc
  have hRA := rightConjugate_le_sup hc h32 h4 h34 ha
  have htRA : t ∈ R ⊔ A := hc.le_sup h32 h4 h34 ht
  have hkN : y'⁻¹ * (t * y * t⁻¹) ∈ normalizer (A : Set G) := mul_mem (inv_mem hy'N) htyN
  have hkK : y'⁻¹ * (t * y * t⁻¹) ∈ Subgroup.centralizer (A : Set G) := by
    have h1 : ψ ⟨y'⁻¹ * (t * y * t⁻¹), hkN⟩ = 1 := by
      have : (⟨y'⁻¹ * (t * y * t⁻¹), hkN⟩ : normalizer (A : Set G)) =
          (⟨y', hy'N⟩ : normalizer (A : Set G))⁻¹ * ⟨t * y * t⁻¹, htyN⟩ := rfl
      rw [this, map_mul, map_inv, hψy, inv_mul_cancel]
    exact (hψ.eq_one_iff _).mp h1
  have hkRA : y'⁻¹ * (t * y * t⁻¹) ∈ R ⊔ A :=
    mul_mem (inv_mem (hRA hy')) (mul_mem (mul_mem htRA (hRA hy)) (inv_mem htRA))
  obtain ⟨r, hr, z, hz, hrz⟩ := exists_mul_of_mem_sup_inf hRN hRK hkRA hkK
  have he : t * y * t⁻¹ = y' * r * z := by
    rw [mul_assoc y', ← hrz]
    group
  have hzc := sup_le_centralizer_of_mem hc hz
  have hzy' : y' * z = z * y' := mem_centralizer_singleton_iff.mp (hzc (hRA hy'))
  have hzr : r * z = z * r := mem_centralizer_singleton_iff.mp (hzc (le_sup_left (b := A) hr))
  have hry' : r * y' = y' * r :=
    (mem_centralizer_iff.mp (rightConjugate_le_centralizer hc ha hy') r hr)
  have hy2 := mul_self_of_mem_rightConjugate hc h32 hy
  have hy'2 := mul_self_of_mem_rightConjugate hc h32 hy'
  have hr2 : r * r = 1 := by
    have h := (hc.elemR h32).2 r hr
    rwa [sq] at h
  have hz2 : z * z = 1 := by
    have h1 : (t * y * t⁻¹) * (t * y * t⁻¹) = 1 := by
      rw [show (t * y * t⁻¹) * (t * y * t⁻¹) = t * (y * y) * t⁻¹ by group, hy2, mul_one,
        mul_inv_cancel]
    rw [he] at h1
    have h2 : y' * r * z * (y' * r * z) = (y' * y') * (r * r) * (z * z) := by
      calc y' * r * z * (y' * r * z) = y' * r * (z * y') * r * z := by group
        _ = y' * r * (y' * z) * r * z := by rw [hzy']
        _ = y' * (r * y') * z * r * z := by group
        _ = y' * (y' * r) * z * r * z := by rw [hry']
        _ = y' * y' * r * (z * r) * z := by group
        _ = y' * y' * r * (r * z) * z := by rw [hzr]
        _ = (y' * y') * (r * r) * (z * z) := by group
    rw [h2, hy'2, hr2, one_mul, one_mul] at h1
    exact h1
  have hzR : z ∈ R := by
    have hzp : IsPGroup 2 (zpowers z) := by
      have hdvd : orderOf z ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hz2])
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hzN : zpowers z ≤ normalizer (R : Set G) := by
      rw [zpowers_le]
      refine (centralizer_le_normalizer _) ?_
      rw [mem_centralizer_iff]
      intro r' hr'
      exact mem_centralizer_singleton_iff.mp (hzc (le_sup_left (b := A) hr'))
    have hsup : IsPGroup 2 ↥(R ⊔ zpowers z) :=
      IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup hzp hzN
    have heq := hc.sylowR.eq_of_le le_sup_left
      (sup_le hc.sylowR.le (zpowers_le.mpr hz.2)) hsup
    exact heq ▸ (le_sup_right (a := R) (mem_zpowers z))
  exact ⟨r * z, mul_mem hr hzR, by rw [he, mul_assoc]⟩

end ConjMem

section Normalizes

variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include hc h32 h4 h34

omit h32 h4 h34 in
theorem rightConjugate_le_normalizer {a : G} (ha : a ∈ A) :
    rightConjugate T a ≤ normalizer (A : Set G) := by
  intro y hy
  rw [mem_rightConjugate_iff] at hy
  have haN : a ∈ normalizer (A : Set G) := le_normalizer ha
  rw [show y = a⁻¹ * (a * y * a⁻¹) * a by group]
  exact mul_mem (mul_mem (inv_mem haN) (hc.le_normalizer hy)) haN

omit h4 h34 in
theorem commute_of_mem_rightConjugate {a y y' : G} (hy : y ∈ rightConjugate T a)
    (hy' : y' ∈ rightConjugate T a) : y * y' = y' * y := by
  rw [mem_rightConjugate_iff] at hy hy'
  have h : a * y * a⁻¹ * (a * y' * a⁻¹) = a * y' * a⁻¹ * (a * y * a⁻¹) :=
    congrArg Subtype.val ((hc.elemT h32).1.is_comm.comm (⟨_, hy⟩ : T) ⟨_, hy'⟩)
  calc y * y' = a⁻¹ * (a * y * a⁻¹ * (a * y' * a⁻¹)) * a := by group
    _ = a⁻¹ * (a * y' * a⁻¹ * (a * y * a⁻¹)) * a := by rw [h]
    _ = y' * y := by group

theorem mem_normalizer_of_map {W : Type*} [Group W] {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ) {a : G} (ha : a ∈ A)
    {t : normalizer (A : Set G)} (ht : (t : G) ∈ T)
    (hnorm : ∀ y : normalizer (A : Set G), (y : G) ∈ rightConjugate T a →
      ∃ y' : normalizer (A : Set G), (y' : G) ∈ rightConjugate T a ∧ ψ (t * y * t⁻¹) = ψ y')
    {y₀ : normalizer (A : Set G)} (hy₀ : (y₀ : G) ∈ rightConjugate T a)
    (hne : ψ (t * y₀ * t⁻¹) ≠ ψ y₀) :
    (t : G) ∈ normalizer (rightConjugate T a : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconj : ∀ y : normalizer (A : Set G), (y : G) ∈ rightConjugate T a →
      ∃ y' : normalizer (A : Set G), (y' : G) ∈ rightConjugate T a ∧ ψ (t * y * t⁻¹) = ψ y' ∧
        ∃ r ∈ R, (t : G) * y * (t : G)⁻¹ = y' * r := by
    intro y hy
    obtain ⟨y', hy', hψy⟩ := hnorm y hy
    exact ⟨y', hy', hψy, exists_conj_eq_mul hc h32 h4 h34 hψ ha ht hy hy' (t * y * t⁻¹).2 y'.2 hψy⟩
  have ht2 : (t : G) * t = 1 := by
    have h := (hc.elemT h32).2 _ ht
    rwa [sq] at h
  have hQt : TightlyEmbedded (rightConjugate (rightConjugate (Subgroup.centralizer (A : Set G)) g)
      a) := tightlyEmbedded_rightConjugate' (tightlyEmbedded_rightConjugate'
        (tightlyEmbedded_centralizer_of_standard hc.hyp.standard) g) a
  have hTQ : IsSylowOf 2 (rightConjugate T a)
      (rightConjugate (rightConjugate (Subgroup.centralizer (A : Set G)) g) a) :=
    AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowT a
  obtain ⟨y₁, hy₁, hψ₁, r, hr, hyr⟩ := hconj y₀ hy₀
  have hrt : (t : G) * r = r * t := (mem_centralizer_iff.mp (hc.le_centralizer ht) r hr).symm
  have hry₀ : r * y₀ = y₀ * r :=
    mem_centralizer_iff.mp (rightConjugate_le_centralizer hc ha hy₀) r hr
  have hrtt : (t : G) * r * t = r * (t * t) := by rw [hrt, mul_assoc]
  have hy₁eq : (y₁ : G) = t * y₀ * (t : G)⁻¹ * r⁻¹ := by rw [hyr]; group
  have hty₁ : (t : G) * y₁ * (t : G)⁻¹ = y₀ * r⁻¹ := by
    rw [hy₁eq]
    calc (t : G) * (t * y₀ * (t : G)⁻¹ * r⁻¹) * (t : G)⁻¹ = (t * t) * y₀ * (t * r * t)⁻¹ := by
          group
      _ = (t * t) * y₀ * (r * (t * t))⁻¹ := by rw [hrtt]
      _ = y₀ * r⁻¹ := by rw [ht2]; group
  have hx₀T : (y₀ : G) * y₁ ∈ rightConjugate T a := mul_mem hy₀ hy₁
  have htx₀ : (t : G) * (y₀ * y₁) = y₀ * y₁ * t := by
    have h1 : (t : G) * (y₀ * y₁) * (t : G)⁻¹ = y₀ * y₁ := by
      calc (t : G) * (y₀ * y₁) * (t : G)⁻¹ = (t * y₀ * (t : G)⁻¹) * (t * y₁ * (t : G)⁻¹) := by
            group
        _ = (y₁ * r) * (y₀ * r⁻¹) := by rw [hyr, hty₁]
        _ = y₁ * (r * y₀) * r⁻¹ := by group
        _ = y₁ * (y₀ * r) * r⁻¹ := by rw [hry₀]
        _ = y₁ * y₀ := by group
        _ = y₀ * y₁ := commute_of_mem_rightConjugate hc h32 hy₁ hy₀
    calc (t : G) * (y₀ * y₁) = ((t : G) * (y₀ * y₁) * (t : G)⁻¹) * t := by group
      _ = y₀ * y₁ * t := by rw [h1]
  have hx₀1 : (y₀ : G) * y₁ ≠ 1 := by
    intro h
    apply hne
    have hy : y₁ = y₀ := by
      apply Subtype.ext
      have h2 := mul_self_of_mem_rightConjugate hc h32 hy₀
      calc (y₁ : G) = y₀ * (y₀ * y₁) := by rw [← mul_assoc, h2, one_mul]
        _ = y₀ := by rw [h, mul_one]
    rw [hψ₁, hy]
  have htQ := mem_normalizer_of_commute_of_tightlyEmbedded hQt (hTQ.le hx₀T) hx₀1
    (by rw [sq]; exact mul_self_of_mem_rightConjugate hc h32 hx₀T) htx₀
  have hRT : IsPGroup 2 ↥(R ⊔ rightConjugate T a) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup hTQ.isPGroup
      ((rightConjugate_le_centralizer hc ha).trans (centralizer_le_normalizer _))
  have heq := hTQ.eq_of_le (le_inf hTQ.le le_sup_right) inf_le_left (hRT.to_le inf_le_right)
  have hfwd : ∀ y : G, y ∈ rightConjugate T a → (t : G) * y * (t : G)⁻¹ ∈ rightConjugate T a := by
    intro y hy
    obtain ⟨y', hy', -, r', hr', hyr'⟩ :=
      hconj ⟨y, rightConjugate_le_normalizer hc ha hy⟩ hy
    rw [← heq]
    refine ⟨(mem_normalizer_iff.mp htQ y).mp (hTQ.le hy), ?_⟩
    rw [show (t : G) * y * (t : G)⁻¹ = y' * r' from hyr']
    exact mul_mem (le_sup_right (a := R) hy') (le_sup_left (b := rightConjugate T a) hr')
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hfwd y, fun hy => ?_⟩
  have h := hfwd _ hy
  rwa [show (t : G) * ((t : G) * y * (t : G)⁻¹) * (t : G)⁻¹ = y by
    calc (t : G) * ((t : G) * y * (t : G)⁻¹) * (t : G)⁻¹ = ((t : G) * t) * y * ((t : G) * t)⁻¹ := by
          group
      _ = y := by rw [ht2]; group] at h

theorem map_conj_eq_of_normalizes {W : Type*} [Group W] {X : Subgroup W}
    {ψ : normalizer (A : Set G) →* W} (hψ : IsActionHom A X ψ) {a : G} (ha : a ∈ A)
    (h24 : T ⊓ normalizer (rightConjugate T a : Set G) ≤
      Subgroup.centralizer (rightConjugate T a : Set G))
    {t : normalizer (A : Set G)} (ht : (t : G) ∈ T)
    (hnorm : ∀ y : normalizer (A : Set G), (y : G) ∈ rightConjugate T a →
      ∃ y' : normalizer (A : Set G), (y' : G) ∈ rightConjugate T a ∧ ψ (t * y * t⁻¹) = ψ y')
    {y : normalizer (A : Set G)} (hy : (y : G) ∈ rightConjugate T a) :
    ψ (t * y * t⁻¹) = ψ y := by
  by_contra hne
  have hC := h24 ⟨ht, mem_normalizer_of_map hc h32 h4 h34 hψ ha ht hnorm hy hne⟩
  have h1 : (y : G) * t = t * y := mem_centralizer_iff.mp hC y hy
  apply hne
  congr 1
  apply Subtype.ext
  show (t : G) * y * (t : G)⁻¹ = y
  rw [← h1]
  group

end Normalizes

section Root

variable (hc : Sec3 A R T g) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
  (h2 : Asc76Theorem2) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
include hc h32 h4 h34 h2 hOut

theorem exists_eq_kleinFour_map {n : ℕ} (hn : 7 ≤ n) {ψ : normalizer (A : Set G) →* Perm (Fin n)}
    (hψ : IsActionHom A (alternatingGroup (Fin n)) ψ) :
    ∃ ι : Fin 4 ↪ Fin n,
      (T.subgroupOf (normalizer (A : Set G))).map ψ = kleinFour.map (viaEmbeddingHom ι) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hTab, hT4, hTN, hTC⟩, ⟨Xh, hXle, hTsyl, hnil, htight⟩, h24, -⟩ :=
    Lemma39.lemma39_three h4 h32 h34 h2 hc.hyp hc.not_mem hc.sylowT hc.le_normalizer hOut
  have hTX : T ≤ Xh := hTsyl.le
  have hXN : Xh ≤ normalizer (A : Set G) := hXle.trans (sup_le hTN le_normalizer)
  have hTsyl' : IsSylowOf 2 T (Xh ⊓ normalizer (A : Set G)) := by
    rwa [inf_eq_left.mpr hXN]
  have hQ : ∀ t ∈ T, t ≠ 1 → ∀ c ∈ A, c * t = t * c → c ∈ normalizer (Xh : Set G) := by
    intro t ht ht1 c hc' hct
    have hn := mem_normalizer_of_commute_of_tightlyEmbedded htight
      (t := ⟨t, le_sup_left (a := T) (b := A) ht⟩) (c := ⟨c, le_sup_right (a := T) hc'⟩)
      (hTX ht) (fun h => ht1 (congrArg Subtype.val h)) (Subtype.ext (hTab.2 t ht))
      (Subtype.ext hct)
    rw [mem_normalizer_iff]
    intro x
    by_cases hx : x ∈ T ⊔ A
    · have := (mem_normalizer_iff.mp hn) ⟨x, hx⟩
      simpa [mem_subgroupOf] using this
    · have hcx : c * x * c⁻¹ ∉ T ⊔ A := by
        intro h
        apply hx
        have := (T ⊔ A).mul_mem ((T ⊔ A).mul_mem ((T ⊔ A).inv_mem
          (le_sup_right (a := T) hc')) h) (le_sup_right (a := T) hc')
        simpa [mul_assoc] using this
      exact ⟨fun h => absurd (hXle h) hx, fun h => absurd (hXle h) hcx⟩
  have hcardE : Nat.card ((T.subgroupOf (normalizer (A : Set G))).map ψ) = Nat.card T := by
    rw [card_map_eq_of_inf_centralizer hψ hTC]
    exact Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv
  refine eq_kleinFour_map (by simp only [Fintype.card_fin]; omega) ?_ (hcardE ▸ hT4)
    (fun hw => not_isTwoNilpotent_of_qWitness hw (isTwoNilpotent_nE_map hψ hTX hTN hQ hnil))
    (not_yWitness_map hψ hTsyl' hTab.2 hQ) ?_
  ·
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact congrArg Subtype.val (hTab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hTab.2 _ hx)
      rw [this, map_one]
  ·
    intro hcard a' ha' t' ht' hnorm' x' hx'
    have hT4' : Nat.card T ≠ 4 := by omega
    obtain ⟨a, haA, rfl⟩ := hψ.exists_eq a' ha'
    obtain ⟨t, htT, rfl⟩ := ht'
    obtain ⟨x, hxT, rfl⟩ := hx'
    replace htT : (t : G) ∈ T := htT
    replace hxT : (x : G) ∈ T := hxT
    set aN : normalizer (A : Set G) := ⟨a, le_normalizer haA⟩ with haN
    have hmem : ∀ z : normalizer (A : Set G), (z : G) ∈ T →
        ((aN⁻¹ * z * aN : normalizer (A : Set G)) : G) ∈ rightConjugate T a := by
      intro z hz
      rw [mem_rightConjugate_iff]
      show a * (a⁻¹ * (z : G) * a) * a⁻¹ ∈ T
      rw [show a * (a⁻¹ * (z : G) * a) * a⁻¹ = z by group]
      exact hz
    have key := map_conj_eq_of_normalizes hc h32 h4 h34 hψ haA ((h24.resolve_left hT4') a haA)
      htT ?_ (hmem x hxT)
    · simp only [map_mul, map_inv] at key
      calc ψ t * ((ψ aN)⁻¹ * ψ x * ψ aN)
          = (ψ t * ((ψ aN)⁻¹ * ψ x * ψ aN) * (ψ t)⁻¹) * ψ t := by group
        _ = (ψ aN)⁻¹ * ψ x * ψ aN * ψ t := by rw [key]
    · intro y hy
      have hz : aN * y * aN⁻¹ ∈ T.subgroupOf (normalizer (A : Set G)) := by
        rw [mem_subgroupOf]
        exact (mem_rightConjugate_iff _ _ _).mp hy
      obtain ⟨_, ⟨z, hzT, rfl⟩, hzeq⟩ := hnorm' (ψ (aN * y * aN⁻¹)) ⟨_, hz, rfl⟩
      replace hzT : (z : G) ∈ T := hzT
      refine ⟨aN⁻¹ * z * aN, hmem z hzT, ?_⟩
      simp only [map_mul, map_inv] at hzeq ⊢
      rw [← hzeq]
      group

end Root

end CFSG.ComponentClassification.RankTwoAlt
