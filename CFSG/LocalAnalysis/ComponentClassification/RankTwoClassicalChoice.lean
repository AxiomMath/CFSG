module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConfig
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b

namespace SplitData

variable {G : Type} [Group G] {A J : Subgroup G} {P₁ P₂ : G → Prop} {F : Type} [Field F]
  {ι₁ ι₂ : F → G} (h : SplitData A J P₁ P₂ F ι₁ ι₂)
include h

theorem map_zero₁ : ι₁ 0 = 1 := by
  have h0 := h.map_add₁ 0 0
  rw [add_zero] at h0
  exact mul_eq_left.mp h0.symm

theorem map_zero₂ : ι₂ 0 = 1 := by
  have h0 := h.map_add₂ 0 0
  rw [add_zero] at h0
  exact mul_eq_left.mp h0.symm

theorem map_neg₁ (x : F) : ι₁ (-x) = (ι₁ x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← h.map_add₁, add_neg_cancel, h.map_zero₁]

theorem map_neg₂ (x : F) : ι₂ (-x) = (ι₂ x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← h.map_add₂, add_neg_cancel, h.map_zero₂]

theorem commute₁₁ (x y : F) : Commute (ι₁ x) (ι₁ y) := by
  show ι₁ x * ι₁ y = ι₁ y * ι₁ x
  rw [← h.map_add₁, ← h.map_add₁, add_comm]

theorem commute₂₂ (x y : F) : Commute (ι₂ x) (ι₂ y) := by
  show ι₂ x * ι₂ y = ι₂ y * ι₂ x
  rw [← h.map_add₂, ← h.map_add₂, add_comm]

theorem commute_mul (x y x' y' : F) : Commute (ι₁ x * ι₂ y) (ι₁ x' * ι₂ y') :=
  ((h.commute₁₁ x x').mul_right (h.comm x y')).mul_left
    (((h.comm x' y).symm).mul_right (h.commute₂₂ y y'))

theorem mul_mul (x y x' y' : F) :
    ι₁ x * ι₂ y * (ι₁ x' * ι₂ y') = ι₁ (x + x') * ι₂ (y + y') := by
  rw [h.map_add₁, h.map_add₂]
  have hc : ι₂ y * ι₁ x' = ι₁ x' * ι₂ y := (h.comm x' y).eq.symm
  calc ι₁ x * ι₂ y * (ι₁ x' * ι₂ y') = ι₁ x * (ι₂ y * ι₁ x') * ι₂ y' := by group
    _ = ι₁ x * (ι₁ x' * ι₂ y) * ι₂ y' := by rw [hc]
    _ = ι₁ x * ι₁ x' * (ι₂ y * ι₂ y') := by group

theorem eq_of_mul_eq {x y x' y' : F} (he : ι₁ x * ι₂ y = ι₁ x' * ι₂ y') : x = x' ∧ y = y' := by
  have h1 : ι₁ (-x' + x) = ι₂ (y' + -y) := by
    rw [h.map_add₁, h.map_add₂, h.map_neg₁, h.map_neg₂]
    calc (ι₁ x')⁻¹ * ι₁ x = (ι₁ x')⁻¹ * (ι₁ x * ι₂ y) * (ι₂ y)⁻¹ := by group
      _ = (ι₁ x')⁻¹ * (ι₁ x' * ι₂ y') * (ι₂ y)⁻¹ := by rw [he]
      _ = ι₂ y' * (ι₂ y)⁻¹ := by group
  have hxx : x = x' := (neg_add_eq_zero.mp (h.inf _ _ h1)).symm
  refine ⟨hxx, ?_⟩
  subst hxx
  have h2 : ι₂ y = ι₂ y' := mul_left_cancel he
  have h3 : ι₂ (-y + y') = 1 := by rw [h.map_add₂, h.map_neg₂, h2, inv_mul_cancel]
  exact neg_add_eq_zero.mp (h.inj₂ _ h3)

theorem mul_self₁ [CharP F 2] (x : F) : ι₁ x * ι₁ x = 1 := by
  rw [← h.map_add₁, CharTwo.add_self_eq_zero, h.map_zero₁]

theorem mul_self₂ [CharP F 2] (x : F) : ι₂ x * ι₂ x = 1 := by
  rw [← h.map_add₂, CharTwo.add_self_eq_zero, h.map_zero₂]

theorem ne_one₁ {x : F} (hx : x ≠ 0) : ι₁ x ≠ 1 := fun h1 => hx (h.inj₁ x h1)

theorem ne_one₂ {x : F} (hx : x ≠ 0) : ι₂ x ≠ 1 := fun h1 => hx (h.inj₂ x h1)

end SplitData

theorem ClassicalModel.exists_q_eq {G : Type} [Group G] {A : Subgroup G} (D : ClassicalModel A) :
    ∃ m : ℕ, D.q = 2 ^ m := by
  cases D with
  | linear n m => exact ⟨m, rfl⟩
  | unitary n m => exact ⟨m, rfl⟩
  | symplectic n m => exact ⟨m, rfl⟩
  | orthPlus n m => exact ⟨m, rfl⟩
  | orthMinus n m => exact ⟨m, rfl⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_le_centralizer {A Q : Subgroup G} (hZ : Odd (Nat.card (center ↥A)))
    (hQ : IsPGroup 2 ↥Q) (hQK : Q ≤ centralizer (A : Set G)) : Q ⊓ A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxQ, hxA⟩ := mem_inf.mp hx
  have hxZ : (⟨x, hxA⟩ : ↥A) ∈ center ↥A := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hQK hxQ) y y.2)
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd := Subgroup.orderOf_dvd_natCard (center ↥A) hxZ
  rw [Subgroup.orderOf_mk] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rw [hj] at hdvd
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    rw [hj, mem_bot]
  · exfalso
    have h2 : 2 ∣ Nat.card (center ↥A) := (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr h2)

omit [Finite G] in
theorem eq_one_of_mem_centralizer {A : Subgroup G} (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hpA : p ∈ A) (hpK : p ∈ centralizer (A : Set G)) (hp2 : p ^ 2 = 1) : p = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥(zpowers p) := by
    have hd : orderOf p ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hp2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have h := inf_eq_bot_of_le_centralizer hZ hQ (zpowers_le.mpr hpK)
  have hp : p ∈ zpowers p ⊓ A := mem_inf.mpr ⟨mem_zpowers p, hpA⟩
  rwa [h, mem_bot] at hp

theorem sec3_of_conj {A R : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hZ : Odd (Nat.card (center ↥A))) {x : G}
    (hxR : rightConjugate R x ≤ centralizer (R : Set G)) {s p : G} (hs : s ∈ rightConjugate R x)
    (hp : p ∈ A) (hρ : s⁻¹ * p ∈ R) (hp1 : p ≠ 1) (hp2 : p ^ 2 = 1) :
    Sec3 A R (rightConjugate R x) x := by
  refine ⟨hA, hR, fun hx => hp1 ?_, AschbacherTheorem3.isSylowOf_rightConjugate hR x, hxR⟩
  have hK : rightConjugate (centralizer (A : Set G)) x = centralizer (A : Set G) := by
    rw [← centralizer_rightConjugate, (rightConjugate_eq_self_iff _ _).mpr hx]
  have hsK : s ∈ centralizer (A : Set G) := by
    rw [← hK]
    exact map_mono hR.le hs
  have hpK : p ∈ centralizer (A : Set G) := by
    rw [show p = s * (s⁻¹ * p) by group]
    exact mul_mem hsK (hR.le hρ)
  exact eq_one_of_mem_centralizer hZ hp hpK hp2

@[expose] noncomputable def choiceMeasure {A : Subgroup G} (D : ClassicalModel A)
    (R T : Subgroup G) : ℕ :=
  sInf {n | ∃ t ∈ T, t ≠ 1 ∧ ∃ p ∈ A, t⁻¹ * p ∈ R ∧ D.HasMeasure p n}

omit [Finite G] in
theorem choiceMeasure_le {A : Subgroup G} {D : ClassicalModel A} {R T : Subgroup G} {t p : G}
    {n : ℕ} (ht : t ∈ T) (ht1 : t ≠ 1) (hp : p ∈ A) (hρ : t⁻¹ * p ∈ R)
    (hn : D.HasMeasure p n) : choiceMeasure D R T ≤ n :=
  Nat.sInf_le ⟨t, ht, ht1, p, hp, hρ, hn⟩

structure MinChoice {A : Subgroup G} (D : ClassicalModel A) (R T : Subgroup G) (g : G) :
    Prop where
  sec3 : Sec3 A R T g
  le_of_le : ∀ (T' : Subgroup G) (g' : G), Sec3 A R T' g' → T' ≤ A → T ≤ A
  measure_le : ∀ (T' : Subgroup G) (g' : G), Sec3 A R T' g' → (T' ≤ A ∨ ¬ T ≤ A) →
    choiceMeasure D R T ≤ choiceMeasure D R T'

theorem exists_minChoice {A : Subgroup G} (D : ClassicalModel A) {R T₀ : Subgroup G} {g₀ : G}
    (h : Sec3 A R T₀ g₀) : ∃ (T : Subgroup G) (g : G), MinChoice D R T g := by
  let S : Set (Subgroup G × G) := {c | Sec3 A R c.1 c.2 ∧
    (c.1 ≤ A ∨ ¬ ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ T' ≤ A)}
  have hS : S.Nonempty := by
    by_cases hex : ∃ (T' : Subgroup G) (g' : G), Sec3 A R T' g' ∧ T' ≤ A
    · obtain ⟨T', g', h', hT'⟩ := hex
      exact ⟨(T', g'), h', Or.inl hT'⟩
    · exact ⟨(T₀, g₀), h, Or.inr hex⟩
  obtain ⟨c, ⟨hc, hcA⟩, hmin⟩ :=
    (measure fun c : Subgroup G × G => choiceMeasure D R c.1).wf.has_min S hS
  refine ⟨c.1, c.2, hc, fun T' g' h' hT' => ?_, fun T' g' h' hT' => ?_⟩
  · rcases hcA with h1 | h1
    · exact h1
    · exact absurd ⟨T', g', h', hT'⟩ h1
  · have hmem : (T', g') ∈ S := by
      refine ⟨h', ?_⟩
      rcases hT' with h1 | h1
      · exact Or.inl h1
      · rcases hcA with h2 | h2
        · exact absurd h2 h1
        · exact Or.inr h2
    exact not_lt.mp (hmin _ hmem)

theorem MinChoice.le_of_mem {A : Subgroup G} {D : ClassicalModel A} {R T : Subgroup G} {g : G}
    (hm : MinChoice D R T g) {T' : Subgroup G} {g' : G} (h' : Sec3 A R T' g')
    (hT' : T' ≤ A ∨ ¬ T ≤ A) {s p : G} (hs : s ∈ T') (hs1 : s ≠ 1) (hp : p ∈ A)
    (hρ : s⁻¹ * p ∈ R) {m : ℕ} (hpm : D.HasMeasure p m) : choiceMeasure D R T ≤ m :=
  (hm.measure_le T' g' h' hT').trans (choiceMeasure_le hs hs1 hp hρ hpm)

namespace Sec3

variable {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem R_inf_A (hZ : Odd (Nat.card (center ↥A))) : R ⊓ A = ⊥ :=
  inf_eq_bot_of_le_centralizer hZ hc.sylowR.isPGroup hc.sylowR.le

theorem T_inf_conj (hZ : Odd (Nat.card (center ↥A))) : T ⊓ rightConjugate A g = ⊥ := by
  have h := hc.swap.R_inf_A hZ
  have h' : rightConjugate (rightConjugate T g⁻¹ ⊓ A) g = ⊥ := by
    rw [h]
    exact Subgroup.map_bot _
  rwa [rightConjugate_inf, rightConjugate_inv_rightConjugate] at h'

theorem aPart_unique (hZ : Odd (Nat.card (center ↥A))) {t p p' : G} (hp : p ∈ A)
    (hρ : t⁻¹ * p ∈ R) (hp' : p' ∈ A) (hρ' : t⁻¹ * p' ∈ R) : p = p' := by
  have h1 : p⁻¹ * p' ∈ R ⊓ A := by
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem hp) hp'⟩
    have := mul_mem (inv_mem hρ) hρ'
    simpa [mul_assoc] using this
  rw [hc.R_inf_A hZ, mem_bot] at h1
  calc p = p * (p⁻¹ * p') := by rw [h1, mul_one]
    _ = p' := by group

theorem aPart_conj {t p a : G} (hρ : t⁻¹ * p ∈ R) (ha : a ∈ A) :
    (a⁻¹ * t * a)⁻¹ * (a⁻¹ * p * a) ∈ R := by
  have hcomm : Commute a (t⁻¹ * p) := hc.commute_of_mem ha hρ
  have h1 : (a⁻¹ * t * a)⁻¹ * (a⁻¹ * p * a) = a⁻¹ * (t⁻¹ * p) * a := by group
  rw [h1, mul_assoc, ← hcomm.eq, inv_mul_cancel_left]
  exact hρ

theorem aPart_mul {s u p q : G} (hρs : s⁻¹ * p ∈ R) (hρu : u⁻¹ * q ∈ R) (hq : q ∈ A) :
    (s * u)⁻¹ * (p * q) ∈ R := by
  have hcomm : Commute q (s⁻¹ * p) := hc.commute_of_mem hq hρs
  have h1 : (s * u)⁻¹ * (p * q) = (u⁻¹ * q) * (s⁻¹ * p) := by
    calc (s * u)⁻¹ * (p * q) = u⁻¹ * ((s⁻¹ * p) * q) := by group
      _ = u⁻¹ * (q * (s⁻¹ * p)) := by rw [← hcomm.eq]
      _ = (u⁻¹ * q) * (s⁻¹ * p) := by group
  rw [h1]
  exact mul_mem hρu hρs

theorem exists_choiceMeasure (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (D : ClassicalModel A) (hZ : Odd (Nat.card (center ↥A))) :
    ∃ t ∈ T, t ≠ 1 ∧ ∃ p ∈ A, t⁻¹ * p ∈ R ∧ D.HasMeasure p (choiceMeasure D R T) := by
  obtain ⟨t, ht, ht1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p, hp, hρ⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨n, hn⟩ := D.exists_hasMeasure hZ hp (hc.orderOf_aPart h32 ht ht1 hρ)
  have hne : {n | ∃ t ∈ T, t ≠ 1 ∧ ∃ p ∈ A, t⁻¹ * p ∈ R ∧ D.HasMeasure p n}.Nonempty :=
    ⟨n, t, ht, ht1, p, hp, hρ, hn⟩
  exact Nat.sInf_mem hne

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
