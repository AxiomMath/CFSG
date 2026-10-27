module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalStep83Basic
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AS76b

@[expose] def ExcPairCent : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    (ChevalleyExceptionalModel S .F4 2 1 ∨ ChevalleyExceptionalModel S .twistedE6 2 1) →
    ∀ x y : S, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x ≠ y →
      ¬ (oUpperTwo (centralizer ({x} : Set S)) ≤ centralizer ({y} : Set S) ∧
        oUpperTwo (centralizer ({x * y} : Set S)) ≤ centralizer ({y} : Set S))

namespace Step83Proof

open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoClassical CFSG.ComponentClassification.RankTwoStandard

theorem mem_inner_of_odd_F4
    {B : Type} [Group B] (hperf : commutator B = ⊤)
    (hS : ChevalleyExceptionalModel (B ⧸ center B) .F4 2 1) {α : MulAut B}
    (hodd : Odd (orderOf α)) : α ∈ OuterAutomorphisms.inner B := by
  have : Group.IsPerfect B := Group.isPerfect_def.2 hperf
  obtain ⟨⟨hp, hm, -⟩, hmod⟩ := hS
  have hmod' : UntwistedChevalleyModel (B ⧸ center B) .F4 (2 ^ 1) := hmod
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmod'
  have : CharP K LieType.Ree.ReeTag.F4.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hm hK
  obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
    LieType.Chevalley.even_F4_exact_automorphism_normal_form hm K hK
  have e' : B ⧸ center B ≃* ↥(adjointGroup LieType.Ree.ReeTag.F4.tag K) := e
  have hker' : Θ.ker = OuterAutomorphisms.inner (adjointGroup LieType.Ree.ReeTag.F4.tag K) := hker
  have hφ₃ : Function.Injective (QuotientGroup.lift
      (OuterAutomorphisms.inner (adjointGroup LieType.Ree.ReeTag.F4.tag K)) Θ hker'.ge) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hker', QuotientGroup.map_mk'_self]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : OuterAutomorphisms.Outer B →* Multiplicative (ZMod (2 * 1)),
      Function.Injective Ψ :=
    ⟨(QuotientGroup.lift (OuterAutomorphisms.inner (adjointGroup LieType.Ree.ReeTag.F4.tag K)) Θ
        hker'.ge).comp ((OuterAutomorphisms.equivalence e').toMonoidHom.comp
          (OuterAutomorphisms.centerQuotientOuterHom B)),
      hφ₃.comp ((OuterAutomorphisms.equivalence e').injective.comp
        (OuterAutomorphisms.centerQuotient_outer_injective B))⟩
  set x : OuterAutomorphisms.Outer B := (α : OuterAutomorphisms.Outer B) with hx
  have h2 : Ψ x ^ 2 = 1 := by
    generalize Ψ x = a
    induction a using Multiplicative.rec with
    | ofAdd k =>
      rw [← ofAdd_nsmul, ← ofAdd_zero]
      congr 1
      fin_cases k <;> decide
  have hm' : Ψ x ^ orderOf α = 1 := by
    rw [← map_pow, hx, ← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one, map_one]
  have h1 : Ψ x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · have h5 := orderOf_dvd_of_pow_eq_one hm'
      rw [h] at h5
      exact absurd (even_iff_two_dvd.mpr h5) (Nat.not_even_iff_odd.mpr hodd)
  have hx1 : x = 1 := hΨ (by rw [h1, map_one])
  exact (QuotientGroup.eq_one_iff α).mp hx1

theorem commute_center_of_odd_F4
    {G : Type} [Group G] {A : Subgroup G} (hperf : commutator ↥A = ⊤)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .F4 2 1) {n z : G}
    (hn : n ∈ normalizer (A : Set G)) (hodd : Odd (orderOf n)) (hzA : z ∈ A)
    (hzK : z ∈ centralizer (A : Set G)) : n * z * n⁻¹ = z := by
  have hαo : Odd (orderOf (Lemma39.normConj A ⟨n, hn⟩)) := by
    refine hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow]
    have h1 : (⟨n, hn⟩ : ↥(normalizer (A : Set G))) ^ orderOf n = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [h1, map_one]
  obtain ⟨b, hb⟩ := mem_inner_of_odd_F4 hperf hS hαo
  have hzc : (⟨z, hzA⟩ : A) ∈ center A :=
    mem_center_iff.mpr fun c => Subtype.ext (mem_centralizer_iff.mp hzK c c.2)
  have h1 : Lemma39.normConj A ⟨n, hn⟩ ⟨z, hzA⟩ = ⟨z, hzA⟩ := by
    rw [← hb, MulAut.conj_apply, mem_center_iff.mp hzc b, mul_inv_cancel_right]
  have h2 := congrArg Subtype.val h1
  rwa [Lemma39.normConj_apply] at h2

section Pair

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

omit [Finite G] in
theorem conj_mem_of_mem_normalizer {n z : G} (hn : n ∈ normalizer (A : Set G)) (hzA : z ∈ A)
    (hzK : z ∈ centralizer (A : Set G)) :
    n * z * n⁻¹ ∈ A ∧ n * z * n⁻¹ ∈ centralizer (A : Set G) :=
  ⟨(mem_normalizer_iff.mp hn z).mp hzA,
    (mem_normalizer_iff.mp (Lemma22.normalizer_le_normalizer_centralizer A hn) z).mp hzK⟩

omit [Finite G] in
theorem conj_eq_of_sq_conj_eq [Finite G] {c z : G} (hodd : Odd (orderOf c))
    (h : c ^ 2 * z * (c ^ 2)⁻¹ = z) : c * z * c⁻¹ = z := by
  obtain ⟨k, hk⟩ := hodd
  have hc : (c ^ 2) ^ (k + 1) = c := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hcomm : Commute (c ^ 2) z := by
    change c ^ 2 * z = z * c ^ 2
    calc c ^ 2 * z = c ^ 2 * z * (c ^ 2)⁻¹ * c ^ 2 := by group
      _ = z * c ^ 2 := by rw [h]
  have h2 := hcomm.pow_left (k + 1)
  rw [hc] at h2
  rw [h2.eq, mul_inv_cancel_right]

namespace Sec3

variable (hc : Sec3 A R T g)
include hc

theorem conj_mem_normalizer (h32 : Lemma32) {u c : G} (hu : u ∈ T) (hu1 : u ≠ 1)
    (hcu : c ∈ centralizer ({u} : Set G)) : g * c * g⁻¹ ∈ normalizer (A : Set G) :=
  (mem_normalizer_rightConjugate_iff A g c).mp
    (Lemma39.centralizer_le_normalizer_rightConjugate hc.hyp g (hc.sylowT.le hu) hu1
      ((hc.elemT h32).2 u hu) hcu)

theorem exists_pair (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34) {y s : G}
    (hy : y ∈ T) (hs : s ∈ T) (hy1 : y ≠ 1) (hs1 : s ≠ 1) (hsy : s ≠ y)
    (hodd : ∀ u : G, (u = s ∨ u = s * y) → ∀ c ∈ A ⊓ centralizer ({u} : Set G),
      Odd (orderOf c) → c * y = y * c) :
    ∃ x' y' : rankTwoQuot A, orderOf x' = 2 ∧ orderOf y' = 2 ∧ x' * y' = y' * x' ∧ x' ≠ y' ∧
      oUpperTwo (centralizer ({x'} : Set (rankTwoQuot A))) ≤
        centralizer ({y'} : Set (rankTwoQuot A)) ∧
      oUpperTwo (centralizer ({x' * y'} : Set (rankTwoQuot A))) ≤
        centralizer ({y'} : Set (rankTwoQuot A)) := by
  obtain ⟨p, hpA, hρp⟩ := hc.exists_aPart h32 h4 h34 hs
  obtain ⟨q, hqA, hρq⟩ := hc.exists_aPart h32 h4 h34 hy
  have hpq : p * q = q * p := by
    have h1 : Commute p y := aPart_commute hc h32 hs hρp hy
    have h3 := h1.mul_right (commute_of_mem_R hc hpA hρq)
    rwa [mul_inv_cancel_left] at h3
  have hρpq : (s * y)⁻¹ * (p * q) ∈ R := by
    have hyr : y * (s⁻¹ * p) = (s⁻¹ * p) * y := commute_T_R hc hy hρp
    have e : (s * y)⁻¹ * (p * q) = (s⁻¹ * p) * (y⁻¹ * q) := by
      calc (s * y)⁻¹ * (p * q) = y⁻¹ * (s⁻¹ * p) * y * y⁻¹ * q := by group
        _ = y⁻¹ * (y * (s⁻¹ * p)) * y⁻¹ * q := by rw [hyr]; group
        _ = (s⁻¹ * p) * (y⁻¹ * q) := by group
    rw [e]
    exact mul_mem hρp hρq
  have hone : (1 : G)⁻¹ * 1 ∈ R := by rw [inv_one, one_mul]; exact one_mem R
  have hord : ∀ {t r : G} (ht : t ∈ T) (hr : r ∈ A) (hρ : t⁻¹ * r ∈ R), t ≠ 1 →
      orderOf ((⟨r, hr⟩ : A) : A ⧸ center A) = 2 := by
    intro t r ht hr hρ ht1
    refine orderOf_eq_prime ?_ fun h => ht1 ?_
    · rw [sq, ← QuotientGroup.mk_mul]
      have h1 : (⟨r, hr⟩ : A) * ⟨r, hr⟩ = 1 := Subtype.ext (aPart_mul_self hc h32 ht hρ)
      rw [h1, QuotientGroup.mk_one]
    · refine eq_of_mk_aPart_eq hc ht (one_mem T) hr (one_mem A) hρ hone ?_
      rw [h]
      rfl
  have hlift : ∀ {u r : G} (_ : u = s ∨ u = s * y) (hr : r ∈ A) (_ : u⁻¹ * r ∈ R),
      ∀ a : A, a * ⟨r, hr⟩ = ⟨r, hr⟩ * a → Odd (orderOf a) → a * ⟨q, hqA⟩ = ⟨q, hqA⟩ * a := by
    intro u r hu hr hρ a har hao
    have ha : (a : G) ∈ A ⊓ centralizer ({u} : Set G) := by
      rw [inf_centralizer_eq hc hρ]
      exact mem_inf.mpr ⟨a.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val har)⟩
    have hay : Commute (a : G) y := hodd u hu a ha (by rwa [Subgroup.orderOf_coe])
    have h3 := hay.mul_right (commute_of_mem_R hc a.2 hρq)
    rw [mul_inv_cancel_left] at h3
    exact Subtype.ext h3
  have hP2 : (⟨p, hpA⟩ : A) * ⟨p, hpA⟩ = 1 := Subtype.ext (aPart_mul_self hc h32 hs hρp)
  have hPQ : (⟨p, hpA⟩ : A) * ⟨q, hqA⟩ = ⟨q, hqA⟩ * ⟨p, hpA⟩ := Subtype.ext hpq
  have hPQ2 : (⟨p * q, mul_mem hpA hqA⟩ : A) * ⟨p * q, mul_mem hpA hqA⟩ = 1 := by
    have hq2 := aPart_mul_self hc h32 hy hρq
    have hp2 := aPart_mul_self hc h32 hs hρp
    refine Subtype.ext ?_
    change p * q * (p * q) = 1
    calc p * q * (p * q) = p * (q * p) * q := by group
      _ = p * (p * q) * q := by rw [hpq]
      _ = (p * p) * (q * q) := by group
      _ = 1 := by rw [hp2, hq2, one_mul]
  refine ⟨((⟨p, hpA⟩ : A) : A ⧸ center A), ((⟨q, hqA⟩ : A) : A ⧸ center A),
    hord hs hpA hρp hs1, hord hy hqA hρq hy1, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hPQ]
  · intro h
    exact hsy (eq_of_mk_aPart_eq hc hs hy hpA hqA hρp hρq h)
  · exact oUpperTwo_centralizer_le hP2 (hlift (Or.inl rfl) hpA hρp)
  · rw [← QuotientGroup.mk_mul]
    exact oUpperTwo_centralizer_le hPQ2 (hlift (Or.inr rfl) (mul_mem hpA hqA) hρpq)

theorem false_of_choice (hPC : ExcPairCent) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .F4 2 1 ∨
      ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 1) {y s : G}
    (hy : y ∈ T) (hs : s ∈ T) (hy1 : y ≠ 1) (hs1 : s ≠ 1) (hsy : s ≠ y)
    (hodd : ∀ u : G, (u = s ∨ u = s * y) → ∀ c ∈ A ⊓ centralizer ({u} : Set G),
      Odd (orderOf c) → c * y = y * c) : False := by
  obtain ⟨x', y', h1, h2, h3, h5, h6, h7⟩ := exists_pair hc h32 h4 h34 hy hs hy1 hs1 hsy hodd
  exact hPC (rankTwoQuot A) hS x' y' h1 h2 h3 h5 ⟨h6, h7⟩

omit hc in
theorem exists_mem_ne_ne {T' : Subgroup G} (hT : 4 ≤ Nat.card T') (y : G) :
    ∃ s ∈ T', s ≠ 1 ∧ s ≠ y := by
  by_contra h
  push Not at h
  have hsub : (T' : Set G) ⊆ {1, y} := by
    intro s hs
    by_cases h1 : s = 1
    · exact Or.inl h1
    · exact Or.inr (h s hs h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, y} : Set G).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have h3 : Nat.card T' = (T' : Set G).ncard := Nat.card_coe_set_eq _
  omega

omit [Finite G] hc in
theorem commute_conj_of_conj_eq {c z : G} (h : (g * c * g⁻¹) * z * (g * c * g⁻¹)⁻¹ = z) :
    c * (g⁻¹ * z * g) = (g⁻¹ * z * g) * c := by
  calc c * (g⁻¹ * z * g) = g⁻¹ * ((g * c * g⁻¹) * z * (g * c * g⁻¹)⁻¹) * g * c := by group
    _ = (g⁻¹ * z * g) * c := by rw [h]

theorem false_of_fixed (hPC : ExcPairCent) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .F4 2 1 ∨
      ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 1) {z : G} (hzA : z ∈ A)
    (hzK : z ∈ centralizer (A : Set G)) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hfix : ∀ n ∈ normalizer (A : Set G), Odd (orderOf n) → n * z * n⁻¹ = z) : False := by
  have hyT : g⁻¹ * z * g ∈ T :=
    conj_mem_of_mem_center hc hzA hzK (k := 1) (by rw [pow_one, sq, hz2])
  have hy1 : g⁻¹ * z * g ≠ 1 := fun h => hz1 (by
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨s, hs, hs1, hsy⟩ := exists_mem_ne_ne (hc.card_eq ▸ hc.four_le) (g⁻¹ * z * g)
  refine false_of_choice hc hPC h32 h4 h34 hS hyT hs hy1 hs1 hsy ?_
  rintro u hu c ⟨hcA, hcu⟩ hco
  have huT : u ∈ T := by rcases hu with rfl | rfl <;> [exact hs; exact mul_mem hs hyT]
  have hu1 : u ≠ 1 := by
    rcases hu with rfl | rfl
    · exact hs1
    · intro h
      apply hsy
      have hy2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
        calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
          _ = 1 := by rw [hz2]; group
      calc s = s * (g⁻¹ * z * g) * (g⁻¹ * z * g) := by rw [mul_assoc, hy2, mul_one]
        _ = g⁻¹ * z * g := by rw [h, one_mul]
  have hn := conj_mem_normalizer hc h32 huT hu1 hcu
  have hno : Odd (orderOf (g * c * g⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hco
  exact commute_conj_of_conj_eq (hfix _ hn hno)

theorem false_of_three (hPC : ExcPairCent) (h32 : Lemma32) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .F4 2 1 ∨
      ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 1) {z₁ z₂ : G}
    (h1A : z₁ ∈ A) (h1K : z₁ ∈ centralizer (A : Set G)) (h12 : z₁ * z₁ = 1) (h11 : z₁ ≠ 1)
    (h2A : z₂ ∈ A) (h2K : z₂ ∈ centralizer (A : Set G)) (h22 : z₂ * z₂ = 1) (h21 : z₂ ≠ 1)
    (hne : z₁ ≠ z₂)
    (hall : ∀ w : G, w ∈ A → w ∈ centralizer (A : Set G) → w * w = 1 → w ≠ 1 →
      w = z₁ ∨ w = z₂ ∨ w = z₁ * z₂) : False := by
  have hcomm : z₁ * z₂ = z₂ * z₁ := mem_centralizer_iff.mp h2K z₁ h1A
  have hconjT : ∀ {w : G}, w ∈ A → w ∈ centralizer (A : Set G) → w * w = 1 → g⁻¹ * w * g ∈ T :=
    fun hwA hwK hw2 => conj_mem_of_mem_center hc hwA hwK (k := 1) (by rw [pow_one, sq, hw2])
  have hconj1 : ∀ {w : G}, w ≠ 1 → g⁻¹ * w * g ≠ 1 := by
    intro w hw h
    apply hw
    calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hsy : g⁻¹ * z₁ * g ≠ g⁻¹ * z₂ * g := fun h => hne (by
    calc z₁ = g * (g⁻¹ * z₁ * g) * g⁻¹ := by group
      _ = z₂ := by rw [h]; group)
  have hprod : (g⁻¹ * z₁ * g) * (g⁻¹ * z₂ * g) = g⁻¹ * (z₁ * z₂) * g := by group
  have h12A : z₁ * z₂ ∈ A := mul_mem h1A h2A
  have h12K : z₁ * z₂ ∈ centralizer (A : Set G) := mul_mem h1K h2K
  have hkey : ∀ n ∈ normalizer (A : Set G), Odd (orderOf n) →
      (n * z₁ * n⁻¹ = z₁ ∨ n * (z₁ * z₂) * n⁻¹ = z₁ * z₂) → n * z₂ * n⁻¹ = z₂ := by
    intro n hn hno hfix
    obtain ⟨hwA, hwK⟩ := conj_mem_of_mem_normalizer hn h2A h2K
    have hw2 : (n * z₂ * n⁻¹) * (n * z₂ * n⁻¹) = 1 := by
      calc (n * z₂ * n⁻¹) * (n * z₂ * n⁻¹) = n * (z₂ * z₂) * n⁻¹ := by group
        _ = 1 := by rw [h22]; group
    have hw1 : n * z₂ * n⁻¹ ≠ 1 := fun h => h21 (by
      calc z₂ = n⁻¹ * (n * z₂ * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group)
    have hsq : ∀ v : G, n * z₂ * n⁻¹ = v → n * v * n⁻¹ = z₂ → n * z₂ * n⁻¹ = z₂ := by
      intro v hv hv'
      refine conj_eq_of_sq_conj_eq hno ?_
      calc n ^ 2 * z₂ * (n ^ 2)⁻¹ = n * (n * z₂ * n⁻¹) * n⁻¹ := by rw [sq]; group
        _ = z₂ := by rw [hv, hv']
    rcases hall _ hwA hwK hw2 hw1 with h | h | h
    ·
      rcases hfix with hf | hf
      · exact absurd (by
          calc z₂ = n⁻¹ * (n * z₂ * n⁻¹) * n := by group
            _ = n⁻¹ * (n * z₁ * n⁻¹) * n := by rw [h, hf]
            _ = z₁ := by group) (Ne.symm hne)
      · refine hsq z₁ h ?_
        have e : z₁ = (z₁ * z₂) * z₂ := by rw [mul_assoc, h22, mul_one]
        calc n * z₁ * n⁻¹ = n * (z₁ * z₂) * n⁻¹ * (n * z₂ * n⁻¹) := by
              conv_lhs => rw [e]
              group
          _ = z₂ := by rw [hf, h, mul_assoc, ← hcomm, ← mul_assoc, h12, one_mul]
    · exact h
    ·
      rcases hfix with hf | hf
      · refine hsq (z₁ * z₂) h ?_
        calc n * (z₁ * z₂) * n⁻¹ = (n * z₁ * n⁻¹) * (n * z₂ * n⁻¹) := by group
          _ = z₂ := by rw [hf, h, ← mul_assoc, h12, one_mul]
      · exact absurd (by
          calc z₂ = n⁻¹ * (n * z₂ * n⁻¹) * n := by group
            _ = n⁻¹ * (n * (z₁ * z₂) * n⁻¹) * n := by rw [h, hf]
            _ = z₁ * z₂ := by group) (fun h' => h11 (by
              calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, h22, mul_one]
                _ = z₂ * z₂ := by rw [← h']
                _ = 1 := h22))
  refine false_of_choice hc hPC h32 h4 h34 hS (hconjT h2A h2K h22) (hconjT h1A h1K h12)
    (hconj1 h21) (hconj1 h11) hsy ?_
  rintro u hu c ⟨hcA, hcu⟩ hco
  rw [hprod] at hu
  have huT : u ∈ T := by
    rcases hu with rfl | rfl
    · exact hconjT h1A h1K h12
    · refine hconjT h12A h12K ?_
      calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
        _ = z₁ * (z₁ * z₂) * z₂ := by rw [hcomm]
        _ = 1 := by rw [← mul_assoc, h12, one_mul, h22]
  have hu1 : u ≠ 1 := by
    rcases hu with rfl | rfl
    · exact hconj1 h11
    · exact hconj1 fun h => hne (by
        calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, h22, mul_one]
          _ = z₂ := by rw [h, one_mul])
  have hn := conj_mem_normalizer hc h32 huT hu1 hcu
  have hno : Odd (orderOf (g * c * g⁻¹)) := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hco
  refine commute_conj_of_conj_eq (hkey _ hn hno ?_)
  have hcu' : c * u * c⁻¹ = u := by
    rw [mem_centralizer_singleton_iff.mp hcu, mul_inv_cancel_right]
  rcases hu with rfl | rfl
  · left
    calc g * c * g⁻¹ * z₁ * (g * c * g⁻¹)⁻¹ = g * (c * (g⁻¹ * z₁ * g) * c⁻¹) * g⁻¹ := by group
      _ = z₁ := by rw [hcu']; group
  · right
    calc g * c * g⁻¹ * (z₁ * z₂) * (g * c * g⁻¹)⁻¹ =
        g * (c * (g⁻¹ * (z₁ * z₂) * g) * c⁻¹) * g⁻¹ := by group
      _ = z₁ * z₂ := by rw [hcu']; group

end Sec3

@[expose] def CenterElemFour (A : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ A ⊓ centralizer (A : Set G) → (∀ x ∈ P, x * x = 1) → Nat.card P ≤ 4

theorem eq_of_centerElemFour (h4 : CenterElemFour A) {z₁ z₂ w : G} (h1A : z₁ ∈ A)
    (h1K : z₁ ∈ centralizer (A : Set G)) (h12 : z₁ * z₁ = 1) (h11 : z₁ ≠ 1) (h2A : z₂ ∈ A)
    (h2K : z₂ ∈ centralizer (A : Set G)) (h22 : z₂ * z₂ = 1) (h21 : z₂ ≠ 1) (hne : z₁ ≠ z₂)
    (hwA : w ∈ A) (hwK : w ∈ centralizer (A : Set G)) (hw2 : w * w = 1) (hw1 : w ≠ 1) :
    w = z₁ ∨ w = z₂ ∨ w = z₁ * z₂ := by
  by_contra hw
  push Not at hw
  obtain ⟨hw₁, hw₂, hw₁₂⟩ := hw
  set Z := A ⊓ centralizer (A : Set G) with hZ
  have hcommZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (mem_inf.mp hb).2 a (mem_inf.mp ha).1)
  set P := closure ({z₁, z₂, w} : Set G) with hP
  have hPZ : P ≤ Z := by
    rw [hP, closure_le]
    rintro v (rfl | rfl | rfl)
    exacts [mem_inf.mpr ⟨h1A, h1K⟩, mem_inf.mpr ⟨h2A, h2K⟩, mem_inf.mpr ⟨hwA, hwK⟩]
  have hP2 : ∀ x ∈ P, x * x = 1 := by
    intro x hx
    induction hx using closure_induction with
    | mem v hv =>
      rcases hv with rfl | rfl | rfl
      exacts [h12, h22, hw2]
    | one => exact one_mul 1
    | mul a b ha hb iha ihb =>
      have hab := hcommZ a (hPZ ha) b (hPZ hb)
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = 1 := by rw [← mul_assoc, iha, one_mul, ihb]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  have hcomm : z₁ * z₂ = z₂ * z₁ := mem_centralizer_iff.mp h2K z₁ h1A
  have hp1 : z₁ * z₂ ≠ 1 := fun h => hne (by
    calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, h22, mul_one]
      _ = z₂ := by rw [h, one_mul])
  have hp₁ : z₁ * z₂ ≠ z₁ := fun h => h21 (by
    calc z₂ = z₁ * (z₁ * z₂) := by rw [← mul_assoc, h12, one_mul]
      _ = 1 := by rw [h, h12])
  have hp₂ : z₁ * z₂ ≠ z₂ := fun h => h11 (by
    calc z₁ = z₁ * z₂ * z₂ := by rw [mul_assoc, h22, mul_one]
      _ = 1 := by rw [h, h22])
  have m1 : z₁ ∈ P := subset_closure (Set.mem_insert _ _)
  have m2 : z₂ ∈ P := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have m3 : w ∈ P := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hsub : ({1, z₁, z₂, z₁ * z₂, w} : Set G) ⊆ P := by
    rintro v (rfl | rfl | rfl | rfl | rfl)
    exacts [one_mem P, m1, m2, mul_mem m1 m2, m3]
  have n4 : z₁ * z₂ ∉ ({w} : Set G) := fun h => hw₁₂ (Set.mem_singleton_iff.mp h).symm
  have n3 : z₂ ∉ ({z₁ * z₂, w} : Set G) := by
    rintro (h | h)
    exacts [hp₂ h.symm, hw₂ (Set.mem_singleton_iff.mp h).symm]
  have n2 : z₁ ∉ ({z₂, z₁ * z₂, w} : Set G) := by
    rintro (h | h | h)
    exacts [hne h, hp₁ h.symm, hw₁ (Set.mem_singleton_iff.mp h).symm]
  have n1 : (1 : G) ∉ ({z₁, z₂, z₁ * z₂, w} : Set G) := by
    rintro (h | h | h | h)
    exacts [h11 h.symm, h21 h.symm, hp1 h.symm, hw1 (Set.mem_singleton_iff.mp h).symm]
  have hcard : ({1, z₁, z₂, z₁ * z₂, w} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_singleton]
  have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq] at h5
  have h6 : 5 ≤ Nat.card P := h5
  have := h4 P hPZ hP2
  omega

end Pair

section Main

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G}

theorem odd_card_center_of_pair
    (hPC : ExcPairCent) (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g)
    (hS : ChevalleyExceptionalModel (rankTwoQuot A) .F4 2 1 ∨
      ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 1)
    (hE6 : ChevalleyExceptionalModel (rankTwoQuot A) .twistedE6 2 1 → CenterElemFour A) :
    Odd (Nat.card (center A)) := by
  by_contra hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center A) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
  have hzA : ((x : A) : G) ∈ A := (x : A).2
  have hzK : ((x : A) : G) ∈ centralizer (A : Set G) := by
    rw [mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (mem_center_iff.mp x.2 ⟨a, ha⟩)
  have hz2 : ((x : A) : G) * ((x : A) : G) = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, sq] at h
    exact congrArg (fun y : center A => ((y : A) : G)) h
  have hz1 : ((x : A) : G) ≠ 1 := by
    intro h
    have h1 : x = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hx
    omega
  rcases hS with hF4 | hE6'
  · exact Sec3.false_of_fixed hc hPC h32 h4 h34 (Or.inl hF4) hzA hzK hz2 hz1
      fun n hn hno => commute_center_of_odd_F4 hc.hyp.standard.1.1 hF4 hn hno hzA hzK
  · by_cases hu : ∃ w : G, w ∈ A ∧ w ∈ centralizer (A : Set G) ∧ w * w = 1 ∧ w ≠ 1 ∧
        w ≠ ((x : A) : G)
    · obtain ⟨w, hwA, hwK, hw2, hw1, hwz⟩ := hu
      exact Sec3.false_of_three hc hPC h32 h4 h34 (Or.inr hE6') hzA hzK hz2 hz1 hwA hwK hw2 hw1
        (Ne.symm hwz) fun v hvA hvK hv2 hv1 =>
          eq_of_centerElemFour (hE6 hE6') hzA hzK hz2 hz1 hwA hwK hw2 hw1 (Ne.symm hwz) hvA hvK hv2
            hv1
    · push Not at hu
      refine Sec3.false_of_fixed hc hPC h32 h4 h34 (Or.inr hE6') hzA hzK hz2 hz1 fun n hn _ => ?_
      obtain ⟨hwA, hwK⟩ := conj_mem_of_mem_normalizer hn hzA hzK
      refine hu _ hwA hwK ?_ ?_
      · calc n * ((x : A) : G) * n⁻¹ * (n * ((x : A) : G) * n⁻¹) =
            n * (((x : A) : G) * ((x : A) : G)) * n⁻¹ := by group
          _ = 1 := by rw [hz2]; group
      · intro h
        apply hz1
        calc ((x : A) : G) = n⁻¹ * (n * ((x : A) : G) * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group

end Main

end Step83Proof

end CFSG.ComponentClassification.RankTwoExceptional
