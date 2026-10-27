module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenPower
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.PrincipalIdealDomain

public section

namespace CFSG.AGLEmbedding.ThompsonGen

open scoped commutatorElement
open Subgroup

variable {P : Type*} [Group P]

theorem mem_sup_zpowers_iff {E : Subgroup P} [E.Normal] {q y : P} :
    y ∈ E ⊔ zpowers q ↔ ∃ e ∈ E, ∃ i : ℤ, y = e * q ^ i := by
  rw [Subgroup.mem_sup_of_normal_left]
  constructor
  · rintro ⟨e, he, z, hz, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ⟨e, he, i, rfl⟩
  · rintro ⟨e, he, i, rfl⟩
    exact ⟨e, he, q ^ i, Subgroup.zpow_mem_zpowers q i, rfl⟩

theorem line_mul_comm {E : Subgroup P} [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {q : P}
    (hq : q ∈ centralizer (E : Set P)) :
    ∀ a ∈ E ⊔ zpowers q, ∀ b ∈ E ⊔ zpowers q, a * b = b * a := by
  intro a ha b hb
  obtain ⟨e, he, i, rfl⟩ := mem_sup_zpowers_iff.1 ha
  obtain ⟨e', he', j, rfl⟩ := mem_sup_zpowers_iff.1 hb
  have hqe : ∀ f ∈ E, Commute q f := fun f hf => (mem_centralizer_iff.1 hq f hf).symm
  have h1 : Commute e e' := hEc e he e' he'
  have h2 : Commute e (q ^ j) := ((hqe e he).zpow_left j).symm
  have h3 : Commute (q ^ i) e' := (hqe e' he').zpow_left i
  have h4 : Commute (q ^ i) (q ^ j) := (Commute.refl q).zpow_zpow i j
  exact ((h1.mul_right h2).mul_left (h3.mul_right h4) : Commute (e * q ^ i) (e' * q ^ j))

theorem line_pow_eq_one {p : ℕ} {E : Subgroup P} [E.Normal] (hEp : ∀ a ∈ E, a ^ p = 1) {q : P}
    (hq : q ∈ centralizer (E : Set P)) (hqp : q ^ p = 1) :
    ∀ a ∈ E ⊔ zpowers q, a ^ p = 1 := by
  intro a ha
  obtain ⟨e, he, i, rfl⟩ := mem_sup_zpowers_iff.1 ha
  have hqe : Commute q e := (mem_centralizer_iff.1 hq e he).symm
  have h1 : Commute e (q ^ i) := (hqe.zpow_left i).symm
  rw [h1.mul_pow, hEp e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hqp, one_zpow]

theorem line_le_of_mem {p : ℕ} (hp : p.Prime) {E : Subgroup P} [E.Normal] {q : P}
    (hqp : q ^ p = 1) {y : P} (hy : y ∈ E ⊔ zpowers q) (hyE : y ∉ E) :
    E ⊔ zpowers q ≤ E ⊔ zpowers y := by
  obtain ⟨e, he, i, hyi⟩ := mem_sup_zpowers_iff.1 hy
  have hi : ¬ (p : ℤ) ∣ i := by
    rintro ⟨j, rfl⟩
    apply hyE
    have : q ^ ((p : ℤ) * j) = 1 := by rw [zpow_mul, zpow_natCast, hqp, one_zpow]
    rwa [hyi, this, mul_one]
  have hcop : IsCoprime (p : ℤ) i :=
    ((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).2 hi
  obtain ⟨a, b, hab⟩ := hcop
  have hqi : q ^ i ∈ E ⊔ zpowers y := by
    have : q ^ i = e⁻¹ * y := by rw [hyi]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ he))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hq : q ∈ E ⊔ zpowers y := by
    have h1 : q = (q ^ i) ^ b := by
      calc q = q ^ ((p : ℤ) * a + i * b) := by
            rw [show (p : ℤ) * a + i * b = 1 by linarith, zpow_one]
        _ = (q ^ i) ^ b := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, hqp, one_zpow, one_mul]
    rw [h1]
    exact Subgroup.zpow_mem _ hqi b
  exact sup_le le_sup_left (Subgroup.zpowers_le.2 hq)

theorem conj_mem_sup_zpowers {E : Subgroup P} [E.Normal] {q q' : P} (n : P)
    (h : n * q * n⁻¹ ∈ E ⊔ zpowers q') : ∀ s ∈ E ⊔ zpowers q, n * s * n⁻¹ ∈ E ⊔ zpowers q' := by
  intro s hs
  obtain ⟨e, he, i, rfl⟩ := mem_sup_zpowers_iff.1 hs
  have : n * (e * q ^ i) * n⁻¹ = (n * e * n⁻¹) * (n * q * n⁻¹) ^ i := by
    rw [conj_zpow]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Normal.conj_mem ‹E.Normal› e he n))
    (Subgroup.zpow_mem _ h i)

theorem conj_mem_centralizer {E : Subgroup P} [E.Normal] {x : P}
    (hx : x ∈ centralizer (E : Set P)) (m : P) : m * x * m⁻¹ ∈ centralizer (E : Set P) := by
  rw [mem_centralizer_iff]
  intro e he
  have h1 : m⁻¹ * e * m ∈ E := by
    have := Normal.conj_mem ‹E.Normal› e he m⁻¹
    simpa using this
  have h2 := mem_centralizer_iff.1 hx _ h1
  calc e * (m * x * m⁻¹) = m * ((m⁻¹ * e * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * e * m)) * m⁻¹ := by rw [h2]
    _ = m * x * m⁻¹ * e := by group

theorem commutator_conj_mem {p : ℕ} (hp : p.Prime) {E : Subgroup P} [E.Normal]
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {x : P} (hxC : x ∈ centralizer (E : Set P))
    (hxp : x ^ p = 1) {N : Subgroup P} (hxN : x ∈ N)
    (hNF : ∀ n ∈ N, ∀ f ∈ E ⊔ zpowers x, n * f * n⁻¹ ∈ E ⊔ zpowers x)
    {m₁ m₂ : P} (h₁ : m₁ ∈ normalizer (N : Set P)) (h₂ : m₂ ∈ normalizer (N : Set P)) :
    ⁅m₁ * x * m₁⁻¹, m₂ * x * m₂⁻¹⁆ ∈ E := by
  have key : ∀ m ∈ normalizer (N : Set P), m * x * m⁻¹ ∈ N ∧
      ∀ n ∈ N, ∀ s ∈ E ⊔ zpowers (m * x * m⁻¹), n * s * n⁻¹ ∈ E ⊔ zpowers (m * x * m⁻¹) := by
    intro m hm
    have hmN : ∀ n, n ∈ N ↔ m * n * m⁻¹ ∈ N := Subgroup.mem_normalizer_iff.1 hm
    refine ⟨(hmN x).1 hxN, fun n hn => ?_⟩
    apply conj_mem_sup_zpowers
    have hn' : m⁻¹ * n * m ∈ N := by
      rw [hmN]
      simpa [mul_assoc] using hn
    have h1 := hNF _ hn' x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have h2 := conj_mem_sup_zpowers (E := E) (q := x) (q' := m * x * m⁻¹) m
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _ h1
    have : m * ((m⁻¹ * n * m) * x * (m⁻¹ * n * m)⁻¹) * m⁻¹ = n * (m * x * m⁻¹) * n⁻¹ := by
      group
    rwa [this] at h2
  obtain ⟨hq₁N, hN₁⟩ := key m₁ h₁
  obtain ⟨hq₂N, hN₂⟩ := key m₂ h₂
  have hq₂C := conj_mem_centralizer (E := E) hxC m₂
  have hq₁p : (m₁ * x * m₁⁻¹) ^ p = 1 := by rw [conj_pow, hxp]; simp
  have hq₁mem : m₁ * x * m₁⁻¹ ∈ E ⊔ zpowers (m₁ * x * m₁⁻¹) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hq₂mem : m₂ * x * m₂⁻¹ ∈ E ⊔ zpowers (m₂ * x * m₂⁻¹) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  by_cases hy : ∃ y, y ∈ E ⊔ zpowers (m₁ * x * m₁⁻¹) ∧ y ∈ E ⊔ zpowers (m₂ * x * m₂⁻¹) ∧ y ∉ E
  · obtain ⟨y, hy1, hy2, hyE⟩ := hy
    have hle : E ⊔ zpowers (m₁ * x * m₁⁻¹) ≤ E ⊔ zpowers (m₂ * x * m₂⁻¹) :=
      (line_le_of_mem hp hq₁p hy1 hyE).trans (sup_le le_sup_left (Subgroup.zpowers_le.2 hy2))
    have hcomm := line_mul_comm hEc hq₂C _ (hle hq₁mem) _ hq₂mem
    have : ⁅m₁ * x * m₁⁻¹, m₂ * x * m₂⁻¹⁆ = 1 := by
      rw [commutatorElement_def, hcomm]; group
    rw [this]; exact one_mem E
  · push Not at hy
    have hA : ⁅m₁ * x * m₁⁻¹, m₂ * x * m₂⁻¹⁆ ∈ E ⊔ zpowers (m₂ * x * m₂⁻¹) := by
      have := hN₂ _ hq₁N _ hq₂mem
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hq₂mem)
    have hB : ⁅m₁ * x * m₁⁻¹, m₂ * x * m₂⁻¹⁆ ∈ E ⊔ zpowers (m₁ * x * m₁⁻¹) := by
      have := hN₁ _ hq₂N _ (Subgroup.inv_mem _ hq₁mem)
      have h3 : ⁅m₁ * x * m₁⁻¹, m₂ * x * m₂⁻¹⁆ =
          (m₁ * x * m₁⁻¹) * ((m₂ * x * m₂⁻¹) * (m₁ * x * m₁⁻¹)⁻¹ * (m₂ * x * m₂⁻¹)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [h3]
      exact Subgroup.mul_mem _ hq₁mem this
    exact hy _ hB hA

theorem closure_commutator_mem {E : Subgroup P} [E.Normal] {G₀ : Set P}
    (hcomm : ∀ g₁ ∈ G₀, ∀ g₂ ∈ G₀, ⁅g₁, g₂⁆ ∈ E) :
    ∀ r₁ ∈ closure G₀, ∀ r₂ ∈ closure G₀, ⁅r₁, r₂⁆ ∈ E := by
  let ρ := QuotientGroup.mk' E
  have hT : (ρ '' G₀).Pairwise Commute := by
    rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩ _
    have h1 : ρ ⁅g₁, g₂⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hcomm g₁ hg₁ g₂ hg₂)
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_commute.1 h1)
  have := Subgroup.isMulCommutative_closure hT
  intro r₁ h₁ r₂ h₂
  have hm : ∀ r ∈ closure G₀, ρ r ∈ closure (ρ '' G₀) := fun r hr => by
    rw [← MonoidHom.map_closure]; exact mem_map_of_mem ρ hr
  have hc : Commute (ρ r₁) (ρ r₂) := by
    have := mul_comm' (⟨ρ r₁, hm r₁ h₁⟩ : closure (ρ '' G₀)) ⟨ρ r₂, hm r₂ h₂⟩
    exact congrArg Subtype.val this
  have : ρ ⁅r₁, r₂⁆ = 1 := by rw [map_commutatorElement]; exact hc.commutator_eq
  exact (QuotientGroup.eq_one_iff _).1 this

theorem closure_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup P} [E.Normal]
    (hEp : ∀ a ∈ E, a ^ p = 1) {G₀ : Set P} (hcent : G₀ ⊆ centralizer (E : Set P))
    (hpow : ∀ g ∈ G₀, g ^ p = 1) (hcomm : ∀ g₁ ∈ G₀, ∀ g₂ ∈ G₀, ⁅g₁, g₂⁆ ∈ E) :
    ∀ r ∈ closure G₀, r ^ p = 1 := by
  have hcl : closure G₀ ≤ centralizer (E : Set P) := (closure_le _).2 hcent
  have h1 := closure_commutator_mem hcomm
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem g hg => exact hpow g hg
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    have hc : ⁅b, a⁆ ∈ E := h1 b hb a ha
    have hcx : Commute ⁅b, a⁆ a := mem_centralizer_iff.1 (hcl ha) _ hc
    have hcy : Commute ⁅b, a⁆ b := mem_centralizer_iff.1 (hcl hb) _ hc
    rw [mul_pow_prime_of_commutator hp hp2 hcx hcy (hEp _ hc), iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem exists_mem_relative_center_aux {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    (hΓ : IsPGroup p Γ) {E R : Subgroup Γ} [E.Normal] [R.Normal] (hER : E < R) :
    ∃ z ∈ R, z ∉ E ∧ ∀ γ : Γ, ⁅γ, z⁆ ∈ E := by
  have : Group.IsNilpotent (Γ ⧸ E) := (hΓ.to_quotient E).isNilpotent
  let π := QuotientGroup.mk' E
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective E
  have : (R.map π).Normal := Subgroup.Normal.map ‹R.Normal› π hsurj
  obtain ⟨r, hr, hrE⟩ := IsConcreteLE.exists_of_lt hER
  have hne : R.map π ≠ ⊥ := by
    intro h
    have : π r ∈ R.map π := mem_map_of_mem π hr
    rw [h, mem_bot] at this
    exact hrE ((QuotientGroup.eq_one_iff r).1 this)
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc
  obtain ⟨hwR, hwZ⟩ := hw
  obtain ⟨z, hzR, hzw⟩ := mem_map.1 hwR
  refine ⟨z, hzR, fun hzE => hw1 ?_, fun γ => ?_⟩
  · apply Subtype.ext
    show w = 1
    rw [← hzw]
    exact (QuotientGroup.eq_one_iff z).2 hzE
  · have h : π ⁅γ, z⁆ = 1 := by
      rw [map_commutatorElement, hzw]
      exact commutatorElement_eq_one_iff_mul_comm.2 ((mem_center_iff.1 hwZ) (π γ))
    exact (QuotientGroup.eq_one_iff _).1 h

theorem exists_mem_relative_center {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {E R : Subgroup P} [E.Normal] (hER : E < R) :
    ∃ z ∈ R, z ∉ E ∧ ∀ γ ∈ normalizer (R : Set P), ⁅γ, z⁆ ∈ E := by
  let Γ := normalizer (R : Set P)
  have hRΓ : R ≤ Γ := Subgroup.le_normalizer
  have : (R.subgroupOf Γ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hRΓ).2 le_rfl
  have hlt : E.subgroupOf Γ < R.subgroupOf Γ := by
    obtain ⟨r, hr, hrE⟩ := IsConcreteLE.exists_of_lt hER
    refine lt_of_le_of_ne (fun a ha => hER.le ha) (fun h => hrE ?_)
    have : (⟨r, hRΓ hr⟩ : Γ) ∈ R.subgroupOf Γ := hr
    rw [← h] at this
    exact this
  obtain ⟨z, hz, hzE, hcomm⟩ := exists_mem_relative_center_aux (hP.to_subgroup Γ) hlt
  refine ⟨z.1, hz, hzE, fun γ hγ => ?_⟩
  exact hcomm ⟨γ, hγ⟩

end CFSG.AGLEmbedding.ThompsonGen
