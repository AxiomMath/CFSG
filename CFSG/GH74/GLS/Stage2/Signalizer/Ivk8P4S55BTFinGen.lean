module

public import CFSG.CharacterTheory.Burnside
public import CFSG.RankThree.PartOne.N143.GroupLemmas
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinGen

open Subgroup
open scoped Nat commutatorElement

variable {G : Type} [Group G]

theorem isSolvable_of_card_eq_pow_mul_pow {H : Type*} [Group H] [Finite H] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card H = p ^ a * q ^ b) :
    Group.IsSolvable H := by
  have := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rwa [← Nat.card_eq_fintype_card])

theorem eq_bot_of_perfect_of_le {I W : Subgroup G} (hIW : I ≤ W) (hW : Group.IsSolvable ↥W)
    (hI : ⁅I, I⁆ = I) : I = ⊥ := by
  by_contra hne
  have : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).mpr hne
  have : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr hI
  have hsol : Group.IsSolvable ↥I :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hIW).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hIW).surjective
  exact Group.IsPerfect.not_isSolvable ↥I hsol

theorem le_centralizer_of_conj_mem {I : Subgroup G} (hI : ⁅I, I⁆ = I) {x : G}
    (hN : ∀ g ∈ I, g * x * g⁻¹ ∈ zpowers x) : I ≤ centralizer ({x} : Set G) := by
  have hpow : ∀ h ∈ I, ∃ k : ℤ, h * x * h⁻¹ = x ^ k := fun h hh => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hN h hh)
    exact ⟨k, hk.symm⟩
  have hconj : ∀ h ∈ I, ∀ k m : ℤ, h * x * h⁻¹ = x ^ k → h * x ^ m * h⁻¹ = x ^ (k * m) :=
    fun h _ k m hk => by
      rw [show h * x ^ m * h⁻¹ = (h * x * h⁻¹) ^ m by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow], hk, ← zpow_mul]
  rw [← hI, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨k₁, hk₁⟩ := hpow a⁻¹ (inv_mem ha)
  obtain ⟨k₂, hk₂⟩ := hpow b⁻¹ (inv_mem hb)
  have h12 : a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹ = x ^ (k₁ * k₂) := by
    rw [show a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹ = a⁻¹ * (b⁻¹ * x * b⁻¹⁻¹) * a⁻¹⁻¹ by group, hk₂,
      hconj _ (inv_mem ha) k₁ k₂ hk₁]
  have h21 : b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹ = x ^ (k₁ * k₂) := by
    rw [show b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹ = b⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) * b⁻¹⁻¹ by group, hk₁,
      hconj _ (inv_mem hb) k₂ k₁ hk₂, mul_comm]
  rw [mem_centralizer_singleton_iff]
  have key : (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) * x * ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹))⁻¹ = x := by
    calc (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) * x * ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹))⁻¹
        = (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹ * x * (a⁻¹ * b⁻¹)⁻¹) * (b⁻¹ * a⁻¹) := by group
      _ = (b⁻¹ * a⁻¹)⁻¹ * (b⁻¹ * a⁻¹ * x * (b⁻¹ * a⁻¹)⁻¹) * (b⁻¹ * a⁻¹) := by rw [h12, h21]
      _ = x := by group
  have hc : ⁅a, b⁆ = (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hc]
  calc (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) * x
      = ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) * x * ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹))⁻¹) *
          ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹)) := by group
    _ = x * ((b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹)) := by rw [key]

theorem le_centralizer_of_le_normalizer_zpowers {I : Subgroup G} (hI : ⁅I, I⁆ = I) {x : G}
    (hN : I ≤ normalizer ((zpowers x : Subgroup G) : Set G)) :
    I ≤ centralizer ({x} : Set G) :=
  le_centralizer_of_conj_mem hI fun _ hg => (mem_normalizer_iff.mp (hN hg) x).mp (mem_zpowers x)

theorem le_centralizer_of_nine [Finite G] {I Ω : Subgroup G} (hI : ⁅I, I⁆ = I)
    (hN : I ≤ normalizer (Ω : Set G)) [CFSG.IsElementaryAbelian 3 ↥Ω] (hcard : Nat.card ↥Ω = 9) :
    I ≤ centralizer (Ω : Set G) := by
  have : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr hI
  let ψ : ↥I →* MulAut ↥Ω := Ω.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hsol : Group.IsSolvable ↥ψ.range := by
    have hd : Nat.card ↥ψ.range ∣ 2 ^ 4 * 3 ^ 1 :=
      (Subgroup.card_subgroup_dvd_card _).trans
        (CFSG.RankThree.PartOne.N143.card_mulAut_dvd_forty_eight Ω hcard)
    obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 hd
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hk₂
    exact isSolvable_of_card_eq_pow_mul_pow Nat.prime_two Nat.prime_three (by norm_num) hk.symm
  have hbot : ψ.range = ⊥ := eq_bot_of_perfect_of_le le_rfl hsol hperf
  intro g hg
  have h1 : ψ ⟨g, hg⟩ = 1 := by
    have : ψ ⟨g, hg⟩ ∈ ψ.range := ⟨⟨g, hg⟩, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h2 : (⟨g, hN hg⟩ : ↥(normalizer (Ω : Set G))) ∈ Ω.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
  exact h2

@[expose] def omegaZ (X : Subgroup G) (p : ℕ) : Subgroup G where
  carrier := {z | z ∈ X ∧ (∀ x ∈ X, z * x = x * z) ∧ z ^ p = 1}
  one_mem' := ⟨X.one_mem, fun x _ => by simp, one_pow p⟩
  mul_mem' := by
    rintro a b ⟨haX, ha, hap⟩ ⟨hbX, hb, hbp⟩
    refine ⟨X.mul_mem haX hbX, fun x hx => ?_, ?_⟩
    · rw [mul_assoc, hb x hx, ← mul_assoc, ha x hx, mul_assoc]
    · rw [(show Commute a b from ha b hbX).mul_pow, hap, hbp, one_mul]
  inv_mem' := by
    rintro a ⟨haX, ha, hap⟩
    refine ⟨X.inv_mem haX, fun x hx => ?_, by rw [inv_pow, hap, inv_one]⟩
    have h := ha x hx
    calc a⁻¹ * x = a⁻¹ * (x * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * x) * a⁻¹ := by rw [h]
      _ = x * a⁻¹ := by group

theorem le_normalizer_omegaZ {X I : Subgroup G} (p : ℕ) (hIX : I ≤ normalizer (X : Set G)) :
    I ≤ normalizer ((omegaZ X p : Subgroup G) : Set G) := by
  have key : ∀ g ∈ normalizer (X : Set G), ∀ z ∈ omegaZ X p, g * z * g⁻¹ ∈ omegaZ X p := by
    rintro g hg z ⟨hzX, hz, hzp⟩
    refine ⟨(mem_normalizer_iff.mp hg z).mp hzX, fun x hx => ?_, ?_⟩
    · have hx' : g⁻¹ * x * g ∈ X := by
        have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
        simpa using this
      have h := hz _ hx'
      calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [h]
        _ = x * (g * z * g⁻¹) := by group
    · rw [show (g * z * g⁻¹) ^ p = g * z ^ p * g⁻¹ by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_pow], hzp]
      group
  intro g hg
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key g (hIX hg) z, fun h => ?_⟩
  have := key g⁻¹ (inv_mem (hIX hg)) _ h
  simpa [mul_assoc] using this

theorem exists_centralized [Finite G] {p : ℕ} (hp : p.Prime) {X I : Subgroup G}
    (hX : IsPGroup p ↥X) (hX1 : X ≠ ⊥) (hI : ⁅I, I⁆ = I) (hIX : I ≤ normalizer (X : Set G))
    (hrank : ∀ E : Subgroup G, CFSG.IsElementaryAbelian p ↥E →
      Nat.card ↥E ≤ p ∨ (p = 3 ∧ Nat.card ↥E ≤ 9)) :
    ∃ x ∈ X, orderOf x = p ∧ I ≤ centralizer ({x} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  set Ω := omegaZ X p with hΩ
  have hΩX : Ω ≤ X := fun z hz => hz.1
  have hΩp : IsPGroup p ↥Ω := hX.to_le hΩX
  have hΩab : ∀ a ∈ Ω, ∀ b ∈ Ω, a * b = b * a := fun a ha b hb => ha.2.1 b hb.1
  have hEA : CFSG.IsElementaryAbelian p ↥Ω :=
    { is_comm := ⟨fun a b => Subtype.ext (hΩab a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a =>
        Subtype.ext (by simpa using a.2.2.2) }
  have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hZ := hX.center_nontrivial
  have hZp : IsPGroup p ↥(Subgroup.center ↥X) := hX.to_subgroup (Subgroup.center ↥X)
  obtain ⟨n, hn, hcn⟩ := hZp.nontrivial_iff_card.mp hZ
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥X)) p
    (by rw [hcn]; exact dvd_pow_self p hn.ne')
  set x : G := ((z₀ : ↥X) : G) with hx
  have hxp : orderOf x = p := by
    rw [hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz₀]
  have hxΩ : x ∈ Ω := by
    refine ⟨(z₀ : ↥X).2, fun y hy => ?_, by rw [← hxp, pow_orderOf_eq_one]⟩
    have := Subgroup.mem_center_iff.mp z₀.2 ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  have hIΩ := le_normalizer_omegaZ p hIX
  refine ⟨x, hΩX hxΩ, hxp, ?_⟩
  have hcardΩ := hrank Ω hEA
  have hx1 : Nat.card ↥(zpowers x) = p := by rw [Nat.card_zpowers, hxp]
  have hxle : zpowers x ≤ Ω := (zpowers_le).mpr hxΩ
  have hpdvd : p ∣ Nat.card ↥Ω := hx1 ▸ Subgroup.card_dvd_of_le hxle
  rcases hcardΩ with hle | ⟨rfl, hle⟩
  · have heq : zpowers x = Ω := Subgroup.eq_of_le_of_card_ge hxle (by
      rw [hx1]; exact hle)
    exact le_centralizer_of_le_normalizer_zpowers hI (heq ▸ hIΩ)
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hΩp
    have hk2 : k ≤ 2 := by
      by_contra hk2
      have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k
    · simp at hk
      rw [hk] at hpdvd
      exact absurd hpdvd (by norm_num)
    · have heq : zpowers x = Ω := Subgroup.eq_of_le_of_card_ge hxle (by rw [hx1, hk]; norm_num)
      exact le_centralizer_of_le_normalizer_zpowers hI (heq ▸ hIΩ)
    · have hc := le_centralizer_of_nine hI hIΩ (by rw [hk]; norm_num)
      intro g hg
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp (hc hg) x hxΩ).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinGen
