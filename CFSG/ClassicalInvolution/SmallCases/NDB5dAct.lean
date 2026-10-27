module

public import CFSG.ClassicalInvolution.SmallCases.NDB5dSL2
public import CFSG.ClassicalInvolution.Q3.TL3Act
public import CFSG.ClassicalInvolution.Balance.FuzzyAdjAxis

public section

namespace CFSG.ClassicalInvolution.NDB.WC

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups commutatorElement

section Congr

variable {A B : Type*} [Group A] [Group B]

@[expose] def autCongr (e : A ≃* B) : MulAut A →* MulAut B where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := by
    ext b
    simp
  map_mul' φ ψ := by
    ext b
    simp [MulAut.mul_apply]

theorem autCongr_conj (e : A ≃* B) (a : A) : autCongr e (MulAut.conj a) = MulAut.conj (e a) := by
  ext b
  show e (a * e.symm b * a⁻¹) = e a * b * (e a)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem autCongr_eq_one_iff (e : A ≃* B) (φ : MulAut A) : autCongr e φ = 1 ↔ φ = 1 := by
  constructor
  · intro h
    ext a
    have := DFunLike.congr_fun h (e a)
    simp only [autCongr, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulAut.one_apply] at this
    exact e.injective this
  · rintro rfl
    exact map_one _

end Congr

theorem commutator_top_of {G : Type*} [Group G] {N : Subgroup G} (hN : ⁅N, N⁆ = N) :
    ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ = ⊤ := by
  have htop : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, htop, hN]

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem odd_card_galoisField (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : Odd (Nat.card (GaloisField p f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow

theorem exists_sl2_action (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) {c t : G} (hc : c ∈ Subgroup.normalizer (J : Set G))
    (ht : t ∈ J) (htt : t * t = z) (hct : c * t⁻¹ ∈ trivialOnQuot J) :
    ∃ (τ : SL(2, GaloisField p f))
      (ρ : Subgroup.normalizer (J : Set G) →* MulAut SL(2, GaloisField p f)),
      ((τ * τ : SL(2, GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) = -1 ∧
        ρ ⟨c, hc⟩ = MulAut.conj τ ∧ ∀ g, ρ g = 1 → (g : G) ∈ trivialOnQuot J := by
  have hF := odd_card_galoisField hp2 hq
  obtain ⟨e⟩ : Nonempty (J ⧸ CFSG.oddCore J ≃* SL(2, GaloisField p f)) := hJ.nonempty_equiv
  set ρ : Subgroup.normalizer (J : Set G) →* MulAut SL(2, GaloisField p f) :=
    (autCongr e).comp (Q3.tl3Act J) with hρ
  set τ : SL(2, GaloisField p f) := e (((⟨t, ht⟩ : J) : J ⧸ CFSG.oddCore J)) with hτdef
  have hzq : orderOf (((⟨z, hJ.mem⟩ : J) : J ⧸ CFSG.oddCore J)) = 2 := by
    have hz2 : (⟨z, hJ.mem⟩ : J) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hJ.orderOf_eq_two]
      exact pow_orderOf_eq_one z
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hz2, QuotientGroup.mk_one]
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      have hdvd := Subgroup.orderOf_dvd_natCard (CFSG.oddCore J) h1
      have hodd : Odd (Nat.card (CFSG.oddCore J)) :=
        CFSG.ComponentClassification.OddCore.odd_card J
      have h2 : orderOf (⟨z, hJ.mem⟩ : J) = 2 := by
        rw [← Subgroup.orderOf_coe]
        exact hJ.orderOf_eq_two
      rw [h2] at hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hτ : ((τ * τ : SL(2, GaloisField p f)) : Matrix (Fin 2) (Fin 2) (GaloisField p f)) =
      -1 := by
    have h1 : τ * τ = e (((⟨z, hJ.mem⟩ : J) : J ⧸ CFSG.oddCore J)) := by
      rw [hτdef, ← map_mul, ← QuotientGroup.mk_mul]
      congr 2
      exact Subtype.ext htt
    have h2 : orderOf (τ * τ) = 2 := by
      rw [h1, MulEquiv.orderOf_eq]
      exact hzq
    rw [(sl2_orderOf_eq_two_iff hF _).mp h2]
    rfl
  have hρc : ρ ⟨c, hc⟩ = MulAut.conj τ := by
    have hct' : Q3.tl3Act J ⟨c * t⁻¹, hct.1⟩ = 1 :=
      (Q3.tl3Act_eq_one_iff J ⟨c * t⁻¹, hct.1⟩).mpr hct.2
    have e1 : (⟨c, hc⟩ : Subgroup.normalizer (J : Set G)) =
        ⟨c * t⁻¹, hct.1⟩ * ⟨t, Subgroup.le_normalizer ht⟩ := Subtype.ext (by simp)
    rw [hρ, MonoidHom.comp_apply, e1, map_mul, hct', one_mul,
      Q3.tl3Act_of_mem J ⟨t, ht⟩, autCongr_conj]
  refine ⟨τ, ρ, hτ, hρc, fun g hg => ?_⟩
  rw [hρ, MonoidHom.comp_apply, autCongr_eq_one_iff] at hg
  exact ⟨g.2, (Q3.tl3Act_eq_one_iff J g).mp hg⟩

theorem mem_trivialOnQuot_of_derived (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) {X : Subgroup G}
    (hXJ : X ≤ Subgroup.normalizer (J : Set G)) {c t : G}
    (hc : c ∈ Subgroup.normalizer (J : Set G)) (ht : t ∈ J) (htt : t * t = z)
    (hct : c * t⁻¹ ∈ trivialOnQuot J) (hcX : ∀ x ∈ X, c * x = x * c) {x a : G} (hx : x ∈ X)
    (hx2 : x * x = 1) (ha : a ∈ X) (ha3 : (⟨a, ha⟩ : X) ∈ derivedSeries X 3)
    (hodd : Odd (orderOf (a⁻¹ * x))) : x ∈ trivialOnQuot J := by
  obtain ⟨τ, ρ, hτ, hρc, hρ1⟩ := exists_sl2_action hp2 hq hJ hc ht htt hct
  set φ := ρ.comp (Subgroup.inclusion hXJ) with hφ
  have hder := derived_map_eq_one (odd_card_galoisField hp2 hq) hτ φ (fun y => by
    rw [← hρc, hφ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcX y y.2).symm) ⟨a, ha⟩ ha3
  set b : X := (⟨a, ha⟩ : X)⁻¹ * ⟨x, hx⟩ with hb
  have hφx : φ ⟨x, hx⟩ = φ b := by
    rw [hb, map_mul, map_inv, hder, inv_one, one_mul]
  have hob : Odd (orderOf (φ b)) := by
    refine Odd.of_dvd_nat ?_ (orderOf_map_dvd φ b)
    rw [← Subgroup.orderOf_coe]
    exact hodd
  have h2 : orderOf (φ ⟨x, hx⟩) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_two]
    have : (⟨x, hx⟩ : X) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
    rw [this, map_one]
  rw [hφx] at h2
  have h1 : orderOf (φ b) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hob
      exact absurd hob (by decide)
  rw [orderOf_eq_one_iff, ← hφx] at h1
  exact hρ1 _ h1

end CFSG.ClassicalInvolution.NDB.WC
