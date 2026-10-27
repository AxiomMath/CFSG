module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

section Inner

variable {X : Type*} [Group X]

theorem mem_inner_of_pow_prime_pow_eq_one {K : Type*} [Group K] [Finite (Outer K)] {p : ℕ}
    (hp : p.Prime) (hOut : ¬ p ∣ Nat.card (Outer K)) {f : MulAut K} {n : ℕ}
    (hf : f ^ p ^ n = 1) : f ∈ inner K := by
  have h1 : orderOf (QuotientGroup.mk' (inner K) f) ∣ p ^ n :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hf, map_one])
  have h2 : orderOf (QuotientGroup.mk' (inner K) f) ∣ Nat.card (Outer K) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime (p ^ n) (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hOut)
  have h3 : orderOf (QuotientGroup.mk' (inner K) f) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  rwa [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3

theorem mem_sup_centralizer_of_pow {p : ℕ} (hp : p.Prime) {K : Subgroup X} [K.Normal]
    [Finite (Outer K)] (hOut : ¬ p ∣ Nat.card (Outer K)) {x : X} {n : ℕ} (hx : x ^ p ^ n = 1) :
    x ∈ K ⊔ Subgroup.centralizer (K : Set X) := by
  have hf : (MulAut.conjNormal x : MulAut K) ^ p ^ n = 1 := by
    rw [← map_pow, hx, map_one]
  obtain ⟨k, hk⟩ := mem_inner_of_pow_prime_pow_eq_one hp hOut hf
  have hc : (k : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg (fun f : MulAut K => ((f ⟨y, hy⟩ : K) : X)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * (k * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = (k : X)⁻¹ * x * y := by group
  have e : x = (k : X) * ((k : X)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup k.2 hc

end Inner

theorem not_dvd_card_outer_of_quotient {K : Type*} [Group K] [Group.IsPerfect K] {p : ℕ}
    (h : ¬ p ∣ Nat.card (Outer (K ⧸ Subgroup.center K))) : ¬ p ∣ Nat.card (Outer K) :=
  fun hd => h (hd.trans (Subgroup.card_dvd_of_injective _ (centerQuotient_outer_injective K)))

section Uniform

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {R : Sylow p X}
  {X₀ : Subgroup X}

theorem not_le_of_le_sup_centralizer (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    [K.Normal] (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X))
    (hCp : IsPGroup p (Subgroup.centralizer (K : Set X)))
    (hRK : (R : Subgroup X) ≤ K ⊔ Subgroup.centralizer (K : Set X)) : ¬ K ≤ X₀ := by
  have hp : p.Prime := Fact.out
  set T : Subgroup X := (R : Subgroup X) ⊓ K
  have hT2 : 2 ≤ Open.pRank p T :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (R.isPGroup'.to_le inf_le_left) hnc
  have hCR : Subgroup.centralizer (K : Set X) ≤ (R : Subgroup X) :=
    IsPGroup.le_sylow_of_normal hCp R
  have hRle : (R : Subgroup X) ≤ T ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (T : Set X)) := by
    intro x hx
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hRK hx)
    have hcR : c ∈ (R : Subgroup X) := hCR hc
    have hkR : k ∈ (R : Subgroup X) := by
      have e : k = k * c * c⁻¹ := by group
      rw [e]
      exact (R : Subgroup X).mul_mem hx ((R : Subgroup X).inv_mem hcR)
    exact Subgroup.mul_mem_sup ⟨hkR, hk⟩
      ⟨hcR, Subgroup.centralizer_le (show (T : Set X) ⊆ K from fun _ hy => hy.2) hc⟩
  have hT3 : 3 ≤ Open.pRank p (T ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (T : Set X))) :=
    h.three_le_pRank.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp hRle)
  have hN : Subgroup.normalizer (T : Set X) ≤ X₀ :=
    (PreuniquenessRankFour.Helpers.normalizer_le_weakCore p inf_le_left hT2 hT3).trans
      h.weakCore_le
  exact not_le_of_normalizer_inf_le R hN h.ne_top

theorem weakCore_le_comap (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (T₀ : Sylow p K) (hT₀ : (T₀ : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K) :
    GLBWeakCore p (T₀ : Subgroup K) ≤ X₀.comap K.subtype := by
  have hp : p.Prime := Fact.out
  rw [PreuniquenessRankFour.Helpers.weakCore_le_iff]
  intro Q hQT hQ2 hQ3
  set Q' : Subgroup X := Q.map K.subtype
  have hQ'R : Q' ≤ (R : Subgroup X) :=
    (Subgroup.map_mono hQT).trans (hT₀.le.trans inf_le_left)
  have hQ'2 : 2 ≤ Open.pRank p Q' := by
    rwa [PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
      K.subtype_injective]
  have hmap : (Q ⊔ ((T₀ : Subgroup K) ⊓ Subgroup.centralizer (Q : Set K))).map K.subtype ≤
      Q' ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (Q' : Set X)) := by
    rw [Subgroup.map_sup]
    refine sup_le_sup_left ?_ _
    rintro _ ⟨y, ⟨hyT, hyC⟩, rfl⟩
    refine ⟨(hT₀.le ⟨y, hyT, rfl⟩).1, ?_⟩
    show (y : X) ∈ Subgroup.centralizer (Q' : Set X)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hyC q hq)
  have hQ'3 :
      3 ≤ Open.pRank p (Q' ⊔ ((R : Subgroup X) ⊓ Subgroup.centralizer (Q' : Set X))) := by
    refine le_trans ?_ (PreuniquenessRankFour.Helpers.pRank_mono p hp hmap)
    rwa [PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
      K.subtype_injective]
  have hN := (PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hQ'R hQ'2 hQ'3).trans
    h.weakCore_le
  intro x hx
  exact hN (Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hx))

theorem le_of_weakCore_eq_top (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (T₀ : Sylow p K) (hT₀ : (T₀ : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (htop : GLBWeakCore p (T₀ : Subgroup K) = ⊤) : K ≤ X₀ := by
  intro x hxK
  have hx : (⟨x, hxK⟩ : K) ∈ GLBWeakCore p (T₀ : Subgroup K) := htop ▸ Subgroup.mem_top _
  exact weakCore_le_comap h T₀ hT₀ hx

theorem pRank_le_two_of_centralizer_eq_bot {K : Subgroup X} (T₀ : Sylow p K)
    (hT₀ : (T₀ : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hC : Subgroup.centralizer (K : Set X) = ⊥)
    (hRK : (R : Subgroup X) ≤ K ⊔ Subgroup.centralizer (K : Set X))
    (hT2 : Open.pRank p (T₀ : Subgroup K) ≤ 2) : Open.pRank p (R : Subgroup X) ≤ 2 := by
  have hp : p.Prime := Fact.out
  rw [hC, sup_bot_eq] at hRK
  have hR : (R : Subgroup X) = (T₀ : Subgroup K).map K.subtype := by
    rw [hT₀, inf_eq_left.mpr hRK]
  rwa [hR, PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
    K.subtype_injective]

omit [Finite X] [Fact p.Prime] in
theorem le_inf_sup_centralizer {K : Subgroup X} [K.Normal]
    (hCR : Subgroup.centralizer (K : Set X) ≤ (R : Subgroup X))
    (hRK : (R : Subgroup X) ≤ K ⊔ Subgroup.centralizer (K : Set X)) :
    (R : Subgroup X) ≤ ((R : Subgroup X) ⊓ K) ⊔ Subgroup.centralizer (K : Set X) := by
  intro x hx
  obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hRK hx)
  have hkR : k ∈ (R : Subgroup X) := by
    have e : k = k * c * c⁻¹ := by group
    rw [e]
    exact (R : Subgroup X).mul_mem hx ((R : Subgroup X).inv_mem (hCR hc))
  exact Subgroup.mul_mem_sup ⟨hkR, hk⟩ hc

end Uniform

end CFSG.AGLEmbedding
