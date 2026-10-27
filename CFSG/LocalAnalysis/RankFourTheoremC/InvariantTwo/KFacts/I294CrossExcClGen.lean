module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTorus
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

section NumberTheory

@[expose] def crossExcClGeom (q x : ℕ) : ℕ := ∑ j ∈ Finset.range x, q ^ j

theorem crossExcClGeom_mul {q : ℕ} (hq : 1 ≤ q) (x : ℕ) :
    (q - 1) * crossExcClGeom q x = q ^ x - 1 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_sub (Nat.one_le_pow _ _ hq), crossExcClGeom]
  push_cast
  rw [mul_comm]
  exact geom_sum_mul (q : ℤ) x

theorem crossExcClGeom_cast {p q : ℕ} (hqp : (q : ZMod p) = 1) (x : ℕ) :
    ((crossExcClGeom q x : ℕ) : ZMod p) = x := by
  rw [crossExcClGeom]
  push_cast
  simp [hqp]

theorem crossExcClGeom_not_dvd {p q x : ℕ} (hq : 1 ≤ q) (hpq : p ∣ q - 1) (hx : ¬ p ∣ x) :
    ¬ p ∣ crossExcClGeom q x := by
  have hqp : (q : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) p).2 hpq
    rwa [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
  intro h
  apply hx
  rw [← ZMod.natCast_eq_zero_iff, ← crossExcClGeom_cast hqp x]
  exact (ZMod.natCast_eq_zero_iff _ p).2 h

theorem crossExcCl_prod_pow_two {q : ℕ} (hq : 1 ≤ q) (m : ℕ) :
    ∏ i ∈ Finset.Icc 1 m, (q ^ (2 * i) - 1) =
      (q - 1) ^ m * ∏ i ∈ Finset.Icc 1 m, crossExcClGeom q (2 * i) := by
  have h : ∀ i ∈ Finset.Icc 1 m, q ^ (2 * i) - 1 = (q - 1) * crossExcClGeom q (2 * i) :=
    fun i _ => (crossExcClGeom_mul hq _).symm
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc,
    Nat.add_sub_cancel]

theorem crossExcCl_not_dvd_prod_geom {p q m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) (hm : m < p) : ¬ p ∣ ∏ i ∈ Finset.Icc 1 m, crossExcClGeom q (2 * i) := by
  intro h
  obtain ⟨i, hi, hdvd⟩ := (Prime.dvd_finset_prod_iff hp.prime _).1 h
  rw [Finset.mem_Icc] at hi
  apply crossExcClGeom_not_dvd hq hpq _ hdvd
  intro h2
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  · have := Nat.le_of_dvd (by omega) h2
    omega

end NumberTheory

section Torus

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Finite K]

theorem crossExcCl_sylow_abelian_of_torus {s : ℕ} (τ : (Fin s → Kˣ) →* G)
    (hτ : Function.Injective τ) {M : ℕ} (hM : Nat.card G = (Nat.card K - 1) ^ s * M)
    (hpM : ¬ p ∣ M) (S : Sylow p G) : IsMulCommutative (S : Subgroup G) := by
  have hT : Nat.card τ.range = (Nat.card K - 1) ^ s := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv, Nat.card_pi]
    simp [Nat.card_units]
  have hne : (Nat.card K - 1) ^ s ≠ 0 :=
    pow_ne_zero _ (Nat.sub_ne_zero_of_lt Finite.one_lt_card)
  have hidx : τ.range.index = M := by
    have h := τ.range.card_mul_index
    rw [hT, hM] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) h
  refine isMulCommutative_sylow_of_comm_index (H := τ.range) ?_ (hidx ▸ hpM) S
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

end Torus

section Reduction

theorem crossExcCl_isMulCommutative_of_map_injective {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (hf : Function.Injective f) {P : Subgroup G} (h : IsMulCommutative (P.map f)) :
    IsMulCommutative P :=
  .of_setLike_mul_comm fun a ha b hb => hf (by
    simpa using setLike_mul_comm (Subgroup.mem_map_of_mem f ha) (Subgroup.mem_map_of_mem f hb))

theorem crossExcCl_exists_order_data {K : Type*} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hpK : ¬ p ∣ Nat.card K) : ∃ e : ℕ, 0 < e ∧ ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j := by
  set q := Nat.card K with hq
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpK
  refine ⟨orderOf (q : ZMod p), ?_, fun j => ?_⟩
  · refine orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, ?_, ?_⟩)
    · have := hp.out.two_le
      omega
    · exact ZMod.pow_card_sub_one_eq_one hq0
  · have hq1 : 1 ≤ q ^ j := Nat.one_le_pow _ _ Finite.card_pos
    rw [orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, Nat.cast_pow,
      Nat.cast_one, sub_eq_zero]

theorem crossExcCl_isMulCommutative_GL {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {p : ℕ} [Fact p.Prime] (hp2 : Odd p) (hpK : ¬ p ∣ Nat.card K) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (hne : Fintype.card ι / e < p)
    {P : Subgroup (GL ι K)} (hP : IsPGroup p P) : IsMulCommutative P := by
  let ψ : GL ι K ≃* (Module.End K (ι → K))ˣ := Matrix.GeneralLinearGroup.toLin
  have h1 : IsPGroup p (P.map ψ.toMonoidHom) := hP.map ψ.toMonoidHom
  have hfr : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  exact crossExcCl_isMulCommutative_of_map_injective ψ.toMonoidHom ψ.injective
    (isMulCommutative_of_isPGroup_GL (V := ι → K) hp2 hpK he hpe (by rw [hfr]; exact hne) h1)

theorem crossExcCl_sylow_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hN : Fintype.card ι / 2 < p) (H : Subgroup (GL ι K))
    (hsplit : p ∣ Nat.card K - 1 → ∀ S : Sylow p H, IsMulCommutative (S : Subgroup H))
    (R : Sylow p (StatedProj H)) : IsMulCommutative (R : Subgroup (StatedProj H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hH : ∀ S : Sylow p H, IsMulCommutative (S : Subgroup H) := by
    by_cases h1 : p ∣ Nat.card K - 1
    · exact hsplit h1
    · intro S
      obtain ⟨e, he, hpe⟩ := crossExcCl_exists_order_data hpK
      have he1 : e ≠ 1 := by
        rintro rfl
        exact h1 (by simpa using (hpe 1).2 dvd_rfl)
      have hne : Fintype.card ι / e < p :=
        lt_of_le_of_lt (Nat.div_le_div_left (by omega) (by norm_num)) hN
      have hodd : Odd p := hp.odd_of_ne_two hp2
      have h2 : IsMulCommutative ((S : Subgroup H).map H.subtype) :=
        crossExcCl_isMulCommutative_GL hodd hpK he hpe hne (S.isPGroup'.map _)
      exact crossExcCl_isMulCommutative_of_map_injective H.subtype H.subtype_injective h2
  exact isMulCommutative_sylow_of_surjective
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)) (QuotientGroup.mk'_surjective _) hH R

end Reduction

end CFSG.LocalAnalysis.RankFourTheoremC
