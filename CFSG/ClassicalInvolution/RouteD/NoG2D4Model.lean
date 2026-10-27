module

public import CFSG.ClassicalInvolution.RouteD.NoG2D4Count

public section

namespace CFSG.ClassicalInvolution.RouteD.G2D4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.Generic CFSG.Open
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime]

theorem center_modelUniv_g2d4_eq_bot (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4) (n : ℕ) {e : ℕ} (he : 1 ≤ e) :
    Subgroup.center (modelUniv t n p e Fact.out).K = ⊥ := by
  rcases ht with rfl | rfl
  · show Subgroup.center ↥(adjointGroup .G2 (GaloisField p e)) = ⊥
    exact center_adjointGroup_eq_bot
  · show Subgroup.center ↥(twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e)) = ⊥
    have h3 := map_twistedGroup_eq_graphFixedRootGroup p e hp2 he
    have hK3 : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
      rw [GaloisField.card p (3 * e) (by omega), pow_mul']
    have hfin : Finite (GaloisField p (3 * e)) := Nat.finite_of_card_ne_zero (by
      rw [hK3]
      exact (pow_pos (pow_pos (Fact.out : p.Prime).pos e) _).ne')
    have hZ := center_graphFixedRootGroup_eq_bot (t := TwistTag.D4) (K := GaloisField p (3 * e))
      (σ := iterateFrobenius (GaloisField p (3 * e)) p e)
      (Finite.surjective_of_injective (iterateFrobenius (GaloisField p (3 * e)) p e).injective)
    let e₁ := Subgroup.equivMapOfInjective
      (twistedGroup (iterateFrobenius (GaloisField p (3 * e)) p e))
      (adjointGroup d4 (GaloisField p (3 * e))).subtype (Subgroup.subtype_injective _)
    let e₂ := e₁.trans (MulEquiv.subgroupCongr h3)
    have hcard : Nat.card (Subgroup.center ↥(twistedGroup
        (iterateFrobenius (GaloisField p (3 * e)) p e))) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr e₂).toEquiv, hZ, Subgroup.card_bot]
    exact Subgroup.card_eq_one.mp hcard

theorem injective_of_ker_le_center (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4) (n : ℕ) {e : ℕ} (he : 1 ≤ e) {X : Type} [Group X]
    (φ : (modelUniv t n p e Fact.out).K →* X)
    (hker : φ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  exact hker.trans (center_modelUniv_g2d4_eq_bot hp2 ht n he).le

@[expose] def G2D4SharedInvolution (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e → p ≠ 2 →
    (t = .G2 ∨ t = .trialityD4) →
    ∀ P : Subgroup (modelUniv t n p e Fact.out).K, ⁅P, P⁆ = P →
    ∀ c₁ c₂ : (modelUniv t n p e Fact.out).K, c₁ * c₁ = 1 → c₁ ≠ 1 → c₂ ≠ 1 → c₂ ∈ P →
      (∀ r ∈ P, c₂ * r = r * c₂) → (∀ r ∈ P, c₁ * r = r * c₁) → c₂ = c₁

theorem eq_of_central_involutions (h : G2D4SharedInvolution p) (hp2 : p ≠ 2) {t : StatedLieTag}
    (ht : t = .G2 ∨ t = .trialityD4) {n e : ℕ} (hadm : StatedLieAdmissible t n p e) {X : Type}
    [Group X] (φ : (modelUniv t n p e Fact.out).K →* X) (hinj : Function.Injective φ)
    {B : Subgroup X} (hB : B ≤ φ.range) (hBperf : ⁅B, B⁆ = B) {a b : X} (ha : a ∈ φ.range)
    (hasq : a * a = 1) (ha1 : a ≠ 1) (hab : ∀ y ∈ B, a * y = y * a) (hb : b ∈ B) (hb1 : b ≠ 1)
    (hbcent : ∀ y ∈ B, b * y = y * b) : b = a := by
  obtain ⟨ra, hra⟩ := ha
  obtain ⟨rb, hrb⟩ := hB hb
  set P : Subgroup (modelUniv t n p e Fact.out).K := B.comap φ with hP
  have hPmap : P.map φ = B := Subgroup.map_comap_eq_self hB
  have hperf : ⁅P, P⁆ = P := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hPmap, hBperf]
  have hrbP : rb ∈ P := by
    rw [hP, Subgroup.mem_comap, hrb]
    exact hb
  have key := h t n e hadm hp2 ht P hperf ra rb
    (hinj (by rw [map_mul, hra, hasq, map_one])) (fun e1 => ha1 (by rw [← hra, e1, map_one]))
    (fun e1 => hb1 (by rw [← hrb, e1, map_one])) hrbP
    (fun r hr => hinj (by
      rw [map_mul, map_mul, hrb]
      exact hbcent (φ r) (by simpa [hP, Subgroup.mem_comap] using hr)))
    (fun r hr => hinj (by
      rw [map_mul, map_mul, hra]
      exact hab (φ r) (by simpa [hP, Subgroup.mem_comap] using hr)))
  rw [← hrb, ← hra, key]

end CFSG.ClassicalInvolution.RouteD.G2D4
