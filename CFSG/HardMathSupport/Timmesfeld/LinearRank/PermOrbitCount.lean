module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

open MulAction

theorem card_le_prod_card_orbit {n : ℕ} (F : Subgroup (Equiv.Perm (Fin n)))
    [Fintype (orbitRel.Quotient F (Fin n))] (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) :
    Nat.card F ≤ ∏ ω : orbitRel.Quotient F (Fin n), Nat.card (orbit F (Quotient.out ω)) := by
  let φ : F → ∀ ω : orbitRel.Quotient F (Fin n), orbit F (Quotient.out ω) :=
    fun g ω => ⟨g • Quotient.out ω, mem_orbit _ _⟩
  have hφ : Function.Injective φ := by
    intro g g' hgg'
    have hrep : ∀ ω : orbitRel.Quotient F (Fin n), g • Quotient.out ω = g' • Quotient.out ω :=
      fun ω => congrArg Subtype.val (congrFun hgg' ω)
    have hcomm : ∀ a b : F, a * b = b * a := fun a b => Subtype.ext (hFc _ a.2 _ b.2)
    refine Subtype.ext (Equiv.ext fun x => ?_)
    obtain ⟨h, hh⟩ :=
      mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.mk_out (s := orbitRel F (Fin n)) x))
    have key : h • (g • x) = h • (g' • x) := by
      rw [smul_smul, hcomm, ← smul_smul, hh, hrep, ← hh, smul_smul, hcomm, ← smul_smul]
    exact smul_left_cancel_iff h |>.mp key
  rw [← Nat.card_pi]
  exact Nat.card_le_card_of_injective φ hφ

theorem card_sq_mul_pow_orbits_le {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (F : Subgroup (Equiv.Perm (Fin n)))
    (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hFp : ∀ x ∈ F, x ^ p = 1) :
    Nat.card F ^ 2 * p ^ Nat.card (orbitRel.Quotient F (Fin n)) ≤ p ^ n := by
  classical
  have := Fact.mk hp
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have hlin : ∀ k : ℕ, 2 * k + 1 ≤ p ^ k := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
      have h2 : p ^ k * 3 ≤ p ^ k * p := Nat.mul_le_mul_left _ h3
      rw [pow_succ]
      omega
  have hpg : IsPGroup p F := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hFp _ g.2)⟩
  set c : orbitRel.Quotient F (Fin n) → ℕ := fun ω => Nat.card (orbit F (Quotient.out ω))
    with hc
  have hcard : Nat.card F ≤ ∏ ω, c ω := card_le_prod_card_orbit F hFc
  have hsum : ∑ ω, c ω = n := by
    rw [hc, ← Nat.card_sigma, ← Nat.card_congr (selfEquivSigmaOrbits F (Fin n)),
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hpow : ∀ ω, c ω ^ 2 * p ≤ p ^ c ω := fun ω => by
    obtain ⟨k, hk⟩ := hpg.card_orbit (Quotient.out ω)
    have hck : c ω = p ^ k := hk
    rw [hck, ← pow_mul, ← pow_succ]
    exact Nat.pow_le_pow_right hp.pos (by have := hlin k; omega)
  calc Nat.card F ^ 2 * p ^ Nat.card (orbitRel.Quotient F (Fin n))
      ≤ (∏ ω, c ω) ^ 2 * p ^ Nat.card (orbitRel.Quotient F (Fin n)) := by gcongr
    _ = ∏ ω, (c ω ^ 2 * p) := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
        Nat.card_eq_fintype_card]
    _ ≤ ∏ ω, p ^ c ω := Finset.prod_le_prod fun ω _ => hpow ω
    _ = p ^ n := by rw [Finset.prod_pow_eq_pow_sum, hsum]

end CFSG.HardMathSupport.Timmesfeld.LinearRank
