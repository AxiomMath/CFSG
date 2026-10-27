module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningFrobenius
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Abstract

variable {ι : Type*} {K : Type*} [Field K] [IsAlgClosed K]

theorem exists_pow_perm_eq_mul (σ : Equiv.Perm ι) {N : ℕ} (hN : 1 ≤ N) (hσ : σ ^ N = 1) {Q : ℕ}
    (hQ : 2 ≤ Q) (b : ι → Kˣ) : ∃ s : ι → Kˣ, ∀ i, s (σ i) ^ Q = b i * s i := by
  let Φ : (ι → Kˣ) →* (ι → Kˣ) :=
    { toFun := fun s i => s (σ i) ^ Q
      map_one' := by ext i; simp
      map_mul' := by intro s s'; ext i; simp [mul_pow] }
  have hΦ : ∀ (n : ℕ) (s : ι → Kˣ) (i : ι), (Φ^[n] s) i = s ((σ ^ n) i) ^ (Q ^ n) := by
    intro n
    induction n with
    | zero => intro s i; simp
    | succ n ih =>
      intro s i
      rw [Function.iterate_succ_apply', show Φ (Φ^[n] s) i = (Φ^[n] s) (σ i) ^ Q from rfl, ih,
        ← pow_mul, ← pow_succ, pow_succ σ n, Equiv.Perm.mul_apply]
  have hΦN : ∀ s : ι → Kˣ, Φ^[N] s = s ^ (Q ^ N) := by
    intro s
    ext i
    rw [hΦ, hσ]
    rfl
  have hpow : 0 < Q ^ N - 1 := by
    have : 2 ≤ Q ^ N := le_trans hQ (Nat.le_self_pow (by omega) Q)
    omega
  have hroot : ∀ u : Kˣ, ∃ z : Kˣ, z ^ (Q ^ N - 1) = u := by
    intro u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) hpow
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hpow.ne'] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose r hr using fun i => hroot (b i)
  have hrb : r ^ (Q ^ N - 1) = b := by
    funext i
    exact hr i
  set P : ι → Kˣ := ∏ j ∈ Finset.range N, Φ^[j] r with hPdef
  have hmap : Φ P = ∏ j ∈ Finset.range N, Φ^[j + 1] r := by
    rw [hPdef, map_prod]
    exact Finset.prod_congr rfl fun j _ => by rw [Function.iterate_succ_apply']
  have h1 : (∏ j ∈ Finset.range N, Φ^[j + 1] r) * Φ^[0] r = P * Φ^[N] r := by
    rw [hPdef, ← Finset.prod_range_succ' (fun j => Φ^[j] r) N, Finset.prod_range_succ]
  have h3 : Φ^[N] r = b * r := by
    rw [hΦN, ← hrb, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ Q ^ N)]
  have hP : Φ P = P * b := by
    rw [hmap]
    refine mul_right_cancel (b := r) ?_
    calc (∏ j ∈ Finset.range N, Φ^[j + 1] r) * r = P * Φ^[N] r := h1
      _ = P * (b * r) := by rw [h3]
      _ = P * b * r := by rw [mul_assoc]
  refine ⟨P, fun i => ?_⟩
  have := congrFun hP i
  rw [mul_comm (b i)]
  exact this

end Abstract

section Torus

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem frobTwistGL_diagramMap_rootDiagUnit (t : TwistTag) (e : ℕ) (s : Fin t.tag.rank → kˣ) :
    frobTwistGL t.tag k p e (diagramMap t k) (rootDiagUnit t.tag s) =
      rootDiagUnit t.tag fun i =>
        Units.map (iterateFrobenius k p e).toMonoidHom (s (t.perm.symm i)) := by
  rw [frobTwistGL_apply, entrywiseFrobGL_rootDiagUnit_eq_map, mul_inv_eq_iff_eq_mul,
    diagramMap_mul_rootDiagUnit]

theorem exists_rootDiagUnit_frob_eq [IsAlgClosed k] (t : TwistTag) {e : ℕ} (he : 1 ≤ e)
    (b : Fin t.tag.rank → kˣ) :
    ∃ s : Fin t.tag.rank → kˣ,
      frobTwistGL t.tag k p e (diagramMap t k) (rootDiagUnit t.tag s) =
        rootDiagUnit t.tag b * rootDiagUnit t.tag s := by
  have hp2 : 2 ≤ p ^ e := by
    have := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  have hσ : (t.perm.symm) ^ t.order = 1 := by cases t <;> decide
  have hN : 1 ≤ t.order := by cases t <;> decide
  obtain ⟨s, hs⟩ := exists_pow_perm_eq_mul (K := k) (t.perm.symm) hN hσ hp2 b
  refine ⟨s, ?_⟩
  rw [frobTwistGL_diagramMap_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext i
  have h := hs i
  refine Units.ext ?_
  simp only [Units.coe_map, Pi.mul_apply, Units.val_mul]
  exact congrArg Units.val h

end Torus

end CFSG.ClassicalInvolution.ModelFacts
