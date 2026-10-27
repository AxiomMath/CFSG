module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

public noncomputable section

namespace CFSG.StandardType.ExcFramesHalf

open scoped Matrix

theorem vecMulVec_mulVec_eq_dotProduct_smul {r : ℕ} (u c x : Fin r → ℤ) :
    (Matrix.vecMulVec u c) *ᵥ x = (c ⬝ᵥ x) • u := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_vecMulVec_of_rank_rat_le_one {r : ℕ} (T : Matrix (Fin r) (Fin r) ℤ)
    (hT : T ≠ 0) (hrank : (T.map (Int.castRingHom ℚ)).rank ≤ 1) :
    ∃ u c : Fin r → ℤ, u ≠ 0 ∧ c ≠ 0 ∧
      (∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1) ∧
      T = Matrix.vecMulVec u c := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, T.col j ≠ 0 := by
    by_contra h
    push Not at h
    exact hT (by ext i j; simpa using congrFun (h j) i)
  let v : Fin r → ℤ := T.col j₀
  have hv : v ≠ 0 := hj₀
  obtain ⟨u, huv, hugcd⟩ := Finset.extract_gcd (s := Finset.univ) v ⟨j₀, Finset.mem_univ j₀⟩
  let G : ℤ := Finset.univ.gcd v
  have hG : G ≠ 0 := by
    intro h0
    exact hv (funext fun j => (Finset.gcd_eq_zero_iff.mp h0) j (Finset.mem_univ j))
  have hu : u ≠ 0 := by
    intro h
    apply hv
    funext j
    rw [huv j (Finset.mem_univ j), h]
    simp
  have hprim : ∀ d : ℤ, (∀ j, d ∣ u j) → d = 1 ∨ d = -1 := by
    intro d hd
    have h1 : d ∣ (1 : ℤ) := by
      have h := Finset.dvd_gcd (s := Finset.univ) (f := u) (fun j _ => hd j)
      rwa [hugcd] at h
    exact Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr h1)
  let TQ : Matrix (Fin r) (Fin r) ℚ := T.map (Int.castRingHom ℚ)
  let W : Submodule ℚ (Fin r → ℚ) := Submodule.span ℚ (Set.range TQ.col)
  have hWle : Module.finrank ℚ W ≤ 1 := by
    rw [show Module.finrank ℚ W = TQ.rank from (Matrix.rank_eq_finrank_span_cols TQ).symm]
    exact hrank
  obtain ⟨v₀, hv₀⟩ := finrank_le_one_iff.mp hWle
  let w₀ : W := ⟨TQ.col j₀, Submodule.subset_span ⟨j₀, rfl⟩⟩
  have hw₀_ne : w₀ ≠ 0 := by
    intro h
    have hval : TQ.col j₀ = 0 := congrArg Subtype.val h
    apply hv
    funext a
    have hthis := congrFun hval a
    change (v a : ℚ) = 0 at hthis
    exact_mod_cast hthis
  obtain ⟨a, ha⟩ := hv₀ w₀
  have ha_ne : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_smul] at ha
    exact hw₀_ne ha.symm
  have hcol : ∀ k, ∃ q : ℚ, TQ.col k = q • TQ.col j₀ := by
    intro k
    let wk : W := ⟨TQ.col k, Submodule.subset_span ⟨k, rfl⟩⟩
    obtain ⟨b, hb⟩ := hv₀ wk
    refine ⟨b * a⁻¹, ?_⟩
    have hbval : b • (v₀ : Fin r → ℚ) = TQ.col k := congrArg Subtype.val hb
    have haval : a • (v₀ : Fin r → ℚ) = TQ.col j₀ := congrArg Subtype.val ha
    have hv0 : (v₀ : Fin r → ℚ) = a⁻¹ • TQ.col j₀ := by
      rw [← haval]
      exact (inv_smul_smul₀ ha_ne (v₀ : Fin r → ℚ)).symm
    rw [← hbval, hv0, smul_smul]
  choose q hq using hcol
  let uQ : Fin r → ℚ := fun a => (u a : ℚ)
  have huvQ : TQ.col j₀ = (G : ℚ) • uQ := by
    funext a
    change (v a : ℚ) = (G : ℚ) * (u a : ℚ)
    rw [huv a (Finset.mem_univ a)]
    push_cast
    ring
  have hcolQ : ∀ k, TQ.col k = (q k * (G : ℚ)) • uQ := by
    intro k
    rw [hq k, huvQ, smul_smul]
  have hcolQ_comp : ∀ k a, (T a k : ℚ) = (q k * (G : ℚ)) * (u a : ℚ) := by
    intro k a
    have h := congrFun (hcolQ k) a
    change (T a k : ℚ) = (q k * (G : ℚ)) * (u a : ℚ) at h
    exact h
  obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin r)) u
  have hg1 : ∑ a : Fin r, u a * g a = 1 := by
    have h1 : ∑ a ∈ Finset.univ, u a * g a = 1 := by rw [← hg, hugcd]
    simpa using h1
  let c : Fin r → ℤ := fun k => ∑ a, T a k * g a
  have hcQ : ∀ k, ((c k : ℤ) : ℚ) = q k * (G : ℚ) := by
    intro k
    have hsum1 : ((∑ a, T a k * g a : ℤ) : ℚ) =
        (q k * (G : ℚ)) * ((∑ a, u a * g a : ℤ) : ℚ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hcolQ_comp k a]
      ring
    change ((∑ a, T a k * g a : ℤ) : ℚ) = q k * (G : ℚ)
    rw [hsum1, hg1]
    ring
  have hTcol : ∀ k, T.col k = c k • u := by
    intro k
    funext a
    show T a k = c k * u a
    have hq_eq : ((T a k : ℤ) : ℚ) = ((c k * u a : ℤ) : ℚ) := by
      push_cast
      rw [hcolQ_comp k a, hcQ k]
    exact_mod_cast hq_eq
  refine ⟨u, c, hu, ?_, hprim, ?_⟩
  · intro hc0
    apply hT
    ext i j
    have h1 := congrFun (hTcol j) i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h1
    have hcj : c j = 0 := by simp [hc0]
    rw [h1, hcj, zero_mul]
    rfl
  · ext i j
    have h1 := congrFun (hTcol j) i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1]
    simp [Matrix.vecMulVec_apply, mul_comm]

end CFSG.StandardType.ExcFramesHalf
