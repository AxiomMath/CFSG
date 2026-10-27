module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

public section

open Subgroup

namespace CFSG.ABGLocalTools

private theorem roe_exists_two_mul_sq_eq_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (h2 : (2 : K) ≠ 0) (T R : V →ₗ[K] V)
    (hT : ∀ v, T (T v) = v) (hRTR : ∀ v, R (T (R v)) = T v)
    (hR8 : ∀ v, R (R (R (R (R (R (R (R v))))))) = v)
    (hR4 : ∃ v, R (R (R (R v))) ≠ v)
    (hdim : ∀ x y, T x = -x → T y = -y → x ≠ 0 → ∃ c : K, y = c • x) :
    ∃ α : K, 2 * α ^ 2 = 1 := by
  set J : V →ₗ[K] V := R * R
  set S : V →ₗ[K] V := J * J
  have hJ : ∀ v, J v = R (R v) := fun _ => rfl
  have hS : ∀ v, S v = J (J v) := fun _ => rfl
  have hS2 : ∀ v, S (S v) = v := hR8
  have hRS : ∀ v, R (S v) = S (R v) := fun _ => rfl
  have hRJ : ∀ v, R (J v) = J (R v) := fun _ => rfl
  have hJS : ∀ v, J (S v) = S (J v) := fun _ => rfl
  have hJTJ : ∀ v, J (T (J v)) = T v := fun v => by rw [hJ, hJ, hRTR, hRTR]
  have hSTS : ∀ v, S (T (S v)) = T v := fun v => by rw [hS, hS, hJTJ, hJTJ]
  have hTS : ∀ v, T (S v) = S (T v) := fun v => by
    have := hSTS (S v)
    rw [hS2] at this
    exact this.symm
  have hTJ : ∀ v, T (J v) = J (T (S v)) := fun v => (hJTJ (J v)).symm
  have hJinj : ∀ v, J v = 0 → v = 0 := fun v h => by
    have : S (S v) = 0 := by rw [hS, hS, hJ, h]; simp
    rwa [hS2] at this
  obtain ⟨v₀, hv₀⟩ := hR4
  set u := v₀ - S v₀ with hu
  have hSu : S u = -u := by rw [hu, map_sub, hS2, neg_sub]
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hv₀)
  obtain ⟨e, he0, hTe, hSe⟩ : ∃ e, e ≠ 0 ∧ T e = e ∧ S e = -e := by
    by_cases h : u + T u = 0
    · have hTu : T u = -u := eq_neg_of_add_eq_zero_right h
      refine ⟨J u, fun h0 => hu0 (hJinj u h0), ?_, ?_⟩
      · rw [hTJ, hSu, map_neg, hTu, neg_neg]
      · rw [← hJS, hSu, map_neg]
    · refine ⟨u + T u, h, ?_, ?_⟩
      · rw [map_add, hT, add_comm]
      · rw [map_add, hSu, ← hTS, hSu, map_neg, neg_add]
  set f := J e with hf
  have hTf : T f = -f := by rw [hf, hTJ, hSe, map_neg, hTe, map_neg]
  have hJf : J f = -e := hSe
  have hf0 : f ≠ 0 := fun h0 => he0 (by rw [← neg_eq_zero, ← hJf, h0, map_zero])
  obtain ⟨b, hb⟩ := hdim f (R e - T (R e)) hTf (by rw [map_sub, hT, neg_sub]) hf0
  have hSRe : S (R e) = -R e := by rw [← hRS, hSe, map_neg]
  have hTJp : T (J (R e + T (R e))) = -J (R e + T (R e)) := by
    rw [hTJ, map_add, hSRe, ← hTS, hSRe, map_neg, ← neg_add, map_neg, map_neg, map_add,
      hT, add_comm (T (R e))]
  obtain ⟨a, ha⟩ := hdim f (J (R e + T (R e))) hTf hTJp hf0
  have ha' : R e + T (R e) = a • e := by
    have : J (R e + T (R e) - a • e) = 0 := by rw [map_sub, ha, map_smul, sub_self]
    exact sub_eq_zero.mp (hJinj _ this)
  obtain ⟨α, β, hRe⟩ : ∃ α β : K, R e = α • e + β • f := by
    refine ⟨2⁻¹ * a, 2⁻¹ * b, ?_⟩
    have h2' : (2 : K) • R e = a • e + b • f := by
      rw [two_smul, ← ha', ← hb]; abel
    rw [mul_smul, mul_smul, ← smul_add, ← h2', smul_smul, inv_mul_cancel₀ h2, one_smul]
  have hRf : R f = α • f - β • e := by
    rw [hf, hRJ, hRe, map_add, map_smul, map_smul, ← hf, hJf]
    module
  have h1 : (α ^ 2 - β ^ 2) • e + (2 * α * β - 1) • f = 0 := by
    have h : R (R e) = f := rfl
    rw [hRe, map_add, map_smul, map_smul, hRe, hRf] at h
    linear_combination (norm := module) h
  have h1T := congrArg T h1
  rw [map_add, map_smul, map_smul, hTe, hTf, map_zero] at h1T
  have hA : (2 * (α ^ 2 - β ^ 2)) • e = 0 := by
    linear_combination (norm := module) h1 + h1T
  have hA' : α ^ 2 - β ^ 2 = 0 :=
    (mul_eq_zero.mp ((smul_eq_zero.mp hA).resolve_right he0)).resolve_left h2
  have h3 : (α ^ 2 + β ^ 2 - 1) • e = 0 := by
    have h := hRTR e
    rw [hRe, map_add, map_smul, map_smul, hTe, hTf, smul_neg, ← sub_eq_add_neg, map_sub,
      map_smul, map_smul, hRe, hRf] at h
    linear_combination (norm := module) h
  have h3' : α ^ 2 + β ^ 2 - 1 = 0 := (smul_eq_zero.mp h3).resolve_right he0
  exact ⟨α, by linear_combination h3' + hA'⟩

private theorem roe_eq_of_inv_mul_mem_centralizer {G : Type*} [Group G] {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {t a b : G} (ha : a ^ r = 1) (hb : b ^ r = 1)
    (hta : t * a * t⁻¹ = a⁻¹) (htb : t * b * t⁻¹ = b⁻¹)
    (hab : a⁻¹ * b ∈ centralizer {t}) : a = b := by
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hz : t * (a⁻¹ * b) = a⁻¹ * b * t := mem_centralizer_iff.mp hab t rfl
  have h1 : a * b⁻¹ = a⁻¹ * b := by
    calc a * b⁻¹ = (t * a * t⁻¹)⁻¹ * (t * b * t⁻¹) := by rw [hta, htb, inv_inv]
      _ = t * (a⁻¹ * b) * t⁻¹ := by group
      _ = a⁻¹ * b := by rw [hz]; group
  have h2 : a ^ 2 = b ^ 2 := by
    calc a ^ 2 = a * (a * b⁻¹) * b := by rw [sq]; group
      _ = a * (a⁻¹ * b) * b := by rw [h1]
      _ = b ^ 2 := by rw [sq]; group
  have key : ∀ c : G, c ^ r = 1 → c = ((c ^ 2) ^ k)⁻¹ := fun c hc => by
    rw [eq_inv_iff_mul_eq_one, ← pow_mul, ← pow_succ', ← hk, hc]
  rw [key a ha, key b hb, h2]

private theorem roe_exists_pow_eq_of_inverted {G : Type*} [Group G] [Finite G] {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {W : Subgroup G} (hWr : ∀ w ∈ W, w ^ r = 1) {t : G}
    (hrefl : (W ⊓ centralizer {t}).relIndex W = r) {x y : G} (hx : x ∈ W) (hy : y ∈ W)
    (htx : t * x * t⁻¹ = x⁻¹) (hty : t * y * t⁻¹ = y⁻¹) (hx1 : x ≠ 1) :
    ∃ n : ℕ, y = x ^ n := by
  have : Fact r.Prime := ⟨hr⟩
  have hxo : orderOf x = r := orderOf_eq_prime (hWr x hx) hx1
  have htxn : ∀ n : ℕ, t * x ^ n * t⁻¹ = (x ^ n)⁻¹ := fun n => by
    rw [← conj_pow, htx, inv_pow]
  set H := (W ⊓ centralizer {t}).subgroupOf W with hH
  have hcard : Nat.card (W ⧸ H) = r := hrefl
  let F : Fin r → W ⧸ H := fun i => ((⟨x, hx⟩ : W) ^ (i : ℕ) : W)
  have hmem : ∀ a b : W, (a : W ⧸ H) = b → (a : G)⁻¹ * b ∈ centralizer {t} := by
    intro a b h
    have := QuotientGroup.eq.mp h
    rw [hH, mem_subgroupOf] at this
    simpa using this.2
  have hF : Function.Injective F := by
    intro i j hij
    have h := hmem _ _ hij
    simp only [SubgroupClass.coe_pow] at h
    have := roe_eq_of_inv_mul_mem_centralizer hr hr2 (hWr _ (W.pow_mem hx _))
      (hWr _ (W.pow_mem hx _)) (htxn i) (htxn j) h
    exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hxo]; exact i.2) (by rw [hxo]; exact j.2) this)
  have hFs : Function.Surjective F :=
    (hF.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])).2
  obtain ⟨i, hi⟩ := hFs ((⟨y, hy⟩ : W) : W ⧸ H)
  have h := hmem _ _ hi
  simp only [SubgroupClass.coe_pow] at h
  exact ⟨i, (roe_eq_of_inv_mul_mem_centralizer hr hr2 (hWr _ (W.pow_mem hx _)) (hWr y hy)
    (htxn i) hty h).symm⟩

private def roeConj {G : Type*} [Group G] (W : Subgroup G) (g : G)
    (hg : g ∈ normalizer (W : Set G)) : W →* W where
  toFun w := ⟨g * w * g⁻¹, (mem_normalizer_iff.mp hg w).mp w.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem exists_two_mul_sq_eq_one_of_reflection {G : Type*} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {W : Subgroup G}
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hWr : ∀ w ∈ W, w ^ r = 1) {t ρ : G}
    (ht : t ∈ Subgroup.normalizer (W : Set G)) (hρ : ρ ∈ Subgroup.normalizer (W : Set G))
    (ht2 : t * t = 1) (hrefl : (W ⊓ Subgroup.centralizer {t}).relIndex W = r)
    (hinv : t * ρ * t⁻¹ * ρ ∈ Subgroup.centralizer (W : Set G))
    (h8 : ρ ^ 8 ∈ Subgroup.centralizer (W : Set G))
    (h4 : ρ ^ 4 ∉ Subgroup.centralizer (W : Set G)) :
    ∃ α : ZMod r, 2 * α ^ 2 = 1 := by
  have : Fact r.Prime := ⟨hr⟩
  let _ : CommGroup W := CommGroup.mk (fun a b => Subtype.ext (hWab a a.2 b b.2))
  have _ : Module (ZMod r) (Additive W) := AddCommGroup.zmodModule (n := r) fun x =>
    Additive.ext (Subtype.ext (by simpa using hWr _ (Additive.toMul x).2))
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp (by exact_mod_cast h)
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let T := (MonoidHom.toAdditive (roeConj W t ht)).toZModLinearMap r
  let R := (MonoidHom.toAdditive (roeConj W ρ hρ)).toZModLinearMap r
  have hTv : ∀ v, ((Additive.toMul (T v) : W) : G) = t * (Additive.toMul v : W) * t⁻¹ :=
    fun _ => rfl
  have hRv : ∀ v, ((Additive.toMul (R v) : W) : G) = ρ * (Additive.toMul v : W) * ρ⁻¹ :=
    fun _ => rfl
  have hext : ∀ v w : Additive W, ((Additive.toMul v : W) : G) = (Additive.toMul w : W) →
      v = w := fun v w h => Additive.ext (Subtype.ext h)
  refine roe_exists_two_mul_sq_eq_one h2 T R ?_ ?_ ?_ ?_ ?_
  · intro v
    apply hext
    rw [hTv, hTv, htinv]
    set x := ((Additive.toMul v : W) : G)
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by simp only [mul_assoc]
      _ = x := by rw [ht2, one_mul, mul_one]
  · intro v
    apply hext
    rw [hRv, hTv, hRv, hTv]
    set x := ((Additive.toMul v : W) : G)
    have hc : x * (t⁻¹ * ρ * t * ρ) = (t⁻¹ * ρ * t * ρ) * x := by
      have := mem_centralizer_iff.mp hinv x (Additive.toMul v).2
      rw [htinv] at this
      rw [htinv]
      exact this
    calc ρ * (t * (ρ * x * ρ⁻¹) * t⁻¹) * ρ⁻¹
        = t * ((t⁻¹ * ρ * t * ρ) * x) * (t⁻¹ * ρ * t * ρ)⁻¹ * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * ρ * t * ρ)) * (t⁻¹ * ρ * t * ρ)⁻¹ * t⁻¹ := by rw [hc]
      _ = t * x * t⁻¹ := by group
  · intro v
    apply hext
    simp only [hRv]
    set x := ((Additive.toMul v : W) : G)
    have hc : x * ρ ^ 8 = ρ ^ 8 * x := mem_centralizer_iff.mp h8 x (Additive.toMul v).2
    calc _ = ρ ^ 8 * x * (ρ ^ 8)⁻¹ := by
          simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      _ = x := by rw [← hc, mul_inv_cancel_right]
  · simp only [mem_centralizer_iff, not_forall] at h4
    obtain ⟨w, hw, hw4⟩ := h4
    refine ⟨Additive.ofMul ⟨w, hw⟩, fun h => hw4 ?_⟩
    have h' : ρ ^ 4 * w * (ρ ^ 4)⁻¹ = w := by
      have := congrArg (fun v : Additive W => ((Additive.toMul v : W) : G)) h
      simp only [hRv, toMul_ofMul] at this
      refine Eq.trans ?_ this
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    calc w * ρ ^ 4 = ρ ^ 4 * w * (ρ ^ 4)⁻¹ * ρ ^ 4 := by rw [h']
      _ = ρ ^ 4 * w := inv_mul_cancel_right _ _
  · intro x y hx hy hx0
    have hx' : t * (Additive.toMul x : W) * t⁻¹ = ((Additive.toMul x : W) : G)⁻¹ := by
      rw [← hTv, hx]; rfl
    have hy' : t * (Additive.toMul y : W) * t⁻¹ = ((Additive.toMul y : W) : G)⁻¹ := by
      rw [← hTv, hy]; rfl
    have hx1 : ((Additive.toMul x : W) : G) ≠ 1 := fun h => hx0 (by
      apply hext; rw [h]; rfl)
    obtain ⟨n, hn⟩ := roe_exists_pow_eq_of_inverted hr hr2 hWr hrefl (Additive.toMul x).2
      (Additive.toMul y).2 hx' hy' hx1
    refine ⟨n, ?_⟩
    rw [Nat.cast_smul_eq_nsmul]
    apply hext
    rw [hn]
    rfl

end CFSG.ABGLocalTools
