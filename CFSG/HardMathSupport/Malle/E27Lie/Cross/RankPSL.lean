module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Polynomial CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Timmesfeld.LinearRank

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem card_le_of_statedProj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    (hpK : p ∣ Nat.card Fˣ) {H : Subgroup (GL (Fin n) F)} (E : Subgroup (StatedProj H))
    (hE : CFSG.Open.IsElemAbelian p E) : Nat.card E ≤ p ^ (n - 1) := by
  refine card_le_of_scalar_kernel hp hp2 hpK hn H
    (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf H)) ?_ E ?_ hE
  · intro A
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  · rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _)]
    exact le_top

theorem irreducible_X_sq_add_X_add_one_of_not_dvd (h3 : ((3 : ℕ) : F) ≠ 0)
    (hd : ¬ 3 ∣ Nat.card Fˣ) : Irreducible (X ^ 2 + X + 1 : F[X]) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ fun x hx => ?_
  · rw [Finset.mem_Icc]
    have : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
    omega
  · simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hx
    have hx3 : x ^ 3 = 1 := by linear_combination (x - 1) * hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply h3
      have : (1 : F) ^ 2 + 1 + 1 = 0 := hx
      rw [show ((3 : ℕ) : F) = 1 + 1 + 1 by norm_num]
      simpa using this
    let u : Fˣ := Units.mk0 x hx0
    have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hx3)
    have hu1 : u ≠ 1 := fun h => hx1 (by simpa [u] using congrArg Units.val h)
    exact hd (by rw [← orderOf_eq_prime hu3 hu1]; exact orderOf_dvd_natCard u)

theorem card_le_of_statedProj_SL (h3 : ((3 : ℕ) : F) ≠ 0) (hn : 0 < n)
    (E : Subgroup (StatedProj (StatedSL n F))) (hE : CFSG.Open.IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ (n - 1) := by
  by_cases hd : 3 ∣ Nat.card Fˣ
  · exact card_le_of_statedProj Nat.prime_three (by norm_num) hn hd E hE
  have hirr := irreducible_X_sq_add_X_add_one_of_not_dvd h3 hd
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : F[X])) := ⟨hirr⟩
  let F' := AdjoinRoot (X ^ 2 + X + 1 : F[X])
  haveI : Module.Finite F F' := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Finite F' := Module.finite_of_finite F
  let ι : GL (Fin n) F →* GL (Fin n) F' := Matrix.GeneralLinearGroup.map (algebraMap F F')
  have hinj : Function.Injective ι := by
    intro A B h
    apply Units.ext
    have := congrArg (fun C : GL (Fin n) F' => (C : Matrix (Fin n) (Fin n) F')) h
    exact Matrix.map_injective (algebraMap F F').injective this
  let U : Subgroup (GL (Fin n) F') := (StatedSL n F).map ι
  let φ : ↥(StatedSL n F) ≃* ↥U := Subgroup.equivMapOfInjective (StatedSL n F) ι hinj
  let ρ : U →* StatedProj (StatedSL n F) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) F).subgroupOf (StatedSL n F))).comp
      φ.symm.toMonoidHom
  have hroot : (AdjoinRoot.root (X ^ 2 + X + 1 : F[X])) ^ 2 + AdjoinRoot.root (X ^ 2 + X + 1 : F[X])
      + 1 = 0 := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 + X + 1 : F[X])
    simpa only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] using h
  have hpK : 3 ∣ Nat.card F'ˣ := by
    set r : F' := AdjoinRoot.root (X ^ 2 + X + 1 : F[X])
    have hr3 : r ^ 3 = 1 := by linear_combination (r - 1) * hroot
    have hr0 : r ≠ 0 := by
      rintro h0
      rw [h0] at hr3
      simp at hr3
    have hr1 : r ≠ 1 := by
      intro h1
      rw [h1] at hroot
      have h30 : ((3 : ℕ) : F') = 0 := by
        push_cast
        linear_combination hroot
      exact h3 ((algebraMap F F').injective (by rw [map_zero, map_natCast]; exact h30))
    let u : F'ˣ := Units.mk0 r hr0
    have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hr3)
    have hu1 : u ≠ 1 := fun h => hr1 (by simpa [u] using congrArg Units.val h)
    rw [← orderOf_eq_prime hu3 hu1]
    exact orderOf_dvd_natCard u
  refine card_le_of_scalar_kernel Nat.prime_three (by norm_num) hpK hn U ρ ?_ E ?_ hE
  · intro A
    have hB : (A : GL (Fin n) F') = ι (φ.symm A : StatedSL n F) := by
      calc (A : GL (Fin n) F') = ((φ (φ.symm A) : U) : GL (Fin n) F') := by
            rw [φ.apply_symm_apply]
        _ = ι (φ.symm A : StatedSL n F) :=
            Subgroup.coe_equivMapOfInjective_apply (StatedSL n F) ι hinj _
    simp only [ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [hB, StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    set B : StatedSL n F := φ.symm A
    constructor
    · intro hc
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc ⊢
      obtain ⟨c, hc⟩ := hc
      refine ⟨Units.map (algebraMap F F') c, ?_⟩
      rw [← Matrix.GeneralLinearGroup.map_scalar, hc]
    · intro hc
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro g
      apply hinj
      rw [map_mul, map_mul]
      exact hc (ι g)
  · have : ρ.range = ⊤ := by
      refine MonoidHom.range_eq_top.2 ?_
      exact (QuotientGroup.mk'_surjective _).comp φ.symm.surjective
    rw [this]
    exact le_top

end CFSG.HardMathSupport.Malle.E27Lie
