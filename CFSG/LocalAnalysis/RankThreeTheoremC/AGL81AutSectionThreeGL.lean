module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionThreeDefs
public import Mathlib.LinearAlgebra.Quotient.Basic
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTorus
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamTransfer
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionAutomizer
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree

open Module Polynomial
open scoped commutatorElement


variable {F W : Type} [Field F] [Finite F] [AddCommGroup W] [Module F W] [Module.Finite F W]

section Restrict

variable {S : Subgroup (Module.End F W)ˣ} {U : Submodule F W}
variable (hUinv : ∀ g ∈ S, ∀ w ∈ U, ((g : Module.End F W) w) ∈ U)

noncomputable def restrictUnit (g : S) : (Module.End F U)ˣ where
  val := LinearMap.restrict ((g : (Module.End F W)ˣ) : Module.End F W) (hUinv g g.2)
  inv := LinearMap.restrict (((g⁻¹ : S) : (Module.End F W)ˣ) : Module.End F W)
    (hUinv g⁻¹ (S.inv_mem g.2))
  val_inv := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.restrict_apply]
    exact congrArg (fun f : Module.End F W => f (x : W)) (Units.mul_inv ((g : (Module.End F W)ˣ)))
  inv_val := by
    ext x
    simp only [Module.End.mul_apply, LinearMap.restrict_apply]
    exact congrArg (fun f : Module.End F W => f (x : W)) (Units.inv_mul ((g : (Module.End F W)ˣ)))

noncomputable def restrictHom : S →* (Module.End F U)ˣ where
  toFun := restrictUnit hUinv
  map_one' := by
    ext x
    simp [restrictUnit]
  map_mul' := by
    intro a b
    ext x
    simp [restrictUnit, Module.End.mul_apply]

noncomputable def quotientUnit (g : S) : (Module.End F (W ⧸ U))ˣ where
  val := U.mapQ U ((g : (Module.End F W)ˣ) : Module.End F W) (hUinv g g.2)
  inv := U.mapQ U (((g⁻¹ : S) : (Module.End F W)ˣ) : Module.End F W) (hUinv g⁻¹ (S.inv_mem g.2))
  val_inv := by
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    refine Submodule.Quotient.induction_on (p := U) x ?_
    intro y
    have h : ((g : (Module.End F W)ˣ) : Module.End F W) *
        (((g⁻¹ : ↥S) : (Module.End F W)ˣ) : Module.End F W) = 1 := by
      simpa [Subgroup.coe_inv] using congrArg (fun u : (Module.End F W)ˣ =>
        (u : Module.End F W)) (Units.mul_inv ((g : (Module.End F W)ˣ)))
    simp only [Submodule.mapQ_apply]
    change Submodule.Quotient.mk ((((g : (Module.End F W)ˣ) : Module.End F W) *
      (((g⁻¹ : ↥S) : (Module.End F W)ˣ) : Module.End F W)) y) = Submodule.Quotient.mk y
    rw [h, Module.End.one_apply]
  inv_val := by
    apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    refine Submodule.Quotient.induction_on (p := U) x ?_
    intro y
    have h : (((g⁻¹ : ↥S) : (Module.End F W)ˣ) : Module.End F W) *
        ((g : (Module.End F W)ˣ) : Module.End F W) = 1 := by
      simpa [Subgroup.coe_inv] using congrArg (fun u : (Module.End F W)ˣ =>
        (u : Module.End F W)) (Units.inv_mul ((g : (Module.End F W)ˣ)))
    simp only [Submodule.mapQ_apply]
    change Submodule.Quotient.mk (((((g⁻¹ : ↥S) : (Module.End F W)ˣ) : Module.End F W) *
      ((g : (Module.End F W)ˣ) : Module.End F W)) y) = Submodule.Quotient.mk y
    rw [h, Module.End.one_apply]

noncomputable def quotientHom : S →* (Module.End F (W ⧸ U))ˣ where
  toFun := quotientUnit hUinv
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := U) x ?_
    intro y
    simp [quotientUnit, Submodule.mapQ_apply]
  map_mul' := by
    intro a b
    apply Units.ext
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := U) x ?_
    intro y
    simp [quotientUnit, Submodule.mapQ_apply, Module.End.mul_apply]

end Restrict

private theorem isMulCommutative_range_restrict
    {S : Subgroup (Module.End F W)ˣ} {U : Submodule F W} (hS : IsPGroup 3 S)
    (h3card : ¬ 3 ∣ Nat.card F)
    (hUinv : ∀ g ∈ S, ∀ w ∈ U, ((g : Module.End F W) w) ∈ U)
    (hU : Module.finrank F U < 3) :
    IsMulCommutative (restrictHom hUinv).range := by
  obtain ⟨e, he, hpe⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_order_data
    (K := F) (p := 3) h3card
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup_GL
    (K := F) (V := U) (p := 3) (e := e) (by norm_num) h3card he hpe
    (by calc Module.finrank F U / e ≤ Module.finrank F U := Nat.div_le_self _ _
          _ < 3 := hU)
    (IsPGroup.of_surjective hS (restrictHom hUinv).rangeRestrict
      (restrictHom hUinv).rangeRestrict_surjective)

private theorem isMulCommutative_range_quotient
    {S : Subgroup (Module.End F W)ˣ} {U : Submodule F W} (hS : IsPGroup 3 S)
    (h3card : ¬ 3 ∣ Nat.card F)
    (hUinv : ∀ g ∈ S, ∀ w ∈ U, ((g : Module.End F W) w) ∈ U)
    (hQ : Module.finrank F (W ⧸ U) < 3) :
    IsMulCommutative (quotientHom hUinv).range := by
  obtain ⟨e, he, hpe⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_order_data
    (K := F) (p := 3) h3card
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup_GL
    (K := F) (V := W ⧸ U) (p := 3) (e := e) (by norm_num) h3card he hpe
    (by calc Module.finrank F (W ⧸ U) / e ≤ Module.finrank F (W ⧸ U) := Nat.div_le_self _ _
          _ < 3 := hQ)
    (IsPGroup.of_surjective hS (quotientHom hUinv).rangeRestrict
      (quotientHom hUinv).rangeRestrict_surjective)

private theorem eq_one_of_fixes_invariant
    {S : Subgroup (Module.End F W)ˣ} {U : Submodule F W} (h3F : (3 : F) ≠ 0)
    (hexp : ∀ x ∈ S, x ^ 3 = 1) {c : ↥S}
    (hfixU : ∀ w ∈ U, (((c : (Module.End F W)ˣ) : Module.End F W) w = w))
    (hfixQ : ∀ w : W, (((c : (Module.End F W)ˣ) : Module.End F W) w - w) ∈ U) :
    c = 1 := by
  have hc3 : (((c : (Module.End F W)ˣ) : Module.End F W)) ^ 3 = 1 :=
    congrArg Units.val (hexp (c : (Module.End F W)ˣ) c.2)
  set n : Module.End F W := (((c : (Module.End F W)ˣ) : Module.End F W)) - 1 with hn
  have hn2 : n * n = 0 := by
    apply LinearMap.ext
    intro w
    rw [Module.End.mul_apply]
    have h1 : n w ∈ U := by
      simpa [hn, LinearMap.sub_apply] using hfixQ w
    have h2 : ∀ u ∈ U, n u = 0 := by
      intro u hu
      simp [hn, hfixU u hu]
    exact h2 _ h1
  have hc1 : (((c : (Module.End F W)ˣ) : Module.End F W)) = 1 := by
    have h1 : (1 : Module.End F W) + n = ((c : (Module.End F W)ˣ) : Module.End F W) := by
      rw [hn]; abel
    have h3 : (1 + n) ^ 3 = 1 := by rw [h1, hc3]
    have hn2' : n ^ 2 = 0 := by rw [pow_two]; exact hn2
    have hn3 : n ^ 3 = 0 := by rw [pow_succ, hn2', zero_mul]
    have h3n : (3 : F) • n = 0 := by
      have h : 1 + (3 : F) • n = 1 := by
        calc 1 + (3 : F) • n = (1 + n) ^ 3 := by
              rw [show (1 + n) ^ 3 = 1 + (3 : F) • n by
                calc (1 + n) ^ 3 = 1 + 3 * n + 3 * n ^ 2 + n ^ 3 := by noncomm_ring
                  _ = 1 + 3 * n := by simp [hn2', hn3]
                  _ = 1 + (3 : F) • n := by
                        rw [Algebra.smul_def]
                        have h3map : (algebraMap F (Module.End F W)) (3 : F) = 3 := by
                          rw [show (3 : F) = ((3 : ℕ) : F) from rfl]
                          exact map_natCast _ 3
                        rw [h3map]]
          _ = 1 := h3
      simpa using h
    have hn0 : n = 0 := by
      rcases smul_eq_zero.mp h3n with h | h
      · exact absurd h h3F
      · exact h
    rw [← h1, hn0, add_zero]
  exact Subtype.ext (Units.ext hc1)

private theorem commutator_fixes_invariant
    {S : Subgroup (Module.End F W)ˣ} {U : Submodule F W} (hS : IsPGroup 3 S)
    (h3card : ¬ 3 ∣ Nat.card F)
    (hUinv : ∀ g ∈ S, ∀ w ∈ U, ((g : Module.End F W) w) ∈ U)
    (hU : Module.finrank F U < 3) (hQ : Module.finrank F (W ⧸ U) < 3) (a b : ↥S) :
    (∀ w ∈ U, (((((⁅a, b⁆ : ↥S) : (Module.End F W)ˣ)) : Module.End F W) w = w)) ∧
      (∀ w : W, (((((⁅a, b⁆ : ↥S) : (Module.End F W)ˣ)) : Module.End F W) w - w) ∈ U) := by
  have hUab := isMulCommutative_range_restrict hS h3card hUinv hU
  have hQab := isMulCommutative_range_quotient hS h3card hUinv hQ
  have hcommU : ∀ x y : ↥S, (restrictHom hUinv) x * (restrictHom hUinv) y =
      (restrictHom hUinv) y * (restrictHom hUinv) x := by
    intro x y
    exact congrArg Subtype.val (isMulCommutative_iff.mp hUab
      ⟨(restrictHom hUinv) x, ⟨x, rfl⟩⟩ ⟨(restrictHom hUinv) y, ⟨y, rfl⟩⟩)
  have hcommQ : ∀ x y : ↥S, (quotientHom hUinv) x * (quotientHom hUinv) y =
      (quotientHom hUinv) y * (quotientHom hUinv) x := by
    intro x y
    exact congrArg Subtype.val (isMulCommutative_iff.mp hQab
      ⟨(quotientHom hUinv) x, ⟨x, rfl⟩⟩ ⟨(quotientHom hUinv) y, ⟨y, rfl⟩⟩)
  have hcU : (restrictHom hUinv) ⁅a, b⁆ = 1 := by
    have hmap : (restrictHom hUinv) ⁅a, b⁆ =
        ⁅(restrictHom hUinv) a, (restrictHom hUinv) b⁆ := by
      simp [commutatorElement_def]
    rw [hmap]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcommU a b)
  have hcQ : (quotientHom hUinv) ⁅a, b⁆ = 1 := by
    have hmap : (quotientHom hUinv) ⁅a, b⁆ =
        ⁅(quotientHom hUinv) a, (quotientHom hUinv) b⁆ := by
      simp [commutatorElement_def]
    rw [hmap]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcommQ a b)
  constructor
  · intro w hw
    have h2 := congrArg (fun f : Module.End F U => f ⟨w, hw⟩) (congrArg Units.val hcU)
    change ((restrictUnit hUinv ⁅a, b⁆).val ⟨w, hw⟩) =
      (1 : Module.End F U) ⟨w, hw⟩ at h2
    change (((⁅a, b⁆ : ↥S) : (Module.End F W)ˣ) : Module.End F W) w = w
    simpa [restrictUnit, LinearMap.restrict_apply] using h2
  · intro w
    have h := congrArg (fun f : Module.End F (W ⧸ U) => f (Submodule.Quotient.mk w))
      (congrArg Units.val hcQ)
    change (quotientUnit hUinv (⁅a, b⁆ : ↥S)).val (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk w at h
    change (U.mapQ U (((⁅a, b⁆ : ↥S) : (Module.End F W)ˣ) : Module.End F W)
      (hUinv ((⁅a, b⁆ : ↥S) : (Module.End F W)ˣ) (⁅a, b⁆ : ↥S).2)) (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk w at h
    rw [Submodule.mapQ_apply] at h
    exact (Submodule.Quotient.eq U).mp h

theorem isMulCommutative_of_invariant_submodule
    {S : Subgroup (Module.End F W)ˣ} (hS : IsPGroup 3 S)
    (hexp : ∀ x ∈ S, x ^ 3 = 1)
    (h3F : (3 : F) ≠ 0) (h3card : ¬ 3 ∣ Nat.card F)
    (U : Submodule F W) (hU0 : U ≠ ⊥) (hUt : U ≠ ⊤)
    (hUinv : ∀ g ∈ S, ∀ w ∈ U, ((g : Module.End F W) w) ∈ U)
    (hU : Module.finrank F U < 3) (hQ : Module.finrank F (W ⧸ U) < 3) :
    IsMulCommutative S := by
  refine isMulCommutative_iff.mpr fun a b => ?_
  obtain ⟨hfixU, hfixQ⟩ := commutator_fixes_invariant hS h3card hUinv hU hQ a b
  have hc1 : (⁅a, b⁆ : ↥S) = 1 :=
    eq_one_of_fixes_invariant h3F hexp hfixU hfixQ
  exact commutatorElement_eq_one_iff_mul_comm.mp (by
    simpa using congrArg Subtype.val hc1)

private theorem poly_prod_cube {F : Type} [Field F] {ω : F} (hω3 : ω ^ 3 = 1)
    (hωsum : ω ^ 2 + ω + 1 = 0) :
    (X - C (1 : F)) * (X - C ω) * (X - C (ω ^ 2)) = X ^ 3 - 1 := by
  have hCone : (C (1 : F) : F[X]) = 1 := map_one _
  have hCsum : (C (1 : F) : F[X]) + C ω + C (ω ^ 2) = 0 := by
    rw [← map_add, ← map_add, show (1 : F) + ω + ω ^ 2 = 0 by linear_combination hωsum,
      map_zero]
  have hCthree : (C ω : F[X]) * C (ω ^ 2) = 1 := by
    rw [← map_mul, show ω * ω ^ 2 = ω ^ 3 by ring, hω3, map_one]
  have hCsum' : (1 : F[X]) + C ω + C (ω ^ 2) = 0 := by
    rw [← hCone]; exact hCsum
  have hCprod : (C (1 : F) : F[X]) * C ω + (C (1 : F) : F[X]) * C (ω ^ 2) +
      C ω * C (ω ^ 2) = 0 := by
    rw [hCone, one_mul, one_mul, hCthree]
    linear_combination hCsum'
  have hexp : (X - C (1 : F)) * (X - C ω) * (X - C (ω ^ 2)) =
      X ^ 3 - ((C (1 : F) : F[X]) + C ω + C (ω ^ 2)) * X ^ 2 +
        ((C (1 : F) : F[X]) * C ω + (C (1 : F) : F[X]) * C (ω ^ 2) +
          C ω * C (ω ^ 2)) * X -
        (C (1 : F) : F[X]) * C ω * C (ω ^ 2) := by ring
  rw [hexp, hCsum, hCprod, hCone, one_mul, hCthree]
  ring

private theorem prod_factor_eq_zero {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {f : Module.End F W} {ω : F} (hω3 : ω ^ 3 = 1) (hωsum : ω ^ 2 + ω + 1 = 0)
    (hz3 : f ^ 3 = 1) :
    (f - algebraMap F (Module.End F W) 1) *
      (f - algebraMap F (Module.End F W) ω) *
      (f - algebraMap F (Module.End F W) (ω ^ 2)) = 0 := by
  have hpoly := poly_prod_cube hω3 hωsum
  have h := congrArg (aeval f) hpoly
  simpa [map_mul, map_sub, map_pow, hz3] using h

private theorem not_isMulCommutative_of_noncommuting {G : Type*} [Group G]
    {D : Subgroup G} (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) :
    ¬ IsMulCommutative D := by
  intro hab
  obtain ⟨x, hx, x', hx', hne⟩ := hna
  exact hne (congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩))

private theorem nontrivial_of_exists_noncommuting {F W : Type} [Field F] [AddCommGroup W]
    [Module F W] {D : Subgroup (Module.End F W)ˣ}
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) : Nontrivial W := by
  rcases subsingleton_or_nontrivial W with h | h
  · exfalso
    haveI : Subsingleton W := h
    haveI : Subsingleton (Module.End F W) := inferInstance
    haveI : Subsingleton (Module.End F W)ˣ := inferInstance
    obtain ⟨x, hx, x', hx', hne⟩ := hna
    exact hne (Subsingleton.elim _ _)
  · exact h

private theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    (h3dvd : ¬ 3 ∣ q - 1) : 3 ∣ q ^ 2 - 1 := by
  have hqprime : q.Prime := Fact.out
  have hq_gt1 : 1 < q := hqprime.one_lt
  have hqnotdvd : ¬ 3 ∣ q := by
    intro h
    have hqeq : 3 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hqprime).mp h
    exact hq3 hqeq.symm
  have hqZall : ∀ x : ZMod 3, x ≠ 0 → x ≠ 1 → x ^ 2 = 1 := by decide
  have hqZ : (q : ZMod 3) ^ 2 = 1 := by
    refine hqZall (q : ZMod 3) ?_ ?_
    · rw [Ne, ZMod.natCast_eq_zero_iff q 3]
      exact hqnotdvd
    · intro h
      apply h3dvd
      have hle : 1 ≤ q := hq_gt1.le
      have hzero : ((q - 1 : ℕ) : ZMod 3) = 0 := by
        rw [Nat.cast_sub hle, h, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff (q - 1) 3).mp hzero
  have hle : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq_gt1.le
  have h0 : ((q ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sub hle, Nat.cast_pow, hqZ, Nat.cast_one, sub_self]
  exact (ZMod.natCast_eq_zero_iff (q ^ 2 - 1) 3).mp h0

private theorem isMulCommutative_of_three_not_dvd_sub_one {q : ℕ} [Fact q.Prime]
    (hq3 : q ≠ 3) {W : Type} [AddCommGroup W] [Module (ZMod q) W]
    [Module.Finite (ZMod q) W] (hW : Module.finrank (ZMod q) W ≤ 3)
    {D : Subgroup (Module.End (ZMod q) W)ˣ} (hD : IsPGroup 3 D)
    (h3dvd : ¬ 3 ∣ q - 1) : IsMulCommutative D := by
  have hqnotdvd : ¬ 3 ∣ q := by
    intro h
    have hqeq : 3 = q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : q.Prime)).mp h
    exact hq3 hqeq.symm
  have h3card : ¬ 3 ∣ Nat.card (ZMod q) := by
    rw [Nat.card_zmod]
    exact hqnotdvd
  have hq2mod := three_dvd_sq_sub_one_of_not_dvd hq3 h3dvd
  obtain ⟨e, he, hpe⟩ := CFSG.LocalAnalysis.RankFourTheoremC.exists_order_data
    (K := ZMod q) (p := 3) h3card
  have hpeq : ∀ j, 3 ∣ q ^ j - 1 ↔ e ∣ j := by
    intro j
    rw [← Nat.card_zmod q]
    exact hpe j
  have he_ne1 : e ≠ 1 := by
    intro he1
    have h1 : 3 ∣ q ^ 1 - 1 :=
      (hpeq 1).mpr (by simpa [he1] using (one_dvd 1 : (1 : ℕ) ∣ 1))
    exact h3dvd (by simpa using h1)
  have he_dvd2 : e ∣ 2 := (hpeq 2).mp hq2mod
  have he2 : e = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp he_dvd2 with h | h
    · exact absurd h he_ne1
    · exact h
  have hlt2 : Module.finrank (ZMod q) W / 2 < 3 := by
    calc Module.finrank (ZMod q) W / 2 ≤ 3 / 2 := Nat.div_le_div_right hW
      _ < 3 := by norm_num
  have hhpe : ∀ j, 3 ∣ Nat.card (ZMod q) ^ j - 1 ↔ 2 ∣ j := by
    intro j
    rw [← he2]
    exact hpe j
  exact CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup_GL
    (K := ZMod q) (V := W) (p := 3) (e := 2) (by norm_num) h3card (by norm_num) hhpe
    hlt2 hD

private theorem kernel_scalar_invariant {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D : Subgroup (Module.End (ZMod q) W)ˣ} {z : (Module.End (ZMod q) W)ˣ}
    (hzc : z ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)) (lam : ZMod q) :
    ∀ g ∈ D, ∀ w ∈ LinearMap.ker ((z : Module.End (ZMod q) W) -
      algebraMap (ZMod q) (Module.End (ZMod q) W) lam),
      ((g : Module.End (ZMod q) W) w) ∈ LinearMap.ker
        ((z : Module.End (ZMod q) W) - algebraMap (ZMod q) (Module.End (ZMod q) W) lam) := by
  intro g hg w hw
  have hcomm : ((g : Module.End (ZMod q) W) * (z : Module.End (ZMod q) W)) =
      ((z : Module.End (ZMod q) W) * (g : Module.End (ZMod q) W)) :=
    congrArg Units.val (Subgroup.mem_centralizer_iff.mp hzc g hg)
  have hcommw : (g : Module.End (ZMod q) W) ((z : Module.End (ZMod q) W) w) =
      (z : Module.End (ZMod q) W) ((g : Module.End (ZMod q) W) w) := by
    simpa [Module.End.mul_apply] using congrArg (fun h => h w) hcomm
  have hscalw : (g : Module.End (ZMod q) W)
      (algebraMap (ZMod q) (Module.End (ZMod q) W) lam w) =
      algebraMap (ZMod q) (Module.End (ZMod q) W) lam
        ((g : Module.End (ZMod q) W) w) := by
    simp [Algebra.algebraMap_eq_smul_one]
  show ((z : Module.End (ZMod q) W) - algebraMap (ZMod q) (Module.End (ZMod q) W) lam)
    ((g : Module.End (ZMod q) W) w) = 0
  calc ((z : Module.End (ZMod q) W) - algebraMap (ZMod q) (Module.End (ZMod q) W) lam)
        ((g : Module.End (ZMod q) W) w)
      = (z : Module.End (ZMod q) W) ((g : Module.End (ZMod q) W) w) -
          algebraMap (ZMod q) (Module.End (ZMod q) W) lam
            ((g : Module.End (ZMod q) W) w) := by rw [LinearMap.sub_apply]
    _ = (g : Module.End (ZMod q) W) ((z : Module.End (ZMod q) W) w) -
          (g : Module.End (ZMod q) W)
            (algebraMap (ZMod q) (Module.End (ZMod q) W) lam w) := by
          rw [hcommw, hscalw]
    _ = (g : Module.End (ZMod q) W)
          (((z : Module.End (ZMod q) W) -
            algebraMap (ZMod q) (Module.End (ZMod q) W) lam) w) := by
          rw [LinearMap.sub_apply]
          exact (LinearMap.map_sub (g : Module.End (ZMod q) W) ((z : Module.End (ZMod q) W) w)
            (algebraMap (ZMod q) (Module.End (ZMod q) W) lam w)).symm
    _ = 0 := by rw [hw, map_zero]

private theorem isMulCommutative_of_scalar_kernel {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hD : IsPGroup 3 D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (h3F : (3 : ZMod q) ≠ 0) (h3card : ¬ 3 ∣ Nat.card (ZMod q))
    {z : (Module.End (ZMod q) W)ˣ} (hz : z ∈ D)
    (hzc : z ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)) {lam : ZMod q}
    (hker : LinearMap.ker ((z : Module.End (ZMod q) W) -
      algebraMap (ZMod q) (Module.End (ZMod q) W) lam) ≠ ⊤)
    (hnu : ¬ IsUnit ((z : Module.End (ZMod q) W) -
      algebraMap (ZMod q) (Module.End (ZMod q) W) lam)) :
    IsMulCommutative D := by
  let U : Submodule (ZMod q) W :=
    LinearMap.ker ((z : Module.End (ZMod q) W) -
      algebraMap (ZMod q) (Module.End (ZMod q) W) lam)
  have hU0 : U ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective ((z : Module.End (ZMod q) W) -
        algebraMap (ZMod q) (Module.End (ZMod q) W) lam) :=
      LinearMap.ker_eq_bot.mp hbot
    have hbij : Function.Bijective ((z : Module.End (ZMod q) W) -
        algebraMap (ZMod q) (Module.End (ZMod q) W) lam) :=
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
    exact hnu ((Module.End.isUnit_iff _).mpr hbij)
  have hUt : U ≠ ⊤ := hker
  have hUinv := kernel_scalar_invariant hzc lam
  have hU : Module.finrank (ZMod q) U < 3 := by
    have hlt : Module.finrank (ZMod q) U < Module.finrank (ZMod q) W :=
      Submodule.finrank_lt hUt
    omega
  have hQ : Module.finrank (ZMod q) (W ⧸ U) < 3 := by
    have hdim := Submodule.finrank_quotient_add_finrank U
    have hpos : 1 ≤ Module.finrank (ZMod q) U :=
      Submodule.one_le_finrank_iff.mpr hU0
    omega
  exact isMulCommutative_of_invariant_submodule hD hexp h3F h3card U hU0 hUt hUinv hU hQ

private theorem exists_primitive_cube_root {q : ℕ} [Fact q.Prime] (h3dvd : 3 ∣ q - 1) :
    ∃ ω : ZMod q, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  have h3units : 3 ∣ Nat.card (ZMod q)ˣ := by
    rw [Nat.card_units, Nat.card_zmod]
    exact h3dvd
  obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' 3 h3units
  refine ⟨(ωu : ZMod q), ?_, ?_, ?_⟩
  · have h := pow_orderOf_eq_one ωu
    rw [hωu] at h
    exact congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h
  · intro h
    have h1 : orderOf ωu = 1 := orderOf_eq_one_iff.mpr (Units.ext h)
    rw [hωu] at h1
    omega
  · have hω3 : ((ωu : ZMod q)) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one ωu
      rw [hωu] at h
      exact congrArg (fun u : (ZMod q)ˣ => (u : ZMod q)) h
    have h : ((ωu : ZMod q) - 1) * (((ωu : ZMod q)) ^ 2 + (ωu : ZMod q) + 1) = 0 := by
      rw [show ((ωu : ZMod q) - 1) * (((ωu : ZMod q)) ^ 2 + (ωu : ZMod q) + 1) =
        ((ωu : ZMod q)) ^ 3 - 1 by ring, hω3]
      ring
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) (by
        intro hω1
        have h1 : orderOf ωu = 1 := orderOf_eq_one_iff.mpr (Units.ext hω1)
        rw [hωu] at h1
        omega)
    · exact h1

private theorem exists_eq_algebraMap_of_three_dvd {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hD : IsPGroup 3 D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) {z : (Module.End (ZMod q) W)ˣ} (hz : z ∈ D)
    (hzc : z ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ))
    (h3F : (3 : ZMod q) ≠ 0) (h3card : ¬ 3 ∣ Nat.card (ZMod q)) (h3dvd : 3 ∣ q - 1) :
    ∃ c : ZMod q, (z : Module.End (ZMod q) W) = algebraMap (ZMod q) _ c := by
  classical
  haveI : Nontrivial W := nontrivial_of_exists_noncommuting hna
  obtain ⟨ω, hω3, hω1, hωsum⟩ := exists_primitive_cube_root h3dvd
  let f : Module.End (ZMod q) W := (z : Module.End (ZMod q) W)
  have hz3 : f ^ 3 = 1 := congrArg Units.val (hexp z hz)
  have hprod := prod_factor_eq_zero hω3 hωsum hz3
  by_cases hscalar : ∃ c : ZMod q, f = algebraMap (ZMod q) (Module.End (ZMod q) W) c
  · exact hscalar
  exfalso
  have hnonunit : ¬ IsUnit (f - algebraMap (ZMod q) (Module.End (ZMod q) W) 1) ∨
      ¬ IsUnit (f - algebraMap (ZMod q) (Module.End (ZMod q) W) ω) ∨
      ¬ IsUnit (f - algebraMap (ZMod q) (Module.End (ZMod q) W) (ω ^ 2)) := by
    by_contra h
    push Not at h
    have hu : IsUnit ((f - algebraMap (ZMod q) (Module.End (ZMod q) W) 1) *
        (f - algebraMap (ZMod q) (Module.End (ZMod q) W) ω) *
        (f - algebraMap (ZMod q) (Module.End (ZMod q) W) (ω ^ 2))) :=
      h.1.mul (h.2.1.mul h.2.2)
    rw [hprod] at hu
    exact not_isUnit_zero hu
  have key : ∀ lam : ZMod q, lam ^ 3 = 1 →
      ¬ IsUnit (f - algebraMap (ZMod q) (Module.End (ZMod q) W) lam) → False := by
    intro lam hlam3 hnu
    by_cases htop : LinearMap.ker (f - algebraMap (ZMod q) (Module.End (ZMod q) W) lam) = ⊤
    · apply hscalar
      refine ⟨lam, ?_⟩
      have hzero : f - algebraMap (ZMod q) (Module.End (ZMod q) W) lam = 0 :=
        LinearMap.ker_eq_top.mp htop
      exact sub_eq_zero.mp hzero
    · exact (not_isMulCommutative_of_noncommuting hna)
        (isMulCommutative_of_scalar_kernel hq3 hW hD hexp h3F h3card hz hzc htop hnu)
  rcases hnonunit with h1 | h2 | h3
  · exact key 1 (by norm_num) h1
  · exact key ω hω3 h2
  · refine key (ω ^ 2) ?_ h3
    calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3]; norm_num

theorem exists_eq_algebraMap_of_mem_centralizer {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hD : IsPGroup 3 D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) {z : (Module.End (ZMod q) W)ˣ} (hz : z ∈ D)
    (hzc : z ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)) :
    ∃ c : ZMod q, (z : Module.End (ZMod q) W) = algebraMap (ZMod q) _ c := by
  classical
  haveI : Nontrivial W := nontrivial_of_exists_noncommuting hna
  have hqnotdvd : ¬ 3 ∣ q := by
    intro h
    have hqeq : 3 = q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : q.Prime)).mp h
    exact hq3 hqeq.symm
  have h3F : (3 : ZMod q) ≠ 0 := by
    change ((3 : ℕ) : ZMod q) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff 3 q]
    intro h
    have hqeq : q = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_three).mp h
    exact hq3 hqeq
  have h3card : ¬ 3 ∣ Nat.card (ZMod q) := by
    rw [Nat.card_zmod]
    exact hqnotdvd
  by_cases h3dvd : 3 ∣ q - 1
  · exact exists_eq_algebraMap_of_three_dvd hq3 hW hD hexp hna hz hzc h3F h3card h3dvd
  · exact absurd (isMulCommutative_of_three_not_dvd_sub_one hq3 hW hD h3dvd)
      (not_isMulCommutative_of_noncommuting hna)

private theorem jointEigenvector_apply {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D : Subgroup (Module.End (ZMod q) W)ˣ} {ι : Type*}
    (rep : ι → ↥D) (scal : ι → ↥D → ZMod q)
    (hscal : ∀ (c : ι) (g : ↥D),
      (((⁅g, rep c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
        algebraMap (ZMod q) (Module.End (ZMod q) W) (scal c g)) :
    ∀ (c : ι) (g : ↥D),
      (LinearMap.mulLeft (ZMod q) ((g : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) ∘ₗ
        LinearMap.mulRight (ZMod q)
          (((g⁻¹ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W))
        (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
          scal c g • (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) := by
  intro c g
  have hspec := hscal c g
  have h6 : (((g : (Module.End (ZMod q) W)ˣ) *
      ((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) *
      ((g : (Module.End (ZMod q) W)ˣ)⁻¹)) =
      (((⁅g, rep c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) *
        ((rep c : ↥D) : (Module.End (ZMod q) W)ˣ))) := by
    rw [commutatorElement_def]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have h6e : ((((g : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) *
      (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) *
      ((((g⁻¹ : ↥D) : (Module.End (ZMod q) W)ˣ)) : Module.End (ZMod q) W)) =
      ((((⁅g, rep c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) *
        (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W))) := by
    simpa [Subgroup.coe_inv] using congrArg Units.val h6
  calc (LinearMap.mulLeft (ZMod q) ((g : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) ∘ₗ
        LinearMap.mulRight (ZMod q)
          (((g⁻¹ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W))
        (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W)
      = ((g : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) *
          (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) *
          ((((g⁻¹ : ↥D) : (Module.End (ZMod q) W)ˣ)) : Module.End (ZMod q) W) := by
          simp [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, mul_assoc]
    _ = ((((⁅g, rep c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ)) : Module.End (ZMod q) W) *
          (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) := h6e
    _ = algebraMap (ZMod q) (Module.End (ZMod q) W) (scal c g) *
          (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) := by
          rw [hspec]
    _ = scal c g • (((rep c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) := by
          rw [Algebra.smul_def]

private theorem card_quotient_le_nine {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D Z : Subgroup (Module.End (ZMod q) W)ˣ}
    (φ : ↥D → Module.End (ZMod q) (Module.End (ZMod q) W))
    (v : (↥D ⧸ Z.subgroupOf D) → Module.End (ZMod q) W)
    (scal : (↥D ⧸ Z.subgroupOf D) → ↥D → ZMod q)
    (hv0 : ∀ c, v c ≠ 0) (hφv : ∀ c g, φ g (v c) = scal c g • v c)
    [Fintype (↥D ⧸ Z.subgroupOf D)] (htinj : Function.Injective scal) :
    Fintype.card (↥D ⧸ Z.subgroupOf D) ≤ 9 := by
  have hli : LinearIndependent (ZMod q) v :=
    iSupIndep.linearIndependent _ ((TauCeti.iSupIndep_iInf_eigenspace φ).comp htinj)
      (fun c => (Submodule.mem_iInf _).mpr fun g =>
        Module.End.mem_eigenspace_iff.mpr (hφv c g)) hv0
  have hcard := hli.fintype_card_le_finrank
  have h9 : Module.finrank (ZMod q) (Module.End (ZMod q) W) ≤ 9 := by
    calc Module.finrank (ZMod q) (Module.End (ZMod q) W) =
          Module.finrank (ZMod q) W * Module.finrank (ZMod q) W :=
            Module.finrank_linearMap (ZMod q) (ZMod q) W W
      _ ≤ 3 * 3 := Nat.mul_le_mul hW hW
      _ = 9 := by norm_num
  exact hcard.trans h9

private theorem commutator_eq_of_scal_eq {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D Z : Subgroup (Module.End (ZMod q) W)ˣ}
    (scal : (↥D ⧸ Z.subgroupOf D) → ↥D → ZMod q)
    (hscal : ∀ (c : ↥D ⧸ Z.subgroupOf D) (g : ↥D),
      (((⁅g, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
        algebraMap (ZMod q) (Module.End (ZMod q) W) (scal c g))
    (hD : ↥D) (c c' : ↥D ⧸ Z.subgroupOf D) (hcc : scal c = scal c') :
    (⁅((hD : ↥D) : (Module.End (ZMod q) W)ˣ),
        ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆ :
      (Module.End (ZMod q) W)ˣ) =
      (⁅((hD : ↥D) : (Module.End (ZMod q) W)ˣ),
        ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆ :
        (Module.End (ZMod q) W)ˣ) := by
  apply Units.ext
  have h1 := hscal c' hD
  have h2 := hscal c hD
  change (((⁅hD, Quotient.out c'⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) :
    Module.End (ZMod q) W) =
    (((⁅hD, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) :
      Module.End (ZMod q) W)
  have hsc : scal c' hD = scal c hD := (congrFun hcc hD).symm
  rw [h1, h2, hsc]

private theorem inv_mul_mem_centralizer {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D Z : Subgroup (Module.End (ZMod q) W)ˣ}
    (hcl : ∀ x ∈ D, ∀ x' ∈ D,
      ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ))
    (scal : (↥D ⧸ Z.subgroupOf D) → ↥D → ZMod q)
    (hscal : ∀ (c : ↥D ⧸ Z.subgroupOf D) (g : ↥D),
      (((⁅g, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
        algebraMap (ZMod q) (Module.End (ZMod q) W) (scal c g))
    (c c' : ↥D ⧸ Z.subgroupOf D) (hcc : scal c = scal c') :
    (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁻¹ *
      ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)) ∈
        Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  let hD : ↥D := ⟨h, hh⟩
  have hcent : ∀ u ∈ D, ⁅h, u⁆ ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) :=
    fun u hu => hcl h hh u hu
  have hcx : Commute ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)
      (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆) :=
    (Subgroup.mem_centralizer_iff.mp (hcent _ (Quotient.out c).2) _
      (Quotient.out c).2)
  have hcx' : Commute ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)
      (⁅h, ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆) :=
    (Subgroup.mem_centralizer_iff.mp (hcent _ (Quotient.out c').2) _
      (Quotient.out c).2)
  have hinv1 : (⁅h, (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹⁆ :
      (Module.End (ZMod q) W)ˣ) =
      (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ := by
    rw [commutatorElement_inv_right]
    rw [show ⁅((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ), h⁆ =
      (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ from
      (commutatorElement_inv h ((Quotient.out c : ↥D) :
        (Module.End (ZMod q) W)ˣ)).symm]
    rw [hcx.inv_left.inv_right.eq]
    group
  have hprod : (⁅h, (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹ *
      ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆ :
      (Module.End (ZMod q) W)ˣ) =
      (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ *
        (⁅h, ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆) := by
    rw [commutatorElement_mul_right_eq_mul_conj, hinv1]
    calc (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ *
          (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹ *
          (⁅h, ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆) *
          (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹⁻¹
        = (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ *
          ((((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹ *
            (⁅h, ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)) *
          (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹⁻¹ := by group
      _ = (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ *
          ((⁅h, ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆) *
            (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹) *
          (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹⁻¹ := by
          rw [hcx'.inv_left.eq]
      _ = (⁅h, ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁆)⁻¹ *
          (⁅h, ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆) := by group
  have hcom : (⁅h, (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ))⁻¹ *
      ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)⁆ :
      (Module.End (ZMod q) W)ˣ) = 1 := by
    rw [hprod, commutator_eq_of_scal_eq scal hscal hD c c' hcc, inv_mul_cancel]
  exact commutatorElement_eq_one_iff_mul_comm.mp hcom

private theorem jointEigenvector_injective {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D Z : Subgroup (Module.End (ZMod q) W)ˣ} (hZ : Z = D ⊓
      Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ))
    (hcl : ∀ x ∈ D, ∀ x' ∈ D,
      ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ))
    (scal : (↥D ⧸ Z.subgroupOf D) → ↥D → ZMod q)
    (hscal : ∀ (c : ↥D ⧸ Z.subgroupOf D) (g : ↥D),
      (((⁅g, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
        algebraMap (ZMod q) (Module.End (ZMod q) W) (scal c g)) :
    Function.Injective scal := by
  subst Z
  intro c c' hcc
  change scal c = scal c' at hcc
  rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c', QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  change (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁻¹ *
    ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)) ∈
      D ⊓ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)
  have hyD : (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ)⁻¹ *
      ((Quotient.out c' : ↥D) : (Module.End (ZMod q) W)ˣ)) ∈ D :=
    D.mul_mem (D.inv_mem (Quotient.out c).2) (Quotient.out c').2
  have hyC := inv_mul_mem_centralizer hcl scal hscal c c' hcc
  exact ⟨hyD, hyC⟩

private theorem relIndex_centralizer_le_nine {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hD : IsPGroup 3 D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hcl : ∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ))
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) :
    (Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)).relIndex D ≤ 9 := by
  classical
  haveI : Nontrivial W := nontrivial_of_exists_noncommuting hna
  set C : Subgroup (Module.End (ZMod q) W)ˣ :=
    Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) with hC
  set Z : Subgroup (Module.End (ZMod q) W)ˣ := D ⊓ C with hZ
  have hZC : Z.relIndex D = C.relIndex D := by
    rw [hZ, inf_comm]
    exact Subgroup.inf_relIndex_right C D
  haveI : Fintype (↥D ⧸ Z.subgroupOf D) := Fintype.ofFinite _
  let scal : (↥D ⧸ Z.subgroupOf D) → ↥D → ZMod q := fun c g =>
    Classical.choose (exists_eq_algebraMap_of_mem_centralizer (q := q) hq3 hW hD hexp hna
      (z := ((⁅g, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ))
      (⁅g, Quotient.out c⁆ : ↥D).2
      (by
        have h := hcl (g : (Module.End (ZMod q) W)ˣ) g.2
          ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ) (Quotient.out c).2
        simpa [commutatorElement_def] using h))
  have hscal : ∀ (c : ↥D ⧸ Z.subgroupOf D) (g : ↥D),
      (((⁅g, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
        algebraMap (ZMod q) (Module.End (ZMod q) W) (scal c g) := by
    intro c g
    exact Classical.choose_spec (exists_eq_algebraMap_of_mem_centralizer (q := q) hq3 hW hD
      hexp hna (z := ((⁅g, Quotient.out c⁆ : ↥D) : (Module.End (ZMod q) W)ˣ))
      (⁅g, Quotient.out c⁆ : ↥D).2
      (by
        have h := hcl (g : (Module.End (ZMod q) W)ˣ) g.2
          ((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ) (Quotient.out c).2
        simpa [commutatorElement_def] using h))
  have hv0 : ∀ c : ↥D ⧸ Z.subgroupOf D,
      (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) ≠ 0 :=
    fun c => Units.ne_zero _
  have hφv : ∀ (c : ↥D ⧸ Z.subgroupOf D) (g : ↥D),
      (LinearMap.mulLeft (ZMod q) ((g : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) ∘ₗ
        LinearMap.mulRight (ZMod q)
          (((g⁻¹ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W))
        (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W) =
          scal c g • (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ) :
            Module.End (ZMod q) W) :=
    jointEigenvector_apply (fun c => Quotient.out c) scal hscal
  have hcard := card_quotient_le_nine hW
    (fun g => LinearMap.mulLeft (ZMod q) ((g : (Module.End (ZMod q) W)ˣ) :
      Module.End (ZMod q) W) ∘ₗ LinearMap.mulRight (ZMod q)
        (((g⁻¹ : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W))
    (fun c => (((Quotient.out c : ↥D) : (Module.End (ZMod q) W)ˣ) : Module.End (ZMod q) W))
    scal hv0 hφv (jointEigenvector_injective hZ hcl scal hscal)
  rw [← hZC]
  calc Z.relIndex D = Fintype.card (↥D ⧸ Z.subgroupOf D) := by
        rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
    _ ≤ 9 := hcard

private theorem k_ne_zero_of_center_quotient {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) {k : ℕ}
    (hk : Nat.card (↥D ⧸ Subgroup.center ↥D) = 3 ^ k) : k ≠ 0 := by
  intro h0
  have hcard : Nat.card (↥D ⧸ Subgroup.center ↥D) = 1 := by
    rw [hk, h0, pow_zero]
  have hidx : (Subgroup.center ↥D).index = 1 := by
    rw [Subgroup.index, hcard]
  have hcen : Subgroup.center ↥D = ⊤ := Subgroup.index_eq_one.mp hidx
  have hcommD : ∀ a b : ↥D, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center ↥D := hcen ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  obtain ⟨x, hx, x', hx', hne⟩ := hna
  exact hne (congrArg Subtype.val (hcommD ⟨x, hx⟩ ⟨x', hx'⟩))

private theorem k_ne_one_of_center_quotient {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) {k : ℕ}
    (hk : Nat.card (↥D ⧸ Subgroup.center ↥D) = 3 ^ k) : k ≠ 1 := by
  intro h1
  have hcard : Nat.card (↥D ⧸ Subgroup.center ↥D) = 3 := by
    rw [hk, h1]; norm_num
  haveI : IsCyclic (↥D ⧸ Subgroup.center ↥D) :=
    isCyclic_of_prime_card (p := 3) hcard
  have hcommD : ∀ a b : ↥D, a * b = b * a :=
    commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center ↥D))
      (by rw [QuotientGroup.ker_mk'])
  obtain ⟨x, hx, x', hx', hne⟩ := hna
  exact hne (congrArg Subtype.val (hcommD ⟨x, hx⟩ ⟨x', hx'⟩))

private theorem nine_le_relIndex_centralizer {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {D : Subgroup (Module.End (ZMod q) W)ˣ} (hD : IsPGroup 3 D)
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x)
    (hle : (Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)).relIndex D ≤ 9) :
    9 ≤ (Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)).relIndex D := by
  set C : Subgroup (Module.End (ZMod q) W)ˣ :=
    Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) with hC
  set Z : Subgroup (Module.End (ZMod q) W)ˣ := D ⊓ C with hZ
  have hZc : Z.subgroupOf D = Subgroup.center ↥D := by
    rw [hZ]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
    constructor
    · rintro ⟨-, hx⟩ g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) g g.2)
    · intro hx
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      exact congrArg Subtype.val (hx ⟨g, hg⟩)
  have hrel : Z.relIndex D = Nat.card (↥D ⧸ Subgroup.center ↥D) := by
    rw [Subgroup.relIndex, hZc]
    rfl
  have hquotp : IsPGroup 3 (↥D ⧸ Subgroup.center ↥D) :=
    IsPGroup.of_surjective hD (QuotientGroup.mk' (Subgroup.center ↥D))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨k, hk⟩ := hquotp.exists_card_eq
  have hkval : Z.relIndex D = 3 ^ k := by rw [hrel, hk]
  have hZC : Z.relIndex D = C.relIndex D := by
    rw [hZ, inf_comm]
    exact Subgroup.inf_relIndex_right C D
  have hk_le : 3 ^ k ≤ 9 := by
    rw [← hkval, hZC]
    exact hle
  have hk2 : k = 2 := by
    have hk_ne0 := k_ne_zero_of_center_quotient hna hk
    have hk_ne1 := k_ne_one_of_center_quotient hna hk
    have hk_le2 : k ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ k := by omega
      have hpow : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h3
      norm_num at hpow
      omega
    omega
  rw [← hZC, hkval, hk2]
  norm_num

theorem relIndex_centralizer_eq_nine {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hD : IsPGroup 3 D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hcl : ∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ))
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x) :
    (Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ)).relIndex D = 9 := by
  set C : Subgroup (Module.End (ZMod q) W)ˣ :=
    Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) with hC
  set Z : Subgroup (Module.End (ZMod q) W)ˣ := D ⊓ C with hZ
  have hZC : Z.relIndex D = C.relIndex D := by
    rw [hZ, inf_comm]
    exact Subgroup.inf_relIndex_right C D
  have hle : C.relIndex D ≤ 9 :=
    relIndex_centralizer_le_nine hq3 hW hD hexp hcl hna
  have hge : 9 ≤ C.relIndex D :=
    nine_le_relIndex_centralizer hD hna hle
  exact le_antisymm hle hge

private theorem critical_subgroup_exp {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {T : Subgroup (Module.End (ZMod q) W)ˣ} {D0 : Subgroup ↥T}
    (hD0exp : ∀ x ∈ D0, x ^ 3 = 1) :
    ∀ x ∈ D0.map T.subtype, x ^ 3 = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  simpa using congrArg Subtype.val (hD0exp a ha)

private theorem critical_subgroup_centralizer {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {T : Subgroup (Module.End (ZMod q) W)ˣ} {D0 : Subgroup ↥T}
    (hD0comm : ⁅D0, (⊤ : Subgroup ↥T)⁆ ≤
      D0 ⊓ Subgroup.centralizer (D0 : Set ↥T)) :
    ∀ x ∈ D0.map T.subtype, ∀ x' ∈ D0.map T.subtype,
      ⁅x, x'⁆ ∈ Subgroup.centralizer (D0.map T.subtype :
        Set (Module.End (ZMod q) W)ˣ) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hmem : ⁅a, b⁆ ∈ D0 ⊓ Subgroup.centralizer (D0 : Set ↥T) :=
    hD0comm (Subgroup.commutator_mem_commutator ha (Subgroup.mem_top b))
  refine Subgroup.mem_centralizer_iff.mpr ?_
  rintro _ ⟨c, hc, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hmem.2 c hc
  simpa [commutatorElement_def] using congrArg Subtype.val hcomm

private theorem critical_subgroup_normalizer {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {T : Subgroup (Module.End (ZMod q) W)ˣ} {D0 : Subgroup ↥T}
    (hD0char : D0.Characteristic) {y : (Module.End (ZMod q) W)ˣ}
    (hy : y ∈ Subgroup.normalizer (T : Set (Module.End (ZMod q) W)ˣ)) :
    y ∈ Subgroup.normalizer (D0.map T.subtype : Set (Module.End (ZMod q) W)ˣ) := by
  letI : D0.Characteristic := hD0char
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    have := CFSG.Walter.conj_mem_map_of_characteristic (X := T) (D := D0) hy hd
    simpa using this
  · intro hd
    have h1 := CFSG.Walter.conj_mem_map_of_characteristic (X := T) (D := D0)
      (Subgroup.inv_mem _ hy) hd
    have h2 : y⁻¹ * (y * d * y⁻¹) * (y⁻¹)⁻¹ = d := by group
    rwa [h2] at h1

private theorem exists_pow_centralizes_T {q : ℕ} [Fact q.Prime]
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    {T : Subgroup (Module.End (ZMod q) W)ˣ} {D0 : Subgroup ↥T}
    (hD0fix : IsPGroup 3 (fixingSubgroup (MulAut ↥T) (D0 : Set ↥T)))
    {y : (Module.End (ZMod q) W)ˣ} (hy : y ∈ Subgroup.normalizer (T : Set _))
    (m : ℕ) (hm : ∀ z ∈ D0.map T.subtype, y ^ m * z = z * y ^ m) :
    ∃ j : ℕ, ∀ x ∈ T, y ^ (m * 3 ^ j) * x = x * y ^ (m * 3 ^ j) := by
  let φ : MulAut ↥T := Subgroup.normalizerMonoidHom T ⟨y, hy⟩
  have hφfix : φ ^ m ∈ fixingSubgroup (MulAut ↥T) (D0 : Set ↥T) := by
    rw [mem_fixingSubgroup_iff]
    intro d0 hd0
    change (φ ^ m) d0 = d0
    apply Subtype.ext
    have hd : ((d0 : ↥T) : (Module.End (ZMod q) W)ˣ) ∈ D0.map T.subtype :=
      ⟨d0, hd0, rfl⟩
    have hcomm := hm ((d0 : ↥T) : (Module.End (ZMod q) W)ˣ) hd
    have hφm : φ ^ m = Subgroup.normalizerMonoidHom T (⟨y, hy⟩ ^ m) := by
      change (Subgroup.normalizerMonoidHom T ⟨y, hy⟩) ^ m =
        Subgroup.normalizerMonoidHom T (⟨y, hy⟩ ^ m)
      rw [map_pow]
    rw [hφm, Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hcoe : ((⟨y, hy⟩ ^ m : ↥(Subgroup.normalizer
        (T : Set (Module.End (ZMod q) W)ˣ))) :
        (Module.End (ZMod q) W)ˣ) = y ^ m := by
      rw [Subgroup.coe_pow]
    rw [hcoe]
    calc y ^ m * ((d0 : ↥T) : (Module.End (ZMod q) W)ˣ) * (y ^ m)⁻¹
        = ((d0 : ↥T) : (Module.End (ZMod q) W)ˣ) * y ^ m * (y ^ m)⁻¹ := by
            rw [hcomm]
      _ = ((d0 : ↥T) : (Module.End (ZMod q) W)ˣ) := by group
  obtain ⟨j, hj⟩ := hD0fix ⟨φ ^ m, hφfix⟩
  refine ⟨j, ?_⟩
  intro x hx
  have hφpow : φ ^ (m * 3 ^ j) = 1 := by
    have h := congrArg Subtype.val hj
    simpa [Subgroup.coe_pow, pow_mul] using h
  have hφpow' : Subgroup.normalizerMonoidHom T (⟨y, hy⟩ ^ (m * 3 ^ j)) = 1 := by
    have hφeq : Subgroup.normalizerMonoidHom T ⟨y, hy⟩ = φ := rfl
    rw [map_pow, hφeq]
    exact hφpow
  have h1 := congrArg (fun τ : MulAut ↥T =>
    ((τ ⟨x, hx⟩ : ↥T) : (Module.End (ZMod q) W)ˣ)) hφpow'
  simp only [MulAut.one_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_pow] at h1
  calc y ^ (m * 3 ^ j) * x
      = (y ^ (m * 3 ^ j) * x * (y ^ (m * 3 ^ j))⁻¹) * y ^ (m * 3 ^ j) := by group
    _ = x * y ^ (m * 3 ^ j) := by rw [h1]

private theorem exists_pow_of_abelian {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {T : Subgroup (Module.End (ZMod q) W)ˣ}
    {D0 : Subgroup ↥T}
    (hD0fix : IsPGroup 3 (fixingSubgroup (MulAut ↥T) (D0 : Set ↥T)))
    {y : (Module.End (ZMod q) W)ˣ} (hy : y ∈ Subgroup.normalizer (T : Set _))
    (hDab : IsMulCommutative (D0.map T.subtype))
    (hD : IsPGroup 3 (D0.map T.subtype))
    (hyD : y ∈ Subgroup.normalizer (D0.map T.subtype :
      Set (Module.End (ZMod q) W)ˣ)) :
    ∃ k : ℕ, ∀ x ∈ T, y ^ (4 * 3 ^ k) * x = x * y ^ (4 * 3 ^ k) := by
  have hqnotdvd : ¬ 3 ∣ q := by
    intro h
    have hqeq : 3 = q :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : q.Prime)).mp h
    exact hq3 hqeq.symm
  obtain h3 | h4 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.AutSection.automizer_pow_three_or_four
      (K := ZMod q) (W := W) (hW := by omega) (p := 3)
      (by rw [Nat.card_zmod]; exact hqnotdvd) hD hDab (g := y) hyD
  · have hm12 : ∀ z ∈ D0.map T.subtype, y ^ 12 * z = z * y ^ 12 := by
      intro z hz
      have hc : Commute (y ^ 3) z := by
        show y ^ 3 * z = z * y ^ 3
        calc y ^ 3 * z = (y ^ 3 * z * (y ^ 3)⁻¹) * y ^ 3 := by group
          _ = z * y ^ 3 := by rw [h3 z hz]
      have h := (hc.pow_left 4).eq
      have h12 : (y ^ 3) ^ 4 = y ^ 12 := by rw [← pow_mul]
      rwa [h12] at h
    obtain ⟨j, hj⟩ := exists_pow_centralizes_T hD0fix hy 12 hm12
    refine ⟨j + 1, fun x hx => ?_⟩
    have h := hj x hx
    have hexp : 4 * 3 ^ (j + 1) = 12 * 3 ^ j := by
      rw [pow_succ]; ring
    rwa [hexp]
  · have hm12 : ∀ z ∈ D0.map T.subtype, y ^ 12 * z = z * y ^ 12 := by
      intro z hz
      have hc : Commute (y ^ 4) z := by
        show y ^ 4 * z = z * y ^ 4
        calc y ^ 4 * z = (y ^ 4 * z * (y ^ 4)⁻¹) * y ^ 4 := by group
          _ = z * y ^ 4 := by rw [h4 z hz]
      have h := (hc.pow_left 3).eq
      have h12 : (y ^ 4) ^ 3 = y ^ 12 := by rw [← pow_mul]
      rwa [h12] at h
    obtain ⟨j, hj⟩ := exists_pow_centralizes_T hD0fix hy 12 hm12
    refine ⟨j + 1, fun x hx => ?_⟩
    have h := hj x hx
    have hexp : 4 * 3 ^ (j + 1) = 12 * 3 ^ j := by
      rw [pow_succ]; ring
    rwa [hexp]

private theorem noncommuting_of_not_isMulCommutative {G : Type*} [Group G]
    {D : Subgroup G} (hDab : ¬ IsMulCommutative D) :
    ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x := by
  by_contra h
  apply hDab
  refine isMulCommutative_iff.mpr ?_
  intro a b
  apply Subtype.ext
  by_contra hne
  exact h ⟨a, a.2, b, b.2, hne⟩

private theorem centralizer_scalars_commute {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {D : Subgroup (Module.End (ZMod q) W)ˣ}
    (hD : IsPGroup 3 D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hna : ∃ x ∈ D, ∃ x' ∈ D, x * x' ≠ x' * x)
    {y : (Module.End (ZMod q) W)ˣ} :
    ∀ z ∈ D, z ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) →
      y * z = z * y := by
  intro z hz hzc
  obtain ⟨c, hc⟩ :=
    exists_eq_algebraMap_of_mem_centralizer hq3 hW hD hexp hna (z := z) hz hzc
  apply Units.ext
  change (y : Module.End (ZMod q) W) * (z : Module.End (ZMod q) W) =
    (z : Module.End (ZMod q) W) * (y : Module.End (ZMod q) W)
  rw [hc]
  exact (Algebra.commute_algebraMap_right c (y : Module.End (ZMod q) W)).eq

private theorem exists_pow_of_nonabelian {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    {W : Type} [AddCommGroup W] [Module (ZMod q) W] [Module.Finite (ZMod q) W]
    (hW : Module.finrank (ZMod q) W ≤ 3) {T : Subgroup (Module.End (ZMod q) W)ˣ}
    {D0 : Subgroup ↥T}
    (hD0fix : IsPGroup 3 (fixingSubgroup (MulAut ↥T) (D0 : Set ↥T)))
    {y : (Module.End (ZMod q) W)ˣ} (hy : y ∈ Subgroup.normalizer (T : Set _))
    (hD : IsPGroup 3 (D0.map T.subtype))
    (hexp : ∀ x ∈ D0.map T.subtype, x ^ 3 = 1)
    (hcl : ∀ x ∈ D0.map T.subtype, ∀ x' ∈ D0.map T.subtype,
      ⁅x, x'⁆ ∈ Subgroup.centralizer (D0.map T.subtype :
        Set (Module.End (ZMod q) W)ˣ))
    (hDab : ¬ IsMulCommutative (D0.map T.subtype))
    (hyD : y ∈ Subgroup.normalizer (D0.map T.subtype :
      Set (Module.End (ZMod q) W)ˣ))
    (h36 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G}, (∀ x ∈ D, x ^ 3 = 1) →
      (∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set G)) →
      (Subgroup.centralizer (D : Set G)).relIndex D = 9 →
      ∀ {y : G}, y ∈ Subgroup.normalizer (D : Set G) →
      (∀ z ∈ D, z ∈ Subgroup.centralizer (D : Set G) → y * z = z * y) →
      ∀ x ∈ D, y ^ 36 * x = x * y ^ 36) :
    ∃ k : ℕ, ∀ x ∈ T, y ^ (4 * 3 ^ k) * x = x * y ^ (4 * 3 ^ k) := by
  have hna := noncommuting_of_not_isMulCommutative hDab
  have hyZ := centralizer_scalars_commute (y := y) hq3 hW hD hexp hna
  have hidx := relIndex_centralizer_eq_nine hq3 hW hD hexp hcl hna
  have h36c := h36 (G := (Module.End (ZMod q) W)ˣ) (D := D0.map T.subtype)
    hexp hcl hidx hyD hyZ
  obtain ⟨j, hj⟩ := exists_pow_centralizes_T hD0fix hy 36 h36c
  refine ⟨j + 2, fun x hx => ?_⟩
  have h := hj x hx
  have hexp : 4 * 3 ^ (j + 2) = 36 * 3 ^ j := by
    rw [pow_succ, pow_succ]; ring
  rwa [hexp]

theorem glThreeAutFour_of_pow_thirtySix {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3)
    (h36 : ∀ {G : Type} [Group G] [Finite G] {D : Subgroup G}, (∀ x ∈ D, x ^ 3 = 1) →
      (∀ x ∈ D, ∀ x' ∈ D, ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set G)) →
      (Subgroup.centralizer (D : Set G)).relIndex D = 9 →
      ∀ {y : G}, y ∈ Subgroup.normalizer (D : Set G) →
      (∀ z ∈ D, z ∈ Subgroup.centralizer (D : Set G) → y * z = z * y) →
      ∀ x ∈ D, y ^ 36 * x = x * y ^ 36) :
    GLThreeAutFour q := by
  intro W _ _ _ hW T hT y hy
  classical
  by_cases hTbot : T = ⊥
  · refine ⟨0, ?_⟩
    intro x hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp (hTbot ▸ hx)
    simp [hx1]
  · haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTbot
    obtain ⟨D0, hD0char, hD0ne, hD0comm, hD0exp, hD0fix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := 3) (by norm_num) hT
    let D : Subgroup (Module.End (ZMod q) W)ˣ := D0.map T.subtype
    have hD : IsPGroup 3 D := hT.to_le (Subgroup.map_subtype_le D0)
    have hDexp : ∀ x ∈ D, x ^ 3 = 1 := critical_subgroup_exp hD0exp
    have hDcl : ∀ x ∈ D, ∀ x' ∈ D,
        ⁅x, x'⁆ ∈ Subgroup.centralizer (D : Set (Module.End (ZMod q) W)ˣ) :=
      critical_subgroup_centralizer hD0comm
    have hyD : y ∈ Subgroup.normalizer (D : Set (Module.End (ZMod q) W)ˣ) :=
      critical_subgroup_normalizer hD0char hy
    by_cases hDab : IsMulCommutative D
    · exact exists_pow_of_abelian hq3 hW hD0fix hy hDab hD hyD
    · exact exists_pow_of_nonabelian hq3 hW hD0fix hy hD hDexp hDcl hDab hyD h36


end CFSG.LocalAnalysis.RankThreeTheoremC.AutSectionThree
