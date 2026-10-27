module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7End1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Tab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Final
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec710Mod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem z4pow4_coord (x : Multiplicative (ZMod 4)) : x ^ 4 = 1 := by
  revert x
  decide

theorem z4Pow4_pow_four (u : Z4Pow4) : u ^ 4 = 1 := by
  funext i
  exact z4pow4_coord (u i)

theorem sec711_exp_of_equiv {U : Subgroup G} (e : ↥U ≃* Z4Pow4) : ∀ x ∈ U, x ^ 4 = 1 := by
  intro x hx
  have h1 : e (⟨x, hx⟩ ^ 4) = 1 := by
    rw [map_pow, z4Pow4_pow_four]
  have h2 : (⟨x, hx⟩ : ↥U) ^ 4 = 1 := e.map_eq_one_iff.mp h1
  simpa using congrArg Subtype.val h2

theorem sec711_comm_of_equiv {U : Subgroup G} (e : ↥U ≃* Z4Pow4) :
    ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
  intro x hx y hy
  have h : (⟨x, hx⟩ : ↥U) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
    apply e.injective
    rw [map_mul, map_mul, mul_comm]
  simpa using Subtype.ext_iff.mp h

theorem sec711_exists_b [Finite G] (h36 : Asc82Lemma36) (h75b : Asc82Lemma75b)
    (hP7 : Asc82Tab7P) {t : G} {L S : Subgroup G} {z g : G} {B : Subgroup G}
    (hc : Sec7Choice G t L S z g B) : ∃ b ∈ B, b ≠ 1 ∧ InducesTypeSome L b 6 1 2 (-1) := by
  obtain ⟨φ, hφ⟩ := (h75b G t L S z hc.ctx B hc.normalE16).2.2.1
  let v : Fin 5 → ZMod 2 := ![1, 1, 0, 0, 0]
  have hv : IsEvenVec v := by unfold IsEvenVec; decide
  have hw : vecWeight v = 2 := by unfold vecWeight; decide
  have hze : IsEvenVec (0 : Fin 5 → ZMod 2) := by unfold IsEvenVec; simp
  refine ⟨φ v, (hφ.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩, ?_, ?_⟩
  · intro h0
    have heq : φ v = φ 0 := by rw [h0, sec710_map_zero hφ]
    have hvz : v = 0 := hφ.2.1 v 0 hv hze heq
    have h10 : v 0 = 0 := by rw [hvz]; rfl
    have hv0 : v 0 = 1 := by simp [v]
    rw [hv0] at h10
    exact one_ne_zero h10
  · exact (hP7.aut_B_types G L hc.ctx.isOm6P (S ⊓ L) (hc.ctx.isSylow2Of_inf h36) B
      hc.normalE16 φ hφ).1 v hv hw

theorem sec711_false [Finite G] (h36 : Asc82Lemma36) (h35 : Asc82Lemma35)
    (h75b : Asc82Lemma75b) (hP : Asc82Tab6P) (hM : Asc82Tab6M) (hF : Asc82AutFacts)
    (hP7 : Asc82Tab7P) (hE : Asc82Final7E) (hPr : Asc82Final7Prince) (hY : Asc82Final7Y)
    (hAb : Asc82AbelAutBound) {t : G} {L S : Subgroup G} {z g : G}
    {B : Subgroup G} (hc : Sec7Choice G t L S z g B) : False := by
  obtain ⟨E, U, hU⟩ := hE G t L S z g B hc
  obtain ⟨b, hbB, hb1, hbtype⟩ := sec711_exists_b h36 h75b hP7 hc
  obtain ⟨Y, hYcomp, hYnorm, hYF, hYC, hlay, hYtype, hEY, hCA, hcyc⟩ :=
    hY G t L S z g B E U hU b hbB hb1 hbtype
  by_cases h6m : IsOmega6Minus Y
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hb2 : orderOf b = 2 := orderOf_eq_prime (hc.normalE16.2.1.1.2 b hbB) hb1
    exact sec711_not_omega6Minus h36 h35 hP hM hF hc.ctx hb2 (hc.normalE16.1 hbB).2 hbtype
      hYcomp hYnorm hYF hlay h6m
  have hQ : IsQuasisimple Y := hYcomp.isQuasisimple
  have hUE : U ≤ E := hU.le
  have hU2 : IsPGroup 2 U := hU.hE.sylow.2.1.to_le hUE
  have hUN : U ≤ normalizer (Y : Set G) := hUE.trans hEY
  have hcard : Nat.card U = 2 ^ 8 := hU.card
  rcases hPr G t L S z g B E U hU with hel | he4
  · haveI : IsMulCommutative ↥U := hel.1.1
    have hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
      Subgroup.mul_comm_of_mem_isMulCommutative (H := U) hx hy
    have hcommAut : ∀ a ∈ autIn U Y, ∀ b ∈ autIn U Y, a * b = b * a :=
      sec7End_autIn_comm hcommU
    have hAb' := hAb G Y U hQ hUN hU2 hcommAut
    have hle := sec7End_card_le_mul hUE hEY hcyc (n := 2) (by norm_num) hel.1.2
    norm_num at hle
    rcases hYtype with h | h | h | h
    · exact absurd (hAb'.1 h) (by omega)
    · exact absurd (hAb'.2.2 h) (by omega)
    · exact absurd h h6m
    · exact absurd (hAb'.2.1 h) (by omega)
  · obtain ⟨e4⟩ := he4
    have hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := sec711_comm_of_equiv e4
    have hcommAut : ∀ a ∈ autIn U Y, ∀ b ∈ autIn U Y, a * b = b * a :=
      sec7End_autIn_comm hcommU
    have hAb' := hAb G Y U hQ hUN hU2 hcommAut
    have hle := sec7End_card_le_mul hUE hEY hcyc (n := 4) (by norm_num)
      (sec711_exp_of_equiv e4)
    norm_num at hle
    rcases hYtype with h | h | h | h
    · exact absurd (hAb'.1 h) (by omega)
    · exact absurd (hAb'.2.2 h) (by omega)
    · exact absurd h h6m
    · exact absurd (hAb'.2.1 h) (by omega)

end CFSG.OddStandard.SmallF3.Omega