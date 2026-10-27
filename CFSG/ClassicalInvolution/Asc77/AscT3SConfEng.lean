module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIClose

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Triple

variable {G : Type} [Group G]

theorem closure_pair_cases {z t x : G} (hz : z * z = 1) (ht : t * t = 1) (hzt : z * t = t * z)
    (hx : x ∈ Subgroup.closure ({z, t} : Set G)) : x = 1 ∨ x = z ∨ x = t ∨ x = z * t := by
  have hcl : Subgroup.closure ({z, t} : Set G) = Subgroup.zpowers z ⊔ Subgroup.zpowers t := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have hcomm : Commutes (Subgroup.zpowers z) (Subgroup.zpowers t) := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_zpow (show Commute z t from hzt) i j)).eq
  rw [hcl] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcomm hx
  rcases eq_one_or_eq_of_mem_zpowers hz ha with h1 | h1 <;>
    rcases eq_one_or_eq_of_mem_zpowers ht hb with h2 | h2
  · left; rw [h1, h2, one_mul]
  · right; right; left; rw [h1, h2, one_mul]
  · right; left; rw [h1, h2, mul_one]
  · right; right; right; rw [h1, h2]

end Triple

section ConfEngine

variable {G : Type} [Group G] [Finite G] {K K' J : Subgroup G} {S : Sylow 2 G} {z t : G}

theorem s_a_not_mem_closure_of (hzK : IsUniqueInvolution K z) (ht2 : t * t = 1)
    (hzt : z * t = t * z) (htor : ∃ r ∈ K, r ∈ (S : Subgroup G) ∧ r * t * r⁻¹ = z * t)
    (c4 : Concl20_4 S K K' J z) {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) (ha1 : a ≠ 1) :
    a ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hmem
  have hA : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') := ha.1
  have hz2 : z * z = 1 := hzK.sq
  obtain ⟨r, hrK, hrS, hrt⟩ := htor
  have hrM : r ∈ K ⊔ K' := Subgroup.mem_sup_left hrK
  have har : a * r = r * a := commutes_of_mem_centModOddCore S.isPGroup'
    (mem_centModOddCore_of_mem_centralizerModOdd hA) hA.1 hrM hrS
  have hrz : r * z = z * r := (hzK.commute_of_mem hrK).symm
  rcases closure_pair_cases hz2 ht2 hzt hmem with h | h | h | h
  · exact ha1 h
  · exact ha1 ((Subgroup.disjoint_def.mp c4.2) ha (h ▸ Subgroup.mem_zpowers z))
  · subst h
    have h1 : r * a * r⁻¹ = a := mul_inv_eq_iff_eq_mul.mpr har.symm
    rw [hrt] at h1
    exact hzK.ne_one (mul_eq_right.mp h1)
  · subst h
    have h1 : r * (z * t) * r⁻¹ = z * t := mul_inv_eq_iff_eq_mul.mpr har.symm
    have h2 : r * (z * t) * r⁻¹ = t := by
      calc r * (z * t) * r⁻¹ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
        _ = z * (z * t) := by rw [hrt, show r * z * r⁻¹ = z by rw [hrz]; group]
        _ = t := by rw [← mul_assoc, hz2, one_mul]
    rw [h2] at h1
    exact hzK.ne_one (mul_eq_right.mp h1.symm)

theorem comm_mem_oddCoreOf_of {M : Subgroup G} (hM : M ≤ K ⊔ K') {a : G}
    (hA : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K'))
    (haN : a ∈ Subgroup.normalizer (M : Set G)) {k : G} (hk : k ∈ M) : ⁅a, k⁆ ∈ oddCoreOf M := by
  have h1 : ⁅a, k⁆ ∈ oddCoreOf (K ⊔ K') := hA.2.2.2 k (hM hk)
  have h2 : ⁅a, k⁆ ∈ M := by
    have e : ⁅a, k⁆ = (a * k * a⁻¹) * k⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact M.mul_mem ((Subgroup.mem_normalizer_iff.mp haN k).mp hk) (M.inv_mem hk)
  exact oddCoreOf_inf_le hM ⟨h1, h2⟩

end ConfEngine

end CFSG.ClassicalInvolution.Asc77.T3CII
