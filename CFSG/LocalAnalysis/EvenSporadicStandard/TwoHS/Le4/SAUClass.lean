module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUE1

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f s y n : G} {S₀ : Subgroup G}

@[expose] def Cl16 (C : ECoord G) (f w : G) : Prop :=
  ∀ m : G, m * f ^ 2 = f ^ 2 * m → m ∈ normalizer (C.E : Set G) →
    ∃ e ∈ C.E, e * e = 1 ∧ m * w * m⁻¹ = w * e

namespace Sect8Hyp

variable {C : ECoord G} (h : Sect8Hyp C f n S₀)
include h

theorem inv_of_mat_neg {x : G} (hx : x ∈ normalizer (C.E : Set G)) (hxm : C.mat x = -1) {e : G}
    (he : e ∈ C.E) : x * e * x⁻¹ = e⁻¹ := by
  have := C.conj_elt hx (C.vec e)
  rw [C.elt_vec he, hxm, neg_mulVec, one_mulVec, C.elt_neg, C.elt_vec he] at this
  exact this

theorem inv_conj_of_mat_neg {x : G} (hx : x ∈ normalizer (C.E : Set G)) (hxm : C.mat x = -1)
    {e : G} (he : e ∈ C.E) : x⁻¹ * e * x = e⁻¹ := by
  have he' : x⁻¹ * e * x ∈ C.E := by
    have := (mem_normalizer_iff.1 (inv_mem hx) e).1 he
    simpa using this
  have h1 := inv_of_mat_neg h hx hxm he'
  have h2 : x * (x⁻¹ * e * x) * x⁻¹ = e := by group
  rw [h2] at h1
  have h3 : e⁻¹ = x⁻¹ * e * x := by simpa using congrArg (·⁻¹) h1
  exact h3.symm

theorem mul_self_of_comm {x : G} (hx : x ∈ normalizer (C.E : Set G)) (hxm : C.mat x = -1)
    {e : G} (he : e ∈ C.E) (hc : x * e = e * x) : e * e = 1 := by
  have h1 := inv_of_mat_neg h hx hxm he
  have h2 : x * e * x⁻¹ = e := by
    calc x * e * x⁻¹ = e * x * x⁻¹ := by rw [hc]
      _ = e := by group
  rw [h2] at h1
  exact (congrArg (e * ·) h1).trans (mul_inv_cancel e)

theorem mat_neg_of_comm {sl : List M4} (hU : UFactsOf sl) {w : G}
    (hwn : w ∈ normalizer (C.E : Set G)) (hws : C.mat w ∈ sl) (hwE : w ∉ C.E)
    (hcomm : ∀ a ∈ C.E, a * a = 1 → w * a = a * w) : C.mat w = -1 := by
  have hker : ∀ v : V4, v + v = 0 → C.mat w *ᵥ v = v := by
    intro v hv
    have haE := C.elt_mem v
    have haa : C.elt v * C.elt v = 1 := by rw [← C.elt_add, hv, C.elt_zero]
    have h1 := hcomm _ haE haa
    have h2 : w * C.elt v * w⁻¹ = C.elt v := by
      calc w * C.elt v * w⁻¹ = (C.elt v * w) * w⁻¹ := by rw [h1]
        _ = C.elt v := by group
    rw [C.conj_elt hwn] at h2
    exact C.elt_injective h2
  rcases hU.ker _ hws hker with h1 | h1
  · exact absurd (h.mem_E_of_mat_eq_one hwn h1) hwE
  · exact h1

theorem exists_central_lift (hQ : Q0Facts) {x : G} (hx : x ∈ normalizer (C.E : Set G))
    (hxm : C.mat x = -1) (hcl : Cl16 C f x) {B : M4} (hB : B ∈ q0List) :
    ∃ c : G, c * f ^ 2 = f ^ 2 * c ∧ c ∈ normalizer (C.E : Set G) ∧ C.mat c = B ∧
      c * x = x * c := by
  obtain ⟨m, hmc, hmn, hmB⟩ := h.actN' B hB
  obtain ⟨ε, hεE, hεε, hmx⟩ := hcl m hmc hmn
  obtain ⟨e, heE, hee⟩ := exists_sqrt h hQ hεE hεε
  have hen : e ∈ normalizer (C.E : Set G) := le_normalizer heE
  refine ⟨e * m, ?_, mul_mem hen hmn, ?_, ?_⟩
  · have hf2E : f ^ 2 ∈ C.E := pow_mem h.f_mem 2
    have hc : e * f ^ 2 = f ^ 2 * e := C.comm heE hf2E
    calc e * m * f ^ 2 = e * (m * f ^ 2) := by rw [mul_assoc]
      _ = e * (f ^ 2 * m) := by rw [hmc]
      _ = (e * f ^ 2) * m := by rw [mul_assoc]
      _ = f ^ 2 * (e * m) := by rw [hc, mul_assoc]
  · rw [C.mat_mul hen hmn, hmB, (C.mat_eq_one_iff hen).2 (fun a ha => C.comm heE ha), one_mul]
  · have hxi := inv_conj_of_mat_neg h hx hxm heE
    have hmx' : m * x = x * ε * m := by
      calc m * x = (m * x * m⁻¹) * m := by group
        _ = x * ε * m := by rw [hmx]
    have hex : e * x = x * e⁻¹ := by
      calc e * x = x * (x⁻¹ * e * x) := by group
        _ = x * e⁻¹ := by rw [hxi]
    calc e * m * x = e * (m * x) := by rw [mul_assoc]
      _ = e * (x * ε * m) := by rw [hmx']
      _ = (e * x) * ε * m := by group
      _ = (x * e⁻¹) * (e * e) * m := by rw [hex, hee]
      _ = x * (e * m) := by group

theorem cent_le_H1 (H : Sect7Hyps G L f s y S₀ n) (hQ : Q0Facts) (hU : UFactsQ) {x : G}
    (hx : x ∈ normalizer (C.E : Set G)) (hxm : C.mat x = -1) (hxH : x ∈ L ⊔ zpowers y)
    (hcl : Cl16 C f x) {c : G} (hcc : c * f ^ 2 = f ^ 2 * c)
    (hcn : c ∈ normalizer (C.E : Set G)) (hcx : c * x = x * c) : c ∈ L ⊔ zpowers y := by
  have hB : C.mat c ∈ q0List := h.actN c hcc hcn
  obtain ⟨A₁, hA₁, A₂, hA₂, hAB⟩ := hU.sqprod _ hB
  obtain ⟨c₁, hc₁c, hc₁n, hc₁m, hc₁x⟩ := exists_central_lift h hQ hx hxm hcl hA₁
  obtain ⟨c₂, hc₂c, hc₂n, hc₂m, hc₂x⟩ := exists_central_lift h hQ hx hxm hcl hA₂
  have hdL : c₁ * c₁ * (c₂ * c₂) ∈ L :=
    L.mul_mem (SAU.sq_mem_L H hc₁c) (SAU.sq_mem_L H hc₂c)
  have hdn : c₁ * c₁ * (c₂ * c₂) ∈ normalizer (C.E : Set G) :=
    mul_mem (mul_mem hc₁n hc₁n) (mul_mem hc₂n hc₂n)
  have hdm : C.mat (c₁ * c₁ * (c₂ * c₂)) = A₁ * A₁ * (A₂ * A₂) := by
    rw [C.mat_mul (mul_mem hc₁n hc₁n) (mul_mem hc₂n hc₂n), C.mat_mul hc₁n hc₁n,
      C.mat_mul hc₂n hc₂n, hc₁m, hc₂m]
  have hdx : Commute (c₁ * c₁ * (c₂ * c₂)) x :=
    ((show Commute c₁ x from hc₁x).mul_left hc₁x).mul_left
      ((show Commute c₂ x from hc₂x).mul_left hc₂x)
  have key : ∀ d' : G, d' ∈ normalizer (C.E : Set G) → C.mat d' = C.mat c → Commute d' x →
      d' ∈ L ⊔ zpowers y → c ∈ L ⊔ zpowers y := by
    intro d' hd'n hd'm hd'x hd'H
    have hq : c * d'⁻¹ ∈ normalizer (C.E : Set G) := mul_mem hcn (inv_mem hd'n)
    have hqm : C.mat (c * d'⁻¹) = 1 := by
      rw [C.mat_mul hcn (inv_mem hd'n), ← hd'm, C.mat_mul_inv hd'n]
    have hqE : c * d'⁻¹ ∈ C.E := h.mem_E_of_mat_eq_one hq hqm
    have hqx : Commute (c * d'⁻¹) x :=
      (show Commute c x from hcx).mul_left (hd'x.inv_left)
    have hqq : (c * d'⁻¹) * (c * d'⁻¹) = 1 := mul_self_of_comm h hx hxm hqE hqx.eq.symm
    have hqL : c * d'⁻¹ ∈ L := E1_le_L h hQ H hU (inv_mem_E1sub h hQ hqE hqq)
    have : c = (c * d'⁻¹) * d' := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hqL) hd'H
  rcases hAB with h1 | h1
  · exact key _ hdn (by rw [hdm, h1]) hdx (Subgroup.mem_sup_left hdL)
  · refine key (x * (c₁ * c₁ * (c₂ * c₂))) (mul_mem hx hdn) ?_ ?_
      (mul_mem hxH (Subgroup.mem_sup_left hdL))
    · rw [C.mat_mul hx hdn, hxm, hdm, neg_one_mul, ← h1]
    · exact (Commute.refl x).mul_left hdx

theorem uniq_Cl16 (H : Sect7Hyps G L f s y S₀ n) (hQ : Q0Facts) (hU : UFactsQ) {w w' : G}
    (hw : w ∈ normalizer (C.E : Set G)) (hwm : C.mat w = -1) (hwH : w ∈ L ⊔ zpowers y)
    (hwcl : Cl16 C f w) (hw' : w' ∈ normalizer (C.E : Set G)) (hw'm : C.mat w' = -1)
    (hw'H : w' ∈ L ⊔ zpowers y) (hw'cl : Cl16 C f w') :
    ∃ e ∈ C.E, e * e = 1 ∧ w' = w * e := by
  have hwinv : C.mat w⁻¹ = -1 := by
    calc C.mat w⁻¹ = C.mat w⁻¹ * (C.mat w * C.mat w) := by
          rw [hwm]; simp
      _ = (C.mat w⁻¹ * C.mat w) * C.mat w := by rw [mul_assoc]
      _ = -1 := by rw [ECoord.mat_inv_mul hw, one_mul, hwm]
  have heE : w⁻¹ * w' ∈ C.E := by
    refine h.mem_E_of_mat_eq_one (mul_mem (inv_mem hw) hw') ?_
    rw [C.mat_mul (inv_mem hw) hw', hwinv, hw'm]
    simp
  have heH : w⁻¹ * w' ∈ L ⊔ zpowers y := mul_mem (inv_mem hwH) hw'H
  have heE1 := mem_E1sub_of_mem_H1 h hQ H hU heE heH
  have hev := ((C.mem_E1sub_iff_vec hQ).1 heE1).2
  refine ⟨w⁻¹ * w', heE, ?_, by group⟩
  rw [C.mul_self_eq_one_iff' heE]
  refine hU.uniq _ hev (fun A hA => ?_)
  obtain ⟨m, hmc, hmn, hmA⟩ := h.actN' A hA
  obtain ⟨ε, hεE, hεε, hmw⟩ := hwcl m hmc hmn
  obtain ⟨ε', hε'E, hε'ε', hmw'⟩ := hw'cl m hmc hmn
  have hmeE : m * (w⁻¹ * w') * m⁻¹ ∈ C.E := (mem_normalizer_iff.1 hmn _).1 heE
  have h1 : w * ε * (m * (w⁻¹ * w') * m⁻¹) = w * (w⁻¹ * w') * ε' := by
    calc w * ε * (m * (w⁻¹ * w') * m⁻¹) = (m * w * m⁻¹) * (m * (w⁻¹ * w') * m⁻¹) := by
          rw [← hmw]
      _ = m * w' * m⁻¹ := by group
      _ = w' * ε' := hmw'
      _ = w * (w⁻¹ * w') * ε' := by group
  have h2 : ε * (m * (w⁻¹ * w') * m⁻¹) = (w⁻¹ * w') * ε' := by
    refine mul_left_cancel (a := w) ?_
    calc w * (ε * (m * (w⁻¹ * w') * m⁻¹)) = w * ε * (m * (w⁻¹ * w') * m⁻¹) :=
          (mul_assoc _ _ _).symm
      _ = w * (w⁻¹ * w') * ε' := h1
      _ = w * ((w⁻¹ * w') * ε') := mul_assoc _ _ _
  have h3 := congrArg C.vec h2
  rw [C.vec_mul hεE hmeE, C.vec_mul heE hε'E, C.vec_conj hmn heE, hmA] at h3
  have hεv := (C.mul_self_eq_one_iff' hεE).1 hεε
  have hε'v := (C.mul_self_eq_one_iff' hε'E).1 hε'ε'
  have h4 : A *ᵥ C.vec (w⁻¹ * w') - C.vec (w⁻¹ * w') = C.vec ε' - C.vec ε := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (A *ᵥ C.vec (w⁻¹ * w')) (C.vec ε), h3, add_comm]
  calc (A *ᵥ C.vec (w⁻¹ * w') - C.vec (w⁻¹ * w')) + (A *ᵥ C.vec (w⁻¹ * w') - C.vec (w⁻¹ * w'))
      = (C.vec ε' - C.vec ε) + (C.vec ε' - C.vec ε) := by rw [h4]
    _ = (C.vec ε' + C.vec ε') - (C.vec ε + C.vec ε) := by abel
    _ = 0 := by rw [hε'v, hεv, sub_zero]

end Sect8Hyp

end CFSG.EvenSporadicStandard.TwoHS
