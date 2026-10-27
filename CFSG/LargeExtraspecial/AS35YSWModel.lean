module

public import Certificates.Certificate21201
public import CFSG.GH74.KGroups.U33
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LargeExtraspecial.AS35YS

open Subgroup CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

theorem u33ElemCheck_sound
    {d : Equiv.Perm (Fin 28)} (hd : d ∈ QP.originalSubgroup) (hdd : d * d = 1) (hd1 : d ≠ 1)
    {e : Equiv.Perm (Fin 28)} (he : e ∈ QA.originalSubgroup) (hee : e * e = 1) (he1 : e ≠ 1)
    (hed : e ≠ d) (hc : e * d = d * e) :
    ∃ c ∈ QP.originalSubgroup, c * d = d * c ∧ e * (c * e * c⁻¹) ≠ c * e * c⁻¹ * e := by
  have hch := Certificates.certificate21201
  unfold u33ElemCheck at hch
  have h := forall_of_all QP QP_ok hch d hd
  have h1 : (d * d == 1) = true := beq_iff_eq.mpr hdd
  have h2 : (d == 1) = false := beq_eq_false_iff_ne.mpr hd1
  rw [h1, h2, Bool.not_true, Bool.false_or, Bool.false_or] at h
  have h3 := forall_of_all QA QA_ok h e he
  have h4 : (e * e == 1) = true := beq_iff_eq.mpr hee
  have h5 : (e == 1) = false := beq_eq_false_iff_ne.mpr he1
  have h6 : (e == d) = false := beq_eq_false_iff_ne.mpr hed
  have h7 : (e * d == d * e) = true := beq_iff_eq.mpr hc
  rw [h4, h5, h6, h7, Bool.not_true, Bool.false_or, Bool.false_or, Bool.false_or,
    Bool.false_or] at h3
  obtain ⟨c, hcm, hcc⟩ := List.any_eq_true.mp h3
  rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hcc
  exact ⟨c, (mem_elemsT QP QP_ok c).mp hcm, hcc.1, hcc.2⟩

theorem QP_le_QA : QP.originalSubgroup ≤ QA.originalSubgroup := by
  have hA : QA.originalSubgroup = closure {g | g ∈ [pa, pb, sg0]} := by
    rw [QA, certificate_originalSubgroup]
  rw [QP_closure, closure_le, hA]
  rintro x (rfl | rfl)
  · exact subset_closure (by simp)
  · exact subset_closure (by simp)

theorem eq_one_of_commute_QP {σ : Equiv.Perm (Fin 28)}
    (hσ : σ ∈ QA.originalSubgroup) (hc : ∀ x ∈ QP.originalSubgroup, σ * x = x * σ) : σ = 1 := by
  obtain ⟨-, -, -, ⟨hu, hv, -, -⟩, -, -, -, -, -, -, -, -, -, -, hcent, -⟩ :=
    Certificates.certificate5133
  rw [QA_closure] at hσ
  rw [QP_closure] at hc
  exact hcent σ hσ (hc pu hu) (hc pv hv)

theorem Φ_conj_eq {K : Type*} [Group K]
    (M : AutModel K (Equiv.Perm (Fin 28))) (hP : M.P = QP.originalSubgroup)
    (hA : M.A = QA.originalSubgroup) (k : K) :
    (M.Φ (MulAut.conj k) : Equiv.Perm (Fin 28)) = M.e k := by
  set φ : Equiv.Perm (Fin 28) := ↑(M.Φ (MulAut.conj k)) with hφ
  set ε : Equiv.Perm (Fin 28) := ↑(M.e k) with hε
  have hεA : ε ∈ QA.originalSubgroup := QP_le_QA ((Subgroup.ext_iff.mp hP _).mp (M.e k).2)
  have hφA : φ ∈ QA.originalSubgroup := (Subgroup.ext_iff.mp hA _).mp (M.Φ (MulAut.conj k)).2
  have hσA : ε⁻¹ * φ ∈ QA.originalSubgroup :=
    QA.originalSubgroup.mul_mem (QA.originalSubgroup.inv_mem hεA) hφA
  have hc : ∀ x ∈ QP.originalSubgroup, ε⁻¹ * φ * x = x * (ε⁻¹ * φ) := by
    intro x hx
    rw [← hP] at hx
    obtain ⟨y, hy⟩ := M.e.surjective ⟨x, hx⟩
    have hx' : (M.e y : Equiv.Perm (Fin 28)) = x := congrArg Subtype.val hy
    have hspec := M.spec (MulAut.conj k) y
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hx'] at hspec
    calc ε⁻¹ * φ * x = ε⁻¹ * (φ * x * φ⁻¹) * φ := by group
      _ = ε⁻¹ * (ε * x * ε⁻¹) * φ := by rw [← hspec]
      _ = x * (ε⁻¹ * φ) := by group
  have h1 := eq_one_of_commute_QP hσA hc
  calc φ = ε * (ε⁻¹ * φ) := by group
    _ = ε := by rw [h1, mul_one]

variable {O : Type*} [Group O]

theorem le_zpowers_of_model
    {M₀ L₀ : Subgroup O} (hLM : L₀ ≤ M₀) (ι : M₀ →* Equiv.Perm (Fin 28))
    (hι : Function.Injective ι) (hιA : ∀ m : M₀, ι m ∈ QA.originalSubgroup)
    (hιL : ∀ (l : O) (hl : l ∈ L₀), ι ⟨l, hLM hl⟩ ∈ QP.originalSubgroup)
    (hιP : ∀ p ∈ QP.originalSubgroup, ∃ (l : O) (hl : l ∈ L₀), ι ⟨l, hLM hl⟩ = p)
    {d : O} (hdL : d ∈ L₀) (hdd : d * d = 1) (hd1 : d ≠ 1) (U : Subgroup O) (hUM : U ≤ M₀)
    (hU2 : ∀ u ∈ U, u * u = 1) (hdU : d ∈ U)
    (hUn : ∀ c ∈ M₀, c * d = d * c → ∀ u ∈ U, c * u * c⁻¹ ∈ U) : U ≤ zpowers d := by
  have hab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
    intro a ha b hb
    have e1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (hU2 _ (U.mul_mem ha hb))
    have e2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hU2 a ha)
    have e3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hU2 b hb)
    rw [← e1, mul_inv_rev, e2, e3]
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1]
    exact one_mem _
  by_cases hud : u = d
  · rw [hud]
    exact mem_zpowers d
  exfalso
  set dm : M₀ := ⟨d, hLM hdL⟩ with hdm
  set um : M₀ := ⟨u, hUM hu⟩ with hum
  have hmul : ∀ a b : M₀, ι a * ι b = ι (a * b) := fun a b => (map_mul ι a b).symm
  have hdd' : ι dm * ι dm = 1 := by
    rw [hmul, show dm * dm = 1 from Subtype.ext hdd, map_one]
  have hd1' : ι dm ≠ 1 := fun h => hd1 (congrArg Subtype.val (hι (h.trans (map_one ι).symm)))
  have huu' : ι um * ι um = 1 := by
    rw [hmul, show um * um = 1 from Subtype.ext (hU2 u hu), map_one]
  have hu1' : ι um ≠ 1 := fun h => hu1 (congrArg Subtype.val (hι (h.trans (map_one ι).symm)))
  have hud' : ι um ≠ ι dm := fun h => hud (congrArg Subtype.val (hι h))
  have hc' : ι um * ι dm = ι dm * ι um := by
    rw [hmul, hmul, show um * dm = dm * um from Subtype.ext (hab u hu d hdU)]
  obtain ⟨c, hcP, hcd, hce⟩ :=
    u33ElemCheck_sound (hιL d hdL) hdd' hd1' (hιA um) huu' hu1' hud' hc'
  obtain ⟨l, hl, hlc⟩ := hιP c hcP
  set lm : M₀ := ⟨l, hLM hl⟩ with hlm
  have hld : l * d = d * l := by
    have h1 : ι (lm * dm) = ι (dm * lm) := by
      rw [map_mul, map_mul, hlc]
      exact hcd
    exact congrArg Subtype.val (hι h1)
  have hlu := hUn l (hLM hl) hld u hu
  have hcomm := hab u hu _ hlu
  apply hce
  have h2 : um * (lm * um * lm⁻¹) = lm * um * lm⁻¹ * um := Subtype.ext hcomm
  have h3 := congrArg ι h2
  simp only [map_mul, map_inv, hlc] at h3
  exact h3

end CFSG.LargeExtraspecial.AS35YS
