module

public import CFSG.LargeExtraspecial.DWCaseIIBAxis
public import CFSG.LargeExtraspecial.DWCaseIIBForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

open Classical in
variable (S) in
@[expose] noncomputable def repD (c : S.Qt) : G :=
  if h : ∃ k : G, k * S.z * k⁻¹ ∈ S.QG ∧ k * S.z * k⁻¹ ≠ S.z ∧ S.cl (k * S.z * k⁻¹) = c then
    h.choose else 1

section Axes

variable (hWs : ∀ v ∈ spanD S, S.q v = 0)
include hWs

theorem repD_spec {c : S.Qt} (hc : c ∈ spanD S) (hc0 : c ≠ 0) :
    repD S c * S.z * (repD S c)⁻¹ ∈ S.QG ∧ repD S c * S.z * (repD S c)⁻¹ ≠ S.z ∧
      S.cl (repD S c * S.z * (repD S c)⁻¹) = c := by
  have h := exists_conj_of_mem_spanD_ne hWs hc hc0
  simp only [repD, h, ↓reduceDIte]
  exact h.choose_spec

variable (S) in
omit hWs in
@[expose] noncomputable def axisV (c : S.Qt) : Submodule (ZMod 2) S.Qt := axisD S (repD S c)

omit hWs [Finite G] in
theorem axisV_le (c : S.Qt) : axisV S c ≤ spanD S := axisD_le_spanD _

theorem axisV_cl {g : G} (hxQ : g * S.z * g⁻¹ ∈ S.QG) (hxz : g * S.z * g⁻¹ ≠ S.z) :
    axisV S (S.cl (g * S.z * g⁻¹)) = axisD S g := by
  have h0 : S.cl (g * S.z * g⁻¹) ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  obtain ⟨h1, h2, h3⟩ := repD_spec hWs (cl_conj_mem_spanD hxQ) h0
  exact axisD_eq_of_cl_eq hWs h1 h2 hxQ hxz h3

theorem mem_axisV_self {c : S.Qt} (hc : c ∈ spanD S) (hc0 : c ≠ 0) : c ∈ axisV S c := by
  obtain ⟨h1, -, h3⟩ := repD_spec hWs hc hc0
  have := cl_mem_axisD_self h1
  rwa [h3] at this

theorem mem_axisV_comm {c c' : S.Qt} (hc : c ∈ spanD S) (hc' : c' ∈ spanD S) (hc0 : c ≠ 0)
    (hc'0 : c' ≠ 0) : c' ∈ axisV S c ↔ c ∈ axisV S c' := by
  obtain ⟨h1, h2, h3⟩ := repD_spec hWs hc hc0
  obtain ⟨h1', h2', h3'⟩ := repD_spec hWs hc' hc'0
  have := cl_mem_axisD_comm h1 h2 h1' h2'
  rwa [h3, h3'] at this

theorem finrank_axisV_eq {c c' : S.Qt} (hc : c ∈ spanD S) (hc' : c' ∈ spanD S) (hc0 : c ≠ 0)
    (hc'0 : c' ≠ 0) : finrank (ZMod 2) (axisV S c) = finrank (ZMod 2) (axisV S c') := by
  obtain ⟨h1, h2, -⟩ := repD_spec hWs hc hc0
  obtain ⟨h1', h2', -⟩ := repD_spec hWs hc' hc'0
  exact finrank_axisD_eq hWs h1 h2 h1' h2'

theorem axisV_le_sup {c c' : S.Qt} (hc : c ∈ spanD S) (hc' : c' ∈ spanD S) (hc0 : c ≠ 0)
    (hc'0 : c' ≠ 0) (hnot : c' ∉ axisV S c) : axisV S c ≤ axisV S c' ⊔ ZMod 2 ∙ c := by
  obtain ⟨h1, h2, h3⟩ := repD_spec hWs hc hc0
  obtain ⟨h1', h2', h3'⟩ := repD_spec hWs hc' hc'0
  have := axisD_le_sup hWs h1 h2 h1' h2' (by rwa [h3'])
  rwa [h3] at this

theorem mem_axisV_ρ_iff (m : S.M) {c : S.Qt} (hc : c ∈ spanD S) (hc0 : c ≠ 0) (v : S.Qt) :
    ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ axisV S (((S.ρ m : S.O) :
      S.Qt ≃ₗ[ZMod 2] S.Qt) c) ↔ v ∈ axisV S c := by
  obtain ⟨h1, h2, h3⟩ := repD_spec hWs hc hc0
  set k := repD S c
  have hmk : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ = m * (k * S.z * k⁻¹) * (m : G)⁻¹ := by
    group
  have hmQ : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ S.QG := by
    rw [hmk]
    exact S.conj_mem_QG m.2 h1
  have hmcl : S.cl (((m : G) * k) * S.z * ((m : G) * k)⁻¹) =
      ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) c := by
    rw [hmk, ← S.ρ_cl m h1, h3]
  have hmz : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ≠ S.z := by
    rw [← cl_ne_zero_iff hmQ, hmcl]
    exact fun e => hc0 ((LinearEquiv.map_eq_zero_iff _).mp e)
  rw [← hmcl, axisV_cl hWs hmQ hmz, mem_axisD_mul_iff hWs h1 h2 m, ← LinearEquiv.mul_apply,
    ← Subgroup.coe_mul, ← map_mul, inv_mul_cancel, map_one]
  rfl

end Axes

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
  (hM : S.M ≤ normalizer (A : Set G))
  (hII : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A)
  (hbad : ∀ g : G, g * S.z * g⁻¹ ∈ A → g * S.z * g⁻¹ ≠ S.z → ¬ A ≤ S.Qa g)
include hA hM hII hbad

theorem axisV_ne {c : S.Qt} (hc : c ∈ spanD S) (hc0 : c ≠ 0) : axisV S c ≠ spanD S := by
  obtain ⟨h1, h2, -⟩ := repD_spec (q_spanD hII) hc hc0
  exact hA.axisD_ne_spanD hM hII (hII _ h1) h2 (hbad _ (hII _ h1) h2)

theorem finrank_axisD_le_one_or {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z) :
    finrank (ZMod 2) (axisD S g) ≤ 1 ∨
      finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S g) + 1 := by
  have := finiteDimensional_Qt (S := S)
  have hWs := q_spanD hII
  have hxQ := hA.le_QG hxA
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  have hxD := cl_conj_mem_spanD hxQ
  rw [← axisV_cl hWs hxQ hxz]
  refine finrank_le_one_or_add_one_ge (U := spanD S) (axisV S)
    (fun c hc hc0 => mem_axisV_self hWs hc hc0) (fun c _ _ => axisV_le c)
    (fun c hc hc0 => finrank_axisV_eq hWs hc hxD hc0 hx0)
    (fun c hc c' hc' hc0 hc'0 => mem_axisV_comm hWs hc hc' hc0 hc'0)
    (fun c hc c' hc' hc0 hc'0 hnot => axisV_le_sup hWs hc hc' hc0 hc'0 hnot) ?_
  exact Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne (axisV_le _) (hA.axisV_ne hM hII hbad hxD hx0))

theorem isHypFamily_axisV {g : G} (hxA : g * S.z * g⁻¹ ∈ A) (hxz : g * S.z * g⁻¹ ≠ S.z)
    (hhyp : finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S g) + 1) :
    IsHypFamily (spanD S) (axisV S) := by
  have := finiteDimensional_Qt (S := S)
  have hWs := q_spanD hII
  have hxQ := hA.le_QG hxA
  have hx0 : S.cl (g * S.z * g⁻¹) ≠ 0 := (cl_ne_zero_iff hxQ).mpr hxz
  have hxD := cl_conj_mem_spanD hxQ
  have hdim : ∀ c ∈ spanD S, c ≠ 0 →
      finrank (ZMod 2) (axisV S c) + 1 = finrank (ZMod 2) (spanD S) := by
    intro c hc hc0
    have h1 := finrank_axisV_eq hWs hc hxD hc0 hx0
    rw [axisV_cl hWs hxQ hxz] at h1
    have h2 := Submodule.finrank_lt_finrank_of_lt
      (lt_of_le_of_ne (axisV_le c) (hA.axisV_ne hM hII hbad hc hc0))
    omega
  refine ⟨fun c hc hc0 => mem_axisV_self hWs hc hc0, fun c hc hc0 => ?_,
    fun c hc hc0 u hu u' hu' h1 h2 =>
      add_mem_of_finrank_add_one (axisV_le c) (hdim c hc hc0) hu hu' h1 h2,
    fun c hc c' hc' hc0 hc'0 => mem_axisV_comm hWs hc hc' hc0 hc'0⟩
  obtain ⟨u, hu, hu'⟩ := IsConcreteLE.exists_of_lt
    (lt_of_le_of_ne (axisV_le c) (hA.axisV_ne hM hII hbad hc hc0))
  exact ⟨u, hu, hu'⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
