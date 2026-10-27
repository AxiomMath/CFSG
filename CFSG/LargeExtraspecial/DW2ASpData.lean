module

public import CFSG.LargeExtraspecial.DW2AStruct

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_mem_of_not_mem_hyperplane [FiniteDimensional (ZMod 2) V] {W H : Submodule (ZMod 2) V}
    (hHW : H ≤ W) (hdim : finrank (ZMod 2) W ≤ finrank (ZMod 2) H + 1) {w w' : V} (hw : w ∈ W)
    (hw' : w' ∈ W) (hwH : w ∉ H) (hw'H : w' ∉ H) : w + w' ∈ H := by
  have hsup : H ⊔ ZMod 2 ∙ w = W := by
    refine Submodule.eq_of_le_of_finrank_le (sup_le hHW ?_) ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hw
    · rw [finrank_sup_span_singleton hwH]
      exact hdim
  rw [← hsup] at hw'
  obtain ⟨h, hh, f, hf, rfl⟩ := Submodule.mem_sup.mp hw'
  obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hf
  rcases zmod2_cases μ with rfl | rfl
  · rw [zero_smul, add_zero] at hw'H
    exact absurd hh hw'H
  · rw [one_smul, add_comm h w, ← add_assoc, add_self_zmod2, zero_add]
    exact hh

theorem ind_add [FiniteDimensional (ZMod 2) V] {W H : Submodule (ZMod 2) V} (hHW : H ≤ W)
    (hdim : finrank (ZMod 2) W ≤ finrank (ZMod 2) H + 1) {w w' : V} (hw : w ∈ W) (hw' : w' ∈ W)
    [Decidable (w ∈ H)] [Decidable (w' ∈ H)] [Decidable (w + w' ∈ H)] :
    (if w + w' ∈ H then (0 : ZMod 2) else 1) =
      (if w ∈ H then 0 else 1) + (if w' ∈ H then 0 else 1) := by
  by_cases h1 : w ∈ H <;> by_cases h2 : w' ∈ H
  · have h3 : w + w' ∈ H := H.add_mem h1 h2
    simp [h1, h2, h3]
  · have h3 : w + w' ∉ H := fun h => h2 (by
      have := H.sub_mem h h1
      rwa [add_sub_cancel_left] at this)
    simp [h1, h2, h3]
  · have h3 : w + w' ∉ H := fun h => h1 (by
      have := H.sub_mem h h2
      rwa [add_sub_cancel_right] at this)
    simp [h1, h2, h3]
  · have h3 : w + w' ∈ H := add_mem_of_not_mem_hyperplane hHW hdim hw hw' h1 h2
    simp only [h1, h2, h3, ↓reduceIte]
    rfl

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

section SpForm

variable (hWs : ∀ v ∈ spanD S, S.q v = 0)

@[expose] noncomputable def spRep (c : S.Qt) : G := by
  classical
  exact if h : c ∈ spanD S ∧ c ≠ 0 then (exists_conj_of_mem_spanD_ne hWs h.1 h.2).choose else 1

theorem spRep_spec {c : S.Qt} (hc : c ∈ spanD S) (hc0 : c ≠ 0) :
    spRep hWs c * S.z * (spRep hWs c)⁻¹ ∈ S.QG ∧ spRep hWs c * S.z * (spRep hWs c)⁻¹ ≠ S.z ∧
      S.cl (spRep hWs c * S.z * (spRep hWs c)⁻¹) = c := by
  have h : c ∈ spanD S ∧ c ≠ 0 := ⟨hc, hc0⟩
  simp only [spRep, h, ne_eq, not_false_eq_true, and_self, ↓reduceDIte]
  exact (exists_conj_of_mem_spanD_ne hWs h.1 h.2).choose_spec

@[expose] noncomputable def spFun (c w : S.Qt) : ZMod 2 := by
  classical
  exact if c = 0 then 0 else if w ∈ axisD S (spRep hWs c) then 0 else 1

variable {hWs} in
theorem spFun_zero_left (w : S.Qt) : spFun hWs 0 w = 0 := by
  simp [spFun]

variable {hWs} in
theorem spFun_eq_zero_iff {c w : S.Qt} (hc0 : c ≠ 0) :
    spFun hWs c w = 0 ↔ w ∈ axisD S (spRep hWs c) := by
  unfold spFun
  by_cases hw : w ∈ axisD S (spRep hWs c) <;> simp [hc0, hw]

variable (hSp : ∀ h : G, h * S.z * h⁻¹ ∈ S.QG → h * S.z * h⁻¹ ≠ S.z →
  finrank (ZMod 2) (spanD S) ≤ finrank (ZMod 2) (axisD S h) + 1)

include hSp in
theorem spFun_add_right {c w w' : S.Qt} (hc : c ∈ spanD S) (hw : w ∈ spanD S)
    (hw' : w' ∈ spanD S) : spFun hWs c (w + w') = spFun hWs c w + spFun hWs c w' := by
  classical
  by_cases hc0 : c = 0
  · rw [hc0, spFun_zero_left, spFun_zero_left, spFun_zero_left, add_zero]
  obtain ⟨h1, h2, -⟩ := spRep_spec hWs hc hc0
  have hle := axisD_le_spanD (S := S) (spRep hWs c)
  have hdim := hSp _ h1 h2
  simp only [spFun, hc0, ↓reduceIte]
  exact ind_add hle hdim hw hw'

theorem spFun_comm {c w : S.Qt} (hc : c ∈ spanD S) (hw : w ∈ spanD S) :
    spFun hWs c w = spFun hWs w c := by
  by_cases hc0 : c = 0
  · rw [hc0, spFun_zero_left]
    by_cases hw0 : w = 0
    · rw [hw0, spFun_zero_left]
    · exact ((spFun_eq_zero_iff hw0).mpr (zero_mem _)).symm
  by_cases hw0 : w = 0
  · rw [hw0, spFun_zero_left]
    exact (spFun_eq_zero_iff hc0).mpr (zero_mem _)
  obtain ⟨h1, h2, h3⟩ := spRep_spec hWs hc hc0
  obtain ⟨h1', h2', h3'⟩ := spRep_spec hWs hw hw0
  have key : w ∈ axisD S (spRep hWs c) ↔ c ∈ axisD S (spRep hWs w) := by
    have := cl_mem_axisD_comm h1 h2 h1' h2'
    rwa [h3, h3'] at this
  rcases zmod2_cases (spFun hWs c w) with h | h <;> rcases zmod2_cases (spFun hWs w c) with h' | h'
  · rw [h, h']
  · exfalso
    rw [spFun_eq_zero_iff hc0] at h
    have := (spFun_eq_zero_iff hw0).mpr (key.mp h)
    rw [this] at h'
    exact absurd h' (by decide)
  · exfalso
    rw [spFun_eq_zero_iff hw0] at h'
    have := (spFun_eq_zero_iff hc0).mpr (key.mpr h')
    rw [this] at h
    exact absurd h (by decide)
  · rw [h, h']

include hSp in
theorem spFun_add_left {c c' w : S.Qt} (hc : c ∈ spanD S) (hc' : c' ∈ spanD S)
    (hw : w ∈ spanD S) : spFun hWs (c + c') w = spFun hWs c w + spFun hWs c' w := by
  rw [spFun_comm hWs (add_mem hc hc') hw, spFun_add_right hWs hSp hw hc hc',
    spFun_comm hWs hw hc, spFun_comm hWs hw hc']

theorem spFun_self {c : S.Qt} (hc : c ∈ spanD S) : spFun hWs c c = 0 := by
  by_cases hc0 : c = 0
  · rw [hc0, spFun_zero_left]
  obtain ⟨h1, -, h3⟩ := spRep_spec hWs hc hc0
  rw [spFun_eq_zero_iff hc0]
  have := cl_mem_axisD_self h1
  rwa [h3] at this

@[expose] noncomputable def spForm : LinearMap.BilinForm (ZMod 2) (spanD S) :=
  LinearMap.mk₂ (ZMod 2) (fun c w => spFun hWs (c : S.Qt) (w : S.Qt))
    (fun c c' w => spFun_add_left hWs hSp c.2 c'.2 w.2)
    (fun a c w => by
      rcases zmod2_cases a with rfl | rfl
      · simp only [zero_smul, Submodule.coe_zero, spFun_zero_left, smul_eq_mul, zero_mul]
      · simp only [one_smul, smul_eq_mul, one_mul])
    (fun c w w' => spFun_add_right hWs hSp c.2 w.2 w'.2)
    (fun a c w => by
      rcases zmod2_cases a with rfl | rfl
      · simp only [zero_smul, Submodule.coe_zero, smul_eq_mul, zero_mul]
        rw [spFun_comm hWs c.2 (zero_mem _), spFun_zero_left]
      · simp only [one_smul, smul_eq_mul, one_mul])

theorem spForm_apply (c w : spanD S) : spForm hWs hSp c w = spFun hWs (c : S.Qt) (w : S.Qt) :=
  rfl

theorem spForm_isAlt : (spForm hWs hSp).IsAlt := fun c => spFun_self hWs c.2

include hSp in
theorem spForm_nondegenerate (hlt : finrank (ZMod 2) (spanD S) < S.width) :
    (spForm hWs hSp).Nondegenerate := by
  have hrefl : (spForm hWs hSp).IsRefl := (spForm_isAlt hWs hSp).isRefl
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr fun c hc => ?_
  by_contra hc0
  have hc0' : (c : S.Qt) ≠ 0 := fun h => hc0 (Subtype.ext h)
  obtain ⟨h1, h2, -⟩ := spRep_spec hWs c.2 hc0'
  apply axisD_ne_spanD hWs hlt h1 h2
  refine le_antisymm (axisD_le_spanD _) fun w hw => ?_
  have := hc ⟨w, hw⟩
  rw [spForm_apply] at this
  exact (spFun_eq_zero_iff hc0').mp this

end SpForm

end CFSG.LargeExtraspecial.DW
