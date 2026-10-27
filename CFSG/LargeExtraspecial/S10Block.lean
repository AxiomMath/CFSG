module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S7Perm

public section

namespace CFSG.LargeExtraspecial.S10

open Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
theorem add_self_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  exact (show (2 : ZMod 2) = 0 from rfl) ▸ zero_smul (ZMod 2) v

omit [FiniteDimensional (ZMod 2) V] in
theorem sub_eq_add_zmod2 (v w : V) : v - w = v + w := by
  rw [sub_eq_iff_eq_add, add_assoc, add_self_zmod2, add_zero]

theorem finrank_map_add_finrank_inf_ker (f : V →ₗ[ZMod 2] V) (U : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (U.map f) + finrank (ZMod 2) ↥(U ⊓ LinearMap.ker f) =
      finrank (ZMod 2) U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  rw [← h1, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem half_dim (D T : V →ₗ[ZMod 2] V) (hD3 : ∀ v, D (D (D v)) = v)
    (hT2 : ∀ v, T (T v) = v) (hTD : ∀ v, T (D v) = D (D (T v))) (U : Submodule (ZMod 2) V)
    (hDU : ∀ u ∈ U, D u ∈ U) (hTU : ∀ u ∈ U, T u ∈ U) (hfpf : ∀ u ∈ U, D u = u → u = 0) :
    U = (U ⊓ LinearMap.ker (T - 1)) ⊔ (U ⊓ LinearMap.ker (T - 1)).map D ∧
      finrank (ZMod 2) U = 2 * finrank (ZMod 2) ↥(U ⊓ LinearMap.ker (T - 1)) := by
  set F := U ⊓ LinearMap.ker (T - 1) with hF
  have hmemF : ∀ v, v ∈ F ↔ v ∈ U ∧ T v = v := fun v => by
    simp [hF, sub_eq_zero]
  have hDinj : Function.Injective D := fun v w h => by
    have := congrArg (fun x => D (D x)) h
    simpa [hD3] using this
  have hdisj : F ⊓ F.map D = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, w, hw, rfl⟩
    rw [Submodule.mem_bot]
    have hw' := (hmemF w).mp hw
    have hv' := ((hmemF _).mp hv).2
    rw [hTD, hw'.2] at hv'
    have h1 : D w = w := by
      have := congrArg D hv'
      rw [hD3, hv'] at this
      exact this.symm
    rw [hfpf w hw'.1 h1, map_zero]
  have hrange : U.map (T - 1) ≤ F := by
    rintro _ ⟨u, hu, rfl⟩
    refine (hmemF _).mpr ⟨?_, ?_⟩
    · simp only [LinearMap.sub_apply, Module.End.one_apply]
      exact sub_mem (hTU u hu) hu
    · simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hT2]
      rw [sub_eq_add_zmod2, sub_eq_add_zmod2, add_comm]
  have h1 : finrank (ZMod 2) (U.map (T - 1)) + finrank (ZMod 2) F = finrank (ZMod 2) U :=
    finrank_map_add_finrank_inf_ker (T - 1) U
  have h2 := Submodule.finrank_mono hrange
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq F (F.map D)
  rw [hdisj, finrank_bot, LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective D hDinj F).symm] at h3
  have hle : F ⊔ F.map D ≤ U :=
    sup_le inf_le_left (by rintro _ ⟨w, hw, rfl⟩; exact hDU w ((hmemF w).mp hw).1)
  have h4 := Submodule.finrank_mono hle
  have heq : F ⊔ F.map D = U := Submodule.eq_of_le_of_finrank_le hle (by omega)
  exact ⟨heq.symm, by omega⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_fix_of_ne_bot (T₁ T₂ : V →ₗ[ZMod 2] V) (hT₁ : ∀ v, T₁ (T₁ v) = v)
    (hT₂ : ∀ v, T₂ (T₂ v) = v) (hT : ∀ v, T₁ (T₂ v) = T₂ (T₁ v)) (W : Submodule (ZMod 2) V)
    (h₁ : ∀ w ∈ W, T₁ w ∈ W) (h₂ : ∀ w ∈ W, T₂ w ∈ W) {w : V} (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ u ∈ W, u ≠ 0 ∧ T₁ u = u ∧ T₂ u = u := by
  obtain ⟨w₁, hw₁, hw₁0, hT₁w₁⟩ : ∃ w₁ ∈ W, w₁ ≠ 0 ∧ T₁ w₁ = w₁ := by
    by_cases h : T₁ w = w
    · exact ⟨w, hw, hw0, h⟩
    · refine ⟨T₁ w + w, add_mem (h₁ w hw) hw, fun h' => h ?_, ?_⟩
      · rw [← sub_eq_add_zmod2, sub_eq_zero] at h'
        exact h'
      · rw [map_add, hT₁, add_comm]
  by_cases h : T₂ w₁ = w₁
  · exact ⟨w₁, hw₁, hw₁0, hT₁w₁, h⟩
  · refine ⟨T₂ w₁ + w₁, add_mem (h₂ w₁ hw₁) hw₁, fun h' => h ?_, ?_, ?_⟩
    · rw [← sub_eq_add_zmod2, sub_eq_zero] at h'
      exact h'
    · rw [map_add, hT, hT₁w₁]
    · rw [map_add, hT₂, add_comm]

theorem block_fix (D E T₁ T₂ : V →ₗ[ZMod 2] V) (hD3 : ∀ v, D (D (D v)) = v)
    (hE3 : ∀ v, E (E (E v)) = v) (hT₁ : ∀ v, T₁ (T₁ v) = v) (hT₂ : ∀ v, T₂ (T₂ v) = v)
    (hDE : ∀ v, D (E v) = E (D v)) (hT : ∀ v, T₁ (T₂ v) = T₂ (T₁ v))
    (hT₁D : ∀ v, T₁ (D v) = D (D (T₁ v))) (hT₁E : ∀ v, T₁ (E v) = E (T₁ v))
    (hT₂D : ∀ v, T₂ (D v) = D (T₂ v)) (hT₂E : ∀ v, T₂ (E v) = E (E (T₂ v)))
    (hfix : ∀ v, D v = v → E v = v → T₁ v = v → T₂ v = v → v = 0)
    (hdim : finrank (ZMod 2) V ≤
      2 * finrank (ZMod 2) ↥(LinearMap.ker (T₁ - 1) ⊓ LinearMap.ker (T₂ - 1))) :
    LinearMap.ker (T₁ - 1) ≤ (LinearMap.ker (T₁ - 1) ⊓ LinearMap.ker (T₂ - 1)) ⊔
      (LinearMap.ker (T₁ - 1) ⊓ LinearMap.ker (T₂ - 1)).map E := by
  set C := LinearMap.ker (T₁ - 1) ⊓ LinearMap.ker (T₂ - 1) with hC
  have hmemC : ∀ v, v ∈ C ↔ T₁ v = v ∧ T₂ v = v := fun v => by
    simp [hC, sub_eq_zero]
  have hk1 : ∀ v, v ∈ LinearMap.ker (T₁ - 1) ↔ T₁ v = v := fun v => by simp [sub_eq_zero]
  have hk2 : ∀ v, v ∈ LinearMap.ker (T₂ - 1) ↔ T₂ v = v := fun v => by simp [sub_eq_zero]
  set P : V →ₗ[ZMod 2] V := LinearMap.id + E + E ∘ₗ E with hP
  have hPv : ∀ v, P v = v + E v + E (E v) := fun v => rfl
  have hEP : ∀ v, E (P v) = P v := fun v => by
    rw [hPv, map_add, map_add, hE3]
    abel
  have hPP : ∀ v, P (P v) = P v := fun v => by
    rw [hPv (P v), hEP, hEP, add_self_zmod2, zero_add]
  have hDP : ∀ v, D (P v) = P (D v) := fun v => by
    simp only [hPv, map_add, hDE]
  have hT₁P : ∀ v, T₁ (P v) = P (T₁ v) := fun v => by
    simp only [hPv, map_add, hT₁E]
  have hT₂P : ∀ v, T₂ (P v) = P (T₂ v) := fun v => by
    simp only [hPv, map_add, hT₂E, hE3]
    abel
  have hPE : ∀ v, P (E v) = P v := fun v => by
    rw [hPv, hPv, hE3]
    abel
  have hDE0 : ∀ v, D v = v → E v = v → v = 0 := by
    intro v hDv hEv
    by_contra hv0
    set W : Submodule (ZMod 2) V := LinearMap.ker (D - 1) ⊓ LinearMap.ker (E - 1) with hW
    have hWmem : ∀ w, w ∈ W ↔ D w = w ∧ E w = w := fun w => by simp [hW, sub_eq_zero]
    have h₁ : ∀ w ∈ W, T₁ w ∈ W := by
      intro w hw
      obtain ⟨hDw, hEw⟩ := (hWmem w).mp hw
      refine (hWmem _).mpr ⟨?_, by rw [← hT₁E, hEw]⟩
      have h := hT₁D w
      rw [hDw] at h
      have := congrArg D h
      rw [hD3] at this
      exact this
    have h₂ : ∀ w ∈ W, T₂ w ∈ W := by
      intro w hw
      obtain ⟨hDw, hEw⟩ := (hWmem w).mp hw
      refine (hWmem _).mpr ⟨by rw [← hT₂D, hDw], ?_⟩
      have h := hT₂E w
      rw [hEw] at h
      have := congrArg E h
      rw [hE3] at this
      exact this
    obtain ⟨u, huW, hu0, hu1, hu2⟩ := exists_fix_of_ne_bot T₁ T₂ hT₁ hT₂ hT W h₁ h₂
      ((hWmem v).mpr ⟨hDv, hEv⟩) hv0
    exact hu0 (hfix u ((hWmem u).mp huW).1 ((hWmem u).mp huW).2 hu1 hu2)
  have hYP : ∀ u, u ∈ LinearMap.ker P ↔ P u = 0 := fun u => LinearMap.mem_ker
  have hX := half_dim D T₁ hD3 hT₁ hT₁D (LinearMap.range P)
    (by rintro _ ⟨v, rfl⟩; exact ⟨D v, (hDP v).symm⟩)
    (by rintro _ ⟨v, rfl⟩; exact ⟨T₁ v, (hT₁P v).symm⟩)
    (by rintro _ ⟨v, rfl⟩ hDu; exact hDE0 _ hDu (hEP v))
  have hY := half_dim E T₂ hE3 hT₂ hT₂E (LinearMap.ker P)
    (fun u hu => by rw [hYP] at hu ⊢; rw [hPE, hu])
    (fun u hu => by rw [hYP] at hu ⊢; rw [← hT₂P, hu, map_zero])
    (fun u hu hEu => by
      rw [hYP] at hu
      rw [hPv, hEu, hEu, add_self_zmod2, zero_add] at hu
      exact hu)
  have hsplit : C ≤ (C ⊓ LinearMap.range P) ⊔ (C ⊓ LinearMap.ker P) := by
    intro v hv
    have hv' := (hmemC v).mp hv
    have h1 : P v ∈ C ⊓ LinearMap.range P :=
      ⟨(hmemC _).mpr ⟨by rw [hT₁P, hv'.1], by rw [hT₂P, hv'.2]⟩, ⟨v, rfl⟩⟩
    have h2 : v - P v ∈ C ⊓ LinearMap.ker P :=
      ⟨sub_mem hv h1.1, LinearMap.mem_ker.mpr (by rw [map_sub, hPP, sub_self])⟩
    have e : v = P v + (v - P v) := by abel
    rw [e]
    exact Submodule.add_mem_sup h1 h2
  have hCX : C ⊓ LinearMap.range P ≤ LinearMap.range P ⊓ LinearMap.ker (T₁ - 1) :=
    fun v hv => ⟨hv.2, hv.1.1⟩
  have hCY : C ⊓ LinearMap.ker P ≤ LinearMap.ker P ⊓ LinearMap.ker (T₂ - 1) :=
    fun v hv => ⟨hv.2, hv.1.2⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker P
  have d1 := Submodule.finrank_mono hsplit
  have d2 := Submodule.finrank_add_le_finrank_add_finrank (C ⊓ LinearMap.range P)
    (C ⊓ LinearMap.ker P)
  have d3 := Submodule.finrank_mono hCX
  have d4 := Submodule.finrank_mono hCY
  have hXd := hX.2
  have hYd := hY.2
  have hXeq : C ⊓ LinearMap.range P = LinearMap.range P ⊓ LinearMap.ker (T₁ - 1) :=
    Submodule.eq_of_le_of_finrank_le hCX (by omega)
  have hYeq : C ⊓ LinearMap.ker P = LinearMap.ker P ⊓ LinearMap.ker (T₂ - 1) :=
    Submodule.eq_of_le_of_finrank_le hCY (by omega)
  intro v hv
  have hv1 := (hk1 v).mp hv
  have hPv1 : P v ∈ C := by
    have : P v ∈ LinearMap.range P ⊓ LinearMap.ker (T₁ - 1) :=
      ⟨⟨v, rfl⟩, (hk1 _).mpr (by rw [hT₁P, hv1])⟩
    rw [← hXeq] at this
    exact this.1
  have hrest : v - P v ∈ C ⊔ C.map E := by
    have hmem : v - P v ∈ LinearMap.ker P := by rw [hYP, map_sub, hPP, sub_self]
    rw [hY.1, ← hYeq] at hmem
    have hle : (C ⊓ LinearMap.ker P) ⊔ (C ⊓ LinearMap.ker P).map E ≤ C ⊔ C.map E :=
      sup_le_sup inf_le_left (Submodule.map_mono inf_le_left)
    exact hle hmem
  have e : v = P v + (v - P v) := by abel
  rw [e]
  exact add_mem (Submodule.mem_sup_left hPv1) hrest

end CFSG.LargeExtraspecial.S10
