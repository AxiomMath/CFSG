module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Inf
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Gen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 E1 E2 : Subgroup G}

theorem sec8t84d3_Y_inf_C (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    Sec8T84Y X1 ⊓ centralizer (E : Set G) = E1 ⊔ oddCoreIn (normalizer (E : Set G)) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyY, hyC⟩ := hy
    obtain ⟨e, heE, o, hoO, rfl⟩ := sec8t84d3_C_decomp h hyC
    have hoY : o ∈ Sec8T84Y X1 := sec8t84d3_O_le_Y h hoO
    have heY : e ∈ Sec8T84Y X1 := by
      have heq : e = (e * o) * o⁻¹ := by group
      rw [heq]
      exact (Sec8T84Y X1).mul_mem hyY ((Sec8T84Y X1).inv_mem hoY)
    have heE1 : e ∈ E1 := sec8t84d3_Y_inf_E h hd ⟨heY, heE⟩
    exact (E1 ⊔ oddCoreIn (normalizer (E : Set G))).mul_mem
      (Subgroup.mem_sup_left heE1) (Subgroup.mem_sup_right hoO)
  · refine sup_le (fun e he => ⟨sec8t84d3_E1_le_Y h hd he, ?_⟩)
      (fun o ho => ⟨sec8t84d3_O_le_Y h ho, h.hO ho⟩)
    haveI := h.elem.1.1
    exact (hd.le1.trans (Subgroup.le_centralizer E)) he

theorem sec8t84d3_quot (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    QuotEquivTo (Sec8T84Y X1) (E1 ⊔ oddCoreIn (normalizer (E : Set G)))
      (alternatingGroup (Fin 6)) := by
  classical
  obtain ⟨φ, hsurj, hker⟩ := h.hX.quot1
  refine ⟨φ.comp (Subgroup.inclusion (sec8t84y_le X1)), ?_, ?_⟩
  · intro a
    obtain ⟨x, rfl⟩ := hsurj a
    obtain ⟨k, hk, y, hy, hxy⟩ := sec8t84y_exists_mul h.hX.quot1 x.2
    refine ⟨⟨y, hy⟩, ?_⟩
    have hx' : x = (⟨k, h.hX.c_le1 hk⟩ : ↥X1) *
        Subgroup.inclusion (sec8t84y_le X1) (⟨y, hy⟩ : ↥(Sec8T84Y X1)) := by
      apply Subtype.ext
      simp [hxy]
    have hk1 : φ (⟨k, h.hX.c_le1 hk⟩ : ↥X1) = 1 := by
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      exact hk
    rw [hx', map_mul, hk1, one_mul]
    rfl
  · ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change φ (Subgroup.inclusion (sec8t84y_le X1) y) = 1 ↔
      (y : G) ∈ E1 ⊔ oddCoreIn (normalizer (E : Set G))
    rw [show Subgroup.inclusion (sec8t84y_le X1) y =
        (⟨(y : G), sec8t84y_le X1 y.2⟩ : ↥X1) from rfl,
      ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, ← sec8t84d3_Y_inf_C h hd]
    exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩

theorem sec8t84d3_cent (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    Sec8T84Y X1 ⊓ centralizer (E1 : Set G) ≤ E1 ⊔ oddCoreIn (normalizer (E : Set G)) := by
  intro y hy
  obtain ⟨hyY, hyC⟩ := hy
  have hyX : y ∈ X1 := sec8t84y_le X1 hyY
  have hyCc : y ∈ centralizer (E : Set G) :=
    hd.faith1 y hyX (fun e he => by
      have hcomm := (Subgroup.mem_centralizer_iff.mp hyC) e he
      rw [← hcomm]; group)
  rw [← sec8t84d3_Y_inf_C h hd]
  exact ⟨hyY, hyCc⟩

theorem sec8t84d3_trans (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    ∀ v ∈ E1, v ≠ 1 → ∀ w ∈ E1, w ≠ 1 → ∃ y ∈ Sec8T84Y X1, y * v * y⁻¹ = w := by
  intro v hv hv1 w hw hw1
  obtain ⟨x, hx, hxv⟩ := hd.trans1 v hv hv1 w hw hw1
  obtain ⟨k, hk, y, hy, hxy⟩ := sec8t84y_exists_mul h.hX.quot1 hx
  refine ⟨y, hy, ?_⟩
  have hyX : y ∈ X1 := sec8t84y_le X1 hy
  have hyE : y * v * y⁻¹ ∈ E := by
    have hyN : y ∈ normalizer (E : Set G) := h.hX.le1 hyX
    exact (Subgroup.mem_normalizer_iff.mp hyN v).mp (hd.le1 hv)
  have hkfix : k * (y * v * y⁻¹) * k⁻¹ = y * v * y⁻¹ := by
    have hcomm := (Subgroup.mem_centralizer_iff.mp hk) (y * v * y⁻¹) hyE
    rw [← hcomm]; group
  have h1 : k * y * v * (k * y)⁻¹ = y * v * y⁻¹ := by
    calc k * y * v * (k * y)⁻¹ = k * (y * v * y⁻¹) * k⁻¹ := by group
      _ = y * v * y⁻¹ := hkfix
  calc y * v * y⁻¹ = k * y * v * (k * y)⁻¹ := h1.symm
    _ = w := by rw [← hxy]; exact hxv

end CFSG.OddStandard.SmallF3.Omega
