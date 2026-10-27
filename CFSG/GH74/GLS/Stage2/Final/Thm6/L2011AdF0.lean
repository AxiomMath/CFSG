module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Stmts
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_barOf_iff bar_mem_conjugate_iff)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_conj_mem F20_le_OddCore)
open scoped commutatorElement

variable {G : Type} [Group G] {z : G} {g : G}

theorem mem_H0_of_comm {x : G} (hx : ∀ f ∈ F0 z g, x * f = f * x) : x ∈ H0 z g := by
  unfold H0
  rw [Subgroup.mem_normalizer_iff]
  intro f
  have key : ∀ f' ∈ F0 z g, x * f' * x⁻¹ = f' := fun f' hf' => by
    rw [hx f' hf', mul_inv_cancel_right]
  constructor
  · intro hf
    rw [key f hf]; exact hf
  · intro hf
    have hf' : x * f * x⁻¹ = f := by
      have h1 : x * f = f * x := by
        have h2 := hx (x * f * x⁻¹) hf
        have h3 : x * (x * f * x⁻¹) = (x * f * x⁻¹) * x := h2
        calc x * f = x⁻¹ * (x * (x * f * x⁻¹)) * x := by group
          _ = x⁻¹ * ((x * f * x⁻¹) * x) * x := by rw [h3]
          _ = f * x := by group
      rw [h1, mul_inv_cancel_right]
    rw [hf'] at hf
    exact hf

theorem F0_comm_z {f : G} (hf : f ∈ F0 z g) : z * f = f * z :=
  (Subgroup.mem_centralizer_singleton_iff.1 (oddCore_le_Cen z (F20_le_OddCore z hf.1))).symm

theorem F0_comm_t {f : G} (hf : f ∈ F0 z g) : zc z g * f = f * zc z g := by
  have hf2 : g * f * g⁻¹ ∈ OddCore z := bar_mem_conjugate_iff.1 hf.2
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (oddCore_le_Cen z hf2)
  simp only [zc]
  calc g⁻¹ * z * g * f = g⁻¹ * (z * (g * f * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * f * g⁻¹) * z) * g := by rw [hc]
    _ = f * (g⁻¹ * z * g) := by group

theorem F0_comm_layer [Finite G] {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hK : CompData z K₁ K₂ L₁ L₂) {a : G} (ha : a ∈ Em (Cen z)) {f : G} (hf : f ∈ F0 z g) :
    a * f = f * a :=
  (hK.oddcomm f (F20_le_OddCore z hf.1) a ha).symm

theorem F0_comm_conj_layer [Finite G] {K₁ K₂ : Subgroup G} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hK : CompData z K₁ K₂ L₁ L₂) {a : G} (ha : g * a * g⁻¹ ∈ Em (Cen z)) {f : G}
    (hf : f ∈ F0 z g) : a * f = f * a := by
  have hf2 : g * f * g⁻¹ ∈ OddCore z := bar_mem_conjugate_iff.1 hf.2
  have h := (hK.oddcomm _ hf2 _ ha).symm
  calc a * f = g⁻¹ * ((g * a * g⁻¹) * (g * f * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * f * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
    _ = f * a := by group

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
