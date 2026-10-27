module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjDisp

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg Module

section Lead

variable {τ : Tag} {K : Type*} [Field K] {f : (Fin τ.rank → ℤ) →+ ℤ} [Fintype (Label τ)]

theorem lead_split (hLD : LevelData (rootSubgroup τ K) (posS f) f) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ posS f) {a : (Module.End K (RootModule τ K))ˣ}
    (ha : a ∈ lvl (rootSubgroup τ K) (posS f) f (f γ))
    (hna : a ∉ lvl (rootSubgroup τ K) (posS f) f (f γ + 1)) :
    ∃ c : K, c ≠ 0 ∧ ∃ n : Module.End K (RootModule τ K),
      IsShiftL (lblDeg f) (f γ + 1) n ∧
        (a : Module.End K (RootModule τ K)) - 1 = c • pinnedE τ K γ + n := by
  obtain ⟨x, hx, κ, hκ, rfl⟩ := hLD.lvl_decomp hγ ha
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  have hf : 0 < f γ := hγ.2
  have hc : c ≠ 0 := by
    rintro rfl
    apply hna
    rw [pinnedX_zero, one_mul]
    exact hκ
  set E := pinnedE τ K γ with hE
  have hκ' : IsShiftL (lblDeg f) (f γ + 1) ((κ : Module.End K (RootModule τ K)) - 1) :=
    isShiftL_of_mem_lvl (by omega) hκ
  have hx1 := isShiftL_pinnedX_sub_one (K := K) (f := f) hγ.1 hf c
  have hx2 := isShiftL_pinnedX_sub_lead (K := K) (f := f) hγ.1 hf c
  set n : Module.End K (RootModule τ K) :=
    ((pinnedX τ K γ c * κ : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1 -
      c • E with hn
  have hsplit : n = (((pinnedX τ K γ c : (Module.End K (RootModule τ K))ˣ) :
      Module.End K (RootModule τ K)) - 1 - c • E) +
      (((pinnedX τ K γ c : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K)) - 1) *
        ((κ : Module.End K (RootModule τ K)) - 1) +
      ((κ : Module.End K (RootModule τ K)) - 1) := by
    rw [hn, Units.val_mul]; noncomm_ring
  have hnS : IsShiftL (lblDeg f) (f γ + 1) n := by
    rw [hsplit]
    exact ((hx2.mono (by omega)).add ((hx1.mul hκ').mono (by omega))).add hκ'
  refine ⟨c, hc, n, hnS, ?_⟩
  rw [hn]; abel

end Lead

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
