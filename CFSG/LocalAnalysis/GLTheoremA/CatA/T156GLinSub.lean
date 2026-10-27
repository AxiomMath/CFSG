module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLinMat
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearSub

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156.Lin

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.StandardType CFSG.StandardType.LinearFieldFix
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem range_subfieldHom' (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {σ : K ≃+* K} (hk : SLOK d (fixF σ))
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f) :
    (subfieldHom σ).range = ggFixDer f := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let H : Subgroup (GL (Fin d) K) := LargeEvenSLGroup (Fin d) K
  let π : H →* LargeEvenProj H := LargeEvenProjMk H
  let ρ : MulAut H := matAct H (slMapStable d K) σ
  let C : Subgroup H := FP.fixSub ρ
  let D : Subgroup (LargeEvenProj H) := C.map π
  let T : Subgroup (LargeEvenProj H) := FP.fixSub f
  have hInc : (subfieldInclusion (d := d) σ).range = C := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨A, rfl⟩
      rw [FP.mem_fixSub]
      apply Subtype.ext
      change ((ρ (subfieldInclusion σ A) : H) : GL (Fin d) K) =
        ((subfieldInclusion σ A : H) : GL (Fin d) K)
      rw [matAct_coe H (slMapStable d K) σ (subfieldInclusion σ A), coe_subfieldInclusion]
      exact glMap_subtype_fixed σ A.1
    · intro x hx
      rw [FP.mem_fixSub] at hx
      rw [MonoidHom.mem_range]
      have hfix : Matrix.GeneralLinearGroup.map σ.toRingHom (x : GL (Fin d) K) =
          (x : GL (Fin d) K) := by
        rw [← matAct_coe H (slMapStable d K) σ x]
        exact congrArg (fun y : H => (y : GL (Fin d) K)) hx
      obtain ⟨A, hA⟩ := exists_descend σ (x : GL (Fin d) K) hfix
      refine ⟨⟨A, ?_⟩, ?_⟩
      · apply (sl_map_subtype_iff σ A).1
        rw [hA]
        exact x.2
      · apply Subtype.ext
        rw [coe_subfieldInclusion]
        exact hA
  have hRange : (subfieldHom (d := d) σ).range = D := by
    unfold subfieldHom
    rw [MonoidHom.range_comp, hInc]
  have hZc : (LargeEvenScalars (Fin d) K).subgroupOf H ≤ Subgroup.center H :=
    scalars_subgroupOf_le_center H
  have hZodd : Odd (Nat.card ((LargeEvenScalars (Fin d) K).subgroupOf H)) :=
    scalars_subgroupOf_odd hm hK H
  have hmem : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ x) := hf
  obtain ⟨hDT, hcomm, -⟩ := FR.subfield_core ((LargeEvenScalars (Fin d) K).subgroupOf H)
    hZc hZodd ρ f hmem
  haveI hperf : Group.IsPerfect ↥(LargeEvenSLGroup (Fin d) (fixF σ)) :=
    Subgroup.isPerfect_iff.2 (commutator_slGroup' (F := fixF σ) hd hk)
  have hDperf : Group.IsPerfect ↥D := by
    have h1 : Group.IsPerfect ↥((subfieldHom (d := d) σ).range) :=
      Group.IsPerfect.range (subfieldHom (d := d) σ)
    rwa [hRange] at h1
  have hT : ggFixSub f = T := Subgroup.ext fun _ => Iff.rfl
  rw [hRange]
  unfold ggFixDer
  rw [hT]
  refine le_antisymm ?_ hcomm
  · haveI := hDperf
    rw [← Subgroup.commutator_eq_self (H := D)]
    exact Subgroup.commutator_mono hDT hDT

@[expose] noncomputable def subfieldEquiv' (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {σ : K ≃+* K} (hk : SLOK d (fixF σ))
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f) :
    LargeEvenProj (LargeEvenSLGroup (Fin d) (fixF σ)) ≃* ggFixDer f :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_subfieldHom (by omega) σ).symm).trans
    (QuotientGroup.quotientKerEquivRange (subfieldHom σ))).trans
    (MulEquiv.subgroupCongr (range_subfieldHom' hd hm hK hk hf))

end CFSG.LocalAnalysis.GLTheoremA.T156.Lin

end
