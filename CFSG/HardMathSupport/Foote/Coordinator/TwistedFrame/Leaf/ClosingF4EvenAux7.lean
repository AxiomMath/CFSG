module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4EvenAux6

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

set_option linter.unusedSectionVars false


section StepD2

open T7

variable {L : Type} [Field L] [CharP L 2] {Fr : L →+* L} {H : Subgroup (ModGL Tag.F4 L)}

theorem rB23_deg' : rB23 0 = 1 := by decide
theorem pB23_deg : pB23 0 = 1 := by decide
theorem isRoot_rB23 : IsRoot Tag.F4 rB23 := mem_rootFinset.1 rB23_root
theorem isRoot_pB23 : IsRoot Tag.F4 pB23 := mem_rootFinset.1 pB23_root'
theorem rB23_mem_Deg1 : rB23 ∈ Deg1 Tag.F4 := ⟨isRoot_rB23, rB23_deg'⟩
theorem pB23_mem_Deg1 : pB23 ∈ Deg1 Tag.F4 := ⟨isRoot_pB23, pB23_deg⟩

theorem commPairs_rB23_pB23 : commPairs Tag.F4 rB23 pB23 = [] := commPairs_eq_of (by decide +kernel)

theorem commute_rB23_pB23 (a b : L) :
    Commute (pinnedX Tag.F4 L rB23 a) (pinnedX Tag.F4 L pB23 b) :=
  commute_pinnedX_of_commPairs_nil Tag.F4 L isRoot_rB23 isRoot_pB23 (by decide) (by decide)
    commPairs_rB23_pB23 a b

@[expose] def vA (a b : L) : ModGL Tag.F4 L :=
  pinnedX Tag.F4 L rB23 a * pinnedX Tag.F4 L pB23 b

theorem sig_vA {a : L} (ha : InE Fr a) : sigHom Fr (vA a (Fr a)) = vA a (Fr a) := by
  unfold vA
  rw [map_mul, sigHom_pinnedX Fr isRoot_rB23, sigHom_pinnedX Fr isRoot_pB23, w_rB23, w_pB23]
  have : Fr (Fr a) = a := ha
  rw [this]
  exact (commute_rB23_pB23 a (Fr a)).symm.eq

theorem heisCoord_vA (a : L) : vA a (Fr a) ∈ Qθ Tag.F4 L ∧
    heisCoord Tag.F4 L (vA a (Fr a)) = fv Fr rB23 a := by
  have h1 := pinnedX_mem_Qθ_of_mem_Deg1 (K := L) rB23_mem_Deg1 a
  have h2 := pinnedX_mem_Qθ_of_mem_Deg1 (K := L) pB23_mem_Deg1 (Fr a)
  refine ⟨mul_mem h1 h2, ?_⟩
  unfold vA
  rw [(heisCoord_spec Tag.F4 L).mul _ h1 _ h2, (heisCoord_spec Tag.F4 L).pinnedX_deg1 _ rB23_mem_Deg1,
    (heisCoord_spec Tag.F4 L).pinnedX_deg1 _ pB23_mem_Deg1, fv, w_rB23]

theorem vA_mem (E : Elts Fr H) {a : L} (ha : InE Fr a) (hW : IsW Fr H (fv Fr rB23 a)) :
    vA a (Fr a) ∈ H :=
  mem_of_isW E.eth hW (heisCoord_vA a).1 (sig_vA ha) (heisCoord_vA a).2

theorem supp_fv {μ : Fin Tag.F4.rank → ℤ} (h1 : μ ∈ Deg1 Tag.F4) (h2 : wF4 • μ ∈ Deg1 Tag.F4)
    (l : L) : Supp (fv Fr μ l) := by
  intro ν hν
  have hne1 : ν ≠ μ := fun e => hν (e ▸ h1)
  have hne2 : ν ≠ wF4 • μ := fun e => hν (e ▸ h2)
  simp [fv, Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2]

theorem sf_fv {μ : Fin Tag.F4.rank → ℤ} (hww : wF4 • wF4 • μ = μ) (hne : μ ≠ wF4 • μ) {l : L}
    (hl : InE Fr l)
    (ν : Fin Tag.F4.rank → ℤ) : fv Fr μ l ν = Fr (fv Fr μ l (wF4⁻¹ • ν)) := by
  have hFF : Fr (Fr l) = l := hl
  have e1 : wF4⁻¹ • ν = μ ↔ ν = wF4 • μ := by rw [inv_smul_eq_iff]
  have e2 : wF4⁻¹ • ν = wF4 • μ ↔ ν = μ := by rw [inv_smul_eq_iff, hww]
  simp only [fv, Pi.add_apply, Pi.single_apply, map_add, e1, e2]
  by_cases h1 : ν = μ
  · have h2 : ν ≠ wF4 • μ := fun h => hne (h1.symm.trans h)
    simp [h1, h2, hFF, add_comm, hne]
  · by_cases h2 : ν = wF4 • μ
    · simp [h1, h2, hFF, add_comm, hne.symm]
    · simp [h1, h2]

theorem isW_fv_B23 {l : L} (hl : InE Fr l) (hP : (⟨0, 0, 0, 0, 0, 0, l⟩ : T7 L) ∈ Pset Fr H) :
    IsW Fr H (fv Fr rB23 l) := by
  obtain ⟨u, hu, hcrd⟩ := hP
  have hww : wF4 • wF4 • rB23 = rB23 := by rw [w_rB23, w_pB23]
  have hwD : wF4 • rB23 ∈ Deg1 Tag.F4 := by rw [w_rB23]; exact ⟨mem_rootFinset.1 (by decide +kernel), by decide⟩
  have : u = fv Fr rB23 l := by
    refine eq_of_crd (Fr := Fr) (fun ν hν => hu.supp hν) (supp_fv rB23_mem_Deg1 hwD l)
      (fun ν => hu.sf ν) (sf_fv hww (by rw [w_rB23]; decide) hl) ?_
    rw [hcrd, crd_fv_rB23]
  rw [← this]
  exact hu

end StepD2

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.F4Even
