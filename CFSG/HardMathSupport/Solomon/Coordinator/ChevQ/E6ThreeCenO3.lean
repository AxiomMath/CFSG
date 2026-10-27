module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenDefs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenTorus
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenInner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenReps

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.TableBExc.E6Three (gE6)

set_option linter.unusedSectionVars false

section Census

variable
  {K : Type} [Field K] {ω : Kˣ}

theorem e6Cen_le_innerAut_of_frame [Finite K] (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    {S : Set (WeylGroup Tag.E6)} (hF : E6CenFrame (Subgroup.closure S) E)
    {Z : MulAut (adjointGroup Tag.E6 K)} (hZE : Z ∈ E) (hZ : BmMono Z e6CenZ)
    (hS : S ⊆ e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K))) :
    E ≤ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K) := by
  intro Y hYE
  obtain ⟨v, hv, hYv⟩ := hF.1 Y hYE
  obtain ⟨W, hW, hWv⟩ := mem_e6CenImage.1 ((Subgroup.closure_le _).2 hS hv)
  have hWE := (Subgroup.mem_inf.1 hW).1
  have h' := hYv.mul hWv.inv
  rw [mul_inv_cancel] at h'
  have hd := e6Cen_inner_of_bmMono_one h3 h1 hE hZE hZ (mul_mem hYE (inv_mem hWE)) h'
  have h := mul_mem hd (Subgroup.mem_inf.1 hW).2
  rw [inv_mul_cancel_right] at h
  exact h

theorem e6Cen_O3 [Finite K] (hK : 3 ∣ Nat.card K - 1) (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hcube : E6CenCube K E)
    (hF : E6CenFrame e6CenO3 E) : E6CenConcl K E := by
  obtain ⟨hE, -, -, hEi, -, -⟩ := hcube
  have hmem : ∀ i : Fin 3, gE6 i ∈ e6CenO3 := by
    intro i
    apply Subgroup.subset_closure
    fin_cases i <;> simp
  choose X hXE hX using fun i => hF.2 _ (hmem i)
  have hXi := e6Cen_inner_O3 hK hX (fun i => hE.2 _ (hXE i))
    fun i j => congrArg Subtype.val (hE.1.is_comm.comm (⟨X i, hXE i⟩ : E) ⟨X j, hXE j⟩)
  have hS : ({gE6 0, gE6 1, gE6 2} : Set (WeylGroup Tag.E6)) ⊆
      e6CenImage (E ⊓ CFSG.Fischer.innerAut (adjointGroup Tag.E6 K)) := by
    rintro _ (rfl | rfl | rfl)
    · exact mem_e6CenImage.2 ⟨X 0, Subgroup.mem_inf.2 ⟨hXE 0, hXi 0⟩, hX 0⟩
    · exact mem_e6CenImage.2 ⟨X 1, Subgroup.mem_inf.2 ⟨hXE 1, hXi 1⟩, hX 1⟩
    · exact mem_e6CenImage.2 ⟨X 2, Subgroup.mem_inf.2 ⟨hXE 2, hXi 2⟩, hX 2⟩
  exact (hEi (e6Cen_le_innerAut_of_frame h3 h1 hE hF
    (mul_mem (mul_mem (hXE 0) (hXE 1)) (hXE 2)) (((hX 0).mul (hX 1)).mul (hX 2)) hS)).elim

end Census

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
