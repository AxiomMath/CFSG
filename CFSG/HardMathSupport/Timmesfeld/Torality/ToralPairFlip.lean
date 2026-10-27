module

public import CFSG.HardMathSupport.Timmesfeld.Torality.ToralPairOne
public import CFSG.HardMathSupport.Timmesfeld.Torality.ToralPairTwo

public section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem conj_rootDiagUnit_mem_familyGroup_E6_three
    {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (halg : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L)
    {a b : Fin Tag.E6.rank → Lˣ} {y g : ModGL Tag.E6 L}
    (hyb : y ∈ familyGroup (fun _ : Unit => b)) (hy3 : y ^ 3 = 1)
    (hg : g ∈ adjointGroup Tag.E6 L) (hga : g * y * g⁻¹ = rootDiagUnit Tag.E6 a) :
    g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ familyGroup (fun _ : Unit => a) := by
  classical
  obtain ⟨m, hmb, hmy⟩ :=
    exists_conj_mem_torusGroup_of_mem_familyGroup_E6_three halg hyb hy3
  have hmC : m ∈ familyCentralizer Tag.E6 L (fun _ : Unit => b) :=
    familyGroup_le_familyCentralizer (K := L) (fun _ : Unit => b) hmb
  have hmadj : m ∈ adjointGroup Tag.E6 L := (mem_familyCentralizer.1 hmC).1
  have hmfix : rootDiagUnit Tag.E6 b * m * (rootDiagUnit Tag.E6 b)⁻¹ = m :=
    (mem_familyCentralizer.1 hmC).2 ()
  have hcomm : rootDiagUnit Tag.E6 b * m = m * rootDiagUnit Tag.E6 b := by
    calc rootDiagUnit Tag.E6 b * m
        = (rootDiagUnit Tag.E6 b * m * (rootDiagUnit Tag.E6 b)⁻¹) *
            rootDiagUnit Tag.E6 b := by group
      _ = m * rootDiagUnit Tag.E6 b := by rw [hmfix]
  have hmd : m * rootDiagUnit Tag.E6 b * m⁻¹ = rootDiagUnit Tag.E6 b := by
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hga' : g⁻¹ * rootDiagUnit Tag.E6 a * g = y := by
    rw [← hga]
    group
  have hk : m * g⁻¹ ∈ adjointGroup Tag.E6 L := mul_mem hmadj (inv_mem hg)
  have hka : (m * g⁻¹) * rootDiagUnit Tag.E6 a * (m * g⁻¹)⁻¹ ∈ torusGroup Tag.E6 L := by
    have h : (m * g⁻¹) * rootDiagUnit Tag.E6 a * (m * g⁻¹)⁻¹ = m * y * m⁻¹ := by
      calc (m * g⁻¹) * rootDiagUnit Tag.E6 a * (m * g⁻¹)⁻¹
          = m * (g⁻¹ * rootDiagUnit Tag.E6 a * g) * m⁻¹ := by group
        _ = m * y * m⁻¹ := by rw [hga']
    rw [h]
    exact hmy
  have hkb : (m * g⁻¹) * (g * rootDiagUnit Tag.E6 b * g⁻¹) * (m * g⁻¹)⁻¹ ∈
      torusGroup Tag.E6 L := by
    have h : (m * g⁻¹) * (g * rootDiagUnit Tag.E6 b * g⁻¹) * (m * g⁻¹)⁻¹ =
        rootDiagUnit Tag.E6 b := by
      calc (m * g⁻¹) * (g * rootDiagUnit Tag.E6 b * g⁻¹) * (m * g⁻¹)⁻¹
          = m * rootDiagUnit Tag.E6 b * m⁻¹ := by group
        _ = rootDiagUnit Tag.E6 b := hmd
    rw [h]
    exact rootDiagUnit_mem_torusGroup b
  exact mem_familyGroup_of_conj_mem_torusGroup (τ := Tag.E6) hk hka hkb

end CFSG.HardMathSupport.Timmesfeld.Torality
