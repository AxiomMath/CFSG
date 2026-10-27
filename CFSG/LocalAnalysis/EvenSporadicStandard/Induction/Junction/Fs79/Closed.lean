module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.SylowImage
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.GWExc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ExcDihedral

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.GorensteinWalter

theorem sol78ExcClosed_proved : Sol78ExcClosed := by
  intro X _ _ K hX hK hexc
  have hD := hasDihedralSylowTwo_of_excType hexc
  let ι : ↥K →* X ⧸ center X := (QuotientGroup.mk' (center X)).comp K.subtype
  let q : ↥K →* ↥K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : ι.ker ≤ q.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : (x : X) ∈ center X := (QuotientGroup.eq_one_iff (x : X)).1 hx
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hxc y)
  let SY : Sylow 2 (↥K ⧸ center ↥K) := default
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.1
  rcases sylow_image_cyclic_or_dihedral hD ι q hq hker SY with hcyc | ⟨j, hj, hS⟩
  · exact absurd hcyc (not_isCyclic_sylow_two hK.2.2 SY)
  · exact excType_of_dihedral_sylow hK SY hj hS

end CFSG.EvenSporadicStandard.Induction.Junction
