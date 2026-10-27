module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GFH
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5GSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.L2Aut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

private theorem sec5op4h_fix_img {X : Type} [Group X] {A : Subgroup X}
    (ρ : X →* MulAut (Sec5GBar A))
    (hρ : ∀ (g : X) (m : ↥(normalClosure (A : Set X))),
      ρ g (sec5g_pi A m) = sec5g_pi A (MulAut.conjNormal (H := normalClosure (A : Set X)) g m))
    {D : Subgroup X} (hD : ∀ d ∈ D, ∀ a ∈ A, d * a * d⁻¹ = a)
    {d : X} (hd : d ∈ D) {x : Sec5GBar A} (hx : x ∈ Sec5GImg A) : ρ d x = x := by
  obtain ⟨a, ha, rfl⟩ := (sec5g_mem_img A).1 hx
  rw [hρ d ⟨a, subset_normalClosure ha⟩]
  congr 1
  refine Subtype.ext ?_
  simpa using hD d hd a ha

theorem sec5op4_comm_le_ker {X : Type}
    [Group X] [Finite X] {A : Subgroup X} (hA : Sec5GCaseI A ∨ Sec5GCaseII A)
    (ρ : X →* MulAut (Sec5GBar A))
    (hρ : ∀ (g : X) (m : ↥(normalClosure (A : Set X))),
      ρ g (sec5g_pi A m) = sec5g_pi A (MulAut.conjNormal (H := normalClosure (A : Set X)) g m))
    {D : Subgroup X} (hD : ∀ d ∈ D, ∀ a ∈ A, d * a * d⁻¹ = a) : ⁅D, D⁆ ≤ ρ.ker := by
  have hfix : ∀ d ∈ D, ∀ x ∈ Sec5GImg A, ρ d x = x :=
    fun d hd x hx => sec5op4h_fix_img (A := A) ρ hρ hD hd hx
  rcases hA with hI | hII
  ·
    have hItop : Sec5GImg A = ⊤ := hI
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have ha1 : ρ a = 1 := by
      ext x
      exact hfix a ha x (by rw [hItop]; exact Subgroup.mem_top x)
    have hb1 : ρ b = 1 := by
      ext x
      exact hfix b hb x (by rw [hItop]; exact Subgroup.mem_top x)
    rw [MonoidHom.mem_ker, map_commutatorElement, ha1, hb1]
    simp
  ·
    obtain ⟨F, hF, hFin, h5, h8, ⟨e⟩, P, hP⟩ := sec5g_caseII_field (A := A) hII
    letI := hF
    letI := hFin
    exact l2aut_commutator_acts_trivially e h5 h8 P ρ fun d hd x hx =>
      hfix d hd x (by rwa [← hP])

end CFSG.OddStandard.SmallF3.Omega
