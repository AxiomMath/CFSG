module

public import CFSG.CGT.Foote81L6.FinalCore
public import CFSG.CGT.Foote81L6.CaseFour
public import CFSG.CGT.Foote81L6.TStruct.Lemma2Three

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

@[expose] def FooteFinalHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    D.a ∈ center G → ¬ StronglyInvolutionClosed D.A T → ¬ StronglyInvolutionClosed D.Astar T →
      ∃ h ∈ (T : Subgroup G), D.Astar = oddCent ((D.Frep 0 1).map (MulAut.conj h).toMonoidHom)

@[expose] def FooteNotConjAAstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteCore G T 2 n),
    D.a ∈ center G → ∀ g : G, D.A.map (MulAut.conj g).toMonoidHom ≠ D.Astar

theorem footeFinal_of (hHalf : FooteFinalHalf) (hL32 : FooteNotConjAAstar) : FooteFinal := by
  intro G _ _ T n D hcen
  by_contra hneither
  push Not at hneither
  obtain ⟨hnA, hnAs⟩ := hneither
  obtain ⟨h₁, -, hA₁⟩ := hHalf G T n D hcen hnA hnAs
  obtain ⟨h₂, -, hA₂⟩ := hHalf G T n D.star hcen (by rwa [FooteCore.star_A])
    (by rwa [FooteCore.star_Astar])
  rw [FooteCore.star_Astar, D.star_Frep rfl] at hA₂
  have hrep : (D.Frep 0 1).map (MulAut.conj h₂).toMonoidHom =
      ((D.Frep 0 1).map (MulAut.conj h₁).toMonoidHom).map
        (MulAut.conj (h₂ * h₁⁻¹)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hrep, oddCent_map_conj, ← hA₁] at hA₂
  apply hL32 G T n D hcen (h₁ * h₂⁻¹)
  rw [hA₂, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id D.Astar]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

end CFSG.CGT.Foote81L6
