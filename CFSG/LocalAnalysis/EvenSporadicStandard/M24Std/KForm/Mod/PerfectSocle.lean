module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup

theorem perfect_le_socle_of_perfect {K : Type} [Group K] [Finite K] (S : Subgroup K) [S.Normal]
    (hC : centralizer (S : Set K) = ⊥)
    (hsolv : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S))
    (P : Subgroup K) (hP : ⁅P, P⁆ = P) : P ≤ S := by
  let φ : K →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)).comp
      (MulAut.conjNormal (H := S))
  let ψ : ↥P →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥S := φ.comp P.subtype
  have hψ : ψ.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial ψ.range := (Subgroup.nontrivial_iff_ne_bot ψ.range).2 hne
    haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
    haveI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    exact Group.IsPerfect.not_isSolvable ψ.range inferInstance
  intro d hd
  have h1 : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S)
      (MulAut.conjNormal (H := S) d) = 1 := by
    have hmem : ψ ⟨d, hd⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩
    rw [hψ, Subgroup.mem_bot] at hmem
    exact hmem
  have hinner : MulAut.conjNormal (H := S) d ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥S :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨s, hs⟩ := hinner
  have hcent : (s : K)⁻¹ * d ∈ centralizer (S : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hx := congrArg (fun f : MulAut ↥S => ((f ⟨h, hh⟩ : ↥S) : K)) hs
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at hx
    calc h * ((s : K)⁻¹ * d) = (s : K)⁻¹ * ((s : K) * h * (s : K)⁻¹) * d := by group
      _ = (s : K)⁻¹ * (d * h * d⁻¹) * d := by rw [hx]
      _ = (s : K)⁻¹ * d * h := by group
  rw [hC, Subgroup.mem_bot] at hcent
  have hds : (s : K) = d := inv_mul_eq_one.mp hcent
  rw [← hds]
  exact s.2

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
