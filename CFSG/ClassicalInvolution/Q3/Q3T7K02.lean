module

public import CFSG.ClassicalInvolution.Q3.Q3T7M00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7M

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

section Connected

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem not_commutes_self {M : Subgroup G} {z : G} (h : Q3.IsClassicalMember3 M z) :
    ¬ Commutes M M := by
  intro hc
  have hcomm : ∀ a b : M, a * b = b * a := fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)
  obtain ⟨e⟩ := h.nonempty_equiv
  have hab : ∀ a b : SL(2, ZMod 3), a * b = b * a := by
    intro a b
    obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore M) (e.symm a)
    obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore M) (e.symm b)
    apply e.symm.injective
    rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hcomm a' b']
  exact Q3.sl2Three_not_comm hab

theorem nonCommConnected_of_transitive (hΩ : Q3.InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) : NonCommConnected Ω := by
  by_contra hnc
  obtain ⟨Λ₁, Λ₂, hU, h1, h2, hi1, hi2, hcomm⟩ :=
    Generic.exists_split hΩ.nonempty hΩ.conjInvariant hΩ.generated hnc
  have hKU : K ∈ Λ₁ ∪ Λ₂ := hU ▸ hK
  rcases hKU with hK1 | hK2
  · obtain ⟨M, hM⟩ := h2
    have hMΩ : M ∈ Ω := hU ▸ Or.inr hM
    obtain ⟨g, hg⟩ := htrans M hMΩ
    have hM1 : M ∈ Λ₁ := hg ▸ hi1 g K hK1
    obtain ⟨zM, hzM⟩ := hΩ.classical M hMΩ
    exact not_commutes_self hzM (hcomm M hM1 M hM)
  · obtain ⟨M, hM⟩ := h1
    have hMΩ : M ∈ Ω := hU ▸ Or.inl hM
    obtain ⟨g, hg⟩ := htrans M hMΩ
    have hM2 : M ∈ Λ₂ := hg ▸ hi2 g K hK2
    obtain ⟨zM, hzM⟩ := hΩ.classical M hMΩ
    exact not_commutes_self hzM (hcomm M hM M hM2)

end Connected

end CFSG.ClassicalInvolution.Q3.Q3T7M

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform

section Simple


theorem EInputs.of_qs3 (hQ : Q3.QuasisimpleConnected3) : EInputs where
  simple G _ _ Ω hΩ hbelow hO hsolv hgen K hK htrans := by
    classical
    have hIn : Q3.InClass3 Ω :=
      inClassU_three_iff.mp ⟨⟨K, hK⟩, hΩ.conjInvariant, hgen, hΩ.classical⟩
    have hbelow3 : Q3.CIT3Below (Nat.card G) :=
      (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hbelow
    have hconn : NonCommConnected Ω :=
      Q3T7M.nonCommConnected_of_transitive hIn hK htrans
    obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
    have hns : ¬ Group.IsSolvable G := by
      intro hs
      have : Group.IsSolvable G := hs
      have h1 : (⊤ : Subgroup G) = ⊥ := hsolv ⊤ inferInstance inferInstance
      apply hz.ne_one
      have : z ∈ (⊤ : Subgroup G) := trivial
      rw [h1] at this
      exact this
    have hqs : CFSG.Open.IsQuasisimple G := hQ G hbelow3 hO Ω hIn hconn hns
    have hZ : Subgroup.center G = ⊥ :=
      hsolv _ inferInstance (Group.isSolvable_of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1))
    have hsimple : IsSimpleGroup G := by
      have : IsSimpleGroup (G ⧸ Subgroup.center G) := hqs.2
      exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
        |>.isSimpleGroup
    refine ⟨⊤, inferInstance, (Subgroup.topEquiv (G := G)).isSimpleGroup, ?_, ?_⟩
    · by_contra hab
      push Not at hab
      exact hns (Group.isSolvable_of_comm fun a b => hab a trivial b trivial)
    · rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]

end Simple

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
