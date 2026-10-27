module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HI3L
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HI3B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem sec8t84h_i3_core [Finite G] (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) {S : Subgroup G}
    (hS : IsSylow2Of S (Subgroup.normalizer (L : Set G))) {y' : G} (hy'S : y' ∈ S)
    {x₁ : ProjSim Q} (hx₁ : ffTheta6M hQ hdim hsgn e ⟨y', hS.1 hy'S⟩ = x₁)
    (hty : ∃ α : ℤˣ, SimHasType x₁ 1 α ∨ SimHasType x₁ 3 α) :
    ∃ B : Subgroup G, B ≤ L ⊓ S ∧ IsElemAb2 B 4 ∧
      ∃ x ∈ S ⊓ Subgroup.centralizer (B : Set G), x ∉ Subgroup.centralizer (L : Set G) ∧
        ∃ α : ℤˣ, InducesTypeSome L x 6 (-1) 3 α := by
  have hmain : ∃ x'' : ProjOrth Q, projOrthToProjSim Q x'' = x₁ ∧
      ∃ α : ℤˣ, HasType x'' 1 α ∨ HasType x'' 3 α := by
    obtain ⟨α, hα | hα⟩ := hty
    · unfold SimHasType at hα
      obtain ⟨x'', hx'', ht⟩ := hα
      exact ⟨x'', hx'', α, Or.inl ht⟩
    · unfold SimHasType at hα
      obtain ⟨x'', hx'', ht⟩ := hα
      exact ⟨x'', hx'', α, Or.inr ht⟩
  obtain ⟨x'', hx''ι, α₂, hty''⟩ := hmain
  have hx : projOrthToProjSim Q x'' = ffTheta6M hQ hdim hsgn e ⟨y', hS.1 hy'S⟩ :=
    hx''ι.trans hx₁.symm
  have hsq : x'' * x'' = 1 := by
    rcases hty'' with h | h
    · unfold HasType at h
      obtain ⟨-, t, htt, -, htx⟩ := h
      rw [← htx, ← map_mul, htt, map_one]
    · unfold HasType at h
      obtain ⟨-, t, htt, -, htx⟩ := h
      rw [← htx, ← map_mul, htt, map_one]
  have hnorm := sec8t84hImg_normalizes hQ hdim hsgn e hS.1 hy'S hx
  have hsyl := sec8t84hImg_sylow hQ e hodd hS
  obtain ⟨B, hBP, hBE, p, hp, -, hcomm, α₃, hα₃⟩ :=
    sec8t84_modelI3 V Q hQ hdim hsgn (sec8t84hImg e S) hsyl x'' hnorm hsq ⟨α₂, hty''⟩
  have hne : p * x'' ≠ 1 := hα₃.1
  obtain ⟨B', hB'le, hB'E, x, hxcent, hxN, hxnot, hθx⟩ :=
    sec8t84h_lift hQ hdim hsgn e hodd hS hy'S hx hBP hBE hp hcomm hne
  refine ⟨B', hB'le, hB'E, x, hxcent, hxnot, α₃, ?_⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
    projOrthToProjSim Q (p * x''), hdim, hsgn, ?_, simHasType_projOrthToProjSim hα₃⟩
  exact hθx ▸ ffTheta_induces hQ (Or.inr ⟨hdim, Or.inr hsgn⟩) e ⟨x, hxN⟩

end CFSG.OddStandard.SmallF3.Omega
