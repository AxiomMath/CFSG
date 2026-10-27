module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Quasithin.SmithCurtis CoxeterSystem

variable {Ĝ G : Type*} [Group Ĝ] [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*}
  [Group W] {cs : CoxeterSystem M W} {p : ℕ}
variable [Finite Ĝ] [Fact p.Prime] {D : CurtisDatum G cs p} {π : Ĝ →* G}
  {C : CentralCoverData D π p} {F : B → Type} [∀ s, Field (F s)] {R : CoverRankOne C F}
  [Fintype B]

omit [Fintype B] in
theorem IsCoverType.chi_one {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k Ĝ V} {y : V} {χ : Ĝ → k} {J : Finset B}
    (ht : IsCoverType R ρ y χ J) : χ 1 = 1 := by
  have e := ht.2.2.1 1 (one_mem _)
  rw [map_one, Module.End.one_apply] at e
  exact smul_left_injective k ht.2.1 (e.symm.trans (one_smul k y).symm)

omit [Fintype B] in
theorem IsCoverType.chi_mul_of_mem {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k Ĝ V} {y : V} {χ : Ĝ → k} {J : Finset B}
    (ht : IsCoverType R ρ y χ J) {h h' : Ĝ}
    (hh : h ∈ D.H.comap π) (hh' : h' ∈ D.H.comap π) : χ (h * h') = χ h * χ h' := by
  have e := ht.2.2.1 (h * h') (mul_mem hh hh')
  rw [map_mul, Module.End.mul_apply, ht.2.2.1 h' hh', map_smul, ht.2.2.1 h hh, smul_smul,
    mul_comm] at e
  exact (smul_left_injective k ht.2.1 e).symm

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
