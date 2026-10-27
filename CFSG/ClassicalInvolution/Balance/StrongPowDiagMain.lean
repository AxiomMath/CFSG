module

public import CFSG.ClassicalInvolution.Balance.StrongPowDiagGlue
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagLinear
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagUnitary
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagSp

public section

namespace CFSG.ClassicalInvolution.Balance.BootRank3

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance.StrongBalance
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Transport

variable {K K' X : Type*} [Group K] [Group K'] [Group X]

theorem range_comp_symm (ε : K ≃* K') (ψ : K →* X) :
    (ψ.comp ε.symm.toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ε.symm.surjective,
    ← MonoidHom.range_eq_map]

theorem ker_comp_symm_le_center (ε : K ≃* K') (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) :
    (ψ.comp ε.symm.toMonoidHom).ker ≤ Subgroup.center K' := by
  intro x hx
  have h1 : ε.symm x ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  apply ε.symm.injective
  rw [map_mul, map_mul]
  exact h1 (ε.symm y)

end Transport

theorem deltaDiagOn_PSL : DeltaDiagOn 2 .PSL (fun _ _ _ => True) := by
  intro n p e hp _ hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral d hd x hx
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hε⟩ := htoral.1 rfl
  have hn : 2 ≤ n := hadm.2.2.1
  have hrange := range_comp_symm ε ψ
  refine Linear.deltaCore_trivial_gf hn hp2 h5 (ψ.comp ε.symm.toMonoidHom)
    (ker_comp_symm_le_center ε ψ hker) (by rw [hrange]; exact hnorm) hcard hF2
    (fun f hf hf1 h => hfaith f hf hf1 (by rwa [hrange] at h)) hε hd ?_
  rwa [hrange]

theorem deltaDiagOn_PSU : DeltaDiagOn 2 .PSU (fun _ _ _ => True) := by
  intro n p e hp _ hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral d hd x hx
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hε⟩ := htoral.2.1 rfl
  have hn : 3 ≤ n := hadm.2.2.1
  have hrange := range_comp_symm ε ψ
  refine Unitary.deltaCore_trivial_su_gf hp2 h5 hn (ψ.comp ε.symm.toMonoidHom)
    (ker_comp_symm_le_center ε ψ hker) (by rw [hrange]; exact hnorm) hcard hF2 hε hd ?_
  rwa [hrange]

theorem deltaDiagOn_PSp_two : DeltaDiagOn 2 .PSp (fun n _ _ => n = 2) := by
  intro n p e hp hn hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral d hd x hx
  subst hn
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hε⟩ := htoral.2.2.1 rfl
  have hrange := range_comp_symm ε ψ
  refine Sp.deltaCore_trivial_psp_two hp2 h5 (ψ.comp ε.symm.toMonoidHom)
    (ker_comp_symm_le_center ε ψ hker) (by rw [hrange]; exact hnorm) hcard hF2
    (fun f hf hf1 h => hfaith f hf hf1 (by rwa [hrange] at h)) hε hd ?_
  rwa [hrange]

@[expose] def provedOrdDiag : StatedLieTag → ℕ := fun _ => 2

@[expose] def provedModelsDiag (t : StatedLieTag) (n _p _e : ℕ) : Prop :=
  (t = .PSp ∧ n = 2) ∨ t = .PSL ∨ t = .PSU

theorem deltaDiagAll_provedModels : DeltaDiagAll provedOrdDiag provedModelsDiag := by
  intro t n p e hp hq
  rcases hq with ⟨rfl, rfl⟩ | rfl | rfl
  · exact deltaDiagOn_PSp_two 2 p e hp rfl
  · exact deltaDiagOn_PSL n p e hp trivial
  · exact deltaDiagOn_PSU n p e hp trivial

theorem bootNoTriple_of_goodBootData_provedDiag (h27 : p ^ f ≠ 27)
    (h : GoodBootDataDiagExists p f provedOrdDiag provedModelsDiag) : BootNoTriple p f :=
  bootNoTriple_of_goodBootData_diag h27 deltaDiagAll_provedModels h

end CFSG.ClassicalInvolution.Balance.BootRank3
