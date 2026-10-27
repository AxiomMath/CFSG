module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFRankAutGrp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Sign

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem ffOutFFRankAutOrth_card_comap {Γ A : Type*} [Group Γ] [Group A] (φ : Γ →* A)
    (hφ : Function.Bijective φ) (X : Subgroup A) : Nat.card (X.comap φ) = Nat.card X := by
  have h := Subgroup.card_map_of_injective (K := X.comap φ) hφ.1
  rw [Subgroup.map_comap_eq_self_of_surjective hφ.2] at h
  exact h.symm

private theorem ffOutFFRankAutOrth_norms (o : Option (Fin 5)) :
    ffRADPlus ((finSuccEquiv 5).symm o) = ffC o := by
  cases o with
  | none => simp [finSuccEquiv_symm_none, ffRADPlus, ffC]
  | some i => fin_cases i <;> simp [finSuccEquiv_symm_some, ffRADPlus, ffC]

private theorem ffOutFFRankAutOrth_basis_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1) :
    ∃ b : Module.Basis (Fin 6) (ZMod 3) V,
      ∀ x, Q x = ∑ i, ffRADPlus i * (b.repr x i) ^ 2 := by
  obtain ⟨fr⟩ := exists_pframe_six_plus hQ hdim hsgn
  refine ⟨fr.b.reindex (finSuccEquiv 5).symm, fun x => ?_⟩
  rw [fr.map_eq x]
  refine Fintype.sum_equiv (finSuccEquiv 5).symm _ _ fun o => ?_
  rw [Module.Basis.repr_reindex_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    ffOutFFRankAutOrth_norms]

theorem ffRA_mulAut_omega_plus
    (hchk : FFRAGroup 512 ffRADPlus false 32 ∧ FFRAGroup 1024 ffRADMinus true 32)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (X : Subgroup (MulAut ↥(omegaProj hQ))) (hp : IsPGroup 2 X) (hc : IsMulCommutative X) :
    Nat.card X ≤ 32 := by
  obtain ⟨b, hb⟩ := ffOutFFRankAutOrth_basis_plus hQ hdim hsgn
  have hd : ∀ i, ffRADPlus i ≠ 0 := fun i => by fin_cases i <;> decide
  have hs := ffRASide_of_group hchk.1
  have hcard : Nat.card (ProjSim Q) = 512 * 47385 := by
    rw [ff_natCard_projSim_six_plus hQ hdim hsgn]
  haveI : Finite (ProjSim Q) :=
    Nat.finite_of_card_ne_zero (by rw [ff_natCard_projSim_six_plus hQ hdim hsgn]; norm_num)
  have hφ := ffSimOmegaAct_bijective_six_plus hQ hdim hsgn
  set φ : ProjSim Q →* MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ (by omega) with hφdef
  have hE2 : IsPGroup 2 (X.comap φ) := hp.comap_of_injective φ hφ.1
  have hEc : IsMulCommutative (X.comap φ) := by
    refine ⟨⟨fun a b => Subtype.ext (hφ.1 ?_)⟩⟩
    have h := hc.1.1 ⟨φ a, a.2⟩ ⟨φ b, b.2⟩
    have h' := congrArg Subtype.val h
    simpa [map_mul] using h'
  have h := ffRA_projSim_abelian_le b hb hd (k := 9) (m := 47385) (by norm_num)
    ⟨23692, by norm_num⟩ hcard hs (X.comap φ) hE2 hEc
  rwa [ffOutFFRankAutOrth_card_comap φ hφ] at h

theorem ffRA_mulAut_omega_minus
    (hchk : FFRAGroup 512 ffRADPlus false 32 ∧ FFRAGroup 1024 ffRADMinus true 32)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1)
    (X : Subgroup (MulAut ↥(omegaProj hQ))) (hX : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 32 := by
  obtain ⟨fr⟩ := exists_nframe_six_unit hQ hdim hsgn 1
  have hb : ∀ x, Q x = ∑ i, ffRADMinus i * (fr.b.repr x i) ^ 2 := by
    intro x
    rw [fr.map_eq x, Finset.mul_sum]
    simp [ffRADMinus]
  have hd : ∀ i, ffRADMinus i ≠ 0 := fun i => by simp [ffRADMinus]
  have hs := ffRASide_of_group hchk.2
  have hcard : Nat.card (ProjSim Q) = 1024 * 25515 := by
    rw [ff_natCard_projSim_six_minus hQ hdim hsgn]
  haveI : Finite (ProjSim Q) :=
    Nat.finite_of_card_ne_zero (by rw [ff_natCard_projSim_six_minus hQ hdim hsgn]; norm_num)
  have hφ := ffSimOmegaAct_bijective_six_minus hQ hdim hsgn
  set φ : ProjSim Q →* MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ (by omega) with hφdef
  have hE : ∀ x ∈ X.comap φ, x * x = 1 := by
    intro x hx
    apply hφ.1
    rw [map_mul, map_one]
    exact hX _ hx
  have h := ffRA_projSim_elemAb_le fr.b hb hd (k := 10) (m := 25515) (by norm_num)
    ⟨12757, by norm_num⟩ hcard hs (X.comap φ) hE
  rwa [ffOutFFRankAutOrth_card_comap φ hφ] at h

end CFSG.OddStandard.SmallF3.Omega
