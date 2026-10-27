module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafGLR
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafU34Exp
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Lin

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.GH74.Uniqueness.Bender

theorem autU34NoQ16Q16_holds :
    ∀ (F : Type) [Group F], CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSU 3 2 2 →
      NoQ16Q16 (MulAut F) := by
  intro F _ hF
  obtain ⟨e⟩ := (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff F 2 (by norm_num)).1 hF
  haveI : Finite F := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (MulAut F) := Nobq.finite_mulAut_of_finite F
  have hB : BenderType F 2 3 ((2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1)) :=
    BenderType.unitary 2 (by norm_num) e
  have hZ : Subgroup.center F = ⊥ := hB.center_eq_bot
  have hinj : Function.Injective (MulAut.conj : F →* MulAut F) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcZ : c ∈ Subgroup.center F := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut F => φ g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * c = c * g * c⁻¹ * c := by rw [hg]
        _ = c * g := by group
    rw [hZ, Subgroup.mem_bot] at hcZ
    exact hcZ
  have hO : Nobq.OutTwoCyclic ↥(CFSG.ComponentClassification.OuterAutomorphisms.inner F) :=
    Nobq.OutTwoCyclic.of_mulEquiv (MonoidHom.ofInjective hinj).symm
      (CFSG.ClassicalInvolution.Q3.TA3.outTwoCyclic_PSU hF (by norm_num))
  intro x y x' y' hq
  obtain ⟨g, hg, hg8⟩ := Q16Q16.exists_orderOf_eight_of_out
    (CFSG.ComponentClassification.OuterAutomorphisms.inner F)
    (CFSG.GH74.GLS.IVK.Proofs2.centralizer_inner_eq_bot_of_center_eq_bot hZ) hO hq
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.1 hg
  rw [orderOf_injective MulAut.conj hinj c] at hg8
  exact no_orderOf_eight_of_benderType hB hg8

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
