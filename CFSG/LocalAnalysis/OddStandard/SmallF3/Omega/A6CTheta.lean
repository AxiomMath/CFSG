module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem a6c_theta_homs (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (hL : commutator ↥L = ⊤) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    {X R : Subgroup G} (hXL : X ≤ L) (hRN : R ≤ normalizer (L : Set G))
    (hRX : R ≤ centralizer (X : Set G)) :
    ∃ (φ : ↥X →* ProjSim Q) (ψ : ↥R →* ProjSim Q),
      (∀ x : ↥X, φ x = 1 → x ∈ center ↥X) ∧
      (∀ x : ↥X, ∃ u : ↥(omegaProj hQ), φ x = projOrthToProjSim Q (u : ProjOrth Q)) ∧
      (∀ (x : ↥X) (r : ↥R), φ x * ψ r = ψ r * φ x) ∧
      ψ.ker = (centralizer (L : Set G)).subgroupOf R := by
  have hXN : X ≤ normalizer (L : Set G) := fun x hx => Subgroup.le_normalizer (hXL hx)
  refine ⟨(ffTheta hQ h e).comp (Subgroup.inclusion hXN),
    (ffTheta hQ h e).comp (Subgroup.inclusion hRN), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := (ffTheta_eq_one_iff hQ h e hL ⟨(x : G), hXN x.2⟩).mp hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx' (y : G) (hXL y.2)))
  · intro x
    exact ⟨e (QuotientGroup.mk ⟨(x : G), hXL x.2⟩),
      ffTheta_of_mem hQ h e ⟨(x : G), hXL x.2⟩⟩
  · intro x r
    show ffTheta hQ h e (Subgroup.inclusion hXN x) * ffTheta hQ h e (Subgroup.inclusion hRN r) =
      ffTheta hQ h e (Subgroup.inclusion hRN r) * ffTheta hQ h e (Subgroup.inclusion hXN x)
    rw [← map_mul, ← map_mul]
    refine congrArg (ffTheta hQ h e) (Subtype.ext ?_)
    exact Subgroup.mem_centralizer_iff.mp (hRX r.2) (x : G) x.2
  · ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ffTheta_eq_one_iff hQ h e hL ⟨(r : G), hRN r.2⟩

end CFSG.OddStandard.SmallF3.Omega
