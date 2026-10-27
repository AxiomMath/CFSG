module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTheta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

theorem fg_oz_mem_sup_of_theta (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hL : commutator ↥L = ⊤)
    (s : ↥(Subgroup.normalizer (L : Set G))) (hs : SimInOmegaStar hQ (ffTheta hQ h e s)) :
    (s : G) ∈ L ⊔ Subgroup.centralizer (L : Set G) := by
  obtain ⟨y, hy_mem, hy⟩ := hs
  obtain ⟨l, hl⟩ := ffTheta_surjective_of_mem hQ h e ⟨y, hy_mem⟩
  let t : ↥(Subgroup.normalizer (L : Set G)) := ⟨(l : G), Subgroup.le_normalizer l.2⟩
  have hθ : ffTheta hQ h e t = ffTheta hQ h e s := hl.trans hy
  have hθu : ffTheta hQ h e (s * t⁻¹) = 1 := by
    rw [map_mul, map_inv, hθ]
    simp
  have hmem : ((s * t⁻¹ : ↥(Subgroup.normalizer (L : Set G))) : G) ∈
      Subgroup.centralizer (L : Set G) :=
    (ffTheta_eq_one_iff hQ h e hL (s * t⁻¹)).mp hθu
  have heq : ((s * t⁻¹ : ↥(Subgroup.normalizer (L : Set G))) : G) * (l : G) = (s : G) := by
    simp [t]
  have hsup : (s : G) ∈ Subgroup.centralizer (L : Set G) ⊔ L := by
    have h := Subgroup.mul_mem_sup hmem l.2
    rwa [heq] at h
  rw [sup_comm]
  exact hsup

end CFSG.OddStandard.SmallF3.Omega
