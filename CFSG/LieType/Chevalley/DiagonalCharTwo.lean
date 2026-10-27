module

public import CFSG.LieType.Chevalley.BorelStructure

public section

namespace CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type} [Field R] [CharP R 2]

theorem eq_one_of_mem_diagonalGroup_of_sq_eq_one {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ diagonalGroup) (hg2 : g ^ 2 = 1) : g = 1 := by
  refine Units.ext (Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_)
  change (g : Module.End R (RootModule τ R)) (Finsupp.single b 1) =
    (1 : Module.End R (RootModule τ R)) (Finsupp.single b 1)
  obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hg b
  have hp : ((g ^ 2 : (Module.End R (RootModule τ R))ˣ) : Module.End R (RootModule τ R))
      (Finsupp.single b 1) = (c : R) ^ 2 • Finsupp.single b 1 := by
    rw [pow_two, Units.val_mul, Module.End.mul_apply, hc, map_smul, hc, smul_smul, pow_two]
  have hc2 : (c : R) ^ 2 = 1 := by
    rw [hg2, Units.val_one, Module.End.one_apply] at hp
    simpa using (congrArg (fun v : RootModule τ R => v b) hp).symm
  have hc1 : (c : R) = 1 := CharTwo.sq_inj.mp (hc2.trans (one_pow 2).symm)
  rw [hc, hc1, one_smul]
  rfl

theorem eq_one_of_mem_diagonalGroup_of_pow_two_pow_eq_one {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ diagonalGroup) {m : ℕ} (hgm : g ^ (2 ^ m) = 1) : g = 1 := by
  induction m with
  | zero => simpa using hgm
  | succ m ih =>
    apply ih
    apply eq_one_of_mem_diagonalGroup_of_sq_eq_one (Subgroup.pow_mem _ hg (2 ^ m))
    rw [← pow_mul, ← pow_succ]
    exact hgm

end CFSG.LieType.Chevalley
