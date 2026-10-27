module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def e6Weight : Fin Tag.E6.rank → ℤ := ![1, 0, 2, 0, 1, 2]

@[expose] def e6Cube : Fin Tag.E6.rank → ℤ := ![0, 0, 1, -1, 0, 1]

theorem e6_cartan_weight (i : Fin Tag.E6.rank) :
    ∑ l, Tag.E6.cartan i l * e6Weight l = 3 * e6Cube i := by
  revert i
  decide

@[expose] def e6Invariant (K : Type) [Field K] : (Fin Tag.E6.rank → Kˣ) →* Kˣ where
  toFun b := ∏ l, b l ^ e6Weight l
  map_one' := by simp
  map_mul' x y := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem e6Invariant_apply {K : Type} [Field K] (b : Fin Tag.E6.rank → Kˣ) :
    e6Invariant K b = ∏ l, b l ^ e6Weight l :=
  rfl

theorem e6Invariant_torus {K : Type} [Field K] (i : Fin Tag.E6.rank) (s : Kˣ) :
    e6Invariant K (fun j => s ^ Tag.E6.cartan i j) = (s ^ e6Cube i) ^ 3 := by
  rw [e6Invariant_apply]
  simp only [← zpow_mul]
  rw [prod_zpow_eq_zpow_sum, e6_cartan_weight, mul_comm, zpow_mul]
  norm_num

theorem exists_cube_of_mem_torusGroup {K : Type} [Field K]
    {g : ModGL Tag.E6 K} (hg : g ∈ torusGroup Tag.E6 K) :
    ∃ b : Fin Tag.E6.rank → Kˣ, rootDiagUnit Tag.E6 b = g ∧
      ∃ z : Kˣ, z ^ 3 = e6Invariant K b := by
  let P : Subgroup (Fin Tag.E6.rank → Kˣ) :=
    Subgroup.comap (e6Invariant K) (powMonoidHom 3 : Kˣ →* Kˣ).range
  have hle : torusGroup Tag.E6 K ≤ P.map (rootDiagUnitHom Tag.E6 K) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    refine ⟨fun j => s ^ Tag.E6.cartan i j, ?_, (torusElt_eq_rootDiagUnit i s).symm⟩
    exact ⟨s ^ e6Cube i, by rw [powMonoidHom_apply, e6Invariant_torus]⟩
  obtain ⟨b, ⟨z, hz⟩, hb⟩ := hle hg
  exact ⟨b, hb, z, hz⟩

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
