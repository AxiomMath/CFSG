module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CanonicalBFixedHyperplane

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaTransitivity

open CFSG.LocalAnalysis.RankThreeUC.Section5

variable {G : Type} [Group G] [Finite G]

private theorem to_canonical {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {D : Subgroup G} (hD : D ∈ Delta p P ρ) :
    ∃ s ∈ twoCoreCommutator T B, ⁅B, P⁆ = D.map (MulAut.conj s).toMonoidHom := by
  obtain ⟨s, hs, hB⟩ := OrbitHasBFixedMember.exists_member hc hD
  refine ⟨s, hs, ?_⟩
  have hmem := DeltaConjugationAction.map_mem (p := p) hc.faithfulBinaryIrreducibleAction.normal ρ s hD
  have hB' : B ≤ Subgroup.normalizer
      ((D.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := fun b hb => hB b hb
  exact ((CanonicalBFixedHyperplane.canonical hc).2.2 _ hmem hB').symm

theorem transitive {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    ∀ D1 ∈ Delta p P ρ, ∀ D2 ∈ Delta p P ρ,
      ∃ s ∈ twoCoreCommutator T B, D2 = D1.map (MulAut.conj s).toMonoidHom := by
  intro D1 h1 D2 h2
  obtain ⟨s1, hs1, e1⟩ := to_canonical hc h1
  obtain ⟨s2, hs2, e2⟩ := to_canonical hc h2
  refine ⟨s2⁻¹ * s1, (twoCoreCommutator T B).mul_mem ((twoCoreCommutator T B).inv_mem hs2) hs1, ?_⟩
  have : D2 = (D2.map (MulAut.conj s2).toMonoidHom).map (MulAut.conj s2⁻¹).toMonoidHom := by
    rw [Subgroup.map_map]
    have : (MulAut.conj s2⁻¹).toMonoidHom.comp (MulAut.conj s2).toMonoidHom = MonoidHom.id G := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [this]; simp
  rw [this, ← e2, e1, Subgroup.map_map]
  congr 1
  ext x; simp [MulAut.conj_apply, mul_assoc]

end CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaTransitivity
