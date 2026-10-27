module

public import CFSG.LieType.Chevalley.EvenRootCommutatorRows

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley RootOps
open scoped commutatorElement

theorem d4_even_root_pair_relations
    {R : Type*} [CommRing R] [CharP R 2]
    {α β : Fin Tag.D4.rank → ℤ} (hα : IsRoot .D4 α) (hβ : IsRoot .D4 β) (hne : α ≠ β)
    (hne' : α ≠ -β) (s t : R) :
    (IsRoot .D4 (α + β) →
      ⁅pinnedX .D4 R α s, pinnedX .D4 R β t⁆ = pinnedX .D4 R (α + β) (s * t)) ∧
    (¬IsRoot .D4 (α + β) → ⁅pinnedX .D4 R α s, pinnedX .D4 R β t⁆ = 1) := by
  have h2 : (2 : R) = 0 := CharTwo.two_eq_zero
  obtain ⟨row, hrow, w, hwα, hwβ, hfr, hcomm⟩ :=
    exists_pairTable_commutatorElement_of_two_eq_zero hα hβ hne hne'
  have hc := hcomm R h2 s t
  have hfac := ((rank_two_pair_certificate .D4).2 row hrow).2.2.2.2.2.2.2.2.1
  have hrows : row.2.2.2 = [] ∨ row.2.2.2 = [(1, 1, 19, -1)] := by
    simp only [pairTable, d4PairTable, List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with rfl | rfl | rfl | rfl | rfl <;> simp
  rcases hrows with h0 | h1
  ·
    have hnot : ¬IsRoot .D4 (α + β) := by
      intro hab
      have hab' : IsRoot .D4 (orbitCertRoot .D4 row.1 + orbitCertRoot .D4 row.2.1) := by
        have := IsRoot.smul hab w⁻¹
        rwa [smul_add, ← hwα, ← hwβ, inv_smul_smul, inv_smul_smul] at this
      obtain ⟨a, ha, hae⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .D4) hab'
      obtain ⟨C, hC⟩ := (hfac 1 1 (certWitnessPos .D4 a)).2 ⟨one_pos, one_pos,
        certWitnessPos_lt ha, by rw [orbitCertRoot_certWitnessPos ha, hae, one_nsmul, one_nsmul]⟩
      rw [h0] at hC
      exact List.not_mem_nil hC
    refine ⟨fun h => absurd h hnot, fun _ => ?_⟩
    rw [hc, h0, List.map_nil, List.prod_nil]
  · refine ⟨fun _ => ?_, fun hnot => absurd ?_ hnot⟩
    · rw [hc, h1]
      simp [CharTwo.neg_eq]
    · have := hfr (1, 1, 19, -1) (h1 ▸ List.mem_cons_self)
      simpa only [one_nsmul] using this

end CFSG.LieType.Chevalley
