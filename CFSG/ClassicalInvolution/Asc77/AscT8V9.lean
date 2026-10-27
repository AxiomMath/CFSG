module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectKB
public import CFSG.ClassicalInvolution.Asc77.AscMuTabEdge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open scoped MatrixGroups

namespace T8V

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}


theorem dstarConnected_psl4 (M : Ih8Model p f Ω .PSL 4 e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq4 : p ^ f % 4 = 1) : T3.DStarConnected Ω := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hsys := WeakCT.weakCTSystem_standard (K := GaloisField p e) 3
  have h := fundamentalSubgroups_psl_eq (p := p) (f := e) (m := 3) (by norm_num)
  let L : Fin 3 → Subgroup (modelUniv .PSL 4 p e Fact.out).K := fun i =>
    (WeakCT.blockSL2 (GaloisField p e) 3 i).range
  have hLmem : ∀ i, L i ∈ M.cls := fun i => by
    refine M.fund_subset_cls hne hG2 hD4 ?_
    rw [h]
    exact ⟨_, Models.isLongRootSL2_range_blockSL h2 (j := (i : ℕ)) (by have := i.isLt; omega)⟩
  have hadj : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      dstarAdj Ω ((L i).map M.ψ) ((L j).map M.ψ) := fun i j hj =>
    M.muTab_dstarAdj_linear hΩ hp2 hq hD4 hnpsl hq4 (hLmem i) (hLmem j) (hsys.pair i j hj)
  refine M.dstarConnected_of_gens hΩ hG2 hD4 L 0 hLmem (WeakCT.iSup_range_blockSL2 3) ?_
  intro i
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (hadj 0 1 rfl)
  · exact (Relation.ReflTransGen.single (hadj 0 1 rfl)).tail (hadj 1 2 rfl)

theorem dstarConnected_psu4 (M : Ih8Model p f Ω .PSU 4 e) (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) (hq3 : p ^ f % 4 = 3) : T3.DStarConnected Ω := by
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSU = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  have hq2 : p ^ e ≠ 2 := by
    intro h
    have hd : p ∣ 2 := h ▸ dvd_pow_self p (by omega : e ≠ 0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hd)
  obtain ⟨φ, hφ⟩ := psu_model_equiv hp2 M.admissible
  have hsys := Phan.weakPhanA_standard hK hq2 3
  let L : Fin 3 → Subgroup (modelUniv .PSU 4 p e Fact.out).K := fun i =>
    (Phan.standardU (GaloisField p (2 * e)) p e 3 i).map φ.symm.toMonoidHom
  have hLmem : ∀ i, L i ∈ M.cls := fun i => by
    refine M.fund_subset_cls hne hG2 hD4 ?_
    show (Phan.standardU (GaloisField p (2 * e)) p e 3 i).map φ.symm.toMonoidHom ∈ _
    rw [hφ, muTab_map_equiv_symm_map]
    exact ⟨_, Models.isLongRootSU2_range_blockEmb hK hp2 (by have := i.isLt; omega)⟩
  have hadj : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      dstarAdj Ω ((L i).map M.ψ) ((L j).map M.ψ) := fun i j hj =>
    M.muTab_dstarAdj_unitary hΩ hp2 hq hD4 hnpsl hq3 (hLmem i) (hLmem j)
      (Models.unitaryBlockStandardPair_map (hsys.pair i j hj) φ.symm.toMonoidHom φ.symm.injective)
  refine M.dstarConnected_of_gens hΩ hG2 hD4 L 0 hLmem ?_ ?_
  · show ⨆ i, (Phan.standardU (GaloisField p (2 * e)) p e 3 i).map φ.symm.toMonoidHom = ⊤
    rw [← Subgroup.map_iSup, hsys.gen, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr φ.symm.surjective
  · intro i
    fin_cases i
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (hadj 0 1 rfl)
    · exact (Relation.ReflTransGen.single (hadj 0 1 rfl)).tail (hadj 1 2 rfl)

end T8V

end CFSG.ClassicalInvolution.Asc77
