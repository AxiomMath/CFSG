module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41GPh
public import CFSG.GH74.NoComponent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY13

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup
open scoped Pointwise

namespace S4A

variable {G : Type} [Group G] [Finite G]

theorem sectionalTwoRankLE_of_sylow_rank (S : Sylow 2 G) {r : ℕ}
    (hrank : ∀ Q : Subgroup G, Q ≤ (S : Subgroup G) →
      ∃ s : Finset G, s.card ≤ r ∧ closure (s : Set G) = Q) :
    GH74.SectionalTwoRankLE G r := by
  classical
  intro P hP
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  have hle : P.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hPR
  obtain ⟨s, hs, hsP⟩ := hrank _ hle
  refine ⟨s.image (MulAut.conj g⁻¹), Finset.card_image_le.trans hs, ?_⟩
  have himg : (↑(s.image (MulAut.conj g⁻¹)) : Set G) =
      (MulAut.conj g⁻¹).toMonoidHom '' (s : Set G) := by
    rw [Finset.coe_image]; rfl
  rw [himg, ← MonoidHom.map_closure, hsP, Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem l41_sylow_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (hc : L41GPh1 t L S x₁ x₂ lam rho) (hgen : ¬ GH74.Gen4 G) : Lemma4_2Concl S := by
  by_contra hodd
  have hS : IsPGroup 2 S := hc.isPGroup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hgen
    (sectionalTwoRankLE_of_sylow_rank (hS.toSylow hodd) fun Q hQ => hc.basic.rank_S Q hQ)

end S4A

theorem l41_sylow_holds : L41SylowStmt := by
  intro G _ _ t L S x₁ x₂ lam rho hc
  refine S4A.l41_sylow_of hc.toG fun hgen4 => ?_
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push_neg at hcon
    haveI : IsSimpleGroup G := hc.glob.simple
    letI : CommGroup G := { ‹Group G› with mul_comm := fun a b => hcon a b }
    have hprime : (Nat.card G).Prime := IsSimpleGroup.prime_card
    rcases hprime.eq_one_or_self_of_dvd (2 ^ 11) hc.glob.dvd with h1 | h1
    · norm_num at h1
    · rw [← h1] at hprime
      norm_num at hprime
  have hconcl := hc.inputs.gh74 G hc.glob.simple hnonab
    (CFSG.OddStandard.SmallF3.FritzII.three_le_twoRank_of_ctx0 hc.toCtx0) hgen4
  exact hc.glob.not_catalog (CFSG.GH74.catalog_of_ghList hconcl.ghList)

end CFSG.OddStandard.SmallF3.HarrisU33
