module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34LocalGroup
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.L34Local

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

theorem localData_eZero {k : Type} [Field k] (hk : Nat.card k = 4) :
    LocalData (projectiveSL 3 k) (eZero k) where
  card_eq := card_eZero hk
  card_normalizer := card_normalizer_eZero hk
  centralizer_le := fun t ht ht1 g hg => by
    rw [← centralizer_eq_of_card_eq_nine hk (card_eZero hk) ht ht1]
    exact Subgroup.mem_centralizer_singleton_iff.2 hg
  trans := fun x hx hx1 y hy hy1 =>
    exists_mem_normalizer_conj_eq_of_card_eq_nine hk (card_eZero hk) hx hx1 hy hy1
  aut := by
    intro f hf
    have := LinearFieldFour.finite_of_card_eq_four hk
    have := LinearFieldFour.charP_two_of_card_eq_four hk
    have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
    obtain ⟨e, he, hfe⟩ := (forall_fixes_eZero_iff hk hσ f).1 hf
    refine ⟨e, he, fun n hn => ?_⟩
    rcases hfe with rfl | rfl
    · simp [MulAut.conj_apply]
    · have hβ : betaAut (frobeniusEquiv k 2) n = n := by
        rw [← autFixed_betaAut hk hσ] at hn
        exact hn
      simp [MulAut.mul_apply, hβ, MulAut.conj_apply]

theorem nonempty_equiv_of_isLinThreeFour {K : Type} [Group K] (h : IsLinThreeFour K) :
    Nonempty (K ≃* projectiveSL 3 (GaloisField 2 2)) := by
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := h
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨p, f, hp, hf⟩ := q
  simp only at hqp hqe
  subst hqp hqe
  have eC := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 ⟨2, 2, hp, hf⟩ hv
  exact ⟨(e.trans eC).trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField 2 2))⟩

theorem card_sylow_three {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 20160)
    (P : Sylow 3 G) : Nat.card P = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : Nat.factorization (Nat.card G) 3 = 2 := by
    rw [hG, Nat.factorization_def _ Nat.prime_three]
    rw [show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [Sylow.card_eq_multiplicity, hf]
  norm_num

end KFactProofs.L34Local

section

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34 (card_projectiveSL eZero exists_eq_map_conj_eZero)

theorem kFactL34Local : KFactL34Local := by
  intro K _ _ hK T
  obtain ⟨ε₀⟩ := KFactProofs.L34Local.nonempty_equiv_of_isLinThreeFour hK
  have hk : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hK20 : Nat.card K = 20160 := by
    rw [Nat.card_congr ε₀.toEquiv]
    exact card_projectiveSL hk
  have hTcard : Nat.card (T : Subgroup K) = 9 := KFactProofs.L34Local.card_sylow_three hK20 T
  have hP₁ : Nat.card ((T : Subgroup K).map ε₀.toMonoidHom) = 9 := by
    rw [← hTcard]
    exact (Nat.card_congr (ε₀.subgroupMap (T : Subgroup K)).toEquiv).symm
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hP₁
  let ε : projectiveSL 3 (GaloisField 2 2) ≃* K := (MulAut.conj g).trans ε₀.symm
  have hεT : ∀ y, y ∈ eZero (GaloisField 2 2) ↔ ε y ∈ (T : Subgroup K) := by
    intro y
    have h1 : ε y ∈ (T : Subgroup K) ↔ g * y * g⁻¹ ∈ (T : Subgroup K).map ε₀.toMonoidHom := by
      rw [Subgroup.mem_map_equiv]
      rfl
    rw [h1, hg, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group]
  exact ((KFactProofs.L34Local.localData_eZero hk).map ε hεT).conclusion

end

end CFSG.AGLEmbedding
