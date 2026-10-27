module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CU4Diag
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CSplit

public section

namespace CFSG.ComponentClassification.GSThmB.Cent516

open CFSG Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open CFSG.ComponentClassification.CatFactsL4U4 InvClassU

variable {Y : Type} [Group Y] [Finite Y] {p f : ℕ} {K : Type} [Field K]
  (hZ : Nat.card (center Y) = 2) (hp : p.Prime) (hp2 : p ≠ 2) (h : UnitaryFieldData p f K)
  (e : Y ⧸ center Y ≃* hypPSU h 2 0) (α : MulAut Y)

include hZ hp hp2 in
theorem diagU_bar {A : GL (HypIndex 2 0) K} (hA : A ∈ hypUnitary h 2 0) {σ : K ≃+* K}
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex 2 0) K) ∈ semilinearSimilitudes h 2 0)
    (hα' : MulAut.congr e (barAut α) = semilinearAutHom h one_le_two zero_le_one ⟨_, hx⟩)
    (hσ : ∀ c, σ c = h.bar c) {c : K} (hc0 : c ≠ 0)
    (hAA : (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (A : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar = c • 1) :
    Concl516 Y α (p ^ f) := by
  have := h.finite
  obtain ⟨ψ, hψ, hψs⟩ := exists_comm_conj_of_bar h hp2 (by norm_num) hA hc0 hAA
  have hfix : ∀ g, barAut α ((e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) g) =
      (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)) g := fun g =>
    barAut_fixed_of_congr e α hα'
      (fixed_of_comm_bar h (by norm_num) (by norm_num) hσ hx ψ hψ _ ⟨g, rfl⟩)
  have hout := outer_of_congr e α hα' (not_inner_bar h hx hA hσ)
  have hgood := hgood_SL2 hp hp2 h.card_fixedField
  have heven := even_card_range_hypProj_comp ψ (slQuatI_pow_four (K := h.fixedField)) hψs
  have h2d : 2 ∣ Nat.card (e.symm.toMonoidHom.comp ((hypProj h 2 0).comp ψ)).range := by
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective (by exact e.symm.injective)]
    exact even_iff_two_dvd.mp heven
  exact concl516_outer hZ α _ hfix hgood hout (four_dvd_range hgood h2d)

include hZ hp hp2 in
theorem cent516_unitary_of_equiv [Group.IsPerfect Y]
    (hcov : p ^ f % 4 = 1 → ∃ σ : hypSU h 2 0 →* Y, Function.Injective σ ∧
      ∀ g, piZ (σ g) = e.symm (hypProj h 2 0 g))
    (hα : α ^ 2 = 1) : Concl516 Y α (p ^ f) := by
  by_cases h1 : barAut α = 1
  · exact concl516_one inferInstance α h1
  have hβ1 : MulAut.congr e (barAut α) ≠ 1 := fun h0 =>
    h1 ((MulAut.congr e).injective (by rw [h0, map_one]))
  have hβ2 : MulAut.congr e (barAut α) ^ 2 = 1 := by
    rw [← map_pow, barAut_sq hα, map_one]
  obtain ⟨A, σ, hx, hA, hαeq, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp2 (by norm_num) (by norm_num)
      (by norm_num)).2.2.2 _ (orderOf_eq_prime hβ2 hβ1)
  rcases hσ with rfl | hσ
  · obtain ⟨l, -, -, hcls⟩ := classify_inv_U4 h hp2 hA (hrefl rfl)
    rcases hcls with ⟨-, ⟨v, hv, hAv⟩ | ⟨d, hd, v, hv, hAv⟩⟩ |
      ⟨hN, e', g', hAe, hAg, hee, hgg, heg⟩
    · exact diagU_t2 hZ hp hp2 h e α hx hA hαeq.symm hv hAv
    · exact diagU_D1 hZ hp hp2 h e α hx hA hαeq.symm hd hv hAv
    · exact diagU_pair hZ hp hp2 h e α hx hA hαeq.symm hcov hN hAe hAg hee hgg heg
  · obtain ⟨c, hc0, hAA⟩ := hbar hσ
    exact diagU_bar hZ hp hp2 h e α hA hx hαeq.symm hσ hc0 hAA

theorem cent516_unitary (hY : IsQuasisimple Y) (hZ : Nat.card (center Y) = 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) (hm : Blueprint.LieModel (Y ⧸ center Y) .PSU 4 p f)
    (α : MulAut Y) (hα : α ^ 2 = 1) : Concl516 Y α (p ^ f) := by
  have := hY.1
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty ((Y ⧸ center Y) ≃*
        Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (p ^ f) K)) := by
    rcases hm with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  exact cent516_unitary_of_equiv hZ hp hp2 h
    (e₀.trans (hypPSUEquivStatedProj h hR₀ (by norm_num)).symm) α
    (fun hq => exists_cover_U4 hZ h hp2 hq e₀ hR₀) hα

end CFSG.ComponentClassification.GSThmB.Cent516

namespace CFSG.ComponentClassification.GSThmB

theorem cf516CentU4 : CF516CentU4 := fun _ _ _ hY hZ _ _ hp hp2 hf hm α hα =>
  Cent516.cent516_unitary hY hZ hp hp2 hf hm α hα

theorem cf516Cent : CF516Cent := cf516Cent_of_unitary cf516CentU4

end CFSG.ComponentClassification.GSThmB
