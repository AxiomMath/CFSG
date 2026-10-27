module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47Order
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2FieldCent
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

theorem sq_mem_inn_of_right_mul_self {S : Type} [Group S] {F : Type} [Field F] [Finite F]
    (e : S ≃* PSL2 F) (x : MulAut S) (h1 : (autEquiv e x).right * (autEquiv e x).right = 1) :
    x ^ 2 ∈ (MulAut.conj : S →* MulAut S).range := by
  have hmem : autEquiv e x * autEquiv e x ∈ pGammaL2PSLRange F := by
    rw [mem_pslRange_iff, sqLeft_mul]
    exact ⟨by rw [SemidirectProduct.mul_right]; exact h1, Iff.rfl⟩
  rw [← map_autEquiv_innAut e] at hmem
  obtain ⟨z, hz, hzx⟩ := hmem
  have : z = x ^ 2 := by
    apply (autEquiv e).injective
    rw [pow_two, map_mul]
    exact hzx
  rw [← this]
  exact hz

theorem commutatorElement_mem_of_index_two {G : Type*} [Group G] {H : Subgroup G}
    (hH : H.index = 2) (x y : G) : ⁅x, y⁆ ∈ H := by
  rw [commutatorElement_def, mul_mem_iff_of_index_two hH, mul_mem_iff_of_index_two hH,
    mul_mem_iff_of_index_two hH, inv_mem_iff, inv_mem_iff]
  tauto

theorem commutator_eq_map_perfectResidual {G : Type*} [Group G] [Finite G] (C : Subgroup G)
    (h2 : 2 * Nat.card (perfectResidual ↥C) = Nat.card C) :
    ⁅C, C⁆ = (perfectResidual ↥C).map C.subtype := by
  have hi : (perfectResidual ↥C).index = 2 := by
    have h1 := (perfectResidual ↥C).card_mul_index
    rw [← h2, mul_comm 2] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  apply le_antisymm
  · rw [commutator_le]
    intro a ha b hb
    exact ⟨⁅⟨a, ha⟩, ⟨b, hb⟩⁆, commutatorElement_mem_of_index_two hi _ _, rfl⟩
  · have h1 : perfectResidual ↥C ≤ commutator ↥C := by
      rw [← derivedSeries_one]
      exact iInf_le (fun n => derivedSeries (↥C) n) 1
    calc (perfectResidual ↥C).map C.subtype ≤ (commutator ↥C).map C.subtype := map_mono h1
      _ = ⁅C, C⁆ := by
        rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]

theorem footeL2RootedOuter :
    ∀ (S : Type) [Group S] [Finite S],
      (Nonempty (S ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel S .PSL 2 p f) →
      ∀ y : MulAut S, y ^ 4 = 1 → y ^ 2 ≠ 1 → y ^ 2 ∉ (MulAut.conj : S →* MulAut S).range →
        IsSimpleGroup ↥⁅MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S),
          MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S)⁆ ∧
        2 ≤ CFSG.pRank 2 ↥⁅MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S),
          MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S)⁆ ∧
        ∀ σ : MulAut S,
          (∀ j ∈ ⁅MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S),
            MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S)⁆, σ j = j) →
          σ = 1 ∨ σ = y ^ 2 := by
  intro S _ _ hS y hy4 hy2 hyinn
  rcases hS with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact absurd (sq_mem_inn_of_a7 e y) hyinn
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hL
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hσ : (autEquiv e y).right * (autEquiv e y).right ≠ 1 := fun h =>
    hyinn (sq_mem_inn_of_right_mul_self e y h)
  have hσ2 : (autEquiv e y).right ^ 2 ≠ 1 := by rwa [pow_two]
  have hσ4 : (autEquiv e y).right ^ 4 = 1 := by
    rw [← right_pow, ← map_pow, hy4, map_one, SemidirectProduct.one_right]
  have hord : orderOf (autEquiv e y).right = 2 ^ 2 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one])
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact hσ4)
  obtain ⟨m, hm⟩ : 4 ∣ f := by
    have h1 := orderOf_dvd_natCard (autEquiv e y).right
    rw [card_ringAut F hp hF, hord] at h1
    simpa using h1
  have h16 : 16 ∣ p ^ f - 1 := by
    rw [hm, mul_comm, pow_mul]
    exact sixteen_dvd_pow_four_sub_one (hp.odd_of_ne_two hp2).pow
  have hfe : Even f := ⟨2 * m, by omega⟩
  have hH : HarrisHyp F := harrisHyp_of hp hp2 hF hfe h16
  have hY4 : ∃ z : S, z ^ 4 = 1 ∧ z ^ 2 ≠ 1 := by
    obtain ⟨z, hz4, hz2⟩ := exists_psl2_pow_four (F := F) (by have := hH.four_le; omega)
    refine ⟨e.symm z, by rw [← map_pow, hz4, map_one], fun h => hz2 ?_⟩
    rw [← map_pow] at h
    exact e.symm.injective (h.trans (map_one _).symm)
  have hw : HarrisLit.IsFieldAutPSL2 (y ^ 2) := by
    rw [isFieldAutPSL2_iff hodd e hY4]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply isFieldInvModel_of_involution hodd
    · apply orderOf_eq_prime
      · rw [← map_pow, ← pow_mul, show 2 * 2 = 4 from rfl, hy4, map_one]
      · intro h
        apply hy2
        exact (autEquiv e).injective (h.trans (map_one _).symm)
    · rw [map_pow, right_pow]
      exact hσ2
  obtain ⟨hLie, hidx, -, hfix⟩ := autPSL2FieldCentralizer S p f hp hp2 hfe h16 hL (y ^ 2) hw
  set C := MonoidHom.eqLocus (y ^ 2).toMonoidHom (MonoidHom.id S) with hC
  rw [commutator_eq_map_perfectResidual C hidx]
  refine ⟨?_, ?_, hfix⟩
  all_goals
    obtain ⟨-, -, -, -, F', _, _, hF', ⟨e'⟩⟩ := lieModel_psl2_data hLie
    have hF'4 : 4 ≤ Nat.card F' := by
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        have : p ≠ 2 := hp2
        omega
      rw [hF']
      calc 4 ≤ 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
        _ ≤ p ^ (f / 2) := Nat.pow_le_pow_right (by omega) (by omega)
    set eJ : ↥((perfectResidual ↥C).map C.subtype) ≃* PSL2 F' :=
      ((perfectResidual ↥C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans e'
    have hsimple : IsSimpleGroup (PSL2 F') :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF'4
    have hJsimple : IsSimpleGroup ↥((perfectResidual ↥C).map C.subtype) :=
      (MulEquiv.isSimpleGroup_congr eJ).mpr hsimple
  · exact hJsimple
  · have : Group.IsPerfect (PSL2 F') := psl2_isPerfect_of_card_gt_three F' (by omega)
    have hJperf : Group.IsPerfect ↥((perfectResidual ↥C).map C.subtype) :=
      Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom) eJ.symm.surjective
    have hnab : ∃ a b : ↥((perfectResidual ↥C).map C.subtype), a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨h⟩⟩
    exact CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup hnab) (by
        rw [CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnab,
          Subgroup.card_bot]
        exact odd_one)

end CFSG.ComponentClassification.AutL2Facts
