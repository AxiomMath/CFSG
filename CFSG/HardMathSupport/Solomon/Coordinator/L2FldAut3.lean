module

public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3Alg
public import CFSG.HardMathSupport.Solomon.Coordinator.L2FldDefs
public import CFSG.Quasithin.Background.F918Z4bAut
public import CFSG.RankThree.PartTwo.KFacts.AutPSL2OrderThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (StatedProj StatedSL)
open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

theorem l2Aut3Classification_holds : L2Aut3Classification := by
  intro F _ _ β hβ3
  by_cases hβ1 : β = 1
  · exact Or.inl hβ1
  right
  let e₀ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* StatedProj (StatedSL 2 F) :=
    CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F
  let β' : MulAut (PSL2 F) := MulAut.congr e₀.symm β
  have hβ'3 : β' ^ 3 = 1 := by
    change MulAut.congr e₀.symm β ^ 3 = 1
    rw [← map_pow, hβ3, map_one]
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβ1
    apply (MulAut.congr e₀.symm).injective
    rw [map_one]; exact h
  have hback : MulAut.congr e₀ β' = β := by
    change MulAut.congr e₀ (MulAut.congr e₀.symm β) = β
    ext y
    simp [MulAut.congr_apply]
  by_cases hD : β' ∈ (pglAction F).range
  · left
    obtain ⟨g, hg⟩ := hD
    obtain ⟨G, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    have hg3 : (Matrix.ProjGenLinGroup.mk G) ^ 3 = 1 := by
      apply CFSG.Quasithin.pglAction_injective_of_finite F
      rw [map_pow, hg, hβ'3, map_one]
    have hGn : ∀ d : Fˣ, G ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) d := by
      intro d hd
      apply hβ'1
      rw [← hg]
      have : Matrix.ProjGenLinGroup.mk G = 1 := by
        rw [hd]; exact Matrix.ProjGenLinGroup.mk_scalar d
      rw [this, map_one]
    obtain ⟨c, hc⟩ : ∃ c : Fˣ, G ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      have h1 : Matrix.ProjGenLinGroup.mk (G ^ 3) = 1 := by rw [map_pow]; exact hg3
      rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, hc.symm⟩
    refine Group.isSolvable_of_comm ?_
    have hfix : ∀ x : ↥(fixSub β),
        pglAction F (Matrix.ProjGenLinGroup.mk G) (e₀.symm (x : StatedProj (StatedSL 2 F))) =
          e₀.symm (x : StatedProj (StatedSL 2 F)) := by
      intro x
      rw [hg]
      have := mem_fixSub.1 x.2
      show e₀.symm (β (e₀ (e₀.symm (x : StatedProj (StatedSL 2 F))))) =
        e₀.symm (x : StatedProj (StatedSL 2 F))
      rw [MulEquiv.apply_symm_apply, this]
    intro x y
    apply Subtype.ext
    apply e₀.symm.injective
    change e₀.symm ((x : StatedProj (StatedSL 2 F)) * (y : StatedProj (StatedSL 2 F))) =
      e₀.symm ((y : StatedProj (StatedSL 2 F)) * (x : StatedProj (StatedSL 2 F)))
    rw [map_mul, map_mul]
    exact l2fld_fixed_comm G c hc hGn _ _ (hfix x) (hfix y)
  · right
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf β' = 3 := orderOf_eq_prime hβ'3 hβ'1
    obtain ⟨σ, -, g, hgσ⟩ := linear_two_prime_order_field_descent Nat.prime_three β' hord hD
    refine ⟨σ, MulAut.congr e₀ (psl2FieldAut F σ), MulAut.congr e₀ (pglAction F g), ?_, ?_⟩
    · intro A A' hA
      obtain ⟨B, rfl⟩ := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).surjective A
      have h1 : e₀ (psl2QuotientMap F B) = QuotientGroup.mk
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F B) := rfl
      have h2 : e₀.symm (QuotientGroup.mk
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F B)) =
            psl2QuotientMap F B := by
        rw [MulEquiv.symm_apply_eq]; exact h1.symm
      change e₀ (psl2FieldAut F σ (e₀.symm _)) = _
      rw [h2, CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2.psl2FieldAut_mk]
      have h3 : e₀ (psl2QuotientMap F (Matrix.SpecialLinearGroup.map σ.toRingHom B)) =
          QuotientGroup.mk (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F
            (Matrix.SpecialLinearGroup.map σ.toRingHom B)) := rfl
      rw [h3]
      congr 1
      apply Subtype.ext
      apply Units.ext
      rw [CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe] at hA ⊢
      rw [hA]
      ext i j
      rfl
    · rw [← hback, hgσ]
      simp only [map_mul, map_inv]

end CFSG.HardMathSupport.Solomon.Coordinator
