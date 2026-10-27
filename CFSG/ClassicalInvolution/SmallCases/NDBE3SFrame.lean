module

public import CFSG.ClassicalInvolution.SmallCases.NDBE3SCore

public section

namespace CFSG.ClassicalInvolution.NDB.ExoticModel

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.LieType.Universal
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem rankOne_oddDatum {K : Type} [Field K] {n : ℕ} {k j : Fin n} (hk : k.val + 1 < n)
    (hj : j.val = k.val + 1) (hkj : k ≠ j) :
    rankOne (oddDatum n K).rootGroup k = ((oddFrame n K).longSL2 hkj true false).range := by
  have h1 : rankOne (oddRootGroup n K) k = (rankOneB K k).range :=
    le_antisymm (OddCT.rankOne_le_range k) (by
      rintro _ ⟨M, rfl⟩
      exact OddCT.rankOneB_mem_rankOne k M)
  show rankOne (oddRootGroup n K) k = _
  rw [h1, rankOneB_of_lt K hk hj hkj]

@[expose] def StdPair {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
    {m : ℕ} (F₀ : HypFrame Q m) {i₀ i₁ i₂ : Fin m} (h01 : i₀ ≠ i₁) (h12 : i₁ ≠ i₂)
    (θ : SL(3, F) →* spinGroup Q) (c : SL(3, F)) : Prop :=
  (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h01 true false).range ∧
      ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range) ∨
    (((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h12 true false).range ∧
      ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ = (F₀.longSL2 h01 true false).range)

theorem std_odd {e : ℕ} (hadm : StatedLieAdmissible .POmegaOdd 3 p e) :
    ∃ (θ : SL(3, GaloisField p e) →* spinGroup (quadOdd 3 (GaloisField p e)))
      (c : SL(3, GaloisField p e)), θ.ker ≤ Subgroup.center SL(3, GaloisField p e) ∧
      ((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈
        fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 p e Fact.out).D ∧
      StdPair (oddFrame 3 (GaloisField p e)).toHypFrame (i₀ := 0) (i₁ := 1) (i₂ := 2)
        (by decide) (by decide) θ c := by
  obtain ⟨-, W, θ, c, -, hker, hUV⟩ :=
    ModelFacts.standardPair_oddDatum (F := GaloisField p e) (n := 3) le_rfl
  have hU : ((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈
      fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd 3 p e Fact.out).D := by
    rcases hUV with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact ⟨1, _, Or.inl (ModelFacts.isLongestRoot_single .POmegaOdd 3 p e Fact.out trivial hadm
        ⟨0, by show 0 < 3; omega⟩ (by show 0 + 1 < 3; omega)), by rw [conjSub_one]; rfl⟩
    · exact ⟨1, _, Or.inl (ModelFacts.isLongestRoot_single .POmegaOdd 3 p e Fact.out trivial hadm
        ⟨1, by show 1 < 3; omega⟩ (by show 1 + 1 < 3; omega)), by rw [conjSub_one]; rfl⟩
  have h0 : rankOne (oddDatum 3 (GaloisField p e)).rootGroup
      (⟨0, by show 0 < 3; omega⟩ : Fin (oddDatum 3 (GaloisField p e)).rank) =
      ((oddFrame 3 (GaloisField p e)).longSL2 (i := 0) (j := 1) (by decide) true false).range :=
    rankOne_oddDatum (by show 0 + 1 < 3; omega) rfl (Fin.ne_of_val_ne (by norm_num))
  have h1 : rankOne (oddDatum 3 (GaloisField p e)).rootGroup
      (⟨1, by show 1 < 3; omega⟩ : Fin (oddDatum 3 (GaloisField p e)).rank) =
      ((oddFrame 3 (GaloisField p e)).longSL2 (i := 1) (j := 2) (by decide) true false).range :=
    rankOne_oddDatum (by show 1 + 1 < 3; omega) rfl (Fin.ne_of_val_ne (by norm_num))
  rw [h0, h1] at hUV
  exact ⟨θ, c, hker, hU, hUV⟩

theorem std_minus (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .POmegaMinus 4 p e) :
    ∃ (θ : SL(3, GaloisField p e) →* spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
        (minusCoeffs p e).2)) (c : SL(3, GaloisField p e)),
      θ.ker ≤ Subgroup.center SL(3, GaloisField p e) ∧
      ((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈
        fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p e Fact.out).D ∧
      StdPair (Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).toHypFrame
        (i₀ := 0) (i₁ := 1) (i₂ := 2) (by decide) (by decide) θ c := by
  obtain ⟨-, W, θ, c, -, hker, hUV⟩ := ModelFacts.standardPair_minusDatum
    (F := GaloisField p e) (n := 4) le_rfl (ModelFacts.two_ne_zero_galoisField e hp2)
    (minusCoeffs_irr p e)
  have hU : ((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ ∈
      fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 4 p e Fact.out).D := by
    rcases hUV with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact ⟨1, _, Or.inl (ModelFacts.isLongestRoot_single .POmegaMinus 4 p e Fact.out trivial
        hadm ⟨0, by show 0 < 4 - 1; omega⟩ (by show 0 + 2 < 4; omega)), by rw [conjSub_one]; rfl⟩
    · exact ⟨1, _, Or.inl (ModelFacts.isLongestRoot_single .POmegaMinus 4 p e Fact.out trivial
        hadm ⟨1, by show 1 < 4 - 1; omega⟩ (by show 1 + 2 < 4; omega)), by rw [conjSub_one]; rfl⟩
  have h0 : rankOne (Twisted.minusDatum 4 (minusCoeffs_irr p e)).rootGroup
      (⟨0, by show 0 < 4 - 1; omega⟩ : Fin (Twisted.minusDatum 4 (minusCoeffs_irr p e)).rank) =
      ((Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).longSL2 (i := 0) (j := 1)
        (Fin.ne_of_val_ne (by norm_num)) true false).range :=
    Twisted.rankOne_minusRootGroup_of_lt 4 (minusCoeffs_irr p e) (k := ⟨0, by omega⟩)
      (by show 0 + 1 < 4 - 1; omega)
  have h1 : rankOne (Twisted.minusDatum 4 (minusCoeffs_irr p e)).rootGroup
      (⟨1, by show 1 < 4 - 1; omega⟩ : Fin (Twisted.minusDatum 4 (minusCoeffs_irr p e)).rank) =
      ((Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).longSL2 (i := 1) (j := 2)
        (Fin.ne_of_val_ne (by norm_num)) true false).range :=
    Twisted.rankOne_minusRootGroup_of_lt 4 (minusCoeffs_irr p e) (k := ⟨1, by omega⟩)
      (by show 1 + 1 < 4 - 1; omega)
  rw [h0, h1] at hUV
  exact ⟨θ, c, hker, hU, hUV⟩

theorem exists_frame_spin_full (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e) {t : StatedLieTag} {n : ℕ}
    (ht : SpinTag t n) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {x₀ : (modelUniv t n p e Fact.out).K} (hx₀ : IsUniqueInvolution R₀ x₀) :
    ∃ k : (modelUniv t n p e Fact.out).K, FrameRel x₀ k ∧
      (∃ r ∈ conjSub k R₀, x₀ * r ≠ r * x₀) ∧
      (∃ r ∈ R₀, k * x₀ * k⁻¹ * r ≠ r * (k * x₀ * k⁻¹)) ∧
      (∃ r ∈ R₀, x₀ * (k * x₀ * k⁻¹) * r ≠ r * (x₀ * (k * x₀ * k⁻¹))) ∧
      (∀ (H : Type) [Group H] [Finite H] (ψ : (modelUniv t n p e Fact.out).K →* H),
        ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K →
        alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x₀, mem_normalizer_range ψ x₀⟩,
          toInducedAutOn ψ.range ⟨ψ (k * x₀ * k⁻¹), mem_normalizer_range ψ _⟩} :
            Set ↥(inducedAutOn ψ.range))) = ⊥) ∧
      Subgroup.centralizer ({x₀} : Set (modelUniv t n p e Fact.out).K) ⊔
        Subgroup.centralizer ({k * x₀ * k⁻¹} : Set (modelUniv t n p e Fact.out).K) ⊔
          Subgroup.centralizer ({x₀ * (k * x₀ * k⁻¹)} : Set (modelUniv t n p e Fact.out).K) =
            ⊤ := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have h5 : 5 ≤ Nat.card (GaloisField p e) := by rw [GaloisField.card p e he]; exact hq
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  have hfund : IsFundTag t := by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> trivial
  have hsc := ModelFacts.fundamentalSingleClass t n p e Fact.out hfund hadm
    (by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
    (by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨θ, c, hker, hU, hpair⟩ := std_odd (p := p) hadm
    obtain ⟨g, hg⟩ : ∃ g : (modelUniv .POmegaOdd 3 p e Fact.out).K,
        R₀ = conjSub g (((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ) :=
      hsc _ hU R₀ hR₀
    obtain ⟨hgv, hk₂, hrel, h₁, h₂, h₃⟩ :=
      frame_of_sl3 (X := (modelUniv .POmegaOdd 3 p e Fact.out).K) h2 θ hker c hx₀ g hg
    have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField p e))) :=
      isPerfect_spinGroup_quadOdd h2 le_rfl
    obtain ⟨hα, hgen⟩ := NDB.SpinStd.core hodd h5 (nondegenerate_polarBilin_quadOdd 3 _ h2)
      (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_unit])
      (range_spinAction_quadOdd h2 le_rfl) (oddFrame 3 (GaloisField p e)).toHypFrame
      (i₀ := 0) (i₁ := 1) (i₂ := 2) (by decide) (by decide) (by decide) hker hpair g
    refine ⟨_, hrel, h₁, ?_, ?_, ?_, ?_⟩
    · rw [hk₂]
      exact h₂
    · rw [hk₂]
      exact h₃
    · intro H _ _ ψ hψ
      subst hgv
      rw [hk₂]
      exact hα H ψ hψ
    · subst hgv
      rw [hk₂]
      exact hgen
  · obtain ⟨θ, c, hker, hU, hpair⟩ := std_minus hp2 hadm
    obtain ⟨g, hg⟩ : ∃ g : (modelUniv .POmegaMinus 4 p e Fact.out).K,
        R₀ = conjSub g (((B12 (GaloisField p e)).map (MulAut.conj c⁻¹).toMonoidHom).map θ) :=
      hsc _ hU R₀ hR₀
    obtain ⟨hgv, hk₂, hrel, h₁, h₂, h₃⟩ :=
      frame_of_sl3 (X := (modelUniv .POmegaMinus 4 p e Fact.out).K) h2 θ hker c hx₀ g hg
    have : Group.IsPerfect (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1
        (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus le_rfl (minusCoeffs_irr p e)
    obtain ⟨hα, hgen⟩ := NDB.SpinStd.core hodd h5
      (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e))
      (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]
        omega)
      (range_spinAction_quadMinus le_rfl (minusCoeffs_irr p e))
      (Twisted.minusFrame 4 (minusCoeffs p e).1 (minusCoeffs p e).2).toHypFrame
      (i₀ := 0) (i₁ := 1) (i₂ := 2) (Fin.ne_of_val_ne (by norm_num))
      (Fin.ne_of_val_ne (by norm_num)) (Fin.ne_of_val_ne (by norm_num)) hker hpair g
    refine ⟨_, hrel, h₁, ?_, ?_, ?_, ?_⟩
    · rw [hk₂]
      exact h₂
    · rw [hk₂]
      exact h₃
    · intro H _ _ ψ hψ
      subst hgv
      rw [hk₂]
      exact hα H ψ hψ
    · subst hgv
      rw [hk₂]
      exact hgen

end CFSG.ClassicalInvolution.NDB.ExoticModel
