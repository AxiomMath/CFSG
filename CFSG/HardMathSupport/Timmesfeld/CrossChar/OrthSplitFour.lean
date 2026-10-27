module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitFourClause

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

section General

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem card_orthSupportedFactor (hx : OddOrderIsometry Q p x)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) :
    Nat.card ↥(supportedFactor hx J) = Nat.card ↥J := by
  unfold supportedFactor
  rw [Subgroup.card_map_of_injective (supportedBlock Q x (X - 1)).subtype_injective,
    Subgroup.card_map_of_injective (fixedBlockEquiv hx).symm.injective]

theorem orthOthersSpace_X_sub_one_ne_bot (hx : OddOrderIsometry Q p x) (hx1 : x ≠ 1) :
    othersSpace x.toLinearMap (X - 1) ≠ ⊥ := by
  intro hbot
  have hc := hx.fixed_others.1
  rw [hbot] at hc
  have htop : fixedSpace x = ⊤ := codisjoint_bot.mp hc.codisjoint
  apply hx1
  ext v
  have hv : v ∈ fixedSpace x := by rw [htop]; trivial
  simpa using mem_fixedSpace.mp hv

theorem card_orthFixedFactorImage_eq_card (hx : OddOrderIsometry Q p x) (hx1 : x ≠ 1)
    (J : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)))
    (hΩ : supportedFactor hx J ≤ orthDerived Q) :
    Nat.card ↥(fixedFactorImage hx J) = Nat.card ↥J := by
  obtain ⟨r, hr, hr0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (orthOthersSpace_X_sub_one_ne_bot hx hx1)
  set ρ := QuotientGroup.mk'
    ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q)) with hρ
  have hinj : Function.Injective
      (ρ.domRestrict ((supportedFactor hx J).subgroupOf (orthDerived Q))) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : ρ (a : ↥(orthDerived Q)) = 1 := ha
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      CFSG.ClassicalGroups.Orthogonal.mem_scalars] at ha'
    obtain ⟨c, hc⟩ := ha'
    have hmem : ((a : ↥(orthDerived Q)) : V ≃ₗ[K] V) ∈ supportedFactor hx J :=
      Subgroup.mem_subgroupOf.mp a.2
    obtain ⟨b, -, hb⟩ := Subgroup.mem_map.mp hmem
    have hfix := ((mem_supportedBlock.mp b.2).2 r hr)
    have hbr : ((a : ↥(orthDerived Q)) : V ≃ₗ[K] V) r = r := by
      rw [← hb]; exact hfix
    rw [hc r] at hbr
    have hc1 : c = 1 := by
      by_contra hne
      have : (c - 1) • r = 0 := by rw [sub_smul, hbr, one_smul, sub_self]
      rcases smul_eq_zero.mp this with h | h
      · exact hne (sub_eq_zero.mp h)
      · exact hr0 h
    apply Subtype.ext
    apply Subtype.ext
    ext v
    simp [hc v, hc1]
  have hsub : Nat.card ↥((supportedFactor hx J).subgroupOf (orthDerived Q)) =
      Nat.card ↥(supportedFactor hx J) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩ).toEquiv
  unfold fixedFactorImage
  rw [← hρ, ← MonoidHom.domRestrict_range]
  rw [← card_orthSupportedFactor hx J, ← hsub]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end General

section Factors

variable {K : Type*} [Field K]

theorem card_determinantLeftFactor :
    Nat.card ↥(determinantLeftFactor K) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hinj : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inl _ _)) := by
    intro A A' h
    have h1 := congrArg (fun g : DeterminantIsometries K => g.val 1) h
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, specialRho_apply, inv_one,
      Matrix.SpecialLinearGroup.coe_one, mul_one] at h1
    exact Subtype.ext h1
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem card_determinantRightFactor :
    Nat.card ↥(determinantRightFactor K) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hinj : Function.Injective ((specialRho (K := K)).comp (MonoidHom.inr _ _)) := by
    intro B B' h
    have h1 := congrArg (fun g : DeterminantIsometries K => g.val 1) h
    simp only [MonoidHom.comp_apply, MonoidHom.inr_apply, specialRho_apply,
      Matrix.SpecialLinearGroup.coe_one, one_mul, mul_one] at h1
    have h2 : (B⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) = B'⁻¹ := Subtype.ext h1
    exact inv_injective h2
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Factors

section SplitFour

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem card_fixedFactorImage_splitFourFactors
    (hx : OddOrderIsometry Q p x) (hx1 : x ≠ 1)
    (e : ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype)) ≃*
      DeterminantIsometries K)
    (i : Fin 2) (hΩ : supportedFactor hx (splitFourFactors e i) ≤ orthDerived Q) :
    Nat.card ↥(fixedFactorImage hx (splitFourFactors e i)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [card_orthFixedFactorImage_eq_card hx hx1 _ hΩ]
  fin_cases i
  · change Nat.card ↥((determinantLeftFactor K).map e.symm.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective e.symm.injective, card_determinantLeftFactor]
  · change Nat.card ↥((determinantRightFactor K).map e.symm.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective e.symm.injective, card_determinantRightFactor]

end SplitFour

end CFSG.HardMathSupport.Timmesfeld.CrossChar
