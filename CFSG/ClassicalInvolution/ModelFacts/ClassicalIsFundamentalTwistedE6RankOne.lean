module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Fixed
public import CFSG.LieType.AlgebraicGroups.RationalInnerInvolutionReduction

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

omit [IsAlgClosed k] in
theorem rootDiagUnit_inv_mul_pinnedX_mul {τ : Tag} (s : Fin τ.rank → kˣ) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (c : k) :
    (rootDiagUnit τ s)⁻¹ * pinnedX τ k γ c * rootDiagUnit τ s =
      pinnedX τ k γ ((rootChar s⁻¹ γ : k) * c) := by
  have h := rootDiagUnit_conj_pinnedX s⁻¹ hγ c
  rwa [← rootDiagUnit_inv s, inv_inv] at h

theorem eq_fixed_rootSubgroup_sup_of_conj (t : TwistTag) {e : ℕ} (he : 1 ≤ e)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) (hfix : permLattice t.perm β = β)
    (s : Fin t.tag.rank → kˣ) {J : Subgroup (ModGL t.tag k)}
    (hJF : ∀ y ∈ J, frobTwistGL t.tag k p e (diagramMap t k) y = y)
    {Fq : Subfield k} (hFq : Nat.card Fq = p ^ e)
    (hJ : ∀ y : ModGL t.tag k,
      y ∈ J.map (MulAut.conj (rootDiagUnit t.tag s)).toMonoidHom ↔
        ∃ A : SL(2, Fq), y = rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype A)) :
    J = fixedPointsIn (rootSubgroup t.tag k β) (frobTwistGL t.tag k p e (diagramMap t k)) ⊔
      fixedPointsIn (rootSubgroup t.tag k (-β)) (frobTwistGL t.tag k p e (diagramMap t k)) := by
  classical
  set u := rootDiagUnit t.tag s with hu
  set F := frobTwistGL t.tag k p e (diagramMap t k) with hF
  have hβ' : IsRoot t.tag (-β) := IsRoot.neg hβ
  have hfix' : permLattice t.perm (-β) = -β := by rw [permLattice_neg, hfix]
  have hRfin : Finite (fixedPointsIn (adjointGroup t.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p he (by cases t <;> decide)
      (units_map_entrywiseHom_diagramMap (t := t) (iterateFrobenius k p e))
      (diagramMap_pow_order t k)
  have hρJ : ∀ A : SL(2, Fq),
      u⁻¹ * rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype A) * u ∈ J := by
    intro A
    obtain ⟨y, hy, hyA⟩ := Subgroup.mem_map.1 ((hJ _).2 ⟨A, rfl⟩)
    have : y = u⁻¹ * rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype A) * u := by
      rw [← hyA]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rwa [← this]
  have hmapu : ∀ c : Fq, Matrix.SpecialLinearGroup.map Fq.subtype (uSL c) = uSL (c : k) := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_uSL]
  have hmapv : ∀ c : Fq, Matrix.SpecialLinearGroup.map Fq.subtype (vSL c) = vSL (c : k) := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_vSL]
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := k) hβ
  have hε0 : ε ≠ 0 := fun h => by simp [h] at hε
  have hsgn : ∀ c c' : k, (pinnedData t.tag β).2.2 • c = (pinnedData t.tag β).2.2 • c' → c = c' := by
    intro c c' h
    rcases pinnedSign_eq t.tag β with h1 | h1 <;> rw [h1] at h <;> simpa using h
  have hup : ∀ c : Fq,
      u⁻¹ * rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype (uSL c)) * u ∈
        fixedPointsIn (rootSubgroup t.tag k β) F := by
    intro c
    refine mem_fixedPointsIn.2 ⟨?_, hJF _ (hρJ _)⟩
    rw [hmapu, rootSL2_uSL_eq, hu, rootDiagUnit_inv_mul_pinnedX_mul s hβ]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  have hvp : ∀ c : Fq,
      u⁻¹ * rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype (vSL c)) * u ∈
        fixedPointsIn (rootSubgroup t.tag k (-β)) F := by
    intro c
    refine mem_fixedPointsIn.2 ⟨?_, hJF _ (hρJ _)⟩
    rw [hmapv, hv, hu, rootDiagUnit_inv_mul_pinnedX_mul s hβ']
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  apply le_antisymm
  ·
    intro y hy
    obtain ⟨A, hA⟩ := (hJ (u * y * u⁻¹)).1 (Subgroup.mem_map.2 ⟨y, hy, rfl⟩)
    have hy' : y = u⁻¹ * rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype A) * u := by
      rw [← hA]
      group
    rw [hy']
    set S := fixedPointsIn (rootSubgroup t.tag k β) F ⊔
      fixedPointsIn (rootSubgroup t.tag k (-β)) F with hS
    let φ : SL(2, Fq) →* ModGL t.tag k :=
      (MulAut.conj u⁻¹).toMonoidHom.comp ((rootSL2 t.tag k β).comp
        (Matrix.SpecialLinearGroup.map Fq.subtype))
    have hφ : ∀ A, φ A = u⁻¹ * rootSL2 t.tag k β (Matrix.SpecialLinearGroup.map Fq.subtype A) * u :=
      fun A => by
        simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have htop : S.comap φ = ⊤ := by
      rw [eq_top_iff, ← sl2_closure_upper_lower (K := Fq), Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
        exact Subgroup.mem_sup_left (hup c)
      · rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
        exact Subgroup.mem_sup_right (hvp c)
    have hA' : A ∈ S.comap φ := by rw [htop]; exact Subgroup.mem_top A
    rw [Subgroup.mem_comap, hφ] at hA'
    exact hA'
  ·
    refine sup_le ?_ ?_
    · have hfin : Finite (fixedPointsIn (rootSubgroup t.tag k β) F) :=
        Finite.of_injective _ (Subgroup.inclusion_injective
          (inf_le_inf_right _ (rootSubgroup_le_adjointGroup β) :
            fixedPointsIn (rootSubgroup t.tag k β) F ≤ fixedPointsIn (adjointGroup t.tag k) F))
      let f : Fq → fixedPointsIn (rootSubgroup t.tag k β) F := fun c =>
        ⟨_, hup c⟩
      have hfi : Function.Injective f := by
        intro c c' h
        have h1 := congrArg Subtype.val h
        simp only [f] at h1
        have h2 := mul_left_cancel (mul_right_cancel h1)
        rw [hmapu, hmapu, rootSL2_uSL_eq, rootSL2_uSL_eq] at h2
        have h3 := pinnedX_injective t.tag k β h2
        exact Subtype.ext (hsgn _ _ h3)
      have hbij : Function.Bijective f := hfi.bijective_of_nat_card_le
        ((card_fixedPointsIn_rootSubgroup_le p t he hβ hfix).trans hFq.symm.le)
      intro g hg
      obtain ⟨c, hc⟩ := hbij.2 ⟨g, hg⟩
      have := congrArg Subtype.val hc
      simp only [f] at this
      rw [← this]
      exact hρJ _
    · have hfin : Finite (fixedPointsIn (rootSubgroup t.tag k (-β)) F) :=
        Finite.of_injective _ (Subgroup.inclusion_injective
          (inf_le_inf_right _ (rootSubgroup_le_adjointGroup (-β)) :
            fixedPointsIn (rootSubgroup t.tag k (-β)) F ≤
              fixedPointsIn (adjointGroup t.tag k) F))
      let f : Fq → fixedPointsIn (rootSubgroup t.tag k (-β)) F := fun c =>
        ⟨_, hvp c⟩
      have hfi : Function.Injective f := by
        intro c c' h
        have h1 := congrArg Subtype.val h
        simp only [f] at h1
        have h2 := mul_left_cancel (mul_right_cancel h1)
        rw [hmapv, hmapv, hv, hv] at h2
        have h3 := pinnedX_injective t.tag k (-β) h2
        exact Subtype.ext (mul_left_cancel₀ hε0 h3)
      have hbij : Function.Bijective f := hfi.bijective_of_nat_card_le
        ((card_fixedPointsIn_rootSubgroup_le p t he hβ' hfix').trans hFq.symm.le)
      intro g hg
      obtain ⟨c, hc⟩ := hbij.2 ⟨g, hg⟩
      have := congrArg Subtype.val hc
      simp only [f] at this
      rw [← this]
      exact hρJ _

end CFSG.ClassicalInvolution.ModelFacts
