module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.LieType.Universal.SymplecticRoots
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem nonempty_centerQuotient_equiv_range {S G : Type*} [Group S] [Group G]
    (hS : IsQuasisimple S) (f : S →* G) (hne : f.range ≠ ⊥) :
    Nonempty (S ⧸ center S ≃* f.range ⧸ center f.range) := by
  have hker : f.ker ≤ center S := by
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hS
      (Subgroup.Normal.isSubnormal (MonoidHom.normal_ker f)) with h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
    · exact h
  exact LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hS f.rangeRestrict
    f.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)

theorem eq_commutator_of_isComponent {G : Type*} [Group G] (hq : IsQuasisimple (commutator G))
    {M : Subgroup G} (hM : IsComponent M) : M = commutator G := by
  have hsolv : Group.IsSolvable (G ⧸ commutator G) := by
    have : Group.IsSolvable (Abelianization G) := inferInstance
    exact this
  exact eq_of_isComponent_of_normal_quasisimple hq hsolv hM

theorem ne_bot_of_isQuasisimple {G : Type*} [Group G] {M : Subgroup G} (hM : IsQuasisimple M) :
    M ≠ ⊥ := by
  intro h
  have hnt := LocalCores.isQuasisimple_nontrivial hM
  rw [h] at hnt
  exact not_nontrivial_iff_subsingleton.mpr inferInstance hnt

theorem nonempty_centerQuotient_equiv_of_eq_map {G H S : Type*} [Group G] [Group H] [Group S]
    {M : Subgroup G} (e : G ≃* H) (hS : IsQuasisimple S) (f : S →* H)
    (hq : IsQuasisimple f.range) (hM : M = f.range.map e.symm.toMonoidHom) :
    Nonempty (M ⧸ center M ≃* S ⧸ center S) := by
  obtain ⟨eS⟩ := nonempty_centerQuotient_equiv_range hS f (ne_bot_of_isQuasisimple hq)
  let eM : M ≃* f.range := (MulEquiv.subgroupCongr hM).trans
    (f.range.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm
  exact ⟨(QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)).trans eS.symm⟩

theorem not_isComponent_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G]
    {M : Subgroup G} (hM : IsComponent M) : False := by
  have : Nontrivial M := LocalCores.isQuasisimple_nontrivial hM.1
  have : Group.IsPerfect M := hM.1.1
  have : Group.IsSolvable M := Group.isSolvable_of_isSolvable_injective M.subtype_injective
  exact Group.IsPerfect.not_isSolvable M inferInstance

theorem oddLieCentralQuotient_of_equiv_psl_two {M : Type} [Group M] {F : Type} [Field F]
    [Finite F] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hF : Nat.card F = p ^ e)
    (hF2 : Nat.card F ≠ 2) (hF3 : Nat.card F ≠ 3)
    (E : M ⧸ center M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    OddLieCentralQuotient p M := by
  have hadm : StatedLieAdmissible .PSL 2 p e :=
    ⟨hp, he, le_rfl, fun h => hF2 (hF.trans (Prod.mk.inj h).2),
      fun h => hF3 (hF.trans (Prod.mk.inj h).2)⟩
  exact ⟨.PSL, 2, e, hadm, LieType.CurtisTits.lieModel_of_mulEquiv E.symm
    (Or.inl ⟨by decide, ⟨hadm, F, inferInstance, inferInstance, hF,
      ⟨projectiveSpecialLinearGroupEquivStatedProj 2 F⟩⟩⟩)⟩

open LocalAnalysis.ComponentInitial CatalogueBOrthogonal in
theorem orthogonal_three_component_oddLieCentralQuotient {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 3)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_three_p_components_frontier
      hodd Q hQ hdim).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_three_derived hodd hK3 Q hQ hdim
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e'
    (CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2) (Or.inr hK3))
    (traceZeroOrthogonalAction.comp
      (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) K →* _))
    (traceZeroSpecialImage_quasisimple hK2 hK3) (hMeq.trans hcomm)
  exact oddLieCentralQuotient_of_equiv_psl_two hp he hK hK2 hK3 E

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFive in
theorem orthogonal_five_component_oddLieCentralQuotient {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 5)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  obtain ⟨-, -, e', -, -, hcomm, hq, -⟩ := orthogonal_five_derived hodd Q hQ hdim
  have hMeq := eq_commutator_of_isComponent hq hM
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' (symplecticKernel_quasisimple hodd)
    (selfAdjointSymplecticAction h2) (selfAdjointSymplecticImage_quasisimple hodd)
    (hMeq.trans hcomm)
  have hadm : StatedLieAdmissible .PSp 2 p e := by
    refine ⟨hp, he, le_rfl, fun h => ?_⟩
    have h1 : p ^ e = 2 := (Prod.mk.inj h).2
    rw [← hK] at h1
    exact absurd (h1 ▸ hodd) (by decide)
  let eSp := symplecticKernelEquivFin.trans (LieType.Universal.Symplectic.equivStatedSp 2 K)
  let eTot := E.trans (QuotientGroup.congr _ _ eSp (Subgroup.map_center_eq eSp))
  exact ⟨.PSp, 2, e, hadm, LieType.CurtisTits.lieModel_of_mulEquiv eTot.symm
    (Or.inl ⟨by decide,
      LieType.Universal.Symplectic.statedClassicalModel_center_quotient 2 K hadm hK⟩)⟩

theorem eq_or_eq_of_isComponent_le_sup {G : Type*} [Group G] [Finite G] {D L₁ L₂ : Subgroup G}
    (hD : D = L₁ ⊔ L₂) (hq₁ : IsQuasisimple L₁) (hq₂ : IsQuasisimple L₂)
    (hn₁ : (L₁.subgroupOf D).Normal) (hn₂ : (L₂.subgroupOf D).Normal) {M : Subgroup G}
    (hM : IsComponent M) (hMD : M ≤ D) : M = L₁ ∨ M = L₂ := by
  have hL₁D : L₁ ≤ D := hD ▸ le_sup_left
  have hL₂D : L₂ ≤ D := hD ▸ le_sup_right
  let eM := Subgroup.subgroupOfEquivOfLe hMD
  have hM' : IsComponent (M.subgroupOf D) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv eM.symm hM.1, hM.2.subgroupOf⟩
  obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := exists_mul_ne_of_isQuasisimple hM.1 (MulEquiv.refl M)
    exact ⟨x, x.2, y, y.2, fun h => hxy (Subtype.ext h)⟩
  have hin : ∀ {L : Subgroup G}, IsQuasisimple L → M ≤ L → M = L := by
    intro L hL hML
    rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hL
      (hM.2.subgroupOf (K := L)) with h | h
    · exact le_antisymm hML (Subgroup.subgroupOf_eq_top.mp h)
    · exfalso
      apply hab
      have hc := Subgroup.mem_center_iff.mp (h (show (⟨b, hML hb⟩ : L) ∈ M.subgroupOf L from hb))
        ⟨a, hML ha⟩
      exact congrArg Subtype.val hc
  have hcase : ∀ {L : Subgroup G}, IsQuasisimple L → L ≤ D → (L.subgroupOf D).Normal →
      M = L ∨ ∀ x ∈ M, ∀ y ∈ L, x * y = y * x := by
    intro L hL hLD hn
    rcases LocalCores.component_normal_subgroup hM' hn with h | h
    · left
      refine hin hL fun x hx => ?_
      exact h (show (⟨x, hMD hx⟩ : D) ∈ M.subgroupOf D from hx)
    · right
      intro x hx y hy
      have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
        (show (⟨x, hMD hx⟩ : D) ∈ M.subgroupOf D from hx)
      have h2 := Subgroup.mem_centralizer_iff.mp h1 ⟨y, hLD hy⟩
        (show (⟨y, hLD hy⟩ : D) ∈ L.subgroupOf D from hy)
      exact (congrArg Subtype.val h2).symm
  rcases hcase hq₁ hL₁D hn₁ with h | h₁
  · exact Or.inl h
  rcases hcase hq₂ hL₂D hn₂ with h | h₂
  · exact Or.inr h
  exfalso
  have hcent : D ≤ Subgroup.centralizer (M : Set G) := by
    rw [hD]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => h₁ x hx y hy
    · exact Subgroup.mem_centralizer_iff.mpr fun x hx => h₂ x hx y hy
  exact hab (Subgroup.mem_centralizer_iff.mp (hcent (hMD hb)) a ha)

open LocalAnalysis.ComponentInitial CatalogueBOrthogonalFourSplit in
theorem orthogonal_split_four_component_oddLieCentralQuotient {K W : Type} [Field K] [Finite K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (hK : Nat.card K = p ^ e) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (hdim : Module.finrank K W = 4)
    (hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0)
    {M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hodd) (by decide)
  by_cases hK3 : Nat.card K = 3
  · have := ((CatalogueBOrthogonalLowDimensionFrontiers.orthogonal_four_split_p_components_frontier
      hodd Q hQ hdim hS).2 hK3).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨-, e', -, -, hsup, hq₁, hq₂, hn₁, hn₂, -, hperf, -⟩ :=
    orthogonal_split_four_derived hK2 hK3 Q hQ hdim hS
  have hMD : M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    calc M = ⁅M, M⁆ := (Subgroup.isPerfect_iff.mp hM.1.1).symm
      _ ≤ commutator _ := Subgroup.commutator_mono le_top le_top
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  rcases eq_or_eq_of_isComponent_le_sup hsup hq₁ hq₂ hn₁ hn₂ hM hMD with h | h
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inl _ _)) (determinantLeftFactor_quasisimple hK2 hK3)
      h
    exact oddLieCentralQuotient_of_equiv_psl_two hp he hK hK2 hK3 E
  · obtain ⟨E⟩ := nonempty_centerQuotient_equiv_of_eq_map e' hSL
      ((specialRho (K := K)).comp (MonoidHom.inr _ _))
      (determinantRightFactor_quasisimple hK2 hK3) h
    exact oddLieCentralQuotient_of_equiv_psl_two hp he hK hK2 hK3 E

end CFSG.ComponentClassification.CatLeafProof
