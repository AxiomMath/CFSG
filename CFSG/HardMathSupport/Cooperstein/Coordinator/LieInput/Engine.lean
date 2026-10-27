module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Quotient
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Overgroups

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding CFSG.LieType.BorelTits CFSG.Quasithin.SmithC27
  CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank

theorem center_sl2_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by
      have : r ^ 2 = 1 := by simpa using hr2
      calc (r - 1) ^ 2 = r ^ 2 + 1 - 2 * r := by ring
        _ = 0 := by rw [this]; linear_combination (1 - r) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h
    exact sub_eq_zero.mp this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hr, hr1]
  simp

theorem center_eq_bot_of_quasisimple_simple {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hq : CFSG.IsQuasisimple Y) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have ha' : a' ∈ Subgroup.center Y := by rw [h1]; trivial
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp ha' b']

theorem chev_of_sl2_image {K Y F : Type} [Group K] [Group Y]
    [Field F] [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) (π : K →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center K) (C : Subgroup K)
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥C) :
    CFSG.IsQuasisimple ↥(C.map π) ∧
      IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π)) := by
  have hinj : Function.Injective (π.comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : π (x : K) = 1 := hx
    have hxz := Subgroup.mem_center_iff.mp (hker _ hx1)
    have : e.symm x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul]
      exact hxz (e g)
    rw [center_sl2_eq_bot, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    have := congrArg e this
    simpa using this
  have hrange : (π.comp C.subtype).range = C.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eA : ↥C ≃* ↥(C.map π) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  obtain ⟨h1, h2⟩ := isChevComponent_sl (F := F) (k := 2) (Or.inr ⟨rfl, hF4⟩)
  have eB : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(C.map π) := e.trans eA
  exact ⟨isQuasisimple_of_mulEquiv eB h1, isClassicalTwoOrG2_of_mulEquiv (quotCenterCongr eB) h2⟩

open CFSG.LieType.Universal CFSG.AGLEmbeddingD2.ParabLevi in
theorem simpleStmt_of_borelQuotient {K Y : Type} [Group K] [Group Y] [Finite K] [Finite Y]
    {D : CFSG.LieType.Universal.UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}
    (hq : CFSG.IsQuasisimple Y) (hZ : Subgroup.center Y = ⊥) (hcl : IsClassicalTwoOrG2 Y)
    (hrad : IsRadicalParabolic (⊤ : Subgroup Y)) (hb : BorelQuotient D n H π M)
    (hOb : ∀ π' : K →* Y, BorelQuotient D n H π' M → ∀ I : Set (Fin D.rank),
      I ≠ Set.univ → LeviOb D H π' I)
    (hCent : ∀ I : Set (Fin D.rank), I ≠ Set.univ → CentOb D I) : SimpleStmt Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro R hR
  by_cases hne : (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) = ⊤
  · exact ⟨leviStructure_improper hq hZ hcl hR hne, fun h' => absurd hne h'⟩
  have hR2 : IsPGroup 2 R := by rw [hR]; exact pCoreOf_isPGroup 2 _
  have hRbot : R ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [eq_top_iff]
    intro x _
    exact ⟨trivial, Subgroup.mem_normalizer_iff.mpr fun y => by simp⟩
  obtain ⟨-, S, hS, hSN⟩ := hrad R le_top hRbot hR2 hR.symm
  obtain ⟨T, hT⟩ := exists_sylow_of_isSylowTwoOf'' hS
  have hpar : ∃ T : Sylow 2 Y, Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤
      (⊤ : Subgroup Y) ⊓ Subgroup.normalizer (R : Set Y) :=
    ⟨T, by rw [hT]; simpa using hSN⟩
  exact ⟨leviStructure_of_borelQuotient hb hR hne hpar hOb,
    fun _ => centralizer_of_borelQuotient hb hR hne hpar hZ hCent⟩

section LeviM

open CFSG.AGLEmbeddingD2.ParabLevi CFSG.LieType.CurtisTits

variable {K : Type} [Group K] (D : CFSG.LieType.Universal.UniversalRootDatum K)

theorem leviM_empty : leviM D ∅ = ⊥ := by simp [leviM]

theorem leviM_singleton (i : Fin D.rank) : leviM D {i} = rankOne D.rootGroup i := by
  simp [leviM]

theorem torus_le_normalizer_rankOne {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (i : Fin D.rank) :
    (⨆ k, H k) ≤ Subgroup.normalizer (rankOne D.rootGroup i : Set K) := by
  have := torus_le_normalizer_leviM (I := {i}) hct
  rwa [leviM_singleton] at this

end LeviM

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
