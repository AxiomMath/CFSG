module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneHeightRigidity
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def e6HeightEightRoot : Fin Tag.E6.rank → ℤ :=
  (![1, 1, 1, 2, 2, 1] : Fin 6 → ℤ)

theorem e6HeightEightRoot_facts :
    IsRoot Tag.E6 e6HeightEightRoot ∧
      IsRoot Tag.E6 (permLattice TwistTag.E6.perm e6HeightEightRoot) ∧
      height e6HeightEightRoot = 8 ∧
      height (permLattice TwistTag.E6.perm e6HeightEightRoot) = height e6HeightEightRoot ∧
      permLattice TwistTag.E6.perm e6HeightEightRoot ≠ e6HeightEightRoot :=
  ⟨isRoot_of_listedRootCheck (by decide +kernel), isRoot_of_listedRootCheck (by decide +kernel),
    by decide, by decide, fun he => absurd (congrFun he ⟨2, by decide⟩) (by decide)⟩


theorem eq_of_conj_pinnedX_eq_pinnedX_of_height_eq {τ : Tag} {u : ModGL τ K}
    (hu : u ∈ posUnipotent τ K) {γ γ' : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγp : 0 < height γ)
    (hγ' : IsRoot τ γ') (hht : height γ' = height γ) {c d : K} (hd : d ≠ 0)
    (h : u * pinnedX τ K γ' c * u⁻¹ = pinnedX τ K γ d) : γ' = γ := by
  by_contra hne
  have hu1 : u ∈ heightSeries τ K 1 := by
    rw [heightSeries_one]
    exact hu
  have hx : pinnedX τ K γ' c ∈ heightSeries τ K (height γ) :=
    pinnedX_mem_rootSpan (show γ' ∈ {β | IsRoot τ β ∧ 0 < height β ∧ height γ ≤ height β} from
      ⟨hγ', by omega, hht.ge⟩) c
  have h3 := commutator_heightSeries_le K 1 (height γ)
    (Subgroup.commutator_mem_commutator hu1 hx)
  have h2 : pinnedX τ K γ d = ⁅u, pinnedX τ K γ' c⁆ * pinnedX τ K γ' c := by
    rw [commutatorElement_def, h]
    group
  set T : Set (Fin τ.rank → ℤ) :=
    {β | IsRoot τ β ∧ 0 < height β ∧ height γ ≤ height β ∧ β ≠ γ} with hT
  have hle : heightSeries τ K (1 + height γ) ≤ rootSpan τ K T :=
    iSup₂_le fun β hβ => le_iSup₂_of_le β ⟨hβ.1, hβ.2.1, by have := hβ.2.2; omega, by
      rintro rfl
      have := hβ.2.2
      omega⟩ le_rfl
  have hγ'T : pinnedX τ K γ' c ∈ rootSpan τ K T :=
    pinnedX_mem_rootSpan (show γ' ∈ T from ⟨hγ', by omega, hht.ge, hne⟩) c
  have hmem : pinnedX τ K γ d ∈ rootSpan τ K T := by
    rw [h2]
    exact mul_mem (hle h3) hγ'T
  have hTc : ∀ β ∈ T, ∀ ε ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • β + b • ε) →
      a • β + b • ε ∈ T := by
    intro β hβ ε hε a b ha hb hr
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have hht' : height (a • β + b • ε) = a * height β + b * height ε :=
      height_nsmul_add_nsmul a b β ε
    have hge : 2 * height γ ≤ height (a • β + b • ε) := by
      rw [hht']
      nlinarith [hβ.2.1, hβ.2.2.1, hε.2.1, hε.2.2.1]
    refine ⟨hr, by omega, by omega, ?_⟩
    rintro he
    rw [he] at hge
    omega
  have hγT := mem_of_pinnedX_mem_rootSpan (T := T) (fun β hβ => ⟨hβ.1, hβ.2.1⟩) hTc
    ⟨hγ, hγp⟩ hd hmem
  exact hγT.2.2.2 rfl

theorem mem_diagonalFieldActors_E7_E8 [Finite K] {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    (β : MulAut (adjointGroup τ K)) : β ∈ diagonalFieldActors τ K := by
  obtain ⟨g, a, σ, ε, hβ⟩ :=
    (ordinary_E_exact_automorphism_normal_form τ (Or.inr hτ) K).2.2 β
  have hQ : exactQ τ K ε = 1 := by
    rcases hτ with rfl | rfl <;> rfl
  obtain ⟨φ, hφ, hφx⟩ := (Chevalley_diagonal_field_actor_data.1 τ K).2.1 g g.2 a σ
  have e : β = φ := MulEquiv.ext fun x => Subtype.ext (by
    rw [hβ, hφx, hQ, inv_one, mul_one, mul_one])
  exact e ▸ hφ

theorem mem_diagonalFieldActors_of_fix_heightSeries_E6 [Finite K] {h : ℤ} (h1 : 1 ≤ h)
    (h7 : h ≤ 7) {β : MulAut (adjointGroup .E6 K)}
    (hfix : ∀ x : adjointGroup .E6 K, (x : ModGL .E6 K) ∈ heightSeries .E6 K h → β x = x) :
    β ∈ diagonalFieldActors .E6 K := by
  obtain ⟨g, a, σ, ⟨e, he⟩, hβ⟩ :=
    (ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K).2.2 β
  have he2 : e < 2 := he
  obtain ⟨φ, hφ, hφx⟩ := (Chevalley_diagonal_field_actor_data.1 .E6 K).2.1 g g.2 a σ
  interval_cases e
  ·
    have hQ : exactQ .E6 K 0 = 1 := pow_zero _
    have e : β = φ := MulEquiv.ext fun x => Subtype.ext (by
      rw [hβ, hφx]
      simp only [hQ, inv_one, mul_one])
    exact e ▸ hφ
  ·
    exfalso
    set P : ModGL Tag.E6 K := diagramMap TwistTag.E6 K with hPdef
    have hQ : exactQ .E6 K 1 = P := pow_one _
    set F : ModGL Tag.E6 K →* ModGL Tag.E6 K := twistHom TwistTag.E6 K σ.toRingHom with hF
    have hFx : ∀ x : ModGL Tag.E6 K, F x = P * Units.map (entrywiseHom σ.toRingHom) x * P⁻¹ :=
      fun x => rfl
    have hβF : ∀ x : adjointGroup .E6 K,
        (β x : ModGL .E6 K) = g * diagFieldAut .E6 a 1 (F x) * (g : ModGL .E6 K)⁻¹ := by
      intro x
      rw [hβ, hFx, diagFieldAut_apply, units_map_entrywiseHom_one_ringEquiv]
      simp only [hQ]
      group
    have hQC : ∀ h' : ℤ, heightSeries .E6 K h' ≤ adjointGroup .E6 K := fun h' =>
      (heightSeries_le_posUnipotent h').trans posUnipotent_le_adjointGroup
    have hN : ∀ h' : ℤ, h ≤ h' → ∀ y ∈ heightSeries .E6 K h',
        (g : ModGL .E6 K) * y * (g : ModGL .E6 K)⁻¹ ∈ heightSeries .E6 K h' := by
      intro h' hh y hy
      have hS : ∀ α ∈ {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α ∧ 0 < height α ∧
          h' ≤ height α}, IsRoot Tag.E6 α := fun α hα => hα.1
      have hD := map_diagFieldAut_rootSpan (K := K) a 1 hS
      have hFS : (heightSeries .E6 K h').map F = heightSeries .E6 K h' :=
        map_twistHom_rootSpan_of_stable (t := TwistTag.E6) σ.surjective hS
          (fun α hα => ⟨hα.1.permLattice TwistTag.E6.cartan_perm,
            hα.2.1.trans_eq (height_permLattice _ _).symm,
            hα.2.2.trans_eq (height_permLattice _ _).symm⟩)
          (fun α hα => ⟨hα.1.permLattice (cartan_perm_symm TwistTag.E6.cartan_perm),
            hα.2.1.trans_eq (height_permLattice _ _).symm,
            hα.2.2.trans_eq (height_permLattice _ _).symm⟩)
      have hy' : y ∈ (heightSeries .E6 K h').map (diagFieldAut .E6 a 1).toMonoidHom := by
        rw [heightSeries, hD]
        exact hy
      obtain ⟨y', hy'S, rfl⟩ := hy'
      rw [← hFS] at hy'S
      obtain ⟨x, hxS, rfl⟩ := hy'S
      have hle : heightSeries .E6 K h' ≤ heightSeries .E6 K h :=
        iSup₂_le fun α hα => le_iSup₂_of_le α ⟨hα.1, hα.2.1, hh.trans hα.2.2⟩ le_rfl
      have hxh : x ∈ heightSeries .E6 K h := hle hxS
      have h1 := congrArg Subtype.val (hfix ⟨x, hQC h hxh⟩ hxh)
      rw [hβF] at h1
      change (g : ModGL .E6 K) * diagFieldAut .E6 a 1 (F x) * (g : ModGL .E6 K)⁻¹ ∈ _
      rw [h1]
      exact hxS
    have hgB : (g : ModGL .E6 K) ∈ (borelGroup .E6 K : Set (ModGL .E6 K)) :=
      mem_borelGroup_of_normalizes_heightSeries h1 (simpleDiffTail_of_le (τ := .E6) h7) g.2 hN
    rw [(triangular_borel_structure.{0, 0} .E6 K).2.2.2.2.2.1] at hgB
    obtain ⟨u, hu, t, ht, hut⟩ := hgB
    beta_reduce at hut
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨hγ, hργ, hγ8, hht, hne⟩ := e6HeightEightRoot_facts
    set γ := e6HeightEightRoot with hγdef
    obtain ⟨ε, -, hP⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.E6 hγ
    have hγh : h ≤ height γ := by omega
    have hfixγ := congrArg Subtype.val (hfix ⟨pinnedX .E6 K γ 1, pinnedX_mem_adjointGroup _ _⟩
      (pinnedX_mem_rootSpan (S := {α | IsRoot Tag.E6 α ∧ 0 < height α ∧ h ≤ height α})
        ⟨hγ, by omega, hγh⟩ 1))
    rw [hβF] at hfixγ
    have hFγ : F (pinnedX .E6 K γ 1) =
        pinnedX .E6 K (permLattice TwistTag.E6.perm γ) (ε * 1) := by
      rw [hFx, show Units.map (entrywiseHom σ.toRingHom) (pinnedX .E6 K γ 1) =
        pinnedX .E6 K γ (σ.toRingHom 1) from Units.ext (entrywise_pinnedX _ γ 1), map_one]
      exact hP 1
    change (g : ModGL .E6 K) * diagFieldAut .E6 a 1 (F (pinnedX .E6 K γ 1)) *
      (g : ModGL .E6 K)⁻¹ = pinnedX .E6 K γ 1 at hfixγ
    rw [hFγ, diagFieldAut_pinnedX a 1 hργ, ← hut] at hfixγ
    have hconj : u * pinnedX .E6 K (permLattice TwistTag.E6.perm γ)
        ((rootChar b (permLattice TwistTag.E6.perm γ) : K) *
          ((rootChar a (permLattice TwistTag.E6.perm γ) : K) * (1 : K ≃+* K) (ε * 1))) * u⁻¹ =
        pinnedX .E6 K γ 1 := by
      rw [← rootDiagUnit_conj_pinnedX b hργ, ← hfixγ]
      group
    exact hne (eq_of_conj_pinnedX_eq_pinnedX_of_height_eq hu hγ (by omega) hργ hht
      one_ne_zero hconj)

theorem mem_diagonalFieldActors_of_fix_heightSeries_E [Finite K] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {h : ℤ} (h1 : 1 ≤ h) (hh : h ≤ simpleDiffTailMax τ)
    {β : MulAut (adjointGroup τ K)}
    (hfix : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x) :
    β ∈ diagonalFieldActors τ K := by
  rcases hτ with rfl | hτ
  · exact mem_diagonalFieldActors_of_fix_heightSeries_E6 h1 hh hfix
  · exact mem_diagonalFieldActors_E7_E8 hτ β

theorem exists_eq_conj_of_fix_heightSeries_E [Finite K] {τ : Tag}
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {h : ℤ} (h1 : 1 ≤ h) (hh : h ≤ simpleDiffTailMax τ)
    {β : MulAut (adjointGroup τ K)}
    (hfix : ∀ x : adjointGroup τ K, (x : ModGL τ K) ∈ heightSeries τ K h → β x = x) :
    ∃ u ∈ posUnipotent τ K, ∃ hu : u ∈ adjointGroup τ K, β = MulAut.conj ⟨u, hu⟩ ∧
      ∀ x ∈ heightSeries τ K h, u * x = x * u :=
  exists_eq_conj_commute_of_mem_actors_of_fix_heightSeries h1 (simpleDiffTail_of_le hh)
    (mem_diagonalFieldActors_of_fix_heightSeries_E hτ h1 hh hfix) hfix

end CFSG.SeitzReduction
