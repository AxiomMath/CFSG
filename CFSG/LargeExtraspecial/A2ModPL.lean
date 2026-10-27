module

public import CFSG.LargeExtraspecial.A2ModLinesAbel
public import CFSG.LargeExtraspecial.A2ModSLc
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.OrthoF2Fixed
public import CFSG.LargeExtraspecial.OrthoF2SpRadical
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.Timmesfeld.Outcome

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.A2Mod

open Module Matrix CFSG.RankThree.OrthogonalInvolutions

theorem apply_mem_commSpace_conj {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {X : Type*} [Group X] (ρ : X →* (V ≃ₗ[K] V)) (g : X) {a : X} {x : V}
    (hx : x ∈ commSpace (ρ a)) : ρ g x ∈ commSpace (ρ (g * a * g⁻¹)) := by
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hx
  refine mem_commSpace.mpr ⟨ρ g y, ?_⟩
  have h1 : ρ g⁻¹ (ρ g y) = y := by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one, id]
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, map_sub]

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsPointCentre (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V))
    (v : Fin n → ZMod 2) (p : V) : Prop :=
  p ≠ 0 ∧ ∀ φ : Fin n → ZMod 2, φ ≠ 0 → φ ⬝ᵥ v = 0 → p ∈ commSpace (ρ (tv v φ))

@[expose] def IsHyperplaneCentre (ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V))
    (φ : Fin n → ZMod 2) (p : V) : Prop :=
  p ≠ 0 ∧ ∀ v : Fin n → ZMod 2, v ≠ 0 → φ ⬝ᵥ v = 0 → p ∈ commSpace (ρ (tv v φ))

variable {ρ : SpecialLinearGroup (Fin n) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}

theorem isPointCentre_iff {v : Fin n → ZMod 2} (hv : v ≠ 0) {p : V} :
    IsPointCentre ρ v p ↔ p ≠ 0 ∧ ∀ a ∈ pointGroup v, a ≠ 1 → p ∈ commSpace (ρ a) := by
  refine and_congr_right fun _ => ⟨fun h a ha ha1 => ?_, fun h φ hφ hφv => ?_⟩
  · obtain ⟨φ, hφv, rfl⟩ := mem_pointGroup.mp ha
    have hφ : φ ≠ 0 := by
      rintro rfl
      exact ha1 (tv_zero_right v)
    exact h φ hφ hφv
  · exact h _ (tv_mem_pointGroup v φ) (tv_ne_one hv hφ hφv)

theorem isHyperplaneCentre_iff {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) {p : V} :
    IsHyperplaneCentre ρ φ p ↔ p ≠ 0 ∧ ∀ a ∈ hyperplaneGroup φ, a ≠ 1 → p ∈ commSpace (ρ a) := by
  refine and_congr_right fun _ => ⟨fun h a ha ha1 => ?_, fun h v hv hφv => ?_⟩
  · obtain ⟨v, hφv, rfl⟩ := mem_hyperplaneGroup.mp ha
    have hv : v ≠ 0 := by
      rintro rfl
      exact ha1 (tv_zero_left φ)
    exact h v hv hφv
  · exact h _ (tv_mem_hyperplaneGroup v φ) (tv_ne_one hv hφ hφv)

theorem IsPointCentre.apply {v : Fin n → ZMod 2} {p : V} (hp : IsPointCentre ρ v p)
    (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    IsPointCentre ρ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v) (ρ g p) := by
  refine ⟨fun h => hp.1 ((LinearEquiv.map_eq_zero_iff (ρ g)).mp h), fun φ hφ hφv => ?_⟩
  have hφ' : contra g⁻¹ φ ≠ 0 := fun h => hφ ((contra_eq_zero_iff g⁻¹).mp h)
  have hφ'v : contra g⁻¹ φ ⬝ᵥ v = 0 := by
    have h := contra_dotProduct_mulVec g⁻¹ φ ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v)
    rw [sl_inv_mulVec_mulVec] at h
    rw [h, hφv]
  have h := apply_mem_commSpace_conj ρ g (hp.2 _ hφ' hφ'v)
  rwa [conj_tv, contra_contra_inv] at h

theorem IsHyperplaneCentre.apply {φ : Fin n → ZMod 2} {p : V} (hp : IsHyperplaneCentre ρ φ p)
    (g : SpecialLinearGroup (Fin n) (ZMod 2)) : IsHyperplaneCentre ρ (contra g φ) (ρ g p) := by
  refine ⟨fun h => hp.1 ((LinearEquiv.map_eq_zero_iff (ρ g)).mp h), fun v hv hφv => ?_⟩
  set w := ((g⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v
    with hw
  have hv' : w ≠ 0 := fun h => hv ((sl_mulVec_eq_zero_iff g⁻¹).mp h)
  have hφv' : φ ⬝ᵥ w = 0 := by
    have h := contra_dotProduct_mulVec g φ w
    rw [hw, sl_mulVec_inv_mulVec] at h
    rw [← h, hφv]
  have h := apply_mem_commSpace_conj ρ g (hp.2 _ hv' hφv')
  rwa [conj_tv, sl_mulVec_inv_mulVec] at h

theorem exists_isPointCentre_of_isPointCentre {v₀ : Fin n → ZMod 2} (hv₀ : v₀ ≠ 0) {p : V}
    (hp : IsPointCentre ρ v₀ p) {v : Fin n → ZMod 2} (hv : v ≠ 0) : ∃ p', IsPointCentre ρ v p' := by
  obtain ⟨g, hg⟩ := exists_mulVec_eq hv₀ hv
  exact ⟨ρ g p, hg ▸ hp.apply g⟩

theorem exists_isHyperplaneCentre_of_isHyperplaneCentre {φ₀ : Fin n → ZMod 2} (hφ₀ : φ₀ ≠ 0)
    {p : V} (hp : IsHyperplaneCentre ρ φ₀ p) {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) :
    ∃ p', IsHyperplaneCentre ρ φ p' := by
  obtain ⟨g, hg⟩ := exists_contra_eq hφ₀ hφ
  exact ⟨ρ g p, hg ▸ hp.apply g⟩

variable [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem forall_mem_pointGroup_mem_transvectionSet {v : Fin n → ZMod 2} :
    ∀ a ∈ pointGroup v, a ≠ 1 → a ∈ transvectionSet n (ZMod 2) :=
  fun _ ha ha1 => mem_transvectionSet_of_mem_pointGroup ha ha1

theorem forall_mem_hyperplaneGroup_mem_transvectionSet {φ : Fin n → ZMod 2} :
    ∀ a ∈ hyperplaneGroup φ, a ≠ 1 → a ∈ transvectionSet n (ZMod 2) :=
  fun _ ha ha1 => mem_transvectionSet_of_mem_hyperplaneGroup ha ha1

theorem exists_isPointCentre (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 5 ≤ n)
    {v : Fin n → ZMod 2} (hv : v ≠ 0) : ∃ p, IsPointCentre ρ v p := by
  have h8 : 8 < Nat.card (pointGroup v) := by
    rw [card_pointGroup hv]
    calc 8 < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨p, hp, hpA⟩ := hA.exists_common_point forall_mem_pointGroup_mem_transvectionSet h8
  exact ⟨p, (isPointCentre_iff hv).mpr ⟨hp, hpA⟩⟩

theorem exists_isHyperplaneCentre (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 5 ≤ n)
    {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) : ∃ p, IsHyperplaneCentre ρ φ p := by
  have h8 : 8 < Nat.card (hyperplaneGroup φ) := by
    rw [card_hyperplaneGroup hφ]
    calc 8 < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨p, hp, hpA⟩ := hA.exists_common_point forall_mem_hyperplaneGroup_mem_transvectionSet h8
  exact ⟨p, (isHyperplaneCentre_iff hφ).mpr ⟨hp, hpA⟩⟩

theorem IsPointCentre.unique (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    {v : Fin n → ZMod 2} (hv : v ≠ 0) {p p' : V} (hp : IsPointCentre ρ v p)
    (hp' : IsPointCentre ρ v p') : p = p' := by
  have h2 : 2 < Nat.card (pointGroup v) := by
    rw [card_pointGroup hv]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hp0, hpA⟩ := (isPointCentre_iff hv).mp hp
  obtain ⟨hp'0, hp'A⟩ := (isPointCentre_iff hv).mp hp'
  exact hA.common_point_unique forall_mem_pointGroup_mem_transvectionSet h2 hp0 hp'0 hpA hp'A

theorem IsHyperplaneCentre.unique (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (hn : 3 ≤ n)
    {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) {p p' : V} (hp : IsHyperplaneCentre ρ φ p)
    (hp' : IsHyperplaneCentre ρ φ p') : p = p' := by
  have h2 : 2 < Nat.card (hyperplaneGroup φ) := by
    rw [card_hyperplaneGroup hφ]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hp0, hpA⟩ := (isHyperplaneCentre_iff hφ).mp hp
  obtain ⟨hp'0, hp'A⟩ := (isHyperplaneCentre_iff hφ).mp hp'
  exact hA.common_point_unique forall_mem_hyperplaneGroup_mem_transvectionSet h2 hp0 hp'0 hpA hp'A

theorem finrank_commSpaceOf_top_le_add (i : Fin n) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤
      finrank (ZMod 2) (commSpaceOf ρ (pointGroup (Pi.single i 1))) +
        finrank (ZMod 2) (commSpaceOf ρ (hyperplaneGroup (Pi.single i 1))) := by
  rw [← pointGroup_sup_hyperplaneGroup (F := ZMod 2) i, commSpaceOf_sup]
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

theorem finrank_commSpaceOf_pointGroup_le (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    {v : Fin n → ZMod 2} (hv : v ≠ 0) :
    finrank (ZMod 2) (commSpaceOf ρ (pointGroup v)) ≤ max n 3 := by
  have h := hA.finrank_commSpaceOf_le_max forall_mem_pointGroup_mem_transvectionSet
    (card_pointGroup hv)
  have hn : n ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at h

theorem finrank_commSpaceOf_hyperplaneGroup_le (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ)
    {φ : Fin n → ZMod 2} (hφ : φ ≠ 0) :
    finrank (ZMod 2) (commSpaceOf ρ (hyperplaneGroup φ)) ≤ max n 3 := by
  have h := hA.finrank_commSpaceOf_le_max forall_mem_hyperplaneGroup_mem_transvectionSet
    (card_hyperplaneGroup hφ)
  have hn : n ≠ 0 := by
    rintro rfl
    exact hφ (Subsingleton.elim _ _)
  rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] at h

theorem finrank_commSpaceOf_top_le (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 2 * max n 3 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : (⊤ : Subgroup (SpecialLinearGroup (Fin 0) (ZMod 2))) = ⊥ := Subsingleton.elim _ _
    rw [h, commSpaceOf_bot, finrank_bot]
    exact Nat.zero_le _
  have hei : (Pi.single (⟨0, hn⟩ : Fin n) 1 : Fin n → ZMod 2) ≠ 0 :=
    Pi.single_ne_zero_iff.mpr one_ne_zero
  have h1 := finrank_commSpaceOf_pointGroup_le hA hei
  have h2 := finrank_commSpaceOf_hyperplaneGroup_le hA hei
  have h3 := finrank_commSpaceOf_top_le_add (ρ := ρ) (⟨0, hn⟩ : Fin n)
  omega

theorem finrank_commSpaceOf_top_le_of_not_concurrent
    (hA : A2Action (transvectionSet n (ZMod 2)) Q ρ) (i : Fin n)
    (h : ¬ ((∃ p : V, p ≠ 0 ∧ ∀ a ∈ pointGroup (Pi.single i 1), a ≠ 1 → p ∈ commSpace (ρ a)) ∧
      ∃ p : V, p ≠ 0 ∧ ∀ a ∈ hyperplaneGroup (Pi.single i 1), a ≠ 1 → p ∈ commSpace (ρ a))) :
    finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ max n 3 + 3 := by
  have hei : (Pi.single i 1 : Fin n → ZMod 2) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have h1 := finrank_commSpaceOf_pointGroup_le hA hei
  have h2 := finrank_commSpaceOf_hyperplaneGroup_le hA hei
  have h3 := finrank_commSpaceOf_top_le_add (ρ := ρ) i
  rcases hA.common_point_or_finrank_le_three (A := pointGroup (Pi.single i 1))
      forall_mem_pointGroup_mem_transvectionSet with hcA | hA3
  · rcases hA.common_point_or_finrank_le_three (A := hyperplaneGroup (Pi.single i 1))
      forall_mem_hyperplaneGroup_mem_transvectionSet with hcB | hB3
    · exact absurd ⟨hcA, hcB⟩ h
    · omega
  · omega

end CFSG.LargeExtraspecial.A2Mod
