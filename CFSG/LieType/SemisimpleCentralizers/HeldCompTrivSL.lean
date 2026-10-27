module

public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.Models.PGLSimple
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LieType.SemisimpleCentralizers.Held

open CFSG.Open CFSG.Open.StatedAPI Matrix
open scoped commutatorElement

theorem hct_nontrivial_of_isComponentOf_top {Γ : Type*} [Group Γ] {X : Subgroup Γ}
    (hX : IsComponentOf X ⊤) : Nontrivial X := by
  have hq : IsSimpleGroup (X ⧸ Subgroup.center X) := hX.2.2.2
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq
  exact (QuotientGroup.mk_surjective :
    Function.Surjective (QuotientGroup.mk : X → X ⧸ Subgroup.center X)).nontrivial

theorem hct_not_isQuasisimple_of_comm {Γ : Type*} [Group Γ] (h : ∀ a b : Γ, a * b = b * a) :
    ¬ CFSG.Open.IsQuasisimple Γ := by
  intro hq
  have hsimple : IsSimpleGroup (Γ ⧸ Subgroup.center Γ) := hq.2
  obtain ⟨q, hq1⟩ := exists_ne (1 : Γ ⧸ Subgroup.center Γ)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  apply hq1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  exact fun g => h g a

theorem hct_commutatorElement_mul_central_left {Γ : Type*} [Group Γ] {z : Γ}
    (hz : z ∈ Subgroup.center Γ) (a b : Γ) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have hzb : b * z = z * b := Subgroup.mem_center_iff.mp hz b
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem hct_commutatorElement_mul_central_right {Γ : Type*} [Group Γ] {w : Γ}
    (hw : w ∈ Subgroup.center Γ) (a b : Γ) : ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have hwa : a⁻¹ * w = w * a⁻¹ := Subgroup.mem_center_iff.mp hw a⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← hwa]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem hct_comp_eq_top_of_central_quotient {Γ : Type*} [Group Γ] (Z : Subgroup Γ) [Z.Normal]
    (hZ : Z ≤ Subgroup.center Γ) (hperf : Group.IsPerfect Γ) (hsimp : IsSimpleGroup (Γ ⧸ Z))
    {X : Subgroup Γ} (hX : IsComponentOf X ⊤) : X = ⊤ := by
  have hsub : IsSubnormal (X.map (QuotientGroup.mk' Z))
      ((⊤ : Subgroup Γ).map (QuotientGroup.mk' Z)) :=
    CFSG.Open.IsSubnormal.map (QuotientGroup.mk' Z) hX.2.1
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)] at hsub
  haveI := hsimp
  have hB : IsSimpleGroup (↥(⊤ : Subgroup (Γ ⧸ Z))) := Subgroup.topEquiv.isSimpleGroup
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub hB with hbot | htop
  ·
    exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : (a : Γ) ∈ Subgroup.center Γ := by
        have hmem : QuotientGroup.mk' Z (a : Γ) ∈ X.map (QuotientGroup.mk' Z) :=
          Subgroup.mem_map_of_mem _ a.2
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hZ ((QuotientGroup.eq_one_iff (a : Γ)).mp hmem)
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp ha (b : Γ)).symm
    exact hct_not_isQuasisimple_of_comm hcomm hX.2.2
  ·
    have hcov : ∀ g : Γ, ∃ x ∈ X, ∃ z ∈ Z, g = x * z := by
      intro g
      have hg : QuotientGroup.mk' Z g ∈ X.map (QuotientGroup.mk' Z) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
      have hxg' : (x : Γ ⧸ Z) = (g : Γ ⧸ Z) := hxg
      exact ⟨x, hx, x⁻¹ * g, QuotientGroup.eq.mp hxg', by group⟩
    have hle : commutator Γ ≤ X := by
      show ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ ≤ X
      refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
      obtain ⟨x, hx, z, hz, rfl⟩ := hcov g
      obtain ⟨y, hy, w, hw, rfl⟩ := hcov h
      rw [hct_commutatorElement_mul_central_left (hZ hz),
        hct_commutatorElement_mul_central_right (hZ hw), commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
    rw [Group.isPerfect_def.mp hperf] at hle
    exact eq_top_iff.mpr hle

theorem hct_comp_eq_top_of_isQuasisimple {Γ : Type*} [Group Γ] (hq : CFSG.Open.IsQuasisimple Γ)
    {X : Subgroup Γ} (hX : IsComponentOf X ⊤) : X = ⊤ :=
  hct_comp_eq_top_of_central_quotient (Subgroup.center Γ) le_rfl (Group.isPerfect_def.mpr hq.1)
    hq.2 hX

theorem hct_comp_eq_top_of_perfect_statedProj {n : ℕ} {K : Type} [Field K]
    (H : Subgroup (GL (Fin n) K)) (hperf : Group.IsPerfect H)
    (hsimp : IsSimpleGroup (StatedProj H)) {X : Subgroup H} (hX : IsComponentOf X ⊤) :
    X = ⊤ := by
  refine hct_comp_eq_top_of_central_quotient ((StatedScalars (Fin n) K).subgroupOf H) ?_ hperf
    hsimp hX
  intro x hx
  rw [Subgroup.mem_subgroupOf, statedScalars_eq_center, Subgroup.mem_center_iff] at hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (hx (g : GL (Fin n) K))

theorem hct_not_component_top_of_isSolvable {Γ : Type*} [Group Γ] (hs : Group.IsSolvable Γ)
    {X : Subgroup Γ} (hX : IsComponentOf X ⊤) : False := by
  haveI := hs
  haveI := hct_nontrivial_of_isComponentOf_top hX
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hX.2.2.1
  exact Group.IsPerfect.not_isSolvable (G := X) inferInstance

theorem hct_not_component_top_of_subsingleton {Γ : Type*} [Group Γ] [Subsingleton Γ]
    {X : Subgroup Γ} (hX : IsComponentOf X ⊤) : False := by
  haveI := hct_nontrivial_of_isComponentOf_top hX
  haveI : Subsingleton X := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact (not_subsingleton X) inferInstance

theorem hct_isSolvable_of_natCard_eq {Γ : Type*} [Group Γ] [Finite Γ] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card Γ = p ^ a * q ^ b) :
    Group.IsSolvable Γ := by
  letI := Fintype.ofFinite Γ
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, h])

theorem hct_subsingleton_statedSL_of_le_one {K : Type} [Field K] {d : ℕ} (hd : d ≤ 1) :
    Subsingleton ↥(StatedSL d K) := by
  have key : ∀ x : GL (Fin d) K, x ∈ StatedSL d K → x = 1 := by
    intro x hx
    rw [mem_statedSL_iff] at hx
    interval_cases d
    · exact Subsingleton.elim _ _
    · refine Units.ext (Matrix.ext fun a b => ?_)
      rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
      simpa [Matrix.det_fin_one, Matrix.one_apply] using hx
  exact ⟨fun x y => Subtype.ext ((key x x.2).trans (key y y.2).symm)⟩

theorem hct_isPerfect_statedSL {d : ℕ} (K : Type) [Field K] [Finite K] (hd : 2 ≤ d)
    (h22 : d ≠ 2 ∨ Nat.card K ≠ 2) (h23 : d ≠ 2 ∨ Nat.card K ≠ 3) :
    Group.IsPerfect (StatedSL d K) := by
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin d) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_perfect d K hd h22 h23
  exact Group.IsPerfect.ofSurjective
    (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d K).toMonoidHom)
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d K).surjective

theorem hct_isQuasisimple_statedSL {d : ℕ} (K : Type) [Field K] [Finite K] (hd : 2 ≤ d)
    (h22 : d ≠ 2 ∨ Nat.card K ≠ 2) (h23 : d ≠ 2 ∨ Nat.card K ≠ 3) :
    CFSG.Open.IsQuasisimple (StatedSL d K) := by
  refine ⟨Group.isPerfect_def.mp (hct_isPerfect_statedSL K hd h22 h23), ?_⟩
  haveI := isSimpleGroup_statedProj_statedSL K hd h22 h23
  exact (QuotientGroup.quotientMulEquivOfEq (center_statedSL_eq d)).isSimpleGroup

theorem SLComponentsTrivial_holds : SLComponentsTrivial := by
  unfold SLComponentsTrivial
  intro d K _ _ X hX
  by_cases hd : d ≤ 1
  · haveI := hct_subsingleton_statedSL_of_le_one (K := K) hd
    exact (hct_not_component_top_of_subsingleton hX).elim
  · have hd2 : 2 ≤ d := by omega
    by_cases hexc : d = 2 ∧ (Nat.card K = 2 ∨ Nat.card K = 3)
    ·
      obtain ⟨rfl, hK⟩ := hexc
      have hcard : Nat.card (StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
        card_statedSL_two K
      rcases hK with hK | hK
      · have hs : Group.IsSolvable (StatedSL 2 K) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two
            Nat.prime_three (by norm_num) (by rw [hcard, hK] <;> norm_num)
        exact (hct_not_component_top_of_isSolvable hs hX).elim
      · have hs : Group.IsSolvable (StatedSL 2 K) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two
            Nat.prime_three (by norm_num) (by rw [hcard, hK] <;> norm_num)
        exact (hct_not_component_top_of_isSolvable hs hX).elim
    · have h22 : d ≠ 2 ∨ Nat.card K ≠ 2 := by
        by_cases h : d = 2
        · exact Or.inr fun hK => hexc ⟨h, Or.inl hK⟩
        · exact Or.inl h
      have h23 : d ≠ 2 ∨ Nat.card K ≠ 3 := by
        by_cases h : d = 2
        · exact Or.inr fun hK => hexc ⟨h, Or.inr hK⟩
        · exact Or.inl h
      exact hct_comp_eq_top_of_perfect_statedProj (StatedSL d K)
        (hct_isPerfect_statedSL K hd2 h22 h23)
        (isSimpleGroup_statedProj_statedSL K hd2 h22 h23) hX

end CFSG.LieType.SemisimpleCentralizers.Held

end
