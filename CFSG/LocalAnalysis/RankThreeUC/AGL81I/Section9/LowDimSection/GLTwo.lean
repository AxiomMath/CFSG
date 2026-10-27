module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Inputs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix MatrixGroups Subgroup

variable {P : (S : Type) → [Group S] → Prop}

private theorem bijective_of_isSimpleGroup {A S : Type*} [Group A] [Group S] [IsSimpleGroup A]
    [Nontrivial S] (ψ : A →* S) (hψ : Function.Surjective ψ) : Function.Bijective ψ := by
  refine ⟨?_, hψ⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff ψ).1 h
  · exfalso
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨a, rfl⟩ := hψ s
    exact hs (MonoidHom.mem_ker.1 (h ▸ mem_top a))

theorem SimpleSectionsIn.specialLinearGroup_of_projective {n F : Type*} [Fintype n]
    [DecidableEq n] [Field F]
    (h : SimpleSectionsIn P (ProjectiveSpecialLinearGroup n F)) :
    SimpleSectionsIn P (SpecialLinearGroup n F) :=
  SimpleSectionsIn.of_isSolvable_ker (QuotientGroup.mk' (center (SpecialLinearGroup n F)))
    (by rw [QuotientGroup.ker_mk']; infer_instance) h

private theorem det_ker_map_ne_bot {n F : Type*} [Fintype n] [DecidableEq n] [Field F]
    {Y : Subgroup (GL n F)} {S : Type} [Group S] (hS : ¬ IsMulCommutative S) {ψ : ↥Y →* S}
    (hψ : Function.Surjective ψ) :
    ((GeneralLinearGroup.det.comp Y.subtype).ker).map ψ ≠ ⊥ := by
  intro hbot
  refine hS ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, rfl⟩ := hψ a
  obtain ⟨y, rfl⟩ := hψ b
  have hmem : x * y * (y * x)⁻¹ ∈ (GeneralLinearGroup.det.comp Y.subtype).ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv]
    exact mul_inv_eq_one.mpr (mul_comm _ _)
  have h1 : ψ (x * y * (y * x)⁻¹) = 1 := by
    have := mem_map_of_mem ψ hmem
    rwa [hbot, mem_bot] at this
  rw [map_mul, map_inv, map_mul, map_mul] at h1
  exact mul_inv_eq_one.mp h1

theorem SimpleSectionsIn.generalLinearGroup_of_special {n F : Type*} [Fintype n]
    [DecidableEq n] [Field F] (h : SimpleSectionsIn P (SpecialLinearGroup n F)) :
    SimpleSectionsIn P (GL n F) := by
  intro Y S _ _ hS ψ hψ
  set N : Subgroup ↥Y := (GeneralLinearGroup.det.comp Y.subtype).ker
  have htop : N.map ψ = ⊤ :=
    (map_eq_bot_or_eq_top_of_normal hψ (MonoidHom.normal_ker _)).resolve_left
      (det_ker_map_ne_bot hS hψ)
  let ι : ↥N →* SpecialLinearGroup n F :=
    (SpecialLinearGroup.toGLKerEquiv (n := n) (R := F)).symm.toMonoidHom.comp
      ((Y.subtype.comp N.subtype).codRestrict _ fun x => x.2)
  have hι : Function.Injective ι := by
    intro x y hxy
    have h' := congrArg (fun z => ((z : GeneralLinearGroup.det.ker) : GL n F))
      ((SpecialLinearGroup.toGLKerEquiv (n := n) (R := F)).symm.injective hxy)
    exact Subtype.ext (Subtype.ext h')
  refine h.of_injective ι hι ⊤ S hS (ψ.comp (N.subtype.comp (topEquiv).toMonoidHom)) ?_
  intro s
  obtain ⟨x, hx, rfl⟩ := mem_map.1 (htop ▸ mem_top s : s ∈ N.map ψ)
  exact ⟨⟨⟨x, hx⟩, mem_top _⟩, rfl⟩

private theorem card_psl_two_three_lt : Nat.card PSL(2, ZMod 3) < 60 := by
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [card_GL_field, ZMod.card]
    decide
  have h1 : Nat.card PSL(2, ZMod 3) ≤ Nat.card SL(2, ZMod 3) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card SL(2, ZMod 3) ≤ Nat.card (GL (Fin 2) (ZMod 3)) :=
    Nat.card_le_card_of_injective _ SpecialLinearGroup.toGL_injective
  omega

private theorem isLowDimSimpleSection_of_top (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) {S : Type}
    [Group S] [IsSimpleGroup S] (hS : ¬ IsMulCommutative S)
    (ψ : ↥(⊤ : Subgroup PSL(2, ZMod q)) →* S) (hψ : Function.Surjective ψ) :
    IsLowDimSimpleSection q S := by
  have hq3 : 3 ≤ q := (Fact.out : q.Prime).two_le.lt_of_ne' hq
  rcases hq3.eq_or_lt with h3 | h5
  · subst h3
    have : Finite S := Finite.of_surjective ψ hψ
    have hna : ∃ x y : S, x * y ≠ y * x := by
      by_contra hc
      push Not at hc
      exact hS ⟨⟨hc⟩⟩
    have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty inferInstance hna
    have hle : Nat.card S ≤ Nat.card ↥(⊤ : Subgroup PSL(2, ZMod 3)) :=
      Nat.card_le_card_of_surjective ψ hψ
    rw [Subgroup.card_top] at hle
    exact absurd card_psl_two_three_lt (by omega)
  · have : IsSimpleGroup PSL(2, ZMod q) :=
      ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
    let ψ' : PSL(2, ZMod q) →* S := ψ.comp (topEquiv).symm.toMonoidHom
    have hψ' : Function.Surjective ψ' := hψ.comp (topEquiv).symm.surjective
    exact Or.inl ⟨(MulEquiv.ofBijective ψ' (bijective_of_isSimpleGroup ψ' hψ')).symm⟩

theorem pslTwoLowDimSections_of (hD : DicksonPSLTwo) (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    SimpleSectionsIn (IsLowDimSimpleSection q) PSL(2, ZMod q) := by
  intro L S _ _ hS ψ hψ
  rcases hD q hq L with hsol | rfl | he
  · have : Group.IsSolvable S := solvable_of_surjective hψ
    exact (hS ⟨⟨IsSimpleGroup.comm_iff_isSolvable.2 inferInstance⟩⟩).elim
  · exact isLowDimSimpleSection_of_top q hq hS ψ hψ
  · obtain ⟨e⟩ := he
    let ψ' : alternatingGroup (Fin 5) →* S := ψ.comp e.symm.toMonoidHom
    have hψ' : Function.Surjective ψ' := hψ.comp e.symm.surjective
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(MulEquiv.ofBijective ψ' (bijective_of_isSimpleGroup ψ' hψ')).symm⟩))))

theorem gLTwoLowDimSections_of (hD : DicksonPSLTwo) : GLTwoLowDimSections := fun q _ hq =>
  ((pslTwoLowDimSections_of hD q hq).specialLinearGroup_of_projective).generalLinearGroup_of_special

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
