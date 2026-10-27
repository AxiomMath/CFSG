module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Char3Good (C : Type) [Group C] : Prop :=
  (∃ (M : Subgroup C) (_ : M.Normal), IsSimpleGroup ↥M ∧ (∃ a b : ↥M, a * b ≠ b * a) ∧
      CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 3 ↥M ∧
      IsEmpty (↥M ≃* alternatingGroup (Fin 6)) ∧ Group.IsSolvable (C ⧸ M)) ∨
    ∀ J : Subgroup C, ¬ GLAPComponent 3 (⊤ : Subgroup C) J

section Transfer

variable {S : Type} [Group S]

theorem coprime_three_card_inf_ker_subtype (H : Subgroup S) (A : Subgroup ↥H) :
    Nat.Coprime 3 (Nat.card ↥(A ⊓ H.subtype.ker)) := by
  rw [(MonoidHom.ker_eq_bot_iff _).2 H.subtype_injective, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

private theorem map_subtype_top_eq (H : Subgroup S) : (⊤ : Subgroup ↥H).map H.subtype = H := by
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_glaPComponent_top_of_subgroup [Finite S] {H J : Subgroup S}
    (hJ : GLAPComponent 3 H J) : ∃ K : Subgroup ↥H, GLAPComponent 3 (⊤ : Subgroup ↥H) K := by
  haveI : Finite ↥H := Subtype.finite
  have hJ' : GLAPComponent 3 ((⊤ : Subgroup ↥H).map H.subtype) J := by
    rwa [map_subtype_top_eq]
  obtain ⟨K, hK, -⟩ := exists_glaPComponent_map_eq Nat.prime_three H.subtype
    (coprime_three_card_inf_ker_subtype H ⊤) hJ'
  exact ⟨K, hK⟩

theorem glaPComponent_map_subtype_of_top [Finite S] {H : Subgroup S} {K : Subgroup ↥H}
    (hK : GLAPComponent 3 (⊤ : Subgroup ↥H) K) : GLAPComponent 3 H (K.map H.subtype) := by
  haveI : Finite ↥H := Subtype.finite
  have h := glaPComponent_map Nat.prime_three H.subtype (coprime_three_card_inf_ker_subtype H ⊤) hK
  rwa [map_subtype_top_eq] at h

end Transfer

section Constructors

variable {C C' : Type} [Group C] [Group C']

theorem Char3Good.of_simple [IsSimpleGroup C] (hnc : ∃ a b : C, a * b ≠ b * a)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 3 C)
    (hA6 : IsEmpty (C ≃* alternatingGroup (Fin 6))) : Char3Good C := by
  left
  let e : ↥(⊤ : Subgroup C) ≃* C := Subgroup.topEquiv
  refine ⟨⊤, inferInstance, e.isSimpleGroup_congr.2 inferInstance, ?_,
    isChevSimple_congr e.symm hchev, ⟨fun f => hA6.false (e.symm.trans f)⟩, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  · haveI : Subsingleton (C ⧸ (⊤ : Subgroup C)) := QuotientGroup.subsingleton_quotient_top
    exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _

theorem Char3Good.of_noComponent {S : Type} [Group S] [Finite S] {β : MulAut S}
    (h : ∀ I : Subgroup S, ¬ GLAPComponent 3 (fixSubgroup β) I) :
    Char3Good ↥(fixSubgroup β) :=
  Or.inr fun _ hK => h _ (glaPComponent_map_subtype_of_top hK)

theorem Char3Good.of_mulEquiv [Finite C] (e : C ≃* C') (h : Char3Good C') : Char3Good C := by
  rcases h with ⟨M, hMn, hMs, hMnc, hMchev, hMA6, hsol⟩ | hno
  · left
    let N : Subgroup C := M.comap (e : C →* C')
    have hNM : N.map (e : C →* C') = M := Subgroup.map_comap_eq_self_of_surjective e.surjective M
    haveI : N.Normal := hMn.comap _
    let eN : ↥N ≃* ↥M :=
      (N.equivMapOfInjective (e : C →* C') e.injective).trans (MulEquiv.subgroupCongr hNM)
    let eQ : C ⧸ N ≃* C' ⧸ M := QuotientGroup.congr N M e hNM
    refine ⟨N, inferInstance, eN.isSimpleGroup_congr.2 hMs, ?_, isChevSimple_congr eN.symm hMchev,
      ⟨fun f => hMA6.false (eN.symm.trans f)⟩,
      Group.isSolvable_of_isSolvable_injective (f := eQ.toMonoidHom) eQ.injective⟩
    obtain ⟨a, b, hab⟩ := hMnc
    exact ⟨eN.symm a, eN.symm b, fun h => hab (by simpa using congrArg eN h)⟩
  · right
    intro J hJ
    have h1 := glaPComponent_map Nat.prime_three (e : C →* C') (A := ⊤)
      (by
        rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, inf_bot_eq, Subgroup.card_bot]
        exact Nat.coprime_one_right 3) hJ
    rw [Subgroup.map_top_of_surjective _ e.surjective] at h1
    exact hno _ h1

end Constructors

section Fixed

variable {S : Type} [Group S] [Finite S]

theorem Char3Good.of_conj_aut (ε β : MulAut S) (h : Char3Good ↥(fixSubgroup (ε * β * ε⁻¹))) :
    Char3Good ↥(fixSubgroup β) := by
  have hc : MulAut.congr (ε : S ≃* S) β = ε * β * ε⁻¹ := by
    ext x
    rfl
  rw [← hc] at h
  exact Char3Good.of_mulEquiv (fixSubgroupCongrEquiv (ε : S ≃* S) β) h

theorem Char3Good.of_inv (β : MulAut S) (h : Char3Good ↥(fixSubgroup β⁻¹)) :
    Char3Good ↥(fixSubgroup β) := by
  have hfix : fixSubgroup β⁻¹ = fixSubgroup β := by
    ext x
    rw [mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · intro hx
      calc β x = β (β⁻¹ x) := by rw [hx]
        _ = x := MulAut.apply_inv_self _ β x
    · intro hx
      calc β⁻¹ x = β⁻¹ (β x) := by rw [hx]
        _ = x := MulAut.inv_apply_self _ β x
  rwa [hfix] at h

end Fixed

theorem lieCompExport_or_noThreeComponents_of_char3Good {S : Type} [Group S] [Finite S]
    (β : MulAut S) (h : Char3Good ↥(fixSubgroup β)) :
    LieCompExport 3 β ∨ NoThreeComponents β := by
  rcases h with ⟨M, hMn, hMs, hMnc, hMchev, hMA6, hsol⟩ | hno
  · left
    let J : Subgroup S := M.map (fixSubgroup β).subtype
    have hJC : J ≤ fixSubgroup β := Subgroup.map_subtype_le M
    have hJM : J.subgroupOf (fixSubgroup β) = M :=
      Subgroup.comap_map_eq_self_of_injective (fixSubgroup β).subtype_injective M
    let eJ : ↥M ≃* ↥J :=
      M.equivMapOfInjective (fixSubgroup β).subtype (fixSubgroup β).subtype_injective
    haveI hJn : (J.subgroupOf (fixSubgroup β)).Normal := by
      rw [hJM]
      exact hMn
    have hsolJ : Group.IsSolvable (↥(fixSubgroup β) ⧸ J.subgroupOf (fixSubgroup β)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (QuotientGroup.quotientMulEquivOfEq hJM).toMonoidHom)
        (QuotientGroup.quotientMulEquivOfEq hJM).injective
    have hJs : IsSimpleGroup ↥J := eJ.isSimpleGroup_congr.1 hMs
    have hJnc : ∃ x y : ↥J, x * y ≠ y * x := by
      obtain ⟨a, b, hab⟩ := hMnc
      exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by simpa using h))⟩
    refine lieCompExport_of_normal_quasisimple hJC
      (LieSemisimple.isQuasisimple_of_isSimpleGroup hJs hJnc) hsolJ
      ⟨↥M, inferInstance, inferInstance, lieFactorData_of_simple hMnc hMchev, eJ.toMonoidHom,
        eJ.surjective, ?_⟩ ?_
    · intro x hx
      rw [MonoidHom.mem_ker] at hx
      have : x = 1 := eJ.injective (by rw [map_one]; exact hx)
      rw [this]
      exact one_mem _
    · exact isEmpty_quotient_center_alt6 (b3Lie_center_eq_bot hJnc)
        ⟨fun f => hMA6.false (eJ.trans f)⟩
  · right
    intro J hJ
    obtain ⟨K, hK⟩ := exists_glaPComponent_top_of_subgroup (H := fixSubgroup β) hJ
    exact hno K hK

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
