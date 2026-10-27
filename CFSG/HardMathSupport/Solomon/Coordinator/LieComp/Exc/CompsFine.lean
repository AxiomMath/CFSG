module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false

@[expose] def CompsWith (P : (X : Type) → [Group X] → Prop) (C : Type) [Group C] : Prop :=
  ∀ K : Subgroup C, IsComponentOf K ⊤ → P ↥K

@[expose] def ComponentFactor (q : ℕ) (X : Type) [Group X] : Prop :=
  (∃ (Y : Type) (_ : Group Y) (_ : Finite Y), LieFactorData q Y ∧
    ∃ f : Y →* X, Function.Surjective f ∧ f.ker ≤ Subgroup.center Y) ∧
  IsEmpty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))

@[expose] def CompsFine (q : ℕ) (C : Type) [Group C] : Prop :=
  ∀ K : Subgroup C, IsComponentOf K ⊤ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥K, Function.Surjective f ∧ f.ker ≤ Subgroup.center X) ∧
    IsEmpty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6))

theorem compsFine_iff_compsWith (q : ℕ) (C : Type) [Group C] :
    CompsFine q C ↔ CompsWith (ComponentFactor q) C :=
  Iff.rfl

structure IsComponentProperty (P : (X : Type) → [Group X] → Prop) : Prop where
  of_mulEquiv : ∀ {X Y : Type} [Group X] [Group Y], (X ≃* Y) → P X → P Y

theorem isComponentProperty_componentFactor (q : ℕ) :
    IsComponentProperty (ComponentFactor q) where
  of_mulEquiv := by
    rintro X Y _ _ e ⟨⟨Z, _, _, hZ, f, hf, hfk⟩, hA6⟩
    refine ⟨⟨Z, inferInstance, inferInstance, hZ, e.toMonoidHom.comp f, e.surjective.comp hf,
      ?_⟩, ?_⟩
    · intro z hz
      apply hfk
      rw [MonoidHom.mem_ker] at hz ⊢
      exact e.injective (by simpa using hz)
    · exact ⟨fun a => hA6.false
        ((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans a)⟩

theorem CompsWith.of_mulEquiv {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {C C' : Type} [Group C] [Group C'] (e : C ≃* C')
    (h : CompsWith P C') : CompsWith P C := by
  intro K hK
  have hK' : IsComponentOf (K.map (e : C →* C')) ⊤ := by
    have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hK
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  let g : ↥K ≃* ↥(K.map (e : C →* C')) := K.equivMapOfInjective (e : C →* C') e.injective
  exact hP.of_mulEquiv g.symm (h _ hK')

theorem CompsFine.of_mulEquiv {q : ℕ} {C C' : Type} [Group C] [Group C'] (e : C ≃* C')
    (h : CompsFine q C') : CompsFine q C := by
  rw [compsFine_iff_compsWith] at h ⊢
  exact CompsWith.of_mulEquiv (isComponentProperty_componentFactor q) e h

theorem lieCompExport_of_compsFine {q : ℕ} {S : Type} [Group S] {β : MulAut S}
    (hlayer : PerfectInLayer β) (hc : CompsFine q ↥(fixSubgroup β)) : LieCompExport q β := by
  refine ⟨hlayer, fun K hK => ?_, fun ⟨K, hK, ⟨a⟩⟩ => ?_⟩
  · have hK' := (LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hK.1).1 hK
    obtain ⟨⟨X, _, _, hX, f, hf, hfk⟩, -⟩ := hc _ hK'
    let g : ↥(K.subgroupOf (fixSubgroup β)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
    refine ⟨X, inferInstance, inferInstance, hX, g.toMonoidHom.comp f, g.surjective.comp hf, ?_⟩
    intro x hx
    apply hfk
    rw [MonoidHom.mem_ker] at hx ⊢
    apply g.injective
    rw [map_one]
    exact hx
  · exfalso
    have hK' := (LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hK.1).1 hK
    obtain ⟨-, hA6⟩ := hc _ hK'
    let g : ↥(K.subgroupOf (fixSubgroup β)) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hK.1
    exact hA6.false ((QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)).trans a)

theorem le_perfectResidual_of_perfect {C : Type} [Group C] {P : Subgroup C} (hP : ⁅P, P⁆ = P) :
    P ≤ CFSG.perfectResidual C := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc P = ⁅P, P⁆ := hP.symm
      _ ≤ ⁅derivedSeries C n, derivedSeries C n⁆ := Subgroup.commutator_mono ih ih

theorem compsWith_of_perfectResidual {P : (X : Type) → [Group X] → Prop} {C : Type} [Group C]
    [Finite C] (hq : CFSG.IsQuasisimple ↥(CFSG.perfectResidual C))
    (hPJ : P ↥(CFSG.perfectResidual C)) : CompsWith P C := by
  intro K hK
  have hRn : (CFSG.perfectResidual C).Normal := by
    haveI := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic (G := C)
    infer_instance
  have hRc : IsComponentOf (CFSG.perfectResidual C) ⊤ :=
    ⟨le_top, IsSubnormal.step le_top ((Subgroup.normal_subgroupOf_iff le_top).2
      fun h k hh _ => hRn.conj_mem h hh k) (IsSubnormal.refl _),
      LieSemisimple.open_isQuasisimple hq⟩
  obtain rfl := eq_of_isComponentOf_of_perfect_le hRc
    (fun P _ hP => le_perfectResidual_of_perfect hP) hK
  exact hPJ

theorem compsFine_of_perfectResidual {q : ℕ} {C : Type} [Group C] [Finite C]
    (hq : CFSG.IsQuasisimple ↥(CFSG.perfectResidual C))
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥(CFSG.perfectResidual C), Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥(CFSG.perfectResidual C) ⧸ Subgroup.center ↥(CFSG.perfectResidual C)) ≃*
      alternatingGroup (Fin 6))) : CompsFine q C := by
  rw [compsFine_iff_compsWith]
  exact compsWith_of_perfectResidual hq ⟨hX, hA6⟩

theorem compsWith_of_isSolvable {P : (X : Type) → [Group X] → Prop} {C : Type} [Group C]
    [Group.IsSolvable C] : CompsWith P C := by
  intro K hK
  exfalso
  obtain ⟨hp, hs⟩ := hK.2.2
  haveI := hs.toNontrivial
  haveI : Nontrivial ↥K := (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
  exact absurd hp (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K))

theorem compsFine_of_isSolvable {q : ℕ} {C : Type} [Group C] [Group.IsSolvable C] :
    CompsFine q C := by
  rw [compsFine_iff_compsWith]
  exact compsWith_of_isSolvable

theorem eq_bot_or_top_of_isSubnormal' {S : Type*} [Group S] [IsSimpleGroup S] {L : Subgroup S}
    (h : IsSubnormal L ⊤) : L = ⊥ ∨ L = ⊤ := by
  suffices ∀ M K : Subgroup S, IsSubnormal M K → K = ⊤ → M = ⊥ ∨ M = ⊤ from this L ⊤ h rfl
  intro M K hMK
  induction hMK with
  | refl => intro hK; exact Or.inr hK
  | @step H M K hle hnormal _ ih =>
    intro hK
    rcases ih hK with hM | hM
    · left
      exact le_bot_iff.1 (hM ▸ hle)
    · subst hM
      have hN : H.Normal := by
        rw [Subgroup.normal_subgroupOf_iff hle] at hnormal
        exact ⟨fun x hx g => hnormal x g hx (Subgroup.mem_top g)⟩
      haveI := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal H

theorem compsWith_of_simple {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {C : Type} [Group C] [Finite C]
    [IsSimpleGroup C] (hnc : ∃ a b : C, a * b ≠ b * a) (hPJ : P C) : CompsWith P C := by
  intro K hK
  have hKtop : K = ⊤ := by
    rcases eq_bot_or_top_of_isSubnormal' hK.2.1 with h | h
    · exfalso
      subst h
      have := hK.2.2.2.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(⊥ : Subgroup C) ⧸ Subgroup.center ↥(⊥ : Subgroup C))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (congrArg _ (Subsingleton.elim a b))
    · exact h
  subst hKtop
  exact hP.of_mulEquiv Subgroup.topEquiv.symm hPJ

theorem compsFine_of_simple {q : ℕ} {C : Type} [Group C] [Finite C] [IsSimpleGroup C]
    (hnc : ∃ a b : C, a * b ≠ b * a)
    (hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple q C) (hA6 : IsEmpty (C ≃* alternatingGroup (Fin 6))) :
    CompsFine q C := by
  rw [compsFine_iff_compsWith]
  refine compsWith_of_simple (isComponentProperty_componentFactor q) hnc ⟨?_, ?_⟩
  · exact ⟨C, inferInstance, inferInstance, lieFactorData_of_simple hnc hchev,
      MonoidHom.id C, Function.surjective_id, by simp⟩
  · have hZ : Subgroup.center C = ⊥ := b3Lie_center_eq_bot hnc
    exact isEmpty_quotient_center_alt6 hZ hA6

theorem compsWith_of_commutator {P : (X : Type) → [Group X] → Prop} {C : Type} [Group C]
    [Finite C] (hq : CFSG.IsQuasisimple ↥(commutator C))
    (hPJ : P ↥(commutator C)) : CompsWith P C := by
  intro K hK
  have hRn : (commutator C).Normal := Subgroup.commutator_normal ⊤ ⊤
  have hRc : IsComponentOf (commutator C) ⊤ :=
    ⟨le_top, IsSubnormal.step le_top ((Subgroup.normal_subgroupOf_iff le_top).2
      fun h k hh _ => hRn.conj_mem h hh k) (IsSubnormal.refl _),
      LieSemisimple.open_isQuasisimple hq⟩
  obtain rfl := eq_of_isComponentOf_of_perfect_le hRc
    (fun P _ hP => by
      calc P = ⁅P, P⁆ := hP.symm
        _ ≤ ⁅(⊤ : Subgroup C), ⊤⁆ := Subgroup.commutator_mono le_top le_top) hK
  exact hPJ

theorem compsFine_of_commutator {q : ℕ} {C : Type} [Group C] [Finite C]
    (hq : CFSG.IsQuasisimple ↥(commutator C))
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥(commutator C), Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥(commutator C) ⧸ Subgroup.center ↥(commutator C)) ≃*
      alternatingGroup (Fin 6))) : CompsFine q C := by
  rw [compsFine_iff_compsWith]
  exact compsWith_of_commutator hq ⟨hX, hA6⟩

theorem le_of_perfect_of_solvable_quotient {C : Type} [Group C] {J P : Subgroup C} [J.Normal]
    (hsol : Group.IsSolvable (C ⧸ J)) (hP : ⁅P, P⁆ = P) : P ≤ J := by
  intro x hx
  haveI := hsol
  have h := LieSemisimple.map_eq_one_of_perfect (G := C) (C := ⊤) (P := P) le_top hP
    ((QuotientGroup.mk' J).comp (Subgroup.topEquiv : ↥(⊤ : Subgroup C) ≃* C).toMonoidHom) x hx
  exact (QuotientGroup.eq_one_iff x).1 h

theorem compsWith_of_normal_quasisimple {P : (X : Type) → [Group X] → Prop} {C : Type} [Group C]
    [Finite C] (J : Subgroup C) [J.Normal] (hq : CFSG.IsQuasisimple ↥J)
    (hsol : Group.IsSolvable (C ⧸ J)) (hPJ : P ↥J) : CompsWith P C := by
  intro K hK
  have hJc : IsComponentOf J ⊤ :=
    ⟨le_top, IsSubnormal.step le_top ((Subgroup.normal_subgroupOf_iff le_top).2
      fun h k hh _ => (inferInstance : J.Normal).conj_mem h hh k) (IsSubnormal.refl _),
      LieSemisimple.open_isQuasisimple hq⟩
  obtain rfl := eq_of_isComponentOf_of_perfect_le hJc
    (fun P _ hP => le_of_perfect_of_solvable_quotient hsol hP) hK
  exact hPJ

theorem compsFine_of_normal_quasisimple {q : ℕ} {C : Type} [Group C] [Finite C] (J : Subgroup C)
    [J.Normal] (hq : CFSG.IsQuasisimple ↥J) (hsol : Group.IsSolvable (C ⧸ J))
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥J, Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 6))) : CompsFine q C := by
  rw [compsFine_iff_compsWith]
  exact compsWith_of_normal_quasisimple J hq hsol ⟨hX, hA6⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
