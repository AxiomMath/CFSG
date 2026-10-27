module

public import CFSG.GH74.Uniqueness.SU.KI1r4F61Mod
public import CFSG.GH74.Uniqueness.SU.KI1r3FamSp1

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open CFSG CFSG.Blueprint CFSG.GH74.Uniqueness.SU.K.R3

@[expose] def StrictFamSp (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], NativeSporadic.IsSporadic K s → StrictFix K

theorem strictFix_of_equiv_inner {K S : Type} [Group K] [Finite K] [Group S] [IsSimpleGroup S]
    (e : K ≃* S) (hS : ¬ (Nat.card S).Prime)
    (hinn : ∀ β : MulAut K, ∃ l : K, ∀ x : K, β x = l⁻¹ * x * l) : StrictFix K := by
  have : IsSimpleGroup K := e.isSimpleGroup
  refine StrictFix.of_inner (FamSp1.exists_noncomm_of_simple ?_) fun α _ => ?_
  · rwa [Nat.card_congr e.toEquiv]
  · obtain ⟨l, hl⟩ := hinn α
    exact ⟨l⁻¹, MulEquiv.ext fun x => by simp [hl x]⟩

@[expose] def OuterFourSp (s : TauCeti.SporadicName) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], NativeSporadic.IsSporadic K s →
    ∀ α : MulAut K, α ^ 2 = 1 → (¬ ∃ g : K, α = MulAut.conj g) →
      ∃ V : Subgroup K, (∀ v ∈ V, α v = v) ∧ Open.IsElemAbelian 2 V ∧ Nat.card V = 4

theorem strictSp_of_outerFour (s : TauCeti.SporadicName)
    (hs : IsSimpleGroup (NativeSporadic.Carrier s))
    (hnp : ¬ (Nat.card (NativeSporadic.Carrier s)).Prime) (h : OuterFourSp s) :
    StrictFamSp s := by
  intro K _ _ he
  obtain ⟨e⟩ := he
  have : IsSimpleGroup K := e.isSimpleGroup
  have hnab : ∃ a b : K, a * b ≠ b * a :=
    FamSp1.exists_noncomm_of_simple (by rwa [Nat.card_congr e.toEquiv])
  exact StrictFix.of_outer hnab fun α hα2 hα => h K ⟨e⟩ α hα2 hα

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover in
theorem strictFix_M12
    : StrictFix NativeSporadic.M12 := by
  have : IsSimpleGroup NativeSporadic.M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  intro α hα
  by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner NativeSporadic.M12
  · obtain ⟨g, rfl⟩ := hin
    exact four_group_fixed_of_inner
      (FamSp1.exists_noncomm_of_simple (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)) g hα
  · have h1 : α ≠ 1 := fun h => hin (h ▸ Subgroup.one_mem _)
    have h2 : orderOf α = 2 := orderOf_eq_prime hα h1
    obtain ⟨g, rfl⟩ := exists_conj_beta_of_outer h2 hin
    obtain ⟨hD, -, -, -, -, -, -, hWD, hW4, -, -, -, hWsq, hWc, -⟩ :=
      fusionData_pinned.map (MulAut.conj g)
    refine ⟨fusionW.map (MulAut.conj g).toMonoidHom, ?_, ?_, hW4⟩
    · intro v hv
      have hv' := hWD hv
      rw [hD] at hv'
      have hle : ⁅fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹),
          fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹)⁆ ≤
          fixSub (MulAut.conj g * beta * (MulAut.conj g)⁻¹) := by
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
          (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
      exact mem_fixSub.1 (hle hv')
    · rw [SU1.isElemAbelian_iff]
      exact ⟨hWc, hWsq⟩

theorem strictSp_M11 :
    StrictFamSp .M11 := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .M11) :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  refine strictFix_of_equiv_inner e ?_ fun β => ?_
  · show ¬ (Nat.card NativeSporadic.M11).Prime
    rw [CFSG.Sporadic.Mathieu.card_M11]
    norm_num
  · exact CFSG.QuasithinUnique.Ch1.autInner_of_equiv_of_inner e
      CFSG.QuasithinUnique.Ch1.m11_all_inner β

theorem strictSp_J1 :
    StrictFamSp .J1 := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .J1) :=
    CFSG.Sporadic.J1.fam_j1_simplicity.2.2
  refine strictFix_of_equiv_inner e ?_ fun β => ?_
  · show ¬ (Nat.card NativeSporadic.J1).Prime
    rw [CFSG.Sporadic.J1.card_J1]
    norm_num
  · exact CFSG.QuasithinUnique.Ch1.isInnerAut_of_carrierJ1 e β

theorem strictSp_M23 :
    StrictFamSp .M23 := by
  intro K _ _ ⟨e⟩
  have : IsSimpleGroup (NativeSporadic.Carrier .M23) :=
    CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  refine strictFix_of_equiv_inner e ?_ fun β => ?_
  · show ¬ (Nat.card NativeSporadic.M23).Prime
    rw [CFSG.Sporadic.Schreier.m23_card]
    norm_num
  · exact CFSG.QuasithinUnique.Ch1.autInner_of_equiv_of_inner e
      CFSG.QuasithinUnique.Ch1.m23_all_inner β

theorem strictSp_M12
    : StrictFamSp .M12 := by
  intro K _ _ ⟨e⟩
  exact StrictFix.of_mulEquiv (K := NativeSporadic.M12) (e.symm : NativeSporadic.M12 ≃* K)
    strictFix_M12

end CFSG.GH74.Uniqueness.SU.K.R4
