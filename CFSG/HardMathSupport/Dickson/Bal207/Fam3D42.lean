module

public import CFSG.HardMathSupport.Dickson.Bal207.Fam3D42Inner
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Glue
public import CFSG.HardMathSupport.Seitz.TrialityEven.TwoThree

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.RankThree.PartTwo.Sec4.Item434D42

set_option linter.unusedSectionVars false

theorem excTriD4_index {d : TauCeti.ValidLieTypeIndex} (hd : IsExc3D42 d.1) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      IsTwoPow q 1 ∧ d = ⟨.trialityD4 q, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | trialityD4 q => exact ⟨q, hv, hd, rfl⟩
  | _ => exact absurd hd (by simp [IsExc3D42])

section TriD4Two


theorem compShape_triD4_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (ψ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥d4P)
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ : β ^ 3 = 1)
    (hβ1 : β ≠ 1) : CompShape G28CompType β := by
  by_cases hin : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  · obtain ⟨x, rfl⟩ := hin
    have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
      center_graphFixedRootGroup_eq_bot σ.surjective
    have hx3 : x ^ 3 = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ, map_one])
    have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    have hxo : orderOf (ψ x) = 3 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime hx3 hx1
    refine CompShape.of_congr isoInvariant_g28CompType ψ ?_
    have hc : MulAut.congr ψ (MulAut.conj x) = MulAut.conj (ψ x) := by
      refine MulEquiv.ext fun y => ?_
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    rw [hc]
    exact compShape_conj_d4P (ψ x) hxo
  · exact compShape_outer hK σ hσ β hβ hin

theorem bal207PlusFam3D42 (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusFam3D42 G := by
  intro X _ _ _ p K B A ctx hq hIH
  obtain ⟨d, ⟨rfl, hd⟩, ⟨f⟩⟩ := hq
  obtain ⟨q, hv, hq1, rfl⟩ := excTriD4_index hd
  obtain ⟨K₃, _, _, σ, hK₃, hσ, -, ⟨eK⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  obtain ⟨φ8, hcard⟩ := CFSG.HardMathSupport.Seitz.TrialityEven.exists_equiv_trialityGroup8
    hq1.1 hq1.2 hv
  obtain ⟨ψ8⟩ := nonempty_mulEquiv_d4P φ8 hcard
  rw [hq1.1, hq1.2] at hK₃ hσ
  exact bal207PlusFamClauses_of_compShape ctx hIH isoInvariant_g28CompType (f.trans eK)
    (fun β hβ hβ1 => compShape_triD4_two hK₃ σ hσ (eK.symm.trans ψ8) β hβ hβ1)
    (fun J hJ hs => absurd (isBalSmall_of_g28CompType hJ) hs)

end TriD4Two

end CFSG.HardMathSupport.Dickson.Bal207.Fam3D42

end
