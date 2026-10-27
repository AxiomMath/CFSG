module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Reduction
public import CFSG.HardMathSupport.Dickson.Bal207.Dvd
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

theorem exc_cases_of_bal207Index {d : TauCeti.LieTypeIndex} (h : Bal207Index 3 d)
    (hs : ¬ IsSpIdx d) (hu : ¬ IsUniIdx d) (ho : ¬ IsOrthIdx d) :
    IsG2EightIndex d ∨ IsExcU62 d ∨ IsExc3D42 d ∨ IsExcF42 d ∨ IsExcTits d := by
  cases d with
  | B r q => exact absurd trivial hs
  | twistedA r q =>
    obtain ⟨-, h1 | h1⟩ := h
    · exact absurd ⟨h1.2, h1.1⟩ hu
    · exact Or.inr (Or.inl ⟨h1.2, h1.1⟩)
  | D r q => exact absurd trivial ho
  | twistedD r q => exact absurd trivial ho
  | trialityD4 q => exact Or.inr (Or.inr (Or.inl h.2))
  | G2 q => exact Or.inl h.2
  | F4 q => exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
  | tits => exact Or.inr (Or.inr (Or.inr (Or.inr trivial)))
  | suzuki m => exact absurd h.1 (by norm_num)
  | reeF4 m => exact absurd h.1 (by norm_num)
  | A r q => exact absurd h (by simp [Bal207Index])
  | C r q => exact absurd h (by simp [Bal207Index])
  | E6 q => exact absurd h (by simp [Bal207Index])
  | E7 q => exact absurd h (by simp [Bal207Index])
  | E8 q => exact absurd h (by simp [Bal207Index])
  | twistedE6 q => exact absurd h (by simp [Bal207Index])
  | reeG2 m => exact absurd h (by simp [Bal207Index])

section Quot

variable {X : Type} [Group X]

theorem su38_card_center_quot_dvd {K J : Subgroup X} (hJK : J ≤ K) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
  let π : ↥J →* ↥K ⧸ Subgroup.center ↥K :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hJK)
  have hker : π.ker ≤ Subgroup.center ↥J := by
    intro j hj
    have hj' : Subgroup.inclusion hJK j ∈ Subgroup.center ↥K := by
      have := (MonoidHom.mem_ker).1 hj
      exact (QuotientGroup.eq_one_iff _).1 this
    rw [Subgroup.mem_center_iff] at hj' ⊢
    intro g
    have h2 : (g : X) * j = j * g :=
      congrArg (fun k : ↥K => (k : X)) (hj' (Subgroup.inclusion hJK g))
    exact Subtype.ext h2
  calc Nat.card (↥J ⧸ Subgroup.center ↥J) = (Subgroup.center ↥J).index :=
        (Subgroup.index_eq_card _).symm
    _ ∣ π.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card π.range := Subgroup.index_ker π
    _ ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := Subgroup.card_subgroup_dvd_card _

theorem nineteen_dvd_card_quot_of_isSU38Comp {J : Subgroup X} (hJ : IsSU38Comp J) :
    19 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨e⟩ := KSF4SU3.nonempty_equiv_projSU_of_isLieQuot (isLieQuot_isU3EightIndexTwo hJ)
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSU_three_eight]
  norm_num

end Quot

section Orders

open CFSG.Assembly.LowTwoRank

set_option linter.unusedSectionVars false


theorem not_nineteen_dvd_card_of_numerator {G : Type} [Group G] {t : StatedLieTag}
    {n p f : ℕ} (hL : CFSG.Blueprint.LieModel G t n p f)
    (hn : ¬ 19 ∣ CFSG.ComponentClassification.CatLeaf.lieOrderNumerator t n (p ^ f)) :
    ¬ 19 ∣ Nat.card G := fun h => by
  obtain ⟨-, hmul, -⟩ :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput G t n p f hL.admissible hL
  exact hn (hmul ▸ h.mul_right _)

theorem not_nineteen_dvd_card_u62 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq : IsTwoPow q 1) :
    ¬ 19 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group := by
  have hL := CFSG.Models.lieModel_twistedA 5 q hv (MulEquiv.refl _)
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ = 2 :=
    (TauCeti.LieTypeIndex.characteristic_twistedA 5 q).trans hq.1
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA 5 q).trans hq.2
  rw [hc, hf] at hL
  exact not_nineteen_dvd_card_of_numerator
    (dvdAux_blueprint_of_models (by simp [CFSG.Blueprint.classicalTags]) hL) (by decide +kernel)

theorem not_nineteen_dvd_card_3d42 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hq : IsTwoPow q 1) :
    ¬ 19 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group
      .trialityD4 0 2 q.exponent :=
    .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hq.1
        (MulEquiv.refl _)⟩)
  refine not_nineteen_dvd_card_of_numerator hL ?_
  rw [hq.2]
  decide +kernel

theorem not_nineteen_dvd_card_f42 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.F4 q).Valid) (hq : IsTwoPow q 1) :
    ¬ 19 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group
      .F4 0 2 q.exponent :=
    .inr (.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
      ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
      CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge hB.f4 q hv hq.1
        (MulEquiv.refl _)⟩)
  refine not_nineteen_dvd_card_of_numerator hL ?_
  rw [hq.2]
  decide +kernel

theorem not_nineteen_dvd_card_tits (hv : TauCeti.LieTypeIndex.tits.Valid) :
    ¬ 19 ∣ Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group .Tits 0 2 1 :=
    .inr (.inr (.inl ⟨rfl, by simp [CFSG.Blueprint.reeTitsTags],
      CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv (MulEquiv.refl _)⟩))
  rw [dvdAux_card_eq_numerator hL rfl]
  show ¬ 19 ∣ 17971200
  norm_num

theorem not_nineteen_dvd_of_exc {d : TauCeti.ValidLieTypeIndex}
    (hd : IsExcU62 d.1 ∨ IsExc3D42 d.1 ∨ IsExcF42 d.1 ∨ IsExcTits d.1) :
    ¬ 19 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    rcases hd with ⟨rfl, hq⟩ | h | h | h
    · exact not_nineteen_dvd_card_u62 hv hq
    all_goals exact False.elim h
  | trialityD4 q =>
    rcases hd with h | hq | h | h
    · exact False.elim h
    · exact not_nineteen_dvd_card_3d42 hv hq
    all_goals exact False.elim h
  | F4 q =>
    rcases hd with h | h | hq | h
    · exact False.elim h
    · exact False.elim h
    · exact not_nineteen_dvd_card_f42 hv hq
    · exact False.elim h
  | tits => exact not_nineteen_dvd_card_tits hv
  | _ => rcases hd with h | h | h | h <;> exact False.elim h

theorem false_of_isSU38Comp_of_exc {X : Type} [Group X] {K J : Subgroup X} (hJK : J ≤ K)
    (hJ : IsSU38Comp J) {d : TauCeti.ValidLieTypeIndex}
    (hd : IsExcU62 d.1 ∨ IsExc3D42 d.1 ∨ IsExcF42 d.1 ∨ IsExcTits d.1)
    (e : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)) : False := by
  obtain ⟨eK⟩ := e
  have h19 : 19 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) :=
    (nineteen_dvd_card_quot_of_isSU38Comp hJ).trans (su38_card_center_quot_dvd hJK)
  rw [Nat.card_congr eK.toEquiv] at h19
  exact not_nineteen_dvd_of_exc hd h19

end Orders

end CFSG.HardMathSupport.Dickson.Bal207

end
