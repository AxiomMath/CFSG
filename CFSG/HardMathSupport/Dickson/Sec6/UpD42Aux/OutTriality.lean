module

public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.InnExcRank
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open TauCeti CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof
  CFSG.TauCetiBridge.Twisted CFSG.HardMathSupport.Solomon.Coordinator

theorem finite_fixedPoints_trialityD4 (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) :
    Finite ↥(TauCeti.fixedSubgroup (d4Index q hv).steinberg) := by
  classical
  let L := d4Closure q hv
  haveI : CharP L q.p := (d4Char_eq q hv) ▸ inferInstance
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let F := frobeniusFixedSubring L q.p (3 * q.exponent)
  haveI : Finite F := finite_frobeniusFixedSubring L q.p (3 * q.exponent)
    (by have h := q.exponent_pos; omega)
  have hentry : ∀ (g : D4Tripled.points L), (d4Index q hv).steinberg g = g →
      ∀ r c, (((g : Matrix.GeneralLinearGroup (Fin 24) L) :
        Matrix (Fin 24) (Fin 24) L) r c) ∈ F := by
    intro g hg r c
    have h0 := steinberg_fixed_entry g hg r c
    have h1 := steinberg_fixed_entry g hg
      (DynkinType.d4TripledTrialityPerm r) (DynkinType.d4TripledTrialityPerm c)
    have h2 := steinberg_fixed_entry g hg
      (DynkinType.d4TripledTrialityPerm (DynkinType.d4TripledTrialityPerm r))
      (DynkinType.d4TripledTrialityPerm (DynkinType.d4TripledTrialityPerm c))
    rw [DynkinType.d4TripledTrialityPerm_apply_apply_apply,
      DynkinType.d4TripledTrialityPerm_apply_apply_apply, h1, h0, ← pow_mul, ← pow_mul] at h2
    have hex : q.card * q.card * q.card = q.p ^ (3 * q.exponent) := by
      rw [PrimePower.card_def, ← pow_add, ← pow_add]
      congr 1
      omega
    simp only [← mul_assoc] at h2
    rw [hex] at h2
    exact mem_frobeniusFixedSubring.mpr h2.symm
  let entries : ↥(TauCeti.fixedSubgroup (d4Index q hv).steinberg) →
      (Fin 24 → Fin 24 → F) := fun g r c =>
    ⟨(((g.val : Matrix.GeneralLinearGroup (Fin 24) L) :
      Matrix (Fin 24) (Fin 24) L) r c), hentry g.val g.property r c⟩
  refine Finite.of_injective entries ?_
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext r c
  exact congrArg Subtype.val (congrFun (congrFun he r) c)

theorem pRank_three_trialityD4_le_three (q : PrimePower)
    (hv : (LieTypeIndex.trialityD4 q).Valid) (hp2 : q.p = 2) :
    letI := finite_fixedPoints_trialityD4 q hv
    CFSG.Open.pRank 3 (⊤ : Subgroup (FixedPointCandidate (d4Index q hv).steinberg)) ≤ 3 := by
  letI := finite_fixedPoints_trialityD4 q hv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let H := TauCeti.fixedSubgroup (d4Index q hv).steinberg
  let Y := commutator ↥H
  have hY2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) ≤ 2 := by
    obtain ⟨E, -, hE, hc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (⊤ : Subgroup ↥Y)
    let φ : ↥Y →* D4Tripled.points (d4Closure q hv) := H.subtype.comp Y.subtype
    have hinj : Function.Injective φ := H.subtype_injective.comp Y.subtype_injective
    letI : Finite (E.map φ) := Finite.of_equiv E
      (E.equivMapOfInjective φ hinj).toEquiv
    have hc' := card_le_nine_of_fixedPoints hp2 (E.map φ)
      (isElemAbelian_map_up34 φ hinj hE) (by
        rintro _ ⟨x, hx, rfl⟩
        exact (x.val : H).property)
    rw [Subgroup.card_map_of_injective hinj, hc] at hc'
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hc')
  exact CFSG.SectionRank.pRank_quotient_le_three (by norm_num) hY2
    (Subgroup.center ↥Y) le_rfl

theorem upD42Chev2Out_triality_holds : UpD42Chev2Out
    (fun d => match d with | .trialityD4 _ => True | _ => False) := by
  intro S _ _ _ _ ⟨d, hv⟩ hd hc ⟨e⟩ α _ hx
  cases d with
  | trialityD4 q =>
    have hp2 : q.p = 2 := hc
    letI := finite_fixedPoints_trialityD4 q hv
    have h3 := pRank_three_trialityD4_le_three q hv hp2
    let e' : S ≃* FixedPointCandidate (d4Index q hv).steinberg := by
      exact e
    obtain ⟨E, hE, h81⟩ := hx.exists_elemAbelian_81
    have hE' := isElemAbelian_map_up34 e'.toMonoidHom e'.injective hE
    have h4 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : E.map e'.toMonoidHom ≤ ⊤)
      hE' (k := 4) (by rw [Subgroup.card_map_of_injective e'.injective, h81]; norm_num)
    omega
  | _ => exact hd.elim

end CFSG.HardMathSupport.Dickson.Sec6

end
