module

public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import Certificates.Certificate12043

public section

namespace CFSG.LieType.Multipliers.G23

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Sporadic.He.Native CFSG.CosetTable CFSG.Open
  CFSG.RankThree.PerfectCover CFSG.LieType.Steinberg.CentralExt

theorem coverCheck_eq_true : coverCheck = true :=
  Certificates.certificate12043.1

theorem relSixCheck_eq_true : relSixCheck = true :=
  Certificates.certificate12043.2

theorem cover_facts :
    toMat 2 54 coverA * toMat 2 54 coverA = 1 ∧ toMat 2 54 coverB * toMat 2 54 coverBInv = 1 ∧
      (∀ v ∈ coverWords rels (fun i => commWords (pairs i)), toMat 2 54 (coverWordArr v) = 1) ∧
      toMat 2 54 (coverWordArr relSix) ^ 3 = 1 ∧ toMat 2 54 (coverWordArr relSix) ≠ 1 := by
  have h := coverCheck_eq_true
  have h' := relSixCheck_eq_true
  simp only [coverCheck, relSixCheck, Bool.and_eq_true, List.all_eq_true] at h h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨h4, h5⟩ := h'
  refine ⟨?_, ?_, fun v hv => ?_, ?_, fun hZ => ?_⟩
  · rw [← toMat_mulM, toMat_eq_of_beq h1, toMat_idM]
  · rw [← toMat_mulM, toMat_eq_of_beq h2, toMat_idM]
  · rw [toMat_eq_of_beq (h3 v hv), toMat_idM]
  · rw [pow_three, ← toMat_mulM, ← toMat_mulM, toMat_eq_of_beq h4, toMat_idM]
  · have h01 := congrFun (congrFun hZ 0) 1
    rw [toMat_apply, Matrix.one_apply_ne (by decide)] at h01
    rw [beq_iff_eq] at h5
    rw [show ((0 : Fin 54) : ℕ) = 0 from rfl, show ((1 : Fin 54) : ℕ) = 1 from rfl, h5] at h01
    exact absurd h01 (by decide)

noncomputable def coverGL : Fin 2 → GL (Fin 54) (ZMod 2)
  | 0 => ⟨toMat 2 54 coverA, toMat 2 54 coverA, cover_facts.1, cover_facts.1⟩
  | 1 => ⟨toMat 2 54 coverB, toMat 2 54 coverBInv, cover_facts.2.1, by
      rw [coverBInv, toMat_mulM, Matrix.mul_assoc, ← toMat_mulM, ← coverBInv, cover_facts.2.1]⟩

theorem val_coverGL_letter (l : Fin 2 × Bool) :
    ((cond l.2 (coverGL l.1) (coverGL l.1)⁻¹ : GL (Fin 54) (ZMod 2)) :
      Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 (coverLetter l) := by
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s <;> rfl

theorem val_lift_coverGL (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift coverGL (FreeGroup.mk w) : GL (Fin 54) (ZMod 2)) :
      Matrix (Fin 54) (Fin 54) (ZMod 2)) = toMat 2 54 (coverWordArr w) := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => rw [List.map_nil, List.prod_nil, Units.val_one, coverWordArr, List.foldr_nil,
      toMat_idM]
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, val_coverGL_letter]
    change _ = toMat 2 54 (mulM 2 54 (coverLetter l) (coverWordArr w))
    rw [toMat_mulM]

abbrev Cov : Type := PresentedCover (wordSet rels) fun i => FreeGroup.mk (commWords (pairs i))

theorem lift_coverGL_coverRelators :
    ∀ r ∈ coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (pairs i))),
      FreeGroup.lift coverGL r = 1 := by
  intro r hr
  rw [coverRelators_wordSet] at hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
  exact Units.ext (by rw [val_lift_coverGL, cover_facts.2.2.1 v hv, Units.val_one])

noncomputable def rho : Cov →* GL (Fin 54) (ZMod 2) :=
  PresentedGroup.toGroup lift_coverGL_coverRelators

theorem relSix_mem : relSix ∈ rels :=
  List.mem_map_of_mem (by simp [relStrings])

theorem orderOf_rho_relSix :
    orderOf (rho (PresentedGroup.mk _ (FreeGroup.mk relSix))) = 3 := by
  have hval := val_lift_coverGL relSix
  refine orderOf_eq_prime (Units.ext ?_) fun h1 => cover_facts.2.2.2.2 ?_
  · change ((FreeGroup.lift coverGL (FreeGroup.mk relSix) ^ 3 : GL (Fin 54) (ZMod 2)) :
      Matrix (Fin 54) (Fin 54) (ZMod 2)) = _
    rw [Units.val_pow_eq_pow_val, hval, cover_facts.2.2.2.1, Units.val_one]
  · change FreeGroup.lift coverGL (FreeGroup.mk relSix) = 1 at h1
    rw [← hval, h1, Units.val_one]

theorem three_dvd_orderOf_relSix :
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk relSix) : Cov) := by
  rw [← orderOf_rho_relSix]
  exact orderOf_map_dvd _ _

section Multiplier


variable {K : Type} [Field K]

theorem nonempty_ringEquiv_zmod_three (hK : Nat.card K = 3) : Nonempty (K ≃+* ZMod 3) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [← Nat.card_eq_fintype_card, hK, ZMod.card])⟩

theorem three_dvd_card_griessHopfMultiplier (hK : Nat.card K = 3) :
    3 ∣ Nat.card (griessHopfMultiplier (adjointGroup .G2 K)) := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_three hK
  have hP := isPresentation σ hK
  have hw : ∀ i, FreeGroup.mk (commWords (pairs i)) ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  have hwg := lift_gens_commWords σ
  have hz : (PresentedGroup.mk _ (FreeGroup.mk relSix) : Cov) ∈ (coverMap hP hwg).ker := by
    rw [MonoidHom.mem_ker, coverMap_mk]
    exact hP.lift_eq_one (List.mem_map_of_mem relSix_mem)
  rw [Nat.card_congr (griessHopfMultiplierEquivKer hP hw hwg).toEquiv]
  exact three_dvd_orderOf_relSix.trans (Subgroup.orderOf_dvd_natCard _ hz)

theorem exists_orderOf_eq_three (hK : Nat.card K = 3) :
    Finite (griessHopfMultiplier (adjointGroup .G2 K)) ∧
      ∃ z : griessHopfMultiplier (adjointGroup .G2 K), orderOf z = 3 := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_zmod_three hK
  have hperf := isPerfect_of_isPresentation (isPresentation σ hK)
    (fun i => mk_commWords_mem_commutator _) (lift_gens_commWords σ)
  have : Finite (adjointGroup .G2 K) :=
    Nat.finite_of_card_ne_zero (by rw [card_adjointGroup_G2_eq hK]; norm_num)
  have : Finite (hopfMultiplier (adjointGroup .G2 K)) := finite_hopfMultiplier hperf
  have : Finite (griessHopfMultiplier (adjointGroup .G2 K)) :=
    Finite.of_equiv _ (hopfMultiplierEquivGriess _).symm.toEquiv
  exact ⟨inferInstance, exists_prime_orderOf_dvd_card' 3 (three_dvd_card_griessHopfMultiplier hK)⟩

theorem nontrivial_griessHopfMultiplier (hK : Nat.card K = 3) :
    Nontrivial (griessHopfMultiplier (adjointGroup .G2 K)) := by
  obtain ⟨-, z, hz⟩ := exists_orderOf_eq_three hK
  exact ⟨⟨z, 1, fun h => by rw [h, orderOf_one] at hz; omega⟩⟩

theorem three_dvd_card_griessHopfMultiplier_of_mulEquiv (hK : Nat.card K = 3) {X : Type}
    [Group X] (e : X ≃* adjointGroup .G2 K) : 3 ∣ Nat.card (griessHopfMultiplier X) := by
  rw [Nat.card_congr (griessHopfMultiplierCongr e).toEquiv]
  exact three_dvd_card_griessHopfMultiplier hK

theorem three_dvd_card_griessHopfMultiplier_adjointQuotient (hK : Nat.card K = 3) :
    3 ∣ Nat.card (griessHopfMultiplier (AdjointQuotient .G2 K)) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  exact three_dvd_card_griessHopfMultiplier_of_mulEquiv hK
    ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)

end Multiplier

end CFSG.LieType.Multipliers.G23
