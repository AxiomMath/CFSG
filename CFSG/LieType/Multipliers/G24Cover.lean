module

public import CFSG.LieType.Multipliers.G24Bridge
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier

public section

namespace CFSG.LieType.Multipliers.G24

open Subgroup CFSG.Open CFSG.Fischer CFSG.Blueprint.Chevalley

theorem toMat_one12 : toMat 12 one12 = 1 :=
  toMat_ofMat 1

theorem ofMat_toMat_mulArr {R : Type*} [Semiring R] (n : ℕ) (A B : Array (Array R)) :
    ofMat (toMat n (mulArr n A B)) = mulArr n A B := by
  rw [toMat_mulArr]
  rfl

theorem ofMat_toMat_wordArr3 (w : List (Fin 6 × Bool)) :
    ofMat (toMat 12 (wordArr3 w)) = wordArr3 w := by
  cases w with
  | nil => exact congrArg ofMat toMat_one12
  | cons l w => exact ofMat_toMat_mulArr 12 _ _

theorem nonempty_ringEquiv_F4 {K : Type} [Field K] (hK : Nat.card K = 4) :
    Nonempty (K ≃+* F4) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [Fintype.card_eq_nat_card, hK, F4.card])⟩

theorem dSq_mem_rels : dSq ∈ rels :=
  List.mem_map_of_mem (by simp only [relStrings, List.mem_cons, true_or, or_true])

abbrev Cov : Type :=
  PresentedCover (wordSet rels) fun i => FreeGroup.mk (commWords (pairs i))

theorem lift_gen_commWords (i : Fin 6) :
    FreeGroup.lift gen (FreeGroup.mk (commWords (pairs i))) = gen i := by
  have h := comm_check
  rw [commCheck, List.all_eq_true] at h
  apply Subtype.ext
  rw [coe_lift_gen]
  exact Units.ext (by rw [val_lift_genGL, of_decide_eq_true (h i (List.mem_finRange i))]; rfl)

@[expose] def liftMat (i : Fin 6) : Matrix (Fin 12) (Fin 12) (ZMod 3) := toMat 12 (liftArr i)

@[expose] def liftInvMat (i : Fin 6) : Matrix (Fin 12) (Fin 12) (ZMod 3) :=
  toMat 12 (liftInvArr i)

section Lifts

theorem liftMat_mul_liftInvMat (i : Fin 6) :
    liftMat i * liftInvMat i = 1 ∧ liftInvMat i * liftMat i = 1 := by
  have h := unit_check
  rw [unitCheck, List.all_eq_true] at h
  have h' := h i (List.mem_finRange i)
  rw [Bool.and_eq_true] at h'
  rw [liftMat, liftInvMat, ← toMat_mulArr, ← toMat_mulArr, of_decide_eq_true h'.1,
    of_decide_eq_true h'.2, toMat_one12]
  exact ⟨rfl, rfl⟩

@[expose] def liftGL (i : Fin 6) : GL (Fin 12) (ZMod 3) :=
  ⟨liftMat i, liftInvMat i, (liftMat_mul_liftInvMat i).1, (liftMat_mul_liftInvMat i).2⟩

theorem val_lift_liftGL (w : List (Fin 6 × Bool)) :
    ((FreeGroup.lift liftGL (FreeGroup.mk w) : GL (Fin 12) (ZMod 3)) :
      Matrix (Fin 12) (Fin 12) (ZMod 3)) = toMat 12 (wordArr3 w) := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => exact toMat_one12.symm
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih]
    change _ = toMat 12 (mulArr 12 (letterArr3 l) (wordArr3 w))
    rw [toMat_mulArr]
    congr 1
    obtain ⟨i, s⟩ := l
    cases s <;> rfl

theorem lift_liftGL_coverRelators :
    ∀ r ∈ coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (pairs i))),
      FreeGroup.lift liftGL r = 1 := by
  rw [coverRelators_wordSet]
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  have h := cover_check
  rw [coverCheck, List.all_eq_true] at h
  exact Units.ext (by rw [val_lift_liftGL, of_decide_eq_true (h w hw), toMat_one12]; rfl)

@[expose] noncomputable def rho : Cov →* GL (Fin 12) (ZMod 3) :=
  PresentedGroup.toGroup lift_liftGL_coverRelators

theorem rho_mk (x : FreeGroup (Fin 6)) : rho (PresentedGroup.mk _ x) = FreeGroup.lift liftGL x :=
  rfl

theorem rho_dSq :
    rho (PresentedGroup.mk _ (FreeGroup.mk dSq)) ≠ 1 ∧
      rho (PresentedGroup.mk _ (FreeGroup.mk dSq)) ^ 2 = 1 := by
  have h := ker_check
  rw [kerCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [rho_mk]
  refine ⟨fun h1 => of_decide_eq_false h.1 ?_, Units.ext ?_⟩
  · have h2 := congrArg
      (fun x : GL (Fin 12) (ZMod 3) => ofMat (x : Matrix (Fin 12) (Fin 12) (ZMod 3))) h1
    simp only [val_lift_liftGL, ofMat_toMat_wordArr3, Units.val_one] at h2
    exact h2
  · rw [sq, Units.val_mul, val_lift_liftGL, ← toMat_mulArr, of_decide_eq_true h.2, toMat_one12,
      Units.val_one]

end Lifts

section Multiplier

noncomputable def griessHopfMultiplierEquiv :
    griessHopfMultiplier grp ≃* (coverMap isPresentation lift_gen_commWords).ker :=
  griessHopfMultiplierEquivKer isPresentation (fun _ => mk_commWords_mem_commutator _)
    lift_gen_commWords

theorem mk_dSq_mem_ker :
    PresentedGroup.mk _ (FreeGroup.mk dSq) ∈ (coverMap isPresentation lift_gen_commWords).ker := by
  rw [MonoidHom.mem_ker, coverMap_mk]
  exact isPresentation.lift_eq_one (List.mem_map_of_mem dSq_mem_rels)

theorem nontrivial_two_dvd_griessHopfMultiplier_grp :
    Nontrivial (griessHopfMultiplier grp) ∧ 2 ∣ Nat.card (griessHopfMultiplier grp) := by
  set z : (coverMap isPresentation lift_gen_commWords).ker := ⟨_, mk_dSq_mem_ker⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (rho (z : Cov)) = 2 := orderOf_eq_prime rho_dSq.2 rho_dSq.1
  have hz : z ≠ 1 := fun h => rho_dSq.1 (by
    rw [show (PresentedGroup.mk _ (FreeGroup.mk dSq) : Cov) = (z : Cov) from rfl, h,
      OneMemClass.coe_one, map_one])
  have hdvd : 2 ∣ orderOf z := by
    rw [← hord]
    exact orderOf_map_dvd (rho.comp (coverMap isPresentation lift_gen_commWords).ker.subtype) z
  refine ⟨⟨griessHopfMultiplierEquiv.symm z, 1, ?_⟩, ?_⟩
  · rw [Ne, MulEquiv.map_eq_one_iff]
    exact hz
  · rw [Nat.card_congr griessHopfMultiplierEquiv.toEquiv]
    exact hdvd.trans (orderOf_dvd_natCard z)

variable {K : Type} [Field K]

theorem nontrivial_griessHopfMultiplier (hK : Nat.card K = 4) :
    Nontrivial (griessHopfMultiplier ↥(adjointGroup .G2 K)) := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_F4 hK
  have := nontrivial_two_dvd_griessHopfMultiplier_grp.1
  exact (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
    (adjointEquiv σ hK)).toEquiv.nontrivial

theorem two_dvd_card_griessHopfMultiplier (hK : Nat.card K = 4) :
    2 ∣ Nat.card (griessHopfMultiplier ↥(adjointGroup .G2 K)) := by
  obtain ⟨σ⟩ := nonempty_ringEquiv_F4 hK
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr
    (adjointEquiv σ hK)).toEquiv]
  exact nontrivial_two_dvd_griessHopfMultiplier_grp.2

theorem multiplier_G2_four (hK : Nat.card K = 4) :
    Nat.card (griessHopfMultiplier ↥(adjointGroup .G2 K)) = 2 ∧
      Nonempty (griessHopfMultiplier ↥(adjointGroup .G2 K) ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨hperf, hle⟩ :=
    CFSG.LieType.Steinberg.CentralExt.G2Four.g2_four_card_griessHopfMultiplier_le hK
  have : Finite ↥(adjointGroup .G2 K) :=
    Nat.finite_of_card_ne_zero (by rw [card_adjointGroup hK]; norm_num)
  have := CFSG.RankThree.PerfectCover.finite_hopfCover hperf
  have : Finite (griessHopfMultiplier ↥(adjointGroup .G2 K)) :=
    Finite.of_equiv _ (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv
  have hpos : 0 < Nat.card (griessHopfMultiplier ↥(adjointGroup .G2 K)) := Nat.card_pos
  obtain ⟨k, hk⟩ := two_dvd_card_griessHopfMultiplier hK
  have hc : Nat.card (griessHopfMultiplier ↥(adjointGroup .G2 K)) = 2 := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨hc, ⟨mulEquivOfPrimeCardEq hc (by simp [Nat.card_eq_fintype_card])⟩⟩

end Multiplier

end CFSG.LieType.Multipliers.G24
