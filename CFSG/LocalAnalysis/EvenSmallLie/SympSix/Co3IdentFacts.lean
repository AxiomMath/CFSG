
module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsBase

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModel
public meta import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModel
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentFactsInputs
public import Certificates.Certificate3094
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDataInputs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Sporadic.Schreier.Co3Arrays
public import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check
public import CFSG.Sporadic.Schreier.Co3OrbitZCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import Certificates.Data.CFSGNative.Co3Schreier.Orbit
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.Co3Sp6CheckInputs
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import Mathlib.Data.Matrix.Block
public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
public import Certificates.Certificate3094Base

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Schreier.Co3.Native Subgroup

theorem fact_check :
    relsV.all (fun r => eqA 276 (wordArr r) (idA 276)) = true ∧
    commutesA 276 (genArr 3) (genArr 2) = true ∧ commutesA 276 (genArr 3) (genArr 5) = true ∧
    eqA 276 (genArr 0) (genArr 4) = false ∧ eqA 276 (genArr 0) (idA 276) = false ∧
    eqA 276 (compA 276 (genArr 0) (genArr 0)) (idA 276) = true ∧
    (∀ j < 4608, (commutesA 276 hList[j]! gArrs[0]! && commutesA 276 hList[j]! gArrs[1]! &&
      commutesA 276 hList[j]! gArrs[2]!) = true →
      (eqA 276 hList[j]! (idA 276) || eqA 276 hList[j]! (genArr 4) ||
        eqA 276 hList[j]! (genArr 0) || eqA 276 hList[j]! eaArr) = true) ∧
    ((List.range 4608).filter fun j => commutesA 276 hList[j]! yArr).length = 128 ∧
    (∀ k < 6, eqA 276 (compA 276 (genArr 3) (compA 276 (posArr (edgePairs.getD k ([], [])).1)
      (genArr 3))) (posArr (edgePairs.getD k ([], [])).2) = true) ∧
    eqA 276 (compA 276 bcbArr bcbArr) (idA 276) = true ∧
    eqA 276 (compA 276 bcbArr (compA 276 (genArr 0) bcbArr)) yArr = true ∧
    eqA 276 (compA 276 bcbArr (compA 276 yArr bcbArr)) (genArr 0) = true ∧
    eqA 276 (compA 276 bcbArr (compA 276 (genArr 2) bcbArr)) (genArr 2) = true ∧
    commutesA 276 kpArr (genArr 0) = true ∧ commutesA 276 kpArr yArr = true ∧
    eqA 276 (compA 276 kpArr kpArr) (idA 276) = true ∧ eqA 276 kpArr (idA 276) = false ∧
    eqA 276 (compA 276 uArr (compA 276 uArr uArr)) kpArr = true ∧
    ((List.range 630).any fun j => eqA 276 cBFS.1[j]! eaArr) = true :=
  Certificates.certificate3094

theorem relsV_perm : ∀ r ∈ relsV,
    FreeGroup.lift
    (fun i : Fin 7 => gp i) (FreeGroup.mk r) = 1 := by
  intro r hr
  have h := List.all_eq_true.1 fact_check.1 r hr
  exact eq_of_eqA (rep_wordArr r) rep_idA h

theorem relsC0_M :
    ∀
    r ∈ relsC0,
    FreeGroup.lift mGen (FreeGroup.mk r)
    = 1 := by
  intro r hr
  apply Subtype.ext
  have hcomp : co3M.subtype (FreeGroup.lift mGen (FreeGroup.mk r)) =
      FreeGroup.lift (fun i => co3M.subtype (mGen i)) (FreeGroup.mk r) := by
    rw [← MonoidHom.comp_apply]
    congr 1
    exact FreeGroup.ext_hom _ _ fun i => by simp
  have h1 : FreeGroup.lift (fun i => co3M.subtype (mGen i)) (FreeGroup.mk r) =
      FreeGroup.lift (fun i : Fin 7 => gp i) (FreeGroup.mk r) :=
    lift_mk_congr fun x hx => coe_mGen (mem_mLetters (relsC0_letters r hr x hx))
  rw [coe_one, ← coe_subtype, hcomp, h1]
  exact relsV_perm r (by simp only [relsV, List.mem_append]; exact Or.inl (Or.inl (Or.inl hr)))

theorem gp0_ne_z : gp 0 ≠ co3Z := by
  intro h
  have h' := (eqA_iff rep_g0 rep_g4).2 (h.trans gp_four.symm)
  rw [fact_check.2.2.2.1] at h'
  exact Bool.false_ne_true h'

theorem sP_facts :
    sP ∈ co3P ∧ sP ∉ co3M ∧ sP * sP = 1 ∧ sP * co3Z *
    sP = gp 0 ∧
    sP * gp 0 * sP = co3Z ∧ sP * gp 2 = gp 2 * sP ∧ sP * gp 5 = gp 5 * sP := by
  refine ⟨sP_mem_P, fun h => gp0_ne_z ?_, sP_mul_self, sP_conj_z, sP_conj_a,
    eq_of_eqA (rep_compA rep_g3 rep_g2) (rep_compA rep_g2 rep_g3) fact_check.2.1,
    eq_of_eqA (rep_compA rep_g3 rep_g5) (rep_compA rep_g5 rep_g3) fact_check.2.2.1⟩
  have hc : sP * co3Z = co3Z * sP := mem_centralizer_singleton_iff.1 (co3M_le_centralizer h)
  rw [← sP_conj_z, hc, mul_assoc, sP_mul_self, mul_one]

theorem ma_ne_one :
    ma ≠ 1 := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [coe_ma, coe_one] at h1
  have h' := (eqA_iff rep_g0 rep_idA).2 h1
  rw [fact_check.2.2.2.2.1] at h'
  exact Bool.false_ne_true h'

theorem ma_mul_self :
    ma * ma = 1 := by
  apply Subtype.ext
  rw [coe_mul, coe_ma, coe_one]
  exact eq_of_eqA (rep_compA rep_g0 rep_g0) rep_idA fact_check.2.2.2.2.2.1

theorem involutions :
    orderOf ma = 2 ∧ orderOf me = 2 ∧ ma ≠ me := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨orderOf_eq_prime (by rw [sq, ma_mul_self]) ma_ne_one, by rw [me_eq, orderOf_co3ZM],
    fun h => gp0_ne_z ?_⟩
  have h1 := congrArg Subtype.val h
  rwa [coe_ma, coe_me] at h1

theorem center_edgeGroup
    (x : edgeGroup) :
    x ∈ center edgeGroup ↔ x = 1 ∨ x = eH ∨ x = aH ∨ x = eH * aH := by
  constructor
  · intro hx
    obtain ⟨j, hj, rfl⟩ := exists_eltH x
    have hc : ∀ i < 3, commutesA 276 hList[j]! gArrs[i]! = true := fun i hi =>
      (commutesA_iff (rep_eltH hj) (rep_gArrs i (by simpa [gArrs] using hi))).2
        (mem_center_iff.1 hx (gH i)).symm
    have h := fact_check.2.2.2.2.2.2.1 j hj
      (by simp only [hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num), Bool.and_self])
    simp only [Bool.or_eq_true] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl (perm_injective (eq_of_eqA (rep_eltH hj) rep_idA h))
    · exact Or.inr (Or.inl (perm_injective
        ((eq_of_eqA (rep_eltH hj) rep_g4 h).trans (by rw [perm_eH, gp_four]))))
    · exact Or.inr (Or.inr (Or.inl (perm_injective
        ((eq_of_eqA (rep_eltH hj) rep_g0 h).trans perm_aH.symm))))
    · exact Or.inr (Or.inr (Or.inr (perm_injective (eq_of_eqA (rep_eltH hj) rep_eaH h))))
  · rintro (rfl | rfl | rfl | rfl)
    · exact (center edgeGroup).one_mem
    · exact eH_mem_center
    · exact aH_mem_center
    · exact (center edgeGroup).mul_mem eH_mem_center aH_mem_center

theorem card_centralizer_y :
    Nat.card
    (centralizer {yH} : Subgroup edgeGroup) = 128 := by
  set P : ℕ → Bool := fun j => commutesA 276 hList[j]! yArr
  have hset : ((centralizer {yH} : Subgroup edgeGroup) : Set edgeGroup) =
      eltH '' ((Finset.range 4608).filter fun j => P j = true : Finset ℕ) := by
    ext x
    simp only [SetLike.mem_coe, mem_centralizer_singleton_iff, Set.mem_image, Finset.coe_filter,
      Finset.mem_range, Set.mem_ofPred_eq]
    constructor
    · intro h
      obtain ⟨j, hj, rfl⟩ := exists_eltH x
      exact ⟨j, ⟨hj, (commutesA_iff (rep_eltH hj) rep_yH).2 h⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hP⟩, rfl⟩
      exact (commutesA_iff (rep_eltH hj) rep_yH).1 hP
  have hinj : Set.InjOn eltH ((Finset.range 4608).filter fun j => P j = true : Finset ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
    exact eltH_injOn hi.1 hj.1 hij
  show Nat.card ((centralizer {yH} : Subgroup edgeGroup) : Set edgeGroup) = 128
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, Set.ncard_coe_finset, card_filter_range]
  exact fact_check.2.2.2.2.2.2.2.1

theorem psi_cH :
    psi cH = cH :=
  perm_injective (by rw [perm_psi, perm_cH, sP_inv, sP_facts.2.2.2.2.2.1, mul_assoc, sP_mul_self,
    mul_one])

theorem psi_yH :
    psi yH = yH := by
  have ha : ∀ g : edgeGroup, g * aH = aH * g := fun g => mem_center_iff.1 aH_mem_center g
  have he : ∀ g : edgeGroup, g * eH = eH * g := fun g => mem_center_iff.1 eH_mem_center g
  rw [yH, map_mul, map_mul, psi_aH, psi_cH, psi_eH, ← he cH, mul_assoc, ← he aH, ← mul_assoc,
    ha cH]

theorem psi_edge :
    ∀ p ∈ edgePairs,
    ∃ x : edgeGroup, (x : co3M) = mWord p.1 ∧ (psi x : co3M) = mWord p.2 := by
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hp
  have hmem := mWord_edgeFirst_mem k
  rw [edgeFirst, List.getD_eq_getElem _ _ hk] at hmem
  refine ⟨⟨_, hmem⟩, rfl, ?_⟩
  apply Subtype.ext
  have hl := edgePairs_letters _ (List.getElem_mem hk)
  have h := fact_check.2.2.2.2.2.2.2.2.1 k hk
  rw [List.getD_eq_getElem _ _ hk] at h
  rw [show (((psi ⟨_, hmem⟩ : edgeGroup) : co3M) : Equiv.Perm (Fin 276)) =
    sP * (((mWord edgePairs[k].1 : co3M)) : Equiv.Perm (Fin 276)) * sP from by
      rw [coe_psi, sP_inv], mul_assoc]
  exact eq_of_eqA (rep_compA rep_g3 (rep_compA (rep_mWord hl.1) rep_g3)) (rep_mWord hl.2) h

theorem bcbM_mul_self :
    bcbM * bcbM =
    1 :=
  Subtype.ext (by
    rw [coe_mul, coe_one]
    exact eq_of_eqA (rep_compA rep_bcb rep_bcb) rep_idA fact_check.2.2.2.2.2.2.2.2.2.1)

theorem bcbM_inv :
    bcbM⁻¹ = bcbM :=
    inv_eq_of_mul_eq_one_right
    bcbM_mul_self

theorem bcb_facts :
    bcbM * bcbM = 1 ∧
    bcbM * ma * bcbM⁻¹ = yM ∧ bcbM
    * yM * bcbM⁻¹ = ma ∧
    bcbM * mc * bcbM⁻¹ = mc := by
  have c := fact_check.2.2.2.2.2.2.2.2.2.2
  refine ⟨bcbM_mul_self, ?_, ?_, ?_⟩ <;> rw [bcbM_inv] <;> apply Subtype.ext <;>
    rw [coe_mul, coe_mul, mul_assoc]
  · exact eq_of_eqA (rep_compA rep_bcb (rep_compA (coe_ma ▸ rep_g0) rep_bcb)) rep_yM c.1
  · rw [coe_ma]
    exact eq_of_eqA (rep_compA rep_bcb (rep_compA rep_yM rep_bcb)) rep_g0 c.2.1
  · rw [coe_mc]
    exact eq_of_eqA (rep_compA rep_bcb (rep_compA rep_g2 rep_bcb)) rep_g2 c.2.2.1

theorem kp_facts :
    kpM ∈ edgeGroup ∧
    kpM * yM = yM * kpM ∧ kpM * kpM
    = 1 ∧ kpM ≠ 1 ∧
    ((bcbM : Equiv.Perm (Fin 276)) * sP) ^ 3 = (kpM : Equiv.Perm (Fin 276)) := by
  have c := fact_check.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, fun h => ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [coe_mul, coe_mul, coe_ma]
    exact eq_of_eqA (rep_compA rep_kp rep_g0) (rep_compA rep_g0 rep_kp) c.1
  · apply Subtype.ext
    rw [coe_mul, coe_mul]
    exact eq_of_eqA (rep_compA rep_kp rep_yM) (rep_compA rep_yM rep_kp) c.2.1
  · apply Subtype.ext
    rw [coe_mul, coe_one]
    exact eq_of_eqA (rep_compA rep_kp rep_kp) rep_idA c.2.2.1
  · have h1 := congrArg Subtype.val h
    rw [coe_one] at h1
    have h' := (eqA_iff rep_kp rep_idA).2 h1
    rw [c.2.2.2.1] at h'
    exact Bool.false_ne_true h'
  · have hu : Rep 276 uArr ((bcbM : Equiv.Perm (Fin 276)) * sP) := rep_compA rep_bcb rep_g3
    rw [pow_three]
    exact eq_of_eqA (rep_compA hu (rep_compA hu hu)) rep_kp c.2.2.2.2.1

theorem classA_facts :
    Nat.card classA = 630 ∧ me * ma ∈ classA ∧ yM
    ∈ classA := by
  refine ⟨card_edgeGroup_classA.2, ?_, isConj_iff.2 ⟨bcbM, bcb_facts.2.1⟩⟩
  obtain ⟨j, hj, h⟩ := List.any_eq_true.1 fact_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [List.mem_range] at hj
  have e : (conjM j)⁻¹ * ma * conjM j = me * ma :=
    Subtype.ext (eq_of_eqA (rep_conjM hj) rep_eaM h)
  exact isConj_iff.2 ⟨(conjM j)⁻¹, by rw [inv_inv, e]⟩

theorem modelFacts :
    ModelFacts where
  relsV_perm := relsV_perm
  relsC0_M := relsC0_M
  sP_facts := sP_facts
  involutions := involutions
  card_edgeGroup := card_edgeGroup
  edgeGroup_eq_closure := edgeGroup_eq_closure
  center_edgeGroup := center_edgeGroup
  card_centralizer_y := ⟨card_centralizer_y, comm_y_iff⟩
  psi_facts := ⟨psi_eH, psi_aH, psi_cH, psi_yH, psiFun_psiFun, psi_edge⟩
  bcb_facts := bcb_facts
  kp_facts := kp_facts
  classA_facts := classA_facts

end CFSG.EvenSmallLie.SympSix.Co3Ident
