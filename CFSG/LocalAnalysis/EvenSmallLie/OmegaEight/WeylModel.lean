module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables

public noncomputable section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover

section Arrays

variable {n : ℕ}

theorem isInvA_spec' {t : Array ℕ} (h : isInvA n t t = true) :
    Rep n t (permOfArr n t) ∧ permOfArr n t * permOfArr n t = 1 := by
  obtain ⟨h1, h2⟩ := rep_permOfArr h
  refine ⟨h1, ?_⟩
  have := h1.unique h2
  calc permOfArr n t * permOfArr n t = permOfArr n t * (permOfArr n t)⁻¹ := by
        rw [← this]
    _ = 1 := mul_inv_cancel _

theorem countP_range_eq_card' (p : ℕ → Bool) :
    (List.range n).countP p = ((Finset.range n).filter fun i => p i = true).card := by
  rw [Finset.card_filter]
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp [List.countP_cons]

@[expose] def fixCard' (x : Equiv.Perm (Fin n)) : ℕ := (Finset.univ.filter fun q => x q = q).card

theorem fixCard'_eq_countP {t : Array ℕ} {x : Equiv.Perm (Fin n)} (h : Rep n t x) :
    fixCard' x = fixCount n t := by
  rw [fixCount, countP_range_eq_card', fixCard', ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply, Finset.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, ?_⟩
    rw [h q, hq]
  · rintro ⟨hi, hti⟩
    refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
    rw [← h ⟨i, hi⟩]
    exact hti

theorem card_fixedPoints_eq' (x : Equiv.Perm (Fin n)) :
    Fintype.card (Function.fixedPoints x) = fixCard' x := by
  rw [fixCard', ← Fintype.card_subtype]
  rfl

theorem card_fixedPoints_of_rep {t : Array ℕ} {x : Equiv.Perm (Fin n)} (h : Rep n t x) :
    Fintype.card (Function.fixedPoints x) = fixCount n t := by
  rw [card_fixedPoints_eq', fixCard'_eq_countP h]

theorem sign_of_isInvA {t : Array ℕ} (h : isInvA n t t = true) :
    Equiv.Perm.sign (permOfArr n t) = (-1) ^ ((n - fixCount n t) / 2) := by
  obtain ⟨hrep, hsq⟩ := isInvA_spec' h
  have h2 : permOfArr n t ^ 2 = 1 := by rw [sq, hsq]
  rw [Equiv.Perm.sign_of_pow_two_eq_one h2, card_fixedPoints_of_rep hrep, Fintype.card_fin]

end Arrays

theorem reflS_size : reflS.size = 120 := by simp [reflS, posRoots]

theorem wS_size : wS.size = 13 := by simp [wS, sgsRoots]

@[expose] def wQ : RawSchreierDatum 240 :=
  RawSchreierDatum.ofArrays 240 (by norm_num) wS 13 (by rw [wS_size]) wBase (by decide) wWords

theorem wChain_ok :
    (rawChainOK 240 (wS.extract 0 13) wS (wBase.map Fin.val).toArray wWords 4 = true ∧
      rawOrbitSizes 240 wS (wBase.map Fin.val).toArray = [240, 126, 60, 2, 24, 2, 2, 2]) ∧
      ∀ r < 240, siftA 240 (rawLevels 240 wS (wBase.map Fin.val).toArray)
        (wBase.map Fin.val).toArray 0 (reflArr r) = true := by
  have h := wChain_check
  simp only [wChainCheck, Bool.and_eq_true, beq_iff_eq, allLt_iff] at h
  exact h

theorem card_wQ : Nat.card wQ.originalSubgroup = 696729600 := by
  rw [wQ, ofArrays_card (by norm_num) wChain_ok.1.1, wChain_ok.1.2]
  rfl

theorem mem_wQ_iff {g : Array ℕ} {G : Equiv.Perm (Fin 240)} (hG : Rep 240 g G) :
    siftA 240 (rawLevels 240 wS (wBase.map Fin.val).toArray) (wBase.map Fin.val).toArray 0 g =
      true ↔ G ∈ wQ.originalSubgroup :=
  ofArrays_mem_iff (by norm_num) wChain_ok.1.1 hG

structure ReflFacts : Prop where
  inv : ∀ r < 240, isInvA 240 (reflArr r) (reflArr r) = true
  fix : ∀ r < 240, fixCount 240 (reflArr r) = 126
  neg_lt : ∀ r < 240, negArr[r]! < 240
  neg : ∀ r < 240, eqA 240 (reflArr negArr[r]!) (reflArr r) = true
  pos : ∀ r < 240, ∃ i < 120, eqA 240 (reflArr r) reflS[i]! = true
  zinv : isInvA 240 negArr negArr = true
  zfix : fixCount 240 negArr = 0
  zcomm : ∀ r < 240, eqA 240 (compA 240 negArr (reflArr r)) (compA 240 (reflArr r) negArr) = true

theorem refl_facts : ReflFacts := by
  have h := refl_check
  simp only [reflCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, decide_eq_true_eq,
    List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨fun r hr => (h1 r hr).1.1.1.1, fun r hr => (h1 r hr).1.1.1.2, fun r hr => (h1 r hr).1.1.2,
    fun r hr => (h1 r hr).1.2, fun r hr => (h1 r hr).2, h2, h3, h4⟩

theorem rep_refl {r : ℕ} (hr : r < 240) : Rep 240 (reflArr r) (refl r) :=
  (isInvA_spec' (refl_facts.inv r hr)).1

theorem refl_mul_self {r : ℕ} (hr : r < 240) : refl r * refl r = 1 :=
  (isInvA_spec' (refl_facts.inv r hr)).2

theorem refl_inv {r : ℕ} (hr : r < 240) : (refl r)⁻¹ = refl r :=
  inv_eq_of_mul_eq_one_right (refl_mul_self hr)

theorem sign_refl {r : ℕ} (hr : r < 240) : Equiv.Perm.sign (refl r) = -1 := by
  rw [refl, sign_of_isInvA (refl_facts.inv r hr), refl_facts.fix r hr]
  decide

theorem reflS_getElem! {i : ℕ} (hi : i < 120) : reflS[i]! = reflArr (posRoots.getD i 0) := by
  rw [reflS, getElem!_pos _ i (by simpa [posRoots] using hi)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa [posRoots] using hi)]

theorem posRoots_lt {i : ℕ} (hi : i < 120) : posRoots.getD i 0 < 240 := by
  interval_cases i <;> decide

theorem wS_getElem! {i : ℕ} (hi : i < 13) : wS[i]! = reflArr (sgsRoots.getD i 0) := by
  rw [wS, getElem!_pos _ i (by simpa [sgsRoots] using hi)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa [sgsRoots] using hi)]

theorem sgsRoots_lt {i : ℕ} (hi : i < 13) : sgsRoots.getD i 0 < 240 := by
  interval_cases i <;> decide

theorem refl_eq_of_eqA {r s : ℕ} (hr : r < 240) (hs : s < 240)
    (h : eqA 240 (reflArr r) (reflArr s) = true) : refl r = refl s :=
  eq_of_eqA (rep_refl hr) (rep_refl hs) h

theorem wE8_eq : wE8 = wQ.originalSubgroup := by
  rw [wQ, ofArrays_originalSubgroup, wE8]
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨r, hr, rfl⟩
    have h := (mem_wQ_iff (rep_refl hr)).1 (wChain_ok.2 r hr)
    rwa [wQ, ofArrays_originalSubgroup] at h
  · rw [closure_le]
    rintro _ ⟨i, hi, rfl⟩
    refine subset_closure ⟨sgsRoots.getD i 0, sgsRoots_lt hi, ?_⟩
    rw [wS_getElem! hi]
    rfl

theorem card_wE8 : Nat.card wE8 = 696729600 := by
  rw [wE8_eq, card_wQ]

theorem refl_mem {r : ℕ} (hr : r < 240) : refl r ∈ wE8 := subset_closure ⟨r, hr, rfl⟩

theorem mem_wE8_of_siftA {g : Array ℕ} {G : Equiv.Perm (Fin 240)} (hG : Rep 240 g G)
    (h : siftA 240 (rawLevels 240 wS (wBase.map Fin.val).toArray) (wBase.map Fin.val).toArray 0
      g = true) : G ∈ wE8 := by
  rw [wE8_eq]
  exact (mem_wQ_iff hG).1 h

theorem wE8_induction {P : Equiv.Perm (Fin 240) → Prop} (h1 : P 1)
    (hmul : ∀ r < 240, ∀ g, P g → P (refl r * g)) : ∀ g ∈ wE8, P g := by
  intro g hg
  refine closure_induction_left (p := fun g _ => P g) h1 ?_ ?_ hg
  · rintro _ ⟨r, hr, rfl⟩ g _ hg
    exact hmul r hr g hg
  · rintro _ ⟨r, hr, rfl⟩ g _ hg
    rw [refl_inv hr]
    exact hmul r hr g hg
