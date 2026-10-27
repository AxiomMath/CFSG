module

public import CFSG.LargeExtraspecial.S63CD4Class
public import CFSG.LargeExtraspecial.S63CD4At
public import Certificates.Certificate21113

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2 (allLt_spec)

theorem d4BCheck_eq_true : d4BCheck = true := Certificates.certificate21113

theorem parts_of_d4BCheckOn {D : EnumData} {c3 : ℕ} {P2 Z : List ℕ}
    (h : d4BCheckOn D c3 P2 Z = true) :
    gensOK cGens = true ∧ (∀ k < cGens.size, mulR cGens[k]! t0R = mulR t0R cGens[k]!) ∧
    enumOK cGens D.El D.P D.K D.idx = true ∧ D.El.size = 3072 ∧ D.invOK 3072 = true ∧
    c3 < 3072 ∧ Z.length ≤ 8 ∧
    ∀ i ∈ P2, (Z.contains i || (List.range 3072).any fun c =>
      Z.any (fun j => D.El[j]! == commI D.El[i]! D.El[D.inv[i]!]! D.El[c]! D.El[D.inv[c]!]!) &&
        !(commI D.El[i]! D.El[D.inv[i]!]! D.El[c]! D.El[D.inv[c]!]! == oneR) &&
        !(commI D.El[i]! D.El[D.inv[i]!]! D.El[c]! D.El[D.inv[c]!]! == t0R)) = true := by
  simp only [d4BCheckOn, EnumData.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, fun k hk => ?_, h3, h4, h5, h6, h7, fun i hi => List.all_eq_true.1 h8 i hi⟩
  simpa using allLt_spec h2 hk


theorem exists_d4BCheckOn :
    ∃ D c3, d4BCheckOn D c3 (twoSet D c3) (zSet D (twoSet D c3)) = true :=
  ⟨_, _, d4BCheck_eq_true⟩

theorem cGens_hyp : ∀ k < cGens.size, RepE d4E cGens[k]! (cGH k) ∧ cGH k * cGH k = 1 := by
  obtain ⟨D, c3, h⟩ := exists_d4BCheckOn
  exact mul_self_of_gensOK (fun k hk => repE_cGens hk) (parts_of_d4BCheckOn h).1

@[expose] noncomputable def d4C : Subgroup trialityGroup8 := closure (genSet cGH cGens.size)

theorem d4C_le_centralizer : d4C ≤ centralizer ({d4t} : Set trialityGroup8) := by
  obtain ⟨D, c3, h⟩ := exists_d4BCheckOn
  have h2 := (parts_of_d4BCheckOn h).2.1
  rw [d4C, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  have h1 := repE_mul (cGens_hyp k hk).1 repE_t0R
  rw [h2 k hk] at h1
  exact eq_of_repE d4E_injective h1 (repE_mul repE_t0R (cGens_hyp k hk).1)

theorem card_d4C : Nat.card d4C = 3072 := by
  obtain ⟨D, c3, h⟩ := exists_d4BCheckOn
  obtain ⟨-, -, h3, h4, -⟩ := parts_of_d4BCheckOn h
  rw [d4C, card_of_enumOK d4E_injective cGens_hyp h3, h4]

theorem centralizer_d4t_le :
    centralizer ({d4t} : Set trialityGroup8) ≤ d4C := by
  have : Finite trialityGroup8 := Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
  have heq : d4C = centralizer ({d4t} : Set trialityGroup8) :=
    Subgroup.eq_of_le_of_card_ge d4C_le_centralizer (card_d4C ▸ card_centralizer_d4t_le)
  exact heq.symm.le


theorem d42At_d4t : D42At trialityGroup8 d4t := by
  classical
  obtain ⟨D, c3, h⟩ := exists_d4BCheckOn
  obtain ⟨-, -, h3, h4, h5, h6, h7, h8⟩ := parts_of_d4BCheckOn h
  have hEl : ∀ i < 3072, ∃ a ∈ d4C, RepE d4E D.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (cGens_hyp k hk).1) h3 i (h4 ▸ hi)
  have hv : ∀ i < 3072, validR D.El[i]! = true := fun i hi =>
    ((enumOK_parts h3).2.2 i (h4 ▸ hi)).1
  choose! el hel hrel using hEl
  set P2 := twoSet D c3 with hP2
  set Zl := zSet D P2 with hZl
  have hP2lt : ∀ i ∈ P2, i < 3072 := fun i hi => by
    simp only [hP2, twoSet, List.mem_filter, List.mem_range] at hi
    exact hi.1
  have hZlP : ∀ i ∈ Zl, i ∈ P2 := fun i hi => by
    simp only [hZl, zSet, List.mem_filter] at hi
    exact hi.1
  refine d42At_of_witness {x | ∃ i ∈ P2, RepE d4E D.El[i]! x} (Zl.map el).toFinset
    ((List.toFinset_card_le _).trans (by rw [List.length_map]; exact h7)) ?_ ?_ ?_
  ·
    intro N hNC hNn hN2 n hn
    have h2elt : ∀ m ∈ N, m ^ 4096 = 1 := by
      intro m hm
      obtain ⟨a, ha⟩ := hN2 ⟨m, hm⟩
      exact pow_4096_eq_one (k := a) (by simpa using congrArg Subtype.val ha)
    obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK cGens_hyp h3 (centralizer_d4t_le (hNC hn))
    rw [h4] at hi
    obtain ⟨hic, hrc'⟩ := repE_inv_of_invOK (fun i hi => ⟨el i, hel i hi, hrel i hi⟩) h5 h6
      (hrel c3 h6)
    have hc : el c3 ∈ centralizer ({d4t} : Set trialityGroup8) := d4C_le_centralizer (hel c3 h6)
    have hm : n * (el c3 * n * (el c3)⁻¹) ∈ N := N.mul_mem hn (hNn _ hc n hn)
    have hrm : RepE d4E (mulR D.El[i]! (conjI D.El[c3]! D.El[D.inv[c3]!]! D.El[i]!))
        (n * (el c3 * n * (el c3)⁻¹)) :=
      repE_mul hri (repE_mul (repE_mul (hrel c3 h6) hri) hrc')
    have hvm : validR (mulR D.El[i]! (conjI D.El[c3]! D.El[D.inv[c3]!]! D.El[i]!)) = true :=
      validR_mulR (size_of_validR (hv i hi)) (validR_conjI (size_of_validR (hv c3 h6)) (hv _ hic))
    have ht1 : sq12R D.El[i]! = oneR := by
      have := repE_sq12R hri
      rw [h2elt n hn] at this
      exact (eq_iff_of_repE (validR_sq12R (hv i hi)) validR_oneR this repE_one).2 rfl
    have ht2 : sq12R (mulR D.El[i]! (conjI D.El[c3]! D.El[D.inv[c3]!]! D.El[i]!)) = oneR := by
      have := repE_sq12R hrm
      rw [h2elt _ hm] at this
      exact (eq_iff_of_repE (validR_sq12R hvm) validR_oneR this repE_one).2 rfl
    refine ⟨i, ?_, hri⟩
    simp only [hP2, twoSet, List.mem_filter, List.mem_range, hi, true_and, Bool.and_eq_true,
      beq_iff_eq]
    exact ⟨ht1, ht2⟩
  ·
    intro y hy x ⟨j, hj, hrj⟩
    simp only [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨i, hiZ, rfl⟩ := hy
    have hiZ' := hiZ
    simp only [hZl, zSet, List.mem_filter, List.all_eq_true, beq_iff_eq] at hiZ'
    have hij := hiZ'.2 j hj
    have hi := hP2lt i (hZlP i hiZ)
    have h1 := repE_mul (hrel i hi) hrj
    rw [hij] at h1
    exact (eq_of_repE d4E_injective h1 (repE_mul hrj (hrel i hi))).symm
  ·
    rintro x ⟨i, hi, hri⟩ hxZ
    have hi' := hP2lt i hi
    have h8' := h8 i hi
    have hiZ : ¬ i ∈ Zl := by
      intro hiZ
      apply hxZ
      simp only [List.mem_toFinset, List.mem_map]
      exact ⟨i, hiZ, eq_of_repE d4E_injective (hrel i hi') hri⟩
    simp only [Bool.or_eq_true, List.contains_iff_mem, hiZ, false_or, List.any_eq_true,
      List.mem_range, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at h8'
    obtain ⟨c, hc, ⟨⟨j, hj, hjw⟩, hw1⟩, hwt⟩ := h8'
    obtain ⟨-, hrx'⟩ := repE_inv_of_invOK (fun i hi => ⟨el i, hel i hi, hrel i hi⟩) h5 hi' hri
    obtain ⟨hic, hrc'⟩ := repE_inv_of_invOK (fun i hi => ⟨el i, hel i hi, hrel i hi⟩) h5 hc
      (hrel c hc)
    have hrw : RepE d4E (commI D.El[i]! D.El[D.inv[i]!]! D.El[c]! D.El[D.inv[c]!]!)
        (x⁻¹ * (el c)⁻¹ * x * el c) := by
      have := repE_mul (repE_mul hrx' hrc') (repE_mul hri (hrel c hc))
      rwa [← mul_assoc] at this
    have hvw : validR (commI D.El[i]! D.El[D.inv[i]!]! D.El[c]! D.El[D.inv[c]!]!) = true :=
      validR_commI (size_of_validR (hv _ (invOK_spec h5 hi').1)) (size_of_validR (hv i hi'))
        (hv c hc)
    refine ⟨el c, d4C_le_centralizer (hel c hc), ?_, ?_, ?_⟩
    · simp only [List.mem_toFinset, List.mem_map]
      refine ⟨j, hj, eq_of_repE d4E_injective (hrel j (hP2lt j (hZlP j hj))) ?_⟩
      rw [hjw]
      exact hrw
    · intro h1
      rw [h1] at hrw
      exact hw1 ((eq_iff_of_repE hvw validR_oneR hrw repE_one).2 rfl)
    · intro h1
      rw [h1] at hrw
      exact hwt ((eq_iff_of_repE hvw validR_t0R hrw repE_t0R).2 rfl)

end CFSG.LargeExtraspecial.S63
