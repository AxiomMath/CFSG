module

public import CFSG.LargeExtraspecial.S63CD4A
public import CFSG.LargeExtraspecial.S63CD4B
public import CFSG.LargeExtraspecial.S63DSchurAt

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2 (allLt_spec)

theorem false_of_witness {H : Type*} [Group H] {t : H} (P : Set H) (Z : Finset H)
    (hZ8 : Z.card ≤ 8)
    (hP : ∀ N : Subgroup H, N ≤ centralizer ({t} : Set H) →
      (∀ c ∈ centralizer ({t} : Set H), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → IsPGroup 2 N →
        ∀ n ∈ N, n ∈ P)
    (hZc : ∀ y ∈ Z, ∀ x ∈ P, x * y = y * x)
    (hw : ∀ x ∈ P, x ∉ Z → ∃ c ∈ centralizer ({t} : Set H),
      x⁻¹ * c⁻¹ * x * c ∈ Z ∧ x⁻¹ * c⁻¹ * x * c ≠ 1 ∧ x⁻¹ * c⁻¹ * x * c ≠ t)
    {N : Subgroup H} (hN : AdmAt t N) : False := by
  have hNP := hP N hN.le_centralizer hN.conj_mem hN.isPGroup
  obtain ⟨x, hxN, hxZ⟩ : ∃ x ∈ N, x ∉ Z := by
    by_contra hne
    push Not at hne
    have := card_le_of_forall_mem N Z hne
    have := hN.card
    omega
  obtain ⟨c, hc, hwZ, hw1, hwt⟩ := hw x (hNP x hxN) hxZ
  have hcN : c⁻¹ * x * c⁻¹⁻¹ ∈ N := hN.conj_mem _ (inv_mem hc) x hxN
  have hwN : x⁻¹ * c⁻¹ * x * c ∈ N := by
    rw [show x⁻¹ * c⁻¹ * x * c = x⁻¹ * (c⁻¹ * x * c⁻¹⁻¹) by group]
    exact N.mul_mem (N.inv_mem hxN) hcN
  rcases hN.center_le _ hwN (fun m hm => (hZc _ hwZ m (hNP m hm)).symm) with h | h
  · exact hw1 h
  · exact hwt h

theorem false_of_admAt_d4t {N : Subgroup trialityGroup8} (hN : AdmAt d4t N) : False := by
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
  refine false_of_witness {x | ∃ i ∈ P2, RepE d4E D.El[i]! x} (Zl.map el).toFinset
    ((List.toFinset_card_le _).trans (by rw [List.length_map]; exact h7)) ?_ ?_ ?_ hN
  ·
    intro M hMC hMn hM2 n hn
    have h2elt : ∀ m ∈ M, m ^ 4096 = 1 := by
      intro m hm
      obtain ⟨a, ha⟩ := hM2 ⟨m, hm⟩
      exact pow_4096_eq_one (k := a) (by simpa using congrArg Subtype.val ha)
    obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK cGens_hyp h3 (centralizer_d4t_le (hMC hn))
    rw [h4] at hi
    obtain ⟨hic, hrc'⟩ := repE_inv_of_invOK (fun i hi => ⟨el i, hel i hi, hrel i hi⟩) h5 h6
      (hrel c3 h6)
    have hc : el c3 ∈ centralizer ({d4t} : Set trialityGroup8) := d4C_le_centralizer (hel c3 h6)
    have hm : n * (el c3 * n * (el c3)⁻¹) ∈ M := M.mul_mem hn (hMn _ hc n hn)
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

theorem eq_d4Q_of_admAt_d4z {N : Subgroup trialityGroup8} (hN : AdmAt d4z N) : N = d4Q := by
  classical
  have hNQ : N ≤ d4Q := le_of_semidirect (fun _ hc => exists_of_mem_centralizer_d4z hc)
    d4L_normalizes (fun _ hx hx' => eq_one_of_mem_d4Q_d4L hx hx') d4L_core d4L_le_centralizer
    hN.le_centralizer hN.conj_mem hN.isPGroup
  refine le_antisymm hNQ (d4Q_irred N hNQ (fun l hl n hn => hN.conj_mem l (d4L_le_centralizer hl)
    n hn) hN.mem ?_)
  by_contra hne
  push Not at hne
  have := card_le_of_forall_mem N {1, d4z} fun m hm => by
    by_cases h1 : m = 1
    · simp [h1]
    · simp [hne m hm h1]
  have h2 : ({1, d4z} : Finset trialityGroup8).card ≤ 2 := Finset.card_le_two
  have := hN.card
  omega

end CFSG.LargeExtraspecial.S63
