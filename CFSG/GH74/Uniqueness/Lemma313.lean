module

public import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting
public import CFSG.GH74.Uniqueness.Lemma31gh
public import CFSG.GH74.Uniqueness.Lemma33b

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Isolated

variable {X : Type} [Group X] [Finite X] {Z : Set X}

theorem IsInvariantInvolutionSet.isConj_of_isolated (hZ : IsInvariantInvolutionSet Z) {z : X}
    (hz : z ∈ Z) (hiso : ∀ y ∈ Z, y * z = z * y → y = z) {a : X} (ha : a ∈ Z) : IsConj a z := by
  have hz2 := hZ.mul_self_eq_one hz
  have ha2 := hZ.mul_self_eq_one ha
  have hodd : Odd (orderOf (z * a)) := by
    by_contra hnot
    have heven : Even (orderOf (z * a)) := Nat.not_odd_iff_even.mp hnot
    obtain ⟨m, hm⟩ := heven
    have hmpos : 0 < m := by
      have := orderOf_pos (z * a)
      omega
    obtain ⟨hv2, hv1, hzv, -, x, -, hx⟩ := dihedral_even hz2 ha2 hmpos (by rw [hm]; ring)
    set v := (z * a) ^ m with hv
    have hzvZ : z * v ∈ Z := by
      rcases hx with h1 | h1
      · rw [← h1]
        exact hZ.2 z hz x
      · rw [← h1]
        exact hZ.2 a ha x
    have hcomm : (z * v) * z = z * (z * v) := by
      calc (z * v) * z = z * (v * z) := by rw [mul_assoc]
        _ = z * (z * v) := by rw [← hzv]
    have heq := hiso (z * v) hzvZ hcomm
    exact hv1 (by simpa using heq)
  obtain ⟨x, -, hx⟩ := exists_mem_closure_conj_of_odd hz2 ha2 hodd
  exact isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]; exact hx⟩

theorem twoRank_le_one_of_isolated_gen (hZ : IsInvariantInvolutionSet Z)
    (hgen : Subgroup.closure Z = ⊤) {z : X} (hz : z ∈ Z)
    (hiso : ∀ y ∈ Z, y * z = z * y → y = z) : Open.twoRank X ≤ 1 :=
  twoRank_le_one_of_isolated hZ hgen hz (fun _ ha => hZ.isConj_of_isolated hz hiso ha) hiso

end Isolated

section Lemma313

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.le_of_odd_normalizer (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {Y : Subgroup X} (hY : Odd (Nat.card Y))
    (hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer (Y : Set X)))) {z : X} (hz : z ∈ Z)
    (hzM : z ∈ M) (hzY : z ∈ normalizer (Y : Set X)) : Y ≤ M := by
  have hz2 := hZ.mul_self_eq_one hz
  by_cases hcase : ∃ y ∈ Z, y ∈ normalizer (Y : Set X) ∧ y ≠ z ∧ y * z = z * y
  ·
    obtain ⟨y, hy, hyN, hne, hyz⟩ := hcase
    have hy2 : y * y = 1 := hZ.mul_self_eq_one hy
    have hyM : y ∈ M := h.centralizer_le_of_mem hz hzM
      (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
    have hy1 : y ≠ 1 := fun h1 => by
      have := hZ.1 y hy
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    have hz1 : z ≠ 1 := fun h1 => by
      have := hZ.1 z hz
      rw [h1, orderOf_one] at this
      exact absurd this (by norm_num)
    obtain ⟨V, hVmem, hVle, -, hVcard⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.FourGroup.exists_kleinFour hy2 hz2 hyz hy1 hz1 hne
    have hVN : V ≤ normalizer (Y : Set X) := hVle _ hyN hzY
    have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
      intro v hv
      rcases hVmem v hv with h1 | h1 | h1 | h1 <;> rw [h1]
      · exact one_pow 2
      · rw [pow_two]; exact hy2
      · rw [pow_two]; exact hz2
      · rw [(show Commute y z from hyz).mul_pow, pow_two y, hy2, pow_two z, hz2, one_mul]
    have hcomplement : ¬ 2 ∣ Nat.card Y := fun h2 =>
      (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h2)
    have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      2 Nat.prime_two V Y (fun m => Subtype.ext (by simpa using hsq m m.2))
      (by rw [hVcard]; norm_num) hcomplement hVN
    conv_lhs => rw [hgen]
    refine iSup₂_le fun v hv1 => ?_
    have hv := hVmem (v : X) v.2
    have hv1' : (v : X) ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
    refine inf_le_right.trans ?_
    rcases hv with h1 | h1 | h1 | h1
    · exact absurd h1 hv1'
    · rw [h1]
      exact h.centralizer_le_of_mem hy hyM
    · rw [h1]
      exact h.centralizer_le_of_mem hz hzM
    · rw [h1]
      have hyz1 : y * z ≠ 1 := fun h1 => hne (by
        have := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact inv_eq_of_mul_eq_one_right hz2)
      have hord : orderOf (y * z) = 2 := by
        refine orderOf_eq_prime ?_ hyz1
        rw [(show Commute y z from hyz).mul_pow, pow_two y, hy2, pow_two z, hz2, one_mul]
      exact h.2.2.2 (y * z) ⟨hord, y, hy, z, hz, hyz, rfl⟩ (M.mul_mem hyM hzM)
  ·
    push Not at hcase
    exfalso
    set N := zHull Z (normalizer (Y : Set X)) with hN
    have hNle : N ≤ normalizer (Y : Set X) := Subgroup.closure_le _ |>.mpr Set.inter_subset_right
    have hzN : z ∈ N := Subgroup.subset_closure ⟨hz, hzY⟩
    have hZ' : IsInvariantInvolutionSet {l : N | (l : X) ∈ Z} := hZ.restrict N
    have hgen' : Subgroup.closure {l : N | (l : X) ∈ Z} = ⊤ := by
      have e : {l : N | (l : X) ∈ Z} =
          (Subtype.val : N → X) ⁻¹' (Z ∩ ((normalizer (Y : Set X) : Subgroup X) : Set X)) := by
        ext l
        exact ⟨fun hl => ⟨hl, hNle l.2⟩, fun hl => hl.1⟩
      rw [e]
      exact Subgroup.closure_closure_coe_preimage
    have hiso : ∀ y' ∈ {l : N | (l : X) ∈ Z}, y' * ⟨z, hzN⟩ = ⟨z, hzN⟩ * y' → y' = ⟨z, hzN⟩ := by
      intro y' hy' hcomm
      by_contra hne
      exact hcase (y' : X) hy' (hNle y'.2) (fun h1 => hne (Subtype.ext h1))
        (congrArg Subtype.val hcomm)
    have hr1 := twoRank_le_one_of_isolated_gen hZ' hgen' (z := ⟨z, hzN⟩) hz hiso
    have hr2 : Open.pRank 2 (⊤ : Subgroup N) = Open.pRank 2 N :=
      CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 2 Nat.prime_two N
    have : Open.twoRank N = Open.pRank 2 N := hr2
    omega

theorem IsProductDisconnected.lemma313 (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {Y : Subgroup X} (hY : Odd (Nat.card Y))
    (hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer (Y : Set X)))) {s : X} (hs : s ∈ Z)
    (hsY : s ∈ normalizer (Y : Set X)) {β : Subgroup X} (hβ : β ∈ omega M)
    (hsβ : conjugate β s = β) : ∀ y ∈ Y, conjugate β y = β := by
  obtain ⟨g, rfl⟩ := hβ
  have hsM : s ∈ conjugate M g := (h.conjugate_eq_iff_mem ⟨g, rfl⟩).mp hsβ
  have hYβ := (h.conjugate_point hZ g).le_of_odd_normalizer hZ hY hrank hs hsM hsY
  intro y hy
  exact (h.conjugate_eq_iff_mem ⟨g, rfl⟩).mpr (hYβ hy)

theorem IsProductDisconnected.lemma313_le (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {Y : Subgroup X} (hY : Odd (Nat.card Y))
    (hrank : 2 ≤ Open.pRank 2 (zHull Z (normalizer (Y : Set X)))) {s : X} (hs : s ∈ Z)
    (hsY : s ∈ normalizer (Y : Set X)) {β : Subgroup X} (hβ : β ∈ omega M)
    (hsβ : conjugate β s = β) : Y ≤ β :=
  fun y hy => (h.conjugate_eq_iff_mem hβ).mp (h.lemma313 hZ hY hrank hs hsY hβ hsβ y hy)

end Lemma313

end CFSG.GH74.Uniqueness
