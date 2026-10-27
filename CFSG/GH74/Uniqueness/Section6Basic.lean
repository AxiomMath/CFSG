module

public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem commutator_mem_invertedSet {W : Subgroup X} {z : X} (hz : orderOf z = 2)
    (hzW : z ∈ normalizer (W : Set X)) {w : X} (hw : w ∈ W) :
    z * w * z⁻¹ * w⁻¹ ∈ CFSG.OddInversion.invertedSet W z := by
  have h := CFSG.OddInversion.invertedSet_inv
    (CFSG.OddInversion.mul_conj_inv_mem_invertedSet hz hzW hw)
  have e : (w * (z * w * z⁻¹)⁻¹)⁻¹ = z * w * z⁻¹ * w⁻¹ := by group
  rwa [e] at h

omit [Finite X] in
theorem closure_invertedSet_eq_commutator {W : Subgroup X} {z : X} (hz : orderOf z = 2)
    (hW : Odd (Nat.card W)) (hzW : z ∈ normalizer (W : Set X)) :
    Subgroup.closure (CFSG.OddInversion.invertedSet W z) = ⁅zpowers z, W⁆ := by
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro d hd
    obtain ⟨e, he, rfl⟩ := CFSG.OddInversion.exists_sq_eq_of_mem_invertedSet hW hd
    have hcomm : e ^ 2 = z * e⁻¹ * z⁻¹ * e⁻¹⁻¹ := by
      have h1 : z * e⁻¹ * z⁻¹ = (z * e * z⁻¹)⁻¹ := by group
      rw [h1, he.2, inv_inv, sq]
    rw [SetLike.mem_coe, hcomm, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) (W.inv_mem he.1)
  · rw [Subgroup.commutator_le]
    intro g hg k hk
    rcases eq_one_or_eq_of_mem_zpowers hzz hg with rfl | rfl
    · simp
    · rw [commutatorElement_def]
      exact Subgroup.subset_closure (commutator_mem_invertedSet hz hzW hk)

omit [Finite X] in
theorem commutator_mem_closure_invertedSet {W : Subgroup X} {z : X} (hz : orderOf z = 2)
    (hW : Odd (Nat.card W)) (hzW : z ∈ normalizer (W : Set X)) {w : X} (hw : w ∈ W) :
    z * w * z⁻¹ * w⁻¹ ∈ Subgroup.closure (CFSG.OddInversion.invertedSet W z) := by
  rw [closure_invertedSet_eq_commutator hz hW hzW, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) hw

theorem T4Cand.odd_card {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) :
    Odd (Nat.card W) := by
  have : Fact p.Prime := ⟨hW.prime⟩
  obtain ⟨n, hn⟩ := hW.pgroup.exists_card_eq
  rw [hn]
  exact (hW.prime.odd_of_ne_two hW.ne_two).pow

omit [Finite X] in
theorem T4Cand.exists_ne_base {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) :
    ∃ β ∈ omegaFix M (W : Set X), β ≠ M := by
  have h1 : 1 < (omegaFix M (W : Set X)).ncard := hW.two_le
  obtain ⟨a, b, ha, hb, hab⟩ :=
    (Set.one_lt_ncard_iff (Set.finite_of_ncard_pos (by omega))).mp h1
  by_cases haM : a = M
  · exact ⟨b, hb, fun hbM => hab (haM.trans hbM.symm)⟩
  · exact ⟨a, ha, haM⟩

omit [Finite X] in
theorem T4Cand.self_mem_omegaFix {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) :
    M ∈ omegaFix M (W : Set X) :=
  ⟨self_mem_omega M, fun _ hg =>
    conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hW.le_M hg))⟩

omit [Finite X] in
theorem T4Cand.conjugate_z_mem_omegaFix {z : X} {p : ℕ} {W : Subgroup X}
    (hW : T4Cand Z M z p W) {β : Subgroup X} (hβ : β ∈ omegaFix M (W : Set X)) :
    conjugate β z ∈ omegaFix M (W : Set X) :=
  conjugate_mem_omegaFix_of_mem_normalizer hW.normalizes hβ

theorem T4Cand.closure_invertedSet (hZ : IsInvariantInvolutionSet Z) {z : X} {p : ℕ}
    {W : Subgroup X} (hW : T4Cand Z M z p W) :
    Subgroup.closure (CFSG.OddInversion.invertedSet W z) = W := by
  rw [closure_invertedSet_eq_commutator (hZ.1 z hW.mem_Z) hW.odd_card hW.normalizes, hW.comm_eq]

theorem T4Cand.omegaFix_invertedSet (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) :
    omegaFix M (CFSG.OddInversion.invertedSet W z) = omegaFix M (W : Set X) := by
  refine Set.Subset.antisymm ?_ (omegaFix_anti fun g hg => hg.1)
  rintro β ⟨hβ, hfix⟩
  rw [h.mem_omegaFix_iff]
  refine ⟨hβ, ?_⟩
  rw [← hW.closure_invertedSet hZ, Subgroup.closure_le]
  exact fun g hg => (h.conjugate_eq_iff_mem hβ).mp (hfix g hg)

theorem T4Cand.one_lt_card_invertedSet (hZ : IsInvariantInvolutionSet Z) {z : X} {p : ℕ}
    {W : Subgroup X} (hW : T4Cand Z M z p W) :
    1 < Nat.card (CFSG.OddInversion.invertedSet W z) := by
  have hk : ∃ k ∈ CFSG.OddInversion.invertedSet W z, k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine hW.ne_bot ?_
    rw [← hW.closure_invertedSet hZ, Subgroup.closure_eq_bot_iff]
    exact fun k hk => hcon k hk
  obtain ⟨k, hkI, hk1⟩ := hk
  have h1 : (1 : X) ∈ CFSG.OddInversion.invertedSet W z := ⟨W.one_mem, by simp⟩
  rw [Nat.card_coe_set_eq]
  exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨1, k, h1, hkI, fun h => hk1 h.symm⟩

theorem T4Cand.card_invertedSet_le (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) :
    Nat.card (CFSG.OddInversion.invertedSet W z) ≤ zNumShare Z M p := by
  obtain ⟨β, hβ, hβM⟩ := hW.exists_ne_base
  obtain ⟨hβΩ, hWβ⟩ := h.mem_omegaFix_iff.mp hβ
  exact (h.prop38b hZ hW.mem_Z hW.mem_M hβΩ hβM hW.prime hW.ne_two (le_inf hW.le_M hWβ)
    hW.pgroup hW.normalizes).1

theorem T4Cand.two_le_zNumShare (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M)
    {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) : 2 ≤ zNumShare Z M p :=
  (hW.one_lt_card_invertedSet hZ).trans_le (hW.card_invertedSet_le hZ h)

end CFSG.GH74.Uniqueness
