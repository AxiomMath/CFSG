module

public import CFSG.ClassicalInvolution.AschTight.S1916Omega3
public import CFSG.ClassicalInvolution.AschTight.S1916Eta
public import CFSG.ClassicalInvolution.AschTight.S1916Quat

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}
  {Y' Q : Subgroup G}

omit [Finite G] in
theorem USet_mono {Ω Ω₁ : Set (Subgroup G)} (h : Ω ⊆ Ω₁) : USet Ω ⊆ USet Ω₁ := by
  rintro U ⟨R, ⟨J, hJ, P, rfl⟩, hUR, hcyc, hidx⟩
  exact ⟨_, ⟨J, h hJ, P, rfl⟩, hUR, hcyc, hidx⟩

theorem eight_le_card_of_yPrimeData (ht : S19R.TightStd p f K z) (hY : YPrimeData K z Y' Q) :
    8 ≤ Nat.card Q := by
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hRmem : (Q₀ : Subgroup ↥K).map K.subtype ∈ RSet (CoreAssembly.conjClass K) :=
    ⟨K, CoreAssembly.mem_conjClass_self K, Q₀, rfl⟩
  rw [← hY.card _ (isSylow2In_map_sylow K Q₀)]
  exact (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hRmem).2

theorem uniqueMember_omegaPrime [IsSimpleGroup G] (ht : S19R.TightStd p f K z)
    (hY : YPrimeData K z Y' Q) :
    ∀ U ∈ USet (omegaPrime K Y'), ∀ J ∈ omegaPrime K Y', ∀ J' ∈ omegaPrime K Y',
      U ≤ J → U ≤ J' → J = J' := by
  intro U hU J hJ J' hJ' hUJ hUJ'
  by_contra hne
  have h1 := ((hypOmegaGen_omegaPrime ht hY).omega4 J hJ J' hJ' hne).1
  obtain ⟨R, hR, hUR, -, hidx⟩ := hU
  obtain ⟨M, hM, hRM⟩ := exists_isSylow2In_of_mem_RSet hR
  have hRcard : Nat.card R = Nat.card Q := natCard_eq_of_isSylow2In_omegaPrime hY hM hRM
  have hQ8 := eight_le_card_of_yPrimeData ht hY
  have hRU : Nat.card R = 2 * Nat.card U := by
    have h2 := Subgroup.relIndex_mul_card (H := U) (K := R)
    rw [hidx, inf_eq_left.mpr hUR] at h2
    exact h2.symm
  have hU2 : IsPGroup 2 U := hRM.2.1.to_le hUR
  obtain ⟨k, hk⟩ := hU2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ 2 ∣ Nat.card ↥(J ⊓ J') :=
    (pow_dvd_pow 2 hk2).trans (hk ▸ Subgroup.card_dvd_of_le (le_inf hUJ hUJ'))
  have := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
  omega

theorem invariant_mem_USet_omegaPrime [IsSimpleGroup G] (ht : S19R.TightStd p f K z)
    (hY : YPrimeData K z Y' Q) (hQq : IsQuaternionSub Q) :
    ∀ M ∈ omegaPrime K Y', ∀ T P : Subgroup G, IsSylow2In T M → IsPGroup 2 P → T ≤ P →
      (∀ q ∈ P, conjSub q T = T) →
        ∃ U ∈ USet (omegaPrime K Y'), U ≤ T ∧ ∀ q ∈ P, conjSub q U = U := by
  intro M hM T P hT hP hTP hTn
  obtain ⟨g, hMg, hzM, -⟩ := exists_data_of_mem_omegaPrime ht hY hM
  rcases hMg with rfl | rfl
  · obtain ⟨U, hU, hUT, hUinv⟩ := exists_invariant_mem_USet ht.branch.odd ht.branch.five
      (hypOmegaMod_of_tightD ht) ⟨g, rfl⟩ hT hP hTP hTn
    exact ⟨U, USet_mono Set.subset_union_left hU, hUT, hUinv⟩
  · have hTcard : Nat.card T = Nat.card Q := natCard_eq_of_isSylow2In_omegaPrime hY hM hT
    have hQ8 := eight_le_card_of_yPrimeData ht hY
    have hzT : IsUniqueInvolution T (g * z * g⁻¹) :=
      ⟨AscL62.mem_of_uniqueInvolution_of_pGroup hzM hT.1 hT.2.1 (by omega), hzM.ne_one, hzM.sq,
        fun y hy hy2 => hzM.unique y (hT.1 hy) hy2⟩
    by_cases h16 : 16 ≤ Nat.card T
    ·
      obtain ⟨c, -, hc⟩ := IsSylow2In.exists_conj (hY.sylow.conj g) hT
      have hTq : IsQuaternionSub T := by
        rw [← hc]
        exact IsQuaternionSub.conjSub' (IsQuaternionSub.conjSub' hQq g) c
      have hTq' := hTq
      obtain ⟨a, b, ha4, hcard, -, -, hcl⟩ := hTq
      have haT : a ∈ T := hcl ▸ Subgroup.subset_closure (by simp)
      set U : Subgroup G := Subgroup.zpowers a with hUdef
      have hUT : U ≤ T := Subgroup.zpowers_le.mpr haT
      have hUcyc : IsCyclic ↥U := Subgroup.isCyclic_zpowers a
      have hUcard : Nat.card T = 2 * Nat.card U := by rw [hUdef, Nat.card_zpowers]; exact hcard
      refine ⟨U, mem_USet_of_natCard hM hT hUT hUcyc hUcard, hUT, fun q hq => ?_⟩
      have hle : conjSub q U ≤ T := by
        have := conjSub_mono (n := q) hUT
        rwa [hTn q hq] at this
      exact (IsQuaternionSub.eq_of_cyclic hTq' h16 hUT hle hUcyc
        (isCyclic_conjSub hUcyc q) hUcard (by rw [natCard_conjSub]; exact hUcard)).symm
    · have h8 : Nat.card T = 8 := by
        obtain ⟨k, hk⟩ := hT.2.1.exists_card_eq
        have hk3 : k = 3 := by
          have h1 : 2 ^ 3 ≤ 2 ^ k := by rw [← hk]; omega
          have h2 : 2 ^ k < 2 ^ 4 := by rw [← hk]; omega
          have h1' := (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
          have h2' := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h2
          omega
        rw [hk, hk3]
        norm_num
      obtain ⟨A, hAT, hcycA, hAcard, hAinv⟩ :=
        exists_invariant_cyclic_order_four hP hTP hTn hzT (by omega)
      exact ⟨A, mem_USet_of_natCard hM hT hAT hcycA (by rw [h8, hAcard]), hAT, hAinv⟩

theorem exists_mem_WSet_omegaPrime_le [IsSimpleGroup G] (ht : S19R.TightStd p f K z)
    (hY : YPrimeData K z Y' Q) (hQq : IsQuaternionSub Q) (S : Sylow 2 G) :
    ∃ W' ∈ WSet (omegaPrime K Y'), W' ≤ (S : Subgroup G) :=
  exists_mem_WSet_le_of (conjInvariant_omegaPrime K Y') (uniqueMember_omegaPrime ht hY)
    (invariant_mem_USet_omegaPrime ht hY hQq) S

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
