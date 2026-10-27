module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PI1XAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffOutFF6PI1X_B1p_mem_X (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    {b : ↥(omegaProj hQ)} (hb : b ∈ ffB1p hQ fr) :
    b ∈ twoPrimeRes (twoRes (ffFix hQ h2 (ffTs fr))) := by
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  obtain ⟨J, hJ, hbJ⟩ := (mem_ffB1p_iff hQ fr).mp hb
  have hb_eq : b = ffOutFF6PI1X_sp hQ fr J hJ := by
    apply Subtype.ext
    rw [hbJ, ffOutFF6PI1X_sp, coe_omegaToProj]
  rw [hb_eq]
  have hR := ffOutFF6PI1X_even_sp_mem hQ hdim hsgn h2 fr J hJ
  have hsq : ffOutFF6PI1X_sp hQ fr J hJ ^ 2 = 1 := by
    rw [pow_two]; exact ffOutFF6PI1X_sp_mul_self hQ fr J hJ
  have hdvd : orderOf (ffOutFF6PI1X_sp hQ fr J hJ) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
  · exact Subgroup.subset_closure ⟨hR, ⟨0, by rw [h1, pow_zero]⟩⟩
  · exact Subgroup.subset_closure ⟨hR, ⟨1, by rw [h2', pow_one]⟩⟩

theorem ffOutFF6PI1X_three_cycle_mem (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    {σ : Equiv.Perm (Fin 5)} (hσ : Equiv.Perm.IsThreeCycle σ) :
    ffOutFF6PI1X_hat hQ fr σ ∈ twoRes (ffFix hQ h2 (ffTs fr)) := by
  have hC := ffOutFF6PI1X_hat_mem_fix hQ hdim hsgn h2 fr σ
  have h3 : σ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ
    rwa [hσ.orderOf] at h
  have hodd : Odd (orderOf (ffOutFF6PI1X_hat hQ fr σ)) := by
    apply Odd.of_dvd_nat (n := 3) (by norm_num)
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, h3, map_one])
  exact Subgroup.subset_closure ⟨hC, hodd⟩

theorem ffOutFF6PI1X_hat_mem_X (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    {τ : Equiv.Perm (Fin 5)} (hτ : τ ^ 2 = 1) (hs : Equiv.Perm.sign τ = 1) :
    omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩ ∈
      twoPrimeRes (twoRes (ffFix hQ h2 (ffTs fr))) := by
  change ffOutFF6PI1X_hat hQ fr τ ∈ twoPrimeRes (twoRes (ffFix hQ h2 (ffTs fr)))
  have hR : ffOutFF6PI1X_hat hQ fr τ ∈ twoRes (ffFix hQ h2 (ffTs fr)) := by
    have hτA : τ ∈ alternatingGroup (Fin 5) :=
      (Equiv.Perm.mem_alternatingGroup).mpr hs
    have hle : Subgroup.closure {σ : Equiv.Perm (Fin 5) | Equiv.Perm.IsThreeCycle σ} ≤
        (twoRes (ffFix hQ h2 (ffTs fr))).comap (ffOutFF6PI1X_hat hQ fr) := by
      rw [Subgroup.closure_le]
      intro σ hσ
      change ffOutFF6PI1X_hat hQ fr σ ∈ twoRes (ffFix hQ h2 (ffTs fr))
      exact ffOutFF6PI1X_three_cycle_mem hQ hdim hsgn h2 fr hσ
    have hmem : τ ∈ Subgroup.closure {σ : Equiv.Perm (Fin 5) | Equiv.Perm.IsThreeCycle σ} := by
      rw [Equiv.Perm.closure_three_cycles_eq_alternating]
      exact hτA
    exact hle hmem
  have hsq : ffOutFF6PI1X_hat hQ fr τ ^ 2 = 1 := by
    rw [← map_pow, hτ, map_one]
  have hdvd : orderOf (ffOutFF6PI1X_hat hQ fr τ) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
  · exact Subgroup.subset_closure ⟨hR, ⟨0, by rw [h1, pow_zero]⟩⟩
  · exact Subgroup.subset_closure ⟨hR, ⟨1, by rw [h2', pow_one]⟩⟩

theorem ffOutFF6PI1X_exists_two :
    ∀ i j : Fin 5, i ≠ j →
      ∃ k l : Fin 5, k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  decide

theorem ffOutFF6PI1X_swap_pair_sq :
    ∀ i j k l : Fin 5, i ≠ j → k ≠ l → k ≠ i → k ≠ j → l ≠ i → l ≠ j →
      (Equiv.swap i j * Equiv.swap k l) ^ 2 = 1 := by
  decide +kernel

theorem ffOutFF6PI1X_swap_pair_apply :
    ∀ i j k l : Fin 5, k ≠ i → k ≠ j → l ≠ i → l ≠ j →
      (Equiv.swap i j * Equiv.swap k l) i = j := by
  decide +kernel

theorem ffOutFF6PI1X_swap_pair_sign :
    ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
      Equiv.Perm.sign (Equiv.swap i j * Equiv.swap k l) = 1 := by
  intro i j k l hij hkl
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.sign_swap hkl]
  decide

theorem ffOutFF6PI1X_even_involution (i j : Fin 5) :
    ∃ τ : Equiv.Perm (Fin 5), τ ^ 2 = 1 ∧ Equiv.Perm.sign τ = 1 ∧ τ i = j := by
  by_cases hij : i = j
  · exact ⟨1, by simp, by simp, by simpa using hij⟩
  · obtain ⟨k, l, hki, hkj, hli, hlj, hlk⟩ := ffOutFF6PI1X_exists_two i j hij
    exact ⟨Equiv.swap i j * Equiv.swap k l,
      ffOutFF6PI1X_swap_pair_sq i j k l hij hlk.symm hki hkj hli hlj,
      ffOutFF6PI1X_swap_pair_sign i j k l hij hlk.symm,
      ffOutFF6PI1X_swap_pair_apply i j k l hki hkj hli hlj⟩

theorem ffOutFF6PI1X_involution_fix_K (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {z : ProjSim Q}
    {K : Finset (Option (Fin 5))}
    (hK : z = projOrthToProjSim Q (toProj Q (fr.signChange K)))
    {τ : Equiv.Perm (Fin 5)}
    (hcomm : z * ffOmegaToSim hQ (omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩) =
      ffOmegaToSim hQ (omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩) * z) :
    K.map (Equiv.optionCongr τ).toEmbedding = K := by
  have hτ' : projOrthToProjSim Q (toProj Q (fr.signChange K)) *
      projOrthToProjSim Q (toProj Q (ffHat fr τ)) =
      projOrthToProjSim Q (toProj Q (ffHat fr τ)) *
        projOrthToProjSim Q (toProj Q (fr.signChange K)) := by
    rw [ffOmegaToSim_apply, coe_omegaToProj] at hcomm
    rw [hK] at hcomm
    exact hcomm
  have h2 : toProj Q (fr.signChange K) * toProj Q (ffHat fr τ) =
      toProj Q (ffHat fr τ) * toProj Q (fr.signChange K) := by
    apply projOrthToProjSim_injective
    rw [map_mul, map_mul]
    exact hτ'
  have h3 : toProj Q (ffHat fr τ * fr.signChange K * (ffHat fr τ)⁻¹) =
      toProj Q (fr.signChange K) := by
    rw [map_mul, map_mul, map_inv, ← h2]
    group
  have h4 : toProj Q (fr.signChange (K.map (Equiv.optionCongr τ).toEmbedding)) =
      toProj Q (fr.signChange K) := by
    rw [← ffHat_conj_signChange fr τ K]
    exact h3
  rcases (ff6p_toProj_signChange_eq_iff fr (K.map (Equiv.optionCongr τ).toEmbedding) K).mp
    h4 with h | h
  · exact h
  · exfalso
    have hnone : none ∈ K.map (Equiv.optionCongr τ).toEmbedding ↔ none ∈ K := by
      rw [Finset.mem_map]
      constructor
      · rintro ⟨x, hxK, hx⟩
        cases x with
        | none => simpa using hxK
        | some i => simp [Equiv.optionCongr_apply] at hx
      · intro hK
        exact ⟨none, hK, by
          show (Equiv.optionCongr τ) none = none
          simp [Equiv.optionCongr_apply]⟩
    rw [h] at hnone
    rw [Finset.mem_compl] at hnone
    tauto

theorem ffOutFF6PI1X_cent_X (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : PFrame Q (Option (Fin 5)) ffC)
    {z : ProjSim Q}
    (hB : ∀ b ∈ ffB1p hQ fr, z * ffOmegaToSim hQ b = ffOmegaToSim hQ b * z)
    (hτ : ∀ τ : Equiv.Perm (Fin 5), τ ^ 2 = 1 → Equiv.Perm.sign τ = 1 →
      z * ffOmegaToSim hQ (omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩) =
        ffOmegaToSim hQ (omegaToProj hQ ⟨ffHat fr τ, ffHat_mem_omega hQ fr τ⟩) * z) :
    z = 1 ∨ z = ffTs fr := by
  obtain ⟨K, hK⟩ := ff6p_star_cent_sim hQ h2 fr hB
  have hfix : ∀ τ : Equiv.Perm (Fin 5), τ ^ 2 = 1 → Equiv.Perm.sign τ = 1 →
      K.map (Equiv.optionCongr τ).toEmbedding = K := fun τ h1 h2' =>
    ffOutFF6PI1X_involution_fix_K hQ fr hK (hτ τ h1 h2')
  have hsome : (∀ i : Fin 5, some i ∈ K) ∨ (∀ i : Fin 5, some i ∉ K) := by
    by_cases hex : ∃ i : Fin 5, some i ∈ K
    · left
      intro j
      obtain ⟨i, hi⟩ := hex
      obtain ⟨τ, hτ2, hτs, hτij⟩ := ffOutFF6PI1X_even_involution i j
      have hmap := hfix τ hτ2 hτs
      have hmj : some j ∈ K.map (Equiv.optionCongr τ).toEmbedding := by
        rw [Finset.mem_map]
        exact ⟨some i, hi, by
          show (Equiv.optionCongr τ) (some i) = some j
          simp [Equiv.optionCongr_apply, hτij]⟩
      rwa [hmap] at hmj
    · right
      intro i hi
      exact hex ⟨i, hi⟩
  rcases hsome with hall | hnone
  · by_cases hKnone : none ∈ K
    · left
      have hKuniv : K = Finset.univ := by
        apply Finset.eq_univ_iff_forall.mpr
        intro x
        cases x with
        | none => exact hKnone
        | some i => exact hall i
      rw [hK, hKuniv, ← fr.piOrth_eq_signChange_univ, toProj_piOrth, map_one]
    · right
      have hKcompl : K = ({none} : Finset (Option (Fin 5)))ᶜ := by
        ext x
        cases x with
        | none => simp [hKnone]
        | some i => simp [hall i]
      rw [hK, hKcompl, ff6p_toProj_signChange_compl]
      rfl
  · by_cases hKnone : none ∈ K
    · right
      have hKeq : K = {none} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        exact ⟨hKnone, fun y hy => by
          cases y with
          | none => rfl
          | some i => exact absurd hy (hnone i)⟩
      rw [hK, hKeq]
      rfl
    · left
      have hKeq : K = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x
        cases x with
        | none => exact hKnone
        | some i => exact hnone i
      rw [hK, hKeq, fr.signChange_empty]
      simp

end CFSG.OddStandard.SmallF3.Omega
