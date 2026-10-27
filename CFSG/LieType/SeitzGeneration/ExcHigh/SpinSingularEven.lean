module

public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinSingular
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.LieType.Universal QuadraticMap Module

section NR

theorem exists_rGroup_normalized_of_invariant_singular_of_charTwo {K : Type*} [Field K]
    [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate) (hV : 5 ≤ finrank K V)
    (hinj : Function.Injective (Spin.spinAction Q))
    (E : Subgroup (spinGroup Q)) (T : Submodule K V) (hT0 : T ≠ ⊥) (hTs : ∀ v ∈ T, Q v = 0)
    (hTi : ∀ e ∈ E, ∀ v ∈ T, Spin.spinAction Q e v ∈ T) :
    ∃ U : Subgroup (spinGroup Q), U ≠ ⊥ ∧ IsPGroup (ringChar K) U ∧
      ∀ e ∈ E, U.map (MulAut.conj e).toMonoidHom = U := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hr : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨W, hW⟩ : ∃ W, W = LinearMap.BilinForm.orthogonal (polarBilin Q) T := ⟨_, rfl⟩
  have hTW : T ≤ W := hW ▸ le_orthogonal_of_forall_eq_zero Q hTs
  set P : Subgroup (spinGroup Q) :=
    Subgroup.comap (Spin.spinAction Q) (flagRadical T W hTW) with hP
  refine ⟨P, ?_, ?_, fun e he => ?_⟩
  · obtain ⟨y, hy1, hyr, hyR⟩ := exists_ne_one_pow_ringChar_eq_one_mem_flagRadical Q hQ hV hT0 hTs
    intro hP0
    have hyP : y ∈ P := by
      subst hW
      rw [hP, Subgroup.mem_comap]
      exact hyR
    rw [hP0, Subgroup.mem_bot] at hyP
    exact hy1 hyP
  · intro x
    refine ⟨2, Subtype.ext ?_⟩
    have hx : Spin.spinAction Q (x : spinGroup Q) ∈ flagRadical T W hTW := x.2
    have h4 : (Spin.spinAction Q (x : spinGroup Q)) ^ 4 = 1 := by
      refine LinearEquiv.ext fun v => ?_
      rw [pow_apply_of_mem_flagRadical hx 4 v]
      have h4' : ((4 : ℕ) : K) = 0 := by
        rw [show ((4 : ℕ) : K) = 2 * 2 by norm_num, h2, zero_mul]
      have h6 : ((Nat.choose 4 2 : ℕ) : K) = 0 := by
        rw [show Nat.choose 4 2 = 2 * 3 by decide, Nat.cast_mul, show ((2 : ℕ) : K) = 0 from h2,
          zero_mul]
      rw [h4', h6]
      simp
    have h4x : (x : spinGroup Q) ^ 4 = 1 := hinj (by rw [map_pow, h4, map_one])
    have h4y : (x : spinGroup Q) ^ (ringChar K ^ 2) = 1 := by
      rw [hr]
      exact h4x
    rw [Subgroup.coe_pow, h4y]
    rfl
  · have hconj : ∀ e ∈ E, ∀ y ∈ P, e * y * e⁻¹ ∈ P := by
      intro e he y hyP
      have hs := hTi e he
      have hs' := hTi e⁻¹ (E.inv_mem he)
      rw [hP, Subgroup.mem_comap] at hyP ⊢
      rw [map_mul, map_mul, map_inv]
      refine mul_mul_inv_mem_flagRadical hyP hs (fun w hw => ?_) ?_ (fun w hw => ?_)
      · rw [hW] at hw ⊢
        exact spinAction_mem_orthogonal Q hs' hw
      · rw [← map_inv]
        exact hs'
      · rw [hW] at hw ⊢
        rw [← map_inv]
        exact spinAction_mem_orthogonal Q (by rwa [inv_inv]) hw
    refine le_antisymm ?_ fun y hy => ⟨e⁻¹ * y * e, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact hconj e he y hy
    · simpa using hconj e⁻¹ (E.inv_mem he) y hy
    · simp [mul_assoc]

theorem exists_rGroup_normalized_of_invariant_singular_charTwo
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 3 ≤ n)
    (E : Subgroup (spinGroup (Spin.quadPlus n K)))
    (T : Submodule K (Fin n ⊕ Fin n → K)) (hT0 : T ≠ ⊥)
    (hTs : ∀ v ∈ T, Spin.quadPlus n K v = 0)
    (hTi : ∀ e ∈ E, ∀ v ∈ T, Spin.spinAction (Spin.quadPlus n K) e v ∈ T) :
    ∃ U : Subgroup (spinGroup (Spin.quadPlus n K)), U ≠ ⊥ ∧ IsPGroup (ringChar K) U ∧
      ∀ e ∈ E, U.map (MulAut.conj e).toMonoidHom = U :=
  exists_rGroup_normalized_of_invariant_singular_of_charTwo (Spin.quadPlus n K)
    (Spin.nondegenerate_polarBilin_quadPlus n K)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; omega)
    CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective E T hT0 hTs hTi

end NR

section Center

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.ModelFacts

theorem not_dvd_card_center_spinPlus_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn3 : 3 ≤ n) : ¬ 2 ∣ Nat.card (Subgroup.center (spinGroup (Spin.quadPlus n K))) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  haveI : Finite (spinGroup (Spin.quadPlus n K)) :=
    finite_spinGroup_of_ker _ Spin.coe_ker_spinMatrix_quadPlus
  obtain ⟨-, hcomap, hZ⟩ := Spin.spinToStatedProj_quadPlus (n := n) (K := K) hn3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine not_dvd_card_center_of_forall (p := 2) fun x hx hx2 => ?_
  have hx' : x ∈ (CFSG.Open.StatedScalars _ K).comap (Spin.spinMatrix (Spin.quadPlus n K)) := by
    rw [← hcomap, hZ]
    exact hx
  obtain ⟨c, hc⟩ := Subgroup.mem_comap.mp hx'
  have hc2 : c ^ 2 = 1 := by
    apply scalar_injective_of_nonempty (ι := Fin n ⊕ Fin n)
    rw [map_pow, hc, ← map_pow, hx2, map_one, map_one]
  have hc1 : c = 1 := by
    apply Units.ext
    have h0 : ((c : K) - 1) ^ 2 = 0 := by
      rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hc2]
      simp
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp h0
    simpa [sub_eq_zero] using this
  have hxm : Spin.spinMatrix (Spin.quadPlus n K) x = 1 := by
    rw [← hc, hc1, map_one]
  have hker := Spin.ker_spinMatrix_quadPlus_eq_bot (n := n) (K := K) CharTwo.two_eq_zero
  have : x ∈ (Spin.spinMatrix (Spin.quadPlus n K)).ker := MonoidHom.mem_ker.mpr hxm
  rw [hker] at this
  exact Subgroup.mem_bot.mp this

end Center

end CFSG.LieType.SeitzGeneration.ExcHigh
