module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.P12Gen
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open Subgroup

@[expose] def A12SylowType (F : Type) [Group F] : Prop :=
  ∃ (S : Sylow 2 F) (S' : Sylow 2 (alternatingGroup (Fin 12))),
    Nonempty (↥(S : Subgroup F) ≃* ↥(S' : Subgroup (alternatingGroup (Fin 12))))

variable {F : Type} [Group F]

theorem elemFactsIn_sylow_of_type [Finite F]
    (hA12 : ∀ S' : Sylow 2 (alternatingGroup (Fin 12)),
      ElemFactsIn (S' : Subgroup (alternatingGroup (Fin 12))))
    (h : A12SylowType F) (S : Sylow 2 F) : ElemFactsIn (S : Subgroup F) := by
  obtain ⟨S₀, S', ⟨e⟩⟩ := h
  have hS₀ : ElemFactsIn (S₀ : Subgroup F) := ElemFactsIn.of_mulEquiv e (hA12 S')
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F S₀ S
  refine ElemFactsIn.of_mulEquiv ?_ hS₀
  rw [← hg]
  exact (Sylow.equivSMul S₀ g).symm

theorem factorization_card_two [Finite F]
    (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F)) :
    (Nat.card F).factorization 2 = 9 := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 F))
  have hcard : Nat.card S = 2 ^ 9 := (hS S).1
  have hmult : Nat.card S = 2 ^ (Nat.card F).factorization 2 := Sylow.card_eq_multiplicity S
  rw [hcard] at hmult
  exact (Nat.pow_right_injective (le_refl 2) hmult).symm

theorem perm_orderOf_ne_sixteen (σ : Equiv.Perm (Fin 12)) : orderOf σ ≠ 16 := by
  intro h
  have hdvd : ∀ n ∈ σ.cycleType, n ∣ 8 := by
    intro n hn
    have h1 : n ∣ 16 := by
      rw [← h]
      exact Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : n ≤ 12 := by
      simpa using (Multiset.le_sum_of_mem hn).trans (Equiv.Perm.sum_cycleType_le σ)
    have h1' : n ∣ 2 ^ 4 := by simpa using h1
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow (p := 2) (by norm_num)).mp h1'
    have hk3 : k ≤ 3 := by
      rcases Nat.lt_or_ge k 4 with hklt | hkge
      · omega
      · have hk4 : k = 4 := by omega
        subst hk4
        norm_num at h2
    have : 2 ^ k ∣ 2 ^ 3 := pow_dvd_pow 2 hk3
    simpa using this
  have hlcm : σ.cycleType.lcm ∣ 8 := Multiset.lcm_dvd.mpr hdvd
  rw [Equiv.Perm.lcm_cycleType, h] at hlcm
  exact absurd hlcm (by norm_num)

theorem orderOf_ne_sixteen [Finite F] (h : A12SylowType F) (x : F) : orderOf x ≠ 16 := by
  intro hx
  have hPcard : Nat.card (zpowers x) = 2 ^ 4 := by
    rw [Nat.card_zpowers, hx]
    norm_num
  obtain ⟨T, hPT⟩ := (IsPGroup.of_card hPcard).exists_le_sylow
  obtain ⟨S₀, S', ⟨e⟩⟩ := h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq F S₀ T
  let eT : ↥(T : Subgroup F) ≃* ↥(S' : Subgroup (alternatingGroup (Fin 12))) := by
    rw [← hg]
    exact (Sylow.equivSMul S₀ g).symm.trans e
  have hx' : orderOf (⟨x, hPT (mem_zpowers x)⟩ : ↥(T : Subgroup F)) = 16 := by
    rw [Subgroup.orderOf_mk]
    exact hx
  have h2 : orderOf (eT ⟨x, hPT (mem_zpowers x)⟩) = 16 := by
    rw [MulEquiv.orderOf_eq, hx']
  have h3 : orderOf ((eT ⟨x, hPT (mem_zpowers x)⟩ : alternatingGroup (Fin 12))) = 16 := by
    rw [Subgroup.orderOf_coe, h2]
  have h4 : orderOf (((eT ⟨x, hPT (mem_zpowers x)⟩ : alternatingGroup (Fin 12)) :
      Equiv.Perm (Fin 12))) = 16 := by
    rw [Subgroup.orderOf_coe, h3]
  exact perm_orderOf_ne_sixteen _ h4

theorem six_le_twoRank [Finite F] {E : Subgroup F} (hsq : ∀ x ∈ E, x * x = 1)
    (hc : Nat.card E = 2 ^ 6) : 6 ≤ CFSG.Open.twoRank F := by
  have hcomm : IsMulCommutative E :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext <| by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        have ha : (a : F)⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a a.2)
        have hb : (b : F)⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b b.2)
        have hab : ((a : F) * b)⁻¹ = (a : F) * b :=
          inv_eq_of_mul_eq_one_right (hsq ((a : F) * b) (mul_mem a.2 b.2))
        calc (a : F) * b = ((a : F) * b)⁻¹ := hab.symm
          _ = (b : F)⁻¹ * (a : F)⁻¹ := mul_inv_rev _ _
          _ = b * a := by rw [ha, hb]
  have hE : CFSG.Open.IsElemAbelian 2 E :=
    ⟨hcomm, fun x hx => by rw [pow_two]; exact hsq x hx⟩
  exact CFSG.SectionRank.le_pRank (H := ⊤) Nat.one_lt_two le_top hE hc

theorem dvd_card_normalizer_of_elem [Finite F]
    (hS : ∀ S : Sylow 2 F, ElemFactsIn (S : Subgroup F)) (E₀ : Subgroup F)
    (h0sq : ∀ x ∈ E₀, x * x = 1) (h0c : 2 ^ 6 ≤ Nat.card E₀) (H : Subgroup F)
    (hH : H ≤ normalizer (E₀ : Set F)) (h5 : 5 ∣ Nat.card H) (E : Subgroup F)
    (hEsq : ∀ x ∈ E, x * x = 1) (hEc : Nat.card E = 2 ^ 6) :
    5 ∣ Nat.card (normalizer (E : Set F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE₀2 : IsPGroup 2 E₀ := by
    intro g
    exact ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa [pow_two] using h0sq (g : F) g.2)⟩
  have hE2 : IsPGroup 2 E := by
    intro g
    exact ⟨1, by
      rw [pow_one]
      exact Subtype.ext (by simpa [pow_two] using hEsq (g : F) g.2)⟩
  obtain ⟨S₀, hE₀S₀⟩ := hE₀2.exists_le_sylow
  obtain ⟨S₁, hES₁⟩ := hE2.exists_le_sylow
  obtain ⟨-, -, E₁, hE₁S₀, hE₁sq, hE₁card, hE₁max⟩ := hS S₀
  have hE₀E₁ : E₀ ≤ E₁ := hE₁max E₀ hE₀S₀ h0sq h0c
  have hE₀eq : E₀ = E₁ := Subgroup.eq_of_le_of_card_ge hE₀E₁ (by rw [hE₁card]; exact h0c)
  have hE₀card : Nat.card E₀ = 2 ^ 6 := by rw [hE₀eq, hE₁card]
  obtain ⟨-, -, E₂, hE₂S₁, hE₂sq, hE₂card, hE₂max⟩ := hS S₁
  have hEE₂ : E ≤ E₂ := hE₂max E hES₁ hEsq (by rw [hEc])
  have hEeqE₂ : E = E₂ := Subgroup.eq_of_le_of_card_ge hEE₂ (by rw [hE₂card, hEc])
  haveI : Finite (Sylow 2 F) := Sylow.finite_of_finiteIndex S₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := F) S₀ S₁
  let f : F →* F := MulDistribMulAction.toMonoidEnd (MulAut F) F (MulAut.conj g)
  have hSmap : (S₁ : Subgroup F) = S₀.map f := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact (MulAut.conj g).injective (by simpa [f, MulAut.smul_def] using hab)
  let A : Subgroup F := E₀.map f
  have hAS₁ : A ≤ (S₁ : Subgroup F) := by
    change E₀.map f ≤ (S₁ : Subgroup F)
    rw [hSmap]
    exact Subgroup.map_mono (f := f) hE₀S₀
  have hA_sq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, h0sq y hy, map_one]
  have hA_card : Nat.card A = 2 ^ 6 := by
    change Nat.card (E₀.map f) = 2 ^ 6
    rw [Subgroup.card_map_of_injective hf_inj, hE₀card]
  have hA_le_E : A ≤ E := by
    rw [hEeqE₂]
    exact hE₂max A hAS₁ hA_sq (by rw [hA_card])
  have hAeq : A = E := Subgroup.eq_of_le_of_card_ge hA_le_E (by rw [hA_card, hEc])
  have hEeq : E = E₀.map f := hAeq.symm
  let H' : Subgroup F := H.map f
  have hH'le : H' ≤ normalizer (E : Set F) := by
    change H.map f ≤ normalizer (E : Set F)
    rw [hEeq]
    exact (Subgroup.map_mono (f := f) hH).trans (Subgroup.le_normalizer_map f)
  have hH'card : Nat.card H' = Nat.card H := by
    change Nat.card (H.map f) = Nat.card H
    rw [Subgroup.card_map_of_injective hf_inj]
  have hdvd : Nat.card H' ∣ Nat.card (normalizer (E : Set F)) :=
    Subgroup.card_dvd_of_le hH'le
  have h5' : 5 ∣ Nat.card H' := by rw [hH'card]; exact h5
  exact h5'.trans hdvd

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
