module

public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionWitness
public import CFSG.ClassicalGroups.Orthogonal.RootInvolutionTypes
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol
import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalEmptyInvolutionEightThree
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.GF2n.Smith81

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_orderOf_mul_conj_of_conj {s t h : V ≃ₗ[K] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hst : h * s * h⁻¹ = t) {n : ℕ}
    (hs : ∃ k ∈ elementaryGroup Q, orderOf (s * (k * s * k⁻¹)) = n) :
    ∃ g ∈ elementaryGroup Q, orderOf (t * (g * t * g⁻¹)) = n := by
  obtain ⟨k, hk, hkn⟩ := hs
  refine ⟨h * k * h⁻¹, conj_mem_elementaryGroup hh hk, ?_⟩
  have hconj : t * (h * k * h⁻¹ * t * (h * k * h⁻¹)⁻¹) = MulAut.conj h (s * (k * s * k⁻¹)) := by
    rw [← hst, MulAut.conj_apply]
    group
  rw [hconj, ← hkn]
  exact orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective _

variable [Finite K] [CharP K 2] [FiniteDimensional K V]

omit [Finite K] [CharP K 2] in
theorem finrank_commSpace_ne_zero {t : V ≃ₗ[K] V} (ht : t ≠ 1) : finrank K (commSpace t) ≠ 0 := by
  intro h0
  rw [Submodule.finrank_eq_zero] at h0
  refine ht (LinearEquiv.ext fun v => ?_)
  have hv : t v - v ∈ commSpace t := mem_commSpace.mpr ⟨v, rfl⟩
  rw [h0, Submodule.mem_bot, sub_eq_zero] at hv
  exact hv

omit [Finite K] [CharP K 2] in
private theorem ne_one_of_finrank_commSpace_ne_zero {s : V ≃ₗ[K] V}
    (h : finrank K (commSpace s) ≠ 0) : s ≠ 1 := by
  rintro rfl
  refine h (Submodule.finrank_eq_zero.mpr (eq_bot_iff.mpr fun y hy => ?_))
  obtain ⟨x, rfl⟩ := mem_commSpace.mp hy
  rw [Submodule.mem_bot, LinearEquiv.coe_one, id, sub_self]

private theorem exists_orderOf_of_same_type (hQ : (polarBilin Q).Nondegenerate)
    {s t : V ≃ₗ[K] V} (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : orderOf s = 2)
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht : orderOf t = 2)
    (hlet : suzukiLetter Q t = suzukiLetter Q s)
    (hdim : finrank K (commSpace t) = finrank K (commSpace s)) {n : ℕ}
    (hk : ∃ k ∈ elementaryGroup Q, orderOf (s * (k * s * k⁻¹)) = n) :
    ∃ g ∈ elementaryGroup Q, orderOf (t * (g * t * g⁻¹)) = n := by
  obtain ⟨h, hh, hst⟩ := (isConj_iff_suzukiLetter_eq hQ hsO hs htO ht).mpr ⟨hlet, hdim⟩
  exact exists_orderOf_mul_conj_of_conj hh hst hk

omit [Finite K] [FiniteDimensional K V] in
private theorem exists_orderOf_eichlerPairProd_eq_six {P : ℕ → HypPair Q} {r k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : 2 * k ≤ r) (hk2 : 2 ≤ k) :
    ∃ g ∈ elementaryGroup Q,
      orderOf (eichlerPairProd P 0 k * (g * eichlerPairProd P 0 k * g⁻¹)) = 6 := by
  have hsplit : eichlerPairProd P 0 k = a4Involution P * eichlerPairProd P 4 (k - 2) := by
    have h := eichlerPairProd_add P 0 2 (k - 2)
    rw [show 2 + (k - 2) = k by omega, show 0 + 2 * 2 = 4 by rfl] at h
    rw [h, eichlerPairProd_succ, eichlerPairProd_succ, eichlerPairProd_zero, one_mul]
    rfl
  refine ⟨a4Conjugator P, a4Conjugator_mem_elementaryGroup P, ?_⟩
  rw [hsplit]
  exact orderOf_a4_mul_conj (fun i i' hi hi' hne => hP i i' (by omega) (by omega) hne)
    (eichlerPairProd_mem_orthogonalGroup P 4 (k - 2)) (eichlerPairProd_mul_self hP (by omega))
    fun i hi => ⟨eichlerPairProd_apply_of_polar fun i' h1 h2 =>
        (hP i i' (by omega) (by omega) (by omega)).ee,
      eichlerPairProd_apply_of_polar fun i' h1 h2 =>
        (hP i i' (by omega) (by omega) (by omega)).fe⟩

omit [Finite K] [FiniteDimensional K V] in
private theorem exists_orderOf_eichler_mul_eichlerPairProd_eq_six {P : ℕ → HypPair Q} {r k : ℕ}
    (hP : ∀ i i', i < r → i' < r → i ≠ i' → (P i).Orth (P i')) (hk : 2 * k + 1 ≤ r) (hr : 2 ≤ r)
    {a₁ a₂ : V} (ha₁ : Q a₁ = 1) (ha₁₂ : polar Q a₁ a₂ = 1)
    (hperp : ∀ i < r, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 ∧
      polar Q (P i).e a₂ = 0 ∧ polar Q (P i).f a₂ = 0) :
    ∃ g ∈ elementaryGroup Q, orderOf (eichler Q (P 0).e a₁ * eichlerPairProd P 1 k *
      (g * (eichler Q (P 0).e a₁ * eichlerPairProd P 1 k) * g⁻¹)) = 6 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · refine ⟨c2Conjugator P a₁ a₂, c2Conjugator_mem_elementaryGroup P a₁ a₂, ?_⟩
    rw [eichlerPairProd_zero, mul_one]
    exact orderOf_c2_mul_conj (hP 0 1 (by omega) (by omega) (by omega)) ha₁ ha₁₂
      fun i hi => hperp i (by omega)
  have hsplit : eichler Q (P 0).e a₁ * eichlerPairProd P 1 k =
      c4Involution P a₁ * eichlerPairProd P 3 (k - 1) := by
    have h := eichlerPairProd_add P 1 1 (k - 1)
    rw [show 1 + (k - 1) = k by omega, show 1 + 2 * 1 = 3 by rfl] at h
    rw [h, eichlerPairProd_succ, eichlerPairProd_zero, one_mul, ← mul_assoc]
    rfl
  have hfix : ∀ x, (∀ i, 3 ≤ i → i < 3 + 2 * (k - 1) → polar Q x (P i).e = 0) →
      eichlerPairProd P 3 (k - 1) x = x := fun x hx => eichlerPairProd_apply_of_polar hx
  refine ⟨c4Conjugator P, c4Conjugator_mem_elementaryGroup P, ?_⟩
  rw [hsplit]
  exact orderOf_c4_mul_conj (fun i i' hi hi' hne => hP i i' (by omega) (by omega) hne) ha₁ ha₁₂
    (fun i hi => hperp i (by omega)) (eichlerPairProd_mem_orthogonalGroup P 3 (k - 1))
    (eichlerPairProd_mul_self hP (by omega))
    (fun i hi => ⟨hfix _ fun i' h1 h2 => (hP i i' (by omega) (by omega) (by omega)).ee,
      hfix _ fun i' h1 h2 => (hP i i' (by omega) (by omega) (by omega)).fe⟩)
    ⟨hfix _ fun i' h1 h2 => by rw [polar_comm]; exact (hperp i' (by omega)).1,
      hfix _ fun i' h1 h2 => by rw [polar_comm]; exact (hperp i' (by omega)).2.2.1⟩

theorem exists_orderOf_mul_conj_eq_six_of_vanish (hQ : (polarBilin Q).Nondegenerate)
    {t : V ≃ₗ[K] V} (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht : orderOf t = 2)
    (hl : 4 ≤ finrank K (commSpace t)) (heven : Even (finrank K (commSpace t)))
    (hvan : ∀ x ∈ commSpace t, Q x = 0) :
    ∃ g ∈ elementaryGroup Q, orderOf (t * (g * t * g⁻¹)) = 6 := by
  have hne : commSpace t ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hl
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨P₀, -⟩ := exists_hypPair hQ (hvan x hx) hx0
  obtain ⟨r, P, hP, hA⟩ := exists_family_anisotropic hQ P₀
  have hlr := CFSG.LocalAnalysis.ComponentInitial.finrank_le_of_totallySingular hP hA hvan
  obtain ⟨k, hk⟩ := heven
  obtain ⟨hdim, hsing⟩ := commSpace_eichlerPairProd (j := 0) (k := k) hP (by omega)
  have hs2 : orderOf (eichlerPairProd P 0 k) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact eichlerPairProd_mul_self hP (by omega))
      (ne_one_of_finrank_commSpace_ne_zero (by omega))
  refine exists_orderOf_of_same_type hQ (eichlerPairProd_mem_orthogonalGroup P 0 k) hs2 htO ht ?_
    (by omega) (exists_orderOf_eichlerPairProd_eq_six hP (by omega) (by omega))
  rw [suzukiLetter_eq_a_iff.mpr ⟨⟨k, hk⟩, hvan⟩, suzukiLetter_eq_a_iff.mpr ⟨⟨k, by omega⟩, hsing⟩]

theorem exists_orderOf_mul_conj_eq_six_of_not_vanish (hQ : (polarBilin Q).Nondegenerate)
    {m : ℕ} (hm : finrank K V = 2 * m) (hm3 : 3 ≤ m) {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht : orderOf t = 2)
    (heven : Even (finrank K (commSpace t))) (hnv : ∃ x ∈ commSpace t, Q x ≠ 0) :
    ∃ g ∈ elementaryGroup Q, orderOf (t * (g * t * g⁻¹)) = 6 := by
  have htt : t * t = 1 := by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp ht).1
  have hlm : finrank K (commSpace t) ≤ m := by
    have h1 := Submodule.finrank_mono (commSpace_le_fixSpace htt)
    have h2 := finrank_commSpace_add_finrank_fixSpace t
    omega
  have hl0 := finrank_commSpace_ne_zero (orderOf_eq_prime_iff.mp ht).2
  obtain ⟨k, hk⟩ := heven
  obtain ⟨P, a₁, a₂, hP, ha₁, ha₁₂, hperp⟩ := exists_rootCFrame hQ hm (by omega)
  have hperp' : ∀ i < m - 1, polar Q (P i).e a₁ = 0 ∧ polar Q (P i).f a₁ = 0 :=
    fun i hi => ⟨(hperp i hi).1, (hperp i hi).2.1⟩
  obtain ⟨hdim, hns⟩ := commSpace_eichler_mul_eichlerPairProd (k := k - 1) hQ hP (by omega)
    (by rw [ha₁]; exact one_ne_zero) hperp'
  have hsO : eichler Q (P 0).e a₁ * eichlerPairProd P 1 (k - 1) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (eichler_mem_orthogonalGroup Q _ _) (eichlerPairProd_mem_orthogonalGroup P 1 (k - 1))
  have hs2 : orderOf (eichler Q (P 0).e a₁ * eichlerPairProd P 1 (k - 1)) = 2 :=
    orderOf_eq_prime
      (by rw [pow_two]; exact eichler_mul_eichlerPairProd_mul_self hP (by omega) hperp')
      (ne_one_of_finrank_commSpace_ne_zero (by omega))
  refine exists_orderOf_of_same_type hQ hsO hs2 htO ht ?_ (by omega)
    (exists_orderOf_eichler_mul_eichlerPairProd_eq_six hP (by omega) (by omega) ha₁ ha₁₂ hperp)
  rw [suzukiLetter_eq_c_iff.mpr ⟨⟨k, hk⟩, hnv⟩, suzukiLetter_eq_c_iff.mpr ⟨⟨k, by omega⟩, hns⟩]

theorem exists_orderOf_mul_conj_eq_six (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : finrank K V = 2 * m) (hm3 : 3 ≤ m) {t : V ≃ₗ[K] V} (htE : t ∈ elementaryGroup Q)
    (ht : orderOf t = 2) (hnot : ¬IsOrthA2 Q t) :
    ∃ g ∈ elementaryGroup Q, orderOf (t * (g * t * g⁻¹)) = 6 := by
  have htO := elementaryGroup_le_orthogonalGroup Q htE
  have heven : Even (finrank K (commSpace t)) := (elementaryGroup_le_omegaGroup hQ htE).2
  by_cases hvan : ∀ x ∈ commSpace t, Q x = 0
  · refine exists_orderOf_mul_conj_eq_six_of_vanish hQ htO ht ?_ heven hvan
    have htt : t * t = 1 := by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp ht).1
    have h0 := finrank_commSpace_ne_zero (orderOf_eq_prime_iff.mp ht).2
    have h2 : finrank K (commSpace t) ≠ 2 := fun h2 => hnot ⟨htO, htt, h2, hvan⟩
    obtain ⟨r, hr⟩ := heven
    omega
  · push Not at hvan
    exact exists_orderOf_mul_conj_eq_six_of_not_vanish hQ hm hm3 htO ht heven hvan

theorem isOrthA2_of_forall_orderOf_mul_conj (hQ : (polarBilin Q).Nondegenerate) {m : ℕ}
    (hm : finrank K V = 2 * m) (hm3 : 3 ≤ m) {t : V ≃ₗ[K] V} (htE : t ∈ elementaryGroup Q)
    (ht : orderOf t = 2)
    (hord : ∀ g ∈ elementaryGroup Q,
      orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))) :
    IsOrthA2 Q t := by
  by_contra hnot
  obtain ⟨g, hg, h6⟩ := exists_orderOf_mul_conj_eq_six hQ hm hm3 htE ht hnot
  rcases hord g hg with h | h <;> rw [h6] at h
  · exact absurd h (by norm_num)
  · exact absurd h (by rw [Nat.odd_iff]; norm_num)

end CFSG.ClassicalGroups.Orthogonal
