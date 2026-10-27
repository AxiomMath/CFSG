module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutB
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_involution_inf_centralizer [Finite X] {Q T : Subgroup X} (hT : IsPGroup 2 T)
    (hQT : Q ≤ T) (hTN : T ≤ normalizer (Q : Set X)) (hQ : Q ≠ ⊥) :
    ∃ z ∈ Q, orderOf z = 2 ∧ ∀ y ∈ T, y * z = z * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (Q.subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hTN
  have hne : Q.subgroupOf T ≠ ⊥ := by
    intro h
    apply hQ
    rw [← map_subgroupOf_eq_of_le hQT, h, Subgroup.map_bot]
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set Z := Q.subgroupOf T ⊓ center ↥T with hZdef
  have hZ2 : IsPGroup 2 Z := hT.to_subgroup Z
  have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).mpr hZ
  obtain ⟨k, hk⟩ := hZ2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card Z by
    rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨((w : ↥T) : X), (mem_inf.mp w.2).1, ?_, fun y hy => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  · have h1 := mem_center_iff.mp (mem_inf.mp w.2).2 ⟨y, hy⟩
    exact congrArg Subtype.val h1

theorem le_normalizer_of_sylow_kernel [Finite X] {E M : Subgroup X}
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2)
    (hQS : Q ≤ Sc) (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hS2 : IsPGroup 2 Sc) : Sc ≤ normalizer (Q : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  set K : Subgroup X := H ⊓ UnbalancedLayer.coreActionKernel M with hKdef
  set P : Subgroup X := Sc ⊓ K with hPdef
  have hQP : Q ≤ P := le_inf hQS hQK
  have hP2 : IsPGroup 2 P := hS2.to_le inf_le_left
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hPdvd : Nat.card P ∣ Nat.card K := card_dvd_of_le inf_le_right
  have hkle : k ≤ (Nat.card K).factorization 2 := by
    rw [hk] at hPdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hPdvd
  have hcard : Nat.card P ≤ Nat.card Q := by
    rw [hk, hQcard]
    exact Nat.pow_le_pow_right (by norm_num) hkle
  have hPQ : P = Q := (Subgroup.eq_of_le_of_card_ge hQP hcard).symm
  intro y hy
  rw [mem_normalizer_iff]
  intro q
  have hyH : y ∈ H := hSH hy
  have hyM : y ∈ normalizer (M : Set X) := hHN hyH
  constructor
  · intro hq
    rw [← hPQ] at hq ⊢
    obtain ⟨hqS, hqHK⟩ := mem_inf.mp hq
    obtain ⟨hqH, hqK⟩ := mem_inf.mp hqHK
    exact mem_inf.mpr ⟨mul_mem (mul_mem hy hqS) (inv_mem hy), mem_inf.mpr
      ⟨mul_mem (mul_mem hyH hqH) (inv_mem hyH), UnbalancedLayer.conj_mem_coreActionKernel hyM hqK⟩⟩
  · intro hq
    rw [← hPQ] at hq ⊢
    obtain ⟨hqS, hqHK⟩ := mem_inf.mp hq
    obtain ⟨hqH, hqK⟩ := mem_inf.mp hqHK
    have h1 : q = y⁻¹ * (y * q * y⁻¹) * y⁻¹⁻¹ := by group
    rw [h1]
    exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hy) hqS) (inv_mem (inv_mem hy)), mem_inf.mpr
      ⟨mul_mem (mul_mem (inv_mem hyH) hqH) (inv_mem (inv_mem hyH)),
        UnbalancedLayer.conj_mem_coreActionKernel (inv_mem hyM) hqK⟩⟩

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem centralizer_le_of_commute_of_kernel (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hsup : J ⊔ FooteLit.oddCoreIn M = M) {z : X} (hz : orderOf z = 2)
    (hzt : z * t = t * z) (hzK : z ∈ UnbalancedLayer.coreActionKernel M) :
    centralizer ({z} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  have hzC : z ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr hzt
  have hzN : z ∈ normalizer (J : Set X) := S.centralizer_le_normalizer hT13 hML hSch hzC
  exact S.centralizer_le_of_kernel h33 h35 hT13 hML hSch hz hzC
    (mem_coreActionKernel_of_normalizer_of_sup hsup hzN hzK)

theorem exists_conj_central (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) {M : Subgroup X}
    (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hScard : Nat.card Sc =
      2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2) :
    ∃ h ∈ normalizer (Sol78.signalizerCompletion E E : Set X), h * t * h⁻¹ ∈ Sc ∧
      ∀ y ∈ Sc, y * (h * t * h⁻¹) = h * t * h⁻¹ * y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hQ1 : Q ≠ ⊥ := by
    intro h
    have h1 := htQ
    rw [h, mem_bot] at h1
    have h2 := S.pair.1.1
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨z, hzQ, hzo, hzc⟩ := exists_involution_inf_centralizer hS2 hQS
    (le_normalizer_of_sylow_kernel hHN hQK hQcard hQS hSH hS2) hQ1
  have hzt : z * t = t * z := (hzc t (hQS htQ)).symm
  have hzH : z ∈ H := (hQK hzQ).1
  have hzK : z ∈ UnbalancedLayer.coreActionKernel M := (hQK hzQ).2
  have hCz := S.centralizer_le_of_commute_of_kernel h33 h35 hT13 hML hSch hsup hzo hzt hzK
  have hz2 : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  obtain ⟨L, -, hLC, hLpc, -, ⟨θL, -⟩, hLN⟩ := exists_layer_of_kernel hMH hMpc θ hzH hzK hz2 hCz
  have hmaxL := S.pair.2.2.2.2.1 z L ⟨hzo, hLC, hLpc, ⟨θL⟩⟩
  have hScL : Sc ≤ normalizer (L : Set X) := fun y hy => hLN y (hHN (hSH hy)) (hzc y hy)
  have hdvd : Nat.card Sc ∣ Nat.card (normalizer (L : Set X)) := card_dvd_of_le hScL
  rw [hScard] at hdvd
  have h1 : (Nat.card H).factorization 2 ≤ (Nat.card (normalizer (L : Set X))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have hNJH : normalizer (J : Set X) ≤ H := S.normalizer_le_normalizer_completion h33 h35
  have h2 : (Nat.card (normalizer (J : Set X))).factorization 2 ≤ (Nat.card H).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr (card_dvd_of_le hNJH) 2
  obtain ⟨S₀, hS₀N, -, hS₀card, htS₀, hS₀C⟩ := S.pair.2.2.2.2.2
  have hS₀card' : Nat.card S₀ = 2 ^ (Nat.card H).factorization 2 := by
    rw [hS₀card]
    congr 1
    omega
  obtain ⟨h, hhH, hh⟩ := HSFLit.exists_conj_eq_of_card_eq (hS₀N.trans hNJH) hSH hS₀card' hScard
  refine ⟨h, hhH, ?_, fun y hy => ?_⟩
  · rw [← hh]
    exact ⟨t, htS₀, by simp [MulAut.conj_apply]⟩
  rw [← hh] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  have h3 : y₀ * t = t * y₀ := mem_centralizer_singleton_iff.mp (hS₀C hy₀)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc h * y₀ * h⁻¹ * (h * t * h⁻¹) = h * (y₀ * t) * h⁻¹ := by group
    _ = h * (t * y₀) * h⁻¹ := by rw [h3]
    _ = h * t * h⁻¹ * (h * y₀ * h⁻¹) := by group

theorem centralizer_le_of_mem_sylow_kernel (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hScard : Nat.card Sc =
      2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X))).factorization 2)
    {y : X} (hyQ : y ∈ Q) (hy : orderOf y = 2) :
    centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨h, hhH, -, hh⟩ := S.exists_conj_central h33 h35 hT13 hML hSch hMH hMpc hHN θ hsup hQK
    hQcard htQ hQS hSH hS2 hScard
  have hyt : y * (h * t * h⁻¹) = h * t * h⁻¹ * y := hh y (hQS hyQ)
  have hy't : h⁻¹ * y * h * t = t * (h⁻¹ * y * h) := by
    calc h⁻¹ * y * h * t = h⁻¹ * (y * (h * t * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * t * h⁻¹ * y) * h := by rw [hyt]
      _ = t * (h⁻¹ * y * h) := by group
  have hy'o : orderOf (h⁻¹ * y * h) = 2 := by
    rw [show h⁻¹ * y * h = MulAut.conj h⁻¹ y by simp, MulEquiv.orderOf_eq]
    exact hy
  have hy'K : h⁻¹ * y * h ∈ UnbalancedLayer.coreActionKernel M := by
    have h1 := UnbalancedLayer.conj_mem_coreActionKernel (hHN (inv_mem hhH)) (hQK hyQ).2
    rwa [inv_inv] at h1
  have hC := S.centralizer_le_of_commute_of_kernel h33 h35 hT13 hML hSch hsup hy'o hy't hy'K
  intro x hx
  have hxy : x * y = y * x := mem_centralizer_singleton_iff.mp hx
  have hx' : h⁻¹ * x * h ∈ centralizer ({h⁻¹ * y * h} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc h⁻¹ * x * h * (h⁻¹ * y * h) = h⁻¹ * (x * y) * h := by group
      _ = h⁻¹ * (y * x) * h := by rw [hxy]
      _ = h⁻¹ * y * h * (h⁻¹ * x * h) := by group
  have h1 := mul_mem (mul_mem hhH (hC hx')) (inv_mem hhH)
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
