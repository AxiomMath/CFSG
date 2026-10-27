module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L127Syl
public import CFSG.Goldschmidt.Steps.G310Basic

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L121

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold conjugate
  rw [Subgroup.mem_map_equiv]
  simp

theorem sylowIn_of_maxSInv {S H V K : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hV : MaxSInv 3 S H V) (hKH : K ≤ H) (hVK : V ≤ K) (hKodd : ¬ 2 ∣ Nat.card ↥K)
    (hSK : S ≤ normalizer (K : Set G)) :
    CFSG.Open.fusionIsSylowIn 3 V K := by
  obtain ⟨hVH, hV3, hSV, hmax⟩ := hV
  obtain ⟨P, hP, hVP, hSP⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_two Nat.prime_three hS2 hKodd hSK hVK hV3 hSV
  have hPV : P = V := hmax P (hP.1.trans hKH) hP.2.1 hSP hVP
  subst hPV
  exact hP

omit [Finite G] in
theorem inv_conjugate {r : ℕ} {S H W : Subgroup G} (hWH : W ≤ H) (hW3 : IsPGroup r ↥W)
    (hSW : S ≤ normalizer (W : Set G)) {c : G} (hcH : c ∈ H) (hcS : c ∈ centralizer (S : Set G)) :
    conjugate W c ≤ H ∧ IsPGroup r ↥(conjugate W c) ∧ S ≤ normalizer ((conjugate W c : Subgroup G) : Set G) := by
  have hcomm : ∀ s ∈ S, c * s = s * c := fun s hs =>
    (Subgroup.mem_centralizer_iff.mp hcS s hs).symm
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_conjugate_iff'] at hx
    have h1 : c * x * c⁻¹ ∈ H := hWH hx
    have h2 : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rw [h2]
    exact H.mul_mem (H.mul_mem (H.inv_mem hcH) h1) hcH
  · have hiso : conjugate W c = W.map (MulAut.conj c⁻¹).toMonoidHom := rfl
    rw [hiso]
    exact hW3.of_equiv (Subgroup.equivMapOfInjective W _ (MulAut.conj c⁻¹).injective)
  · intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_conjugate_iff', mem_conjugate_iff']
    have hs' : s ∈ normalizer (W : Set G) := hSW hs
    have e : c * (s * x * s⁻¹) * c⁻¹ = s * (c * x * c⁻¹) * s⁻¹ := by
      have h1 : c * s = s * c := hcomm s hs
      have h2 : s⁻¹ * c⁻¹ = c⁻¹ * s⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, h1]
      calc c * (s * x * s⁻¹) * c⁻¹ = (c * s) * x * (s⁻¹ * c⁻¹) := by group
        _ = (s * c) * x * (s⁻¹ * c⁻¹) := by rw [h1]
        _ = s * (c * x * c⁻¹) * s⁻¹ := by rw [h2]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hs' _)

omit [Finite G] in
theorem maxSInv_conjugate {r : ℕ} {S H V : Subgroup G} (hV : MaxSInv r S H V) {c : G}
    (hcH : c ∈ H) (hcS : c ∈ centralizer (S : Set G)) : MaxSInv r S H (conjugate V c) := by
  obtain ⟨hVH, hV3, hSV, hmax⟩ := hV
  obtain ⟨h1, h2, h3⟩ := inv_conjugate (r := r) (S := S) hVH hV3 hSV hcH hcS
  refine ⟨h1, h2, h3, ?_⟩
  intro W hWH hW3 hSW hle
  have hcinvS : c⁻¹ ∈ centralizer (S : Set G) := Subgroup.inv_mem _ hcS
  obtain ⟨k1, k2, k3⟩ := inv_conjugate (r := r) (S := S) hWH hW3 hSW (H.inv_mem hcH) hcinvS
  have hVW : V ≤ conjugate W c⁻¹ := by
    intro v hv
    rw [mem_conjugate_iff']
    have : c⁻¹ * v * c ∈ conjugate V c := by
      rw [mem_conjugate_iff']
      simpa [mul_assoc] using hv
    have h4 := hle this
    simpa using h4
  have hEq := hmax _ k1 k2 k3 hVW
  ext x
  constructor
  · intro hx
    rw [mem_conjugate_iff']
    have : c * x * c⁻¹ ∈ conjugate W c⁻¹ := by
      rw [mem_conjugate_iff']
      simpa [mul_assoc] using hx
    rw [hEq] at this
    exact this
  · intro hx
    exact hle hx

theorem conj_of_maxSInv {S H V V' K : Subgroup G} (hS2 : IsPGroup 2 ↥S)
    (hV : MaxSInv 3 S H V) (hV' : MaxSInv 3 S H V') (hKH : K ≤ H) (hVK : V ≤ K) (hV'K : V' ≤ K)
    (hKodd : ¬ 2 ∣ Nat.card ↥K) (hSK : S ≤ normalizer (K : Set G)) :
    ∃ c ∈ K ⊓ centralizer (S : Set G), V' = conjugate V c := by
  have h1 := sylowIn_of_maxSInv hS2 hV hKH hVK hKodd hSK
  have h2 := sylowIn_of_maxSInv hS2 hV' hKH hV'K hKodd hSK
  obtain ⟨c, hc, hV'eq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_two Nat.prime_three hS2 hKodd hSK h1 h2 hV.2.2.1 hV'.2.2.1
  refine ⟨c⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_inf.mpr ⟨K.inv_mem (Subgroup.mem_inf.mp hc).1,
      Subgroup.inv_mem _ (Subgroup.mem_inf.mp hc).2⟩
  · rw [hV'eq]
    show V.map (MulAut.conj c).toMonoidHom = V.map (MulAut.conj c⁻¹⁻¹).toMonoidHom
    rw [inv_inv]

omit [Finite G] in
theorem fusionIsSylowIn_of_card {W K : Subgroup G} [Finite K] (hWK : W ≤ K) (hW3 : IsPGroup 3 ↥W)
    (hcard : Nat.card ↥(W.subgroupOf K) = 3 ^ (Nat.card ↥K).factorization 3) :
    CFSG.Open.fusionIsSylowIn 3 W K := by
  refine ⟨hWK, hW3, fun P hPK hP3 hWP => ?_⟩
  have : Finite ↥P := Finite.of_injective (Subgroup.inclusion hPK) (Subgroup.inclusion_injective hPK)
  obtain ⟨n, hn⟩ := hP3.exists_card_eq
  have hdvd : Nat.card ↥P ∣ Nat.card ↥K := Subgroup.card_dvd_of_le hPK
  have hle : n ≤ (Nat.card ↥K).factorization 3 := by
    rw [hn] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hdvd
  have hWcard : Nat.card ↥W = 3 ^ (Nat.card ↥K).factorization 3 := by
    rw [← hcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv]
  have hle2 : Nat.card ↥P ≤ Nat.card ↥W := by
    rw [hn, hWcard]
    exact Nat.pow_le_pow_right (by norm_num) hle
  exact (Subgroup.eq_of_le_of_card_ge hWP hle2).symm

theorem le_of_mixed {S H V V' : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hSH : S ≤ H)
    (hV : MaxSInv 3 S H V) (hV' : MaxSInv 3 S H V') (hVO : V ≤ pPrimeCoreOf 2 H) :
    V' ≤ pPrimeCoreOf 2 H := by
  by_contra hV'O
  have hOH : pPrimeCoreOf 2 H ≤ H := CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_le H
  have hHO : H ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := le_normalizer_pPrimeCoreOf H
  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 H)) := odd_card_pPrimeCoreOf H
  have hOodd' : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 H) := fun h =>
    (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hSO : S ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := hSH.trans hHO
  have hcard := L127.inf_sylow_of_maximal hSH hS2 hV'.1 hV'.2.1 hV'.2.2.1 hV'.2.2.2
  have hsyl : CFSG.Open.fusionIsSylowIn 3 (V' ⊓ pPrimeCoreOf 2 H) (pPrimeCoreOf 2 H) :=
    fusionIsSylowIn_of_card inf_le_right (hV'.2.1.to_inf_left) hcard
  have hsylV := sylowIn_of_maxSInv hS2 hV hOH hVO hOodd' hSO
  have hSinf : S ≤ normalizer (((V' ⊓ pPrimeCoreOf 2 H : Subgroup G)) : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hV'.2.2.1 hs) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hSO hs) x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨h1.mp hx1, h2.mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨h1.mpr hx1, h2.mpr hx2⟩
  obtain ⟨c, hc, hEq⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_two Nat.prime_three hS2 hOodd' hSO hsylV hsyl hV.2.2.1 hSinf
  have hcH : c⁻¹ ∈ H := H.inv_mem (hOH (Subgroup.mem_inf.mp hc).1)
  have hcS : c⁻¹ ∈ centralizer (S : Set G) := Subgroup.inv_mem _ (Subgroup.mem_inf.mp hc).2
  have hmaxc := maxSInv_conjugate hV hcH hcS
  have hconj : conjugate V c⁻¹ = V' ⊓ pPrimeCoreOf 2 H := by
    rw [hEq]
    show V.map (MulAut.conj c⁻¹⁻¹).toMonoidHom = V.map (MulAut.conj c).toMonoidHom
    rw [inv_inv]
  have hle : conjugate V c⁻¹ ≤ V' := by rw [hconj]; exact inf_le_left
  have hEq2 := hmaxc.2.2.2 V' hV'.1 hV'.2.1 hV'.2.2.1 hle
  apply hV'O
  have h5 : V' = V' ⊓ pPrimeCoreOf 2 H := hEq2.trans hconj
  calc V' = V' ⊓ pPrimeCoreOf 2 H := h5
    _ ≤ pPrimeCoreOf 2 H := inf_le_right

theorem part_a {S H : Subgroup G} (hS2 : IsPGroup 2 ↥S) (hSH : S ≤ H)
    (huniq : ∀ V₁ V₂ : Subgroup G, MaxSInv 3 S H V₁ → MaxSInv 3 S H V₂ →
      ¬ V₁ ≤ pPrimeCoreOf 2 H → ¬ V₂ ≤ pPrimeCoreOf 2 H →
      pPrimeCoreOf 2 H ⊔ V₁ = pPrimeCoreOf 2 H ⊔ V₂)
    {V : Subgroup G} (hV : MaxSInv 3 S H V) :
    ∀ V' : Subgroup G, MaxSInv 3 S H V' → ∃ c ∈ H ⊓ centralizer (S : Set G), V' = conjugate V c := by
  intro V' hV'
  have hOH : pPrimeCoreOf 2 H ≤ H := CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_le H
  have hHO : H ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := le_normalizer_pPrimeCoreOf H
  have hOodd : Odd (Nat.card ↥(pPrimeCoreOf 2 H)) := odd_card_pPrimeCoreOf H
  have hOodd' : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 H) := fun h =>
    (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hSO : S ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := hSH.trans hHO
  by_cases hVO : V ≤ pPrimeCoreOf 2 H
  ·
    have hV'O : V' ≤ pPrimeCoreOf 2 H := le_of_mixed hS2 hSH hV hV' hVO
    obtain ⟨c, hc, hEq⟩ := conj_of_maxSInv hS2 hV hV' hOH hVO hV'O hOodd' hSO
    exact ⟨c, Subgroup.mem_inf.mpr ⟨hOH (Subgroup.mem_inf.mp hc).1, (Subgroup.mem_inf.mp hc).2⟩, hEq⟩
  · have hV'O : ¬ V' ≤ pPrimeCoreOf 2 H := fun h =>
      hVO (le_of_mixed hS2 hSH hV' hV h)
    have hKeq := huniq V V' hV hV' hVO hV'O
    have hRN : V ≤ normalizer ((pPrimeCoreOf 2 H : Subgroup G) : Set G) := hV.1.trans hHO
    have hKodd : Odd (Nat.card ↥(pPrimeCoreOf 2 H ⊔ V)) :=
      L127.odd_card_sup_of_normalizes hRN hOodd hV.2.1
    have hKodd' : ¬ 2 ∣ Nat.card ↥(pPrimeCoreOf 2 H ⊔ V) := fun h =>
      (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h)
    have hKH : pPrimeCoreOf 2 H ⊔ V ≤ H := sup_le hOH hV.1
    have hSK : S ≤ normalizer ((pPrimeCoreOf 2 H ⊔ V : Subgroup G) : Set G) := fun s hs =>
      Subgroup.inf_normalizer_le_normalizer_sup (pPrimeCoreOf 2 H) V ⟨hSO hs, hV.2.2.1 hs⟩
    have hV'K : V' ≤ pPrimeCoreOf 2 H ⊔ V := (le_sup_right : V' ≤ pPrimeCoreOf 2 H ⊔ V').trans hKeq.ge
    obtain ⟨c, hc, hEq⟩ := conj_of_maxSInv hS2 hV hV' hKH le_sup_right hV'K hKodd' hSK
    exact ⟨c, Subgroup.mem_inf.mpr ⟨hKH (Subgroup.mem_inf.mp hc).1, (Subgroup.mem_inf.mp hc).2⟩, hEq⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L121
