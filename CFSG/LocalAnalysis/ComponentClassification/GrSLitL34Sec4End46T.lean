module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46T
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_mul_of_card_omegaOne_le_four {Z : Subgroup G}
    (h4 : Nat.card ↥(omegaOne Z) ≤ 4) {p q r : G} (hp : p ∈ Z) (hq : q ∈ Z) (hr : r ∈ Z)
    (hpp : p * p = 1) (hqq : q * q = 1) (hrr : r * r = 1) (hp1 : p ≠ 1) (hq1 : q ≠ 1)
    (hr1 : r ≠ 1) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : r = p * q := by
  classical
  by_contra hne
  have hmem : ∀ w, w ∈ Z → w * w = 1 → w ∈ omegaOne Z := fun w hw hww =>
    subset_closure ⟨hw, hww⟩
  have hpqO : p * q ∈ omegaOne Z := mul_mem (hmem p hp hpp) (hmem q hq hqq)
  have h1 : p * q ≠ 1 := fun h => hpq (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hqq])
  have h2 : p * q ≠ p := fun h => hq1 (mul_eq_left.mp h)
  have h3 : p * q ≠ q := fun h => hp1 (mul_eq_right.mp h)
  set s : Finset G := {1, p, q, p * q, r} with hs
  have hsub : (s : Set G) ⊆ (omegaOne Z : Set G) := by
    intro w hw
    simp only [hs, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hmem _ hp hpp
    · exact hmem _ hq hqq
    · exact hpqO
    · exact hmem _ hr hrr
  have hcard : s.card = 5 := by
    rw [hs, Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hp1.symm, hq1.symm, h1.symm, hr1.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hpq, h2.symm, hpr⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h3.symm, hqr⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun h => hne h.symm),
      Finset.card_singleton]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  have : Nat.card ↥(omegaOne Z : Set G) = Nat.card ↥(omegaOne Z) := rfl
  omega

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34Lemma46StrongStep_of_two (hRank : L34CenterRankFact) (hTwo : L34Lemma46TwoStep) :
    L34Lemma46StrongStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl hZS y
    hyS z hzS hy hz hyz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := id hset
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hperf : ⁅J, J⁆ = J := GSThmB.commutator_eq_self_of_isPComponent hJa hJc
  have h4 : Nat.card ↥(omegaOne (S ⊓ zStarIn J)) ≤ 4 := by
    have h := hRank G J (S ⊓ J) hperf hL34 (GrS4.isSylowTwoIn_inf hS)
    rwa [inf_assoc, inf_of_le_right (show zStarIn J ≤ J from map_subtype_le _)] at h
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hinv : ∀ w : G, (∃ g : G, w = g⁻¹ * a * g) → w * w = 1 := by
    rintro w ⟨g, rfl⟩
    rw [show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  have hne1 : ∀ w : G, (∃ g : G, w = g⁻¹ * a * g) → w ≠ 1 := by
    rintro w ⟨g, rfl⟩ h
    apply ha1
    rw [show a = g * (g⁻¹ * a * g) * g⁻¹ by group, h]
    group
  have hZm : ∀ w ∈ S, (∃ g : G, w = g⁻¹ * a * g) → w ∈ S ⊓ zStarIn J := fun w hw hwa =>
    mem_inf.mpr ⟨hw, hZS w hw hwa⟩
  have haa' : ∃ g : G, a = g⁻¹ * a * g := ⟨1, by group⟩
  have haZ := hZm a haS haa'
  have hZab : ∀ s ∈ S ⊓ zStarIn J, ∀ t ∈ S ⊓ zStarIn J, s * t = t * s := by
    intro s hs t ht
    have hsK : s ∈ coreActionKernel J := by
      have h := (mem_inf.mp hs).2
      have hzs : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
      rw [hzs] at h
      exact (mem_inf.mp h).2
    have htJ : t ∈ J := map_subtype_le _ (mem_inf.mp ht).2
    have hc := (mem_coreActionKernel.mp hsK).2 t htJ
    have hcS : t⁻¹ * s⁻¹ * t * s ∈ S :=
      mul_mem (mul_mem (mul_mem (inv_mem (mem_inf.mp ht).1) (inv_mem (mem_inf.mp hs).1))
        (mem_inf.mp ht).1) (mem_inf.mp hs).1
    have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥J).map J.subtype)) :=
      odd_card_map_pPrimeCore J
    have h2 : IsPGroup 2 ↥S := GrS4.isPGroup_of_isSylowTwoIn hS
    have h1 : t⁻¹ * s⁻¹ * t * s = 1 := by
      have hS2 : IsPGroup 2 ↥(S ⊓ (pPrimeCore 2 ↥J).map J.subtype) := h2.to_le inf_le_left
      have hco := hodd.of_dvd_nat (card_dvd_of_le (inf_le_right :
        S ⊓ (pPrimeCore 2 ↥J).map J.subtype ≤ (pPrimeCore 2 ↥J).map J.subtype))
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      rw [hk] at hco
      have hk0 : k = 0 := by
        by_contra hk0
        exact (Nat.not_even_iff_odd.mpr hco) ((Nat.even_pow' hk0).mpr even_two)
      rw [hk0, pow_zero] at hk
      have hmem : t⁻¹ * s⁻¹ * t * s ∈ S ⊓ (pPrimeCore 2 ↥J).map J.subtype := mem_inf.mpr ⟨hcS, hc⟩
      have hbot := (card_eq_one.mp hk)
      rw [hbot, mem_bot] at hmem
      exact hmem
    calc s * t = s * t * (t⁻¹ * s⁻¹ * t * s) := by rw [h1, mul_one]
      _ = t * s := by group
  have key := fun {p q r : G} (hp : p ∈ S ⊓ zStarIn J) (hq : q ∈ S ⊓ zStarIn J)
      (hr : r ∈ S ⊓ zStarIn J) (hpp : p * p = 1) (hqq : q * q = 1) (hrr : r * r = 1)
      (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hr1 : r ≠ 1) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) =>
    GrS4.eq_mul_of_card_omegaOne_le_four h4 hp hq hr hpp hqq hrr hp1 hq1 hr1 hpq hpr hqr
  have main : ∀ b ∈ S, (∃ g : G, b = g⁻¹ * a * g) → b ≠ a →
      ¬ (∃ g : G, a * b = g⁻¹ * a * g) → False := by
    intro b hbS hb hba hab
    have hbZ := hZm b hbS hb
    have hD : ∀ w ∈ S, (∃ g : G, w = g⁻¹ * a * g) → w = a ∨ w = b := by
      intro w hwS hwa
      by_contra hw
      rw [not_or] at hw
      have hwab := key haZ hbZ (hZm w hwS hwa) haa (hinv b hb) (hinv w hwa) ha1 (hne1 b hb)
        (hne1 w hwa) (Ne.symm hba) (Ne.symm hw.1) (Ne.symm hw.2)
      exact hab (hwab ▸ hwa)
    have hbc : ∀ s ∈ S, s * b = b * s := by
      intro s hs
      have hsb : s⁻¹ * b * s ∈ S := mul_mem (mul_mem (inv_mem hs) hbS) hs
      obtain ⟨g, hg⟩ := hb
      rcases hD _ hsb ⟨g * s, by rw [hg]; group⟩ with h | h
      · exfalso
        apply hba
        calc b = s * (s⁻¹ * b * s) * s⁻¹ := by group
          _ = s * a * s⁻¹ := by rw [h]
          _ = a := by rw [hcent s hs, mul_inv_cancel_right]
      · calc s * b = s * (s⁻¹ * b * s) := by rw [h]
          _ = b * s := by group
    obtain ⟨P, hPS⟩ := hSyl
    obtain ⟨g, hg⟩ := hb
    have hxP : a ∈ centralizer ((P : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro s hs
      rw [hPS] at hs
      exact hcent s hs
    have hyP : g⁻¹ * a * g ∈ centralizer ((P : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro s hs
      rw [hPS] at hs
      rw [← hg]
      exact hbc s hs
    obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem_centralizer P a g hxP hyP
    have hn' : n ∈ normalizer (S : Set G) := by
      rw [← hPS]
      exact hn
    exact hTwo G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS ⟨P, hPS⟩
      hZS b hbS ⟨g, hg⟩ hba hD hbc ⟨n, hn', hg.trans hgn⟩
  by_cases hay : a = y
  · subst hay
    exact main z hzS hz (Ne.symm hyz) hno
  · by_cases haz : a = z
    · subst haz
      refine main y hyS hy (Ne.symm hay) fun ⟨g, hg⟩ => hno ⟨g, ?_⟩
      rw [← hg, hZab _ (hZm y hyS hy) _ haZ]
    · have h := key (hZm y hyS hy) (hZm z hzS hz) haZ (hinv y hy) (hinv z hz) haa (hne1 y hy)
        (hne1 z hz) ha1 hyz (Ne.symm hay) (Ne.symm haz)
      exact hno ⟨1, by rw [← h]; group⟩

end CFSG.ComponentClassification.GrSLit
