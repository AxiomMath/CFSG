module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleRank
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.Single

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem diagonal_false_of_involution (hMax : MaximalTwoComponentInput) {a : X}
    {J W K : Subgroup X} (hg : GSMaximalSetting X a J)
    (hNJ : normalizer (J : Set X) ≤ normalizer (W : Set X)) (hKM : K ≤ normalizer (W : Set X))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set X)))) (hKa : conjugate K a ≠ K)
    (hJKK : J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set X))) {s : X}
    (hs2 : orderOf s = 2) (hJs : J ≤ centralizer ({s} : Set X)) (hsK : s ∈ coreActionKernel K)
    (hsK' : s ∈ coreActionKernel (conjugate K a)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup X := normalizer (W : Set X) with hM
  set K' : Subgroup X := conjugate K a with hK'
  set Cs : Subgroup X := centralizer ({s} : Set X) with hCs
  have hJa : J ≤ centralizer ({a} : Set X) := hg.le_centralizer
  have hJc := hg.isPComponent
  have hCaM : centralizer ({a} : Set X) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hg).trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  have hJM : J ≤ M := hJa.trans hCaM
  have hK'M : K' ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM haM
  have hK'c : IsPComponent 2 (K'.subgroupOf M) :=
    UnbalancedCorr.isPComponent_conjugate_subgroupOf haM hKc
  have hne : K ≠ K' := fun e => hKa e.symm
  have hKK' : ⁅K, K'⁆ ≤ oddIn K ⊓ oddIn K' :=
    GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne
  have hK'NK : K' ≤ normalizer (K : Set X) := (GrS5.commutator_le_of_ne hKM hK'M hKc hK'c hne).2
  have hKNK' : K ≤ normalizer (K' : Set X) :=
    (GrS5.commutator_le_of_ne hK'M hKM hK'c hKc hne.symm).2
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hOK' : oddIn K' ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hK'M hK'c
  have hOMK : oddIn M ≤ normalizer (K : Set X) := GrS4.oddIn_le_normalizer_of_isPComponent hKM hKc
  have hOMK' : oddIn M ≤ normalizer (K' : Set X) :=
    GrS4.oddIn_le_normalizer_of_isPComponent hK'M hK'c
  have hJNK : J ≤ normalizer (K : Set X) :=
    hJKK.trans (sup_le (sup_le le_normalizer hK'NK) hOMK)
  have hJNK' : J ≤ normalizer (K' : Set X) :=
    hJKK.trans (sup_le (sup_le hKNK' le_normalizer) hOMK')
  have haa : a * a = 1 := by rw [← pow_two, ← hg.orderOf_eq, pow_orderOf_eq_one]
  have hJnot : ¬ J ≤ coreActionKernel K := fun h => not_le_coreActionKernel_of_diagonal hJa hJc
    hJM hKM hK'M hJNK hJNK' hOK hOK' hJKK haa (Or.inl h)
  have hJnot' : ¬ J ≤ coreActionKernel K' := fun h => not_le_coreActionKernel_of_diagonal hJa hJc
    hJM hKM hK'M hJNK hJNK' hOK hOK' hJKK haa (Or.inr h)
  obtain ⟨hsF, hnF, hoF⟩ := GrS4.fstar_facts_of_gsMaximalSetting hg
  have : IsSimpleGroup X := hg.simple
  have h29 := (hMax X hsF hnF hoF hg.kProper J hg.maximal (by have := hg.rank; omega)
    hg.not_sp4 hg.type s hs2 hJs).1
  set R : Subgroup X := oddIn Cs with hR
  have hconj : ∀ g ∈ Cs, conjugate J g ≤ R ⊔ J := fun g hg' =>
    (le_iSup₂_of_le g (UnbalancedCorr.conjugate_le_of_mem hJs hg') le_rfl).trans h29
  have hJR : J ≤ normalizer (R : Set X) := hJs.trans (GrS4.self_le_normalizer_oddIn Cs)
  set D : Subgroup X := (R ⊓ M) ⊔ oddIn M with hD
  set N₀ : Subgroup X := D ⊔ oddIn J with hN₀
  have hRModd : Odd (Nat.card ↥(R ⊓ M)) :=
    (UnbalancedCorr.odd_card_map_pPrimeCore Cs).of_dvd_nat (card_dvd_of_le inf_le_left)
  have hDodd : Odd (Nat.card D) := odd_card_sup hRModd (UnbalancedCorr.odd_card_map_pPrimeCore M)
    (inf_le_right.trans (GrS4.self_le_normalizer_oddIn M))
  have hJD : J ≤ normalizer (D : Set X) := fun j hj =>
    mem_normalizer_sup (mem_normalizer_inf (hJR hj) (le_normalizer (hJM hj)))
      (GrS4.self_le_normalizer_oddIn M (hJM hj))
  have hN₀odd : Odd (Nat.card N₀) := by
    rw [hN₀, sup_comm]
    exact odd_card_sup (UnbalancedCorr.odd_card_map_pPrimeCore J) hDodd
      ((map_subtype_le _).trans hJD)
  have hJN₀ : J ≤ normalizer (N₀ : Set X) := fun j hj =>
    mem_normalizer_sup (hJD hj) (GrS4.self_le_normalizer_oddIn J hj)
  set Y : Subgroup X := J ⊔ N₀ with hY
  have hYN : Y ≤ normalizer (N₀ : Set X) := sup_le hJN₀ le_normalizer
  have hOJN : oddIn J ≤ N₀ := le_sup_right
  have hOMN : oddIn M ≤ N₀ := le_sup_right.trans le_sup_left
  have hsP : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
  have hcomm : ∀ g ∈ M ⊓ centralizer (zpowers s : Set X), ∀ j ∈ J,
      g⁻¹ * j * g * j⁻¹ ∈ Y := by
    intro g hg' j hj
    have hgs : g ∈ Cs := mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hg'.2 s (mem_zpowers s)).symm)
    have h1 : g⁻¹ * j * g * j⁻¹ ∈ R ⊔ J :=
      mul_mem (hconj g hgs (UnbalancedLayer.conj_mem_conjugate hj g))
        (mem_sup_right (inv_mem hj))
    have h2 : g⁻¹ * j * g * j⁻¹ ∈ M :=
      mul_mem (mul_mem (mul_mem (inv_mem hg'.1) (hJM hj)) hg'.1) (inv_mem (hJM hj))
    rw [sup_comm] at h1
    obtain ⟨j', hj', r, hr, hjr⟩ := exists_mul_of_mem_sup hJR h1
    have hrM : r ∈ M := by
      have := mul_mem (inv_mem (hJM hj')) h2
      rwa [hjr, inv_mul_cancel_left] at this
    rw [hjr]
    exact mul_mem (mem_sup_left hj') (mem_sup_right (mem_sup_left (mem_sup_left ⟨hr, hrM⟩)))
  have hOY : ∀ L : Subgroup X, oddIn L ≤ oddIn M → oddIn L ≤ Y := fun L hL =>
    hL.trans (hOMN.trans le_sup_right)
  have hKY : K ≤ Y := le_of_commutator_mem hKM hKc hsP hsK hJNK hJnot
    (fun g hg' j hj => hcomm g ⟨hKM hg'.1, hg'.2⟩ j hj) (hOY K hOK)
  have hK'Y : K' ≤ Y := le_of_commutator_mem hK'M hK'c hsP hsK' hJNK' hJnot'
    (fun g hg' j hj => hcomm g ⟨hK'M hg'.1, hg'.2⟩ j hj) (hOY K' hOK')
  have hnot : ∀ {L H : Subgroup X}, L ≤ H → IsPComponent 2 (L.subgroupOf H) → ¬ L ≤ N₀ :=
    fun hLH hL hLN =>
      GrS4.not_odd_card_of_isPComponent hLH hL (hN₀odd.of_dvd_nat (card_dvd_of_le hLN))
  have hcase : ∀ L : Subgroup X, L ≤ Y → J ≤ normalizer (L : Set X) → ⁅L, L⁆ = L →
      ¬ L ≤ N₀ → J ≤ L ⊔ N₀ := by
    intro L hLY hJL hLp hLN
    have hJP : J ≤ normalizer ((J ⊓ (L ⊔ N₀) : Subgroup X) : Set X) := fun j hj =>
      mem_normalizer_inf (le_normalizer hj) (mem_normalizer_sup (hJL hj) (hJN₀ hj))
    have hOP : oddIn J ≤ J ⊓ (L ⊔ N₀) := le_inf (map_subtype_le _) (hOJN.trans le_sup_right)
    rcases eq_or_commutator_le_oddIn hJa hJc inf_le_left hJP hOP with h | h
    · rw [← h]
      exact inf_le_right
    · exfalso
      apply hLN
      rw [← hLp, commutator_le]
      intro l₁ hl₁ l₂ hl₂
      obtain ⟨j₁, hj₁, n₁, hn₁, rfl⟩ := exists_mul_of_mem_sup hJN₀ (hLY hl₁)
      obtain ⟨j₂, hj₂, n₂, hn₂, rfl⟩ := exists_mul_of_mem_sup hJN₀ (hLY hl₂)
      rw [commutatorElement_mul_mem_iff (hJN₀ hj₁) (hJN₀ hj₂) hn₁ hn₂]
      have hj₂P : j₂ ∈ J ⊓ (L ⊔ N₀) := ⟨hj₂, by
        have := mul_mem (mem_sup_left hl₂ : j₂ * n₂ ∈ L ⊔ N₀) (mem_sup_right (inv_mem hn₂))
        rwa [mul_inv_cancel_right] at this⟩
      exact hOJN (h (commutator_mem_commutator hj₁ hj₂P))
  have hJK₁ := hcase K hKY hJNK (GSThmB.commutator_eq_self_of_isPComponent hKM hKc)
    (hnot hKM hKc)
  have hJK₂ := hcase K' hK'Y hJNK' (GSThmB.commutator_eq_self_of_isPComponent hK'M hK'c)
    (hnot hK'M hK'c)
  apply hnot hJa hJc
  rw [← GSThmB.commutator_eq_self_of_isPComponent hJa hJc, commutator_le]
  intro j₁ hj₁ j₂ hj₂
  obtain ⟨k, hk, n, hn, rfl⟩ := exists_mul_of_mem_sup (hKY.trans hYN) (hJK₁ hj₁)
  obtain ⟨k', hk', n', hn', rfl⟩ := exists_mul_of_mem_sup (hK'Y.trans hYN) (hJK₂ hj₂)
  rw [commutatorElement_mul_mem_iff (hYN (hKY hk)) (hYN (hK'Y hk')) hn hn']
  exact hOMN (hOK (hKK' (commutator_mem_commutator hk hk')).1)

theorem exists_involution_of_two_subgroup (hMax : MaximalTwoComponentInput) {a : X}
    {J W K : Subgroup X} (hg : GSMaximalSetting X a J)
    (hNJ : normalizer (J : Set X) ≤ normalizer (W : Set X)) (hKM : K ≤ normalizer (W : Set X))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set X)))) (hKa : conjugate K a ≠ K)
    (hJKK : J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set X))) {T : Subgroup X}
    (hTC : T ≤ centralizer (J : Set X)) (hT2 : IsPGroup 2 T) (hT4 : 4 ≤ Nat.card T) :
    ∃ s : X, orderOf s = 2 ∧ J ≤ centralizer ({s} : Set X) ∧ s ∈ coreActionKernel K ∧
      s ∈ coreActionKernel (conjugate K a) := by
  set M : Subgroup X := normalizer (W : Set X) with hM
  have hJa : J ≤ centralizer ({a} : Set X) := hg.le_centralizer
  have hJc := hg.isPComponent
  have hCaM : centralizer ({a} : Set X) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hg).trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  have hJM : J ≤ M := hJa.trans hCaM
  have hK'M : conjugate K a ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM haM
  have hK'c := UnbalancedCorr.isPComponent_conjugate_subgroupOf haM hKc
  have hne : K ≠ conjugate K a := fun e => hKa e.symm
  have haa : a * a = 1 := by rw [← pow_two, ← hg.orderOf_eq, pow_orderOf_eq_one]
  have hK'NK := (GrS5.commutator_le_of_ne hKM hK'M hKc hK'c hne).2
  have hKNK' := (GrS5.commutator_le_of_ne hK'M hKM hK'c hKc hne.symm).2
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hOK' : oddIn (conjugate K a) ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hK'M hK'c
  have hOMK := GrS4.oddIn_le_normalizer_of_isPComponent hKM hKc
  have hOMK' := GrS4.oddIn_le_normalizer_of_isPComponent hK'M hK'c
  have hJNK : J ≤ normalizer (K : Set X) := hJKK.trans (sup_le (sup_le le_normalizer hK'NK) hOMK)
  have hJNK' : J ≤ normalizer ((conjugate K a : Subgroup X) : Set X) :=
    hJKK.trans (sup_le (sup_le hKNK' le_normalizer) hOMK')
  have hJnot : ¬ J ≤ coreActionKernel K := fun h => not_le_coreActionKernel_of_diagonal hJa hJc
    hJM hKM hK'M hJNK hJNK' hOK hOK' hJKK haa (Or.inl h)
  have hJnot' : ¬ J ≤ coreActionKernel (conjugate K a) := fun h =>
    not_le_coreActionKernel_of_diagonal hJa hJc hJM hKM hK'M hJNK hJNK' hOK hOK' hJKK haa
      (Or.inr h)
  have hJKK' : J ≤ conjugate K a ⊔ K ⊔ oddIn M := by rw [sup_comm (conjugate K a) K]; exact hJKK
  have hCJM : ∀ t : X, J ≤ centralizer ({t} : Set X) → t ∈ M := fun t ht =>
    hNJ (mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer ht))
  have hTJ : ∀ t ∈ T, J ≤ centralizer ({t} : Set X) := fun t ht j hj =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hTC ht) j hj)
  have horb : ∀ t ∈ T, conjugate K t = K ∨ conjugate K t = conjugate K a := fun t ht =>
    conjugate_eq_or_eq_of_le_centralizer hKM hK'M hKc hK'c hne hJKK hJnot hJnot'
      (hCJM t (hTJ t ht)) (hTJ t ht)
  obtain ⟨s, hsT, hs2, hsK⟩ := exists_involution_mem_normalizer hT2 hT4 horb
  have hJs := hTJ s hsT
  have hsK' : s ∈ normalizer ((conjugate K a : Subgroup X) : Set X) := by
    rcases conjugate_eq_or_eq_of_le_centralizer hK'M hKM hK'c hKc hne.symm hJKK' hJnot' hJnot
      (hCJM s hJs) hJs with h | h
    · exact mem_normalizer_of_conjugate_eq h
    · exfalso
      apply hne
      have h2 : conjugate K s = K := conjugate_eq_of_mem_normalizer hsK
      have h3 := congrArg (fun H => conjugate H s⁻¹) (h.trans h2.symm)
      simp only [conjugate_conjugate_inv] at h3
      exact h3.symm
  have hK'a : conjugate (conjugate K a) a = K := by
    rw [conjugate_conjugate, haa, conjugate_one]
  exact ⟨s, hs2, hJs, mem_coreActionKernel_of_diagonal hMax hg hNJ hKM hKc rfl hne hJKK hJs hsK
    hsK', mem_coreActionKernel_of_diagonal hMax hg hNJ hK'M hK'c hK'a hne.symm hJKK' hJs hsK'
    hsK⟩

theorem diagonal_false_of_two_subgroup (hMax : MaximalTwoComponentInput) {a : X}
    {J W K : Subgroup X} (hg : GSMaximalSetting X a J)
    (hNJ : normalizer (J : Set X) ≤ normalizer (W : Set X)) (hKM : K ≤ normalizer (W : Set X))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set X)))) (hKa : conjugate K a ≠ K)
    (hJKK : J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set X))) {T : Subgroup X}
    (hTC : T ≤ centralizer (J : Set X)) (hT2 : IsPGroup 2 T) (hT4 : 4 ≤ Nat.card T) : False := by
  obtain ⟨s, hs2, hJs, hsK, hsK'⟩ :=
    exists_involution_of_two_subgroup hMax hg hNJ hKM hKc hKa hJKK hTC hT2 hT4
  exact diagonal_false_of_involution hMax hg hNJ hKM hKc hKa hJKK hs2 hJs hsK hsK'

end CFSG.ComponentClassification.GrSLit.Single
