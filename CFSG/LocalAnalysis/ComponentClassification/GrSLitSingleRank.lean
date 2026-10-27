module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingle
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma41Outer
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.Single

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conjugate_eq_of_mem_normalizer {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : conjugate H g = H := by
  ext x
  rw [mem_conjugate_iff]
  exact (mem_normalizer_iff.mp hg x).symm

omit [Finite X] in
theorem conjugate_eq_self_of_le_centralizer {J : Subgroup X} {t : X}
    (ht : J ≤ centralizer ({t} : Set X)) : conjugate J t = J := by
  have hN : t ∈ normalizer (J : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← mem_centralizer_singleton_iff.mp (ht hh), mul_inv_cancel_right]
      exact hh
    · intro hh
      have hc := mem_centralizer_singleton_iff.mp (ht hh)
      have e : h = t * h * t⁻¹ := by
        calc h = t⁻¹ * ((t * h * t⁻¹) * t) := by group
          _ = t⁻¹ * (t * (t * h * t⁻¹)) := by rw [hc]
          _ = t * h * t⁻¹ := by group
      rw [e]
      exact hh
  exact conjugate_eq_of_mem_normalizer hN

omit [Finite X] in
theorem conjugate_sup (A B : Subgroup X) (g : X) :
    conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g :=
  Subgroup.map_sup A B _

theorem le_coreActionKernel_of_ne {M K L : Subgroup X} (hKM : K ≤ M) (hLM : L ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) (hL : IsPComponent 2 (L.subgroupOf M)) (hne : K ≠ L) :
    L ≤ coreActionKernel K := by
  have hc := GrS5.commutator_le_inf_oddIn hKM hLM hK hL hne
  have hN := (GrS5.commutator_le_of_ne hKM hLM hK hL hne).2
  intro x hx
  refine ⟨hN hx, fun k hk => ?_⟩
  have h1 := hc (commutator_mem_commutator (inv_mem hk) (inv_mem hx))
  rw [commutatorElement_def, inv_inv, inv_inv] at h1
  exact h1.1

theorem oddIn_le_coreActionKernel {M K : Subgroup X} (hKM : K ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) : oddIn M ≤ coreActionKernel K := by
  intro o ho
  have hoN := GrS4.oddIn_le_normalizer_of_isPComponent hKM hK ho
  refine ⟨hoN, fun k hk => ?_⟩
  have h1 : k⁻¹ * o⁻¹ * k * o ∈ oddIn M := by
    have := GrS4.conj_mem_oddIn (hKM (inv_mem hk)) (inv_mem ho)
    rw [inv_inv] at this
    exact mul_mem this ho
  have h2 : k⁻¹ * o⁻¹ * k * o ∈ K := by
    have := (mem_normalizer_iff.mp (inv_mem hoN) k).mp hk
    rw [inv_inv] at this
    rw [show k⁻¹ * o⁻¹ * k * o = k⁻¹ * (o⁻¹ * k * o) by group]
    exact mul_mem (inv_mem hk) this
  exact GrS5.inf_oddIn_le_oddIn hKM ⟨h1, h2⟩

theorem conjugate_eq_or_eq_of_le_centralizer {M J K K' : Subgroup X} (hKM : K ≤ M)
    (hK'M : K' ≤ M) (hK : IsPComponent 2 (K.subgroupOf M))
    (hK' : IsPComponent 2 (K'.subgroupOf M)) (hne : K ≠ K') (hJKK : J ≤ K ⊔ K' ⊔ oddIn M)
    (hJK : ¬ J ≤ coreActionKernel K) (hJK' : ¬ J ≤ coreActionKernel K') {t : X} (htM : t ∈ M)
    (ht : J ≤ centralizer ({t} : Set X)) : conjugate K t = K ∨ conjugate K t = K' := by
  have hLM : conjugate K t ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM htM
  have hL'M : conjugate K' t ≤ M := UnbalancedCorr.conjugate_le_of_mem hK'M htM
  have hL := UnbalancedCorr.isPComponent_conjugate_subgroupOf htM hK
  have hL' := UnbalancedCorr.isPComponent_conjugate_subgroupOf htM hK'
  have hJL : J ≤ conjugate K t ⊔ conjugate K' t ⊔ oddIn M := by
    have h1 : conjugate J t ≤ conjugate (K ⊔ K' ⊔ oddIn M) t := Subgroup.map_mono hJKK
    rwa [conjugate_eq_self_of_le_centralizer ht, conjugate_sup, conjugate_sup,
      conjugate_eq_of_mem_normalizer (GrS4.self_le_normalizer_oddIn M htM)] at h1
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hLK, hLK'⟩ := hcon
  by_cases hL'K : conjugate K' t = K
  · apply hJK'
    refine hJL.trans (sup_le (sup_le ?_ ?_) (oddIn_le_coreActionKernel hK'M hK'))
    · exact le_coreActionKernel_of_ne hK'M hLM hK' hL (Ne.symm hLK')
    · exact le_coreActionKernel_of_ne hK'M hL'M hK' hL' (by rw [hL'K]; exact hne.symm)
  · apply hJK
    refine hJL.trans (sup_le (sup_le ?_ ?_) (oddIn_le_coreActionKernel hKM hK))
    · exact le_coreActionKernel_of_ne hKM hLM hK hL (Ne.symm hLK)
    · exact le_coreActionKernel_of_ne hKM hL'M hK hL' (Ne.symm hL'K)

theorem exists_mem_ne_one_ne {T : Subgroup X} (hT : 3 ≤ Nat.card T) (u : X) :
    ∃ t ∈ T, t ≠ 1 ∧ t ≠ u := by
  by_contra h
  push Not at h
  have hsub : (T : Set X) ⊆ {1, u} := fun t ht => by
    by_cases h1 : t = 1
    · exact Or.inl h1
    · exact Or.inr (h t ht h1)
  have h1 : Nat.card T ≤ ({1, u} : Set X).ncard :=
    (Nat.card_coe_set_eq (T : Set X)).le.trans (Set.ncard_le_ncard hsub (Set.toFinite _))
  have h2 : ({1, u} : Set X).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : X) {u}
    rw [Set.ncard_singleton] at this
    exact this
  omega

theorem exists_involution_mem_normalizer {K K' T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hT4 : 4 ≤ Nat.card T) (horb : ∀ t ∈ T, conjugate K t = K ∨ conjugate K t = K') :
    ∃ s ∈ T, orderOf s = 2 ∧ s ∈ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₀ : Subgroup X := T ⊓ normalizer (K : Set X) with hT₀
  have hne : ∃ t ∈ T₀, t ≠ 1 := by
    by_cases hall : ∀ t ∈ T, t ∈ normalizer (K : Set X)
    · obtain ⟨t, ht, ht1, -⟩ := exists_mem_ne_one_ne (by omega : 3 ≤ Nat.card T) 1
      exact ⟨t, mem_inf.mpr ⟨ht, hall t ht⟩, ht1⟩
    · push Not at hall
      obtain ⟨t₂, ht₂, ht₂N⟩ := hall
      have h₂ : conjugate K t₂ = K' :=
        (horb t₂ ht₂).resolve_left fun h => ht₂N (mem_normalizer_of_conjugate_eq h)
      obtain ⟨t₁, ht₁, ht₁1, ht₁₂⟩ := exists_mem_ne_one_ne (by omega : 3 ≤ Nat.card T) t₂
      by_cases ht₁N : t₁ ∈ normalizer (K : Set X)
      · exact ⟨t₁, mem_inf.mpr ⟨ht₁, ht₁N⟩, ht₁1⟩
      · have h₁ : conjugate K t₁ = K' :=
          (horb t₁ ht₁).resolve_left fun h => ht₁N (mem_normalizer_of_conjugate_eq h)
        refine ⟨t₁ * t₂⁻¹, mem_inf.mpr ⟨mul_mem ht₁ (inv_mem ht₂),
          mem_normalizer_of_conjugate_eq ?_⟩, ?_⟩
        · rw [← conjugate_conjugate, h₁, ← h₂, conjugate_conjugate_inv]
        · intro h
          exact ht₁₂ (mul_inv_eq_one.mp h)
  obtain ⟨t, ht, ht1⟩ := hne
  have hP : IsPGroup 2 T₀ := hT2.to_le inf_le_left
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    rw [hn] at ht
    exact ht1 (mem_bot.mp ht)
  have h2 : 2 ∣ Nat.card T₀ := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥T₀) 2 h2
  exact ⟨s, s.2.1, (Subgroup.orderOf_coe s).trans hs, s.2.2⟩

theorem mem_coreActionKernel_of_diagonal (hMax : MaximalTwoComponentInput) {a : X}
    {J M K K' : Subgroup X} (hg : GSMaximalSetting X a J)
    (hNJ : normalizer (J : Set X) ≤ M) (hKM : K ≤ M) (hKc : IsPComponent 2 (K.subgroupOf M))
    (hK'a : conjugate K a = K') (hne : K ≠ K') (hJKK : J ≤ K ⊔ K' ⊔ oddIn M) {s : X}
    (hJs : J ≤ centralizer ({s} : Set X)) (hsK : s ∈ normalizer (K : Set X))
    (hsK' : s ∈ normalizer (K' : Set X)) : s ∈ coreActionKernel K := by
  subst hK'a
  have hJa : J ≤ centralizer ({a} : Set X) := hg.le_centralizer
  have hJc := hg.isPComponent
  have hCaM : centralizer ({a} : Set X) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hg).trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  have hJM : J ≤ M := hJa.trans hCaM
  have hK'M : conjugate K a ≤ M := UnbalancedCorr.conjugate_le_of_mem hKM haM
  have hK'c := UnbalancedCorr.isPComponent_conjugate_subgroupOf haM hKc
  have haa : a * a = 1 := by rw [← pow_two, ← hg.orderOf_eq, pow_orderOf_eq_one]
  have hKK' := GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne
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
  have hOMN : M ≤ normalizer ((oddIn M : Subgroup X) : Set X) := GrS4.self_le_normalizer_oddIn M
  set Q : Subgroup X := conjugate K a ⊔ oddIn M with hQ
  have hQK : Q ≤ coreActionKernel K := sup_le (le_coreActionKernel_of_ne hKM hK'M hKc hK'c hne)
    (oddIn_le_coreActionKernel hKM hKc)
  have hJQ : J ≤ normalizer (Q : Set X) := fun j hj =>
    mem_normalizer_sup (hJNK' hj) (hOMN (hJM hj))
  have hKQ : K ≤ normalizer (Q : Set X) := fun k hk =>
    mem_normalizer_sup (hKNK' hk) (hOMN (hKM hk))
  set P : Subgroup X := K ⊓ (J ⊔ Q) with hP
  have hOKP : oddIn K ≤ P := le_inf (map_subtype_le _) (hOK.trans (le_sup_right.trans le_sup_right))
  have hKNP : K ≤ normalizer (P : Set X) := by
    intro k hk
    have haka : a * k * a ∈ conjugate K a := by
      rw [mem_conjugate_iff, show a * (a * k * a) * a⁻¹ = (a * a) * k by group, haa, one_mul]
      exact hk
    have hc : (a * k * a)⁻¹ * k⁻¹ * (a * k * a) * k ∈ oddIn M := by
      have h1 := commutator_mem_commutator (inv_mem haka) (inv_mem hk)
      rw [commutator_comm] at h1
      have h2 := hOK (hKK' h1).1
      rwa [commutatorElement_def, inv_inv, inv_inv] at h2
    obtain ⟨n, hn, hyc⟩ := FooteLit.exists_mul_mem_centralizer_of_involution
      (UnbalancedCorr.odd_card_map_pPrimeCore M) haa (hOMN haM) hc
    have hyJ : k * (a * k * a) * n ∈ normalizer (J : Set X) :=
      GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hg hyc
    have hqQ : a * k * a * n ∈ Q := mul_mem (mem_sup_left haka) (mem_sup_right hn)
    have hqC : a * k * a * n ∈ coreActionKernel K := hQK hqQ
    have hyK : k * (a * k * a) * n ∈ normalizer (K : Set X) := by
      rw [mul_assoc]
      exact mul_mem (le_normalizer hk) hqC.1
    have hyQ : k * (a * k * a) * n ∈ normalizer (Q : Set X) := by
      rw [mul_assoc]
      exact mul_mem (hKQ hk) (le_normalizer hqQ)
    have hyP : k * (a * k * a) * n ∈ normalizer (P : Set X) :=
      mem_normalizer_inf hyK (mem_normalizer_sup hyJ hyQ)
    refine FooteLit.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨p, hp, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    set q := a * k * a * n with hq
    have hε : p⁻¹ * q * p * q⁻¹ ∈ oddIn K := by
      have h1 := (inv_mem hqC).2 p hp.1
      rwa [inv_inv] at h1
    have h1 : (k * q) * p * (k * q)⁻¹ ∈ P := by
      have e : k * q = k * (a * k * a) * n := by rw [hq]; group
      rw [e]
      exact (mem_normalizer_iff.mp hyP p).mp hp
    have h2 : k * (p⁻¹ * q * p * q⁻¹) * k⁻¹ ∈ P := hOKP (GrS4.conj_mem_oddIn hk hε)
    have e : k * p * k⁻¹ = ((k * q) * p * (k * q)⁻¹) * (k * (p⁻¹ * q * p * q⁻¹) * k⁻¹)⁻¹ := by
      group
    rw [e]
    exact mul_mem h1 (inv_mem h2)
  rcases eq_or_commutator_le_oddIn hKM hKc inf_le_left hKNP hOKP with h | h
  ·
    have hKJQ : K ≤ J ⊔ Q := by
      rw [← h]
      exact inf_le_right
    have hsQ : s ∈ normalizer (Q : Set X) :=
      mem_normalizer_sup hsK' (hOMN (hNJ (mem_normalizer_of_conjugate_eq
        (conjugate_eq_self_of_le_centralizer hJs))))
    refine mem_coreActionKernel_of_comm hKM hKc hsK fun g hg k hk => ?_
    obtain ⟨j, hj, q, hq, rfl⟩ := exists_mul_of_mem_sup hJQ (hKJQ hg)
    have hsj : s * j = j * s := (mem_centralizer_singleton_iff.mp (hJs hj)).symm
    have e : (j * q)⁻¹ * (s * (j * q) * s⁻¹) = q⁻¹ * (s * q * s⁻¹) := by
      rw [show s * (j * q) * s⁻¹ = s * j * q * s⁻¹ by group, hsj]
      group
    have hzK : q⁻¹ * (s * q * s⁻¹) ∈ K := by
      rw [← e]
      exact mul_mem (inv_mem hg) ((mem_normalizer_iff.mp hsK _).mp hg)
    have hzQ : q⁻¹ * (s * q * s⁻¹) ∈ Q :=
      mul_mem (inv_mem hq) ((mem_normalizer_iff.mp hsQ q).mp hq)
    have hzC := (inv_mem (hQK hzQ)).2 k⁻¹ (inv_mem hk)
    rw [e, commutatorElement_def]
    rwa [inv_inv, inv_inv] at hzC
  ·
    exfalso
    apply hJnot
    intro j hj
    have hJKQ : J ≤ K ⊔ Q := by rw [hQ, ← sup_assoc]; exact hJKK
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup hKQ (hJKQ hj)
    have hpP : p ∈ P := ⟨hp, by
      have := mul_mem (mem_sup_left hj : p * q ∈ J ⊔ Q) (mem_sup_right (inv_mem hq))
      rwa [mul_inv_cancel_right] at this⟩
    refine mul_mem ⟨le_normalizer hp, fun k hk => ?_⟩ (hQK hq)
    have h1 := h (commutator_mem_commutator (inv_mem hk) (inv_mem hpP))
    rwa [commutatorElement_def, inv_inv, inv_inv] at h1

end CFSG.ComponentClassification.GrSLit.Single
