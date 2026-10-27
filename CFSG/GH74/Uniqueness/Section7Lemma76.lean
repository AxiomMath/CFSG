module

public import CFSG.GH74.Uniqueness.Section7Theta
public import CFSG.GH74.Uniqueness.Section4Basic
public import CFSG.GH74.Uniqueness.Section6Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open Section7Theta
open scoped Pointwise

section Lemma76Helpers

variable {X : Type} [Group X] [Finite X]

theorem pPrimeCoreIn_le_of_mul {D E C : Subgroup X} (hED : E ≤ D)
    (hDC : (D : Set X) = (pPrimeCoreIn D : Set X) * (C : Set X)) (hCE : C ≤ E) :
    pPrimeCoreIn E ≤ pPrimeCoreIn D := by
  set N := pPrimeCoreIn E
  set O := pPrimeCoreIn D
  have hNE : N ≤ E := pPrimeCoreIn_le E
  have hOD : O ≤ D := pPrimeCoreIn_le D
  have hNO : N ≤ normalizer (O : Set X) := (hNE.trans hED).trans (pPrimeCoreIn_normalizes D)
  have hodd : Odd (Nat.card ↥(N ⊔ O)) :=
    odd_card_sup_of_le_normalizer hNO (odd_card_pPrimeCoreIn E) (odd_card_pPrimeCoreIn D)
  have hND : N ⊔ O ≤ D := sup_le (hNE.trans hED) hOD
  have hnorm : D ≤ normalizer ((N ⊔ O : Subgroup X) : Set X) := by
    intro d hd
    have hd' : d ∈ (D : Set X) := hd
    rw [hDC] at hd'
    obtain ⟨o, ho, c, hc, rfl⟩ := Set.mem_mul.mp hd'
    refine (normalizer ((N ⊔ O : Subgroup X) : Set X)).mul_mem ?_ ?_
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_right ho)
    · have hcE : c ∈ E := hCE hc
      exact Subgroup.inf_normalizer_le_normalizer_sup N O
        ⟨pPrimeCoreIn_normalizes E hcE, pPrimeCoreIn_normalizes D (hED hcE)⟩
  exact le_sup_left.trans (le_pPrimeCoreIn hND hnorm hodd)

omit [Finite X] in
theorem mem_of_mem_sup_of_coprime_orderOf {p : ℕ} [Fact p.Prime] {A O : Subgroup X}
    (hA : IsPGroup p A) (hAO : A ≤ normalizer (O : Set X)) {t : X} (ht : t ∈ A ⊔ O)
    (hcop : Nat.Coprime p (orderOf t)) : t ∈ O := by
  have hOD : O ≤ A ⊔ O := le_sup_right
  have hDn : A ⊔ O ≤ normalizer (O : Set X) := sup_le hAO Subgroup.le_normalizer
  have : (O.subgroupOf (A ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOD).mpr hDn
  have ht' : t ∈ ((A ⊔ O : Subgroup X) : Set X) := ht
  rw [coe_mul_of_left_le_normalizer_right A O hAO] at ht'
  obtain ⟨a, ha, o, ho, hao⟩ := Set.mem_mul.mp ht'
  let π : ↥(A ⊔ O) →* ↥(A ⊔ O) ⧸ O.subgroupOf (A ⊔ O) := QuotientGroup.mk' _
  have haD : a ∈ A ⊔ O := Subgroup.mem_sup_left ha
  have hoD : o ∈ A ⊔ O := Subgroup.mem_sup_right ho
  have hto : (⟨t, ht⟩ : ↥(A ⊔ O)) = ⟨a, haD⟩ * ⟨o, hoD⟩ := Subtype.ext hao.symm
  have ho1 : π ⟨o, hoD⟩ = 1 :=
    (QuotientGroup.eq_one_iff (⟨o, hoD⟩ : ↥(A ⊔ O))).mpr (Subgroup.mem_subgroupOf.mpr ho)
  have hπ : π ⟨t, ht⟩ = π ⟨a, haD⟩ := by rw [hto, map_mul, ho1, mul_one]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨a, ha⟩
  have hka : orderOf a = p ^ k := by rw [← hk, Subgroup.orderOf_mk]
  have e1 : orderOf (⟨a, haD⟩ : ↥(A ⊔ O)) = orderOf a := Subgroup.orderOf_mk a haD
  have e2 : orderOf (⟨t, ht⟩ : ↥(A ⊔ O)) = orderOf t := Subgroup.orderOf_mk t ht
  have h1 : orderOf (π ⟨t, ht⟩) ∣ p ^ k := by
    rw [hπ, ← hka]
    exact (orderOf_map_dvd π _).trans (dvd_of_eq e1)
  have h2 : orderOf (π ⟨t, ht⟩) ∣ orderOf t := (orderOf_map_dvd π _).trans (dvd_of_eq e2)
  have hcop' : Nat.Coprime (orderOf (π ⟨t, ht⟩)) (p ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h2 hcop.symm)
  have h3 : orderOf (π ⟨t, ht⟩) = 1 := hcop'.eq_one_of_dvd h1
  have h4 : π ⟨t, ht⟩ = 1 := orderOf_eq_one_iff.mp h3
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨t, ht⟩ : ↥(A ⊔ O))).mp h4)

theorem oPrimePrime_sup_pPrimeCoreIn_le {p : ℕ} (hp : p.Prime) {A D : Subgroup X}
    (hA : IsPGroup p A) (hAD : A ≤ D) :
    oPrimePrime p (A ⊔ pPrimeCoreIn D) ≤ oPrimePrime p D := by
  have : Fact p.Prime := ⟨hp⟩
  set O := pPrimeCoreIn D
  have hAO : A ≤ normalizer (O : Set X) := hAD.trans (pPrimeCoreIn_normalizes D)
  have hcopT : Nat.Coprime p (Nat.card (oPrimePrime p (A ⊔ O))) :=
    oPrimePrime_coprime_card hp (A ⊔ O)
  have hTO : oPrimePrime p (A ⊔ O) ≤ O := by
    intro t ht
    refine mem_of_mem_sup_of_coprime_orderOf hA hAO (oPrimePrime_le p _ ht) ?_
    exact hcopT.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ ht)
  exact le_oPrimePrime_of_le_pPrimeCoreIn hTO
    (le_sup_right.trans (le_normalizer_oPrimePrime p (A ⊔ O))) hcopT

theorem oPrimePrime_le_of_pGroup_centralizer_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D E W₁ : Subgroup X} (hDodd : Odd (Nat.card D)) (hED : E ≤ D) (hW₁p : IsPGroup p W₁)
    (hW₁E : W₁ ≤ E) (hcent : centralizer (W₁ : Set X) ⊓ D ≤ E) :
    oPrimePrime p E ≤ oPrimePrime p D := by
  have : Fact p.Prime := ⟨hp⟩
  have hW₁D : W₁ ≤ D := hW₁E.trans hED
  refine CFSG.BenderSuzuki.theorem4b_lemma76_of_pgroup_centralizer_le_E hp2 hDodd hED
    (W₁.subgroupOf D) (hW₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hW₁D).symm) ?_
  refine sup_le ?_ ?_
  · intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hW₁E (Subgroup.mem_subgroupOf.mp hx))
  · intro x hx
    refine Subgroup.mem_subgroupOf.mpr (hcent (Subgroup.mem_inf.mpr ⟨?_, x.2⟩))
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.mem_centralizer_iff.mp hx ⟨w, hW₁D hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
    exact congrArg Subtype.val this

theorem oPrimePrime_le_of_mul_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {D E W₁ C : Subgroup X} (hED : E ≤ D)
    (hDC : (D : Set X) = (pPrimeCoreIn D : Set X) * (C : Set X)) (hCE : C ≤ E)
    (hW₁p : IsPGroup p W₁) (hW₁E : W₁ ≤ E) (hcent : centralizer (W₁ : Set X) ⊓ D ≤ E) :
    oPrimePrime p E ≤ oPrimePrime p D := by
  have : Fact p.Prime := ⟨hp⟩
  have hθO : oPrimePrime p E ≤ pPrimeCoreIn D :=
    (oPrimePrime_le_pPrimeCoreIn p E).trans (pPrimeCoreIn_le_of_mul hED hDC hCE)
  set O := pPrimeCoreIn D
  have hW₁D : W₁ ≤ D := hW₁E.trans hED
  have hW₁O : W₁ ≤ normalizer (O : Set X) := hW₁D.trans (pPrimeCoreIn_normalizes D)
  have hW₁odd : Odd (Nat.card W₁) := by
    obtain ⟨n, hn⟩ := hW₁p.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hD₁odd : Odd (Nat.card ↥(W₁ ⊔ O)) :=
    odd_card_sup_of_le_normalizer hW₁O hW₁odd (odd_card_pPrimeCoreIn D)
  have hD₁D : W₁ ⊔ O ≤ D := sup_le hW₁D (pPrimeCoreIn_le D)
  have h1 : oPrimePrime p E ≤ oPrimePrime p (E ⊓ (W₁ ⊔ O)) :=
    le_oPrimePrime_of_le_normalizer (le_inf (oPrimePrime_le p E) (hθO.trans le_sup_right))
      (inf_le_left.trans (le_normalizer_oPrimePrime p E)) (oPrimePrime_odd_card p E)
      (oPrimePrime_coprime_card hp E)
  have h2 : oPrimePrime p (E ⊓ (W₁ ⊔ O)) ≤ oPrimePrime p (W₁ ⊔ O) :=
    oPrimePrime_le_of_pGroup_centralizer_le hp hp2 hD₁odd inf_le_right hW₁p
      (le_inf hW₁E le_sup_left) fun x hx => ⟨hcent ⟨hx.1, hD₁D hx.2⟩, hx.2⟩
  exact h1.trans (h2.trans (oPrimePrime_sup_pPrimeCoreIn_le hp hW₁p hW₁D))

end Lemma76Helpers

theorem IsProductDisconnected.lemma76 {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (hZ : IsInvariantInvolutionSet Z) (h : IsProductDisconnected Z M)
    {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) {β : Subgroup X}
    (hβ : β ∈ omegaFix M (W : Set X)) (hβM : β ≠ M) (u : X)
    (hK1E : conjSet (CFSG.OddInversion.invertedSet W z) u ⊆
      ((M ⊓ β ⊓ conjugate β z : Subgroup X) : Set X))
    (hcent : centralizer (conjSet (CFSG.OddInversion.invertedSet W z) u) ⊓ M ⊓ β ≤
      M ⊓ β ⊓ conjugate β z) :
    oPrimePrime p (M ⊓ β ⊓ conjugate β z) ≤ oPrimePrime p (M ⊓ β) := by
  have hcl : Subgroup.closure (conjSet (CFSG.OddInversion.invertedSet W z) u) = conjugate W u := by
    rw [← conjugate_closure, hW.closure_invertedSet hZ]
  have hW₁E : conjugate W u ≤ M ⊓ β ⊓ conjugate β z := by
    rw [← hcl, Subgroup.closure_le]
    exact hK1E
  have hW₁p : IsPGroup p (conjugate W u) := hW.pgroup.map (MulAut.conj u⁻¹).toMonoidHom
  have hsub : conjSet (CFSG.OddInversion.invertedSet W z) u ⊆
      ((conjugate W u : Subgroup X) : Set X) := by
    rw [← hcl]
    exact Subgroup.subset_closure
  have hcent' : centralizer ((conjugate W u : Subgroup X) : Set X) ⊓ (M ⊓ β) ≤
      M ⊓ β ⊓ conjugate β z := by
    intro x hx
    obtain ⟨hxC, hxD⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxM, hxβ⟩ := Subgroup.mem_inf.mp hxD
    exact hcent (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le hsub hxC, hxM⟩,
      hxβ⟩)
  have hCE : (M ⊓ β) ⊓ centralizer ({z} : Set X) ≤ M ⊓ β ⊓ conjugate β z := by
    intro c hc
    obtain ⟨hcD, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcomm : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    refine Subgroup.mem_inf.mpr ⟨hcD, mem_conjugate_iff.mpr ?_⟩
    have e : z * c * z⁻¹ = c := by rw [← hcomm]; group
    rw [e]
    exact (Subgroup.mem_inf.mp hcD).2
  exact oPrimePrime_le_of_mul_centralizer hW.prime hW.ne_two inf_le_left
    (h.prop38d hZ hW.mem_Z hW.mem_M hβ.1 hβM).1 hCE hW₁p hW₁E hcent'

end CFSG.GH74.Uniqueness
