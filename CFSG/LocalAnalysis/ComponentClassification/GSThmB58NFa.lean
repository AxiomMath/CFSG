module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Conj
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypB2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpQuot
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bConj
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem not_isoCorrSub_conjugate_B {g β : H} (hβ : β ∈ h.B) (hga : g * h.a * g⁻¹ = β * h.a)
    (L : Subgroup H) : ¬ IsoCorrSub h.a h.J (conjugate h.B g) L := by
  rintro ⟨hLN, hLc, hLa, hsup, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJL : GSLit.fixedLayer h.J (conjugate h.B g) ≤ L := by
    rw [← hsup]
    exact le_sup_left
  have hTa : GSLit.fixedLayer h.J (conjugate h.B g) ≤ centralizer ({h.a} : Set H) :=
    (GSLit.fixedLayer_le_inf _ _).trans (inf_le_left.trans h.J_le)
  have haL : h.a ∈ normalizer (L : Set H) := mem_normalizer_of_conjugate_eq' hLa
  have hLO : ⁅L, zpowers h.a⁆ ≤ oddCoreIn L := commutator_le_oddCoreIn haL hJL hTa hsup
  set M := conjugate L g⁻¹ with hMdef
  have hNg : conjugate (normalizer (conjugate h.B g : Set H)) g⁻¹ =
      normalizer (h.B : Set H) := by
    have h1 : conjugate (normalizer (conjugate h.B g : Set H)) g⁻¹ =
        normalizer (conjugate (conjugate h.B g) g⁻¹ : Set H) :=
      map_equiv_normalizer_eq (conjugate h.B g) (MulAut.conj g⁻¹⁻¹)
    rw [h1, conjugate_conjugate_inv]
  obtain ⟨hMW, hMpc⟩ := Six.isPComponent_conjugate hLN hLc g⁻¹
  rw [hNg] at hMW hMpc
  have hMV : M ≤ layerIn (normalizer (h.B : Set H)) := by
    intro x hx
    have hle : M.subgroupOf (normalizer (h.B : Set H)) ≤ pLayer ↥(normalizer (h.B : Set H)) 2 :=
      le_sSup hMpc
    exact ⟨⟨x, hMW hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  have haW : h.a ∈ normalizer (h.B : Set H) := h.a_mem_normalizer
  have hKa' := Six.isPComponent_conjugate hKW hKpc h.a
  rw [conjugate_eq_of_mem_normalizer (le_normalizer haW)] at hKa'
  obtain ⟨hKaW, hKapc⟩ := hKa'
  have hMKK : M ≤ h.K ⊔ conjugate h.K h.a := by
    rw [h.layer_eq_K]
    exact hMV
  have hMK := GSLit.eq_or_eq_of_le_sup hMW hMpc hKW hKpc hKaW hKapc hMKK
  have hMC : M ≤ centralizer (h.B : Set H) := hMV.trans h.V_le_centralizer_B
  have hβM : β ∈ centralizer (M : Set H) :=
    mem_centralizer_iff.mpr fun m hm => (mem_centralizer_iff.mp (hMC hm) β hβ).symm
  have hMβ : conjugate M β = M := conjugate_eq_of_mem_normalizer (centralizer_le_normalizer _ hβM)
  have hMa : conjugate M (β * h.a) = M := by
    rw [← hga, hMdef, conjugate_conjugate, show g⁻¹ * (g * h.a * g⁻¹) = h.a * g⁻¹ by group,
      ← conjugate_conjugate, hLa]
  have hMa' : conjugate M h.a = M := by
    calc conjugate M h.a = conjugate (conjugate M β) h.a := by rw [hMβ]
      _ = conjugate M (β * h.a) := conjugate_conjugate M β h.a
      _ = M := hMa
  have haa : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]
  by_cases hKa : conjugate h.K h.a = h.K
  ·
    have hMK' : M = h.K := by
      rcases hMK with h1 | h1
      · exact h1
      · exact h1.trans hKa
    have hMO : ⁅M, zpowers (β * h.a)⁆ ≤ oddCoreIn M := by
      have h1 := map_mono (f := (MulAut.conj g⁻¹⁻¹).toMonoidHom) hLO
      have h2 : (⁅L, zpowers h.a⁆).map (MulAut.conj g⁻¹⁻¹).toMonoidHom =
          ⁅M, zpowers (β * h.a)⁆ := by
        rw [Subgroup.map_commutator]
        congr 1
        change conjugate (zpowers h.a) g⁻¹ = zpowers (β * h.a)
        rw [conjugate_zpowers', inv_inv, hga]
      have h3 : (oddCoreIn L).map (MulAut.conj g⁻¹⁻¹).toMonoidHom = oddCoreIn M :=
        Six.conjugate_oddCoreIn L g⁻¹
      rw [h2, h3] at h1
      exact h1
    rw [hMK'] at hMO hβM
    have hβa : Commute β h.a := h.comm_a (h.B_le_S hβ)
    have haK : h.a ∈ normalizer (h.K : Set H) := mem_normalizer_of_conjugate_eq' hKa
    have hKO : ⁅h.K, zpowers h.a⁆ ≤ oddCoreIn h.K := by
      rw [commutator_le]
      intro k hk x hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
      have hkn : (h.a ^ n) * k * (h.a ^ n)⁻¹ ∈ h.K :=
        (mem_normalizer_iff.mp (zpow_mem haK n) k).mp hk
      have hβn : β ^ n ∈ centralizer (h.K : Set H) := zpow_mem hβM n
      have hc1 : k * β ^ n = β ^ n * k := mem_centralizer_iff.mp hβn k hk
      have hcK : ⁅k, h.a ^ n⁆ ∈ h.K := by
        have hk' : h.a ^ n * k⁻¹ * (h.a ^ n)⁻¹ ∈ h.K := by
          rw [show h.a ^ n * k⁻¹ * (h.a ^ n)⁻¹ = (h.a ^ n * k * (h.a ^ n)⁻¹)⁻¹ by group]
          exact inv_mem hkn
        rw [commutatorElement_def,
          show k * h.a ^ n * k⁻¹ * (h.a ^ n)⁻¹ = k * (h.a ^ n * k⁻¹ * (h.a ^ n)⁻¹) by group]
        exact mul_mem hk hk'
      have hc3 : ⁅k, h.a ^ n⁆ * β ^ n = β ^ n * ⁅k, h.a ^ n⁆ := mem_centralizer_iff.mp hβn _ hcK
      have h1 : ⁅k, h.a ^ n⁆ = ⁅k, (β * h.a) ^ n⁆ := by
        rw [hβa.mul_zpow, show ⁅k, β ^ n * h.a ^ n⁆ =
          (k * β ^ n * k⁻¹) * ⁅k, h.a ^ n⁆ * (β ^ n)⁻¹ by simp only [commutatorElement_def]; group,
          show k * β ^ n * k⁻¹ = β ^ n by rw [hc1]; group, ← hc3]
        group
      rw [h1]
      exact hMO (commutator_mem_commutator hk (zpow_mem (mem_zpowers _) n))
    have hV : layerIn (normalizer (h.B : Set H)) = h.K := by
      rw [← h.layer_eq_K, hKa, sup_idem]
    have hKKO : h.K ≤ oddCoreIn h.K := by
      have h1 := h.commutator_eq
      rw [hV] at h1
      exact (le_of_eq h1.symm).trans hKO
    have hKp : ⁅h.K, h.K⁆ = h.K :=
      Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hKW hKpc)
    have hodd : Odd (Nat.card ↥(oddCoreIn h.K)) := by
      rw [oddCoreIn, card_map_of_injective h.K.subtype_injective]
      exact OddQuot.odd_card_pPrimeCore
    have hbot := Pump516.eq_bot_of_perfect_of_le_odd hKp hKKO hodd
    have hnt := B5a.nontrivial_of_isPComponent_subgroupOf hKW hKpc
    rw [hbot] at hnt
    exact not_nontrivial _ hnt
  ·
    rcases hMK with h1 | h1
    · have h1' : M = h.K := h1
      rw [h1'] at hMa'
      exact hKa hMa'
    · have h1' : M = conjugate h.K h.a := h1
      rw [h1', conjugate_conjugate, haa, conjugate_one] at hMa'
      exact hKa hMa'.symm

theorem card_inf_normalizer_conjugate_B_le {g β : H} (hβ : β ∈ h.B)
    (hga : g * h.a * g⁻¹ = β * h.a) (hBP : conjugate h.B g ≤ h.S ⊓ coreActionKernel h.J) :
    Nat.card ↥(h.S ⊓ normalizer (conjugate h.B g : Set H)) ≤
      Nat.card ↥(h.S ⊓ normalizer (h.B : Set H)) := by
  by_contra hlt
  push Not at hlt
  have hcard : Nat.card ↥(conjugate h.B g) = Nat.card ↥h.B :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  obtain ⟨L, hL⟩ := h.isoCorr_of_lt (conjugate h.B g) hBP (Or.inr ⟨hcard, hlt⟩)
  exact h.not_isoCorrSub_conjugate_B hβ hga L hL

end Hyp52

end CFSG.ComponentClassification.GSThmB
