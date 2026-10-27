module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCJ2Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Table
public import Certificates.Certificate25880

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.J2Cover.Models

@[expose] noncomputable def eltX
    (a : ℕ) : Perm315 :=
  if a < 128 then (elt a : Perm315) else (elt (a - 128) : Perm315) * bOut

theorem eltX_lt {a : ℕ}
    (h : a < 128) : eltX a = (elt a : Perm315) := by
  simp [eltX, h]

theorem eltX_ge {a : ℕ}
    (h : 128 ≤ a) : eltX a = (elt (a - 128) : Perm315) * bOut := by
  simp [eltX, not_lt.2 h]

theorem eltX_mem
    {a : ℕ} (_ha : a < 256) : eltX a ∈ TX := by
  by_cases h : a < 128
  · rw [eltX_lt h]
    exact S_le_TX (elt a).2
  · rw [eltX_ge (not_lt.1 h)]
    refine Or.inr ?_
    rw [mul_assoc, bOut_mul_self, mul_one]
    exact (elt (a - 128)).2

@[expose] noncomputable def eltA
    (a : ℕ) : MulAut J2Cover.P :=
  if h : a < 256 then J2Cover.rConj ⟨eltX a, TX_le_R (eltX_mem h)⟩ else 1

theorem eltA_of_lt
    {a : ℕ} (h : a < 256) :
    eltA a = J2Cover.rConj ⟨eltX a, TX_le_R (eltX_mem h)⟩ := by
  simp [eltA, h]

theorem eltX_mul
    {a d : ℕ} (ha : a < 256) (hd : d < 256) :
    mulX a d < 256 ∧ eltX a * eltX d = eltX (mulX a d) := by
  by_cases h1 : a < 128 <;> by_cases h2 : d < 128
  · have hm := mulIdx_spec (a := a) h2
    have e : mulX a d = mulIdx a d := by
      simp only [mulX, h1, h2, ↓reduceIte, mulJ2, mulTab_get h1 h2]
    rw [e]
    refine ⟨by omega, ?_⟩
    rw [eltX_lt h1, eltX_lt h2, eltX_lt hm.1, coe_elt_mul a h2]
  · have hd' : d - 128 < 128 := by omega
    have hm := mulIdx_spec (a := a) hd'
    have e : mulX a d = 128 + mulIdx a (d - 128) := by
      simp only [mulX, h1, h2, ↓reduceIte, mulJ2, mulTab_get h1 hd']
    rw [e]
    refine ⟨by omega, ?_⟩
    rw [eltX_lt h1, eltX_ge (not_lt.1 h2), eltX_ge (by omega), Nat.add_sub_cancel_left,
      ← mul_assoc, coe_elt_mul a hd']
  · have ha' : a - 128 < 128 := by omega
    have hb := betaIdx_lt h2
    have hm := mulIdx_spec (a := a - 128) hb
    have e : mulX a d = 128 + mulIdx (a - 128) (betaIdx d) := by
      simp only [mulX, h1, h2, ↓reduceIte, mulJ2, mulTab_get ha' hb]
    rw [e]
    refine ⟨by omega, ?_⟩
    rw [eltX_ge (not_lt.1 h1), eltX_lt h2, eltX_ge (by omega), Nat.add_sub_cancel_left,
      mul_assoc, bOut_mul_elt h2, ← mul_assoc, coe_elt_mul (a - 128) hb]
  · have ha' : a - 128 < 128 := by omega
    have hd' : d - 128 < 128 := by omega
    have hb := betaIdx_lt hd'
    have hm := mulIdx_spec (a := a - 128) hb
    have e : mulX a d = mulIdx (a - 128) (betaIdx (d - 128)) := by
      simp only [mulX, h1, h2, ↓reduceIte, mulJ2, mulTab_get ha' hb]
    rw [e]
    refine ⟨by omega, ?_⟩
    rw [eltX_ge (not_lt.1 h1), eltX_ge (not_lt.1 h2), eltX_lt hm.1]
    calc (elt (a - 128) : Perm315) * bOut * ((elt (d - 128) : Perm315) * bOut)
        = (elt (a - 128) : Perm315) * (bOut * (elt (d - 128) : Perm315)) * bOut := by group
      _ = (elt (a - 128) : Perm315) * ((elt (betaIdx (d - 128)) : Perm315) * bOut) * bOut := by
          rw [bOut_mul_elt hd']
      _ = (elt (a - 128) : Perm315) * (elt (betaIdx (d - 128)) : Perm315) * (bOut * bOut) := by
          group
      _ = (elt (mulIdx (a - 128) (betaIdx (d - 128))) : Perm315) := by
          rw [bOut_mul_self, mul_one, coe_elt_mul (a - 128) hb]

theorem eltA_mul
    {a d : ℕ} (ha : a < 256) (hd : d < 256) :
    mulX a d < 256 ∧ eltA a * eltA d = eltA (mulX a d) := by
  obtain ⟨h1, h2⟩ := eltX_mul ha hd
  refine ⟨h1, ?_⟩
  rw [eltA_of_lt ha, eltA_of_lt hd, eltA_of_lt h1, ← map_mul]
  exact congrArg J2Cover.rConj (Subtype.ext h2)

theorem eltA_injective
    {a b : ℕ} (ha : a < 256) (hb : b < 256)
    (h : eltA a = eltA b) : a = b := by
  rw [eltA_of_lt ha, eltA_of_lt hb] at h
  have h1 : eltX a = eltX b := congrArg Subtype.val (J2Cover.rConj_injective h)
  by_cases ha1 : a < 128 <;> by_cases hb1 : b < 128
  · rw [eltX_lt ha1, eltX_lt hb1] at h1
    exact elt_injective ha1 hb1 (Subtype.ext h1)
  · exfalso
    rw [eltX_lt ha1, eltX_ge (not_lt.1 hb1)] at h1
    have e : bOut = ((elt (b - 128) : Perm315))⁻¹ * (elt a : Perm315) := by rw [h1]; group
    exact bOut_not_mem_S (by
      rw [e]
      exact S.mul_mem (S.inv_mem (elt (b - 128)).2) (elt a).2)
  · exfalso
    rw [eltX_ge (not_lt.1 ha1), eltX_lt hb1] at h1
    have e : bOut = ((elt (a - 128) : Perm315))⁻¹ * (elt b : Perm315) := by rw [← h1]; group
    exact bOut_not_mem_S (by
      rw [e]
      exact S.mul_mem (S.inv_mem (elt (a - 128)).2) (elt b).2)
  · rw [eltX_ge (not_lt.1 ha1), eltX_ge (not_lt.1 hb1)] at h1
    have h2 : (elt (a - 128) : Perm315) = elt (b - 128) := mul_right_cancel h1
    have := elt_injective (by omega : a - 128 < 128) (by omega : b - 128 < 128) (Subtype.ext h2)
    omega

@[expose] noncomputable def tP :
    J2Cover.P := ⟨(elt 4 : Perm315), S_le_autP (elt 4).2⟩

theorem eltA_zero :
    eltA 0 = 1 := by
  rw [eltA_of_lt (by norm_num)]
  have h0 : eltX 0 = 1 := by rw [eltX_lt (a := 0) (by norm_num), elt_zero]; rfl
  have : (⟨eltX 0, TX_le_R (eltX_mem (by norm_num))⟩ : J2Cover.R) = 1 := Subtype.ext h0
  rw [this, map_one]

theorem eltA_four :
    eltA 4 = MulAut.conj tP := by
  rw [eltA_of_lt (by norm_num), ← rConj_eq_conj tP]
  exact congrArg J2Cover.rConj (Subtype.ext (eltX_lt (a := 4) (by norm_num)))

theorem eltA_inner
    {a : ℕ} (ha : a < 128) :
    ∃ y : J2Cover.P, eltA a = MulAut.conj y := by
  refine ⟨⟨(elt a : Perm315), S_le_autP (elt a).2⟩, ?_⟩
  rw [eltA_of_lt (by omega), ← rConj_eq_conj]
  exact congrArg J2Cover.rConj (Subtype.ext (eltX_lt ha))

theorem outerEData_autP :
    OuterEData ↥J2Cover.P := by
  have := J2Cover.finite_mulAut_P
  obtain ⟨hfacts, hfix⟩ := Certificates.certificate25880
  have ht : (tP : Perm315) = (elt 4 : Perm315) := rfl
  suffices hconj : ∀ a ∈ TableX.eListX 256 innX mulX 4, mulX a a = 0 → a ≠ 0 →
      ∃ c : J2Cover.P, eltA a = MulAut.conj (c * tP * c⁻¹) by
    obtain ⟨K, E, hf⟩ := hfacts eltA tP (mul_self_eq_one_of_coe ht) (ne_one_of_coe ht)
      (fun a b ha hb h => eltA_injective ha hb h) (fun a b ha hb => eltA_mul ha hb)
      eltA_zero eltA_four (fun a ha => eltA_inner ha) hconj
    exact OuterEData.of_card ⟨4725, by decide, by rw [J2Cover.card_mulAut_P]⟩ hf
  · intro a hmem hsq h0
    obtain ⟨halt, hfa⟩ := hfix a hmem
    have ha : a < 256 := by omega
    have hfa' : fixCountArr eltArrs[a]! = 11 := hfa hsq h0
    have hsq' : mulIdx a a = 0 := by
      have e : mulX a a = mulIdx a a := by
        simp only [mulX, halt, ↓reduceIte, mulJ2, mulTab_get halt halt]
      rw [← e]
      exact hsq
    have hx2 : (elt a : S) * elt a = 1 := by
      rw [← (mulIdx_spec (a := a) halt).2, hsq', elt_zero]
    have hne : (elt a : S) ≠ 1 := fun h =>
      h0 (elt_injective halt (by norm_num) (h.trans elt_zero.symm))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hinc : Function.Injective (incl : S →* P) := Subgroup.inclusion_injective S_le_P
    have hx : orderOf (incl (elt a) : P) = 2 :=
      orderOf_eq_prime (by rw [pow_two, ← map_mul, hx2, map_one])
        (fun h => hne (hinc (by rw [h, map_one])))
    obtain ⟨g, ⟨-, hg⟩ | ⟨h15, -⟩⟩ := involution_conj_rep (incl (elt a)) hx
    · have hg' : (g : Perm315) * (elt a : Perm315) * (g : Perm315)⁻¹ = (elt 4 : Perm315) := by
        have := congrArg Subtype.val hg
        simpa [incl_coe] using this
      have hgm : (g : Perm315)⁻¹ ∈ J2Cover.P := by
        rw [← P_eq_autP]
        exact inv_mem g.2
      refine ⟨⟨(g : Perm315)⁻¹, hgm⟩, ?_⟩
      have hc := rConj_eq_conj ((⟨(g : Perm315)⁻¹, hgm⟩ : J2Cover.P) * tP *
        (⟨(g : Perm315)⁻¹, hgm⟩ : J2Cover.P)⁻¹)
      rw [eltA_of_lt ha]
      refine Eq.trans ?_ hc
      refine congrArg J2Cover.rConj (Subtype.ext ?_)
      show eltX a = (g : Perm315)⁻¹ * (elt 4 : Perm315) * (g : Perm315)⁻¹⁻¹
      rw [eltX_lt halt, ← hg']
      group
    · rw [incl_coe, fixCount_elt halt, hfa'] at h15
      omega

theorem outerEData_P :
    OuterEData ↥CFSG.ComponentClassification.J2Cover.Models.P :=
  outerEData_autP.of_mulEquiv (MulEquiv.subgroupCongr J2Cover.Models.P_eq_autP.symm)

end CFSG.EvenSporadicStandard.Fin76b.J2
