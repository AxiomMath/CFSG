module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransportAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowCounting
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimePairs

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime

variable {G Ω : Type*} [Group G] [Finite G] [MulAction Gᵐᵒᵖ Ω]

theorem triple_sylow_normalizer_base_transporter
    {z : G} {alpha beta : Ω}
    (hunique : ∀ a : Ω, rightAct a z = a ↔ a = alpha)
    (hcentralizer : ∀ a b : Ω, a ≠ alpha → b ≠ alpha →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), rightAct a c = b)
    (hbeta : beta ≠ alpha) (p : ℕ) (hp : p.Prime)
    (P : Sylow p (tripleStabilizer z alpha beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (tripleStabilizer z alpha beta)).map
        (tripleStabilizer z alpha beta).subtype : Subgroup G) : Set G))
    {delta : Ω}
    (hdelta : delta ∈ rightFixedSet
      ((P : Subgroup (tripleStabilizer z alpha beta)).map
        (tripleStabilizer z alpha beta).subtype)) (hdelta_ne : delta ≠ alpha) :
    ∃ n : G,
      n ∈ Subgroup.normalizer
        (((P : Subgroup (tripleStabilizer z alpha beta)).map
          (tripleStabilizer z alpha beta).subtype : Subgroup G) : Set G) ⊓
        rightStabilizer alpha ∧ rightAct beta n = delta := by
  let : Fact p.Prime := ⟨hp⟩
  let E := tripleStabilizer z alpha beta
  let U : Subgroup G := (P : Subgroup E).map E.subtype
  let F := tripleStabilizer z alpha delta
  have hUE : U ≤ E := Subgroup.map_subtype_le _
  obtain ⟨halpha, _, _⟩ := triple_subgroup_fixes_three z alpha beta U hUE
  have hdelta_z : rightAct delta z ∈ rightFixedSet U :=
    normalizer_preserves_rightFixedSet U z hzP hdelta
  have hUF : U ≤ F := le_inf
    (le_inf ((mem_rightFixedSet U alpha).mp halpha) ((mem_rightFixedSet U delta).mp hdelta))
    ((mem_rightFixedSet U _).mp hdelta_z)
  obtain ⟨c, hc, hbetac⟩ := hcentralizer beta delta hbeta hdelta_ne
  have hEF : rightConjugate E c = F := by
    simpa only [E, F, hbetac] using tripleStabilizer_rightConjugate hunique beta c hc
  have hFEcard : Nat.card F = Nat.card E := by
    rw [← hEF]
    exact (Nat.card_congr
      (E.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective).toEquiv).symm
  have hUcard : Nat.card U = p ^ (Nat.card E).factorization p := by
    exact (Nat.card_congr (Subgroup.equivMapOfInjective
      (P : Subgroup E) E.subtype E.subtype_injective).toEquiv).symm.trans P.card_eq_multiplicity
  obtain ⟨R, hR⟩ := p_subgroup_sylow_of_full_card p hp F U hUF
    (hFEcard ▸ hUcard)
  let V := rightConjugate U c
  have hVF : V ≤ F := by
    rw [← hEF]
    exact Subgroup.map_mono hUE
  have hVcard : Nat.card V = p ^ (Nat.card F).factorization p := by
    have hVU : Nat.card V = Nat.card U := (Nat.card_congr
      (U.equivMapOfInjective (MulAut.conj c⁻¹).toMonoidHom (MulAut.conj c⁻¹).injective).toEquiv).symm
    rw [hVU, hFEcard]
    exact hUcard
  obtain ⟨T, hT⟩ := p_subgroup_sylow_of_full_card p hp F V hVF hVcard
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq F T R
  have hconj : rightConjugate V (e : G)⁻¹ = U := by
    have hh := sylow_ambient_image_smul p F T e
    rw [he, hR, hT] at hh
    simpa only [rightConjugate, Subgroup.conjBy, inv_inv] using hh.symm
  let n := c * (e : G)⁻¹
  have hnconj : rightConjugate U n = U := by
    calc
      rightConjugate U n = rightConjugate (rightConjugate U c) (e : G)⁻¹ := by
        simp only [n, rightConjugate, mul_inv_rev, inv_inv, Subgroup.conjBy_conjBy]
      _ = U := hconj
  have hninv : n⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hnconj
  have hnN : n ∈ Subgroup.normalizer (U : Set G) := by
    simpa only [inv_inv] using (Subgroup.normalizer (U : Set G)).inv_mem hninv
  have heF : (e : G)⁻¹ ∈ F := F.inv_mem e.property
  have healpha : rightAct alpha (e : G)⁻¹ = alpha :=
    (mem_rightStabilizer alpha _).mp heF.1.1
  have hedelta : rightAct delta (e : G)⁻¹ = delta :=
    (mem_rightStabilizer delta _).mp heF.1.2
  refine ⟨n, ⟨hnN, ?_⟩, ?_⟩
  · apply (mem_rightStabilizer alpha n).mpr
    rw [← rightAct_mul, centralizer_fixes_unique_point hunique c hc, healpha]
  · rw [← rightAct_mul, hbetac, hedelta]

theorem triple_sylow_normalizer_point_stabilizer_transitive
    {z : G} {alpha beta : Ω}
    (hunique : ∀ a : Ω, rightAct a z = a ↔ a = alpha)
    (hcentralizer : ∀ a b : Ω, a ≠ alpha → b ≠ alpha →
      ∃ c ∈ Subgroup.centralizer ({z} : Set G), rightAct a c = b)
    (hbeta : beta ≠ alpha) (p : ℕ) (hp : p.Prime)
    (P : Sylow p (tripleStabilizer z alpha beta))
    (hzP : z ∈ Subgroup.normalizer
      (((P : Subgroup (tripleStabilizer z alpha beta)).map
        (tripleStabilizer z alpha beta).subtype : Subgroup G) : Set G)) :
    ∀ a b : Ω,
      a ∈ rightFixedSet ((P : Subgroup (tripleStabilizer z alpha beta)).map
        (tripleStabilizer z alpha beta).subtype) →
      b ∈ rightFixedSet ((P : Subgroup (tripleStabilizer z alpha beta)).map
        (tripleStabilizer z alpha beta).subtype) →
      a ≠ alpha → b ≠ alpha →
      ∃ n : G,
        n ∈ Subgroup.normalizer
          (((P : Subgroup (tripleStabilizer z alpha beta)).map
            (tripleStabilizer z alpha beta).subtype : Subgroup G) : Set G) ⊓
          rightStabilizer alpha ∧ rightAct a n = b := by
  intro a b ha hb hane hbne
  let N := Subgroup.normalizer
    (((P : Subgroup (tripleStabilizer z alpha beta)).map
      (tripleStabilizer z alpha beta).subtype : Subgroup G) : Set G) ⊓ rightStabilizer alpha
  obtain ⟨na, hna, hba⟩ := triple_sylow_normalizer_base_transporter
    hunique hcentralizer hbeta p hp P hzP ha hane
  obtain ⟨nb, hnb, hbb⟩ := triple_sylow_normalizer_base_transporter
    hunique hcentralizer hbeta p hp P hzP hb hbne
  refine ⟨na⁻¹ * nb, N.mul_mem (N.inv_mem hna) hnb, ?_⟩
  rw [← hba, rightAct_mul]
  simp only [mul_inv_cancel_left]
  exact hbb

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
