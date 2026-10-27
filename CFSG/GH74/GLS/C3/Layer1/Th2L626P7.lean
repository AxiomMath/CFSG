module

public import CFSG.GH74.GLS.C3.Layer1.St1Iv251B

public section

namespace CFSG.GH74.GLS.C3.Layer1.Iv251

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem kQ_cover_self {t : G} {J Q : Subgroup G}
    (hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J) (hQC : Q ≤ CxK t J) (hQ2 : IsPGroup 2 Q) :
    ∀ k ∈ J, ∃ p ∈ kQ J Q, ∃ o ∈ pPrimeCoreOf 2 J, k = p * o := by
  set O := pPrimeCoreOf 2 J with hO
  have hodd : Odd (Nat.card O) := TwoThin.card_pPrimeCoreOf_odd J
  have hQJ : ∀ q ∈ Q, q ∈ normalizer (J : Set G) := fun q hq => (hQC hq).2.1
  have hPN : ∀ p ∈ Q, ∀ n ∈ O, p * n * p⁻¹ ∈ O := fun p hp n hn =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_pPrimeCoreOf (hQJ p hp)) n).mp hn
  have hD : ∀ k ∈ J, ∃ d ∈ J ⊓ centralizer (Q : Set G), ∃ o ∈ O, k = d * o := by
    intro k hk
    have hcomm : ∀ p ∈ Q, k⁻¹ * (p * k * p⁻¹) ∈ O := by
      intro p hp
      have h2 := (hQC hp).2.2.2 k⁻¹ (inv_mem hk)
      have e : ⁅k⁻¹, p⁆ = k⁻¹ * (p * k * p⁻¹) := by
        simp only [commutatorElement_def]; group
      rwa [e] at h2
    obtain ⟨n, hn, hnc⟩ := exists_mul_mem_centralizer_of_odd hQ2 hodd hPN hcomm
    exact ⟨k * n, ⟨mul_mem hk (TwoThin.pPrimeCoreOf_le J hn),
      Subgroup.mem_centralizer_iff.mpr fun p hp => hnc p hp⟩, n⁻¹, inv_mem hn, by group⟩
  have hle : J ≤ kQ J Q ⊔ O := by
    refine PumpRigid.le_of_forall_two_elt hJc fun g hg ⟨a, hga⟩ => ?_
    obtain ⟨d, hd, o', ho', hgd⟩ := hD g hg
    obtain ⟨e, he, hea, o, ho, hgo⟩ :=
      exists_two_elt_mul (inf_le_left : J ⊓ centralizer (Q : Set G) ≤ J) hg hd ho' hgd hga
    have heK : e ∈ kQ J Q := mem_oPrimeResidualOf he hea
    rw [hgo]
    exact mul_mem (Subgroup.mem_sup_left heK) (Subgroup.mem_sup_right ho)
  intro k hk
  have hkQ : kQ J Q ≤ normalizer (O : Set G) := fun p hp =>
    mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer ((kQ_le J Q hp).1))
  have := hle hk
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hkQ] at this
  obtain ⟨p, hp, o, ho, hpo⟩ := this
  exact ⟨p, hp, o, ho, hpo.symm⟩

theorem mem_CxK_of_mem_bigC_self {t : G} {J Q : Subgroup G}
    (hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J) (hQC : Q ≤ CxK t J) (hQ2 : IsPGroup 2 Q)
    {s : G} (hs : s ∈ bigC J Q) (hst : s ∈ centralizer ({t} : Set G))
    (hsJ : s ∈ normalizer (J : Set G)) : s ∈ CxK t J := by
  have hcov := kQ_cover_self hJc hQC hQ2
  have hkJ : kQ J Q ≤ J := (kQ_le J Q).trans inf_le_left
  have hsO : s ∈ normalizer (pPrimeCoreOf 2 J : Set G) := mem_normalizer_pPrimeCoreOf hsJ
  refine ⟨hst, hsJ, hsO, fun k hk => ?_⟩
  obtain ⟨p, hp, o, ho, rfl⟩ := hcov k hk
  have hpJ : p ∈ J := hkJ hp
  have h1 : ⁅p, s⁆ ∈ pPrimeCoreOf 2 J := pPrimeCoreOf_le_of_cover hkJ hcov (hs.2.2.2 p hp)
  have h2 : ⁅o, s⁆ ∈ pPrimeCoreOf 2 J := by
    have e : ⁅o, s⁆ = o * (s * o⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem ho ((Subgroup.mem_normalizer_iff.mp hsO _).mp (inv_mem ho))
  have e2 : ⁅p * o, s⁆ = p * ⁅o, s⁆ * p⁻¹ * ⁅p, s⁆ := by
    simp only [commutatorElement_def]; group
  rw [e2]
  exact mul_mem (TwoThin.pPrimeCoreOf_normalized J hpJ h2) h1

end CFSG.GH74.GLS.C3.Layer1.Iv251
