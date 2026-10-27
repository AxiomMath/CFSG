module

public import CFSG.ClassicalInvolution.Asc77.AscR10QV
public import CFSG.ClassicalInvolution.Uniform.U3M11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement



section SmallComponents

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem quotViol_false_of_sl23 {c : Q3.CompData} (hc : c = Q3.CompData.sl23) (ψ : c.G →* X)
    {R S : Subgroup c.G} (hR : R ∈ c.fund) (hS : S ∈ c.fund) {z j a : X}
    (h : QuotViol Φ (R.map ψ) (S.map ψ) z j a) : False := by
  subst hc
  have hR' : R = ⊤ := hR
  have hS' : S = ⊤ := hS
  rw [hR', hS'] at h
  exact h.ne (h.hz.eq h.hj)

theorem quotViol_false_of_m11 {c : Q3.CompData} (hc : c = Q3.CompData.m11) (ψ : c.G →* X)
    (hker : ψ.ker ≤ Subgroup.center c.G) {R S : Subgroup c.G} (hR : R ∈ c.fund)
    (hS : S ∈ c.fund) {z j a : X} (h : QuotViol Φ (R.map ψ) (S.map ψ) z j a) : False := by
  subst hc
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (Q3.center_m11_eq_bot Q3.m11Facts).le
  obtain ⟨zR, hzR⟩ := hR
  obtain ⟨zS, hzS⟩ := hS
  have hsq : ∀ {w : ↥CFSG.Blueprint.NativeSporadic.M11}, orderOf w = 2 → w * w = 1 := by
    intro w hw
    have := pow_orderOf_eq_one w
    rwa [hw, pow_two] at this
  have hψz : ψ zR = z := by
    have hmem : ψ zR ∈ R.map ψ := Subgroup.mem_map_of_mem _ hzR.mem
    have hs : ψ zR * ψ zR = 1 := by rw [← map_mul, hsq hzR.orderOf_eq_two, map_one]
    rcases h.hz.unique _ hmem hs with h1 | h1
    · exact absurd (hinj (h1.trans (map_one ψ).symm)) hzR.ne_one
    · exact h1
  have hψj : ψ zS = j := by
    have hmem : ψ zS ∈ S.map ψ := Subgroup.mem_map_of_mem _ hzS.mem
    have hs : ψ zS * ψ zS = 1 := by rw [← map_mul, hsq hzS.orderOf_eq_two, map_one]
    rcases h.hj.unique _ hmem hs with h1 | h1
    · exact absurd (hinj (h1.trans (map_one ψ).symm)) hzS.ne_one
    · exact h1
  have haK : a ∈ R.map ψ ⊔ S.map ψ :=
    (sup_le_sup inf_le_left inf_le_left : pairNormalizers (R.map ψ) (S.map ψ) z j ≤ _) h.ha
  have hrange : R.map ψ ⊔ S.map ψ ≤ ψ.range :=
    sup_le (Subgroup.map_le_range _ _) (Subgroup.map_le_range _ _)
  obtain ⟨b, hb⟩ := hrange haK
  have hconj : b * zS * b⁻¹ = zR := by
    apply hinj
    rw [map_mul, map_mul, map_inv, hb, hψj, h.haj, hψz]
  have hS' : Q3.IsClassicalMember3 (conjSub b S) zR := by
    have := hzS.conj b
    rwa [hconj] at this
  have hRS : R = conjSub b S := m11_classical_eq hzR hS'
  refine h.hne ?_
  rw [← hb, ← AscQuot.map_conjSub, ← hRS]

end SmallComponents

section Residual

@[expose] def QV3Model : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), HypOmegaModU (.sl2 3 1) Φ →
    ∀ {ι : Type} (D : Q3.LieSystemData3 ι X Φ) (i : ι)
      (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ),
      D.kind i = Q3.CompData.model t n → t ≠ .G2 →
        ∀ (R S : Subgroup (D.kind i).G), R ∈ (D.kind i).fund → S ∈ (D.kind i).fund →
          ∀ z j a : X, QuotViol Φ (R.map (D.hom i)) (S.map (D.hom i)) z j a → False

theorem qv3Comp_of_qv3Model (hM : QV3Model) : QV3Comp := by
  intro X _ _ Φ hΦ ι D i R S hR hS z j a h
  rcases D.valid i with ⟨t, n, -, hadm, hk⟩ | hk | hk
  · by_cases ht : t = .G2
    · subst ht
      obtain ⟨-, -, hn, -⟩ := hadm
      subst hn
      exact hk
    · exact (hM X Φ hΦ D i t n hk ht R S hR hS z j a h).elim
  · exact (quotViol_false_of_sl23 hk (D.hom i) hR hS h).elim
  · exact (quotViol_false_of_m11 hk (D.hom i) (D.ker_le_center i) hR hS h).elim

theorem g2Comp3_of_qv3Model (hM : QV3Model) : G2Comp3 :=
  g2Comp3_of_qv3Comp (qv3Comp_of_qv3Model hM)

theorem res10aNoConj_nine_of_qv3Model (p f : ℕ) [Fact p.Prime] (h3 : Q3.CIT3Inductive)
    (hM : QV3Model) (h9 : p ^ f = 9) : Res10aNoConj p f :=
  res10aNoConj_nine_of_qv3Comp p f h3 (qv3Comp_of_qv3Model hM) h9

theorem res10aNoConj9_of_qv3Model (p f : ℕ) [Fact p.Prime] (hM : QV3Model) :
    Q3.CIT3Inductive → p ^ f = 9 → Res10aNoConj p f :=
  res10aNoConj9_of_qv3Comp p f (qv3Comp_of_qv3Model hM)

end Residual

end CFSG.ClassicalInvolution.Asc77.T3CII
