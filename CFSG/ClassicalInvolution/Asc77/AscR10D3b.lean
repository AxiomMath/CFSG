module

public import CFSG.ClassicalInvolution.Asc77.AscR10D3a
public import CFSG.ClassicalInvolution.Asc77.AscR10QV

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement



@[expose] def StdDich3 (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∀ R₁ ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D,
  ∀ R₂ ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D,
  ∀ c₁ c₂ : (Generic.modelUniv t n 3 1 Nat.prime_three).K, c₁ ∈ R₁ → c₂ ∈ R₂ →
    orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ * c₂ = c₂ * c₁ →
      R₁ = R₂ ∨ Commutes R₁ R₂ ∨
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) ∨
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W R₁ R₂

section Main

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem quotViol_false_of_dich3 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ}
    (hD : StdDich3 t n) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (ht2 : t ≠ .G2) (ht4 : t ≠ .trialityD4) (hΩ : HypOmegaModU (.sl2 3 1) Φ)
    (hcard : ∀ L ∈ Φ, Nat.card L = 24) {c : Q3.CompData} (hc : c = Q3.CompData.model t n)
    (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G) {R S : Subgroup c.G} (hR : R ∈ c.fund)
    (hS : S ∈ c.fund) {z j a : X} (h : QuotViol Φ (R.map ψ) (S.map ψ) z j a) : False := by
  subst hc
  have hΩg : HypOmegaGen Φ := hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hFcard : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]; norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hFcard]; decide
  have h24 : Nat.card SL(2, GaloisField 3 1) = 24 := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hFcard]; norm_num
  have hMfin : Finite (Q3.CompData.model t n).G :=
    ModelFacts.finite_modelUniv hp2 Nat.prime_three (ih8_isFundTag_mf hfund) hadm
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm ht2 ht4 hR
  obtain ⟨eS⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm ht2 ht4 hS
  have hRcard : Nat.card R = Nat.card (R.map ψ) := by
    rw [hcard _ h.mem_left, Nat.card_congr eR.toEquiv]; exact h24
  have hScard : Nat.card S = Nat.card (S.map ψ) := by
    rw [hcard _ h.mem_right, Nat.card_congr eS.toEquiv]; exact h24
  have hinjR := injOn_of_natCard_map ψ hRcard
  have hinjS := injOn_of_natCard_map ψ hScard
  have hψz : ψ (sl2Inv eR) = z := by
    have hmem : ψ (sl2Inv eR) ∈ R.map ψ := Subgroup.mem_map_of_mem _ (sl2Inv_mem eR)
    have hs : ψ (sl2Inv eR) * ψ (sl2Inv eR) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eR, map_one]
    rcases h.hz.unique _ hmem hs with h1 | h1
    · exact absurd (hinjR _ (sl2Inv_mem eR) 1 R.one_mem (h1.trans (map_one ψ).symm))
        (sl2Inv_ne_one hodd eR)
    · exact h1
  have hψj : ψ (sl2Inv eS) = j := by
    have hmem : ψ (sl2Inv eS) ∈ S.map ψ := Subgroup.mem_map_of_mem _ (sl2Inv_mem eS)
    have hs : ψ (sl2Inv eS) * ψ (sl2Inv eS) = 1 := by
      rw [← map_mul, sl2Inv_mul_self hodd eS, map_one]
    rcases h.hj.unique _ hmem hs with h1 | h1
    · exact absurd (hinjS _ (sl2Inv_mem eS) 1 S.one_mem (h1.trans (map_one ψ).symm))
        (sl2Inv_ne_one hodd eS)
    · exact h1
  have hcomm : sl2Inv eR * sl2Inv eS = sl2Inv eS * sl2Inv eR := by
    obtain ⟨A, B, hAB⟩ := neg_one_eq_commutator_sl2 hFcard
    have hnorm : j ∈ Subgroup.normalizer ((R.map ψ : Subgroup X) : Set X) :=
      mem_normalizer_of_mem_omegaStarNbr_gen hΩg h.star h.hj
    have hN : ∀ r ∈ R, ∃ r' ∈ R, ψ r' = ψ (sl2Inv eS) * ψ r * (ψ (sl2Inv eS))⁻¹ := by
      intro r hr
      rw [hψj]
      have := (Subgroup.mem_normalizer_iff.mp hnorm _).mp (Subgroup.mem_map_of_mem ψ hr)
      obtain ⟨r', hr', hr'e⟩ := this
      exact ⟨r', hr', hr'e⟩
    have hcom : ⁅((eR.symm A : R) : (Q3.CompData.model t n).G),
        ((eR.symm B : R) : (Q3.CompData.model t n).G)⁆ = sl2Inv eR := by
      have h1 := map_commutatorElement R.subtype (eR.symm A) (eR.symm B)
      have h2 := map_commutatorElement eR.symm A B
      rw [hAB] at h2
      simp only [Subgroup.coe_subtype] at h1
      rw [← h1, ← h2]
      rfl
    have hconj := conj_eq_of_normalizes_image ψ hker hinjR (eR.symm A).2 (eR.symm B).2 hcom hN
      (by rw [hψj, hψz, ← h.comm]; group)
    calc sl2Inv eR * sl2Inv eS = (sl2Inv eS * sl2Inv eR * (sl2Inv eS)⁻¹) * sl2Inv eS := by
          rw [hconj]
      _ = sl2Inv eS * sl2Inv eR := by group
  have hRl : R ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSubgroups_subset_longest ht2 ht4 _ hR
  have hSl : S ∈ ModelFacts.longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSubgroups_subset_longest ht2 ht4 _ hS
  rcases hD R hRl S hSl (sl2Inv eR) (sl2Inv eS) (sl2Inv_mem eR) (sl2Inv_mem eS)
    (orderOf_sl2Inv hodd eR) (orderOf_sl2Inv hodd eS) hcomm with hRS | hcm | ⟨W, hW⟩ | ⟨W, hW⟩
  · subst hRS
    exact h.ne (h.hz.eq h.hj)
  · refine quotViol_false_of_commutes h ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcm x hx y hy]
  · obtain ⟨θ, hrange, hθker, hU, hV⟩ := WeakCT.pair_normalize hW
    have hinj' : Function.Injective (ψ.comp θ) :=
      comp_injective_of_center_bot θ ψ hθker hker (center_sl3_eq_bot hFcard)
    have h2F : (2 : GaloisField 3 1) ≠ 0 := ModelFacts.two_ne_zero_galoisField 1 hp2
    have hRW : R ≤ W := (LinearBlockStandardPair.le_group hW).1
    have hSW : S ≤ W := (LinearBlockStandardPair.le_group hW).2
    refine quotViol_false_of_centralizer_comm3 hΩ hcard h (W := W.map ψ)
      (Subgroup.map_mono hRW) (Subgroup.map_mono hSW) ?_
    intro x hx y hy hxc hyc
    have hrange' : (ψ.comp θ).range = W.map ψ := by rw [MonoidHom.range_comp, hrange]
    have key : ∀ s ∈ WeakCT.B12 (GaloisField 3 1), ψ (θ s) ∈ R.map ψ := fun s hs =>
      Subgroup.mem_map_of_mem ψ (hU ▸ Subgroup.mem_map_of_mem θ hs)
    exact linear_centralizer_comm_of_injective h2F (ψ.comp θ) hinj' (hrange' ▸ hx) (hrange' ▸ hy)
      (fun s hs => hxc _ (key s hs)) (fun s hs => hyc _ (key s hs))
  · obtain ⟨θ, hrange, hθker, hU, hV⟩ := Phan.pair_normalize hW
    have hK9 : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := by
      rw [GaloisField.card 3 2 (by norm_num)]; norm_num
    have hinj' : Function.Injective (ψ.comp θ) :=
      comp_injective_of_center_bot θ ψ hθker hker (center_su3_eq_bot hK9 (by norm_num))
    have h2F : (2 : GaloisField 3 2) ≠ 0 := ModelFacts.two_ne_zero_galoisField 2 hp2
    have hRW : R ≤ W := (UnitaryBlockStandardPair.le_group hW).1
    have hSW : S ≤ W := (UnitaryBlockStandardPair.le_group hW).2
    refine quotViol_false_of_centralizer_comm3 hΩ hcard h (W := W.map ψ)
      (Subgroup.map_mono hRW) (Subgroup.map_mono hSW) ?_
    intro x hx y hy hxc hyc
    have hrange' : (ψ.comp θ).range = W.map ψ := by rw [MonoidHom.range_comp, hrange]
    have key : ∀ s ∈ Phan.B12 (GaloisField 3 2) 3 1, ψ (θ s) ∈ R.map ψ := fun s hs =>
      Subgroup.mem_map_of_mem ψ (hU ▸ Subgroup.mem_map_of_mem θ hs)
    exact unitary_centralizer_comm_of_injective h2F (ψ.comp θ) hinj' (hrange' ▸ hx)
      (hrange' ▸ hy) (fun s hs => hxc _ (key s hs)) (fun s hs => hyc _ (key s hs))

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII
