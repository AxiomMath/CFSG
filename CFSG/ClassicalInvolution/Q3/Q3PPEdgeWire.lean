module

public import CFSG.ClassicalInvolution.Q3.Q3PPCommFund
public import CFSG.ClassicalInvolution.Q3.Q3PPCommFundOrth
public import CFSG.ClassicalInvolution.Q3.Q3PPKleinSU
public import CFSG.ClassicalInvolution.Q3.Q3PPKleinM11
public import CFSG.ClassicalInvolution.Q3.Q3PPKleinG2D4
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeKinds
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeThird

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Q3.Q3W
open scoped MatrixGroups


section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

namespace EdgeData

theorem kind_cases_of_third_final [Finite ι] (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) :
    D.kind i = CompData.m11 ∨
      (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), (t = .G2 ∨ t = .trialityD4) ∧
        CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ D.kind i = CompData.model t n) ∨
      (∃ t : CFSG.Assembly.LowTwoRank.StatedLieTag, (t = .PSL ∨ t = .PSU) ∧
        CFSG.Assembly.LowTwoRank.StatedLieAdmissible t 3 3 1 ∧ D.kind i = CompData.model t 3) := by
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  obtain ⟨_, i₂, -, -, hi₂, hA1, hcover, -⟩ :=
    h.layer_z₁_two_components_of_third hR hN hXN h1 h2 D
  have hii : i = i₂ := eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hK₂ hi hi₂
  subst hii
  have hnotA1 : D.kind i ≠ CompData.sl23 :=
    h.not_isA1Comp3_of_two_components hR hnab D hA1 hcover
  rcases D.valid i with ⟨t, n, hfund, hadm, hk⟩ | hsl | hm
  · by_cases hexc : t = .G2 ∨ t = .trialityD4
    · exact Or.inr (Or.inl ⟨t, n, hexc, hadm, hk⟩)
    · push Not at hexc
      obtain ⟨hG2, hD4⟩ := hexc
      have hnA1 := Q3NS.not_psl_two_of_admissible hadm
      have hsc := Q3NS.singleClass_of_eq_model hk hfund hadm hG2 hD4
      have hfalse : (∀ R ∈ (D.kind i).fund, ∃ S ∈ (D.kind i).fund, Commutes R S) → False :=
        fun hcomm => h.false_of_commFund hR hN hXN h1 h2 D hi hsc hcomm
      rcases Q3NS.tag_cases3 hfund hadm hG2 hD4 hnA1 with hconn | hsmall
      · exact (hfalse (commFund_of_connected hk hfund hadm hG2 hD4 hnA1
          (Q3NS.commFamilyConnected_of_eq_model hk hconn))).elim
      · rcases hsmall with ⟨ht, hn3⟩ | hlisted
        · subst hn3
          exact Or.inr (Or.inr ⟨t, ht, hadm, hk⟩)
        · rcases hlisted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
            ⟨rfl, rfl⟩
          · exact (hfalse (by rw [hk]; exact commFund_psp hadm)).elim
          · exact (hfalse (by rw [hk]; exact commFund_psl (m := 3) (by norm_num))).elim
          · exact (hfalse (by rw [hk]; exact commFund_psu hadm (by norm_num))).elim
          · exact (hfalse (by rw [hk]; exact commFund_pomegaOdd hadm)).elim
          · exact (hfalse (by rw [hk]; exact commFund_pomegaPlus hadm)).elim
          · exact (hfalse (by rw [hk]; exact commFund_pomegaMinus hadm)).elim
  · exact absurd hsl hnotA1
  · exact Or.inl hm

theorem kleinAt_of_third [Finite ι] (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeData K K₁ K₂ z₁ z₂) (hN : EdgeThirdFree K K₁ K₂ z₁ z₂)
    (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) : KleinAt K K₁ z₂ := by
  rcases h.kind_cases_of_third_final hR hnab hN hXN h1 h2 D hi with
    hm | ⟨t, n, ht, hadm, hk⟩ | ⟨t, ht, hadm, hk⟩
  · exact h.kleinAt_of_m11 hR D hi hm
  · rcases ht with rfl | rfl
    · exact h.kleinAt_of_kleinData hR D hi (by rw [hk]; exact kleinData_g2 hadm)
    · exact h.kleinAt_of_kleinData hR D hi (by rw [hk]; exact kleinData_trialityD4 hadm)
  · rcases ht with rfl | rfl
    · exact h.kleinAt_of_psl_three hR D hi hk
    · exact h.kleinAt_of_psu_three hR D hi hk hadm

end EdgeData

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
