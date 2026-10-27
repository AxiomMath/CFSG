module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescentCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Clauses

open TwinEdge.Fam

theorem clauses_of_cores {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω)
    (C : Subgroup Y) {Λ : Set (Subgroup Y)}
    (hmem : ∀ M ∈ Λ, ∃ J ∈ Ω, (∃ P : Subgroup Y, IsSylow2In P J ∧ P ≤ C) ∧ M = tightCore (J ⊓ C)) :
    TwinEdge.Fam.Clauses Λ where
  omega1 := by
    intro M hM
    obtain ⟨J, hJ, ⟨P, hP, hPC⟩, rfl⟩ := hmem M hM
    obtain ⟨z, hz, hzm, hS, hnc⟩ := member_data hΩ hJ hP hPC
    exact ⟨⟨z, isUniqueInvolution_mono hz ((tightCore_le _).trans inf_le_left) hzm⟩, P, hS, hnc⟩
  omega2 := by
    intro M hM
    obtain ⟨J, hJ, -, rfl⟩ := hmem M hM
    exact Or.inl (tightCore_tightCore _)
  omega3 := by
    intro M₁ hM₁ M₂ hM₂ Q Q' hQ hQ'
    obtain ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ := hmem M₁ hM₁
    obtain ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ := hmem M₂ hM₂
    obtain ⟨-, -, -, hS₁, -⟩ := member_data hΩ hJ₁ hP₁ hP₁C
    obtain ⟨-, -, -, hS₂, -⟩ := member_data hΩ hJ₂ hP₂ hP₂C
    rw [natCard_eq_of_isSylow2In hS₁ hQ, natCard_eq_of_isSylow2In hS₂ hQ']
    exact hΩ.omega3 J₁ hJ₁ J₂ hJ₂ P₁ P₂ hP₁ hP₂
  omega4 := by
    intro M₁ hM₁ M₂ hM₂ hne
    obtain ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ := hmem M₁ hM₁
    obtain ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ := hmem M₂ hM₂
    have hJJ : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 J₁ hJ₁ J₂ hJ₂ hJJ
    have hle₁ : tightCore (J₁ ⊓ C) ≤ J₁ := (tightCore_le _).trans inf_le_left
    have hle₂ : tightCore (J₂ ⊓ C) ≤ J₂ := (tightCore_le _).trans inf_le_left
    have hle : tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C) ≤ J₁ ⊓ J₂ := inf_le_inf hle₁ hle₂
    have hdvd : Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C)) ∣ Nat.card ↥(J₁ ⊓ J₂) :=
      Subgroup.card_dvd_of_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpos' : Nat.card ↥(J₁ ⊓ J₂) ≠ 0 := Nat.card_pos.ne'
    have hval : padicValNat 2 (Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C))) ≤
        padicValNat 2 (Nat.card ↥(J₁ ⊓ J₂)) := by
      rw [← padicValNat_dvd_iff_le hpos']
      exact (pow_padicValNat_dvd).trans hdvd
    refine ⟨hval.trans h1, fun heq => ?_⟩
    have h2dvd : 2 ∣ Nat.card ↥(tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C)) :=
      dvd_of_one_le_padicValNat heq.ge
    have hJJ1 : padicValNat 2 (Nat.card ↥(J₁ ⊓ J₂)) = 1 :=
      le_antisymm h1 (one_le_padicValNat_of_dvd hpos' (h2dvd.trans hdvd))
    have hcomm := h2 hJJ1
    have hc12 : ⁅J₁, J₂⁆ ≤ J₂ := hcomm.trans (inf_le_right.trans (oddCoreOf_le_self J₂))
    have hc21 : ⁅J₂, J₁⁆ ≤ J₁ := by
      rw [Subgroup.commutator_comm]
      exact hcomm.trans (inf_le_left.trans (oddCoreOf_le_self J₁))
    have hN1 : tightCore (J₂ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₁ ⊓ C) : Set Y) :=
      tightCore_inf_le_normalizer C hc21
    have hN2 : tightCore (J₁ ⊓ C) ≤ Subgroup.normalizer (tightCore (J₂ ⊓ C) : Set Y) :=
      tightCore_inf_le_normalizer C hc12
    have hcR : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤
        tightCore (J₁ ⊓ C) ⊓ tightCore (J₂ ⊓ C) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have hb' : b * a⁻¹ * b⁻¹ ∈ tightCore (J₁ ⊓ C) :=
          (Subgroup.mem_normalizer_iff.mp (hN1 hb) a⁻¹).mp (Subgroup.inv_mem _ ha)
        have := Subgroup.mul_mem _ ha hb'
        simpa [mul_assoc] using this
      · have ha' : a * b * a⁻¹ ∈ tightCore (J₂ ⊓ C) :=
          (Subgroup.mem_normalizer_iff.mp (hN2 ha) b).mp hb
        exact Subgroup.mul_mem _ ha' (Subgroup.inv_mem _ hb)
    have hcJ : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf J₁ ⊓ oddCoreOf J₂ :=
      (Subgroup.commutator_mono hle₁ hle₂).trans hcomm
    have hRo : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf (tightCore (J₁ ⊓ C)) :=
      (le_inf (hcR.trans inf_le_left) (hcJ.trans inf_le_left)).trans (inf_oddCoreOf_le hle₁)
    have hRo' : ⁅tightCore (J₁ ⊓ C), tightCore (J₂ ⊓ C)⁆ ≤ oddCoreOf (tightCore (J₂ ⊓ C)) :=
      (le_inf (hcR.trans inf_le_right) (hcJ.trans inf_le_right)).trans (inf_oddCoreOf_le hle₂)
    exact le_inf hRo hRo'
  omega5 := by
    intro M₁ hM₁ M₂ hM₂ hne z hz v hv hnc hv2 hvz
    obtain ⟨J₁, hJ₁, ⟨P₁, hP₁, hP₁C⟩, rfl⟩ := hmem M₁ hM₁
    obtain ⟨J₂, hJ₂, ⟨P₂, hP₂, hP₂C⟩, rfl⟩ := hmem M₂ hM₂
    have hJJ : J₁ ≠ J₂ := fun h => hne (by rw [h])
    obtain ⟨z₀, hz₀, hz₀m, -, -⟩ := member_data hΩ hJ₁ hP₁ hP₁C
    have hle₁ : tightCore (J₁ ⊓ C) ≤ J₁ := (tightCore_le _).trans inf_le_left
    have hzz : z = z₀ := hz.eq (isUniqueInvolution_mono hz₀ hle₁ hz₀m)
    subst hzz
    have hvJ₂C : v ∈ J₂ ⊓ C := tightCore_le _ hv
    have hnc' : ¬ ∀ w ∈ J₂, v * w = w * v := fun h =>
      hnc fun w hw => h w (((tightCore_le _).trans inf_le_left) hw)
    have hn := hΩ.omega5 J₁ hJ₁ J₂ hJ₂ hJJ z hz₀ v hvJ₂C.1 hnc' hv2 hvz
    have hvC : v ∈ C := hvJ₂C.2
    have hconj : conjSub v (J₁ ⊓ C) = J₁ ⊓ C := by
      rw [conjSub_inf, tl3_conjSub_eq_of_mem_normalizer hn, conjSub_eq_self_of_mem hvC]
    exact mem_normalizer_of_conjSub_eq
      (conjSub_tightCore_of_mem_normalizer (mem_normalizer_of_conjSub_eq hconj))

end Clauses

section Family

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_sylow_centralizer_of_tq (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G}
    (hcJ : c ∈ trivialOnQuot J) :
    ∃ P : Subgroup G, IsSylow2In P J ∧ P ≤ Subgroup.centralizer ({c} : Set G) := by
  have hcomm : ⁅Subgroup.zpowers c, J⁆ ≤ oddCoreOf J :=
    Subgroup.commutator_le.mpr fun a ha x hx =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hcJ ha)).2 x hx
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer hc2 hcomm
  exact ⟨P, hP, by rwa [centralizer_zpowers_eq_singleton'] at hPc⟩

theorem conjSub_coreAt {n : G} (hn : n ∈ Subgroup.centralizer ({c} : Set G)) (J : Subgroup G) :
    conjSub n (coreAt c J) = coreAt c (conjSub n J) := by
  unfold coreAt
  rw [conjSub_tightCore, conjSub_inf, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]

theorem hypOmegaGen_coreFamily (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    HypOmegaGen (restrictFamily (coreFamily Ω c) (Subgroup.centralizer ({c} : Set G))) := by
  have hcl : TwinEdge.Fam.Clauses (coreFamily Ω c) := by
    refine clauses_of_cores hΩ (Subgroup.centralizer ({c} : Set G)) ?_
    rintro _ ⟨J, hJ, rfl⟩
    obtain ⟨P, hP, hPc⟩ := exists_sylow_centralizer_of_tq hc2 hJ.2
    exact ⟨J, hJ.1, ⟨P, hP, hPc⟩, rfl⟩
  refine (hcl.restrict (Subgroup.centralizer ({c} : Set G))).hypOmegaGen ?_
  rintro n _ ⟨L, ⟨J, hJ, rfl⟩, hLY, rfl⟩
  refine ⟨conjSub (n : G) (coreAt c J), ⟨conjSub (n : G) J,
    conjSub_mem_tqMembers3 hΩ.conjInvariant n.2 hJ, (conjSub_coreAt n.2 J)⟩, ?_,
    conjSub_subgroupOf _ n _⟩
  have := conjSub_mono (n := (n : G)) hLY
  rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer n.2)] at this

end Family

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent
