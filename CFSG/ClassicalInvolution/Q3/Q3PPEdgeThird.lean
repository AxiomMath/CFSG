module

public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeTwo
public import CFSG.ClassicalInvolution.Q3.Q3PPKlein

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W

section Third

variable {G : Type} [Group G]

@[expose] def EdgeThirdFree (K K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop :=
  ∀ M ∈ conjClass3 K, ∀ m : G, IsClassicalMember3 M m → Commutes K₁ M → Commutes K₂ M →
    m ∈ Subgroup.closure ({z₁, z₂} : Set G)

end Third

section Edge

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

namespace EdgeData

theorem eq_or_eq_of_third (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    {M : Subgroup G} (hM : M ∈ conjClass3 K) (hc₁ : Commutes K₁ M) (hc₂ : Commutes K₂ M) :
    M = K₁ ∨ M = K₂ := by
  obtain ⟨m, hm⟩ := hR.inClass.classical M hM
  rcases mem_klein_cases h.sq₁ h.sq₂ h.mul_comm₁₂ (hN M hM m hm hc₁ hc₂) with
    h0 | h0 | h0 | h0
  · exact absurd h0 hm.ne_one
  · exact Or.inl (h1 M hM m hm h0)
  · exact Or.inr (h2 M hM m hm h0)
  · exact absurd h0 (hXN M hM m hm)

theorem layer_z₁_two_components_of_third (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) :
    ∃ i₁ i₂ : ι, i₁ ≠ i₂ ∧ locImg (conjClass3 K) z₁ K₁ ≤ (D.hom i₁).range ∧
      locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i₂).range ∧ D.kind i₁ = CompData.sl23 ∧
      (∀ j, j = i₁ ∨ j = i₂) ∧
      ∀ L ∈ centralizingMembers (conjClass3 K) {z₁},
        locImg (conjClass3 K) z₁ L ≤ (D.hom i₂).range → L ≠ K₂ → ¬ Commutes K₂ L := by
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₁ : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  obtain ⟨i₁, hi₁⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₁, hK₁, rfl⟩)
  obtain ⟨i₂, hi₂⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K₂, hK₂, rfl⟩)
  have hu₁' : z₁ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₁ h.cls₁.mem
  have hA1 : D.kind i₁ = CompData.sl23 :=
    kind_eq_sl23_of_ubar_central D hK₁ h.cls₁ hu₁' (ubar_mem_center_at_self hu₁') i₁ hi₁
  have hne : i₁ ≠ i₂ := by
    intro heq
    subst heq
    have hKK : K₁ = K₂ := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ⟨hK₁, hi₁⟩ ⟨hK₂, hi₂⟩
    have hcl₂ : IsClassicalMember3 K₁ z₂ := hKK ▸ h.cls₂
    exact h.ne (involution_unique3 h.cls₁ hcl₂)
  have hcover : ∀ j, j = i₁ ∨ j = i₂ := by
    intro j
    by_contra hj
    push Not at hj
    obtain ⟨M, hM⟩ := exists_mem_compMembers3 (D := D) j
    have hc1 : Commutes K₁ M :=
      commutes_of_ne_comp3 hΩ hex hP1 hO3 D (Ne.symm hj.1) ⟨hK₁, hi₁⟩ hM
    have hc2 : Commutes K₂ M :=
      commutes_of_ne_comp3 hΩ hex hP1 hO3 D (Ne.symm hj.2) ⟨hK₂, hi₂⟩ hM
    rcases h.eq_or_eq_of_third hR hN hXN h1 h2 hM.1.1 hc1 hc2 with hMK | hMK
    · have hM' : locImg (conjClass3 K) z₁ M ≤ (D.hom i₁).range := by
        rw [hMK]
        exact hi₁
      exact hj.1 (eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hM.1 hM.2 hM')
    · have hM' : locImg (conjClass3 K) z₁ M ≤ (D.hom i₂).range := by
        rw [hMK]
        exact hi₂
      exact hj.2 (eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hM.1 hM.2 hM')
  refine ⟨i₁, i₂, hne, hi₁, hi₂, hA1, hcover, ?_⟩
  intro L hL hLi hLK hcomm
  have hc1 : Commutes K₁ L :=
    commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne ⟨hK₁, hi₁⟩ ⟨hL, hLi⟩
  rcases h.eq_or_eq_of_third hR hN hXN h1 h2 hL.1 hc1 hcomm with hLK₁ | hLK₂
  · have hL' : locImg (conjClass3 K) z₁ L ≤ (D.hom i₁).range := by
      rw [hLK₁]
      exact hi₁
    exact hne (eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hL hL' hLi)
  · exact hLK hLK₂

theorem false_of_commFund (hR : RouteD3Setup K z) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (h1 : TwinFreeAt (conjClass3 K) K₁ z₁) (h2 : TwinFreeAt (conjClass3 K) K₂ z₂)
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range)
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    (hcomm : ∀ R ∈ (D.kind i).fund, ∃ S ∈ (D.kind i).fund, Commutes R S) : False := by
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  obtain ⟨_, i₂, -, -, hi₂, -, -, hlast⟩ :=
    h.layer_z₁_two_components_of_third hR hN hXN h1 h2 D
  have hii : i = i₂ := eq_of_locImg_le_range3 hΩ hex hP1 hO3 D hK₂ hi hi₂
  subst hii
  obtain ⟨R₀, -, hR₀f, hR₀⟩ := exists_corr_left3 hΩ hex hP1 hO3 D ⟨hK₂, hi⟩
  obtain ⟨S, hSf, hRS⟩ := hcomm R₀ hR₀f
  obtain ⟨L, hLm, -, hLS⟩ := exists_corr_right3 hΩ D hsc hSf
  have himg : Commutes (locImg (conjClass3 K) z₁ K₂) (locImg (conjClass3 K) z₁ L) := by
    rw [hR₀, hLS]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hRS r hr s hs]
  have hKL : Commutes K₂ L := commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hK₂ hLm himg
  have hLi : locImg (conjClass3 K) z₁ L ≤ (D.hom i).range := by
    rw [hLS]
    exact Subgroup.map_le_range _ _
  have hLne : L ≠ K₂ := by
    rintro rfl
    exact locImg_not_commutes3 hΩ hex hP1 hO3 hLm himg
  exact hlast L hLm hLi hLne hKL

end EdgeData

end Edge

end CFSG.ClassicalInvolution.Q3.Q3PP
