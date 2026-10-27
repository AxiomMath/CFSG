module

public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwKlein
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeThird

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Q3.Q3NS CFSG.Assembly.LowTwoRank

section Center

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} {ι : Type}


theorem mem_center_of_mem_two_ranges (D : LieSystemData3 ι X Φ) {i j : ι} (hij : i ≠ j) {u : X}
    (hui : u ∈ (D.hom i).range) (huj : u ∈ (D.hom j).range) : u ∈ Subgroup.center X := by
  obtain ⟨a, rfl⟩ := hui
  obtain ⟨a', ha'⟩ := huj
  rw [Subgroup.mem_center_iff]
  intro y
  have hy : y ∈ ⨆ k, (D.hom k).range := by
    rw [D.generate]
    exact Subgroup.mem_top y
  refine Subgroup.iSup_induction (fun k => (D.hom k).range)
    (C := fun y => y * D.hom i a = D.hom i a * y) hy ?_ ?_ ?_
  · rintro k _ ⟨b, rfl⟩
    by_cases hk : k = i
    · subst hk
      have hkj : k ≠ j := hij
      rw [← ha']
      exact D.commute k j hkj b a'
    · exact D.commute k i hk b a
  · simp
  · intro u v hu hv
    calc u * v * D.hom i a = u * (v * D.hom i a) := mul_assoc _ _ _
      _ = u * (D.hom i a * v) := by rw [hv]
      _ = (u * D.hom i a) * v := (mul_assoc _ _ _).symm
      _ = (D.hom i a * u) * v := by rw [hu]
      _ = D.hom i a * (u * v) := mul_assoc _ _ _

end Center

section Layer


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

theorem involution_cases_of_third (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    {M : Subgroup G} (hM : M ∈ conjClass3 K) (hc₁ : Commutes K₁ M) (hc₂ : Commutes K₂ M)
    {m : G} (hm : IsClassicalMember3 M m) : m = z₁ ∨ m = z₂ := by
  rcases mem_klein_cases h.sq₁ h.sq₂ h.mul_comm₁₂ (hN M hM m hm hc₁ hc₂) with h0 | h0 | h0 | h0
  · exact absurd h0 hm.ne_one
  · exact Or.inl h0
  · exact Or.inr h0
  · exact absurd h0 (hXN M hM m hm)

theorem layer_of_N [Finite ι] (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeData K K₁ K₂ z₁ z₂) (hN : EdgeThirdFree K K₁ K₂ z₁ z₂)
    (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) :
    ∃ i₁ : ι, i₁ ≠ i ∧ locImg (conjClass3 K) z₁ K₁ ≤ (D.hom i₁).range ∧
      D.kind i₁ = CompData.sl23 ∧ D.kind i ≠ CompData.sl23 ∧
      (∀ j, j ≠ i → D.kind j = CompData.sl23) ∧
      ∀ j, j ≠ i → ∀ M ∈ compMembers3 (conjClass3 K) z₁ D j, ∀ m : G,
        IsClassicalMember3 M m → m = z₁ := by
  classical
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
  have hu₁' : z₁ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₁ h.cls₁.mem
  have hu₂' : z₂ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₂ h.cls₂.mem
  have hz1cen := ubar_mem_center_at_self (Ω := conjClass3 K) hu₁'
  have hA1 : D.kind i₁ = CompData.sl23 :=
    kind_eq_sl23_of_ubar_central D hK₁ h.cls₁ hu₁' hz1cen i₁ hi₁
  have hne : i₁ ≠ i := by
    intro heq
    subst heq
    have hKK : K₁ = K₂ := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ⟨hK₁, hi₁⟩ ⟨hK₂, hi⟩
    have hcl₂ : IsClassicalMember3 K₁ z₂ := hKK ▸ h.cls₂
    exact h.ne (involution_unique3 h.cls₁ hcl₂)
  have hcases : ∀ j, j ≠ i → j ≠ i₁ → ∀ M ∈ compMembers3 (conjClass3 K) z₁ D j, ∀ m : G,
      IsClassicalMember3 M m → m = z₁ ∨ m = z₂ := by
    intro j hji hji₁ M hM m hm
    have hc₁ : Commutes K₁ M :=
      commutes_of_ne_comp3 hΩ hex hP1 hO3 D (Ne.symm hji₁) ⟨hK₁, hi₁⟩ hM
    have hc₂ : Commutes K₂ M :=
      commutes_of_ne_comp3 hΩ hex hP1 hO3 D (Ne.symm hji) ⟨hK₂, hi⟩ hM
    exact involution_cases_of_third h hN hXN hM.1.1 hc₁ hc₂ hm
  have hcen2 : ∀ j, j ≠ i → ∀ M ∈ compMembers3 (conjClass3 K) z₁ D j,
      IsClassicalMember3 M z₂ → D.kind i = CompData.sl23 ∧ D.kind j = CompData.sl23 := by
    intro j hji M hM hm
    have hclM : IsClassicalMember3 (locImg (conjClass3 K) z₁ M)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁))
          ⟨z₂, hu₂'⟩) := (hm.subgroupOf (le_centralizingLayer hM.1)).map_oddQuotient
    have hclK : IsClassicalMember3 (locImg (conjClass3 K) z₁ K₂)
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁))
          ⟨z₂, hu₂'⟩) := (h.cls₂.subgroupOf (le_centralizingLayer hK₂)).map_oddQuotient
    have hcen := mem_center_of_mem_two_ranges D (Ne.symm hji) (hi hclK.mem) (hM.2 hclM.mem)
    exact ⟨kind_eq_sl23_of_ubar_central D hK₂ h.cls₂ hu₂' hcen i hi,
      kind_eq_sl23_of_ubar_central D hM.1 hm hu₂' hcen j hM.2⟩
  have hA1j : ∀ j, j ≠ i → j ≠ i₁ → ∀ M ∈ compMembers3 (conjClass3 K) z₁ D j, ∀ m : G,
      IsClassicalMember3 M m → m = z₁ → D.kind j = CompData.sl23 := by
    intro j _ _ M hM m hm hmz
    have hm1 : IsClassicalMember3 M z₁ := hmz ▸ hm
    exact kind_eq_sl23_of_ubar_central D hM.1 hm1 hu₁' hz1cen j hM.2
  have hnA1 : D.kind i ≠ CompData.sl23 := by
    intro hki
    have hall : ∀ j, D.kind j = CompData.sl23 := by
      intro j
      by_cases hji : j = i
      · subst hji
        exact hki
      by_cases hji₁ : j = i₁
      · subst hji₁
        exact hA1
      obtain ⟨M, hM⟩ := exists_mem_compMembers3 (D := D) j
      obtain ⟨m, hm⟩ := hΩ.classical M hM.1.1
      rcases hcases j hji hji₁ M hM m hm with hmz | hmz
      · exact hA1j j hji hji₁ M hM m hm hmz
      · exact (hcen2 j hji M hM (hmz ▸ hm)).2
    have hpos : 0 < Nat.card ι := by
      have : Nonempty ι := ⟨i₁⟩
      exact Nat.card_pos
    have hshape : LocalShapeC3 (Nat.card ι - 1) CompData.sl23 (conjClass3 K) z₁ :=
      ⟨ι, inferInstance, D, by omega, i₁, hA1, fun j _ => hall j⟩
    rw [← hcl] at hshape
    exact false_of_all_a1_3 hnab hR₁ (Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁) hshape
  refine ⟨i₁, hne, hi₁, hA1, hnA1, fun j hji => ?_, fun j hji M hM m hm => ?_⟩
  · by_cases hji₁ : j = i₁
    · subst hji₁
      exact hA1
    · obtain ⟨M, hM⟩ := exists_mem_compMembers3 (D := D) j
      obtain ⟨m, hm⟩ := hΩ.classical M hM.1.1
      rcases hcases j hji hji₁ M hM m hm with hmz | hmz
      · exact hA1j j hji hji₁ M hM m hm hmz
      · exact absurd (hcen2 j hji M hM (hmz ▸ hm)).1 hnA1
  · by_cases hji₁ : j = i₁
    · subst hji₁
      have hKK : K₁ = M := eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hA1 ⟨hK₁, hi₁⟩ hM
      have hm' : IsClassicalMember3 K₁ m := hKK ▸ hm
      exact involution_unique3 hm' h.cls₁
    · rcases hcases j hji hji₁ M hM m hm with hmz | hmz
      · exact hmz
      · exact absurd (hcen2 j hji M hM (hmz ▸ hm)).1 hnA1

theorem exists_involution_of_corr {Ω : Set (Subgroup G)} {x : G}
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} (hF : KindFund3 (D.kind i))
    {M : Subgroup G} {u : G} (hM : M ∈ centralizingMembers Ω {x}) (hu : IsClassicalMember3 M u)
    (hu' : u ∈ locLayer Ω x) {R : Subgroup (D.kind i).G} (hRf : R ∈ (D.kind i).fund)
    (hMR : locImg Ω x M = R.map (D.hom i)) :
    ∃ r ∈ R, r * r = 1 ∧ r ≠ 1 ∧
      D.hom i r = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ := by
  have h24 : Nat.card (R.map (D.hom i)) = 24 := by
    rw [← hMR]
    exact D.card_eq _ (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩)
  obtain ⟨-, hinj⟩ := fund_facts hF (D.hom i) (D.ker_le_center i) hRf h24
  have hcl : IsClassicalMember3 (locImg Ω x M)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩) :=
    (hu.subgroupOf (le_centralizingLayer hM)).map_oddQuotient
  have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ ∈
      R.map (D.hom i) := by
    rw [← hMR]
    exact hcl.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have hu2 : (⟨u, hu'⟩ : ↥(locLayer Ω x)) * ⟨u, hu'⟩ = 1 :=
    Subtype.ext (Q3NT.mul_self_eq_one_of_orderOf_eq_two hu.orderOf_eq_two)
  refine ⟨r, hrR, hinj _ (R.mul_mem hrR hrR) _ R.one_mem (by
    rw [map_mul, hr, ← map_mul, hu2, map_one, map_one]), ?_, hr⟩
  intro h1
  apply hcl.ne_one
  rw [← hr, h1, map_one]

theorem image_involution_of_corr {Ω : Set (Subgroup G)} {x : G}
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} (hF : KindFund3 (D.kind i))
    {M : Subgroup G} {u : G} (hM : M ∈ centralizingMembers Ω {x}) (hu : IsClassicalMember3 M u)
    (hu' : u ∈ locLayer Ω x) {R R₀ : Subgroup (D.kind i).G} (hRf : R ∈ (D.kind i).fund)
    (hMR : locImg Ω x M = R.map (D.hom i)) {g r₀ : (D.kind i).G} (hg : R = conjSub g R₀)
    (hr₀R : r₀ ∈ R₀) (hr₀2 : r₀ * r₀ = 1) (hr₀1 : r₀ ≠ 1) :
    D.hom i (g * r₀ * g⁻¹) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ := by
  have h24 : Nat.card (R.map (D.hom i)) = 24 := by
    rw [← hMR]
    exact D.card_eq _ (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩)
  obtain ⟨huniq, hinj⟩ := fund_facts hF (D.hom i) (D.ker_le_center i) hRf h24
  have hcl : IsClassicalMember3 (locImg Ω x M)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩) :=
    (hu.subgroupOf (le_centralizingLayer hM)).map_oddQuotient
  have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ ∈
      R.map (D.hom i) := by
    rw [← hMR]
    exact hcl.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have hu2 : (⟨u, hu'⟩ : ↥(locLayer Ω x)) * ⟨u, hu'⟩ = 1 :=
    Subtype.ext (Q3NT.mul_self_eq_one_of_orderOf_eq_two hu.orderOf_eq_two)
  have hr2 : r * r = 1 := hinj _ (R.mul_mem hrR hrR) _ R.one_mem (by
    rw [map_mul, hr, ← map_mul, hu2, map_one, map_one])
  have hr1 : r ≠ 1 := by
    intro h1
    apply hcl.ne_one
    rw [← hr, h1, map_one]
  have hc' : g * r₀ * g⁻¹ ∈ R := hg ▸ conj_mem_conjSub hr₀R
  have hcsq : (g * r₀ * g⁻¹) * (g * r₀ * g⁻¹) = 1 := by
    calc (g * r₀ * g⁻¹) * (g * r₀ * g⁻¹) = g * (r₀ * r₀) * g⁻¹ := by group
      _ = 1 := by rw [hr₀2]; group
  have hcne : g * r₀ * g⁻¹ ≠ 1 := by
    intro h1
    apply hr₀1
    have : r₀ = g⁻¹ * (g * r₀ * g⁻¹) * g := by group
    rw [this, h1]
    group
  rw [← huniq r hrR _ hc' hr2 hcsq hr1 hcne, hr]

theorem eq_z₂_of_commutes_third [Finite ι] (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) {L : Subgroup G}
    (hL : L ∈ compMembers3 (conjClass3 K) z₁ D i) (hcomm : Commutes K₂ L) {m : G}
    (hm : IsClassicalMember3 L m) : m = z₂ := by
  classical
  obtain ⟨i₁, hne, hi₁, -, hnA1, -, -⟩ := layer_of_N hR hnab h hN hXN D hi
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₁ : K₁ ∈ centralizingMembers (conjClass3 K) {z₁} :=
    ⟨h.mem₁, isSubnormal_le h.cls₁.subnormal⟩
  have hu₁' : z₁ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₁ h.cls₁.mem
  have hc₁ : Commutes K₁ L := commutes_of_ne_comp3 hΩ hex hP1 hO3 D hne ⟨hK₁, hi₁⟩ hL
  rcases involution_cases_of_third h hN hXN hL.1.1 hc₁ hcomm hm with hmz | hmz
  · exfalso
    have hm1 : IsClassicalMember3 L z₁ := hmz ▸ hm
    exact hnA1 (kind_eq_sl23_of_ubar_central D hL.1 hm1 hu₁' (ubar_mem_center_at_self hu₁') i
      hL.2)
  · exact hmz

theorem commKer_of_third [Finite ι] (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : EdgeData K K₁ K₂ z₁ z₂) (hN : EdgeThirdFree K K₁ K₂ z₁ z₂)
    (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) (hF : KindFund3 (D.kind i))
    (hconjc : FundConjClosed3 (D.kind i))
    (hsc : ∀ R ∈ (D.kind i).fund, ∀ R' ∈ (D.kind i).fund, ∃ g, R' = conjSub g R)
    {R₀ S₀ : Subgroup (D.kind i).G} (hR₀f : R₀ ∈ (D.kind i).fund)
    (hS₀f : S₀ ∈ (D.kind i).fund) (hcomm : Commutes R₀ S₀) {r₀ s₀ : (D.kind i).G}
    (hr₀R : r₀ ∈ R₀) (hr₀2 : r₀ * r₀ = 1) (hr₀1 : r₀ ≠ 1) (hs₀S : s₀ ∈ S₀)
    (hs₀2 : s₀ * s₀ = 1) (hs₀1 : s₀ ≠ 1) (hcen : s₀ * r₀⁻¹ ∈ Subgroup.center (D.kind i).G) :
    s₀ * r₀⁻¹ ∈ (D.hom i).ker := by
  classical
  have hΩ := hR.inClass
  have hex := hR.setup.1
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hP1 : LocalOddCentral (conjClass3 K) {z₁} := hcl ▸ hR₁.setup.2
  have hO3 : LocalOddThreeFree3 (conjClass3 K) z₁ :=
    hcl ▸ Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z₁} := ⟨h.mem₂, h.le_centralizer₁⟩
  have hu₂' : z₂ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₂ h.cls₂.mem
  obtain ⟨R, hNm, hRf, hNR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D ⟨hK₂, hi⟩
  obtain ⟨g, hg⟩ := hsc R₀ hR₀f R hRf
  have hSf : conjSub g S₀ ∈ (D.kind i).fund := hconjc S₀ hS₀f g
  have hRS : Commutes R (conjSub g S₀) := by
    rw [hg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hcomm a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  obtain ⟨L, hLm, -, hLS⟩ := exists_corr_right3 hΩ D hsc hSf
  have himg : Commutes (locImg (conjClass3 K) z₁ K₂) (locImg (conjClass3 K) z₁ L) := by
    rw [hNR, hLS]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hRS r hr s hs]
  have hKL : Commutes K₂ L := commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hK₂ hLm himg
  have hLi : locImg (conjClass3 K) z₁ L ≤ (D.hom i).range := by
    rw [hLS]
    exact Subgroup.map_le_range _ _
  obtain ⟨m, hm⟩ := hΩ.classical L hLm.1
  have hmz : m = z₂ := eq_z₂_of_commutes_third hR hnab h hN hXN D hi ⟨hLm, hLi⟩ hKL hm
  have hm' : m ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hLm hm.mem
  have h1 := image_involution_of_corr hF hNm h.cls₂ hu₂' hRf hNR hg hr₀R hr₀2 hr₀1
  have h2 := image_involution_of_corr hF hLm hm hm' hSf hLS rfl hs₀S hs₀2 hs₀1
  have hmm : (⟨m, hm'⟩ : ↥(locLayer (conjClass3 K) z₁)) = ⟨z₂, hu₂'⟩ := Subtype.ext hmz
  rw [hmm, ← h1] at h2
  have hcc : g * (s₀ * r₀⁻¹) * g⁻¹ = s₀ * r₀⁻¹ := by
    have := Subgroup.mem_center_iff.mp hcen g
    calc g * (s₀ * r₀⁻¹) * g⁻¹ = (s₀ * r₀⁻¹) * g * g⁻¹ := by rw [this]
      _ = s₀ * r₀⁻¹ := by group
  rw [MonoidHom.mem_ker, ← hcc]
  have e : g * (s₀ * r₀⁻¹) * g⁻¹ = (g * s₀ * g⁻¹) * (g * r₀ * g⁻¹)⁻¹ := by group
  rw [e, map_mul, map_inv, ← h2, mul_inv_cancel]

theorem false_of_connected_third [Finite ι] (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hN : EdgeThirdFree K K₁ K₂ z₁ z₂) (hXN : NonClassicalAt (conjClass3 K) (z₁ * z₂))
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁)) {i : ι}
    (hi : locImg (conjClass3 K) z₁ K₂ ≤ (D.hom i).range) {t : StatedLieTag} {n : ℕ}
    (hk : D.kind i = CompData.model t n) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hconn : CommFamilyConnected (ModelFund 3 t n 1)) : False := by
  classical
  obtain ⟨i₁, hne, hi₁, hA1, hnA1, -, -⟩ := layer_of_N hR hnab h hN hXN D hi
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
  have hu₁' : z₁ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₁ h.cls₁.mem
  have hu₂' : z₂ ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hK₂ h.cls₂.mem
  have hz1cen := ubar_mem_center_at_self (Ω := conjClass3 K) hu₁'
  have hsc := singleClass_of_eq_model hk hfund hadm hG2 hD4
  have hconn' := commFamilyConnected_of_eq_model hk hconn
  have hconjc : FundConjClosed3 (D.kind i) := hk ▸ fundConjClosed3_model t n
  have hF : KindFund3 (D.kind i) := hk ▸ kindFund3_model hfund hadm hG2 hD4
  obtain ⟨R₀, hNm, hR₀f, hNR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D ⟨hK₂, hi⟩
  have hzb : ∀ y : (D.kind i).G,
      D.hom i y * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁))
        ⟨z₁, hu₁'⟩ = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁))
        ⟨z₁, hu₁'⟩ * D.hom i y := fun y => Subgroup.mem_center_iff.mp hz1cen (D.hom i y)
  obtain ⟨R, hRf, S, hSf, hRS, key⟩ := exists_pair_indep_images hk hfund hadm hG2 hD4
    (not_psl_two_of_admissible hadm) hconn' hR₀f (D.hom i) (D.ker_le_center i) hzb
  obtain ⟨g, hg⟩ := hsc R hRf R₀ hR₀f
  have hS'f : conjSub g S ∈ (D.kind i).fund := hconjc S hSf g
  have hRS' : Commutes R₀ (conjSub g S) := by
    rw [hg]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [hRS a ha b hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  obtain ⟨L, hLm, -, hLS⟩ := exists_corr_right3 hΩ D hsc hS'f
  have himg : Commutes (locImg (conjClass3 K) z₁ K₂) (locImg (conjClass3 K) z₁ L) := by
    rw [hNR, hLS]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, hRS' r hr s hs]
  have hKL : Commutes K₂ L := commutes_of_commutes_locImg3 hΩ hex hP1 hO3 hK₂ hLm himg
  have hLi : locImg (conjClass3 K) z₁ L ≤ (D.hom i).range := by
    rw [hLS]
    exact Subgroup.map_le_range _ _
  obtain ⟨m, hm⟩ := hΩ.classical L hLm.1
  have hmz : m = z₂ := eq_z₂_of_commutes_third hR hnab h hN hXN D hi ⟨hLm, hLi⟩ hKL hm
  have hm' : m ∈ locLayer (conjClass3 K) z₁ := le_centralizingLayer hLm hm.mem
  have hclK : IsClassicalMember3 (locImg (conjClass3 K) z₁ K₂)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer (conjClass3 K) z₁))
        ⟨z₂, hu₂'⟩) := (h.cls₂.subgroupOf (le_centralizingLayer hK₂)).map_oddQuotient
  obtain ⟨r, hrR₀, hr2, hr1, hr⟩ := exists_involution_of_corr hF hNm h.cls₂ hu₂' hR₀f hNR
  obtain ⟨s, hsS, hs2, hs1, hs⟩ := exists_involution_of_corr hF hLm hm hm' hS'f hLS
  have hmm : (⟨m, hm'⟩ : ↥(locLayer (conjClass3 K) z₁)) = ⟨z₂, hu₂'⟩ := Subtype.ext hmz
  rw [hmm, ← hr] at hs
  have hr' : g⁻¹ * r * g ∈ R := by
    rw [hg] at hrR₀
    exact mem_conjSub_iff.mp hrR₀
  have hs' : g⁻¹ * s * g ∈ S := mem_conjSub_iff.mp hsS
  have hφ : ∀ x : (D.kind i).G, D.hom i (g⁻¹ * x * g) =
      (D.hom i g)⁻¹ * D.hom i x * D.hom i g := fun x => by simp [map_mul, map_inv]
  have hsq : ∀ x : (D.kind i).G, x * x = 1 → D.hom i (g⁻¹ * x * g) * D.hom i (g⁻¹ * x * g) = 1 := by
    intro x hx
    rw [← map_mul]
    have : g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [this, hx]
    simp
  have hne1 : ∀ x : (D.kind i).G, D.hom i x ≠ 1 → D.hom i (g⁻¹ * x * g) ≠ 1 := by
    intro x hx h1
    apply hx
    rw [hφ] at h1
    have : D.hom i x = D.hom i g * ((D.hom i g)⁻¹ * D.hom i x * D.hom i g) * (D.hom i g)⁻¹ := by
      group
    rw [this, h1]
    group
  have hrne : D.hom i r ≠ 1 := by
    rw [hr]
    exact hclK.ne_one
  have hres := key (g⁻¹ * r * g) hr' (g⁻¹ * s * g) hs' (hsq r hr2) (hsq s hs2) (hne1 r hrne)
    (hne1 s (by rw [hs]; exact hrne))
  apply hres.1
  rw [hφ, hφ, hs]

end Layer

end CFSG.ClassicalInvolution.Q3.Q3OF
