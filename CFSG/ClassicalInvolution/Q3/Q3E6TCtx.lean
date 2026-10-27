module

public import CFSG.ClassicalInvolution.Q3.Q3E6TPartX
public import CFSG.ClassicalInvolution.Q3.Q3E6TRowThm
public import CFSG.ClassicalInvolution.Q3.Q3NGStar
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp
public import CFSG.ClassicalInvolution.Q3.Q3TCP1
public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.Q3.Q3E6TVis

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair)


theorem te6_context3 (hP : Q3TC.ProductP1Input3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) {β : Subgroup G}
    (hβ : IsPartnerU3 c nd β) (hn3 : ¬ Commutes β (nd.j 3)) :
    ∃ X : XCtx3 .POmegaMinus 5 (conjClass3 K) (z * nd.w 0),
      (∀ N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0}, ¬ Commutes K N →
        ∃ R ∈ fundamentalSubgroups .POmegaMinus
            (modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D,
          locImg (conjClass3 K) (z * nd.w 0) N = R.map X.ψ) ∧
      ∀ N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z},
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus 5 3 1 Nat.prime_three).D,
          locImg (conjClass3 K) (z * nd.w 0) N = R.map X.ψ := by
  classical
  have hΩ : InClass3 (conjClass3 K) := c.hΩ
  have hex : ExactMembers3 (conjClass3 K) := c.hex
  have h0 : 0 < 5 := by norm_num
  have hzne : z ≠ nd.w 0 := z_ne_w0 hnab hR c nd
  obtain ⟨hP1x, hO3x⟩ := hP G K z hR (nd.j 0) (nd.mem 0 h0).1 (nd.w 0) (nd.isCl 0 h0)
    (nd.commK 0 h0) hzne
  obtain ⟨ι, hι, ⟨D⟩⟩ := hR.ih {z * nd.w 0} (not_subset_center_mul3 hnab hR c nd)
  have hKx : K ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.K_mem_centralizingMembers_mul3 c nd h0
  have hβx : β ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    ⟨hβ.mem, partner_le_centralizer_mul3 c nd hβ⟩
  have hlinkV := linked_of_visible3 c nd hβx hβ.nK hβ.n0 hn3
  obtain ⟨i₁, hKi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  have hall : ∀ N' ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z},
      locImg (conjClass3 K) (z * nd.w 0) N' ≤ (D.hom i₁).range := fun N' hN' =>
    linked_le_range3 hΩ hex hP1x hO3x D (hlinkV N' hN') hKi
  have hj0x : nd.j 0 ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.mem_centralizingMembers_mul3 c nd h0 (Or.inl rfl)
  have hj2x : nd.j 2 ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.mem_centralizingMembers_mul3 c nd (by norm_num : 2 < 5) (Or.inr le_rfl)
  have hvis : ∀ a (ha : a < 5), (a = 0 ∨ 2 ≤ a) →
      nd.j a ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z} := fun a ha h =>
    mem_centralizingMembers_pair.mpr ⟨UNodes3.mem_centralizingMembers_mul3 c nd ha h,
      (nd.mem a ha).2⟩
  have hKc : K ∈ compMembers3 (conjClass3 K) (z * nd.w 0) D i₁ := ⟨hKx, hKi⟩
  have hj0c : nd.j 0 ∈ compMembers3 (conjClass3 K) (z * nd.w 0) D i₁ :=
    ⟨hj0x, hall _ (hvis 0 h0 (Or.inl rfl))⟩
  have hj2c : nd.j 2 ∈ compMembers3 (conjClass3 K) (z * nd.w 0) D i₁ :=
    ⟨hj2x, hall _ (hvis 2 (by norm_num) (Or.inr le_rfl))⟩
  have hnA1 : ¬ IsA1Comp3 D i₁ := fun hA =>
    nd.ne_K 0 h0 (eq_of_mem_compMembers_a13 hΩ hex hP1x hO3x hA hj0c hKc)
  rcases kind_cases_of_not_a1 D hnA1 with ⟨t', n', hft, hadm, hk⟩ | hk
  swap
  · exfalso
    exact not_commutes_of_m11_comp3 hΩ hex hP1x hO3x hk hKc hj0c (nd.commK 0 h0)
  have hexc : t' ≠ .G2 ∧ t' ≠ .trialityD4 := by
    have key : (t' = .G2 ∨ t' = .trialityD4) → False := fun ht' =>
      hzne (eq_involution_of_commuting_in_g2d43 hΩ hex hP1x hO3x D ht' hadm hk hj2c hKc hj0c
        (nd.isCl 2 (by norm_num)) c.hz (nd.isCl 0 h0)
        (Gaps.commutes_symm (nd.commK 2 (by norm_num)))
        (Gaps.commutes_symm (nd.far 0 h0 2 (by norm_num) (by norm_num))))
    exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
  obtain ⟨X, hXr⟩ := exists_xctx3_of_comp hΩ hex hP1x hO3x D hk hft hadm hexc.1 hexc.2
  have hvisX : ∀ N' ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z},
      locImg (conjClass3 K) (z * nd.w 0) N' ≤ X.ψ.range := fun N' hN' => by
    rw [hXr]
    exact hall N' hN'
  obtain ⟨R₀, hR₀, hKR₀⟩ := X.fam_range K hKx (by rw [hXr]; exact hKi)
  obtain ⟨φP, hφP, hKP⟩ := exists_visible_equiv3 c nd
  obtain ⟨ht1, hn1⟩ := shape_of_visible_e6 X te6Row3 hft hadm hexc.1 hexc.2 c.hz hKx hR₀ hKR₀
    hvisX φP hφP hKP
  subst ht1 hn1
  refine ⟨X, fun N hN hnc => ?_, fun N hN => ?_⟩
  · obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    have hij : i₁ = j := eq_of_not_commutes3 hΩ hex hP1x hO3x D hKc ⟨hN, hj⟩ hnc
    subst hij
    exact X.fam_range N hN (by rw [hXr]; exact hj)
  · exact X.fam_range N (mem_centralizingMembers_pair.mp hN).1 (hvisX N hN)

end CFSG.ClassicalInvolution.Q3.Q3E6T
