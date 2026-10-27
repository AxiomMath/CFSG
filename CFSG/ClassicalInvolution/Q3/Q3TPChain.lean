module

public import CFSG.ClassicalInvolution.Q3.Q3TPModel
public import CFSG.ClassicalInvolution.Q3.Q3EXModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TP

open scoped MatrixGroups Matrix
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Generic.CoreAssembly
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem exists_twin_partner_of_twin3 {G : Type} [Group G] [Finite G]
    {ι : Type} {Ω : Set (Subgroup G)} {x : G} (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {c : ι}
    (hk : D.kind c = CompData.model .POmegaPlus 4) {K M : Subgroup G}
    (hK : K ∈ compMembers3 Ω x D c) (hM : M ∈ compMembers3 Ω x D c) (hKM : K ≠ M)
    (hcomm : Commutes K M) :
    ∃ N ∈ compMembers3 Ω x D c,
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) ∧
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N M := by
  have hTw := CFSG.ClassicalInvolution.Q3.Q3TP.twinPartnerFactTwin3
  have hpc : PowCop3 (D.kind c) := by
    rw [hk]
    exact powCop3_model trivial Q3TC.statedLieAdmissible_plus4_three (by decide) (by decide)
  have hsc : ∀ R ∈ (D.kind c).fund, ∀ R' ∈ (D.kind c).fund, ∃ g, R' = conjSub g R := by
    have key : ∀ κ : CompData, κ = CompData.model .POmegaPlus 4 →
        ∀ R ∈ κ.fund, ∀ R' ∈ κ.fund, ∃ g, R' = conjSub g R := by
      rintro κ rfl R hR R' hR'
      exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1
        Nat.prime_three trivial Q3TC.statedLieAdmissible_plus4_three (by decide) (by decide)
        R hR R' hR'
    exact key _ hk
  have hpart : ∀ R ∈ (D.kind c).fund, ∀ R' ∈ (D.kind c).fund, R ≠ R' → Commutes R R' →
      ∃ R'' ∈ (D.kind c).fund,
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R'') ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R'' R' := by
    have key : ∀ κ : CompData, κ = CompData.model .POmegaPlus 4 →
        ∀ R ∈ κ.fund, ∀ R' ∈ κ.fund, R ≠ R' → Commutes R R' →
          ∃ R'' ∈ κ.fund,
            (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R'') ∧
            ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R'' R' := by
      rintro κ rfl R hR R' hR' hne hcomm
      exact hTw R hR R' hR' hne hcomm
    exact key _ hk
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hK
  obtain ⟨R', hR'⟩ := exists_corr_left3 hΩ hex hP1 hO3 D hM
  have hne : R ≠ R' := by
    rintro rfl
    exact hKM (corr_unique_right3 hΩ hex hP1 hO3 hR hR')
  have hcR : Commutes R R' := (corr_commutes3 hΩ hex hP1 hO3 hpc hR hR').mp hcomm
  obtain ⟨R'', hR''fund, hp1, hp2⟩ := hpart R hR.2.1 R' hR'.2.1 hne hcR
  obtain ⟨N, hN⟩ := exists_corr_right3 hΩ D hsc hR''fund
  have hNc : N ∈ compMembers3 Ω x D c := ⟨hN.1, hN.2.2 ▸ Subgroup.map_le_range _ _⟩
  exact ⟨N, hNc, linearBlockStandardPair_of_corr3 hΩ hex hP1 hO3 hR hN hp1,
    linearBlockStandardPair_of_corr3 hΩ hex hP1 hO3 hN hR' hp2⟩

theorem exists_chain_of_twin_product3 (h3 : OddThreeFreeInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    {T₁ : Subgroup G} (hT₁ : T₁ ∈ centralizingMembers (conjClass3 K) {z}) (hT₁K : T₁ ≠ K)
    (hT₁comm : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T₁ → Commutes T₁ N)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z}) (hK₂K : K₂ ≠ K)
    (hK₂T : K₂ ≠ T₁) {w : G} (hw : IsClassicalMember3 K₂ w) (hzw : z ≠ w)
    (hP1x : LocalOddCentral (conjClass3 K) {z * w})
    (hO3x : LocalOddThreeFree3 (conjClass3 K) (z * w))
    (hlink : LinkedAtProduct (conjClass3 K) K z w) :
    Commutes K K₂ ∧ ∃ N ∈ centralizingMembers (conjClass3 K) {z * w},
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) ∧
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N K₂ := by
  obtain ⟨ι, -, D, c, hkind, hKK₂, hKc, hK₂c, -, -⟩ :=
    Q3TC.exists_d4_component_of_twin_product3 EX.mfTwin3 h3 hnab hR hT₁ hT₁K hT₁comm hK₂ hK₂K
      hK₂T hw hzw hP1x hO3x hlink
  obtain ⟨hex, -⟩ := hR.setup
  obtain ⟨N, hN, p1, p2⟩ := exists_twin_partner_of_twin3 hR.inClass hex hP1x
    hO3x D hkind hKc hK₂c hK₂K.symm hKK₂
  exact ⟨hKK₂, N, hN.1, p1, p2⟩

end CFSG.ClassicalInvolution.Q3.Q3TP
