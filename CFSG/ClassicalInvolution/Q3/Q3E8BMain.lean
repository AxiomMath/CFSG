module

public import CFSG.ClassicalInvolution.Q3.Q3E8Facts
public import CFSG.ClassicalInvolution.Q3.Q3E8BModel
public import CFSG.ClassicalInvolution.Q3.Q3E8BSix
public import CFSG.ClassicalInvolution.Q3.Q3E8BShape
public import CFSG.ClassicalInvolution.Q3.Q3E8BLayer
public import CFSG.ClassicalInvolution.Q3.Q3NGStar
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp
public import CFSG.ClassicalInvolution.Q3.Q3PStage
public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Layer

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)
open scoped MatrixGroups commutatorElement

set_option linter.unusedSectionVars false



section Main

theorem r2_false3 (hB8 : TypeE8.E7FrameRelations 3 1) (hB9 : TypeE8.E7FrameInvolutions 3 1)
    (hLayer : TypeE8.E7LayerEquiv 3 1) (hConn : TypeE8.Fund12Connected 3 1) (hRow : E8D8Row3)
    (hD8 : TypeE8.D8NoThreeAdjPairs 3 .POmegaPlus 8 1) (hP1x : E8P1x3)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {K : Subgroup G} {z : G} (S : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .E7 0) (conjClass3 K) z)
    (c : ETCtx3 .E7 0 (conjClass3 K) K z) {β : Subgroup G} (hβ : β ∈ conjClass3 K) {t : G}
    (htβ : IsClassicalMember3 β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (ht : t * z * t⁻¹ = z) (g : TypeE8.K7 3 1) {p₀ : Fin 7} (hp₀ : p₀ = 1 ∨ p₀ = 4)
    (hT : ToralNormalAt3 c ht g p₀) : False := by
  classical
  have hMFZ : Gaps.FundNoncentral 3 := Gaps.fundNoncentral 3
  obtain ⟨ι₀, hι₀, D₀, -⟩ := id hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨γ₁, γ₂, dx, da, db, ρ, δm, δn, hγ₁, hγ₂, hdx, hda, hdb, hρ, hδm, hδn, eγ₁, eγ₂, edx,
    eda, edb, oρ, oδm, o12, tdx, pdx, ada, a1, a2, b1, b2, adx, bdx, hρpair, ρδm, -, -, pδm,
    -⟩ := TypeE8.exists_r2_roots 3 1 p₀ hp₀
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    Gaps.standardPair_involutions_commute h2 hW c.hz.mem htβ.mem c.hz.orderOf_eq_two
      htβ.orderOf_eq_two
  have hnormK : conjSub t K = K :=
    Gaps.conjSub_eq_of_standardPair h2 hW htβ.mem htβ.orderOf_eq_two
  obtain ⟨W₁, hW₁⟩ := c.exists_isFrameMember hB8 g hγ₁
  obtain ⟨W₂, hW₂⟩ := c.exists_isFrameMember hB8 g hγ₂
  obtain ⟨Ndx, hNdx⟩ := c.exists_isFrameMember hB8 g hdx
  obtain ⟨Nda, hNda⟩ := c.exists_isFrameMember hB8 g hda
  obtain ⟨Ndb, hNdb⟩ := c.exists_isFrameMember hB8 g hdb
  obtain ⟨Nρ, hNρ⟩ := c.exists_isFrameMember hB8 g hρ
  obtain ⟨Nδ, hNδ⟩ := c.exists_isFrameMember hB8 g hδm
  have hβ' : ∀ {δ : Fin 7 → ℤ} {N : Subgroup G}, δ ∈ (TypeE8.D7 3 1).roots →
      ((δ p₀ : ℤ) : ZMod 2) = 0 → c.IsFrameMember g δ N → Commutes β N :=
    fun hδ he h => h.commutes_partner_of_even hMFZ hsingle D₀ hβ htβ ⟨W, hW⟩ hT hδ he
  have hβ₁ : Commutes β W₁ := hβ' hγ₁ eγ₁ hW₁
  have hβ₂ : Commutes β W₂ := hβ' hγ₂ eγ₂ hW₂
  obtain ⟨w₁, hw₁⟩ := c.hΩ.classical W₁ hW₁.mem_Ω
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical W₂ hW₂.mem_Ω
  obtain ⟨wρ, hwρ⟩ := c.hΩ.classical Nρ hNρ.mem_Ω
  obtain ⟨r₁, hr₁, hr₁2, hψ₁⟩ := hW₁.exists_involution hB8 hγ₁ hw₁
  obtain ⟨r₂, hr₂, hr₂2, hψ₂⟩ := hW₂.exists_involution hB8 hγ₂ hw₂
  obtain ⟨rρ, hrρ, hrρ2, hψρ⟩ := hNρ.exists_involution hB8 hρ hwρ
  have hW₁₂ : Commutes W₁ W₂ := hW₁.commutes_of_orth hB8 hW₂ hγ₁ hγ₂ o12
  have hcard := card_closure_triple3 c hB9 hγ₁ hγ₂ o12 hW₁ hW₂ hw₁ hw₂ hr₁ hr₂ hr₁2 hr₂2 hψ₁ hψ₂
    hW₁₂
  obtain ⟨hP1xx, hO3xx⟩ := hP1x G hnab K z S W₁ W₂ w₁ w₂ hW₁.mem_Ω hW₂.mem_Ω hw₁ hw₂
    hW₁.commutes_K hW₂.commutes_K hW₁₂ hcard
  have hw₁2 : w₁ * w₁ = 1 := mul_self_of_isClassicalMember3 hw₁
  have hw₂2 : w₂ * w₂ = 1 := mul_self_of_isClassicalMember3 hw₂
  have hz2 : z * z = 1 := mul_self_of_isClassicalMember3 c.hz
  have hzw₁ : z * w₁ = w₁ * z := hW₁.commutes_K z c.hz.mem w₁ hw₁.mem
  have hxne : w₁ * w₂ ≠ 1 := by
    intro h1
    have hw : w₂ = w₁ := by
      rw [← inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hw₁2]
    have hle := Q3.card_closure_pair_le_four hz2 hw₁2 hzw₁
    have hset : ({z, w₁, w₂} : Set G) = {z, w₁} := by
      subst hw
      ext y
      simp
    rw [hset] at hcard
    omega
  have hxc : ¬ ({w₁ * w₂} : Set G) ⊆ Subgroup.center G :=
    CoreAssembly.singleton_not_subset_center hnab hxne
  obtain ⟨ι, hι, ⟨D⟩⟩ := S.ih {w₁ * w₂} hxc
  have hK₁ : K ≤ Subgroup.centralizer ({w₁} : Set G) :=
    NonClassical.le_centralizer_of_commutes hW₁.commutes_K hw₁.mem
  have hK₂ : K ≤ Subgroup.centralizer ({w₂} : Set G) :=
    NonClassical.le_centralizer_of_commutes hW₂.commutes_K hw₂.mem
  have hw₁x : w₁ ∈ locLayer (conjClass3 K) z := le_centralizingLayer hW₁.1 hw₁.mem
  have hw₂x : w₂ ∈ locLayer (conjClass3 K) z := le_centralizingLayer hW₂.1 hw₂.mem
  have hrootE : ∀ {δ : Fin 7 → ℤ}, δ ∈ (TypeE8.D7 3 1).roots →
      CFSG.Blueprint.Chevalley.IsRoot .E7 δ := fun hδ =>
    CFSG.Blueprint.Chevalley.mem_rootFinset.1 ((TypeE8.mem_roots_D7_iff 3 1 _).1 hδ)
  have hcen : (r₁ * r₂)⁻¹ * rρ ∈ Subgroup.center (TypeE8.K7 3 1) :=
    mul_inv_mul_mem_center3 (g := g) (hrootE hγ₁) (hrootE hγ₂) (hrootE hρ) hρpair hr₁ hr₂ hrρ
      hr₁2 hr₂2 hrρ2
  have hTF : conjSub g (TypeE8.Rroot 3 1 ρ) ∈ TypeE8.F7 3 1 := (hB8 g ρ ρ hρ hρ).1
  have hTvis : conjSub g (TypeE8.Rroot 3 1 ρ) ≤ Subgroup.centralizer ({r₁ * r₂} : Set _) :=
    (ModelFacts.E7Model.le_centralizer_iff_of_mul_mem_center hcen).mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (involution_central_fund3 hTF hrρ hrρ2 a ha)
  have hLvis : ∀ A ∈ TypeE8.F7 3 1, Commutes A (conjSub g (TypeE8.Rroot 3 1 ρ)) →
      A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)) := fun A _ hAT =>
    (ModelFacts.E7Model.le_centralizer_iff_of_mul_mem_center hcen).mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hAT a ha rρ hrρ)
  have hV1 : ∀ N ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z}, N ≠ K →
      N = Nρ ∨ Commutes Nρ N := by
    intro N hN hNK
    obtain ⟨⟨hNΩ, hNx⟩, hNz'⟩ := NonClassical.mem_centralizingMembers_pair.mp hN
    have hNz : N ∈ centralizingMembers (conjClass3 K) {z} := ⟨hNΩ, hNz'⟩
    obtain ⟨A, hA, hNA⟩ := c.exists_fund_of_ne hNz hNK
    have hAx : A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (TypeE8.K7 3 1)) :=
      (c.le_centralizer_mul_iff hNz hA hNA hw₁x hw₂x hψ₁ hψ₂).mp hNx
    have hAρ : A ≤ Subgroup.centralizer ({rρ} : Set (TypeE8.K7 3 1)) :=
      (ModelFacts.E7Model.le_centralizer_iff_of_mul_mem_center hcen).mp hAx
    have hNw : N ≤ Subgroup.centralizer ({wρ} : Set G) :=
      (c.le_centralizer_iff_single hNz hA hNA (le_centralizingLayer hNρ.1 hwρ.mem) hψρ).mpr hAρ
    rcases cp_at_member3_of_hO3 hnab S c.hO3 hNρ.mem_Ω hwρ ⟨hNΩ, hNw⟩ with h | h
    · exact Or.inr h
    · exact Or.inl h
  obtain ⟨e, he⟩ := hLayer _ hTF
  have hKx : K ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} :=
    ⟨c.hK, le_centralizer_mul_of_le3 hK₁ hK₂⟩
  have hβx : β ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} :=
    ⟨hβ, le_centralizer_mul_of_le3 (NonClassical.le_centralizer_of_commutes hβ₁ hw₁.mem)
      (NonClassical.le_centralizer_of_commutes hβ₂ hw₂.mem)⟩
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv_D8_3 c hw₁x hw₂x hψ₁ hψ₂ hK₁ hK₂ hTF hTvis hLvis
    hNρ.1 hNρ.2.1 hNρ.2.2 hV1 e he
  have hAF : conjSub g (TypeE8.Rroot 3 1 δm) ∈ TypeE8.F7 3 1 := (hB8 g δm δm hδm hδm).1
  have hAT : Commutes (conjSub g (TypeE8.Rroot 3 1 δm)) (conjSub g (TypeE8.Rroot 3 1 ρ)) :=
    (hB8 g δm ρ hδm hρ).2.1 ((iform_comm (τ := .E7) δm ρ).trans ρδm)
  have hlink := linked_of_visible_D8_3 c hw₁x hw₂x hψ₁ hψ₂ hK₁ hK₂ hβx hnKβ hTF hTvis hLvis
    hNρ.1 hNρ.2.1 hNρ.2.2 (hNρ.not_commutes_partner_of_odd htβ hT hρ oρ) hV1 hAF hAT hNδ.1
    hNδ.2.2 (hNδ.not_commutes_partner_of_odd htβ hT hδm oδm)
    (TypeE8.connected_of_fund12 hConn e he)
  have hvis : ∀ {δ : Fin 7 → ℤ} {N : Subgroup G}, δ ∈ (TypeE8.D7 3 1).roots →
      c.IsFrameMember g δ N →
      (iform (τ := .E7) δ γ₁ + iform (τ := .E7) δ γ₂) % 2 = 0 →
      N ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} := by
    intro δ N hδ hN hev
    exact ⟨hN.mem_Ω, (c.le_centralizer_mul_iff hN.1 (hB8 g δ δ hδ hδ).1 hN.2.2
      hw₁x hw₂x hψ₁ hψ₂).mpr
      ((hB9 g γ₁ γ₂ hγ₁ hγ₂ o12 r₁ hr₁ r₂ hr₂ hr₁2 hr₂2).2.2.2 δ hδ hev)⟩
  have hvisz : ∀ {δ : Fin 7 → ℤ} {N : Subgroup G}, δ ∈ (TypeE8.D7 3 1).roots →
      c.IsFrameMember g δ N →
      (iform (τ := .E7) δ γ₁ + iform (τ := .E7) δ γ₂) % 2 = 0 →
      N ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z} := fun hδ hN hev =>
    NonClassical.mem_centralizingMembers_pair.mpr ⟨hvis hδ hN hev, hN.1.2⟩
  have hW₁x : W₁ ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} :=
    ⟨hW₁.mem_Ω, le_centralizer_mul_of_le3 (isSubnormal_le hw₁.subnormal)
      (NonClassical.le_centralizer_of_commutes hW₁₂ hw₂.mem)⟩
  have hW₂x : W₂ ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} :=
    ⟨hW₂.mem_Ω, le_centralizer_mul_of_le3
      (NonClassical.le_centralizer_of_commutes (Gaps.commutes_symm hW₁₂) hw₁.mem)
      (isSubnormal_le hw₂.subnormal)⟩
  have hW₁v : W₁ ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z} :=
    NonClassical.mem_centralizingMembers_pair.mpr ⟨hW₁x, hW₁.1.2⟩
  have hW₂v : W₂ ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z} :=
    NonClassical.mem_centralizingMembers_pair.mpr ⟨hW₂x, hW₂.1.2⟩
  have hΩ := c.hΩ
  have hex := c.hex
  obtain ⟨i₁, hKi⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨K, hKx, rfl⟩)
  have hall : ∀ N ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z},
      locImg (conjClass3 K) (w₁ * w₂) N ≤ (D.hom i₁).range := fun N hN =>
    linked_le_range3 hΩ hex hP1xx hO3xx D (hlink N hN) hKi
  have hKc : K ∈ compMembers3 (conjClass3 K) (w₁ * w₂) D i₁ := ⟨hKx, hKi⟩
  have hW₁c : W₁ ∈ compMembers3 (conjClass3 K) (w₁ * w₂) D i₁ := ⟨hW₁x, hall W₁ hW₁v⟩
  have hW₂c : W₂ ∈ compMembers3 (conjClass3 K) (w₁ * w₂) D i₁ := ⟨hW₂x, hall W₂ hW₂v⟩
  have hnA1 : ¬ IsA1Comp3 D i₁ := fun hA =>
    hW₁.2.1 (eq_of_mem_compMembers_a13 hΩ hex hP1xx hO3xx hA hW₁c hKc)
  rcases kind_cases_of_not_a1 D hnA1 with ⟨t', n', hft, hadm, hk⟩ | hk
  swap
  · exact not_commutes_of_m11_comp3 hΩ hex hP1xx hO3xx hk hKc hW₁c hW₁.commutes_K
  have hexc : t' ≠ .G2 ∧ t' ≠ .trialityD4 := by
    have key : (t' = .G2 ∨ t' = .trialityD4) → False := fun ht' => hxne (by
      have := eq_involution_of_commuting_in_g2d43 hΩ hex hP1xx hO3xx D ht' hadm hk hKc hW₁c hW₂c
        c.hz hw₁ hw₂ hW₁.commutes_K hW₂.commutes_K
      rw [this]
      exact hw₂2)
    exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
  obtain ⟨X, hXr⟩ := exists_xctx3_of_comp hΩ hex hP1xx hO3xx D hk hft hadm hexc.1 hexc.2
  have hvisX : ∀ N ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z},
      locImg (conjClass3 K) (w₁ * w₂) N ≤ X.ψ.range := fun N hN => by
    rw [hXr]
    exact hall N hN
  obtain ⟨R₀, hR₀, hKR₀⟩ := X.fam_range K hKx (by rw [hXr]; exact hKi)
  obtain ⟨ht1, hn1⟩ := X.shape_of_visible_D8 hRow hft hadm hexc.1 hexc.2 c.hz hKx hR₀ hKR₀ hvisX
    φ hφ hφK
  subst ht1 hn1
  have hY : YData3 .POmegaPlus 8 := yData3_plus (by norm_num) hadm
  have hfin : Finite (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three (modelFacts_isFundTag hft) hadm
  have hcf := hY.central
  have hβi : locImg (conjClass3 K) (w₁ * w₂) β ≤ X.ψ.range := by
    rw [hXr]
    exact linked_le_range3 hΩ hex hP1xx hO3xx D
      (Relation.ReflTransGen.single ⟨hKx, hβx, hnKβ⟩) hKi
  obtain ⟨Rβ, hRβ, hβR⟩ := X.fam_range β hβx hβi
  have hdxx := hvis hdx hNdx pdx
  have hdax := hvis hda hNda (by rw [a1, a2]; rfl)
  have hdbx := hvis hdb hNdb (by rw [b1, b2]; rfl)
  have hpart : ∀ N ∈ centralizingMembers (conjClass3 K) {w₁ * w₂, z},
      ∃ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D,
        locImg (conjClass3 K) (w₁ * w₂) N = R.map X.ψ := fun N hN =>
    X.fam_range N (NonClassical.mem_centralizingMembers_pair.mp hN).1 (hvisX N hN)
  obtain ⟨RW, hRW, hWR⟩ := hpart W₁ hW₁v
  obtain ⟨Rdx, hRdx, hdxR⟩ := hpart Ndx (NonClassical.mem_centralizingMembers_pair.mpr
    ⟨hdxx, hNdx.1.2⟩)
  obtain ⟨Rda, hRda, hdaR⟩ := hpart Nda (NonClassical.mem_centralizingMembers_pair.mpr
    ⟨hdax, hNda.1.2⟩)
  obtain ⟨Rdb, hRdb, hdbR⟩ := hpart Ndb (NonClassical.mem_centralizingMembers_pair.mpr
    ⟨hdbx, hNdb.1.2⟩)
  obtain ⟨wda, hwda⟩ := c.hΩ.classical Nda hNda.mem_Ω
  obtain ⟨wdb, hwdb⟩ := c.hΩ.classical Ndb hNdb.mem_Ω
  obtain ⟨wdx, hwdx⟩ := c.hΩ.classical Ndx hNdx.mem_Ω
  obtain ⟨Wab, hWab⟩ := hNda.stdPair_of_adj hB8 hNdb hda hdb ada
  obtain ⟨Wxw, hWxw⟩ := hNdx.stdPair_of_adj hB8 hW₁ hdx hγ₁ tdx
  have hadjKβ := X.modelAdj_of_adj hcf hKx hβx hR₀ hRβ hKR₀ hβR c.hz htβ hKne hnKβ hzt hnormK
  have hadjab := X.modelAdj_of_adj hcf hdax hdbx hRda hRdb hdaR hdbR hwda hwdb
    (ne_of_linearBlockStandardPair hWab) (not_commutes_of_linearBlockStandardPair hWab)
    (Gaps.standardPair_involutions_commute h2 hWab hwda.mem hwdb.mem hwda.orderOf_eq_two
      hwdb.orderOf_eq_two)
    (Gaps.conjSub_eq_of_standardPair h2 hWab hwdb.mem hwdb.orderOf_eq_two)
  have hadjxw := X.modelAdj_of_adj hcf hdxx hW₁x hRdx hRW hdxR hWR hwdx hw₁
    (ne_of_linearBlockStandardPair hWxw) (not_commutes_of_linearBlockStandardPair hWxw)
    (Gaps.standardPair_involutions_commute h2 hWxw hwdx.mem hw₁.mem hwdx.orderOf_eq_two
      hw₁.orderOf_eq_two)
    (Gaps.conjSub_eq_of_standardPair h2 hWxw hw₁.mem hw₁.orderOf_eq_two)
  have hstd : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 8 3 1
      Nat.prime_three).K},
      L ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} →
      L' ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} →
      locImg (conjClass3 K) (w₁ * w₂) L = R.map X.ψ →
      locImg (conjClass3 K) (w₁ * w₂) L' = R'.map X.ψ →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W L L') →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R.map X.ψ) (R'.map X.ψ) := by
    intro L L' R R' hL hL' hLR hLR' ⟨W₀, hW₀⟩
    obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members hP1xx hL hL' hW₀
    rw [hLR, hLR'] at hW'
    exact ⟨W', hW'⟩
  have hcm : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 8 3 1
      Nat.prime_three).K},
      L ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} →
      L' ∈ centralizingMembers (conjClass3 K) {w₁ * w₂} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 8 3 1 Nat.prime_three).D →
      locImg (conjClass3 K) (w₁ * w₂) L = R.map X.ψ →
      locImg (conjClass3 K) (w₁ * w₂) L' = R'.map X.ψ → Commutes L L' → Commutes R R' :=
    fun hL hL' hR hLR hLR' h => (X.commutes_iff_fund hL hL' hR hLR hLR').mp h
  exact false_of_six3 hD8 hY X.ψ X.ker_le hR₀ hRβ hRda hRdb hRdx hRW hadjKβ hadjab hadjxw
    (hstd hKx hβx hKR₀ hβR ⟨W, hW⟩) (hstd hdax hdbx hdaR hdbR ⟨Wab, hWab⟩)
    (hstd hdxx hW₁x hdxR hWR ⟨Wxw, hWxw⟩)
    (hcm hKx hdax hR₀ hKR₀ hdaR hNda.commutes_K) (hcm hKx hdbx hR₀ hKR₀ hdbR hNdb.commutes_K)
    (hcm hβx hdax hRβ hβR hdaR (hβ' hda eda hNda)) (hcm hβx hdbx hRβ hβR hdbR (hβ' hdb edb hNdb))
    (hcm hKx hdxx hR₀ hKR₀ hdxR hNdx.commutes_K) (hcm hKx hW₁x hR₀ hKR₀ hWR hW₁.commutes_K)
    (hcm hβx hdxx hRβ hβR hdxR (hβ' hdx edx hNdx)) (hcm hβx hW₁x hRβ hβR hWR hβ₁)
    (hcm hdax hdxx hRda hdaR hdxR (hNda.commutes_of_orth hB8 hNdx hda hdx adx))
    (hcm hdax hW₁x hRda hdaR hWR (hNda.commutes_of_orth hB8 hW₁ hda hγ₁ a1))
    (hcm hdbx hdxx hRdb hdbR hdxR (hNdb.commutes_of_orth hB8 hNdx hdb hdx bdx))
    (hcm hdbx hW₁x hRdb hdbR hWR (hNdb.commutes_of_orth hB8 hW₁ hdb hγ₁ b1))

end Main

theorem e8R2Excluded3 : E8R2Excluded3 := by
  intro hB8 hB9 hLayer hConn hRow hD8 hP1x G _ _ _ hnab K z hR hshape c β hβ t htβ hKβ ht g p₀
    hp₀ hT
  exact r2_false3 hB8 hB9 hLayer hConn hRow hD8 hP1x hnab hR hshape c hβ htβ hKβ ht g hp₀ hT

end CFSG.ClassicalInvolution.Q3.Q3W
