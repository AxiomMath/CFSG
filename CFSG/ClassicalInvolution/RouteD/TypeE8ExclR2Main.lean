module

public import CFSG.ClassicalInvolution.RouteD.TypeE8ExclR2Layer
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase

public section

namespace CFSG.ClassicalInvolution.RouteD.TypeE8

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.WeakCT CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.Adjoint (iform iform_comm)
open CFSG.ClassicalInvolution.RouteD.NonClassical
  (exists_lieSystemData shape_of_perpTableR componentFacts_of_no_exotic card_eq_one_of_linked
    mem_centralizingMembers_pair)
open CFSG.ClassicalInvolution.RouteD.Gaps (commutes_symm exists_corr_left)

variable {p f : ℕ} [Fact p.Prime]

theorem r2_false' (hMFZ : Gaps.FundNoncentral p) (hB8 : E7FrameRelations p f)
    (hB9 : E7FrameInvolutions p f) (hLayer : E7LayerEquiv p f) (hConn : Fund12Connected p f)
    (hRow : E8D8Row' p f) (hD8 : E8D8NoThreeAdj p f) (hP1x : E8P1x p f)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    {K : Subgroup G} {z : G} (S : RouteDSetup p f K z)
    (hshape : LocalShapeT p f 1 .E7 0 (conjClass K) z) (c : ETCtx p f .E7 0 (conjClass K) K z)
    {β : Subgroup G} (hβ : β ∈ conjClass K) {t : G} (htβ : IsClassicalMember p f β t)
    (hKβ : ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W K β)
    (ht : t * z * t⁻¹ = z) (g : K7 p f) {p₀ : Fin 7} (hp₀ : p₀ = 1 ∨ p₀ = 4)
    (hT : ToralNormalAt p f c ht g p₀) : False := by
  classical
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  obtain ⟨γ₁, γ₂, dx, da, db, ρ, δm, δn, hγ₁, hγ₂, hdx, hda, hdb, hρ, hδm, hδn, eγ₁, eγ₂, edx,
    eda, edb, oρ, oδm, o12, tdx, pdx, ada, a1, a2, b1, b2, adx, bdx, hρpair, ρδm, -, -, pδm,
    -⟩ := exists_r2_roots p f p₀ hp₀
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
  have hβ' : ∀ {δ : Fin 7 → ℤ} {N : Subgroup G}, δ ∈ (D7 p f).roots →
      ((δ p₀ : ℤ) : ZMod 2) = 0 → ETCtx.IsFrameMember c g δ N → Commutes β N :=
    fun hδ he h => h.commutes_partner_of_even hMFZ hsingle hshape hβ htβ ⟨W, hW⟩ hT hδ he
  have hβ₁ : Commutes β W₁ := hβ' hγ₁ eγ₁ hW₁
  have hβ₂ : Commutes β W₂ := hβ' hγ₂ eγ₂ hW₂
  obtain ⟨w₁, hw₁⟩ := c.hΩ.classical W₁ hW₁.mem_Ω
  obtain ⟨w₂, hw₂⟩ := c.hΩ.classical W₂ hW₂.mem_Ω
  obtain ⟨wρ, hwρ⟩ := c.hΩ.classical Nρ hNρ.mem_Ω
  obtain ⟨r₁, hr₁, hr₁2, hψ₁⟩ := hW₁.exists_involution hB8 hγ₁ hw₁
  obtain ⟨r₂, hr₂, hr₂2, hψ₂⟩ := hW₂.exists_involution hB8 hγ₂ hw₂
  obtain ⟨rρ, hrρ, hrρ2, hψρ⟩ := hNρ.exists_involution hB8 hρ hwρ
  have hW₁₂ : Commutes W₁ W₂ := hW₁.commutes_of_orth hB8 hW₂ hγ₁ hγ₂ o12
  have hcard := card_closure_triple c hB9 hγ₁ hγ₂ o12 hW₁ hW₂ hw₁ hw₂ hr₁ hr₂ hr₁2 hr₂2 hψ₁ hψ₂
    hW₁₂
  have hP1xx : LocalOddCentral (conjClass K) {w₁ * w₂} :=
    hP1x G hnab K z S W₁ W₂ w₁ w₂ hW₁.mem_Ω hW₂.mem_Ω hw₁ hw₂ hW₁.commutes_K hW₂.commutes_K hW₁₂
      hcard
  have hw₁2 : w₁ * w₁ = 1 := DeltaClosure.sq_eq_one hw₁
  have hw₂2 : w₂ * w₂ = 1 := DeltaClosure.sq_eq_one hw₂
  have hz2 : z * z = 1 := DeltaClosure.sq_eq_one c.hz
  have hzw₁ : z * w₁ = w₁ * z := hW₁.commutes_K z c.hz.mem w₁ hw₁.mem
  have hxne : w₁ * w₂ ≠ 1 := by
    intro h1
    have hw : w₂ = w₁ := by
      rw [← inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hw₁2]
    have hle := Balance.Theorem5.card_closure_pair_le_four (a := z) (b := w₁) hz2 hw₁2 hzw₁
    have hset : ({z, w₁, w₂} : Set G) = {z, w₁} := by
      subst hw
      ext y
      simp
    rw [hset] at hcard
    omega
  have hxc : ¬ ({w₁ * w₂} : Set G) ⊆ Subgroup.center G :=
    singleton_not_subset_center hnab hxne
  obtain ⟨D⟩ := exists_lieSystemData S.ih hxc
  have hK₁ : K ≤ Subgroup.centralizer ({w₁} : Set G) :=
    NonClassical.le_centralizer_of_commutes hW₁.commutes_K hw₁.mem
  have hK₂ : K ≤ Subgroup.centralizer ({w₂} : Set G) :=
    NonClassical.le_centralizer_of_commutes hW₂.commutes_K hw₂.mem
  have hw₁x : w₁ ∈ locLayer (conjClass K) z := le_centralizingLayer hW₁.1 hw₁.mem
  have hw₂x : w₂ ∈ locLayer (conjClass K) z := le_centralizingLayer hW₂.1 hw₂.mem
  have hrootE : ∀ {δ : Fin 7 → ℤ}, δ ∈ (D7 p f).roots →
      CFSG.Blueprint.Chevalley.IsRoot .E7 δ := fun hδ =>
    CFSG.Blueprint.Chevalley.mem_rootFinset.1 ((mem_roots_D7_iff p f _).1 hδ)
  have hcen : (r₁ * r₂)⁻¹ * rρ ∈ Subgroup.center (K7 p f) :=
    ModelFacts.E7Model.mul_inv_mul_mem_center S.odd S.five (g := g) (hrootE hγ₁) (hrootE hγ₂)
      (hrootE hρ) hρpair hr₁ hr₂ hrρ hr₁2 hr₂2 hrρ2
  have hTF : conjSub g (Rroot p f ρ) ∈ F7 p f := (hB8 g ρ ρ hρ hρ).1
  have hTvis : conjSub g (Rroot p f ρ) ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)) :=
    (ModelFacts.E7Model.le_centralizer_iff_of_mul_mem_center hcen).mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (ModelFacts.E7Model.involution_central_fund S.odd S.five hTF hrρ hrρ2 a ha)
  have hLvis : ∀ A ∈ F7 p f, Commutes A (conjSub g (Rroot p f ρ)) →
      A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)) := fun A _ hAT =>
    (ModelFacts.E7Model.le_centralizer_iff_of_mul_mem_center hcen).mpr fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hAT a ha rρ hrρ)
  have hcenG : Subgroup.center G = ⊥ := center_eq_bot hnab
  have hV1 : ∀ N ∈ centralizingMembers (conjClass K) {w₁ * w₂, z}, N ≠ K →
      N = Nρ ∨ Commutes Nρ N := by
    intro N hN hNK
    obtain ⟨⟨hNΩ, hNx⟩, hNz'⟩ := mem_centralizingMembers_pair.mp hN
    have hNz : N ∈ centralizingMembers (conjClass K) {z} := ⟨hNΩ, hNz'⟩
    obtain ⟨A, hA, hNA⟩ := c.exists_fund_of_ne hNz hNK
    have hAx : A ≤ Subgroup.centralizer ({r₁ * r₂} : Set (K7 p f)) :=
      (c.le_centralizer_mul_iff hNz hA hNA hw₁x hw₂x hψ₁ hψ₂).mp hNx
    have hAρ : A ≤ Subgroup.centralizer ({rρ} : Set (K7 p f)) :=
      (ModelFacts.E7Model.le_centralizer_iff_of_mul_mem_center hcen).mp hAx
    have hNw : N ≤ Subgroup.centralizer ({wρ} : Set G) :=
      (c.le_centralizer_iff_single hNz hA hNA (le_centralizingLayer hNρ.1 hwρ.mem) hψρ).mpr hAρ
    rcases S.cp_at_member hcenG hNρ.mem_Ω hwρ ⟨hNΩ, hNw⟩ with h | h
    · exact Or.inr h
    · exact Or.inl h
  obtain ⟨e, he⟩ := hLayer _ hTF
  have hKx : K ∈ centralizingMembers (conjClass K) {w₁ * w₂} :=
    ⟨c.hK, le_centralizer_mul_of_le hK₁ hK₂⟩
  have hβx : β ∈ centralizingMembers (conjClass K) {w₁ * w₂} :=
    ⟨hβ, le_centralizer_mul_of_le (NonClassical.le_centralizer_of_commutes hβ₁ hw₁.mem)
      (NonClassical.le_centralizer_of_commutes hβ₂ hw₂.mem)⟩
  obtain ⟨φ, hφ, hφK⟩ := exists_visible_equiv_D8 c hw₁x hw₂x hψ₁ hψ₂ hK₁ hK₂ hTF hTvis hLvis
    hNρ.1 hNρ.2.1 hNρ.2.2 hV1 e he
  have hAF : conjSub g (Rroot p f δm) ∈ F7 p f := (hB8 g δm δm hδm hδm).1
  have hAT : Commutes (conjSub g (Rroot p f δm)) (conjSub g (Rroot p f ρ)) :=
    (hB8 g δm ρ hδm hρ).2.1 ((iform_comm (τ := .E7) δm ρ).trans ρδm)
  have hlink := linked_of_visible_D8 c hw₁x hw₂x hψ₁ hψ₂ hK₁ hK₂ hβx hnKβ hTF hTvis hLvis hNρ.1
    hNρ.2.1 hNρ.2.2 (hNρ.not_commutes_partner_of_odd htβ hT hρ oρ) hV1 hAF hAT hNδ.1 hNδ.2.2
    (hNδ.not_commutes_partner_of_odd htβ hT hδm oδm) (connected_of_fund12 hConn e he)
  have hcard₀ : D.card = 1 :=
    card_eq_one_of_linked c.hΩ c.hex hP1xx D hKx c.hz.mem hlink
  have hsub₀ : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard₀.le
  have hall : ∀ i₀ : Fin D.card, ∀ N ∈ centralizingMembers (conjClass K) {w₁ * w₂},
      N ∈ Gaps.compMembers (conjClass K) (w₁ * w₂) D i₀ := by
    intro i₀ N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub₀.elim j i₀ ▸ hj⟩
  have hW₁x : W₁ ∈ centralizingMembers (conjClass K) {w₁ * w₂} :=
    ⟨hW₁.mem_Ω, le_centralizer_mul_of_le (le_centralizer_of_isClassicalMember hw₁)
      (NonClassical.le_centralizer_of_commutes hW₁₂ hw₂.mem)⟩
  have hW₂x : W₂ ∈ centralizingMembers (conjClass K) {w₁ * w₂} :=
    ⟨hW₂.mem_Ω, le_centralizer_mul_of_le
      (NonClassical.le_centralizer_of_commutes (commutes_symm hW₁₂) hw₁.mem)
      (le_centralizer_of_isClassicalMember hw₂)⟩
  have hexc : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = ⟨0, by omega⟩ := hsub₀.elim i _
    subst hi
    exact G2D4.tag_ne_of_commuting_triple S.odd c.hΩ c.hex D (hall _ K hKx) (hall _ W₁ hW₁x)
      (hall _ W₂ hW₂x) hW₁.commutes_K hW₂.commutes_K hW₁₂
  obtain ⟨-, hperf⟩ := componentFacts_of_no_exotic D S.odd (by have := S.five; omega) hexc
  obtain ⟨-, i₁, ht1, hn1, -, -⟩ := shape_of_perpTableR S.odd S.five c.hΩ c.hex hP1xx D hexc hKx
    c.hz hlink (D8Layer.rel p f) φ hφ hφK hRow
  have hexp : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht1.symm.trans h) (by decide)
  have hA1 : ¬ (D.tag i₁ = .PSL ∧ D.rank i₁ = 2) := fun h => by
    rw [ht1] at h
    exact absurd h.1 (by decide)
  have hvis : ∀ {δ : Fin 7 → ℤ} {N : Subgroup G}, δ ∈ (D7 p f).roots →
      ETCtx.IsFrameMember c g δ N →
      (iform (τ := .E7) δ γ₁ + iform (τ := .E7) δ γ₂) % 2 = 0 →
      N ∈ centralizingMembers (conjClass K) {w₁ * w₂} := by
    intro δ N hδ hN hev
    exact ⟨hN.mem_Ω, (c.le_centralizer_mul_iff hN.1 (hB8 g δ δ hδ hδ).1 hN.2.2
      hw₁x hw₂x hψ₁ hψ₂).mpr
      ((hB9 g γ₁ γ₂ hγ₁ hγ₂ o12 r₁ hr₁ r₂ hr₂ hr₁2 hr₂2).2.2.2 δ hδ hev)⟩
  have hdxx := hvis hdx hNdx pdx
  have hdax := hvis hda hNda (by rw [a1, a2]; rfl)
  have hdbx := hvis hdb hNdb (by rw [b1, b2]; rfl)
  have hcorr : ∀ N ∈ centralizingMembers (conjClass K) {w₁ * w₂},
      ∃ R, Gaps.Corr (conjClass K) (w₁ * w₂) D i₁ N R := fun N hN =>
    exists_corr_left c.hΩ c.hex D (hall i₁ N hN)
  obtain ⟨RK, hRK⟩ := hcorr K hKx
  obtain ⟨Rβ, hRβ⟩ := hcorr β hβx
  obtain ⟨RW, hRW⟩ := hcorr W₁ hW₁x
  obtain ⟨Rdx, hRdx⟩ := hcorr Ndx hdxx
  obtain ⟨Rda, hRda⟩ := hcorr Nda hdax
  obtain ⟨Rdb, hRdb⟩ := hcorr Ndb hdbx
  obtain ⟨wda, hwda⟩ := c.hΩ.classical Nda hNda.mem_Ω
  obtain ⟨wdb, hwdb⟩ := c.hΩ.classical Ndb hNdb.mem_Ω
  obtain ⟨wdx, hwdx⟩ := c.hΩ.classical Ndx hNdx.mem_Ω
  obtain ⟨Wab, hWab⟩ := hNda.stdPair_of_adj hB8 hNdb hda hdb ada
  obtain ⟨Wxw, hWxw⟩ := hNdx.stdPair_of_adj hB8 hW₁ hdx hγ₁ tdx
  have hadjKβ := NonClassical.corr_modelAdj hMFZ c.hΩ hP1xx (hperf i₁) hA1 hRK hRβ c.hz htβ hKne
    hnKβ hzt hnormK
  have hadjab := NonClassical.corr_modelAdj hMFZ c.hΩ hP1xx (hperf i₁) hA1 hRda hRdb hwda hwdb
    (ne_of_linearBlockStandardPair hWab) (not_commutes_of_linearBlockStandardPair hWab)
    (Gaps.standardPair_involutions_commute h2 hWab hwda.mem hwdb.mem hwda.orderOf_eq_two
      hwdb.orderOf_eq_two)
    (Gaps.conjSub_eq_of_standardPair h2 hWab hwdb.mem hwdb.orderOf_eq_two)
  have hadjxw := NonClassical.corr_modelAdj hMFZ c.hΩ hP1xx (hperf i₁) hA1 hRdx hRW hwdx hw₁
    (ne_of_linearBlockStandardPair hWxw) (not_commutes_of_linearBlockStandardPair hWxw)
    (Gaps.standardPair_involutions_commute h2 hWxw hwdx.mem hw₁.mem hwdx.orderOf_eq_two
      hw₁.orderOf_eq_two)
    (Gaps.conjSub_eq_of_standardPair h2 hWxw hw₁.mem hw₁.orderOf_eq_two)
  have hstd : ∀ {L L' : Subgroup G} {R R' : Subgroup
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K},
      Gaps.Corr (conjClass K) (w₁ * w₂) D i₁ L R → Gaps.Corr (conjClass K) (w₁ * w₂) D i₁ L' R' →
      (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W L L') →
      ∃ W, LinearBlockStandardPair (GaloisField p f) W (R.map (D.hom i₁)) (R'.map (D.hom i₁)) := by
    intro L L' R R' hL hL' hs
    obtain ⟨Ws, hWs⟩ := hs
    obtain ⟨W', hW'⟩ := Gaps.linearBlockStandardPair_locImg_of_members hP1xx hL.1 hL'.1 hWs
    rw [hL.2.2, hL'.2.2] at hW'
    exact ⟨W', hW'⟩
  have hcm : ∀ {L L' : Subgroup G} {R R' : Subgroup
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).K},
      Gaps.Corr (conjClass K) (w₁ * w₂) D i₁ L R → Gaps.Corr (conjClass K) (w₁ * w₂) D i₁ L' R' →
      Commutes L L' → Commutes R R' := fun hL hL' h =>
    (Gaps.corr_commutes c.hΩ hP1xx (hperf i₁) hL hL').mp h
  refine false_of_six (hD8 S.odd S.five) S.odd S.five ht1 hn1 hexp (D.hom i₁) (D.ker_le_center i₁)
    hRK.2.1 hRβ.2.1 hRda.2.1 hRdb.2.1 hRdx.2.1 hRW.2.1 hadjKβ hadjab hadjxw
    (hstd hRK hRβ ⟨W, hW⟩) (hstd hRda hRdb ⟨Wab, hWab⟩) (hstd hRdx hRW ⟨Wxw, hWxw⟩)
    (hcm hRK hRda hNda.commutes_K) (hcm hRK hRdb hNdb.commutes_K)
    (hcm hRβ hRda (hβ' hda eda hNda)) (hcm hRβ hRdb (hβ' hdb edb hNdb))
    (hcm hRK hRdx hNdx.commutes_K) (hcm hRK hRW hW₁.commutes_K)
    (hcm hRβ hRdx (hβ' hdx edx hNdx)) (hcm hRβ hRW hβ₁)
    (hcm hRda hRdx (hNda.commutes_of_orth hB8 hNdx hda hdx adx))
    (hcm hRda hRW (hNda.commutes_of_orth hB8 hW₁ hda hγ₁ a1))
    (hcm hRdb hRdx (hNdb.commutes_of_orth hB8 hNdx hdb hdx bdx))
    (hcm hRdb hRW (hNdb.commutes_of_orth hB8 hW₁ hdb hγ₁ b1))

end CFSG.ClassicalInvolution.RouteD.TypeE8
