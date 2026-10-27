module

public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainAssembly
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeMain

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def P1RowA (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeA p f 2 (conjClass K) z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LocalOddCentral (conjClass K) {z * w}

@[expose] def P1RowU (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeU p f 2 (conjClass K) z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LocalOddCentral (conjClass K) {z * w}

@[expose] def P1RowSL4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSL 4 (conjClass K) z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LocalOddCentral (conjClass K) {z * w}

@[expose] def P1RowSp2 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSp 2 (conjClass K) z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LocalOddCentral (conjClass K) {z * w}

@[expose] def P1RowSU4 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSU 4 (conjClass K) z →
      ∀ M ∈ conjClass K, ∀ w : G, IsClassicalMember p f M w → Commutes K M → z ≠ w →
        LocalOddCentral (conjClass K) {z * w}

structure ProductOfTwoP1Rows (p f : ℕ) [Fact p.Prime] : Prop where
  a : P1RowA p f
  u : P1RowU p f
  sl4 : P1RowSL4 p f
  sp2 : P1RowSp2 p f
  su4 : P1RowSU4 p f

theorem ProductOfTwoP1Rows.of_productOfTwoP1 (h : ProductOfTwoP1 p f) :
    ProductOfTwoP1Rows p f := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · intro G _ _ _ hnab K z S _ M hM w hw hKM hzw
    exact h G hnab K z S M hM w hw hKM hzw

namespace ProductOfTwoP1Rows

theorem twinP1A (h : ProductOfTwoP1Rows p f) : TwinP1A p f := by
  intro G _ _ _ hnab K z S hshape M hM hMK w hw
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  have hMFZ := Gaps.fundNoncentral p
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hKM : Commutes K M :=
    (Gaps.commutes_or_eq_of_involution hMFZ S.inClass S.exact S.p1 D hKz hM S.cls).resolve_right hMK
  have hA₁ : ∀ i : Fin D.card, D.tag i = .PSL → D.rank i = 2 → i = i₀ := by
    intro i hi hri
    have h1 := i.isLt
    have h2 := i₀.isLt
    have h3 := i₁.isLt
    have h4 : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have h5 : i.val ≠ i₁.val := fun e => by
      have := congrArg D.rank (Fin.ext e : i = i₁)
      omega
    exact Fin.ext (by omega)
  have hzw : z ≠ w := by
    intro hzw
    subst hzw
    obtain ⟨i, hit, hir, hiK⟩ := Gaps.locImg_eq_range_of_involution hMFZ D hKz S.cls
    obtain ⟨j, hjt, hjr, hjM⟩ := Gaps.locImg_eq_range_of_involution hMFZ D hM hw
    rw [hA₁ i hit hir] at hiK
    rw [hA₁ j hjt hjr] at hjM
    exact hMK (locImg_injOn S.inClass S.p1 hM hKz (hjM.trans hiK.symm))
  exact h.a G hnab K z S ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ M hM.1 w hw hKM hzw

theorem twinP1U (h : ProductOfTwoP1Rows p f) : TwinP1U p f := by
  intro G _ _ _ hnab K z S hshape M hM hMK w hw
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := hshape
  have hMFZ := Gaps.fundNoncentral p
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hKM : Commutes K M :=
    (Gaps.commutes_or_eq_of_involution hMFZ S.inClass S.exact S.p1 D hKz hM S.cls).resolve_right hMK
  have hA₁ : ∀ i : Fin D.card, D.tag i = .PSL → D.rank i = 2 → i = i₀ := by
    intro i hi hri
    have h1 := i.isLt
    have h2 := i₀.isLt
    have h3 := i₁.isLt
    have h4 : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have h5 : i.val ≠ i₁.val := fun e => by
      have := congrArg D.tag (Fin.ext e : i = i₁)
      rw [hi, ht₁] at this
      exact absurd this (by decide)
    exact Fin.ext (by omega)
  have hzw : z ≠ w := by
    intro hzw
    subst hzw
    obtain ⟨i, hit, hir, hiK⟩ := Gaps.locImg_eq_range_of_involution hMFZ D hKz S.cls
    obtain ⟨j, hjt, hjr, hjM⟩ := Gaps.locImg_eq_range_of_involution hMFZ D hM hw
    rw [hA₁ i hit hir] at hiK
    rw [hA₁ j hjt hjr] at hjM
    exact hMK (locImg_injOn S.inClass S.p1 hM hKz (hjM.trans hiK.symm))
  exact h.u G hnab K z S ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ M hM.1 w hw hKM hzw

theorem twinP1 (h : ProductOfTwoP1Rows p f) : TwinP1 p f :=
  ⟨h.twinP1A, h.twinP1U⟩

theorem twinSp2Chain (h : ProductOfTwoP1Rows p f) (hlink : TwinSp2Linked p f) :
    TwinSp2Chain p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨Λ⟩ := hshape.nonempty_spLayer
  obtain ⟨j₀, hj₀, hKj₀⟩ := SpLayer.exists_other_of_self S.five (mem_conjClass_self K) S.cls Λ
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, hK₂i⟩ :=
    exists_chain_of_layer S.odd S.five (center_eq_bot hnab) S.inClass S.exact S.ih
      (mem_conjClass_self K) (single_class K) S.cls S.p1 Λ.D Λ.i₁
      (by have := Λ.card_eq; omega) Λ.rest
      (by
        rintro ⟨h', -⟩
        rw [Λ.tag_eq] at h'
        exact absurd h' (by decide))
      ⟨j₀, hj₀, hKj₀⟩
      (fun M hM w hw hc hzw => h.sp2 G hnab K z S hshape M hM w hw hc hzw)
      (fun K₂ hK₂ hi w hw => hlink G hnab K z S hshape Λ K₂ hK₂ hi w hw)
      (NonClassical.twinPartnerFactTwin_pOmegaPlus_four S.odd S.five)
  exact ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, hK₂i⟩

theorem twinSU4ChainData (h : ProductOfTwoP1Rows p f) (hlink : TwinSU4Linked p f) :
    TwinSU4ChainData p f := by
  intro G _ _ _ hnab K z S hshape
  obtain ⟨Λ⟩ := hshape.nonempty_suLayer
  obtain ⟨j₀, hj₀, hKj₀⟩ := Λ.exists_other_of_self S.odd S.five (mem_conjClass_self K) S.cls
  obtain ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, hK₂i⟩ :=
    exists_chain_of_layer S.odd S.five (center_eq_bot hnab) S.inClass S.exact S.ih
      (mem_conjClass_self K) (single_class K) S.cls S.p1 Λ.D Λ.i₁
      (by have := Λ.card_eq; omega) Λ.rest
      (by
        rintro ⟨h', -⟩
        rw [Λ.tag_eq] at h'
        exact absurd h' (by decide))
      ⟨j₀, hj₀, hKj₀⟩
      (fun M hM w hw hc hzw => h.su4 G hnab K z S hshape M hM w hw hc hzw)
      (fun K₂ hK₂ hi w hw => hlink G hnab K z S hshape Λ K₂ hK₂ hi w hw)
      (NonClassical.twinPartnerFactTwin_pOmegaPlus_four S.odd S.five)
  exact ⟨K₁, K₂, z₁, hK₁, hK₂, hz₁, c02, p01, p12, Λ, hK₂i⟩

theorem twinSL4Bridge (h : ProductOfTwoP1Rows p f)
    (hD4 : D4LinearClique p f .POmegaPlus 4 f) (hAct : TwinSL4Action p f) :
    TwinSL4Bridge p f := by
  intro G _ _ _ hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02
  classical
  have hcen := center_eq_bot hnab
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hf : 0 < f := pos_of_five_le S.five
  have hMFZ := Gaps.fundNoncentral p
  obtain ⟨x₀, hx₀⟩ := hΩ.classical (j 1) (hjΩ 1)
  have hj0 : j 0 ≤ Subgroup.centralizer ({t * x₀} : Set G) :=
    hAct G hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02 x₀ hx₀
  obtain ⟨W₀, hW₀⟩ := hKβ
  obtain ⟨g, hg⟩ := hβ
  have hβΩ : β ∈ conjClass K := ⟨g, hg⟩
  have htg : t = g * z * g⁻¹ :=
    unique_involution_of_isClassicalMember
      (CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd) (hex β hβΩ) ht
      (hg ▸ S.cls.conj g)
  have hP1t : LocalOddCentral (conjClass K) {t} := by
    rw [htg]
    exact Gaps.localOddCentral_conj hΩ.conjInvariant g z S.p1
  have hshape_t : LocalShapeT p f 2 .PSL 4 (conjClass K) t := by
    rw [htg]
    exact hshape.conj hΩ.conjInvariant g
  have hshape_β : LocalShapeT p f 2 .PSL 4 (conjClass β) t := by
    rw [conjClass_eq_of_mem hβΩ]
    exact hshape_t
  obtain ⟨Dt, hcard, i₁, htag, hrank, hrest⟩ := hshape_t
  have hbig : ¬ (Dt.tag i₁ = .PSL ∧ Dt.rank i₁ = 2) := by
    rintro ⟨-, h'⟩
    rw [hrank] at h'
    omega
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g β := single_class_of_mem hβΩ
  obtain ⟨T, hT, hTβ, hTcomm⟩ := exists_twin_of_layer hMFZ hΩ hex hP1t Dt i₁ (by omega) hrest
    hbig hβΩ ht
  have hnotK : ¬ K ≤ Subgroup.centralizer ({t} : Set G) :=
    S.not_le_centralizer_of_linear hcen (mem_conjClass_self K) hβΩ ht ⟨W₀, hW₀⟩
  have hKx₀ : K ≤ Subgroup.centralizer ({x₀} : Set G) := le_centralizer_of_commutes (hjK 1) hx₀.mem
  have htx : t ≠ x₀ := by
    intro h'
    apply hnotK
    rw [h']
    exact hKx₀
  have hj1β : Commutes β (j 1) := hjβ 1 (by decide)
  have hj1t : j 1 ∈ centralizingMembers (conjClass K) {t} :=
    ⟨hjΩ 1, le_centralizer_of_commutes (Commutes.symm hj1β) ht.mem⟩
  have hj1ne : j 1 ≠ β := fun h' =>
    not_commutes_of_linearBlockStandardPair hW₀ (h' ▸ hjK 1)
  have hj1T : j 1 ≠ T := by
    intro h'
    have hTx : IsClassicalMember p f T x₀ := h' ▸ hx₀
    have heq := centralizingMembers_eq_of_twin S.odd hf hΩ ht hTx (hsingle T hT.1) hT hTcomm
    have hKmem : K ∈ centralizingMembers (conjClass K) {x₀} := ⟨mem_conjClass_self K, hKx₀⟩
    rw [heq] at hKmem
    exact hnotK hKmem.2
  have hP1x : LocalOddCentral (conjClass K) {t * x₀} := by
    have := h.sl4 G hnab β t (S.of_mem_conjClass hβΩ ht) hshape_β (j 1)
      (by rw [conjClass_eq_of_mem hβΩ]; exact hjΩ 1) x₀ hx₀ hj1β htx
    rwa [conjClass_eq_of_mem hβΩ] at this
  have hj0β : j 0 ≠ β := fun h' =>
    not_commutes_of_linearBlockStandardPair hW₀ (h' ▸ hjK 0)
  have hnc : ¬ Commutes β (j 0) := by
    intro hc
    have h1 : j 0 ≤ Subgroup.centralizer ({t} : Set G) :=
      le_centralizer_of_commutes (Commutes.symm hc) ht.mem
    have h2 : j 0 ≤ Subgroup.centralizer ({x₀} : Set G) := fun n hn =>
      mem_centralizer_right_of_mul (hj0 hn) (h1 hn)
    exact S.not_le_centralizer_of_linear hcen (hjΩ 0) (hjΩ 1) hx₀ hp01 h2
  have hlink : LinkedAtProduct (conjClass K) β t x₀ := ⟨j 0, ⟨hjΩ 0, hj0⟩, hj0β, hnc⟩
  obtain ⟨D, c, htg4, hrk, hexp, -, hβc, hj1c, -, hallc⟩ :=
    exists_d4_component_of_twin_product S.odd S.five hcen hΩ hex S.ih hβΩ hsingle ht hP1t hT hTβ
      hTcomm hj1t hj1ne hj1T hx₀ htx hP1x hlink
  have hj0c := hallc (j 0) ⟨hjΩ 0, hj0⟩ hj0β hnc
  have hperf := fundPerfect_modelUniv S.odd (D.isFundTag c) (D.admissible c)
    (by rw [hexp]; have := S.five; omega)
  obtain ⟨R₁, hR₁⟩ := exists_corr_left hΩ hex D hj1c
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D hβc
  obtain ⟨R₃, hR₃⟩ := exists_corr_left hΩ hex D hj0c
  have hne : R₁ ≠ R₂ := fun h' => hj1ne (corr_unique_right hΩ hP1x hR₁ (h' ▸ hR₂))
  have hcomm : Commutes R₁ R₂ :=
    (corr_commutes hΩ hP1x hperf hR₁ hR₂).mp (Commutes.symm hj1β)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_locImg_of_members hP1x hj1c.1 hj0c.1
    (linearBlockStandardPair_symm hp01.choose_spec)
  rw [hR₁.2.2, hR₃.2.2] at hW₁
  have hD4' : D4LinearClique p f (D.tag c) (D.rank c) (D.exp c) := by
    rw [htg4, hrk, hexp]
    exact hD4
  obtain ⟨W₂, hW₂⟩ := hD4' _ (D.hom c) (D.ker_le_center c) R₁ hR₁.2.1 R₂ hR₂.2.1 R₃ hR₃.2.1 hne
    hcomm ⟨W₁, hW₁⟩
  rw [← hR₂.2.2, ← hR₃.2.2] at hW₂
  exact linearBlockStandardPair_of_locImg (by have := S.five; omega) (oddCoverSL3 S.five) hΩ hP1x
    hβc.1 hj0c.1 hW₂

theorem pieceTwinSL4 (h : ProductOfTwoP1Rows p f)
    (hD4 : D4LinearClique p f .POmegaPlus 4 f) (hAct : TwinSL4Action p f) :
    PieceTwinSL4 p f :=
  pieceTwinSL4_of_bridge (h.twinSL4Bridge hD4 hAct)

end ProductOfTwoP1Rows

end CFSG.ClassicalInvolution.Generic.CoreAssembly
