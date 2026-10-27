module

public import CFSG.ClassicalInvolution.RouteD.LocalMembers
public import CFSG.ClassicalInvolution.RouteD.TypeCRecognition
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  isHyperbolicPlane_stdPlane longBlock planeTorus)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem exists_psp_hom {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card) (ht : D.tag i = .PSp) {m : ℕ} (hr : D.rank i = m) :
    ∃ ψ : StatedSp m (GaloisField p f) →* X,
      ψ.ker ≤ Subgroup.center (StatedSp m (GaloisField p f)) ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups (D.tag i)
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)) ↔
        ∃ P, IsHyperbolicPlane P ∧ K = (planeGroup P).map ψ := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = .PSp) (hN : n = m) (hE : e = f)
      (φ : (modelUniv t n p e Fact.out).K →* X) (hφ : φ.ker ≤ Subgroup.center _),
      StatedLieAdmissible t n p e →
      ∃ ψ : StatedSp m (GaloisField p f) →* X,
        ψ.ker ≤ Subgroup.center (StatedSp m (GaloisField p f)) ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
            K = R.map φ) ↔ ∃ P, IsHyperbolicPlane P ∧ K = (planeGroup P).map ψ := by
    intro t n e hT hN hE φ hφ hA
    have hE' : f = e := hE.symm
    subst hT hN hE'
    refine ⟨φ, hφ, rfl, fun K => ?_⟩
    constructor
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨P, hP, rfl⟩ := (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hA R).1 hR
      exact ⟨P, hP, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨planeGroup P, (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hA _).2
        ⟨P, hP, rfl⟩, rfl⟩
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h (by decide)
  exact key _ _ _ ht hr he (D.hom i) (D.ker_le_center i) (D.admissible i)


section Dict

variable {G : Type} [Group G]

structure ShapeCDict (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (z : G) where
  ψ : StatedSp m (GaloisField p f) →* locQuot Ω z
  ker_le : ψ.ker ≤ Subgroup.center (StatedSp m (GaloisField p f))
  Q₀ : Subgroup (locQuot Ω z)
  commutes : Commutes Q₀ ψ.range
  mem_fam : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ locFamily Ω z
  fam_cases : ∀ K' ∈ locFamily Ω z,
    K' ≤ Q₀ ∨ ∃ P, IsHyperbolicPlane P ∧ K' = (planeGroup P).map ψ
  card_le : Nat.card Q₀ ≤ Nat.card SL(2, GaloisField p f)

theorem LocalShapeC.nonempty_dict {G : Type} [Group G] [Finite G] {m : ℕ} {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (h : LocalShapeC p f m Ω z) :
    Nonempty (ShapeCDict p f m Ω z) := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  obtain ⟨ψ₁, hker₁, hrange₁, hfund₁⟩ := exists_psp_hom D i₁ ht₁ hr₁
  obtain ⟨ψ₀, hker₀, hrange₀, hfund₀⟩ := exists_psl_hom D i₀ ht₀ (k := 1) hr₀
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  have hsingle : FundamentalSingleClass (D.tag i₁)
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ p _ _ (D.isFundTag i₁)
      (D.admissible i₁) (by rw [ht₁]; decide) (by rw [ht₁]; decide)
  refine ⟨{
    ψ := ψ₁
    ker_le := hker₁
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_ }⟩
  · rw [hrange₁]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro P hP
    obtain ⟨R', hR', hRR'⟩ := (hfund₁ ((planeGroup P).map ψ₁)).mpr ⟨P, hP, rfl⟩
    rw [hRR']
    exact D.map_mem_of_single_class hΦ i₁ hsingle hR'
  · intro K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    have hi := i.isLt
    have hi₀ := i₀.isLt
    have hi₁ := i₁.isLt
    have hne' : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have : i = i₀ ∨ i = i₁ := by
      rcases Nat.lt_or_ge i.val 1 with h1 | h1
      · by_cases h0 : i₀.val = 0
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      · by_cases h0 : i₀.val = 1
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
    rcases this with rfl | rfl
    · exact Or.inl (Subgroup.map_le_range _ _)
    · exact Or.inr ((hfund₁ _).mp ⟨R, hR, rfl⟩)
  · show Nat.card (D.hom i₀).range ≤ _
    rw [← hrange₀]
    exact Nat.card_le_card_of_surjective (ψ₀.rangeRestrict) ψ₀.rangeRestrict_surjective

end Dict

section Field

theorem natCard_galoisField_of_five_le (h5 : 5 ≤ p ^ f) :
    Nat.card (GaloisField p f) = p ^ f := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  exact GaloisField.card p f hf

theorem four_le_natCard_galoisField (h5 : 5 ≤ p ^ f) : 4 ≤ Nat.card (GaloisField p f) := by
  rw [natCard_galoisField_of_five_le h5]
  omega

theorem exists_unit_ne_inv (h5 : 5 ≤ p ^ f) :
    ∃ a : (GaloisField p f)ˣ, ((a : GaloisField p f)) ≠ ((a⁻¹ : (GaloisField p f)ˣ) : _) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have : Finite (GaloisField p f) := inferInstance
  obtain ⟨t, ht⟩ := CFSG.ClassicalInvolution.ModelFacts.OddCover.exists_unit_sq_ne_one
    (K := GaloisField p f) (by rw [natCard_galoisField_of_five_le h5]; exact h5)
  refine ⟨t, fun h => ht ?_⟩
  have h' : t = t⁻¹ := Units.ext h
  rw [sq]
  calc t * t = t * t⁻¹ := by rw [← h']
    _ = 1 := mul_inv_cancel t

end Field

section DictAPI

variable {G : Type} [Group G] [Finite G] {m : ℕ} {Ω : Set (Subgroup G)}

theorem eq_one_of_mem_planeGroup_of_mem_center {F : Type} [Field F] (hm : 2 ≤ m)
    {P : Submodule F (Fin m ⊕ Fin m → F)} (hP : IsHyperbolicPlane P) {r : StatedSp m F}
    (hr : r ∈ planeGroup P) (hc : r ∈ Subgroup.center (StatedSp m F)) : r = 1 := by
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP
    (⟨0, by omega⟩ : Fin m)
  rw [hg] at hr
  obtain ⟨y, ⟨B, rfl⟩, rfl⟩ := hr
  have hc' : g * longBlock F m ⟨0, by omega⟩ B * g⁻¹ ∈ Subgroup.center (StatedSp m F) := hc
  have h1 := Models.SymplecticPairs.mem_center_of_conj_mem_center hc'
  have h2 : longBlock F m ⟨0, by omega⟩ B = 1 :=
    Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup h1
      (Models.SymplecticPairs.isSupp_longBlock _ B) (t := Sum.inl (⟨1, by omega⟩ : Fin m)) (by
        rintro (h | h)
        · have := Sum.inl_injective h
          simp at this
        · exact Sum.inl_ne_inr h)
  simp [h2]

theorem typeC_locImg_self_le_Q₀ (hm : 2 ≤ m) (h5 : 5 ≤ p ^ f) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (d : ShapeCDict p f m Ω z) : locImg Ω z K ≤ d.Q₀ := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases _ hmem with h | ⟨P, hP, hPK⟩
  · exact h
  · exfalso
    let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hKz hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
        locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hPK] at hzK
    obtain ⟨r, hrP, hr⟩ := hzK
    have hcentral : ∀ w : locQuot Ω z,
        w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {z} w'.2)
    have hrc : r ∈ Subgroup.center (StatedSp m (GaloisField p f)) := by
      refine Models.SymplecticPairs.mem_center_of_forall_commutator_mem_center
        (Models.SymplecticPairs.isPerfect_statedSp_of_four_le (four_le_natCard_galoisField h5))
        fun s => d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    have hr1 : r = 1 := eq_one_of_mem_planeGroup_of_mem_center hm hP hrP hrc
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z)))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem typeC_eq_of_locImg_le_Q₀ (hm : 2 ≤ m) (h5 : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLQ : locImg Ω z L ≤ d.Q₀) :
    L = K := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hKQ := typeC_locImg_self_le_Q₀ hm h5 hK hz d
  have hcL := card_locImg hΩ hex hL
  have hcK := card_locImg hΩ hex hKz
  have e1 : locImg Ω z L = d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact d.card_le)
  have e2 : locImg Ω z K = d.Q₀ :=
    Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact d.card_le)
  exact locImg_injOn hΩ hP1 hL hKz (e1.trans e2.symm)

theorem typeC_exists_plane_of_ne (hm : 2 ≤ m) (h5 : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ P, IsHyperbolicPlane P ∧ locImg Ω z L = (planeGroup P).map d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases d.fam_cases _ hmem with h | h
  · exact absurd (typeC_eq_of_locImg_le_Q₀ hm h5 hΩ hex hK hz hP1 d hL h) hLK
  · exact h

theorem typeC_exists_member_of_plane (hm : 2 ≤ m) (h5 : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f m Ω z) {P : Submodule _ _}
    (hP : IsHyperbolicPlane P) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = (planeGroup P).map d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (d.mem_fam P hP)
  refine ⟨L, hL, fun hLK => ?_, hLR⟩
  subst hLK
  have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
    intro a ha b hb
    have hb' : b ∈ d.ψ.range := by
      rw [hLR] at hb
      obtain ⟨c, _, rfl⟩ := hb
      exact ⟨c, rfl⟩
    exact d.commutes a (typeC_locImg_self_le_Q₀ hm h5 hK hz d ha) b hb'
  exact not_commutes_self_of_isClassicalMember hz ((commutes_iff_locImg hΩ hP1 hL hL).mpr h1)

theorem typeC_commutes_K_of_ne (hm : 2 ≤ m) (h5 : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeCDict p f m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) : Commutes K L := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨P, hP, hLP⟩ := typeC_exists_plane_of_ne hm h5 hΩ hex hK hz hP1 d hL hLK
  refine commutes_of_commutes_locImg hΩ hP1 hKz hL ?_
  intro a ha b hb
  rw [hLP] at hb
  exact d.commutes a (typeC_locImg_self_le_Q₀ hm h5 hK hz d ha) b
    (by obtain ⟨c, _, rfl⟩ := hb; exact ⟨c, rfl⟩)

end DictAPI

section Conj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem centralizingLayer_conj (hΩ : ConjInvariant Ω) (g z : G) :
    centralizingLayer Ω {g * z * g⁻¹} =
      (centralizingLayer Ω {z}).map (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · refine iSup₂_le fun L' hL' => ?_
    rw [centralizingMembers_conj hΩ g z] at hL'
    obtain ⟨L, hL, rfl⟩ := hL'
    exact Subgroup.map_mono (le_centralizingLayer hL)
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL x hx => ?_
    have hmem : conjSub g L ∈ centralizingMembers Ω {g * z * g⁻¹} := by
      rw [centralizingMembers_conj hΩ g z]
      exact ⟨L, hL, rfl⟩
    exact le_centralizingLayer hmem (conj_mem_conjSub hx)

@[expose] noncomputable def layerConj (hΩ : ConjInvariant Ω) (g z : G) :
    ↥(centralizingLayer Ω {z}) ≃* ↥(centralizingLayer Ω {g * z * g⁻¹}) :=
  ((MulAut.conj g).subgroupMap (centralizingLayer Ω {z})).trans
    (MulEquiv.subgroupCongr (centralizingLayer_conj hΩ g z).symm)

omit [Finite G] in
theorem coe_layerConj (hΩ : ConjInvariant Ω) (g z : G) (y : ↥(centralizingLayer Ω {z})) :
    ((layerConj hΩ g z y : ↥(centralizingLayer Ω {g * z * g⁻¹})) : G) = g * y * g⁻¹ := rfl

@[expose] noncomputable def locConj (hΩ : ConjInvariant Ω) (g z : G) :
    locQuot Ω z ≃* locQuot Ω (g * z * g⁻¹) :=
  QuotientGroup.congr _ _ (layerConj hΩ g z)
    (CFSG.ComponentClassification.OddCore.equiv_invariant _)

omit [Finite G] in
theorem locConj_mk (hΩ : ConjInvariant Ω) (g z : G) (y : ↥(centralizingLayer Ω {z})) :
    locConj hΩ g z (QuotientGroup.mk' _ y) = QuotientGroup.mk' _ (layerConj hΩ g z y) := rfl

omit [Finite G] in
theorem locImg_conj (hΩ : ConjInvariant Ω) (g z : G) (L : Subgroup G) :
    locImg Ω (g * z * g⁻¹) (conjSub g L) =
      (locImg Ω z L).map (locConj hΩ g z).toMonoidHom := by
  ext w
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨y, rfl⟩ := (layerConj hΩ g z).surjective y'
    refine ⟨QuotientGroup.mk' _ y, ⟨y, ?_, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy' ⊢
    have := mem_conjSub_iff.mp hy'
    simpa [coe_layerConj, mul_assoc] using this
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨layerConj hΩ g z y, ?_, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy ⊢
    exact mem_conjSub_iff.mpr (by simpa [coe_layerConj, mul_assoc] using hy)

omit [Finite G] in
theorem locFamily_conj (hΩ : ConjInvariant Ω) (g z : G) :
    locFamily Ω (g * z * g⁻¹) =
      Subgroup.map (locConj hΩ g z).toMonoidHom '' locFamily Ω z := by
  rw [locFamily_eq_image, locFamily_eq_image, centralizingMembers_conj hΩ g z]
  ext K
  constructor
  · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
    exact ⟨locImg Ω z L, ⟨L, hL, rfl⟩, (locImg_conj hΩ g z L).symm⟩
  · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
    exact ⟨conjSub g L, ⟨L, hL, rfl⟩, locImg_conj hΩ g z L⟩

variable {p f : ℕ} [Fact p.Prime]

@[expose] noncomputable def typeCTransport {X X' : Type} [Group X] [Group X']
    {Φ : Set (Subgroup X)} (e : X ≃* X') (D : LieSystemData p f X Φ) :
    LieSystemData p f X' (Subgroup.map e.toMonoidHom '' Φ) where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom i := e.toMonoidHom.comp (D.hom i)
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩

@[expose] def IsShapeC {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (m : ℕ) : Prop :=
  D.card = 2 ∧ ∃ i₀ i₁ : Fin D.card, i₀ ≠ i₁ ∧ D.tag i₀ = .PSL ∧ D.rank i₀ = 2 ∧
    D.tag i₁ = .PSp ∧ D.rank i₁ = m

theorem IsShapeC.transport {X X' : Type} [Group X] [Group X'] {Φ : Set (Subgroup X)}
    {D : LieSystemData p f X Φ} {m : ℕ} (e : X ≃* X') (h : IsShapeC D m) :
    IsShapeC (typeCTransport e D) m := by
  obtain ⟨hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  exact ⟨hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩

omit [Finite G] in
theorem LocalShapeC.conj {m : ℕ} (hΩ : ConjInvariant Ω) {z : G} (h : LocalShapeC p f m Ω z)
    (g : G) : LocalShapeC p f m Ω (g * z * g⁻¹) := by
  obtain ⟨D, hD⟩ := h
  have H : ∀ Φ' : Set (Subgroup (locQuot Ω (g * z * g⁻¹))),
      Φ' = Subgroup.map (locConj hΩ g z).toMonoidHom '' locFamily Ω z →
      ∃ D' : LieSystemData p f (locQuot Ω (g * z * g⁻¹)) Φ', IsShapeC D' m := by
    intro Φ' hΦ'
    subst hΦ'
    exact ⟨typeCTransport (locConj hΩ g z) D, IsShapeC.transport _ hD⟩
  exact H _ (locFamily_conj hΩ g z)

end Conj

end CFSG.ClassicalInvolution.RouteD
