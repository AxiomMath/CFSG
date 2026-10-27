module

public import CFSG.ClassicalInvolution.Q3.TL3T19
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Pair

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

@[expose] def ThmDAbsAt (r : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ Ω : Set (Subgroup G), HypOmegaGen Ω →
    (∀ J ∈ Ω, IsPGroup 2 J) → (∀ J ∈ Ω, Nat.card J = 2 ^ r) → (∀ J ∈ Ω, AEmpty Ω J) →
    pSpan Ω = ⊤ → (∀ L ∈ Ω, ∀ L' ∈ Ω, ∃ g : G, conjSub g L = L') →
    classicalInvolutionOddCore G = ⊥ →
    (∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q) →
    (∀ L ∈ Ω, ∀ L' ∈ Ω, L = L') ∨
      (∃ W : Subgroup G, WSet Ω = {W}) ∨ (∃ E : Subgroup G, E8Struct ⊤ E) ∨
      Nonempty (AEIdentOn Ω 7 AE.e64Sets AE.e64Sub) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent Ω n)) ∨
      Nonempty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub)

@[expose] def ThmDAbs (r : ℕ) : Prop := ∀ (G : Type) [Group G] [Finite G], ThmDAbsAt r G

@[expose] def ThmDAbsBelow (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n → ThmDAbsAt r G

variable {G : Type} [Group G]

theorem USet_mono {P Ω : Set (Subgroup G)} (h : P ⊆ Ω) : USet P ⊆ USet Ω := by
  rintro U ⟨R, ⟨J, hJ, S, rfl⟩, hUR, hcyc, hidx⟩
  exact ⟨_, ⟨J, h hJ, S, rfl⟩, hUR, hcyc, hidx⟩

variable [Finite G]

theorem aEmpty_restrictFamily {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) {X K : Subgroup G}
    (hKX : K ≤ X) (hA : AEmpty Ω K) : AEmpty (restrictFamily P X) (K.subgroupOf X) := by
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  set J : Subgroup G := J'.map X.subtype with hJdef
  have hJ'eq : J.subgroupOf X = J' := subgroupOf_map_subtype' J'
  have hJX : J ≤ X := Subgroup.map_subtype_le J'
  have hJP : J ∈ P := mem_restrictFamily_iff.mp hJ'star.1
  have hstarP : J ∈ omegaStarNbr P K := omegaStarNbr_of_restrict hKX hJX (by rwa [hJ'eq])
  have hstar : J ∈ omegaStarNbr Ω K := by
    obtain ⟨-, hne, U, hU, hUJ, hUN⟩ := hstarP
    exact ⟨hPΩ hJP, hne, U, USet_mono hPΩ hU, hUJ, hUN⟩
  have hnbr : J ∉ omegaNbr Ω K := by
    intro h
    apply hJ'nbr
    rw [← hJ'eq]
    obtain ⟨-, hne, hJN⟩ := (mem_omegaNbr_iff hΩ h2).mp h
    have hJ'2 : IsPGroup 2 ↥(J.subgroupOf X) := (h2 J (hPΩ hJP)).comap_subtype
    refine ⟨subgroupOf_mem_restrictFamily hJP hJX, subgroupOf_ne_of_ne hKX hJX hne,
      J.subgroupOf X, mem_RSet_of_isPGroup (subgroupOf_mem_restrictFamily hJP hJX) hJ'2, le_rfl,
      fun x hx => ?_⟩
    exact (mem_normalizer_subgroupOf_iff hKX).mp (hJN (Subgroup.mem_subgroupOf.mp hx))
  have hzK : IsUniqueInvolution K (zK' : G) := isUniqueInvolution_of_subgroupOf hzK' hKX
  have hzJ : IsUniqueInvolution J (zJ' : G) :=
    isUniqueInvolution_of_subgroupOf (by rwa [hJ'eq]) hJX
  obtain ⟨g, hg, hgK⟩ := hA J hstar hnbr _ _ hzK hzJ
  set Z' : Subgroup X := Subgroup.closure ({zK', zJ'} : Set X) with hZ'
  have hZ : Z'.map X.subtype = Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :=
    map_closure_pair_subtype zK' zJ'
  have hZX : Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) ≤ X := by
    rw [← hZ]; exact Subgroup.map_subtype_le _
  have hgX : g ∈ X := by
    have : pairNormalizers K J (zK' : G) (zJ' : G) ≤ X := by
      unfold pairNormalizers
      exact sup_le (inf_le_left.trans hKX) (inf_le_left.trans hJX)
    exact this hg
  have hN : ∀ {A : Subgroup G}, A ≤ X →
      (A ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
        Subgroup G) : Set G)).subgroupOf X ≤
        A.subgroupOf X ⊓ Subgroup.normalizer ((Z' : Subgroup X) : Set X) := by
    intro A hAX x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hx.1, ?_⟩
    have := (mem_normalizer_subgroupOf_iff hZX).mp hx.2
    rwa [← hZ, subgroupOf_map_subtype'] at this
  have hAX : K ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ X := inf_le_left.trans hKX
  have hBX : J ⊓ Subgroup.normalizer ((Subgroup.closure ({(zK' : G), (zJ' : G)} : Set G) :
      Subgroup G) : Set G) ≤ X := inf_le_left.trans hJX
  have hmem : (⟨g, hgX⟩ : X) ∈ (pairNormalizers K J (zK' : G) (zJ' : G)).subgroupOf X :=
    Subgroup.mem_subgroupOf.mpr hg
  have hmem' : (⟨g, hgX⟩ : X) ∈ pairNormalizers (K.subgroupOf X) J' zK' zJ' := by
    have h1 := hmem
    unfold pairNormalizers at h1
    rw [Subgroup.subgroupOf_sup hAX hBX] at h1
    have h2' := hN (A := K) hKX
    have h3 := hN (A := J) hJX
    rw [hJ'eq] at h3
    exact sup_le_sup h2' h3 h1
  refine ⟨⟨g, hgX⟩, hmem', ?_⟩
  rw [conjSub_subgroupOf X ⟨g, hgX⟩ K]
  show (conjSub g K).subgroupOf X = J'
  rw [hgK]
  exact hJ'eq

section Transport

variable {P : Set (Subgroup G)}

noncomputable abbrev spanEquiv (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤) :
    ↥(pSpan P) ≃* ↥(pSpan (restrictFamily P (pSpan P))) :=
  Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgen.symm)

omit [Finite G] in
theorem spanEquiv_symm_coe (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤)
    (y : ↥(pSpan (restrictFamily P (pSpan P)))) : (spanEquiv hgen).symm y = (y : ↥(pSpan P)) :=
  rfl

omit [Finite G] in
theorem map_spanEquiv (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤) (L : Subgroup G) :
    (L.subgroupOf (pSpan P)).map (spanEquiv hgen).toMonoidHom =
      (L.subgroupOf (pSpan P)).subgroupOf (pSpan (restrictFamily P (pSpan P))) := by
  ext y
  simp only [Subgroup.mem_map_equiv, spanEquiv_symm_coe, Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem ker_comp_spanEquiv_le {H : Type} [Group H] (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤)
    {φ : ↥(pSpan (restrictFamily P (pSpan P))) →* H}
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (restrictFamily P (pSpan P)))) :
    (φ.comp (spanEquiv hgen).toMonoidHom).ker ≤ Subgroup.center ↥(pSpan P) := by
  intro x hx
  have h1 : spanEquiv hgen x ∈ Subgroup.center _ := hker hx
  rw [Subgroup.mem_center_iff] at h1 ⊢
  intro y
  have h2 := h1 (spanEquiv hgen y)
  rw [← map_mul, ← map_mul] at h2
  exact (spanEquiv hgen).injective h2

omit [Finite G] in
theorem range_comp_spanEquiv {H : Type} [Group H] (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤)
    (φ : ↥(pSpan (restrictFamily P (pSpan P))) →* H) :
    (φ.comp (spanEquiv hgen).toMonoidHom).range = φ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (spanEquiv hgen).surjective,
    ← MonoidHom.range_eq_map]

noncomputable def AEIdentOn.ofRestrict {n : ℕ} {𝒜 : Set (Finset (Fin n))}
    {H : Subgroup (AE.AEQ n)} (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤)
    (hLX : ∀ L ∈ P, L ≤ pSpan P) (I : AEIdentOn (restrictFamily P (pSpan P)) n 𝒜 H) :
    AEIdentOn P n 𝒜 H where
  φ := I.φ.comp (spanEquiv hgen).toMonoidHom
  range_eq := by rw [range_comp_spanEquiv, I.range_eq]
  ker_le := ker_comp_spanEquiv_le hgen I.ker_le
  label := by
    intro L hL
    obtain ⟨α, hα, h, b, hlab⟩ := I.label _ ⟨L, hL, hLX L hL, rfl⟩
    refine ⟨α, hα, h, b, ?_⟩
    rw [← Subgroup.map_map, map_spanEquiv, hlab]
  label_surj := by
    intro α hα h b
    obtain ⟨_, ⟨L, hL, hLX', rfl⟩, hlab⟩ := I.label_surj α hα h b
    refine ⟨L, hL, ?_⟩
    rw [← Subgroup.map_map, map_spanEquiv, hlab]

noncomputable def AEIdent.ofRestrict {n : ℕ} (hgen : pSpan (restrictFamily P (pSpan P)) = ⊤)
    (hLX : ∀ L ∈ P, L ≤ pSpan P) (I : AEIdent (restrictFamily P (pSpan P)) n) :
    AEIdent P n where
  φ := I.φ.comp (spanEquiv hgen).toMonoidHom
  range_eq := by rw [range_comp_spanEquiv, I.range_eq]
  ker_le := ker_comp_spanEquiv_le hgen I.ker_le
  label := by
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := I.label _ ⟨L, hL, hLX L hL, rfl⟩
    refine ⟨α, h, b, ?_⟩
    rw [← Subgroup.map_map, map_spanEquiv, hlab]
  label_surj := by
    intro α h b
    obtain ⟨_, ⟨L, hL, hLX', rfl⟩, hlab⟩ := I.label_surj α h b
    refine ⟨L, hL, ?_⟩
    rw [← Subgroup.map_map, map_spanEquiv, hlab]

end Transport

omit [Finite G] in
theorem E8Struct.map {X : Subgroup G} {E' : Subgroup X} (hE : E8Struct (⊤ : Subgroup X) E') :
    E8Struct X (E'.map X.subtype) where
  le := Subgroup.map_subtype_le _
  normal := by
    rintro x hx _ ⟨e, he, rfl⟩
    exact ⟨_, hE.normal ⟨x, hx⟩ (Subgroup.mem_top _) e he, rfl⟩
  card := by rw [Subgroup.card_map_of_injective X.subtype_injective, hE.card]
  sq := by
    rintro _ ⟨e, he, rfl⟩
    exact congrArg Subtype.val (hE.sq e he)
  cent := by
    intro x hx hc
    refine ⟨⟨x, hx⟩, hE.cent _ (Subgroup.mem_top _) fun e he => Subtype.ext ?_, rfl⟩
    exact hc (e : G) ⟨e, he, rfl⟩
  core := by
    intro Q hQX hQn hQ2 q hq
    have hle := hE.core (Q.subgroupOf X) le_top
      (fun x _ y hy => Subgroup.mem_subgroupOf.mpr (hQn x x.2 y (Subgroup.mem_subgroupOf.mp hy)))
      hQ2.comap_subtype
    exact ⟨⟨q, hQX hq⟩, hle (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  index := by
    have h1 := Subgroup.relIndex_map_map_of_injective E' (⊤ : Subgroup X) X.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [h1, hE.index]

theorem thmDGen_at {r : ℕ} {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) (hA : ∀ J ∈ Ω, AEmpty Ω J)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hD : ThmDAbsAt r ↥(pSpan P))
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hodd : classicalInvolutionOddCore ↥(pSpan P) = ⊥)
    (hE2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q) :
    (∀ L ∈ P, ∀ L' ∈ P, L = L') ∨
      (∃ W : Subgroup G, WIn P (pSpan P) = {W}) ∨ (∃ E : Subgroup G, E8Struct (pSpan P) E) ∨
      Nonempty (AEIdentOn P 7 AE.e64Sets AE.e64Sub) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (AEIdent P n)) ∨
      Nonempty (AEIdentOn P 8 AE.e29Sets AE.e29Sub) := by
  have hLX : ∀ L ∈ P, L ≤ pSpan P := fun L hL => le_pSpan hL
  have hΩ' : HypOmegaGen (restrictFamily P (pSpan P)) := by
    refine TL4.hypOmegaGen_restrict_of (pSpan P) hLX (fun n hn L hL => hinv L hL n hn)
      (fun K hK => hΩ.omega1 K (hPΩ hK)) (fun K hK => ?_)
      (fun K hK J hJ => hΩ.omega3 K (hPΩ hK) J (hPΩ hJ))
      (fun K hK J hJ hne => hΩ.omega4 K (hPΩ hK) J (hPΩ hJ) hne)
      (fun K hK J hJ hne => hΩ.omega5 K (hPΩ hK) J (hPΩ hJ) hne)
    refine le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx => hx.1) fun x hx => ?_
    exact Subgroup.subset_closure ⟨hx, (h2 K (hPΩ hK)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  have h2' : ∀ J ∈ restrictFamily P (pSpan P), IsPGroup 2 J := by
    rintro _ ⟨J, hJ, -, rfl⟩
    exact (h2 J (hPΩ hJ)).comap_subtype
  have h8' : ∀ J ∈ restrictFamily P (pSpan P), Nat.card J = 2 ^ r := by
    rintro _ ⟨J, hJ, hJX, rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJX).toEquiv]
    exact h8 J (hPΩ hJ)
  have hA' : ∀ J ∈ restrictFamily P (pSpan P), AEmpty (restrictFamily P (pSpan P)) J := by
    rintro _ ⟨J, hJ, hJX, rfl⟩
    exact aEmpty_restrictFamily hΩ h2 hPΩ hJX (hA J (hPΩ hJ))
  have hmap : (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype = pSpan P := by
    refine le_antisymm (Subgroup.map_subtype_le _) (pSpan_le fun L hL => ?_)
    have h1 : L.subgroupOf (pSpan P) ≤ pSpan (restrictFamily P (pSpan P)) :=
      le_pSpan ⟨L, hL, hLX L hL, rfl⟩
    calc L = (L.subgroupOf (pSpan P)).map (pSpan P).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hLX L hL)).symm
      _ ≤ (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype := Subgroup.map_mono h1
  have hgen : pSpan (restrictFamily P (pSpan P)) = ⊤ := by
    apply Subgroup.map_injective (pSpan P).subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have htrans' : ∀ L ∈ restrictFamily P (pSpan P), ∀ L' ∈ restrictFamily P (pSpan P),
      ∃ g : ↥(pSpan P), conjSub g L = L' := by
    rintro _ ⟨L, hL, -, rfl⟩ _ ⟨L', hL', -, rfl⟩
    obtain ⟨x, hx, hxL⟩ := htrans L hL L' hL'
    exact ⟨⟨x, hx⟩, by rw [conjSub_subgroupOf, hxL]⟩
  have hE2' : ∀ L ∈ restrictFamily P (pSpan P), ∀ u : ↥(pSpan P), IsUniqueInvolution L u →
      ∃ Q : Subgroup ↥(pSpan P), Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    rintro _ ⟨L, hL, hLX', rfl⟩ u hu
    obtain ⟨Q, -, hQn, hQ2, huQ⟩ :=
      hE2 L hL (u : G) (isUniqueInvolution_of_subgroupOf hu hLX')
    refine ⟨Q.subgroupOf (pSpan P), ⟨fun q hq g => ?_⟩, hQ2.comap_subtype,
      Subgroup.mem_subgroupOf.mpr huQ⟩
    exact Subgroup.mem_subgroupOf.mpr (hQn g g.2 q (Subgroup.mem_subgroupOf.mp hq))
  rcases hD (restrictFamily P (pSpan P)) hΩ' h2' h8' hA' hgen htrans' hodd hE2' with
    hsing | ⟨W', hW'⟩ | ⟨E', hE'⟩ | hI | ⟨n, hn, hI⟩ | hI
  · refine Or.inl fun L hL L' hL' => ?_
    have h1 := hsing _ ⟨L, hL, hLX L hL, rfl⟩ _ ⟨L', hL', hLX L' hL', rfl⟩
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr (hLX L hL), inf_eq_left.mpr (hLX L' hL')] at h2
  · exact Or.inr (Or.inl ⟨W'.map (pSpan P).subtype, by rw [WIn, hW', Set.image_singleton]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨E'.map (pSpan P).subtype, hE'.map⟩))
  · obtain ⟨I⟩ := hI
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨AEIdentOn.ofRestrict hgen hLX I⟩)))
  · obtain ⟨I⟩ := hI
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨AEIdent.ofRestrict hgen hLX I⟩⟩))))
  · obtain ⟨I⟩ := hI
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨AEIdentOn.ofRestrict hgen hLX I⟩))))

theorem thmDGen_of_abs {r : ℕ} (hD : ThmDAbs r) : ThmDGen r := by
  intro G _ _ Ω hΩ h2 h8 hA P hPΩ htrans hinv hodd hE2
  exact thmDGen_at hΩ h2 h8 hA hPΩ (hD _) htrans hinv hodd hE2

theorem thmDGenBelow_of_absBelow {r n : ℕ} (hD : ThmDAbsBelow r n) : ThmDGenBelow r n := by
  intro G _ _ Ω hΩ h2 h8 hA P hPΩ hcard htrans hinv hodd hE2
  exact thmDGen_at hΩ h2 h8 hA hPΩ (hD _ hcard) htrans hinv hodd hE2

theorem tightThmD3_of_abs (hD : ThmDAbs 3) : TightThmD3 :=
  tightThmD3_of_gen (thmDGen_of_abs hD)

end CFSG.ClassicalInvolution.Q3.TC.Thin
