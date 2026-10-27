module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3
import CFSG.Adapters.LieModelSmallOrders
public import CFSG.ClassicalInvolution.Q3.TL4Conn26GAl
public import CFSG.ClassicalInvolution.Q3.TL4E3Norm

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.Blueprint

theorem card_of_lieModel_psl_three_three_one {X : Type} [Group X] (h : LieModel X .PSL 3 3 1) :
    Nat.card X = 5616 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three (h.statedClassicalModel (by decide))

theorem card_of_lieModel_psu_three_three_one {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Blueprint.LieModel.card_psu_three_three h

theorem E3.map_oddCore_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (classicalInvolutionOddCore A).map e.toMonoidHom = classicalInvolutionOddCore B := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hodd⟩ := hN
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨hNn.map _ e.surjective, ?_⟩
    rwa [Subgroup.card_map_of_injective e.injective]
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hodd⟩ := hN
    have hmap : (N.map e.symm.toMonoidHom).map e.toMonoidHom = N := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id N
      ext x
      simp
    rw [← hmap]
    refine Subgroup.map_mono (le_sSup ⟨hNn.map _ e.symm.surjective, ?_⟩)
    rwa [Subgroup.card_map_of_injective e.symm.injective]

noncomputable def E3.oddQuotEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ classicalInvolutionOddCore A ≃* B ⧸ classicalInvolutionOddCore B :=
  QuotientGroup.congr _ _ e (E3.map_oddCore_mulEquiv e)

theorem E3.isSubnormal_eq_bot_or_eq_top {Q : Type*} [Group Q] [IsSimpleGroup Q]
    {A K : Subgroup Q} (h : IsSubnormal A K) (hK : K = ⊤) : A = ⊥ ∨ A = ⊤ :=
  by subst hK; exact h.eq_bot_or_top

theorem E3.nonempty_oddQuot_mulEquiv {G : Type*} [Group G] [Finite G] {H X : Subgroup G}
    (hHX : H ≤ X) (hH : IsSubnormal H ⊤)
    (hs : IsSimpleGroup (↥X ⧸ classicalInvolutionOddCore ↥X)) {w : G} (hw : w ∈ H)
    (hw2 : orderOf w = 2) :
    Nonempty (↥H ⧸ classicalInvolutionOddCore ↥H ≃* ↥X ⧸ classicalInvolutionOddCore ↥X) := by
  classical
  set OX := classicalInvolutionOddCore ↥X with hOX
  set H' : Subgroup ↥X := H.subgroupOf X with hH'def
  have eH : ↥H' ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHX
  have hH' : IsSubnormal H' ⊤ := by
    have := isSubnormal_subgroupOf hH X
    rwa [Subgroup.top_subgroupOf] at this
  have hoddX : Odd (Nat.card OX) := CFSG.ComponentClassification.OddCore.odd_card _
  set w' : ↥X := ⟨w, hHX hw⟩ with hw'def
  have hw'H : w' ∈ H' := hw
  have hw'2 : orderOf w' = 2 := by rw [hw'def, Subgroup.orderOf_mk]; exact hw2
  have hw'O : w' ∉ OX := by
    intro hmem
    have h1 : orderOf (⟨w', hmem⟩ : ↥OX) = 2 := by rw [Subgroup.orderOf_mk]; exact hw'2
    have h2 := orderOf_dvd_natCard (⟨w', hmem⟩ : ↥OX)
    rw [h1] at h2
    exact (Nat.not_even_iff_odd.mpr hoddX) (even_iff_two_dvd.mpr h2)
  let φ : ↥H' →* ↥X ⧸ OX := (QuotientGroup.mk' OX).comp H'.subtype
  have hrange : φ.range = H'.map (QuotientGroup.mk' OX) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hsub : IsSubnormal (H'.map (QuotientGroup.mk' OX)) ⊤ := by
    have := CFSG.ComponentClassification.Components.chain_map (QuotientGroup.mk' OX) hH'
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  have htop : H'.map (QuotientGroup.mk' OX) = ⊤ := by
    rcases E3.isSubnormal_eq_bot_or_eq_top hsub rfl with h | h
    · exfalso
      apply hw'O
      have hm : QuotientGroup.mk' OX w' ∈ H'.map (QuotientGroup.mk' OX) := ⟨w', hw'H, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
      exact hm
    · exact h
  have hφs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, hrange, htop]
  have hker : φ.ker = classicalInvolutionOddCore ↥H' := by
    apply le_antisymm
    · refine le_sSup ⟨MonoidHom.normal_ker φ, ?_⟩
      have hle : φ.ker.map H'.subtype ≤ OX := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : QuotientGroup.mk' OX (x : ↥X) = 1 := hx
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      have hc := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective H'.subtype_injective] at hc
      exact Odd.of_dvd_nat hoddX hc
    · set N := classicalInvolutionOddCore ↥H' with hNdef
      have hNsub : IsSubnormal N ⊤ :=
        IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
      have hNX := isSubnormal_top_map_subtype hH' hNsub
      have hNQ := CFSG.ComponentClassification.Components.chain_map (QuotientGroup.mk' OX) hNX
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hNQ
      have hoddN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card _
      rcases E3.isSubnormal_eq_bot_or_eq_top hNQ rfl with h | h
      · intro x hx
        rw [MonoidHom.mem_ker]
        have hm : QuotientGroup.mk' OX (x : ↥X) ∈
            (N.map H'.subtype).map (QuotientGroup.mk' OX) := ⟨x, ⟨x, hx, rfl⟩, rfl⟩
        rw [h, Subgroup.mem_bot] at hm
        exact hm
      · exfalso
        have h1 : Nat.card ↥((N.map H'.subtype).map (QuotientGroup.mk' OX)) ∣ Nat.card N := by
          have h2 := Subgroup.card_map_dvd (H := N.map H'.subtype) (QuotientGroup.mk' OX)
          rwa [Subgroup.card_map_of_injective H'.subtype_injective] at h2
        rw [h, Subgroup.card_top] at h1
        have hoddQ : Odd (Nat.card (↥X ⧸ OX)) := Odd.of_dvd_nat hoddN h1
        have hne : QuotientGroup.mk' OX w' ≠ 1 := by
          rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
          exact hw'O
        have hsq : QuotientGroup.mk' OX w' ^ 2 = 1 := by
          rw [← map_pow, ← hw'2, pow_orderOf_eq_one, map_one]
        have ho : orderOf (QuotientGroup.mk' OX w') = 2 := orderOf_eq_prime hsq hne
        have hd := orderOf_dvd_natCard (QuotientGroup.mk' OX w')
        rw [ho] at hd
        exact (Nat.not_even_iff_odd.mpr hoddQ) (even_iff_two_dvd.mpr hd)
  exact ⟨(E3.oddQuotEquiv eH).symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs))⟩

section Frame


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.nonempty_secQ_mulEquiv (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) {X : Subgroup Y}
    (hXC : X ≤ Subgroup.centralizer ({u} : Set Y))
    (hXsub : IsSubnormal (X.subgroupOf (Subgroup.centralizer ({u} : Set Y))) ⊤)
    (hKX : tightCore R ≤ X) (hs : IsSimpleGroup (↥X ⧸ classicalInvolutionOddCore ↥X)) :
    Nonempty (SecQ R u ≃* ↥X ⧸ classicalInvolutionOddCore ↥X) := by
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  have eX : ↥(X.subgroupOf C) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXC
  have hs' : IsSimpleGroup (↥(X.subgroupOf C) ⧸ classicalInvolutionOddCore ↥(X.subgroupOf C)) :=
    (E3.oddQuotEquiv eX).isSimpleGroup
  have hK' : tightCore (R.subgroupOf C) ≤ X.subgroupOf C := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxR, hx2⟩
    show (x : Y) ∈ X
    apply hKX
    refine Subgroup.subset_closure ⟨hxR, ?_⟩
    have h := hx2.map C.subtype
    rwa [MonoidHom.map_zpowers] at h
  have hHX : secH R u ≤ X.subgroupOf C := subnormalClosure_le hK' hXsub
  have hH : IsSubnormal (secH R u) ⊤ := isSubnormal_subnormalClosure _
  have hw2 : orderOf (⟨t, htu⟩ : C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hF.large.datum.order
  obtain ⟨e⟩ := E3.nonempty_oddQuot_mulEquiv hHX hH hs' ht hw2
  exact ⟨e.trans (E3.oddQuotEquiv eX)⟩

theorem E3Frame.sepAlpha_of_core (hF : E3Frame n R S t J u) {Rd : Subgroup Y}
    (hcore : tightCore Rd = J) : TightSepAlpha Rd u := by
  obtain ⟨g, hg⟩ := hF.maxAdj.1.2.1
  have hgJ : conjSub g (tightCore R) = J := hg
  have hu : g * t * g⁻¹ = u := by
    have h1 := hF.large.datum.isUniqueInvolution_core.conj g
    rw [hgJ] at h1
    exact h1.eq hF.inv
  have h := hF.alpha.conj g
  rw [hu] at h
  have hc : tightCore (conjSub g R) = tightCore Rd := by rw [← conjSub_tightCore, hgJ, hcore]
  unfold TightSepAlpha at h ⊢
  rwa [hc] at h

end Frame

section Finish


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.inO2_of_l3u3 (hM : ModelL3U3Acts3) (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    {Sb : Sylow 2 ↥(secR R u)} (hex : TightEx (SecQ R u) (secR R u) Sb (E3.secT htu ht))
    (hX : LieModel (SecQ R u) .PSL 3 3 1 ∨ LieModel (SecQ R u) .PSU 3 3 1) :
    TightInO2 (E3.secT htu ht) := by
  obtain ⟨Sq, hd, hc⟩ := hF.exists_secCls htu ht
  have h3 := hM _ _ Sq _ hd (tightClsR_three_iff.mpr hc) hX
  have hcard : Nat.card (SecQ R u) ≤ 6048 := by
    rcases hX with h | h
    · rw [card_of_lieModel_psl_three_three_one h]
      norm_num
    · rw [card_of_lieModel_psu_three_three_one h]
  have hQ : Nat.card (SecQ R u ⧸ Subgroup.center (SecQ R u)) ≤ 6048 :=
    (Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)).trans hcard
  refine inO2_of_exit_ident hd hc hex h3 ⟨fun e => ?_⟩ (fun h => ?_) (fun h => ?_)
  · have h1 := Nat.card_congr e.toEquiv
    have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
    rw [hc] at h1
    omega
  · have := card_of_lieModel_psp_three_two_one h
    omega
  · have := card_of_lieModel_pomegaPlus_four_two_one h
    omega

theorem tightE3Z2Fin_of (hM : ModelL3U3Acts3) : TightE3Z2Fin n := by
  intro Y _ _ R S t J u hF htu ht Sb hex Rd Sd S' R' T W hcore hs h2
  obtain ⟨-, h, -, -, hL⟩ := h2
  set X := omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) with hXdef
  have hα : TightSepAlpha Rd u := hF.sepAlpha_of_core hcore
  have hXC : X ≤ Subgroup.centralizer ({u} : Set Y) := hs.omegaNbrGen_le_centralizer_of_alpha hα
  have hJN : Subgroup.centralizer ({u} : Set Y) ≤
      Subgroup.normalizer ((tightCore Rd : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hs.large).tight _ hs.mem u hs.hz
  have hXn : (X.subgroupOf (Subgroup.centralizer ({u} : Set Y))).Normal := by
    refine ⟨fun x hx c => ?_⟩
    have hcX := conjSub_omegaNbrGen_of_conjSub_eq hs.hyp.conjInvariant
      (conjSub_eq_of_mem_normalizer (hJN c.2))
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hm : (c : Y) * x * (c : Y)⁻¹ ∈ conjSub (c : Y) X := by
      rw [mem_conjSub_iff]
      have he : (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹) * (c : Y) = x := by group
      rw [he]
      exact hx
    rw [hcX] at hm
    simpa using hm
  have hXsub : IsSubnormal (X.subgroupOf (Subgroup.centralizer ({u} : Set Y))) ⊤ :=
    IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤)
  have hKX : tightCore R ≤ X := le_iSup₂_of_le (tightCore R) hs.hJ le_rfl
  have eh : ↥(conjSub h X) ≃* ↥X :=
    (Subgroup.equivMapOfInjective X (MulAut.conj h).toMonoidHom (MulAut.conj h).injective).symm
  have hLX : LieModel (↥X ⧸ classicalInvolutionOddCore ↥X) .PSL 3 3 1 ∨
      LieModel (↥X ⧸ classicalInvolutionOddCore ↥X) .PSU 3 3 1 := by
    rcases hL with hL | hL
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (E3.oddQuotEquiv eh) hL)
    · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (E3.oddQuotEquiv eh) hL)
  have hs' : IsSimpleGroup (↥X ⧸ classicalInvolutionOddCore ↥X) := by
    rcases hLX with h | h <;> exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
  obtain ⟨e⟩ := hF.nonempty_secQ_mulEquiv htu ht hXC hXsub hKX hs'
  refine hF.inO2_of_l3u3 hM htu ht hex ?_
  rcases hLX with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)

theorem tightE3S3Fin_of (hM : ModelL3U3Acts3) : TightE3S3Fin n := by
  intro Y _ _ R S t J u hF htu ht Sb hex hL
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set X := E3.orbGen Ω J (tightCore R) with hXdef
  set C := Subgroup.centralizer ({u} : Set Y) with hCdef
  obtain ⟨g, Sd, S', R', T, W, hgJ, -, hs⟩ := hF.exists_std8
  have hcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) = Ω := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hα : TightSepAlpha (conjSub g R) u := hF.sepAlpha_of_core hcore
  have hNC : omegaNbrGen Ω J ≤ C := by
    have h := hs.omegaNbrGen_le_centralizer_of_alpha hα
    rwa [hfam, hcore] at h
  have hJN : C ≤ Subgroup.normalizer ((J : Subgroup Y) : Set Y) := by
    have h := (TightLargeHypR.typeRFam hs.large).tight _ hs.mem u hs.hz
    rwa [hcore] at h
  have hΩc : ConjInvariant Ω := hF.large.datum.hypOmegaGen.conjInvariant
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  have hnbr : nbrGen (TC.nbrAdj Ω) J = omegaNbrGen Ω J := by
    apply le_antisymm
    · exact iSup₂_le fun M hM => le_iSup₂_of_le M hM.2 le_rfl
    · exact iSup₂_le fun M hM =>
        le_iSup₂_of_le (f := fun M (_ : M ∈ {M | TC.nbrAdj Ω J M}) => M) M ⟨hJΩ, hM⟩ le_rfl
  have hK₀n : tightCore R ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hF.large.datum.hypOmegaGen hF.maxAdj.1.1 hJΩ
      hF.maxAdj.1.2
  have horb : ∀ M ∈ orbOf (TC.nbrAdj Ω) J (tightCore R), M ∈ omegaNbr Ω J := by
    rintro _ ⟨l, hl, rfl⟩
    have hlN : conjSub l J = J :=
      conjSub_eq_of_mem_normalizer (hJN (hNC (hnbr ▸ hl)))
    have h := omegaNbr_conj hΩc hK₀n l
    rwa [hlN] at h
  have hXN : X ≤ omegaNbrGen Ω J := iSup₂_le fun M hM => le_iSup₂_of_le M (horb M hM) le_rfl
  have hXC : X ≤ C := hXN.trans hNC
  have hKX : tightCore R ≤ X := by
    refine le_iSup₂_of_le (f := fun M (_ : M ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => M)
      (tightCore R) ⟨1, Subgroup.one_mem _, ?_⟩ le_rfl
    ext x
    simp [conjSub]
  have hXn : ∀ y ∈ omegaNbrGen Ω J, conjSub y X ≤ X := by
    intro y hy
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    obtain ⟨l, hl, rfl⟩ := hM
    rw [← Subgroup.map_le_iff_le_comap]
    show conjSub y (conjSub l (tightCore R)) ≤ X
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (f := fun M (_ : M ∈ orbOf (TC.nbrAdj Ω) J (tightCore R)) => M) _
      ⟨y * l, Subgroup.mul_mem _ (hnbr ▸ hy) hl, rfl⟩ le_rfl
  have hNn : ((omegaNbrGen Ω J).subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    have hcN := conjSub_omegaNbrGen_of_conjSub_eq hΩc (conjSub_eq_of_mem_normalizer (hJN c.2))
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hm : (c : Y) * x * (c : Y)⁻¹ ∈ conjSub (c : Y) (omegaNbrGen Ω J) := by
      rw [mem_conjSub_iff]
      have he : (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹) * (c : Y) = x := by group
      rw [he]
      exact hx
    rw [hcN] at hm
    simpa using hm
  have hsub : IsSubnormal (X.subgroupOf C) ⊤ := by
    refine IsSubnormal.step (Subgroup.subgroupOf_mono C hXN) ?_
      (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤))
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono C hXN)]
    intro x y hx hy
    rw [Subgroup.mem_subgroupOf] at hx hy ⊢
    have hm : (y : Y) * x * (y : Y)⁻¹ ∈ conjSub (y : Y) X := by
      rw [mem_conjSub_iff]
      have he : (y : Y)⁻¹ * ((y : Y) * x * (y : Y)⁻¹) * (y : Y) = x := by group
      rw [he]
      exact hx
    simpa using hXn y hy hm
  have hs' : IsSimpleGroup (↥X ⧸ classicalInvolutionOddCore ↥X) := by
    rcases hL with h | h <;> exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
  obtain ⟨e⟩ := hF.nonempty_secQ_mulEquiv htu ht hXC hsub hKX hs'
  refine hF.inO2_of_l3u3 hM htu ht hex ?_
  rcases hL with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)

end Finish

end CFSG.ClassicalInvolution.Q3.TL4
