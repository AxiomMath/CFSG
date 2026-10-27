module

public import CFSG.ClassicalInvolution.Q3.TL4E3E4O
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves
public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.TL4E3Trans
public import CFSG.ClassicalInvolution.Q3.TL4E3Fin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

section Sec

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {t u : Y}

omit [Finite Y] in
theorem E3.tightInO2_secT_of_le (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) {X : Subgroup Y}
    (hXC : X ≤ Subgroup.centralizer ({u} : Set Y))
    (hHX : secH R u ≤ X.subgroupOf (Subgroup.centralizer ({u} : Set Y))) (htX : t ∈ X)
    (h : TightInO2 (⟨t, htX⟩ : ↥X)) : TightInO2 (E3.secT htu ht) := by
  obtain ⟨P, hPn, hP2, htP⟩ := h
  let ι : ↥(secH R u) →* ↥X :=
    (Subgroup.subgroupOfEquivOfLe hXC).toMonoidHom.comp (Subgroup.inclusion hHX)
  have hι : Function.Injective ι := fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun x : ↥X => (x : Y)) hab
    exact this
  have hιt : ι ⟨⟨t, htu⟩, ht⟩ = ⟨t, htX⟩ := rfl
  refine ⟨(P.comap ι).map (QuotientGroup.mk' _),
    (hPn.comap ι).map _ (QuotientGroup.mk'_surjective _),
    (hP2.comap_of_injective ι hι).map _, ⟨⟨⟨t, htu⟩, ht⟩, ?_, rfl⟩⟩
  show ι ⟨⟨t, htu⟩, ht⟩ ∈ P
  rw [hιt]
  exact htP

theorem E3.tightEdgeless_secR_of_le (hR2 : IsPGroup 2 R) {X : Subgroup Y} (hRX : R ≤ X)
    (hXC : X ≤ Subgroup.centralizer ({u} : Set Y))
    (hHX : secH R u ≤ X.subgroupOf (Subgroup.centralizer ({u} : Set Y)))
    (hOH : classicalInvolutionOddCore ↥(secH R u) = ⊥)
    (h : TightEdgeless (R.subgroupOf X)) : TightEdgeless (secR R u) := by
  classical
  set C := Subgroup.centralizer ({u} : Set Y) with hCdef
  have hRC : R ≤ C := hRX.trans hXC
  let ι : ↥(secH R u) →* ↥X :=
    (Subgroup.subgroupOfEquivOfLe hXC).toMonoidHom.comp (Subgroup.inclusion hHX)
  have hι : Function.Injective ι := fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun x : ↥X => (x : Y)) hab
    exact this
  let e : SecQ R u ≃* ↥(secH R u) :=
    (QuotientGroup.quotientMulEquivOfEq hOH).trans QuotientGroup.quotientBot
  let φ : SecQ R u →* ↥X := ι.comp e.toMonoidHom
  have hφ : Function.Injective φ := hι.comp e.injective
  have hφmk : ∀ x : ↥(secH R u), φ (QuotientGroup.mk' _ x) = ι x := fun x => rfl
  have hRX2 : IsPGroup 2 ↥(R.subgroupOf X) := hR2.comap_of_injective X.subtype X.subtype_injective
  have hRH2 : IsPGroup 2 ↥((R.subgroupOf C).subgroupOf (secH R u)) :=
    hR2.comap_of_injective (C.subtype.comp (secH R u).subtype)
      (C.subtype_injective.comp (secH R u).subtype_injective)
  have hsec2 : IsPGroup 2 ↥(secR R u) := hRH2.map _
  have hRCH : ∀ r ∈ R, ∀ hr : r ∈ C, (⟨r, hr⟩ : C) ∈ secH R u := by
    intro r hrR hr
    have hRC2 : IsPGroup 2 ↥(R.subgroupOf C) := hR2.comap_of_injective C.subtype C.subtype_injective
    have h1 : (⟨r, hr⟩ : C) ∈ tightCore (R.subgroupOf C) := by
      rw [tightCore_eq_self_of_isPGroup hRC2]
      exact hrR
    exact le_subnormalClosure _ h1
  have himg : (secR R u).map φ = R.subgroupOf X := by
    ext x
    constructor
    · rintro ⟨y, ⟨h', hh', rfl⟩, rfl⟩
      rw [hφmk]
      exact hh'
    · intro hx
      have hxC : (x : Y) ∈ C := hXC x.2
      refine ⟨QuotientGroup.mk' _ ⟨⟨(x : Y), hxC⟩, hRCH _ hx hxC⟩,
        ⟨⟨⟨(x : Y), hxC⟩, hRCH _ hx hxC⟩, hx, rfl⟩, ?_⟩
      rw [hφmk]
      rfl
  have hΩ : ∀ A ∈ CoreAssembly.conjClass (tightCore (secR R u)),
      A.map φ ∈ CoreAssembly.conjClass (tightCore (R.subgroupOf X)) := by
    rintro _ ⟨a, rfl⟩
    refine ⟨φ a, ?_⟩
    rw [E3.map_conjSub, tightCore_eq_self_of_isPGroup hsec2, himg,
      tightCore_eq_self_of_isPGroup hRX2]
  unfold TightEdgeless Disconnected.DEdgeless at h ⊢
  intro K hK J hJ hadj
  exact h _ (hΩ K hK) _ (hΩ J hJ) (E3.dAdj_map φ hφ hΩ hadj)

end Sec

section E4Norm


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem E3.e4_center (hd : TightDatum R S t) (hc : TightCls Y R S t) (hE2 : ¬ TightInO2 t)
    (hE4 : TightE4 Y) :
    ∃ (Q : Type) (_ : Group Q) (f : Y →* Q), Function.Surjective f ∧ IsPGroup 2 ↥f.ker ∧
      f.ker = Subgroup.center Y ∧ Subgroup.center Y ≠ ⊥ ∧
      (LieModel Q .PSp 3 2 1 ∨ LieModel Q .POmegaPlus 4 2 1) ∧
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) := by
  obtain ⟨Q, _, f, hfs, hfk, hf1, hQ⟩ := hE4
  have hs : IsSimpleGroup Q := by
    rcases hQ with h | h <;> exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel h
  have hcard : ¬ (Nat.card Q).Prime := by
    rcases hQ with h | h
    · rw [card_of_lieModel_psp_three_two_one h]
      norm_num
    · rw [card_of_lieModel_pomegaPlus_four_two_one h]
      norm_num
  have hZ := center_eq_bot_of_isSimpleGroup (exists_ne_comm_of_not_prime hcard)
  have hk := ker_eq_center_of_datum hd hc hE2 hZ f hfs hfk
  obtain ⟨e⟩ := nonempty_mulEquiv_of_datum hd hc hE2 hZ f hfs hfk
  refine ⟨Q, inferInstance, f, hfs, hfk, hk, fun h0 => hf1 (hk.trans h0), hQ, ?_⟩
  rcases hQ with h | h
  · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  · exact Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)

end E4Norm

@[expose] def TightE4Perfect : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (t : X),
    TightDatum R S t → TightCls X R S t → ¬ TightInO2 t → TightE4 X → commutator X = ⊤

section Cit3


@[expose] def TightE3E4Good (n : ℕ) : Prop :=
  TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR 3 n Y R S t → TightOddCent t →
      Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)) →
      TC.SepHyp (CoreAssembly.conjClass (tightCore R)) →
      ∀ J : Subgroup Y, MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J →
      ∀ u : Y, IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
        (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u),
        TightE4 (SecQ R u) → ¬ TightInO2 (E3.secT htu ht) →
          ∀ htX : t ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R),
            ¬ GoodThreeElement
              (R.subgroupOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)))
              (⟨t, htX⟩ : ↥(E3.orbGen (CoreAssembly.conjClass (tightCore R)) J (tightCore R)))

end Cit3

section Main


variable {n : ℕ}

theorem tightE3E4Sec_of (hPerf : TightE4Perfect) (hGood : TightE3E4Good n)
    (hEdge : SecIdE4Edge) : TightE3E4Sec n := by
  intro hP Y _ _ R S t hL hO hcn hsp J hJ u hu htu ht hE4 hE2
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) J (tightCore R) with hπdef
  set C := Subgroup.centralizer ({u} : Set Y) with hCdef
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have h2 : ∀ J' ∈ Ω, IsPGroup 2 J' := hd.isPGroup_member hO
  have htr : ∀ J' ∈ Ω, ∃ g : Y, conjSub g (tightCore R) = J' := fun J' hJ' => hJ'
  have hgen : (⨆ J' ∈ Ω, J') = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  have hstd : OrbitStd Ω := ⟨hΩ, h2, hF⟩
  have hJΩ : J ∈ Ω := hJ.1.2.1
  have hmax : π ∈ maxOrbs (TC.nbrAdj Ω) J := orbOf_mem_maxOrbs hF hJ.1 hJ.2
  have hK₀π : tightCore R ∈ π := ⟨1, Subgroup.one_mem _, by ext x; simp [conjSub]⟩
  have hR2 : IsPGroup 2 R := hd.isPGroup_of_oddCent hO
  have hK₀R : tightCore R = R := tightCore_eq_self_of_isPGroup hR2
  have hRX : R ≤ piGen π := hK₀R ▸ le_piGen hK₀π
  have htR : t ∈ R := Subgroup.map_subtype_le _ hd.mem
  have htX : t ∈ piGen π := hRX htR
  have hXC : piGen π ≤ C := hstd.piGen_le_centralizer hmax hu
  have hJN : C ≤ Subgroup.normalizer ((J : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hL).tight J hJΩ u hu
  have hXn : ∀ c ∈ C, conjSub c (piGen π) = piGen π := by
    intro c hc
    have hcJ : conjSub c J = J := conjSub_eq_of_mem_normalizer (hJN hc)
    have h1 := isMaxOrb_conj hF hmax c
    rw [hcJ] at h1
    have h2' := maxOrb_unique hF hJΩ h1 hmax
    rw [← piGen_conj, h2']
  have hX'n : ((piGen π).subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hm : (c : Y) * x * (c : Y)⁻¹ ∈ conjSub (c : Y) (piGen π) := by
      rw [mem_conjSub_iff]
      have he : (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹) * (c : Y) = x := by group
      rw [he]
      exact hx
    rw [hXn c c.2] at hm
    simpa using hm
  have hK' : tightCore (R.subgroupOf C) ≤ (piGen π).subgroupOf C := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxR, -⟩
    exact hRX hxR
  have hHX : secH R u ≤ (piGen π).subgroupOf C :=
    subnormalClosure_le hK' (IsSubnormal.step le_top Subgroup.normal_subgroupOf
      (IsSubnormal.refl ⊤))
  obtain ⟨g₀, hg₀'⟩ := hJΩ
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have hu₀ : g₀ * t * g₀⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g₀
    rw [hg₀] at h1
    exact h1.eq hu
  have hOu : classicalInvolutionOddCore ↥C = ⊥ := by
    have h1 := card_oddCent_conj (t := t) g₀
    have h3 : Nat.card (oddCoreImg (Subgroup.centralizer ({t} : Set Y))) = 1 := by
      unfold TightOddCent at hO
      rw [hO, Subgroup.card_bot]
    rw [h3, hu₀] at h1
    have h4 : oddCoreImg C = ⊥ := Subgroup.card_eq_one.mp h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h4
  have hOX : classicalInvolutionOddCore ↥(piGen π) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hX'n hXC hOu
  have hOH : classicalInvolutionOddCore ↥(secH R u) = ⊥ := by
    have h1 := Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_subnormalClosure
      (tightCore (R.subgroupOf C)))
    have h2' : Balance.oddCoreIn (⊤ : Subgroup ↥C) = ⊥ := by
      have h3 := E3.map_oddCore_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup ↥C) ≃* ↥C)
      rw [hOu] at h3
      have h4 : classicalInvolutionOddCore ↥(⊤ : Subgroup ↥C) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).mp h3
      show (classicalInvolutionOddCore ↥(⊤ : Subgroup ↥C)).map _ = ⊥
      rw [h4, Subgroup.map_bot]
    rw [h2', le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have hXlt : Nat.card ↥(piGen π) < n := by
    have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu.sq) hu.ne_one
    have hE2u : ¬ TightInO2 u := hu₀ ▸ not_tightInO2_conj hL.notInO2 g₀
    have h1 : Nat.card ↥C < Nat.card Y := card_centralizer_lt hu2 hE2u
    have h3 : Nat.card ↥(piGen π) ≤ Nat.card ↥C := Subgroup.card_le_of_le hXC
    rw [← hL.card]
    omega
  have hSX : (S : Subgroup R).map R.subtype ≤ piGen π := (Subgroup.map_subtype_le _).trans hRX
  obtain ⟨SX, hdX, ⟨eX⟩⟩ := hd.restrict hSX
  have hRX2 : IsPGroup 2 ↥(R.subgroupOf (piGen π)) :=
    hR2.comap_of_injective (piGen π).subtype (piGen π).subtype_injective
  have hself : TightSelfGen (R.subgroupOf (piGen π)) := by
    unfold TightSelfGen
    rw [tightCore_eq_self_of_isPGroup hRX2]
    apply Subgroup.map_injective (piGen π).subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    apply le_antisymm
    · exact iSup_le fun g => Subgroup.map_subtype_le _
    · refine piGen_le fun M hM => ?_
      obtain ⟨a, ha, hMa⟩ := transitive_of_maxOrb hF hmax (tightCore R) hK₀π M hM
      refine le_iSup_of_le ⟨a, ha⟩ ?_
      rw [E3.map_conjSub, Subgroup.map_subgroupOf_eq_of_le hRX, ← hMa, hK₀R]
      rfl
  have hcX : TightCls ↥(piGen π) (R.subgroupOf (piGen π)) SX (⟨t, hSX hd.mem⟩ : ↥(piGen π)) :=
    ⟨⟨eX.trans hL.cls.1.some⟩, hself, hOX⟩
  have hE2X : ¬ TightInO2 (⟨t, hSX hd.mem⟩ : ↥(piGen π)) := fun h =>
    hE2 (E3.tightInO2_secT_of_le htu ht hXC hHX _ h)
  rcases hL.tbelow _ hXlt _ _ _ hdX (tightClsR_three_iff.mpr hcX) with hex | hgood
  · rcases hex with hE2' | ⟨hedge, -⟩ | ⟨hedge, -⟩ | hE4X
    · exact absurd hE2' hE2X
    · obtain ⟨Sq, hdq, hcq⟩ := E3.exists_secCls hd hL.cls.1 hJ.1.2 hu htu ht
      obtain ⟨-, -, -, -, -, -, hcen, -, hlie⟩ := E3.e4_center hdq hcq hE2 hE4
      exact absurd (E3.tightEdgeless_secR_of_le hR2 hRX hXC hHX hOH hedge)
        (hEdge _ _ Sq _ hdq hcq hE2 hcen hlie)
    · obtain ⟨Sq, hdq, hcq⟩ := E3.exists_secCls hd hL.cls.1 hJ.1.2 hu htu ht
      obtain ⟨-, -, -, -, -, -, hcen, -, hlie⟩ := E3.e4_center hdq hcq hE2 hE4
      exact absurd (E3.tightEdgeless_secR_of_le hR2 hRX hXC hHX hOH hedge)
        (hEdge _ _ Sq _ hdq hcq hE2 hcen hlie)
    · have hperf := hPerf _ _ _ _ hdX hcX hE2X hE4X
      obtain ⟨Q, _, f, hfs, hfk, hk, -, hQ, -⟩ := E3.e4_center hdX hcX hE2X hE4X
      refine ⟨?_, Q, inferInstance, f, hfs, hfk, hk.le, hQ⟩
      have h := congrArg (Subgroup.map (piGen π).subtype) hperf
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h
      exact h
  · exact absurd hgood (hGood hP Y R S t hL hO hcn hsp J hJ u hu htu ht hE4 hE2 htX)

end Main

end CFSG.ClassicalInvolution.Q3.TL4
