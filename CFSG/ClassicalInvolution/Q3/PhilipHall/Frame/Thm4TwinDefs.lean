module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep
public import CFSG.ClassicalInvolution.Q3.TL4SepMin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

namespace Thm4Twin

structure TwinT4Hyp (r : ℕ) (G : Type) [Group G] (Δ : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Δ
  twoGroup : ∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J)
  quat : ∀ J ∈ Δ, ∀ P : Subgroup G, IsSylow2In P J →
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))
  aEmpty : ∀ J ∈ Δ, AEmpty Δ J
  odd : classicalInvolutionOddCore G = ⊥

theorem thm4RTwinBelow_iff {r n : ℕ} :
    Thm4RTwinBelow r n ↔ ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
      ∀ Δ : Set (Subgroup G), TwinT4Hyp r G Δ →
        ∀ J ∈ Δ, ∀ L ∈ Δ, (¬ ∃ g : G, conjSub g J = L) → Commutes J L :=
  ⟨fun h G _ _ hG Δ hΔ => h G hG Δ hΔ.hyp hΔ.twoGroup hΔ.quat hΔ.aEmpty hΔ.odd,
    fun h G _ _ hG Δ h1 h2 h3 h4 h5 => h G hG Δ ⟨h1, h2, h3, h4, h5⟩⟩

theorem _root_.CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4RTwinBelow.apply {r n : ℕ}
    (h : Thm4RTwinBelow r n) {G : Type} [Group G] [Finite G] (hG : Nat.card G < n)
    {Δ : Set (Subgroup G)} (hΔ : TwinT4Hyp r G Δ) {J L : Subgroup G} (hJ : J ∈ Δ) (hL : L ∈ Δ)
    (hnc : ¬ ∃ g : G, conjSub g J = L) : Commutes J L :=
  thm4RTwinBelow_iff.mp h G hG Δ hΔ J hJ L hL hnc

end Thm4Twin

open Thm4Twin

theorem _root_.CFSG.ClassicalInvolution.Q3.TL4.T4Hyp.toTwin {r : ℕ} {G : Type} [Group G]
    {Δ : Set (Subgroup G)} (h : TL4.T4Hyp r G Δ) : TwinT4Hyp r G Δ :=
  ⟨h.hyp, h.twoGroup, h.quat, h.aEmpty, h.odd⟩

theorem thm4RBelow_of_thm4RTwin {r n : ℕ} (h : Thm4RTwinBelow r n) :
    TL4.Thm4RBelow r n :=
  fun _ _ _ hG _ hΔ _ hJ _ hL hnc => h.apply hG hΔ.toTwin hJ hL hnc

namespace Thm4Twin

section Sub

variable {G : Type} [Group G] [Finite G]

theorem aEmpty_sub {Δ Δ' : Set (Subgroup G)} (hΩ : HypOmegaGen Δ) (hsub : Δ' ⊆ Δ)
    {K : Subgroup G} (hA : AEmpty Δ K) : AEmpty Δ' K := by
  intro J hJ hJn zK zJ hzK hzJ
  have hstar : J ∈ omegaStarNbr Δ K := by
    obtain ⟨hJ', hne, U, hU, hUJ, hUN⟩ := hJ
    exact ⟨hsub hJ', hne, U, USet_mono hsub hU, hUJ, hUN⟩
  have hnbr : J ∉ omegaNbr Δ K := by
    intro h
    apply hJn
    obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
    have hTs := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ (hsub hJ.1) hT hTJ
    exact ⟨hJ.1, hne, T, mem_RSet_of_isSylow2In hJ.1 hTs, hTJ, hTN⟩
  exact hA J hstar hnbr zK zJ hzK hzJ

theorem aEmpty_restrict {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {P : Set (Subgroup G)}
    (hPΩ : P ⊆ Ω) {X K : Subgroup G} (hKX : K ≤ X) (hA : AEmpty Ω K) :
    AEmpty (restrictFamily P X) (K.subgroupOf X) := by
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
    obtain ⟨-, hne, T, hT, hTJ, hTN⟩ := h
    have hTs : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ (hPΩ hJP) hT hTJ
    have hTX : T ≤ X := hTJ.trans hJX
    have hTs' : IsSylow2In (T.subgroupOf X) (J.subgroupOf X) := by
      refine isSylow2In_map_subtype_iff.mp ?_
      rwa [Subgroup.map_subgroupOf_eq_of_le hTX, Subgroup.map_subgroupOf_eq_of_le hJX]
    refine ⟨subgroupOf_mem_restrictFamily hJP hJX, subgroupOf_ne_of_ne hKX hJX hne,
      T.subgroupOf X, mem_RSet_of_isSylow2In (subgroupOf_mem_restrictFamily hJP hJX) hTs',
      fun x hx => hTJ hx, fun x hx => ?_⟩
    exact (mem_normalizer_subgroupOf_iff hKX).mp (hTN (Subgroup.mem_subgroupOf.mp hx))
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

theorem TwinT4Hyp.sub {r : ℕ} {Δ Δ' : Set (Subgroup G)} (h : TwinT4Hyp r G Δ) (hsub : Δ' ⊆ Δ)
    (hinv : ConjInvariant Δ') : TwinT4Hyp r G Δ' where
  hyp := hypOmegaGen_sub h.hyp hsub hinv
  twoGroup J hJ := h.twoGroup J (hsub hJ)
  quat J hJ := h.quat J (hsub hJ)
  aEmpty J hJ := aEmpty_sub h.hyp hsub (h.aEmpty J (hsub hJ))
  odd := h.odd

theorem TwinT4Hyp.restrict {r : ℕ} {Δ : Set (Subgroup G)} (h : TwinT4Hyp r G Δ) (X : Subgroup G)
    (hX : classicalInvolutionOddCore ↥X = ⊥) : TwinT4Hyp r ↥X (restrictFamily Δ X) where
  hyp := hypOmegaGen_restrict h.hyp X
  twoGroup := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    let φ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
    exact (h.twoGroup L hL).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  quat := by
    rintro _ ⟨L, hL, hLX, rfl⟩ P hP
    have hP' : IsSylow2In (P.map X.subtype) L := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at this
    obtain ⟨e⟩ := h.quat L hL _ hP'
    exact ⟨(P.equivMapOfInjective X.subtype X.subtype_injective).trans e⟩
  aEmpty := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    exact aEmpty_restrict h.hyp subset_rfl hLX (h.aEmpty L hL)
  odd := hX

end Sub

section Min

variable {r : ℕ} {G : Type} [Group G]

structure TwinT4Min (r : ℕ) (G : Type) [Group G] [Finite G] (Δ : Set (Subgroup G))
    (J L : Subgroup G) : Prop where
  ih : Thm4RTwinBelow r (Nat.card G)
  hyp : TwinT4Hyp r G Δ
  memJ : J ∈ Δ
  memL : L ∈ Δ
  notConj : ¬ ∃ g : G, conjSub g J = L
  notComm : ¬ Commutes J L

variable [Finite G] {Δ : Set (Subgroup G)} {J L : Subgroup G}

theorem TwinT4Min.two (h : TwinT4Min r G Δ J L) :
    TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L where
  ih := h.ih
  hyp := by
    refine h.hyp.sub ?_ (TL4.conjInvariant_union (TL4.conjInvariant_conjClass J)
      (TL4.conjInvariant_conjClass L))
    rintro K (⟨g, rfl⟩ | ⟨g, rfl⟩)
    · exact h.hyp.hyp.conjInvariant g J h.memJ
    · exact h.hyp.hyp.conjInvariant g L h.memL
  memJ := Or.inl (CoreAssembly.mem_conjClass_self J)
  memL := Or.inr (CoreAssembly.mem_conjClass_self L)
  notConj := h.notConj
  notComm := h.notComm

theorem TwinT4Min.omegaGen_eq_top (h : TwinT4Min r G Δ J L) : omegaGen Δ = ⊤ := by
  by_contra hne
  set M := omegaGen Δ
  have hOM : classicalInvolutionOddCore ↥M = ⊥ :=
    TL4.oddCore_eq_bot_of_normal h.hyp.odd (omegaGen_normal h.hyp.hyp.conjInvariant)
  have hlt : Nat.card M < Nat.card G := lt_of_le_of_ne (Subgroup.card_le_card_group _)
    (fun e => hne ((Subgroup.card_eq_iff_eq_top _).mp e))
  have hJM : J ≤ M := le_omegaGen h.memJ
  have hLM : L ≤ M := le_omegaGen h.memL
  have hc := h.ih.apply hlt (h.hyp.restrict M hOM) (J := J.subgroupOf M) (L := L.subgroupOf M)
    ⟨J, h.memJ, hJM, rfl⟩ ⟨L, h.memL, hLM, rfl⟩ fun hex => by
      obtain ⟨g, -, hg⟩ := TL4.exists_conjSub_of_restrict hJM hLM hex
      exact h.notConj ⟨g, hg⟩
  exact h.notComm (TL4.commutes_of_restrict hJM hLM hc)

theorem thm4RTwinBelow_of_min {n : ℕ} (hmin : ∀ (G : Type) [Group G] [Finite G],
      Nat.card G < n → ∀ J L : Subgroup G,
      TwinT4Min r G (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) J L →
      omegaGen (CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) = ⊤ → False) :
    Thm4RTwinBelow r n := by
  suffices h : ∀ m, m ≤ n → Thm4RTwinBelow r m from h n le_rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmn
    refine thm4RTwinBelow_iff.mpr fun G _ _ hG Δ hΔ J hJ L hL hnc => ?_
    by_contra hcomm
    have hm : TwinT4Min r G Δ J L := ⟨ih _ hG (hG.le.trans hmn), hΔ, hJ, hL, hnc, hcomm⟩
    exact hmin G (lt_of_lt_of_le hG hmn) J L hm.two hm.two.omegaGen_eq_top

end Min

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
