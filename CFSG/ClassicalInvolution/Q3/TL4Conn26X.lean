module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TightFamily
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Sec
public import CFSG.ClassicalInvolution.Q3.TL4ConnStd
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

section Restrict

theorem TypeRFam.restrict (h : TypeRFam r Ω) (X : Subgroup G) :
    TypeRFam r (restrictFamily Ω X) where
  hyp := PhilipHall.Frame.hypOmegaGen_restrict h.hyp X
  cls := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨L, hL, hLX, rfl⟩
      obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
      have hz' := isUniqueInvolution_subgroupOf hz hLX
      refine ⟨_, hz'.mem, orderOf_eq_prime (by rw [pow_two]; exact hz'.sq) hz'.ne_one, ?_⟩
      have hle : L.subgroupOf X ≤
          Subgroup.centralizer ({(⟨z, hLX hz.mem⟩ : ↥X)} : Set ↥X) := by
        intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (h.le_centralizer hL hz (Subgroup.mem_subgroupOf.mp hy))
      have hn : ((L.subgroupOf X).subgroupOf
          (Subgroup.centralizer ({(⟨z, hLX hz.mem⟩ : ↥X)} : Set ↥X))).Normal := by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
        intro y hy
        exact (mem_normalizer_subgroupOf_iff hLX).mp (h.tight L hL z hz
          (Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))))
      exact IsSubnormal.step hle hn (IsSubnormal.refl _)
    · rintro _ ⟨L, hL, hLX, rfl⟩ u a b hu hu2 huu ha hb hau hbu
      have hc := h.cls.commOdd L hL u a b (Subgroup.mem_subgroupOf.mp hu)
        (isPGroup_zpowers_coe_iff.mpr hu2) (fun h1 => huu (Subtype.ext h1))
        (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb)
        (congrArg Subtype.val hau) (congrArg Subtype.val hbu)
      rw [oddCoreOf_subgroupOf hLX]
      exact Subgroup.mem_subgroupOf.mpr hc
  twoGroup := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    let φ : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
    exact (h.twoGroup L hL).of_equiv (QuotientGroup.congr _ _ φ
      (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).symm
  quat := by
    rintro _ ⟨L, hL, hLX, rfl⟩ P' hP'
    have hP : IsSylow2In (P'.map X.subtype) L := by
      have := isSylow2In_map_subtype_iff.mpr hP'
      rwa [Subgroup.map_subgroupOf_eq_of_le hLX] at this
    obtain ⟨e⟩ := h.quat L hL _ hP
    exact ⟨(P'.equivMapOfInjective X.subtype X.subtype_injective).trans e⟩
  tight := by
    rintro _ ⟨L, hL, hLX, rfl⟩ w hw y hy
    have hw' : IsUniqueInvolution L (w : G) := isUniqueInvolution_of_subgroupOf hw hLX
    have hyw := Subgroup.mem_centralizer_singleton_iff.mp hy
    exact (mem_normalizer_subgroupOf_iff hLX).mp (h.tight L hL _ hw'
      (Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hyw)))
  noTwins := by
    rintro _ ⟨L, hL, hLX, rfl⟩ _ ⟨⟨M, hM, hMX, rfl⟩, w, hwL, hwM⟩
    have hMt : M ∈ twinSet Ω L := ⟨hM, (w : G), isUniqueInvolution_of_subgroupOf hwL hLX,
      isUniqueInvolution_of_subgroupOf hwM hMX⟩
    rw [h.noTwins L hL M hMt]

end Restrict

section Section

variable (Ω) (K : Subgroup G)

abbrev XQuot : Type := ↥(omegaNbrGen Ω K) ⧸ classicalInvolutionOddCore ↥(omegaNbrGen Ω K)

abbrev xFam : Set (Subgroup (XQuot Ω K)) :=
  oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))

variable {Ω K}

theorem TypeRFam.xFam (h : TypeRFam r Ω) : TypeRFam r (xFam Ω K) :=
  (h.restrict _).quotFamily (CFSG.ComponentClassification.OddCore.odd_card _)

theorem xQuot_oddCore_eq_bot : classicalInvolutionOddCore (XQuot Ω K) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree _

omit [Finite G] in
theorem le_omegaNbrGen {M : Subgroup G} (hM : M ∈ omegaNbr Ω K) : M ≤ omegaNbrGen Ω K :=
  le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) M hM

omit [Finite G] in
theorem omegaGen_restrictFamily_omegaNbrGen :
    omegaGen (restrictFamily Ω (omegaNbrGen Ω K)) = ⊤ := by
  apply Subgroup.map_injective (omegaNbrGen Ω K).subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm (Subgroup.map_subtype_le _) ?_
  refine iSup₂_le fun M hM => ?_
  have hMX := le_omegaNbrGen hM
  have hmem : M.subgroupOf (omegaNbrGen Ω K) ≤ omegaGen (restrictFamily Ω (omegaNbrGen Ω K)) :=
    le_omegaGen ⟨M, hM.1, hMX, rfl⟩
  calc M = (M.subgroupOf (omegaNbrGen Ω K)).map (omegaNbrGen Ω K).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hMX).symm
    _ ≤ _ := Subgroup.map_mono hmem

omit [Finite G] in
theorem omegaGen_xFam : omegaGen (xFam Ω K) = ⊤ := by
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(omegaNbrGen Ω K))),
    ← omegaGen_restrictFamily_omegaNbrGen, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_omegaGen ⟨L, hL, rfl⟩

theorem aEmpty_xFam (h : TypeRFam r Ω) : ∀ Lb ∈ xFam Ω K, AEmpty (xFam Ω K) Lb :=
  fun _ hLb => aEmpty_of_noTwins h.xFam.hyp hLb (h.xFam.noTwins _ hLb)

omit [Finite G] in
theorem conjSub_omegaNbrGen_of_conjSub_eq (hcl : ConjInvariant Ω) {b : G}
    (hb : conjSub b K = K) : conjSub b (omegaNbrGen Ω K) = omegaNbrGen Ω K := by
  have key : ∀ c : G, conjSub c K = K → conjSub c (omegaNbrGen Ω K) ≤ omegaNbrGen Ω K := by
    intro c hc
    show (omegaNbrGen Ω K).map (MulAut.conj c).toMonoidHom ≤ omegaNbrGen Ω K
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 := omegaNbr_conj hcl hM c
    rw [hc] at h1
    exact le_omegaNbrGen h1
  refine le_antisymm (key b hb) ?_
  have hb' : conjSub b⁻¹ K = K := by
    calc conjSub b⁻¹ K = conjSub b⁻¹ (conjSub b K) := by rw [hb]
      _ = K := conjSub_inv_conjSub b K
  have h2 := conjSub_mono (n := b) (key b⁻¹ hb')
  rwa [conjSub_conjSub_inv] at h2

omit [Finite G] in
theorem omegaNbrGen_le_sigmaNorm (hcl : ConjInvariant Ω) (hK : K ∈ Ω) :
    omegaNbrGen Ω K ≤ sigmaNorm Ω K :=
  iSup₂_le fun _ hM => s26_le_sigmaNorm_of_mem_dComp hcl hK (mem_dComp_of_mem_omegaNbr hM)

end Section

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.omegaNbrGen_ne_top (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd))) :
    omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ := by
  intro htop
  have hle := omegaNbrGen_le_sigmaNorm hs.hyp.conjInvariant hs.mem
  rw [htop, top_le_iff] at hle
  exact hdisc (dConnected_of_sigmaNorm_eq_top hs.mem hs.trans hle)

theorem TightStd8R.natCard_xQuot_lt_of_ne_top (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hX : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤) :
    Nat.card (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) < n := by
  have h1 : Nat.card (XQuot (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) ≤
      Nat.card ↥(omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) :=
    Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
  have h2 : Nat.card ↥(omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)) <
      Nat.card Y := by
    rw [← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hX)
  rw [← hs.large.card]
  omega

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
