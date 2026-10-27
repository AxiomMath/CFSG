module

public import CFSG.ClassicalInvolution.Q3.TL4Conn26X
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Main

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

@[expose] def TightSecNbrGenR (r n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam r Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ → (∀ L ∈ Φ, AEmpty Φ L) →
      ∀ L ∈ Φ, omegaNbrGen Φ L ≠ ⊤

variable {G : Type} [Group G] [Finite G] {r : ℕ} {Ω : Set (Subgroup G)}

section Image

variable {X : Subgroup G}

theorem map_mk_ne_of_isUniqueInvolution {L M : Subgroup G} (hLX : L ≤ X)
    (hMX : M ≤ X) {z y : G} (hz : IsUniqueInvolution L z) (hy : IsUniqueInvolution M y)
    (hzy : z * y = y * z) (hne : z ≠ y) :
    (L.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ≠
      (M.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) := by
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  intro heq
  have h1 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN _)
    (isUniqueInvolution_subgroupOf hz hLX)
  have h2 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hN _)
    (isUniqueInvolution_subgroupOf hy hMX)
  rw [heq] at h1
  have he := h1.eq h2
  set z' : ↥X := ⟨z, hLX hz.mem⟩
  set y' : ↥X := ⟨y, hMX hy.mem⟩
  have hmem : z' * y' ∈ classicalInvolutionOddCore ↥X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    have e2 : (QuotientGroup.mk z' : ↥X ⧸ classicalInvolutionOddCore ↥X) = QuotientGroup.mk y' :=
      he
    rw [e2, ← QuotientGroup.mk_mul]
    have : y' * y' = 1 := Subtype.ext hy.sq
    rw [this, QuotientGroup.mk_one]
  have hsq : (z' * y') * (z' * y') = 1 := by
    apply Subtype.ext
    show z * y * (z * y) = 1
    calc z * y * (z * y) = z * (y * z) * y := by group
      _ = z * (z * y) * y := by rw [hzy]
      _ = (z * z) * (y * y) := by group
      _ = 1 := by rw [hz.sq, hy.sq]; group
  have h3 := eq_one_of_isPGroup_of_mem_odd hN hmem (isPGroup_zpowers_of_sq hsq)
  apply hne
  have h4 : z * y = 1 := congrArg Subtype.val h3
  calc z = z * (y * y) := by rw [hy.sq, mul_one]
    _ = (z * y) * y := by group
    _ = y := by rw [h4, one_mul]

theorem map_mk_mem_omegaNbr_of_le (h : TypeRFam r Ω) {K J : Subgroup G} (hKX : K ≤ X)
    (hJX : J ≤ X) (hJ : J ∈ omegaNbr Ω K)
    (hne : (K.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ≠
      (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))) :
    (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈
      omegaNbr (oddQuotientFamily (restrictFamily Ω X))
        ((K.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))) := by
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le h.hyp hJΩ hT hTJ
  have hT' : IsSylow2In (T.subgroupOf X) (J.subgroupOf X) := hTsyl.subgroupOf hJX
  have hJmem : (J.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) ∈
      oddQuotientFamily (restrictFamily Ω X) := ⟨_, ⟨J, hJΩ, hJX, rfl⟩, rfl⟩
  refine ⟨hJmem, hne.symm, (T.subgroupOf X).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)),
    mem_RSet_of_isSylow2In hJmem (isSylow2In_map_mk hN hT'), Subgroup.map_mono hT'.1, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp' : (p : G) ∈ Subgroup.normalizer (K : Set G) := hTN (Subgroup.mem_subgroupOf.mp hp)
  exact mk_mem_normalizer_map ((mem_normalizer_subgroupOf_iff hKX).mp hp')

end Image

section Gen

variable {K : Subgroup G}

omit [Finite G] in
theorem top_eq_iSup_subgroupOf_omegaNbr :
    (⊤ : Subgroup ↥(omegaNbrGen Ω K)) =
      ⨆ J ∈ omegaNbr Ω K, J.subgroupOf (omegaNbrGen Ω K) := by
  apply Subgroup.map_injective (omegaNbrGen Ω K).subtype_injective
  rw [Subgroup.map_top, Subgroup.range_subtype]
  refine le_antisymm ?_ (Subgroup.map_subtype_le _)
  refine iSup₂_le fun J hJ => ?_
  calc J = (J.subgroupOf (omegaNbrGen Ω K)).map (omegaNbrGen Ω K).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_omegaNbrGen hJ)).symm
    _ ≤ _ := Subgroup.map_mono (le_iSup₂ (f := fun J (_ : J ∈ omegaNbr Ω K) =>
        J.subgroupOf (omegaNbrGen Ω K)) J hJ)

end Gen

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}
  {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.not_le_omegaNbrGen_of_ne_top (hN : TightSecNbrGenR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hX : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤) :
    ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  set K := tightCore Rd with hKdef
  set X := omegaNbrGen Ω K with hXdef
  intro hKX
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
  have hKb : (K.subgroupOf X).map π ∈ xFam Ω K := ⟨_, ⟨K, hs.mem, hKX, rfl⟩, rfl⟩
  have hnbr : ∀ J' ∈ omegaNbr Ω K, (J'.subgroupOf X).map π ∈
      omegaNbr (xFam Ω K) ((K.subgroupOf X).map π) := by
    intro J' hJ'
    obtain ⟨t', ht'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ'.1
    refine map_mk_mem_omegaNbr_of_le h hKX (le_omegaNbrGen hJ') hJ' ?_
    exact map_mk_ne_of_isUniqueInvolution hKX (le_omegaNbrGen hJ') hs.hz ht'
      (Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hJ' ht')
      (T8.ne_of_mem_omegaNbr hs.noTwins hJ' hs.hz ht')
  have htop : omegaNbrGen (xFam Ω K) ((K.subgroupOf X).map π) = ⊤ := by
    rw [eq_top_iff, ← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _),
      top_eq_iSup_subgroupOf_omegaNbr, Subgroup.map_iSup]
    refine iSup_le fun J' => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hJ' => le_omegaNbrGen (hnbr J' hJ')
  exact hN _ (hs.natCard_xQuot_lt_of_ne_top hX) _ h.xFam xQuot_oddCore_eq_bot omegaGen_xFam
    (aEmpty_xFam h) _ hKb htop

theorem TightStd8R.not_le_omegaNbrGen (hN : TightSecNbrGenR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hdisc : ¬ DConnected (CoreAssembly.conjClass (tightCore Rd))) :
    ¬ tightCore Rd ≤ omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
  hs.not_le_omegaNbrGen_of_ne_top hN (hs.omegaNbrGen_ne_top hdisc)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
