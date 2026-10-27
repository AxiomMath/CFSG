module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSetBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section TwinLiftSet

variable {G : Type} [Group G] [Finite G]

theorem secImage_injOn {X J J' : Subgroup G} (hO : classicalInvolutionOddCore ↥X = ⊥)
    (hJ : J ≤ X) (hJ' : J' ≤ X) (h : secImage X J = secImage X J') : J = J' := by
  by_contra hne
  have hinj : Function.Injective (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO]
  exact subgroupOf_ne_of_ne hJ hJ' (Ne.symm hne) (Subgroup.map_injective hinj h.symm)

theorem twinLiftSet_of_longFundSet3 {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) {K X : Subgroup G} (hK : K ∈ Ω) (hKX : K ≤ X) {z : G}
    (hz : IsUniqueInvolution K z) (hO : classicalInvolutionOddCore ↥X = ⊥)
    (h : LongFundSet3 (secImage X K) (secInv X ⟨z, hKX hz.mem⟩)) :
    ∃ Λ : Subgroup G → Subgroup G,
      (∀ J ∈ twinSet {L | ∃ x : X, conjSub (x : G) K = L} K,
        J ≤ X ∧ Λ J ≤ X ∧ J ≤ Λ J ∧ TwinSecXg.IsClassicalMember3On X (Λ J) z) ∧
      (∀ J ∈ twinSet {L | ∃ x : X, conjSub (x : G) K = L} K,
        ∀ J' ∈ twinSet {L | ∃ x : X, conjSub (x : G) K = L} K, J ≠ J' →
          ∀ x ∈ Λ J, ∀ y ∈ Λ J', x * y = y * x) := by
  have hle : ∀ J ∈ twinSet {L | ∃ x : X, conjSub (x : G) K = L} K, J ≤ X := by
    intro J hJ
    obtain ⟨x, rfl⟩ := hJ.1
    have := conjSub_mono (n := (x : G)) hKX
    rwa [conjSub_eq_self_of_mem x.2] at this
  have htc : tightCore (secImage X K) = secImage X K :=
    tightCore_eq_self_of_isPGroup ((h2 K hK).comap_subtype.map _)
  obtain ⟨Λb, hΛb1, hΛb2, -⟩ := h
  rw [htc] at hΛb1 hΛb2
  set f := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hf
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, hf, QuotientGroup.ker_mk', hO]
  have hbij : Function.Bijective f := ⟨hinj, QuotientGroup.mk'_surjective _⟩
  let φ : SecQuot X ≃* X := (MulEquiv.ofBijective f hbij).symm
  have hφf : ∀ x : X, φ (f x) = x := fun x => (MulEquiv.ofBijective f hbij).symm_apply_apply x
  set s : X := ⟨z, hKX hz.mem⟩ with hs
  have hts : secInv X s = f s := rfl
  have htw : ∀ J ∈ twinSet {L | ∃ x : X, conjSub (x : G) K = L} K,
      secImage X J ∈ twinSet (CoreAssembly.conjClass (secImage X K)) (secImage X K) := by
    intro J hJ
    by_cases hJK : J = K
    · subst hJK
      have hJN : J.subgroupOf X ⊓ classicalInvolutionOddCore ↥X = ⊥ := by
        rw [hO]; exact inf_bot_eq _
      have hut : IsUniqueInvolution (secImage X J) (secInv X s) :=
        AscQuot.isUniqueInvolution_map_mk hJN (isUniqueInvolution_subgroupOf hz hKX)
      exact ⟨CoreAssembly.mem_conjClass_self _, secInv X s, hut, hut⟩
    · exact (TwinSecXg.twin_map_secImage hΩ h2 hK hKX hJ hJK).1
  let Λ : Subgroup G → Subgroup G := fun J => ((Λb (secImage X J)).map φ.toMonoidHom).map X.subtype
  have hsub : ∀ {M : Subgroup G} (hMX : M ≤ X) {Lb₀ : Subgroup (SecQuot X)},
      secImage X M ≤ Lb₀ → M ≤ (Lb₀.map φ.toMonoidHom).map X.subtype := by
    intro M hMX Lb₀ hle m hm
    refine ⟨φ (f ⟨m, hMX hm⟩), ⟨f ⟨m, hMX hm⟩, hle ⟨⟨m, hMX hm⟩, Subgroup.mem_subgroupOf.mpr hm,
      rfl⟩, rfl⟩, ?_⟩
    rw [hφf]
    rfl
  refine ⟨Λ, fun J hJ => ⟨hle J hJ, Subgroup.map_subtype_le _, hsub (hle J hJ) (hΛb1 _ (htw J hJ)).1,
    ⟨hKX hz.mem, ?_⟩⟩, fun J hJ J' hJ' hne => ?_⟩
  · have hLb := (hΛb1 _ (htw J hJ)).2
    have hLxc : IsClassicalMember3 ((Λb (secImage X J)).map φ.toMonoidHom) s := by
      have := TwinSecXg.isClassicalMember3_map_equiv φ hLb
      rwa [hts, hφf] at this
    show IsClassicalMember3 (((Λb (secImage X J)).map φ.toMonoidHom).map X.subtype |>.subgroupOf X) s
    rw [TwinSecXg.subgroupOf_map_subtype_self]
    exact hLxc
  · have hne' : secImage X J ≠ secImage X J' := fun e => hne (secImage_injOn hO (hle J hJ) (hle J' hJ') e)
    rintro _ ⟨x, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨y, ⟨b, hb, rfl⟩, rfl⟩
    have := hΛb2 _ (htw J hJ) _ (htw J' hJ') hne' a ha b hb
    show ((φ a : X) : G) * (φ b : X) = (φ b : X) * (φ a : X)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, this]

end TwinLiftSet

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
