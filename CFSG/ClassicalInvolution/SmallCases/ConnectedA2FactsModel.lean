module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsPairs

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Quotient

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_classicalOddCore_of_sq {Y : Type} [Group Y] [Finite Y] {u : Y}
    (hu : u ∈ classicalInvolutionOddCore Y) (h : u * u = 1) : u = 1 := by
  have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
  have h2 : orderOf (⟨u, hu⟩ : classicalInvolutionOddCore Y) ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    apply Subtype.ext
    simpa [pow_two] using h
  have h3 := orderOf_dvd_natCard (⟨u, hu⟩ : classicalInvolutionOddCore Y)
  have h4 := Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) h2 h3
  have h5 : (⟨u, hu⟩ : classicalInvolutionOddCore Y) = 1 := orderOf_eq_one_iff.mp h4
  exact congrArg Subtype.val h5

theorem isUniqueInvolution_locImg {Ω : Set (Subgroup G)} (hex : ExactMembers Ω) {x : G}
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) {w : G} (hw : IsUniqueInvolution L w) :
    IsUniqueInvolution (locImg Ω x L) (locMk Ω x ⟨w, le_centralizingLayer hL hw.mem⟩) := by
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom
        (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L := CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := inf_oddCore_eq_bot hO
  have hmem : (⟨w, hLY hw.mem⟩ : ↥(locLayer Ω x)) ∈ L.subgroupOf (locLayer Ω x) :=
    Subgroup.mem_subgroupOf.mpr hw.mem
  refine ⟨⟨_, hmem, rfl⟩, ?_, ?_, ?_⟩
  · intro h1
    have hO' : (⟨w, hLY hw.mem⟩ : ↥(locLayer Ω x)) ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have : (⟨w, hLY hw.mem⟩ : ↥(locLayer Ω x)) ∈ L.subgroupOf (locLayer Ω x) ⊓
        classicalInvolutionOddCore ↥(locLayer Ω x) := ⟨hmem, hO'⟩
    rw [hinf, Subgroup.mem_bot] at this
    exact hw.ne_one (congrArg Subtype.val this)
  · rw [← map_mul]
    have : (⟨w, hLY hw.mem⟩ : ↥(locLayer Ω x)) * ⟨w, hLY hw.mem⟩ = 1 :=
      Subtype.ext hw.sq
    rw [this, map_one]
  · rintro _ ⟨k, hk, rfl⟩ hk2
    have hk' : (k : G) ∈ L := Subgroup.mem_subgroupOf.mp hk
    have h1 : locMk Ω x (k * k) = 1 := by rw [map_mul]; exact hk2
    have hO' : k * k ∈ classicalInvolutionOddCore ↥(locLayer Ω x) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have hkk : k * k ∈ L.subgroupOf (locLayer Ω x) ⊓ classicalInvolutionOddCore ↥(locLayer Ω x) :=
      ⟨(L.subgroupOf (locLayer Ω x)).mul_mem hk hk, hO'⟩
    rw [hinf, Subgroup.mem_bot] at hkk
    have hsq : (k : G) * (k : G) = 1 := congrArg Subtype.val hkk
    rcases hw.unique (k : G) hk' hsq with h | h
    · left
      have : k = 1 := Subtype.ext h
      rw [this, map_one]
    · right
      have : k = ⟨w, hLY hw.mem⟩ := Subtype.ext h
      rw [this]

end Quotient

section Normalized

variable {X : Type} [Group X]

structure NormalizedPair (U V : Subgroup X) (a₁ a₂ : X) : Prop where
  uniq₁ : IsUniqueInvolution U a₁
  uniq₂ : IsUniqueInvolution V a₂
  comm : a₁ * a₂ = a₂ * a₁
  ne : a₁ ≠ a₂
  norm₁ : conjSub a₁ V = V
  norm₂ : conjSub a₂ U = U
  nc : ¬ Commutes U V

end Normalized

section Frame

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {F : Type} [Field F] {A : Subgroup G} {S : Set (Subgroup G)}

theorem exists_modelPair_of_frame {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (CoreAssembly.conjClass K))
    (Fr : RankFrame F (CoreAssembly.conjClass K) A S)
    (hP1A : FrameP1 (CoreAssembly.conjClass K) A) {x : G}
    (hP1x : LocalOddCentral (CoreAssembly.conjClass K) {x})
    (D : LieSystemData p f (locQuot (CoreAssembly.conjClass K) x)
      (locFamily (CoreAssembly.conjClass K) x)) {K' L' : Subgroup G} (hK' : K' ∈ S) (hL' : L' ∈ S)
    (hxK : x ∈ axisSub A K') (hxL : x ∈ axisSub A L') (hne : K' ≠ L') (hnc : ¬ Commutes K' L') :
    ∃ (i : Fin D.card)
      (R₀ Rβ : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K)
      (a₁ a₂ : locQuot (CoreAssembly.conjClass K) x),
      R₀ ∈ compFund D i ∧ Rβ ∈ compFund D i ∧
      R₀.map (D.hom i) = locImg (CoreAssembly.conjClass K) x K' ∧
      Rβ.map (D.hom i) = locImg (CoreAssembly.conjClass K) x L' ∧
      NormalizedPair (locImg (CoreAssembly.conjClass K) x K')
        (locImg (CoreAssembly.conjClass K) x L') a₁ a₂ := by
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hb.member
  have hmK := mem_centralizingMembers_of_axisSub (Fr.subset hK') hxK
  have hmL := mem_centralizingMembers_of_axisSub (Fr.subset hL') hxL
  obtain ⟨i, h0i, hβi, -⟩ := exists_pair hΩ hex hP1x D hmK hmL hnc
  obtain ⟨R₀, hR₀⟩ := exists_corr_left hΩ hex D h0i
  obtain ⟨Rβ, hRβ⟩ := exists_corr_left hΩ hex D hβi
  obtain ⟨zK, hzK⟩ := Fr.exists_isUniqueInvolution hK'
  obtain ⟨zL, hzL⟩ := Fr.exists_isUniqueInvolution hL'
  have hzKA : zK ∈ A := Fr.mem_of_isUniqueInvolution hK' hzK
  have hzLA : zL ∈ A := Fr.mem_of_isUniqueInvolution hL' hzL
  have hzKY : zK ∈ locLayer (CoreAssembly.conjClass K) x := le_centralizingLayer hmK hzK.mem
  have hzLY : zL ∈ locLayer (CoreAssembly.conjClass K) x := le_centralizingLayer hmL hzL.mem
  refine ⟨i, R₀, Rβ, locMk _ x ⟨zK, hzKY⟩, locMk _ x ⟨zL, hzLY⟩, hR₀.2.1, hRβ.2.1,
    hR₀.2.2.symm, hRβ.2.2.symm, isUniqueInvolution_locImg hex hmK hzK,
    isUniqueInvolution_locImg hex hmL hzL, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Fr.comm_of_mem hzKA hzLA)
  · intro h
    have h1 := QuotientGroup.eq.mp h
    have hzKinv : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK.sq
    have hcomm := Fr.comm_of_mem hzKA hzLA
    have hsq : ((⟨zK, hzKY⟩ : ↥(locLayer (CoreAssembly.conjClass K) x))⁻¹ * ⟨zL, hzLY⟩) *
        ((⟨zK, hzKY⟩ : ↥(locLayer (CoreAssembly.conjClass K) x))⁻¹ * ⟨zL, hzLY⟩) = 1 := by
      apply Subtype.ext
      show (zK⁻¹ * zL) * (zK⁻¹ * zL) = 1
      rw [hzKinv]
      calc zK * zL * (zK * zL) = zK * (zL * zK) * zL := by group
        _ = zK * (zK * zL) * zL := by rw [← hcomm]
        _ = (zK * zK) * (zL * zL) := by group
        _ = 1 := by rw [hzK.sq, hzL.sq, one_mul]
    have h2 := eq_one_of_mem_classicalOddCore_of_sq h1 hsq
    have h3 : zK = zL := by
      have := congrArg Subtype.val h2
      change zK⁻¹ * zL = 1 at this
      rw [hzKinv] at this
      exact (mul_left_cancel (this.trans (hzK.sq).symm)).symm
    exact hnc (commutes_of_same_involution hb hex Fr hP1A hK' hL' hzK (h3 ▸ hzL) hne)
  · have e : conjSub zK L' = L' := (Fr.inSigma hL').conjSub_eq hzKA
    have h := locImg_conjSub_layer (Ω := CoreAssembly.conjClass K) (x := x) L' ⟨zK, hzKY⟩
    rw [show ((⟨zK, hzKY⟩ : ↥(locLayer (CoreAssembly.conjClass K) x)) : G) = zK from rfl, e] at h
    exact h.symm
  · have e : conjSub zL K' = K' := (Fr.inSigma hK').conjSub_eq hzLA
    have h := locImg_conjSub_layer (Ω := CoreAssembly.conjClass K) (x := x) K' ⟨zL, hzLY⟩
    rw [show ((⟨zL, hzLY⟩ : ↥(locLayer (CoreAssembly.conjClass K) x)) : G) = zL from rfl, e] at h
    exact h.symm
  · exact fun h => hnc ((commutes_iff_locImg hΩ hP1x hmK hmL).mpr h)

end Frame

end CFSG.ClassicalInvolution.ConnectedA2
