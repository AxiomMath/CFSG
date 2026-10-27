module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf51Ambient
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.Q3T6DCaseIC
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.T3Core CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Uniform CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6D

section Case

theorem frame_false_of_g2Section (h4 : Asc75Theorem4) {T : Type} [Group T] [Finite T]
    [CaseIAmbient T] {R : Subgroup T} {t : T} {J : Subgroup T} {zK zJ : T}
    (hh : FrameCaseIHyps T R t J zK zJ) {H : Subgroup T}
    (hHdef : omegaGen (aStar (CoreAssembly.conjClass R) R) = H) (hsec : G2Section H zK) : False := by
  have hD := hh.datum
  have hv := hh.viol
  have hne := hh.ne
  have hΩg : HypOmegaGen (CoreAssembly.conjClass R) := hD.hyp
  have hK : R ∈ CoreAssembly.conjClass R := CoreAssembly.mem_conjClass_self R
  have htrans : ∀ M ∈ CoreAssembly.conjClass R, ∃ g : T, conjSub g R = M := by
    intro M hM
    obtain ⟨g, rfl⟩ := hM
    exact ⟨g, rfl⟩
  have hKS : R ∈ aStar (CoreAssembly.conjClass R) R := Relation.ReflTransGen.refl
  have hJS : J ∈ aStar (CoreAssembly.conjClass R) R :=
    Relation.ReflTransGen.single ⟨hv.mem, Or.inl ⟨zK, zJ, hv⟩⟩
  have hKH : R ≤ H := hHdef ▸ le_omegaGen hKS
  have hJH : J ≤ H := hHdef ▸ le_omegaGen hJS
  have hz : IsUniqueInvolution R zK := hv.hzK
  have ht : IsUniqueInvolution J zJ := hv.hzJ
  have hzH : zK ∈ H := hKH hz.mem
  have htH : zJ ∈ H := hJH ht.mem
  have hHtop : H ≠ ⊤ := fun h =>
    hne (aStar_eq_of_omegaGen_eq_top hΩg.conjInvariant hK htrans (hHdef.trans h))
  have hT : TightlyEmbedded H :=
    tightlyEmbedded_of_g2Section hΩg.conjInvariant hK hz hHdef hsec
  have hlay : twoPrimeLayerIn H = H := twoPrimeLayerIn_eq_self hsec.quasisimple
  have hne' : twoPrimeLayerIn H ≠ oddCoreIn H := by
    rw [hlay]
    intro h
    exact not_mem_oddCoreIn hz (h ▸ hzH)
  have hHn : ¬ H.Normal := fun hN => hHtop (hD.eq_top_of_normal hN hKH)
  have hF : IsSimpleGroup (CFSG.generalizedFitting T) :=
    CaseIAmbient.isSimpleGroup_generalizedFitting
  rcases h4 T H hT hne' with hBn | ⟨hr, -⟩ | ⟨g, hg, P, hPs, hPN, n, hn, φ, hφ, hker⟩
  · exact false_of_normalIn_twoPrimeLayerIn_top hT hHn hF hne' hBn
  · rw [hlay] at hr
    have h2 := two_le_pRank_of_commuting hz.sq ht.sq hz.ne_one ht.ne_one
      (AViol.ne_involution_gen hΩg hK hv).symm (AViol.comm_gen hΩg hv) hzH htH
    omega
  · obtain ⟨k, hkK, hkk, hk4⟩ := Q3T6D.exists_sq_eq_involution3 hΩg hK hz
    have hkH : k ∈ H := hKH hkK
    have hkC : k ∈ oUpperTwoPrime (H ⊔ P) :=
      Subgroup.subset_closure ⟨(le_sup_left : H ≤ H ⊔ P) hkH, 2, by simpa using hk4⟩
    have hzC : zK ∈ oUpperTwoPrime (H ⊔ P) :=
      Subgroup.subset_closure ⟨(le_sup_left : H ≤ H ⊔ P) hzH, 1, by simpa [pow_two] using hz.sq⟩
    set k' : ↥(oUpperTwoPrime (H ⊔ P)) := ⟨k, hkC⟩ with hk'
    set z' : ↥(oUpperTwoPrime (H ⊔ P)) := ⟨zK, hzC⟩ with hz'
    have hkz : k' ^ 2 = z' := Subtype.ext (by rw [pow_two, Subgroup.coe_mul]; exact hkk)
    have hk'4 : k' ^ 4 = 1 := Subtype.ext (by simpa using hk4)
    have hz1 : φ z' ≠ 1 := by
      intro h
      have hzk : z' ∈ φ.ker := h
      rw [hker, Subgroup.mem_subgroupOf] at hzk
      exact not_mem_oddCoreIn hz hzk
    have h44 : (φ k') ^ 4 = 1 := by rw [← map_pow, hk'4, map_one]
    exact hz1 (by rw [← hkz, map_pow]; exact prod_sq_eq_one_of_pow_four _ h44)

@[expose] def FrameC201U3FalseF : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [CaseIAmbient T] (R : Subgroup T) (t : T) (J : Subgroup T)
    (zK zJ : T), FrameCaseIHyps T R t J zK zJ → ∀ H : Subgroup T,
      omegaGen (aStar (CoreAssembly.conjClass R) R) = H → Thm3RowU3 (⊤ : Subgroup ↥H) → False

end Case

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
