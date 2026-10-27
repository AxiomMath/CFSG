module

public import CFSG.GH74.Generic.Front.FrontShapes
public import CFSG.GH74.Generic.Assembly

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint Subgroup

theorem s2_shapeCase (hD : FrontDataStatement) (hO : OuterStatement) (hSp : SpOuterInvolution) :
    S_shapeCase @ShapeS2 := by
  intro G _ _ hs hn hr hgen hK hnab hL x hx K hKc hG2 hsh
  exfalso
  obtain ⟨hS2, hxK⟩ := hsh
  have hmodel : ShapeModel ↥K := Or.inr hS2
  obtain ⟨D⟩ := hD ↥K hmodel
  have hfr : Q8Frame ↥K := ⟨D.φ, D.inj, D.w, D.w_sq, D.w_swap⟩
  obtain ⟨hxK', hlayer, hcentK, -, -, -⟩ := frame_B2 hgen hx hKc hfr
  have hKn : K.Normal := normal_of_layer_eq hlayer
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K := by
    rw [hcentK]
    exact (Subgroup.zpowers_le).2 hxK'
  have hSch := goodSub_le_of_outerStatement hO K hmodel hcentle
  have hB5 := noNoncentralInvolutionConj_of_data hgen hx hKc D hSch
  obtain ⟨v, hv, hconj, hvx, hv2, hvb1, hvbx, hvbK⟩ :=
    exists_outer_involution hs hn hgen hx hfr hB5
  obtain ⟨F, hFfield, hFfin, hodd, ⟨eK⟩⟩ := hS2
  have hbar2 : barOf hv * barOf hv = 1 := by
    have : proj x ((⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩) = 1 := by
      rw [show (⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩ = 1 from Subtype.ext hv2,
        map_one]
    rwa [map_mul] at this
  obtain ⟨H, hHle, hHz, hHgood⟩ := hSp F hodd (CentralizerBar x) K ⟨eK⟩ hcentle
    (gen4_centralizerBar hgen x) (barOf hv) hbar2 hvbK
  obtain ⟨c, hc'⟩ := isConj_iff.1 hconj
  obtain ⟨U, hU⟩ : ∃ U : ↥(centralizer ({x} : Set G)), U = ⟨v, hv⟩ := ⟨_, rfl⟩
  have hU2 : U * U = 1 := by rw [hU]; exact Subtype.ext hv2
  have hc : c⁻¹ * (U : G) * c = x := by
    rw [hU]
    show c⁻¹ * v * c = x
    rw [← hc']
    group
  have hbar : barOf hv = proj x U := by rw [hU]; rfl
  have hHc : ∀ h ∈ H, h * proj x U = proj x U * h := fun h hh => by
    rw [← hbar]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hHle hh).2
  have hxcent : (xH x : ↥(centralizer ({x} : Set G))) ∈ CU x U :=
    Subgroup.mem_centralizer_singleton_iff.2 (xH_central x U).symm
  have hxH : proj x (xH x) ∈ H := by
    refine hHz ⟨xbar x, hxK'⟩ ?_
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (xbar_comm x (g : CentralizerBar x))
  have hres := transfer_bar x U hU2 hc (ThreeModel ↥K) K hSch H hHgood hHc ⟨xH x, hxcent⟩ hxH
    ⟨1, by rw [pow_one, pow_two]; exact xH_mul_self hx⟩
  obtain ⟨x2, hx2⟩ : ∃ x2 : ↥(centralizer ({x} : Set G)),
      x2 = transportC x U hc ⟨xH x, hxcent⟩ := ⟨_, rfl⟩
  have hx2val : (x2 : G) = c⁻¹ * x * c := by rw [hx2]; rfl
  have hx2sq : x2 * x2 = 1 := by
    have h1 : (⟨xH x, hxcent⟩ : ↥(CU x U)) * ⟨xH x, hxcent⟩ = 1 :=
      Subtype.ext (xH_mul_self hx)
    rw [hx2, ← map_mul, h1, map_one]
  have hbK : proj x x2 ∈ K := by rw [hx2]; exact hres
  have hne : proj x x2 ≠ xbar x := by
    intro h
    have hn' : x2⁻¹ * xH x ∈ pPrimeCore 2 ↥(centralizer ({x} : Set G)) :=
      (QuotientGroup.eq).1 h
    have hcomm : x2 * xH x = xH x * x2 := xH_central x x2
    have hsq : (x2⁻¹ * xH x) * (x2⁻¹ * xH x) = 1 := by
      have h1 : xH x * x2⁻¹ = x2⁻¹ * xH x := by
        have := congrArg (fun z => x2⁻¹ * z * x2⁻¹) hcomm
        simpa [mul_assoc] using this
      calc (x2⁻¹ * xH x) * (x2⁻¹ * xH x) = x2⁻¹ * (xH x * x2⁻¹) * xH x := by group
        _ = x2⁻¹ * (x2⁻¹ * xH x) * xH x := by rw [h1]
        _ = (x2 * x2)⁻¹ * (xH x * xH x) := by group
        _ = 1 := by rw [hx2sq, xH_mul_self hx]; group
    have hP : IsPGroup 2 (zpowers (x2⁻¹ * xH x)) :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hsq)
    have h1 := eq_one_of_isPGroup_of_mem_pPrimeCore hP (Subgroup.mem_zpowers _) hn'
    have h2 : x2 = xH x := by
      have := congrArg (fun z => x2 * z) h1
      simpa using this.symm
    have h3 : c⁻¹ * x * c = x := by
      rw [← hx2val, h2]
      rfl
    apply hvx
    rw [← hc']
    have h4 : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [h3] at h4
    exact h4.symm
  exact hB5 (x2 : G) x2.2 (congrArg Subtype.val hx2sq) hbK hne
    (isConj_iff.2 ⟨c⁻¹, by rw [hx2val]; group⟩)

end CFSG.GH74.Generic
