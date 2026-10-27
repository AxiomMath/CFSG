module

public import CFSG.GH74.Generic.S1.SymLayer
public import CFSG.GH74.Generic.Lifting

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

namespace LayerData

variable [Finite G] {y : G} (D : LayerData y S)

theorem ι_comm_of_fixed {w : G} (hw : w ∈ centralizer ({y} : Set G)) {s : ↥S}
    (hs : barOf hw * ((D.iso.symm s : ↥D.K) : CentralizerBar y) * (barOf hw)⁻¹ =
      ((D.iso.symm s : ↥D.K) : CentralizerBar y)) : D.ι s * w = w * D.ι s := by
  have hn := D.normal
  set W : ↥(centralizer ({y} : Set G)) := ⟨w, hw⟩ with hW
  set c : ↥(centralizer ({y} : Set G)) := D.ιC s with hc
  have hWb : proj y W = barOf hw := rfl
  set k : ↥D.K := D.iso.symm s with hk
  have hLn : (liftL y D.K).Normal := liftL_normal
  have hmem : W * c * W⁻¹ * c⁻¹ ∈ liftL y D.K :=
    (liftL y D.K).mul_mem (hLn.conj_mem c (D.ιC_mem s) W) ((liftL y D.K).inv_mem (D.ιC_mem s))
  have hproj : proj y (W * c * W⁻¹ * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hWb, hc, D.proj_ιC s, ← hk, hs]
    simp
  have h1 : W * c * W⁻¹ * c⁻¹ = 1 := D.exact _ hmem hproj
  have h2 : W * c = c * W := by
    have := congrArg (fun z => z * c * W) h1
    simpa [mul_assoc] using this
  have h3 := congrArg Subtype.val h2
  exact h3.symm

theorem fixed_of_ι_comm {w : G} (hw : w ∈ centralizer ({y} : Set G)) {s : ↥S}
    (hs : D.ι s * w = w * D.ι s) :
    barOf hw * ((D.iso.symm s : ↥D.K) : CentralizerBar y) * (barOf hw)⁻¹ =
      ((D.iso.symm s : ↥D.K) : CentralizerBar y) := by
  have h1 : (⟨w, hw⟩ : ↥(centralizer ({y} : Set G))) * D.ιC s =
      D.ιC s * ⟨w, hw⟩ := Subtype.ext hs.symm
  have h2 := congrArg (proj y) h1
  rw [map_mul, map_mul, D.proj_ιC s] at h2
  have h3 : proj y (⟨w, hw⟩ : ↥(centralizer ({y} : Set G))) = barOf hw := rfl
  rw [h3] at h2
  rw [h2]
  group

@[expose] def conjIso (φ : ↥S ≃* ↥S) : LayerData y S :=
  { D with iso := D.iso.trans φ }

omit [Finite G] in
theorem conjIso_K (φ : ↥S ≃* ↥S) : (D.conjIso φ).K = D.K := rfl

theorem conjIso_ι (φ : ↥S ≃* ↥S) (s : ↥S) : (D.conjIso φ).ι s = D.ι (φ.symm s) := rfl

theorem ι_eq_of_xbar (hy : orderOf y = 2) {z : ↥S}
    (hz : ((D.iso.symm z : ↥D.K) : CentralizerBar y) = xbar y) : D.ι z = y := by
  have hz2 : z * z = 1 := by
    apply D.iso.symm.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_one]
    rw [hz]
    exact xbar_mul_self hy
  have hl2 : D.ι z * D.ι z = 1 := by rw [← map_mul, hz2, map_one]
  have hlc : D.ι z ∈ centralizer ({y} : Set G) := D.ι_mem_cent z
  have hyc : y ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.2 rfl
  set u : ↥(centralizer ({y} : Set G)) := (⟨D.ι z, hlc⟩)⁻¹ * ⟨y, hyc⟩ with hu
  have hproj : proj y u = 1 := by
    rw [hu, map_mul, map_inv]
    have h1 : proj y (⟨D.ι z, hlc⟩ : ↥(centralizer ({y} : Set G))) = xbar y := by
      have := D.proj_ιC z
      rw [hz] at this
      exact this
    have h2 : proj y (⟨y, hyc⟩ : ↥(centralizer ({y} : Set G))) = xbar y := rfl
    rw [h1, h2]
    group
  have hmem : u ∈ pPrimeCore 2 ↥(centralizer ({y} : Set G)) := (QuotientGroup.eq_one_iff u).1 hproj
  have hcomm : D.ι z * y = y * D.ι z := D.ι_comm_self z
  have hy2 : y * y = 1 := by rw [← sq, ← hy]; exact pow_orderOf_eq_one y
  have hu2 : u * u = 1 := by
    apply Subtype.ext
    simp only [hu, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
    have hli : (D.ι z)⁻¹ = D.ι z := by
      rw [inv_eq_iff_mul_eq_one]; exact hl2
    rw [hli]
    calc D.ι z * y * (D.ι z * y) = D.ι z * (y * D.ι z) * y := by group
      _ = D.ι z * (D.ι z * y) * y := by rw [hcomm]
      _ = (D.ι z * D.ι z) * (y * y) := by group
      _ = 1 := by rw [hl2, hy2]; group
  have hP : IsPGroup 2 (zpowers u) := isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hu2)
  have h1 := eq_one_of_isPGroup_of_mem_pPrimeCore hP (Subgroup.mem_zpowers _) hmem
  have h3 := congrArg Subtype.val h1
  simp only [hu, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h3
  have : (D.ι z)⁻¹ * y = 1 := h3
  rw [inv_mul_eq_one] at this
  exact this

end LayerData

end CFSG.GH74.Generic.S1
