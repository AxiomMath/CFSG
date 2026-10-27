module

public import CFSG.GH74.QTGen4.Recog.Ku.Final
public import CFSG.GH74.QTGen4.Recog.Ku.GenB
public import CFSG.GH74.QTGen4.Recog.Ku.Gen
public import CFSG.Quasithin.Background.HM22InvConj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem orderOf_eq_two_of_mul_self {X : Type*} [Group X] {x : X} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1

theorem m22_conj_of_involution
    {u v : Equiv.Perm (Fin 22)} (hu : u ∈ NativeSporadic.M22) (hv : v ∈ NativeSporadic.M22)
    (hou : orderOf u = 2) (hov : orderOf v = 2) :
    ∃ c ∈ NativeSporadic.M22, v = c * u * c⁻¹ := by
  obtain ⟨c₁, hc₁, h₁⟩ := CFSG.Quasithin.H.Mathieu.M22Link.m22_involution_conj hu hou
  obtain ⟨c₂, hc₂, h₂⟩ := CFSG.Quasithin.H.Mathieu.M22Link.m22_involution_conj hv hov
  refine ⟨c₂ * c₁⁻¹, NativeSporadic.M22.mul_mem hc₂ (NativeSporadic.M22.inv_mem hc₁), ?_⟩
  rw [h₁, h₂]
  group

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

section Certs


theorem gen_of_close [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafExistsIsParabolicL1]
    [KuLeaf LeafOTwoUpperInfL2] [KuLeaf LeafCardOTwoUpperInfL2] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) (hc : KuClose' T M H P z Ψ) :
    oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H = ⊤ := by
  have : IsSimpleGroup G := h.simple
  obtain ⟨Φ⟩ := h.exists_J_iso_of_close Ψ hc
  set J : Subgroup G := oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H with hJ
  have hzo : orderOf z = 2 := h.orderOf_z
  have hz1 : z ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hzo
    norm_num at hzo
  have hz2 : z * z = 1 := by
    have h0 := pow_orderOf_eq_one z
    rw [hzo, pow_two] at h0
    exact h0
  have hzP : z ∈ P := h.zP_mem
  have hPH := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) h.pH h.hNormP
    h.isPGroup_P
  have hzQ : z ∈ pCoreOf 2 H := hPH hzP
  have hWH : kuW P H ≤ H := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxH : x ∈ H := h.pH hx
    have hyH : y ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hy
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hxH hyH) (H.inv_mem hxH)) (H.inv_mem hyH)
  have hzC : z ∈ Subgroup.centralizer (kuW P H : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr (fun w hw => ?_)
    have hwH : w ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [← h.hCz]
      exact hWH hw
    exact Subgroup.mem_centralizer_singleton_iff.mp hwH
  have hzkuA : z ∈ kuA P H := Subgroup.mem_inf.mpr ⟨hzQ, hzC⟩
  have hzN : z ∈ kuN P H := Subgroup.le_normalizer hzkuA
  have hzJ : z ∈ J := (le_sup_right : kuN P H ≤ J) hzN
  set ψ : ↥J →* Equiv.Perm (Fin 22) := NativeSporadic.M22.subtype.comp Φ.toMonoidHom with hψdef
  have hψΦ : ∀ x : ↥J, ψ x = ((Φ x : ↥NativeSporadic.M22) : Equiv.Perm (Fin 22)) :=
    fun x => rfl
  have hψinj : Function.Injective ψ := fun a b hab => Φ.injective (Subtype.ext hab)
  have hψmem : ∀ x : ↥J, ψ x ∈ NativeSporadic.M22 := fun x => (Φ x).2
  have hψone : ψ 1 = 1 := map_one ψ
  have hψmul : ∀ a b : ↥J, ψ (a * b) = ψ a * ψ b := fun a b => map_mul ψ a b
  set ζ : ↥J := ⟨z, hzJ⟩ with hζdef
  have hζ2 : ζ * ζ = 1 := Subtype.ext hz2
  have hζ1 : ζ ≠ 1 := fun e => hz1 (congrArg Subtype.val e)
  have hu2 : ψ ζ * ψ ζ = 1 := by rw [← hψmul, hζ2, hψone]
  have hu1 : ψ ζ ≠ 1 := fun e => hζ1 (hψinj (e.trans hψone.symm))
  have hou : orderOf (ψ ζ) = 2 := orderOf_eq_two_of_mul_self hu2 hu1
  have huM : ψ ζ ∈ NativeSporadic.M22 := hψmem ζ
  have hCmap : (Subgroup.centralizer ({ζ} : Set ↥J)).map ψ =
      NativeSporadic.M22 ⊓ Subgroup.centralizer ({ψ ζ} : Set (Equiv.Perm (Fin 22))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyz : y * ζ = ζ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      refine Subgroup.mem_inf.mpr ⟨hψmem y, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg ψ hyz
      rw [hψmul, hψmul] at this
      exact this
    · intro hx
      obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.mp hx
      have hxc' : x * ψ ζ = ψ ζ * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
      have hy' : ψ (Φ.symm ⟨x, hxM⟩) = x := by
        rw [hψΦ, MulEquiv.apply_symm_apply]
      refine ⟨Φ.symm ⟨x, hxM⟩, ?_, hy'⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply hψinj
      rw [hψmul, hψmul, hy']
      exact hxc'
  have hcardC : Nat.card ↥(Subgroup.centralizer ({ζ} : Set ↥J)) = 384 := by
    rw [← Subgroup.card_map_of_injective (f := ψ) hψinj, hCmap]
    exact CFSG.Quasithin.H.Mathieu.M22Link.m22_involution_centralizer_card huM hou
  have hCG : (Subgroup.centralizer ({ζ} : Set ↥J)).map J.subtype =
      J ⊓ Subgroup.centralizer ({z} : Set G) := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyz : y * ζ = ζ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
      have hyz' : (y : G) * z = z * (y : G) := congrArg Subtype.val hyz
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyz'⟩
    · intro hg
      obtain ⟨hgJ, hgc⟩ := Subgroup.mem_inf.mp hg
      refine ⟨⟨g, hgJ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hgc
  have hcardJH : Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set G)) = 384 := by
    rw [← hCG, Subgroup.card_map_of_injective (f := J.subtype) J.subtype_injective]
    exact hcardC
  have hcardJH' : Nat.card ↥(J ⊓ H) = 384 := by
    rw [h.hCz]
    exact hcardJH
  have hJH : J ⊓ H = H :=
    Subgroup.eq_of_le_of_card_ge (inf_le_right : J ⊓ H ≤ H)
      (le_of_eq (by rw [h.card_H, hcardJH']))
  have hHJ : H ≤ J := by
    rw [← hJH]
    exact inf_le_left
  have hHM : Subgroup.centralizer ({z} : Set G) ≤ J := by
    rw [← h.hCz]
    exact hHJ
  have hconj : ∀ y ∈ J, y * y = 1 → y ≠ 1 → ∃ k ∈ J, k * z * k⁻¹ = y := by
    intro y hy hy2 hy1
    have hyJ2 : (⟨y, hy⟩ : ↥J) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    have hyJ1 : (⟨y, hy⟩ : ↥J) ≠ 1 := fun e => hy1 (congrArg Subtype.val e)
    have hv2 : ψ ⟨y, hy⟩ * ψ ⟨y, hy⟩ = 1 := by rw [← hψmul, hyJ2, hψone]
    have hv1 : ψ ⟨y, hy⟩ ≠ 1 := fun e => hyJ1 (hψinj (e.trans hψone.symm))
    obtain ⟨c, hc', hcy⟩ := m22_conj_of_involution huM (hψmem ⟨y, hy⟩) hou
      (orderOf_eq_two_of_mul_self hv2 hv1)
    have hψk : ψ (Φ.symm ⟨c, hc'⟩) = c := by
      rw [hψΦ, MulEquiv.apply_symm_apply]
    have key : Φ.symm ⟨c, hc'⟩ * ζ * (Φ.symm ⟨c, hc'⟩)⁻¹ = ⟨y, hy⟩ := by
      apply hψinj
      rw [hcy]
      simp only [map_mul, map_inv, hψk]
    refine ⟨((Φ.symm ⟨c, hc'⟩ : ↥J) : G), (Φ.symm ⟨c, hc'⟩).2, ?_⟩
    exact congrArg Subtype.val key
  have hsyl := h.exists_sylow_card_center_eq_two
  have hcomm : ∃ a : G, a * a = 1 ∧ a ≠ 1 ∧ a ≠ z ∧
      ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ a ∈ (S : Subgroup G) := by
    obtain ⟨S, hPS⟩ := h.isPGroup_P.exists_le_sylow
    obtain ⟨d, hdP, hdz, -⟩ := h.typeM22
    refine ⟨d⁻¹ * z * d, ?_, ?_, ?_, S, hPS hzP, hPS hdP⟩
    · calc d⁻¹ * z * d * (d⁻¹ * z * d) = d⁻¹ * (z * z) * d := by group
        _ = 1 := by rw [hz2]; group
    · intro e
      apply hz1
      calc z = d * (d⁻¹ * z * d) * d⁻¹ := by group
        _ = 1 := by rw [e]; group
    · exact hdz
  exact top_of_conj_z hz2 hz1 hsyl hcomm hHM hconj

theorem nonempty_mulEquiv_m22_of_close [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafExistsIsParabolicL1]
    [KuLeaf LeafOTwoUpperInfL2] [KuLeaf LeafCardOTwoUpperInfL2] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) (hc : KuClose' T M H P z Ψ) :
    Nonempty (G ≃* NativeSporadic.M22) := by
  obtain ⟨Φ⟩ := h.exists_J_iso_of_close Ψ hc
  have hJ := h.gen_of_close Ψ hc
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hJ.symm).trans Φ)⟩

end Certs

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
