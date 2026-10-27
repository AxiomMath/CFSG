module

public import CFSG.GH74.QTGen4.Recog.Ku.RStructE

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

omit [Finite G] in
theorem kuV2_sq (h : KuHyp G T M H P z) {v : G} (hv : v ∈ kuV2 T M) : v * v = 1 := by
  have := h.vElem.2 v hv.1
  rwa [pow_two] at this

omit [Finite G] in
theorem pCore_sq (h : KuHyp G T M H P z) {v : G} (hv : v ∈ pCoreOf 2 M) : v * v = 1 := by
  have := h.vElem.2 v hv
  rwa [pow_two] at this

omit [Finite G] in
theorem kuV2_comm (_h : KuHyp G T M H P z) {v r : G} (hv : v ∈ kuV2 T M) (hr : r ∈ kuR T M) :
    v * r = r * v :=
  (Subgroup.mem_centralizer_iff.mp hv.2 r hr).symm

theorem invol_coset_subset (h : KuHyp G T M H P z) {a b : G} (ha : a ∈ kuR T M)
    (haV : a ∉ pCoreOf 2 M) (haa : a * a = 1) (hb : b * b = 1) (hab : a⁻¹ * b ∈ pCoreOf 2 M) :
    a⁻¹ * b ∈ kuV2 T M := by
  rw [← h.centralizer_pCore_eq_kuV2 ha haV]
  refine ⟨hab, ?_⟩
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hv2 : a⁻¹ * b * (a⁻¹ * b) = 1 := h.pCore_sq hab
  rw [hai] at hv2 ⊢
  show a * b ∈ Subgroup.centralizer ({a} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  symm
  calc a * (a * b) = (a * a) * b := by group
    _ = b := by rw [haa, one_mul]
    _ = a * b * a := by
      calc b = 1 * b := (one_mul b).symm
        _ = (a * b * (a * b)) * b := by rw [hv2]
        _ = a * b * a * (b * b) := by group
        _ = a * b * a := by rw [hb, mul_one]

theorem relIndex_pCore_kuR (h : KuHyp G T M H P z) :
    (pCoreOf 2 M).relIndex (kuR T M) = 4 := by
  have hm := (Subgroup.relIndex_mul_card (H := pCoreOf 2 M) (K := kuR T M))
  rw [inf_eq_left.mpr h.pCore_le_kuR, h.card_kuR, h.vCard] at hm
  omega

theorem commute_conj_involution (h : KuHyp G T M H P z) {y u : G}
    (hyR : y ∈ Subgroup.normalizer (kuR T M : Set G)) (hy3 : y ^ 3 = 1)
    (hf : ∀ v ∈ pCoreOf 2 M, y * v * y⁻¹ * v⁻¹ ∈ kuV2 T M → v ∈ kuV2 T M)
    (hg : ∀ r ∈ kuR T M, y * r * y⁻¹ * r⁻¹ ∈ pCoreOf 2 M → r ∈ pCoreOf 2 M)
    (hu : u ∈ kuR T M) (huu : u * u = 1) :
    u * (y * u * y⁻¹) = (y * u * y⁻¹) * u := by
  have hconj : ∀ x ∈ kuR T M, y * x * y⁻¹ ∈ kuR T M := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hyR x).mp hx
  set c₂ : G := y * u * y⁻¹ with hc₂
  set c₃ : G := y * c₂ * y⁻¹ with hc₃
  have hc₂R : c₂ ∈ kuR T M := hconj u hu
  have hc₃R : c₃ ∈ kuR T M := hconj c₂ hc₂R
  have hc₂₂ : c₂ * c₂ = 1 := by
    have : c₂ * c₂ = y * (u * u) * y⁻¹ := by rw [hc₂]; group
    rw [this, huu]; group
  have hc₃₃ : c₃ * c₃ = 1 := by
    have : c₃ * c₃ = y * (c₂ * c₂) * y⁻¹ := by rw [hc₃]; group
    rw [this, hc₂₂]; group
  have hyc₃ : y * c₃ * y⁻¹ = u := by
    have : y * c₃ * y⁻¹ = y ^ 3 * u * (y ^ 3)⁻¹ := by
      rw [hc₃, hc₂]; simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [this, hy3]; group
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hc₂i : c₂⁻¹ = c₂ := inv_eq_of_mul_eq_one_right hc₂₂
  set w : G := u * c₂ * c₃ with hw
  have hwR : w ∈ kuR T M := mul_mem (mul_mem hu hc₂R) hc₃R
  have hyw : y * w * y⁻¹ = c₂ * c₃ * u := by
    calc y * w * y⁻¹ = (y * u * y⁻¹) * (y * c₂ * y⁻¹) * (y * c₃ * y⁻¹) := by rw [hw]; group
      _ = c₂ * c₃ * u := by rw [hyc₃]
  have hcomm : y * w * y⁻¹ * w⁻¹ ∈ kuV2 T M := by
    have e : y * w * y⁻¹ * w⁻¹ = (c₂ * c₃) * u * (c₂ * c₃)⁻¹ * u⁻¹ := by
      rw [hyw, hw]; group
    rw [e]
    exact h.commutator_mem_kuV2 (mul_mem hc₂R hc₃R) hu
  have hwV : w ∈ pCoreOf 2 M := hg w hwR (hcomm.1)
  have hwV2 : w ∈ kuV2 T M := hf w hwV hcomm
  have hww : w * w = 1 := h.kuV2_sq hwV2
  have hwc₂ : w * c₂ = c₂ * w := h.kuV2_comm hwV2 hc₂R
  have hwu : w * u = u * w := h.kuV2_comm hwV2 hu
  have hc₃eq : c₃ = c₂ * u * w := by
    calc c₃ = (c₂ * c₂) * c₃ := by rw [hc₂₂, one_mul]
      _ = c₂ * ((u * u) * c₂ * c₃) := by rw [huu, one_mul, mul_assoc]
      _ = c₂ * u * w := by rw [hw]; group
  have hsq : c₂ * u * (c₂ * u) = 1 := by
    have h1 : (c₂ * u * w) * (c₂ * u * w) = c₂ * u * (c₂ * u) * (w * w) := by
      have hwcu : w * (c₂ * u) = (c₂ * u) * w := by
        calc w * (c₂ * u) = (w * c₂) * u := by group
          _ = (c₂ * w) * u := by rw [hwc₂]
          _ = c₂ * (w * u) := by group
          _ = c₂ * (u * w) := by rw [hwu]
          _ = (c₂ * u) * w := by group
      calc (c₂ * u * w) * (c₂ * u * w) = (c₂ * u) * (w * (c₂ * u)) * w := by group
        _ = (c₂ * u) * ((c₂ * u) * w) * w := by rw [hwcu]
        _ = c₂ * u * (c₂ * u) * (w * w) := by group
    rw [← hc₃eq, hc₃₃, hww, mul_one] at h1
    exact h1.symm
  have hinv : (c₂ * u)⁻¹ = c₂ * u := inv_eq_of_mul_eq_one_right hsq
  rw [mul_inv_rev, hui, hc₂i] at hinv
  exact hinv

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
