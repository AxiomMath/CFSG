module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Graph
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4CGlue

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
  CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
open scoped MatrixGroups commutatorElement

section NoGraph

variable {F : Type} [Field F]

theorem no_graph_of_maps_radP (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hmem : ∀ a b : F, ∃ a' b' : F,
      (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (elP a b)) = proj 3 F (elP a' b')) :
    False := by
  obtain ⟨a₁, b₁, h₁⟩ := hmem 1 0
  obtain ⟨a₂, b₂, h₂⟩ := hmem 0 1
  rw [apply_ε1] at h₁ h₂
  simp only [map_one, map_zero, neg_zero] at h₁ h₂
  obtain ⟨c₁, hc₁⟩ := exists_scalar_of_proj_eq A _ _ _ _ h₁
  obtain ⟨c₂, hc₂⟩ := exists_scalar_of_proj_eq A _ _ _ _ h₂
  have hd := det_eq_zero_of_scalar_instances (A : Matrix (Fin 3) (Fin 3) F) c₁ c₂ _ _ _ _ hc₁ hc₂
  exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero hd

theorem dual_mul_conj_field (A : GL (Fin 3) F) (σ : F ≃+* F) :
    dualAut 3 F * (conjAut 3 F A * fieldAut 3 F σ) =
      (conjAut 3 F (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 F σ) * dualAut 3 F := by
  have htrans := standard_automorphism_transport (K := F) (n := 3)
  have hδ : dualAut 3 F * dualAut 3 F = 1 := htrans.2.2.2.1
  have h5 := htrans.2.2.2.2.1 A
  have h6 := htrans.2.2.2.2.2.1 σ
  calc dualAut 3 F * (conjAut 3 F A * fieldAut 3 F σ)
      = dualAut 3 F * conjAut 3 F A * (dualAut 3 F * dualAut 3 F) * fieldAut 3 F σ *
          (dualAut 3 F * dualAut 3 F) := by rw [hδ]; group
    _ = (dualAut 3 F * conjAut 3 F A * dualAut 3 F) * (dualAut 3 F * fieldAut 3 F σ * dualAut 3 F) *
          dualAut 3 F := by group
    _ = (conjAut 3 F (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 F σ) * dualAut 3 F := by
        rw [h5, h6]

theorem no_graph_of_maps_radM (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hmem : ∀ a b : F, ∃ a' b' : F,
      (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (elM a b)) = proj 3 F (elM a' b')) :
    False := by
  have hδ : dualAut 3 F * dualAut 3 F = 1 :=
    (standard_automorphism_transport (K := F) (n := 3)).2.2.2.1
  refine no_graph_of_maps_radP (GeneralLinearGroup.inverseTranspose A) σ (fun a b => ?_)
  obtain ⟨a', b', h⟩ := hmem (-a) (-b)
  refine ⟨-a', -b', ?_⟩
  have e1 : conjAut 3 F (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 F σ * dualAut 3 F =
      dualAut 3 F * (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) * dualAut 3 F := by
    calc conjAut 3 F (GeneralLinearGroup.inverseTranspose A) * fieldAut 3 F σ * dualAut 3 F
        = dualAut 3 F * (conjAut 3 F A * fieldAut 3 F σ) := (dual_mul_conj_field A σ).symm
      _ = dualAut 3 F * (conjAut 3 F A * fieldAut 3 F σ) * (dualAut 3 F * dualAut 3 F) := by
          rw [hδ, mul_one]
      _ = _ := by group
  rw [e1, MulAut.mul_apply, MulAut.mul_apply, dual_elP, h, dual_elM]

end NoGraph

section Centralizer

variable {Y : Type} [Group Y]

theorem odd_orderOf_of_no_involution [Finite Y] {K : Subgroup Y}
    (hno : ∀ c : Y, orderOf c = 2 → c ∈ centralizer (K : Set Y) → False) {c : Y}
    (hc : c ∈ centralizer (K : Set Y)) : Odd (orderOf c) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨m, hm⟩ := hodd
  have hpos : 0 < orderOf c := orderOf_pos c
  have hm0 : m ≠ 0 := by omega
  have h1 : orderOf (c ^ m) = 2 := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hm]; exact ⟨2, by ring⟩), hm, ← two_mul,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  exact hno (c ^ m) h1 (pow_mem hc m)

theorem mem_of_sq_mem_of_odd_orderOf {K : Subgroup Y} {c : Y} (hodd : Odd (orderOf c))
    (hc2 : c ^ 2 ∈ K) : c ∈ K := by
  obtain ⟨m, hm⟩ := hodd
  have h1 : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
  have h2 : c = (c ^ 2) ^ (m + 1) := by
    calc c = c * c ^ (2 * m + 1) := by rw [h1, mul_one]
      _ = c ^ (2 * (m + 1)) := by rw [← pow_succ']; ring_nf
      _ = (c ^ 2) ^ (m + 1) := by rw [pow_mul]
  rw [h2]
  exact pow_mem hc2 _

theorem p47_mem_K_of_conj [Finite Y] {K : Subgroup Y} [K.Normal] (hK : IsComponent K)
    (hno : ∀ c : Y, orderOf c = 2 → c ∈ centralizer (K : Set Y) → False) {e : Y}
    (he2 : e * e = 1) {θ : MulAut ↥K} (hθ : ∀ x : ↥K, ((θ x : ↥K) : Y) = e * (x : Y) * e⁻¹)
    {k₀ : ↥K} (h : ∀ x : ↥K, θ x * (k₀ * x * k₀⁻¹)⁻¹ ∈ Subgroup.center ↥K) : e ∈ K := by
  have hcomm : ∀ j ∈ K, ⁅(k₀ : Y)⁻¹ * e, j⁆ ∈ centralizer (K : Set Y) := by
    intro j hj
    have hw := h ⟨j, hj⟩
    set w : ↥K := θ ⟨j, hj⟩ * (k₀ * ⟨j, hj⟩ * k₀⁻¹)⁻¹ with hwdef
    have hwY : (w : Y) = e * j * e⁻¹ * (k₀ * j * (k₀ : Y)⁻¹)⁻¹ := by
      rw [hwdef, Subgroup.coe_mul, hθ]
      simp
    have hk0w : (k₀ : Y)⁻¹ * (w : Y) * k₀ = (w : Y) := by
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw k₀)
      simp only [Subgroup.coe_mul] at this
      rw [mul_assoc, ← this]
      group
    have hcom : ⁅(k₀ : Y)⁻¹ * e, j⁆ = (k₀ : Y)⁻¹ * (w : Y) * k₀ := by
      rw [hwY, commutatorElement_def]
      group
    rw [hcom, hk0w, Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨g, hg⟩)
  have hn : (k₀ : Y)⁻¹ * e ∈ normalizer (K : Set Y) :=
    Subgroup.normalizer_eq_top_iff.2 ‹K.Normal› ▸ Subgroup.mem_top _
  have hc : (k₀ : Y)⁻¹ * e ∈ centralizer (K : Set Y) := centralizes_of_comm_central hK hn hcomm
  set c : Y := (k₀ : Y)⁻¹ * e with hcdef
  have he : e = (k₀ : Y) * c := by rw [hcdef]; group
  have hck : (k₀ : Y) * c = c * k₀ := Subgroup.mem_centralizer_iff.1 hc k₀ k₀.2
  have hsq : (k₀ : Y) * k₀ * (c * c) = 1 := by
    calc (k₀ : Y) * k₀ * (c * c) = (k₀ : Y) * (k₀ * c) * c := by group
      _ = (k₀ : Y) * (c * k₀) * c := by rw [hck]
      _ = ((k₀ : Y) * c) * ((k₀ : Y) * c) := by group
      _ = e * e := by rw [← he]
      _ = 1 := he2
  have hc2 : c ^ 2 ∈ K := by
    have : c ^ 2 = ((k₀ : Y) * k₀)⁻¹ := by
      rw [sq]
      exact eq_inv_of_mul_eq_one_right hsq
    rw [this]
    exact K.inv_mem (K.mul_mem k₀.2 k₀.2)
  have hcK : c ∈ K := mem_of_sq_mem_of_odd_orderOf (odd_orderOf_of_no_involution hno hc) hc2
  rw [he]
  exact K.mul_mem k₀.2 hcK

end Centralizer

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
