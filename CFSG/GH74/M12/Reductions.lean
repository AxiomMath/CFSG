module

public import CFSG.GH74.M12.Statements
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.GH74.M12

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu
open scoped Pointwise

theorem exists_conj_mem_sylow_of_orderOf_two {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    {x : G} (hx : orderOf x = 2) : ∃ g : G, g * x * g⁻¹ ∈ P := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g⁻¹, ?_⟩
  have hxQ : x ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [← hg] at hxQ
  have h2 : x ∈ MulAut.conj g • (P : Subgroup G) := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def] at hxQ
    exact hxQ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : g⁻¹ * x * g ∈ (P : Subgroup G) := by
    simpa [MulAut.conj_inv_apply] using h2
  have h4 : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by simp
  rw [h4]
  exact h3

theorem orderOf_conj_mul_inv {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) x
  simpa using this

theorem twoInvolutionClasses_of_pattern {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (P : Sylow 2 G) (P' : Sylow 2 G') (φ : ↥P ≃* ↥P')
    (hconj : ∀ u v : ↥P, orderOf (u : G) = 2 → orderOf (v : G) = 2 →
      (IsConj (u : G) (v : G) ↔ IsConj ((φ u : ↥P') : G') ((φ v : ↥P') : G')))
    (a t : G') (ha : orderOf a = 2) (ht : orderOf t = 2) (hnc : ¬ IsConj a t) :
    TwoInvolutionClasses G := by
  obtain ⟨g₁, hg₁⟩ := exists_conj_mem_sylow_of_orderOf_two P' ha
  obtain ⟨g₂, hg₂⟩ := exists_conj_mem_sylow_of_orderOf_two P' ht
  obtain ⟨u, hu⟩ := φ.surjective ⟨g₁ * a * g₁⁻¹, hg₁⟩
  obtain ⟨v, hv⟩ := φ.surjective ⟨g₂ * t * g₂⁻¹, hg₂⟩
  have hc1 : IsConj (g₁ * a * g₁⁻¹) a := isConj_iff.2 ⟨g₁⁻¹, by simp [mul_assoc]⟩
  have hc2 : IsConj (g₂ * t * g₂⁻¹) t := isConj_iff.2 ⟨g₂⁻¹, by simp [mul_assoc]⟩
  have hou : orderOf (u : G) = 2 := by
    have e1 : orderOf ((φ u : ↥P') : G') = orderOf (u : G) := by
      calc orderOf ((φ u : ↥P') : G') = orderOf (φ u) := Subgroup.orderOf_coe (φ u)
        _ = orderOf u := MulEquiv.orderOf_eq φ u
        _ = orderOf (u : G) := (Subgroup.orderOf_coe u).symm
    rw [← e1, hu]
    exact (orderOf_conj_mul_inv g₁ a).trans ha
  have hov : orderOf (v : G) = 2 := by
    have e1 : orderOf ((φ v : ↥P') : G') = orderOf (v : G) := by
      calc orderOf ((φ v : ↥P') : G') = orderOf (φ v) := Subgroup.orderOf_coe (φ v)
        _ = orderOf v := MulEquiv.orderOf_eq φ v
        _ = orderOf (v : G) := (Subgroup.orderOf_coe v).symm
    rw [← e1, hv]
    exact (orderOf_conj_mul_inv g₂ t).trans ht
  refine ⟨(u : G), (v : G), hou, hov, fun hc => hnc ?_⟩
  have hc' := (hconj u v hou hov).1 hc
  rw [hu, hv] at hc'
  exact hc1.symm.trans (hc'.trans hc2)

instance : Finite M12Group := inferInstanceAs (Finite ↥NativeSporadic.M12)

def m12TPerm : Equiv.Perm (Fin 12) :=
  (m12gA * m12gB * m12gA * m12gB * m12gA * m12gB⁻¹) ^ 3

theorem m12TPerm_mem : m12TPerm ∈ NativeSporadic.M12 := by
  rw [m12_eq]
  have ha : m12gA ∈ Subgroup.closure ({m12gA, m12gB} : Set (Equiv.Perm (Fin 12))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : m12gB ∈ Subgroup.closure ({m12gA, m12gB} : Set (Equiv.Perm (Fin 12))) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  unfold m12TPerm
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha) hb) ha) (Subgroup.inv_mem _ hb)) 3

def m12InvA : M12Group := m12a

def m12InvT : M12Group := (⟨m12TPerm, m12TPerm_mem⟩ : ↥NativeSporadic.M12)

theorem m12gA_sq : m12gA ^ 2 = 1 := by decide +kernel

theorem m12TPerm_sq : m12TPerm ^ 2 = 1 := by decide +kernel

theorem m12gA_support : m12gA.support.card = 8 := by decide +kernel

theorem m12TPerm_support : m12TPerm.support.card = 12 := by decide +kernel

theorem m12InvA_sq : m12InvA ^ 2 = 1 := by
  apply Subtype.ext
  exact m12gA_sq

theorem m12InvT_sq : m12InvT ^ 2 = 1 := by
  apply Subtype.ext
  exact m12TPerm_sq

theorem orderOf_m12InvA : orderOf m12InvA = 2 := by
  apply orderOf_eq_prime m12InvA_sq
  intro h
  have h1 : (m12InvA : ↥NativeSporadic.M12).1 = (1 : ↥NativeSporadic.M12).1 :=
    congrArg Subtype.val h
  have h2 : m12gA = 1 := h1
  have h3 := congrArg (fun y : Equiv.Perm (Fin 12) => y.support.card) h2
  simp only [Equiv.Perm.support_one, Finset.card_empty] at h3
  rw [m12gA_support] at h3
  omega

theorem orderOf_m12InvT : orderOf m12InvT = 2 := by
  apply orderOf_eq_prime m12InvT_sq
  intro h
  have h1 : (m12InvT : ↥NativeSporadic.M12).1 = (1 : ↥NativeSporadic.M12).1 :=
    congrArg Subtype.val h
  have h2 : m12TPerm = 1 := h1
  have h3 := congrArg (fun y : Equiv.Perm (Fin 12) => y.support.card) h2
  simp only [Equiv.Perm.support_one, Finset.card_empty] at h3
  rw [m12TPerm_support] at h3
  omega

theorem not_isConj_m12InvA_m12InvT : ¬ IsConj m12InvA m12InvT := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h1 : (c * m12InvA * c⁻¹ : ↥NativeSporadic.M12).1 = (m12InvT : ↥NativeSporadic.M12).1 :=
    congrArg Subtype.val hc
  have h2 : (Subtype.val c : Equiv.Perm (Fin 12)) * m12gA * (Subtype.val c : Equiv.Perm (Fin 12))⁻¹
      = m12TPerm := h1
  have h3 := congrArg (fun y : Equiv.Perm (Fin 12) => y.support.card) h2
  simp only [Equiv.Perm.card_support_conj] at h3
  rw [m12gA_support, m12TPerm_support] at h3
  omega

theorem s_gls_of_s_brauerFong (h : S_BrauerFong) : S_GLS_16_1_M12 := by
  intro G _ _ hsimple hpat
  obtain ⟨P, P', φ, hconj, -⟩ := hpat
  exact h G hsimple ⟨P, P', ⟨φ⟩⟩
    (twoInvolutionClasses_of_pattern P P' φ hconj m12InvA m12InvT orderOf_m12InvA
      orderOf_m12InvT not_isConj_m12InvA_m12InvT)

theorem s_m12_core_of_s_asc03_simple (h : S_Asc03_simple) : S_M12_core := by
  intro G _ _ hsimple _ z hz hK
  exact h G hsimple z hz hK

theorem s_gls_of_core (hloc : S_T2_local) (hord : S_T2_order) (hcore : S_M12_core) :
    S_GLS_16_1_M12 := by
  intro G _ _ hsimple hpat
  obtain ⟨z, -, hz, hK⟩ := hloc G hsimple hpat
  exact hcore G hsimple (hord G hsimple hpat) z hz hK

end CFSG.GH74.M12
