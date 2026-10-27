module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23T

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

open A44

def zs4 : List (ZMod 4) := [0, 1, 2, 3]

def allM4 : List M4 :=
  zs4.flatMap fun a => zs4.flatMap fun b => zs4.flatMap fun c => zs4.map fun d => ⟨a, b, c, d⟩

def closedB (l : List M4) : Bool :=
  l.all (fun x => decide x.IsInv) && l.contains M4.one &&
    l.all (fun x => l.all fun y => l.contains (M4.mul x y)) && l.all (fun x => l.contains x.inv)

def vclassB : Bool :=
  ord3list.all fun ξ => allM4.all fun v =>
    !(decide v.IsInv) || decide (v = M4.one) ||
    decide (M4.conj ξ v = v) || decide (M4.conj ξ (M4.conj ξ v) = v) ||
    decide (M4.conj ξ (M4.conj ξ v) = M4.conj ξ v) ||
    !(closedB [M4.one, v, M4.conj ξ v, M4.conj ξ (M4.conj ξ v)]) || V4list.contains v

theorem vclassB_true : vclassB = true := by decide +kernel

theorem mem_allM4 : ∀ v : M4, v ∈ allM4 := by decide +kernel

theorem closedB_of (l : List M4) (h : ClosedList l) : closedB l = true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [closedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem]
  exact ⟨⟨⟨h1, h2⟩, fun x hx y hy => h3 x hx y hy⟩, fun x hx => h4 x hx⟩

theorem vclass (ξ v : M4) (hξ : ξ ∈ ord3list) (hv : v.IsInv) (h1 : v ≠ M4.one)
    (h2 : M4.conj ξ v ≠ v) (h3 : M4.conj ξ (M4.conj ξ v) ≠ v)
    (h4 : M4.conj ξ (M4.conj ξ v) ≠ M4.conj ξ v)
    (h5 : ClosedList [M4.one, v, M4.conj ξ v, M4.conj ξ (M4.conj ξ v)]) : v ∈ V4list := by
  have h := vclassB_true
  simp only [vclassB, List.all_eq_true] at h
  have h' := h ξ hξ v (mem_allM4 v)
  have h6 := closedB_of _ h5
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    List.contains_iff_mem] at h'
  rcases h' with (((((h' | h') | h') | h') | h') | h') | h'
  · exact absurd hv h'
  · exact absurd h' h1
  · exact absurd h' h2
  · exact absurd h' h3
  · exact absurd h' h4
  · rw [h6] at h'; exact absurd h' (by simp)
  · exact h'

theorem subgroup_card_four {G : Type} [Group G] (H : Subgroup G) (hH : Nat.card H = 4)
    (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (h1a : 1 ≠ a) (h1b : 1 ≠ b)
    (h1c : 1 ≠ c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ w ∈ H, w = 1 ∨ w = a ∨ w = b ∨ w = c := by
  classical
  have hcard : ({1, a, b, c} : Finset G).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h1a, h1b, h1c]),
      Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  have hsub : (({1, a, b, c} : Finset G) : Set G) ⊆ (H : Set G) := by
    intro w hw
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact ha
    · exact hb
    · exact hc
  have hT : (H : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hH
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [hH]; norm_num)
  have hfin : (H : Set G).Finite := Set.toFinite _
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hT, Set.ncard_coe_finset, hcard]) hfin
  intro w hw
  have : w ∈ (({1, a, b, c} : Finset G) : Set G) := by rw [heq]; exact hw
  simpa using this

theorem orbit_decomp {G : Type} [Group G] (R : Subgroup G) (hR : Nat.card R = 4) (ξ : G)
    (hξ : ξ * ξ * ξ = 1) (hconj : ∀ v ∈ R, ξ * v * ξ⁻¹ ∈ R)
    (hfpf : ∀ v ∈ R, ξ * v * ξ⁻¹ = v → v = 1) (v : G) (hv : v ∈ R) (hv1 : v ≠ 1) :
    ξ * v * ξ⁻¹ ≠ v ∧ ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ≠ ξ * v * ξ⁻¹ ∧ ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ≠ v ∧
      ∀ w ∈ R, w = 1 ∨ w = v ∨ w = ξ * v * ξ⁻¹ ∨ w = ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ := by
  have hm1 : ξ * v * ξ⁻¹ ∈ R := hconj v hv
  have hm2 : ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ∈ R := hconj _ hm1
  have n1 : ξ * v * ξ⁻¹ ≠ 1 := fun h => hv1 (conj_eq_one_iff.mp h)
  have n2 : ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ≠ 1 := fun h => n1 (conj_eq_one_iff.mp h)
  have d1 : ξ * v * ξ⁻¹ ≠ v := fun h => hv1 (hfpf v hv h)
  have d2 : ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ≠ ξ * v * ξ⁻¹ := fun h => n1 (hfpf _ hm1 h)
  have d3 : ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ≠ v := by
    intro h
    apply d1
    have e : ξ * (ξ * (ξ * v * ξ⁻¹) * ξ⁻¹) * ξ⁻¹ = (ξ * ξ * ξ) * v * (ξ * ξ * ξ)⁻¹ := by group
    rw [h, hξ, one_mul, inv_one, mul_one] at e
    exact e
  refine ⟨d1, d2, d3, ?_⟩
  exact subgroup_card_four R hR v (ξ * v * ξ⁻¹) (ξ * (ξ * v * ξ⁻¹) * ξ⁻¹) hv hm1 hm2
    (Ne.symm hv1) (Ne.symm n1) (Ne.symm n2) (Ne.symm d1) (Ne.symm d3) (Ne.symm d2)

theorem closedList_of_decomp (R : Subgroup G96) (ξ v : G96) (hv : v ∈ R)
    (hm1 : ξ * v * ξ⁻¹ ∈ R) (hm2 : ξ * (ξ * v * ξ⁻¹) * ξ⁻¹ ∈ R)
    (hall : ∀ w ∈ R, w = 1 ∨ w = v ∨ w = ξ * v * ξ⁻¹ ∨ w = ξ * (ξ * v * ξ⁻¹) * ξ⁻¹) :
    ClosedList [M4.one, v.1, M4.conj ξ.1 v.1, M4.conj ξ.1 (M4.conj ξ.1 v.1)] := by
  have hl : ∀ y ∈ [M4.one, v.1, M4.conj ξ.1 v.1, M4.conj ξ.1 (M4.conj ξ.1 v.1)],
      ∃ a ∈ R, a.1 = y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨1, R.one_mem, rfl⟩
    · exact ⟨v, hv, rfl⟩
    · exact ⟨_, hm1, rfl⟩
    · exact ⟨_, hm2, rfl⟩
  have hr : ∀ a ∈ R, a.1 ∈ [M4.one, v.1, M4.conj ξ.1 v.1, M4.conj ξ.1 (M4.conj ξ.1 v.1)] := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hall a ha with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, -, rfl⟩ := hl y hy
    exact a.2
  · simp
  · intro y hy z hz
    obtain ⟨a, ha, rfl⟩ := hl y hy
    obtain ⟨b, hb, rfl⟩ := hl z hz
    exact hr (a * b) (R.mul_mem ha hb)
  · intro y hy
    obtain ⟨a, ha, rfl⟩ := hl y hy
    exact hr a⁻¹ (R.inv_mem ha)

section Vlem

variable {T : Type} [Group T] [Finite T] (A : Subgroup T) [A.Normal] (θ : A ≃* Z4Z4)
  (x : MulAut T) (hA : ∀ a ∈ A, x a ∈ A)

include hA

theorem rho_mem_V4list (hx : x ^ 3 = 1) (hfix : ∀ g : T, x g = g → g = 1)
    (hC : Subgroup.centralizer (A : Set T) = A) (hT : Nat.card T = 64) (hA16 : Nat.card A = 16)
    (t : T) : (rhoHom A θ t).1 ∈ V4list := by
  have hR4 : Nat.card (rhoHom A θ).range = 4 := card_range_rho A θ hC hT hA16
  have hξ3 : xi A θ x hA * xi A θ x hA * xi A θ x hA = 1 := by
    rw [← pow_three']; exact xi_pow_three A θ x hA hx
  have hconj : ∀ v ∈ (rhoHom A θ).range,
      xi A θ x hA * v * (xi A θ x hA)⁻¹ ∈ (rhoHom A θ).range := by
    rintro v ⟨s, rfl⟩
    exact ⟨x s, rho_x A θ x hA s⟩
  have hfpf : ∀ v ∈ (rhoHom A θ).range,
      xi A θ x hA * v * (xi A θ x hA)⁻¹ = v → v = 1 := by
    rintro v ⟨s, rfl⟩ h
    exact xi_fpf A θ x hA hx hfix hC hA16 s h
  by_cases h1 : rhoHom A θ t = 1
  · rw [h1]
    exact (by decide : M4.one ∈ V4list)
  · obtain ⟨d1, d2, d3, hall⟩ := orbit_decomp (rhoHom A θ).range hR4 (xi A θ x hA) hξ3 hconj hfpf
      (rhoHom A θ t) ⟨t, rfl⟩ h1
    exact vclass (xi A θ x hA).1 (rhoHom A θ t).1 (xi_mem_ord3 A θ x hA hx hfix) (rhoHom A θ t).2
      (fun h => h1 (Subtype.ext h)) (fun h => d1 (Subtype.ext h)) (fun h => d3 (Subtype.ext h))
      (fun h => d2 (Subtype.ext h))
      (closedList_of_decomp (rhoHom A θ).range (xi A θ x hA) (rhoHom A θ t) ⟨t, rfl⟩
        (hconj _ ⟨t, rfl⟩) (hconj _ (hconj _ ⟨t, rfl⟩)) hall)

theorem V4list_subset_range (hx : x ^ 3 = 1) (hfix : ∀ g : T, x g = g → g = 1)
    (hC : Subgroup.centralizer (A : Set T) = A) (hT : Nat.card T = 64) (hA16 : Nat.card A = 16) :
    ∀ m ∈ V4list, ∃ t : T, (rhoHom A θ t).1 = m := by
  classical
  have hR4 : Nat.card (rhoHom A θ).range = 4 := card_range_rho A θ hC hT hA16
  have : Fintype (rhoHom A θ).range := Fintype.ofFinite _
  let F : (rhoHom A θ).range → M4 := fun r => r.1.1
  have hFinj : Function.Injective F := fun r s h => Subtype.ext (Subtype.ext h)
  have hcardImg : (Finset.univ.image F).card = 4 := by
    rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, ← Nat.card_eq_fintype_card,
      hR4]
  have hsub : Finset.univ.image F ⊆ V4list.toFinset := by
    intro m hm
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨t, ht⟩ := r.2
    rw [List.mem_toFinset]
    show r.1.1 ∈ V4list
    rw [← ht]
    exact rho_mem_V4list A θ x hA hx hfix hC hT hA16 t
  have hV4card : V4list.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup (by decide)]; rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardImg, hV4card])
  intro m hm
  have hm' : m ∈ Finset.univ.image F := by rw [heq]; exact List.mem_toFinset.mpr hm
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hm'
  obtain ⟨t, ht⟩ := r.2
  exact ⟨t, by rw [ht]; exact hr⟩

end Vlem

end L23

end CFSG.GH74.GLS.Bg.TwoGroups
