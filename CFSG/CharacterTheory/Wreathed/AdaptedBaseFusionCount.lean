module

public import CFSG.CharacterTheory.Wreathed.AdaptedBaseFusionOrbits

public noncomputable section

namespace CFSG.Wreathed.AdaptedBaseFusion

open CFSG.Wreathed CFSG.Wreathed.BrauerWong

universe u

variable {G : Type u} [Group G] [Finite G] {n : ℕ} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
  {σ υ g : G}
  (h : IsAdaptedBase (modelBase S e) (wreathModelHom S e (Original.a (2 ^ n)))
    (wreathModelHom S e (Original.z (2 ^ n))) σ υ g)
include h

omit [Finite G] in
theorem not_mem_exc_of_mem_closure {φ : MulAut (modelBase S e)}
    (hφ : φ ∈ Subgroup.closure {swapAut S e, h.aut}) {x : modelBase S e} (hx : x ∉ h.exc) :
    φ x ∉ h.exc := by
  intro hφx
  apply hx
  have h' := mem_exc_of_mem_closure h (Subgroup.inv_mem _ hφ) hφx
  rwa [MulAut.inv_apply_self] at h'

theorem ncard_orbit_of_not_mem_exc (hn : 2 ≤ n) {x : modelBase S e} (hxE : x ∉ h.exc) :
    (MulAction.orbit (Subgroup.closure {swapAut S e, h.aut}) x).ncard = 6 := by
  rw [← MulAction.index_stabilizer]
  have hstab : MulAction.stabilizer (Subgroup.closure {swapAut S e, h.aut}) x = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [MulAction.mem_stabilizer_iff] at hφ
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_fixed_of_not_mem_exc h hn φ.2 hxE hφ)
  rw [hstab, Subgroup.index_bot, card_closure h (by omega)]

theorem ncard_exc : h.exc.ncard = 3 * 2 ^ n - 2 := by
  have hcard : ∀ y : modelBase S e, orderOf y = 2 ^ n →
      (Subgroup.zpowers y : Set (modelBase S e)).ncard = 2 ^ n := by
    intro y hy
    rw [← Nat.card_coe_set_eq]
    change Nat.card (Subgroup.zpowers y) = _
    rw [Nat.card_zpowers, hy]
  have hinter : ∀ K L : Subgroup (modelBase S e), K ⊓ L = ⊥ →
      (K : Set (modelBase S e)) ∩ L = {1} := by
    intro K L hKL
    rw [← Subgroup.coe_inf, hKL, Subgroup.coe_bot]
  have hA := hcard _ (orderOf_mul' h)
  have hB := hcard _ (orderOf_left' h)
  have hC := hcard _ (orderOf_right' h)
  have hAB := hinter _ _ (zpowers_mul_inf_left h)
  have hAC := hinter _ _ (zpowers_mul_inf_right h)
  have hBC := hinter _ _ (zpowers_left_inf_right' h)
  have h1 := Set.ncard_union_add_ncard_inter (Subgroup.zpowers (h.left * h.right) :
    Set (modelBase S e)) (Subgroup.zpowers h.left)
  have h2 := Set.ncard_union_add_ncard_inter ((Subgroup.zpowers (h.left * h.right) :
    Set (modelBase S e)) ∪ Subgroup.zpowers h.left) (Subgroup.zpowers h.right)
  rw [hAB, Set.ncard_singleton, hA, hB] at h1
  rw [Set.union_inter_distrib_right, hAC, hBC, Set.union_self, Set.ncard_singleton, hC] at h2
  change ((Subgroup.zpowers (h.left * h.right) : Set (modelBase S e)) ∪
    Subgroup.zpowers h.left ∪ Subgroup.zpowers h.right).ncard = _
  omega

omit h in
theorem eq_mul_of_add_eq_sq {m c : ℕ} (hm : 2 ≤ m) (h1 : 3 * m - 2 + c = m ^ 2) :
    c = (m - 1) * (m - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  rw [show 3 * (k + 2) - 2 = 3 * k + 4 by omega] at h1
  ring_nf at h1 ⊢
  linarith

theorem ncard_compl_exc (hn : 2 ≤ n) : h.excᶜ.ncard = (2 ^ n - 1) * (2 ^ n - 2) := by
  have h1 := Set.ncard_add_ncard_compl h.exc
  rw [ncard_exc h, card_modelBase] at h1
  have hm : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact eq_mul_of_add_eq_sq hm h1

theorem ncard_orbits_compl_exc (hn : 2 ≤ n) :
    ((fun x => MulAction.orbit (Subgroup.closure {swapAut S e, h.aut}) x) '' h.excᶜ).ncard =
      (2 ^ n - 1) * (2 ^ n - 2) / 6 := by
  classical
  set H := Subgroup.closure {swapAut S e, h.aut}
  set o : modelBase S e → Set (modelBase S e) := fun x => MulAction.orbit H x
  have hfin : h.excᶜ.Finite := Set.toFinite _
  set s := hfin.toFinset with hs
  have hsum := Finset.card_eq_sum_card_image o s
  have hfib : ∀ b ∈ s.image o, (s.filter (fun x => o x = b)).card = 6 := by
    intro b hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hb
    have hx₀' : x₀ ∉ h.exc := by
      rw [hs, Set.Finite.mem_toFinset] at hx₀
      exact hx₀
    have hfilter : s.filter (fun x => o x = o x₀) = (Set.toFinite (o x₀)).toFinset := by
      ext x
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨_, hx⟩
        exact MulAction.orbit_eq_iff.mp hx
      · intro hx
        refine ⟨?_, MulAction.orbit_eq_iff.mpr hx⟩
        obtain ⟨φ, hφ, rfl⟩ := mem_orbit_iff_exists.mp hx
        exact not_mem_exc_of_mem_closure h hφ hx₀'
    rw [hfilter, ← Set.ncard_eq_toFinset_card _ _]
    exact ncard_orbit_of_not_mem_exc h hn hx₀'
  rw [Finset.sum_const_nat hfib] at hsum
  have hscard : s.card = (2 ^ n - 1) * (2 ^ n - 2) := by
    rw [hs, ← Set.ncard_eq_toFinset_card _ _, ncard_compl_exc h hn]
  have himage : ((fun x => MulAction.orbit H x) '' h.excᶜ).ncard = (s.image o).card := by
    rw [← Set.ncard_coe_finset, Finset.coe_image, hs, Set.Finite.coe_toFinset]
  rw [himage]
  omega

end CFSG.Wreathed.AdaptedBaseFusion
