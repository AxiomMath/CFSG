module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.Elementary
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.SignalizerPerm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

namespace IsTwoANine

variable {J : Type*} [Group J] (hJ : IsTwoANine J)
include hJ

theorem eq_bot_of_odd_of_le_normalizer {E Y : Subgroup J} (hE2 : ∀ x ∈ E, x ^ 2 = 1)
    (hE : Nat.card E = 16) (hY : Odd (Nat.card Y)) (hEY : E ≤ normalizer (Y : Set J)) :
    Y = ⊥ := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  obtain ⟨p, hp, -⟩ := hJ.existsUnique_forall_apply_eq_of_card_eq e hE2 hE
  have hbar : Y.map (proj e) = ⊥ := eq_bot_of_odd_of_regular_le_normalizer
    (fun _ hf => sq_eq_one_of_mem_map_proj e hE2 hf) hp
    (fun _ _ hi hj => hJ.existsUnique_mem_map_proj_apply_eq e hE2 hE hp hi hj)
    (Odd.of_dvd_nat hY (Subgroup.card_map_dvd Y (proj e)))
    ((Subgroup.map_mono hEY).trans (Subgroup.le_normalizer_map (proj e)))
  rw [Subgroup.map_eq_bot_iff, ker_proj] at hbar
  refine (Subgroup.eq_bot_iff_forall Y).mpr fun y hy => ?_
  rcases hJ.mem_center_iff.mp (hbar hy) with h | rfl
  · exact h
  · have hdvd := Subgroup.orderOf_dvd_natCard Y hy
    rw [hJ.orderOf_zbar] at hdvd
    exact absurd (even_iff_two_dvd.mpr hdvd) (Nat.not_even_iff_odd.mpr hY)

omit hJ in
private theorem sq_eq_one_of_mem_map_conj {E : Subgroup J} (hE2 : ∀ x ∈ E, x ^ 2 = 1) (g : J) :
    ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x ^ 2 = 1 := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_pow, hE2 y hy, map_one]

omit hJ in
private theorem card_map_conj (E : Subgroup J) (g : J) :
    Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem exists_le_sylow (T : Sylow 2 J) :
    ∃ E : Subgroup J, E ≤ T ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  have := hJ.finite
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  let T₀ : Sylow 2 J := aNineSylowSylow.comapOfKerIsPGroup (proj e) (hJ.isPGroup_ker_proj e)
    (by rw [MonoidHom.range_eq_top.mpr (proj_surjective e)]; exact le_top)
  have hT₀ : ANineEZero.comap (proj e) ≤ T₀ := Subgroup.comap_mono aNineEZero_le_aNineSylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq J T₀ T
  refine ⟨(ANineEZero.comap (proj e)).map (MulAut.conj g).toMonoidHom, ?_,
    sq_eq_one_of_mem_map_conj (fun x hx => hJ.sq_eq_one_of_mem_comap_aNineEZero e hx) g, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (T₀ : Subgroup J) (hT₀ hy)
  · rw [card_map_conj, hJ.card_comap_aNineEZero e]

theorem eq_bot_of_odd_of_sylow_le_normalizer (T : Sylow 2 J) {Y : Subgroup J}
    (hY : Odd (Nat.card Y)) (hTY : (T : Subgroup J) ≤ normalizer (Y : Set J)) : Y = ⊥ := by
  obtain ⟨E, hET, hE2, hE⟩ := hJ.exists_le_sylow T
  exact hJ.eq_bot_of_odd_of_le_normalizer hE2 hE hY (hET.trans hTY)

theorem exists_le_centralizer {s : J} (hs : orderOf s = 2) :
    ∃ E : Subgroup J, E ≤ centralizer {s} ∧ (∀ x ∈ E, x ^ 2 = 1) ∧ Nat.card E = 16 := by
  obtain ⟨e⟩ := hJ.nonempty_mulEquiv
  have hE2 := fun x (hx : x ∈ ANineEZero.comap (proj e)) =>
    hJ.sq_eq_one_of_mem_comap_aNineEZero e hx
  by_cases hsz : s = zbar J
  · refine ⟨ANineEZero.comap (proj e), fun x _ => ?_, hE2, hJ.card_comap_aNineEZero e⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hsz]
    exact (hJ.commute_zbar x).eq
  obtain ⟨x, hx⟩ := proj_surjective e aNineEGenX
  have hxE : x ∈ ANineEZero.comap (proj e) := by
    rw [Subgroup.mem_comap, hx]
    exact Subgroup.subset_closure (by simp)
  have hx1 : aNineEGenX ≠ 1 := fun h => by
    have h' := congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9))) h
    exact absurd h' (by decide)
  obtain ⟨hxo, hxc⟩ := hJ.orderOf_eq_two_of_cycleType_two_two_two_two e
    (by rw [hx]; exact cycleType_of_mem_aNineEZero (Subgroup.subset_closure (by simp)) hx1)
  have hxz : x ≠ zbar J := fun h => hxc (h ▸ hJ.zbar_mem_center)
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hJ.isConj_of_orderOf_eq_two hxo hs hxz hsz)
  refine ⟨(ANineEZero.comap (proj e)).map (MulAut.conj g).toMonoidHom, ?_,
    sq_eq_one_of_mem_map_conj hE2 g, by rw [card_map_conj, hJ.card_comap_aNineEZero e]⟩
  rintro _ ⟨y, hy, rfl⟩
  have hyx : y * x = x * y := (commute_of_sq_eq_one_of_mul_sq_eq_one (hE2 y hy) (hE2 x hxE)
    (hE2 _ (Subgroup.mul_mem _ hy hxE))).eq
  rw [Subgroup.mem_centralizer_singleton_iff]
  change g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc y, hyx, mul_assoc]

theorem eq_bot_of_odd_of_centralizer_le_normalizer {s : J} (hs : orderOf s = 2)
    {Y : Subgroup J} (hY : Odd (Nat.card Y)) (hsY : centralizer {s} ≤ normalizer (Y : Set J)) :
    Y = ⊥ := by
  obtain ⟨E, hEs, hE2, hE⟩ := hJ.exists_le_centralizer hs
  exact hJ.eq_bot_of_odd_of_le_normalizer hE2 hE hY (hEs.trans hsY)

end IsTwoANine

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
