module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

theorem commute_of_sq_eq_one_of_mul_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) : Commute a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← sq, ha])
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rw [← sq, hb])
  have h : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left (by rw [← sq, hab])
  rw [mul_inv_rev, ha', hb'] at h
  exact h.symm

theorem eq_of_apply_eq_of_cycleType_two_two_two_two {σ : Perm (Fin 9)}
    (hσ : σ.cycleType = {2, 2, 2, 2}) {i j : Fin 9} (hi : σ i = i) (hj : σ j = j) : i = j := by
  by_contra hij
  have h8 : σ.support.card = 8 := by
    rw [← Perm.sum_cycleType, hσ]
    rfl
  have hsub : σ.support ⊆ (Finset.univ.erase i).erase j := by
    intro k hk
    rw [Perm.mem_support] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => hk (h ▸ hj), fun h => hk (h ▸ hi)⟩
  have h7 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp [Ne.symm hij]), Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h7
  omega

theorem exists_forall_apply_eq_of_isPGroup {F : Subgroup (alternatingGroup (Fin 9))}
    (hF : IsPGroup 2 F) : ∃ p : Fin 9, ∀ g ∈ F, (g : Perm (Fin 9)) p = p := by
  obtain ⟨p, hp⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card (Fin 9)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  exact ⟨p, fun g hg => (MulAction.mem_fixedPoints.mp hp) ⟨g, hg⟩⟩

section CycleType

variable {F : Subgroup (alternatingGroup (Fin 9))}
  (hF : ∀ g ∈ F, g ≠ 1 → (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2})
include hF

theorem eq_one_of_apply_eq_of_apply_eq {g : alternatingGroup (Fin 9)} (hg : g ∈ F) {i j : Fin 9}
    (hij : i ≠ j) (hi : (g : Perm (Fin 9)) i = i) (hj : (g : Perm (Fin 9)) j = j) : g = 1 := by
  by_contra h1
  exact hij (eq_of_apply_eq_of_cycleType_two_two_two_two (hF g hg h1) hi hj)

variable {p : Fin 9} (hp : ∀ g ∈ F, (g : Perm (Fin 9)) p = p)
include hp

omit hF in
theorem apply_ne_of_forall_apply_eq {g : alternatingGroup (Fin 9)} (hg : g ∈ F) {i : Fin 9}
    (hi : i ≠ p) : (g : Perm (Fin 9)) i ≠ p := fun h =>
  hi ((g : Perm (Fin 9)).injective (h.trans (hp g hg).symm))

theorem eq_of_mem_of_apply_eq {i : Fin 9} (hi : i ≠ p) {g h : alternatingGroup (Fin 9)}
    (hg : g ∈ F) (hh : h ∈ F) (hgh : (g : Perm (Fin 9)) i = (h : Perm (Fin 9)) i) : g = h := by
  have hmem : h⁻¹ * g ∈ F := F.mul_mem (F.inv_mem hh) hg
  have key : ∀ k, (g : Perm (Fin 9)) k = (h : Perm (Fin 9)) k →
      ((h⁻¹ * g : alternatingGroup (Fin 9)) : Perm (Fin 9)) k = k := fun k hk => by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hk]
    exact Perm.inv_eq_iff_eq.mpr rfl
  have h1 := eq_one_of_apply_eq_of_apply_eq hF hmem hi (key i hgh)
    (key p ((hp g hg).trans (hp h hh).symm))
  rw [inv_mul_eq_one] at h1
  exact h1.symm

private def evalAt {i : Fin 9} (hi : i ≠ p) : F → {j : Fin 9 // j ≠ p} :=
  fun g => ⟨(g : Perm (Fin 9)) i, apply_ne_of_forall_apply_eq hp g.2 hi⟩

omit hF in
private theorem evalAt_apply {i : Fin 9} (hi : i ≠ p) (g : F) :
    (evalAt hp hi g : Fin 9) = ((g : alternatingGroup (Fin 9)) : Perm (Fin 9)) i :=
  rfl

private theorem evalAt_injective {i : Fin 9} (hi : i ≠ p) : Function.Injective (evalAt hp hi) :=
  fun g h hgh => Subtype.ext (eq_of_mem_of_apply_eq hF hp hi g.2 h.2 (congrArg Subtype.val hgh))

omit hF hp in
private theorem card_ne_lt (p : Fin 9) : Nat.card {j : Fin 9 // j ≠ p} < 9 := by
  have h := Finite.card_subtype_lt (p := fun j : Fin 9 => j ≠ p) (x := p) (fun h => h rfl)
  rwa [Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin] at h

theorem existsUnique_mem_apply_eq_of_cycleType (h8 : Nat.card F = 8) {i j : Fin 9} (hi : i ≠ p)
    (hj : j ≠ p) : ∃! g, g ∈ F ∧ (g : Perm (Fin 9)) i = j := by
  have hinj := evalAt_injective hF hp hi
  have hle := Nat.card_le_card_of_injective _ hinj
  have hbij := (Nat.bijective_iff_injective_and_card (evalAt hp hi)).mpr
    ⟨hinj, by have := card_ne_lt p; omega⟩
  obtain ⟨g, hg⟩ := hbij.2 ⟨j, hj⟩
  have hgj : ((g : alternatingGroup (Fin 9)) : Perm (Fin 9)) i = j := by
    rw [← evalAt_apply hp hi, hg]
  exact ⟨g, ⟨g.2, hgj⟩, fun h ⟨hh, hhj⟩ =>
    eq_of_mem_of_apply_eq hF hp hi hh g.2 (hhj.trans hgj.symm)⟩

end CycleType

variable {F : Subgroup (alternatingGroup (Fin 9))}

theorem card_le_eight_of_cycleType (hF2 : IsPGroup 2 F)
    (hF : ∀ g ∈ F, g ≠ 1 → (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) : Nat.card F ≤ 8 := by
  obtain ⟨p, hp⟩ := exists_forall_apply_eq_of_isPGroup hF2
  obtain ⟨i, hi⟩ := exists_ne p
  have := Nat.card_le_card_of_injective _ (evalAt_injective hF hp hi)
  have := card_ne_lt p
  omega

theorem existsUnique_forall_apply_eq_of_cycleType (h8 : Nat.card F = 8)
    (hF : ∀ g ∈ F, g ≠ 1 → (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) :
    ∃! p : Fin 9, ∀ g ∈ F, (g : Perm (Fin 9)) p = p := by
  obtain ⟨p, hp⟩ := exists_forall_apply_eq_of_isPGroup (IsPGroup.of_card (n := 3) h8)
  refine ⟨p, hp, fun q hq => ?_⟩
  by_contra hqp
  have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr fun g hg =>
    eq_one_of_apply_eq_of_apply_eq hF hg hqp (hq g hg) (hp g hg)
  rw [hbot, Subgroup.card_bot] at h8
  exact absurd h8 (by norm_num)

theorem centralizer_eq_self_of_cycleType (hF2 : ∀ g ∈ F, g ^ 2 = 1) (h8 : Nat.card F = 8)
    (hF : ∀ g ∈ F, g ≠ 1 → (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2}) :
    Subgroup.centralizer (F : Set (alternatingGroup (Fin 9))) = F := by
  have hcomm : ∀ g ∈ F, ∀ h ∈ F, g * h = h * g := fun g hg h hh =>
    (commute_of_sq_eq_one_of_mul_sq_eq_one (hF2 g hg) (hF2 h hh) (hF2 _ (F.mul_mem hg hh))).eq
  refine le_antisymm (fun c hc => ?_) fun g hg => Subgroup.mem_centralizer_iff.mpr
    fun h hh => hcomm h hh g hg
  have hc' : ∀ h ∈ F, (h : Perm (Fin 9)) * c = (c : Perm (Fin 9)) * h := fun h hh => by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subgroup.mem_centralizer_iff.mp hc h hh]
  obtain ⟨p, hp, hpu⟩ := existsUnique_forall_apply_eq_of_cycleType h8 hF
  have hcp : (c : Perm (Fin 9)) p = p := hpu _ fun h hh => by
    rw [← Perm.mul_apply, hc' h hh, Perm.mul_apply, hp h hh]
  obtain ⟨i, hi⟩ := exists_ne p
  have hci : (c : Perm (Fin 9)) i ≠ p := fun h =>
    hi ((c : Perm (Fin 9)).injective (h.trans hcp.symm))
  obtain ⟨g, ⟨hg, hgi⟩, -⟩ := existsUnique_mem_apply_eq_of_cycleType hF hp h8 hi hci
  suffices hcg : c = g by rw [hcg]; exact hg
  refine Subtype.ext (Perm.ext fun j => ?_)
  rcases eq_or_ne j p with rfl | hj
  · rw [hcp, hp g hg]
  obtain ⟨h, ⟨hh, rfl⟩, -⟩ := existsUnique_mem_apply_eq_of_cycleType hF hp h8 hi hj
  have hgh : (g : Perm (Fin 9)) * h = (h : Perm (Fin 9)) * g := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm g hg h hh]
  rw [← Perm.mul_apply, ← hc' h hh, Perm.mul_apply, ← hgi, ← Perm.mul_apply, ← hgh,
    Perm.mul_apply]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
