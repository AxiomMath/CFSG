module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BLyConfig

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

open Equiv Equiv.Perm MulAction Subgroup

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem mem_normalizer_inf_fixing {T : Subgroup (Perm X)} {g : Perm X} (hg : g ∈ normalizer T)
    (S : Set X) (hgS : ∀ z ∈ S, g z = z) :
    g ∈ normalizer (T ⊓ fixingSubgroup (Perm X) S : Subgroup (Perm X)) :=
  inf_normalizer_le_normalizer_inf
    ⟨hg, Subgroup.le_normalizer ((mem_fixingSubgroup_iff (Perm X)).2 hgS)⟩

theorem orbit_subset_pair {E T : Subgroup (Perm X)} (c : Config E) (hE : IsPGroup 3 E)
    (hT : IsPGroup 2 T) (hET : E ≤ normalizer T) (hq : c.q ∈ orbit T c.p) :
    ∀ y ∈ orbit T c.p, y = c.p ∨ y = c.q := by
  intro y hy
  by_contra hne
  obtain ⟨hyp, hyq⟩ := not_or.1 hne
  obtain ⟨i, hi⟩ := c.cover y hyp hyq
  let S : Set X := {z | ∃ m, m ≠ i ∧ z ∈ (c.a m).support}
  let T' : Subgroup (Perm X) := T ⊓ fixingSubgroup (Perm X) S
  have hT'2 : IsPGroup 2 T' := hT.to_le inf_le_left
  have key : ∀ w ∈ T, (∀ m, m ≠ i → c.a m * w = w * c.a m) → w ∈ T' := fun w hw hc =>
    ⟨hw, (mem_fixingSubgroup_iff (Perm X)).2 fun z ⟨m, hm, hz⟩ =>
      fix_of_comm hT hw (c.a_cube m) (c.supp_card m) (hc m hm).symm (c.ne_of_mem hz)⟩
  have hnorm : c.a i ∈ normalizer T' := mem_normalizer_inf_fixing (hET (c.a_mem i)) S
    fun z ⟨m, hm, hz⟩ => c.fix_of_notMem fun h => hm (c.mem_inj hz h)
  have hstab : ∀ x ∈ (orbit T' c.p : Set X), c.a i x ∈ (orbit T' c.p : Set X) := fun x hx =>
    (mem_setStab.1 (mem_setStab_orbit (le_refl _) (mem_orbit_self c.p) hnorm
      (c.fix_p _ (c.a_mem i))) x).2 hx
  obtain ⟨⟨τ0, hτ0⟩, hτ0p⟩ := mem_orbit_iff.1 hq
  obtain ⟨τ, hτ, hτp, hτc⟩ := exists_comm_elt hE hT hET (x := c.p) (y := c.q) ⟨τ0, hτ0, hτ0p⟩
  have hτ' : τ ∈ T' := key τ hτ fun m _ =>
    hτc _ (c.a_mem m) (c.fix_p _ (c.a_mem m)) (c.fix_q _ (c.a_mem m))
  obtain ⟨⟨w0, hw0⟩, hw0p⟩ := mem_orbit_iff.1 hy
  obtain ⟨u, hu, hup, huc⟩ := exists_comm_elt hE hT hET (x := c.p) (y := y) ⟨w0, hw0, hw0p⟩
  have hu' : u ∈ T' := key u hu fun m hm => huc _ (c.a_mem m) (c.fix_p _ (c.a_mem m))
    (c.fix_of_notMem fun h => hm (c.mem_inj h hi))
  have hyO : y ∈ (orbit T' c.p : Set X) := mem_orbit_iff.2 ⟨⟨u, hu'⟩, hup⟩
  have hqO : c.q ∈ (orbit T' c.p : Set X) := mem_orbit_iff.2 ⟨⟨τ, hτ'⟩, hτp⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset X, Q = insert c.p (insert c.q (c.a i).support) := ⟨_, rfl⟩
  have hQ : ∀ z, z ∈ Q ↔ z = c.p ∨ z = c.q ∨ z ∈ (c.a i).support := fun z => by simp [hQdef]
  have hset : (orbit T' c.p : Set X) = ↑Q := by
    ext z
    rw [Finset.mem_coe, hQ]
    constructor
    · intro hz
      obtain ⟨⟨t, ht⟩, htz⟩ := mem_orbit_iff.1 hz
      have htz' : t c.p = z := htz
      by_contra hzQ
      obtain ⟨hzp, hzr⟩ := not_or.1 hzQ
      obtain ⟨hzq, hzi⟩ := not_or.1 hzr
      obtain ⟨m, hm⟩ := c.cover z hzp hzq
      have hmi : m ≠ i := fun h => hzi (h ▸ hm)
      have htz2 : t z = z := (mem_fixingSubgroup_iff (Perm X)).1 ht.2 z ⟨m, hmi, hm⟩
      exact hzp (t.injective (htz'.trans htz2.symm)).symm
    · intro hz
      rcases hz with hz | hz | hz
      · rw [hz]; exact mem_orbit_self _
      · rw [hz]; exact hqO
      · rw [c.support_eq i hi] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hz | hz | hz
        · rw [hz]; exact hyO
        · rw [hz]; exact hstab _ hyO
        · rw [hz]; exact hstab _ (hstab _ hyO)
  obtain ⟨k, hk⟩ := exists_card_orbit_eq hT'2 c.p
  have hQc : Q.card = 5 := by
    have h1 : c.q ∉ (c.a i).support := c.q_notMem i
    have h2 : c.p ∉ insert c.q (c.a i).support := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨c.p_ne_q, c.p_notMem i⟩
    rw [hQdef, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1, c.supp_card i]
  have h5 : 2 ^ k = 5 := by
    rw [← hk, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, hQc]
  rcases k with _ | k
  · norm_num at h5
  · rw [pow_succ] at h5; omega

end CFSG.LocalAnalysis.GLTheoremA.H301B.LyA11

end
