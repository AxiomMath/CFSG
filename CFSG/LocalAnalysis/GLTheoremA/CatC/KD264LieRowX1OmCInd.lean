module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCStep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open
open scoped commutatorElement

section Ind

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

scoped instance finite_of_finiteDimensional [FiniteDimensional (ZMod 2) V] : Finite V :=
  Module.finite_of_finite (ZMod 2)

theorem rot_pow_of_perp {a b : V} (h : MinusPair Q a b) {x : V} (hxa : polar Q x a = 0)
    (hxb : polar Q x b = 0) (k : ℕ) : (rot Q a b ^ k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, LinearEquiv.mul_apply, rot_apply_of_perp h hxa hxb, ih]

theorem rot_pow_mem_planeSpan {a b : V} (h : MinusPair Q a b) (k : ℕ) {x : V}
    (hx : x ∈ planeSpan (a, b)) : (rot Q a b ^ k) x ∈ planeSpan (a, b) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply]
    obtain ⟨c, d, hcd⟩ := (mem_planeSpan_iff (a, b) _).1 ih
    rw [← hcd, map_add, map_smul, map_smul, rot_apply_left h, rot_apply_right h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (right_mem_planeSpan (a, b)))
      (Submodule.smul_mem _ _ (Submodule.add_mem _ (left_mem_planeSpan (a, b))
        (right_mem_planeSpan (a, b))))

theorem polar_planeSpan_perp {p : V × V} {x : V} (hx : x ∈ perpPlane Q p) {w : V}
    (hw : w ∈ planeSpan p) : polar Q w x = 0 := by
  obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p w).1 hw
  obtain ⟨h1, h2⟩ := (mem_perpPlane_iff p x).1 hx
  rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h2]
  simp

theorem exists_frame [FiniteDimensional (ZMod 2) V] {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : IsElemAbelian 3 E) :
    ∀ (n : ℕ) (N : Submodule (ZMod 2) V), finrank (ZMod 2) N = n →
      (∀ g ∈ E, ∀ x ∈ N, g x ∈ N) →
      (∀ x ∈ N, (∀ y ∈ N, polar Q x y = 0) → x = 0) →
      ∃ l : List (V × V), IsFrame Q l ∧ (∀ p ∈ l, p.1 ∈ N ∧ p.2 ∈ N) ∧
        ∀ g ∈ E, ∃ t ∈ torus Q l, ∀ x ∈ N, g x = t x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N hn hN hnd
    by_cases htriv : ∀ g ∈ E, ∀ x ∈ N, g x = x
    · refine ⟨[], IsFrame.nil, fun p hp => absurd hp List.not_mem_nil, fun g hg => ?_⟩
      exact ⟨1, one_mem _, fun x hx => htriv g hg x hx⟩
    push Not at htriv
    obtain ⟨g₀, hg₀, x₀, hx₀, hmov⟩ := htriv
    obtain ⟨a, b, ha, hb, hpair, hact⟩ := exists_adapted_pair hEO hE hN hnd hg₀ hx₀ hmov
    set p : V × V := (a, b) with hp
    have hpair' : MinusPair Q p.1 p.2 := hpair
    set N' : Submodule (ZMod 2) V := N ⊓ perpPlane Q p with hN'
    have hplane : ∀ g ∈ E, ∀ x ∈ planeSpan p, g x ∈ planeSpan p := by
      intro g hg x hx
      obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p x).1 hx
      obtain ⟨k, hk1, hk2⟩ := hact g hg
      rw [map_add, map_smul, map_smul]
      change c • g a + d • g b ∈ planeSpan p
      rw [hk1, hk2]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (rot_pow_mem_planeSpan hpair k (left_mem_planeSpan p)))
        (Submodule.smul_mem _ _ (rot_pow_mem_planeSpan hpair k (right_mem_planeSpan p)))
    have hN'inv : ∀ g ∈ E, ∀ x ∈ N', g x ∈ N' := by
      intro g hg x hx
      refine ⟨hN g hg x hx.1, ?_⟩
      show g x ∈ perpPlane Q p
      rw [mem_perpPlane_iff]
      have hginv : g⁻¹ ∈ E := inv_mem hg
      have key : ∀ y ∈ planeSpan p, polar Q y (g x) = 0 := by
        intro y hy
        have h1 := E_polar hEO hginv y (g x)
        have h2 : g⁻¹ (g x) = x := by
          show g.symm (g x) = x
          exact g.symm_apply_apply x
        rw [h2] at h1
        rw [← h1]
        exact polar_planeSpan_perp hx.2 (hplane g⁻¹ hginv y hy)
      exact ⟨key _ (left_mem_planeSpan p), key _ (right_mem_planeSpan p)⟩
    have hdecomp : ∀ z ∈ N, projPlane Q p z ∈ N ∧ z - projPlane Q p z ∈ N' := by
      intro z hz
      have hw : projPlane Q p z ∈ N :=
        N.add_mem (N.smul_mem _ ha) (N.smul_mem _ hb)
      exact ⟨hw, N.sub_mem hz hw, sub_projPlane_mem hpair' z⟩
    have hN'nd : ∀ x ∈ N', (∀ y ∈ N', polar Q x y = 0) → x = 0 := by
      intro x hx hxy
      refine hnd x hx.1 (fun z hz => ?_)
      obtain ⟨hw, hy⟩ := hdecomp z hz
      have hz' : z = projPlane Q p z + (z - projPlane Q p z) := by abel
      rw [hz', polar_add_right, hxy _ hy, add_zero]
      rw [polar_comm]
      exact polar_planeSpan_perp hx.2 (projPlane_mem Q p z)
    have hlt : finrank (ZMod 2) N' < n := by
      rw [← hn]
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne inf_le_left (fun heq => ?_)
      have : a ∈ N' := by rw [heq]; exact ha
      have h1 := ((mem_perpPlane_iff p a).1 this.2).2
      change polar Q b a = 0 at h1
      rw [hpair.ba] at h1
      exact one_ne_zero h1
    obtain ⟨l', hl', hl'N, hl'g⟩ := ih _ hlt N' rfl hN'inv hN'nd
    have hperp : ∀ q ∈ l', PairPerp Q p q := by
      intro q hq
      have h1 := (mem_perpPlane_iff p q.1).1 (hl'N q hq).1.2
      have h2 := (mem_perpPlane_iff p q.2).1 (hl'N q hq).2.2
      exact ⟨h1.1, h2.1, h1.2, h2.2⟩
    refine ⟨p :: l', IsFrame.cons hpair' hperp hl', ?_, ?_⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨ha, hb⟩
      · exact ⟨(hl'N q hq).1.1, (hl'N q hq).2.1⟩
    · intro g hg
      obtain ⟨k, hk1, hk2⟩ := hact g hg
      obtain ⟨t', ht', hgt'⟩ := hl'g g hg
      refine ⟨(rot Q a b ^ k) * t', ?_, ?_⟩
      · rw [torus_cons]
        exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k) ht'
      · intro x hx
        obtain ⟨hw, hy⟩ := hdecomp x hx
        set w := projPlane Q p x with hwdef
        have hxsplit : x = w + (x - w) := by abel
        have hw' : ∀ q ∈ l', polar Q w q.1 = 0 ∧ polar Q w q.2 = 0 := by
          intro q hq
          obtain ⟨c, d, hcd⟩ := (mem_planeSpan_iff p w).1 (projPlane_mem Q p x)
          have hpq := hperp q hq
          rw [← hcd]
          constructor
          · rw [polar_add_left, polar_smul_left, polar_smul_left, hpq.1, hpq.2.2.1]
            simp
          · rw [polar_add_left, polar_smul_left, polar_smul_left, hpq.2.1, hpq.2.2.2]
            simp
        have ht'w : t' w = w := torus_fixes hl' hw' t' ht'
        have hgy : g (x - w) = t' (x - w) := hgt' _ hy
        have hgyN' : g (x - w) ∈ N' := hN'inv g hg _ hy
        have hgy_perp := (mem_perpPlane_iff p _).1 hgyN'.2
        have hrot : (rot Q a b ^ k) (g (x - w)) = g (x - w) :=
          rot_pow_of_perp hpair (by rw [polar_comm]; exact hgy_perp.1)
            (by rw [polar_comm]; exact hgy_perp.2) k
        have hgw : g w = (rot Q a b ^ k) w := by
          obtain ⟨c, d, hcd⟩ := (mem_planeSpan_iff p w).1 (projPlane_mem Q p x)
          rw [← hcd, map_add, map_smul, map_smul, map_add, map_smul, map_smul]
          change c • g a + d • g b = c • (rot Q a b ^ k) a + d • (rot Q a b ^ k) b
          rw [hk1, hk2]
        rw [LinearEquiv.mul_apply]
        conv_lhs => rw [hxsplit]
        conv_rhs => rw [hxsplit]
        rw [map_add, map_add, ht'w, ← hgt' _ hy, map_add, hrot, hgw]

end Ind

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end
