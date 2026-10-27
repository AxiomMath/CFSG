module

public import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.S11d.FormMaschke

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.K159

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem exists_fixedFree_part {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {N : Submodule F V}
    (hN : RegOn Q N) (hxN : ∀ v ∈ N, x v ∈ N) (hmov : ∃ v ∈ N, x v ≠ v) :
    ∃ U : Submodule F V, U ≤ N ∧ (∀ u ∈ U, x u ∈ U) ∧ RegOn Q U ∧ (∀ u ∈ U, x u = u → u = 0) ∧
      U ≠ ⊥ := by
  classical
  have hcompl := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero hx.pow_eq_one
  refine ⟨N ⊓ CFSG.RankThree.PartOne.LIT.commSpace x, inf_le_left, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact ⟨hxN u hu.1, CFSG.RankThree.PartOne.LIT.map_mem_commSpace (rfl : x * x = x * x) hu.2⟩
  · intro u hu horth
    apply hN u hu.1
    intro m hm
    obtain ⟨f, hf, c, hc, rfl⟩ :=
      CFSG.RankThree.PartOne.LIT.exists_add_of_invariant hx.cast_ne_zero hx.pow_eq_one hxN hm
    have huc : polar Q u c = 0 := horth c ⟨hc.1, hc.2⟩
    have huf : polar Q u f = 0 := by
      obtain ⟨y, hy⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hu.2
      have hfix : x f = f := CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hf.2
      have hsymm : x.symm f = f := by simpa [hfix] using x.symm_apply_apply f
      rw [← hy, polar_sub_left, hx.polar_apply y f, hsymm, sub_self]
    rw [polar_add_right, huf, huc, add_zero]
  · intro u hu hxu
    exact (Submodule.disjoint_def.mp hcompl.disjoint) u
      (CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr hxu) hu.2
  · obtain ⟨v, hvN, hxv⟩ := hmov
    refine (Submodule.ne_bot_iff _).mpr
      ⟨x v - v, ⟨N.sub_mem (hxN v hvN) hvN, CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨v, rfl⟩⟩, ?_⟩
    intro h
    exact hxv (sub_eq_zero.mp h)

theorem exists_nonsingular_of_moved {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {N : Submodule F V} (hN : RegOn Q N)
    (hxN : ∀ v ∈ N, x v ∈ N) (hmov : ∃ v ∈ N, x v ≠ v) :
    ∃ t : F, (∀ c : F, c * c + t * c + 1 ≠ 0) ∧ ∃ v ∈ N, x (x v) + t • x v + v = 0 ∧ Q v ≠ 0 := by
  obtain ⟨U, hUN, hxU, hUreg, hUfix, hU⟩ := exists_fixedFree_part hx hN hxN hmov
  obtain ⟨v, c, hvU, -, hQv, hxx, -, hroot⟩ := exists_plane hx hp hp2 hpq hxU hUreg hUfix hU
  refine ⟨c, fun s => by have h := hroot s; rwa [pow_two] at h, v, hUN hvU, ?_, hQv⟩
  rw [hxx, add_assoc]
  exact vec_add_self F _

end CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

end
