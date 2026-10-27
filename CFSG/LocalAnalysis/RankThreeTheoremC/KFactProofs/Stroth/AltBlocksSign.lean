module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksModel
import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks

variable {k p : ℕ}

theorem sign_swapB [NeZero p] (hp : Odd p) {i j : Fin k} (hij : i ≠ j) :
    Equiv.Perm.sign (swapB (p := p) i j) = -1 := by
  have h : swapB (p := p) i j = Equiv.prodCongrLeft (fun _ : ZMod p => Equiv.swap i j) := rfl
  rw [h, Equiv.Perm.sign_prodCongrLeft]
  simp [Equiv.Perm.sign_swap hij, Finset.prod_const, ZMod.card, hp.neg_one_pow]

theorem sign_scale_eq (i : Fin k) (r : (ZMod p)ˣ) [NeZero p] :
    Equiv.Perm.sign (scale i r) = Equiv.Perm.sign (Units.mulLeft r) := by
  have h : scale (p := p) i r = Equiv.Perm.prodExtendRight i (Units.mulLeft r) := by
    ext ⟨j, y⟩ : 1
    by_cases hj : j = i
    · subst hj
      simp [scale_apply]
    · simp [scale_apply, hj, Equiv.Perm.prodExtendRight_apply_ne]
  rw [h, Equiv.Perm.sign_prodExtendRight]

theorem exists_sign_scale_eq_neg_one [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2) (i : Fin k) :
    ∃ r : (ZMod p)ˣ, Equiv.Perm.sign (scale (p := p) i r) = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨φ, hφ⟩ : ∃ φ : (ZMod p)ˣ →* Equiv.Perm (ZMod p), ∀ u x, φ u x = (u : ZMod p) * x :=
    ⟨MulAction.toPermHom (ZMod p)ˣ (ZMod p), fun u x => rfl⟩
  have hfg : Units.mulLeft g = φ g := Equiv.ext fun x => (hφ g x).symm
  have hpow : ∀ (n : ℤ) (x : ZMod p),
      (Units.mulLeft g ^ n) x = ((g ^ n : (ZMod p)ˣ) : ZMod p) * x := by
    intro n x
    rw [hfg, ← map_zpow φ g n, hφ]
  have hne : (g : ZMod p) ≠ 1 := by
    intro h
    have hg1 : g = 1 := Units.ext h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (-1))
    rw [hg1, one_zpow] at hn
    have h3 : ((-1 : (ZMod p)ˣ) : ZMod p) = ((1 : (ZMod p)ˣ) : ZMod p) := by rw [← hn]
    exact (ZMod.neg_one_ne_one (n := p)) (by simpa using h3)
  have hcyc : (Units.mulLeft g).IsCycle := by
    refine ⟨1, ?_, ?_⟩
    · show (g : ZMod p) * 1 ≠ 1
      rw [mul_one]
      exact hne
    · intro y hy
      have hy0 : y ≠ 0 := by
        rintro rfl
        apply hy
        show (g : ZMod p) * 0 = 0
        rw [mul_zero]
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 y hy0))
      refine ⟨n, ?_⟩
      rw [hpow, hn, Units.val_mk0, mul_one]
  have hsupp : (Units.mulLeft g).support = Finset.univ.erase 0 := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro h rfl
      apply h
      show (g : ZMod p) * 0 = 0
      rw [mul_zero]
    · intro hx h
      apply hne
      have h' : (g : ZMod p) * x = 1 * x := by
        rw [one_mul]
        exact h
      exact mul_right_cancel₀ hx h'
  have hcard : (Units.mulLeft g).support.card = p - 1 := by
    rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)), Finset.card_univ,
      ZMod.card]
  refine ⟨g, ?_⟩
  rw [sign_scale_eq, hcyc.sign, hcard, (hp.even_sub_one hp2).neg_one_pow]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks
