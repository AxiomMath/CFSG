module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.GLTheoremB
open CFSG.RankThree.PartOne.KCUnitary (commutator_iSup_commuting commutator_self_le
  conj_mem_commutator_self)
open scoped commutatorElement

section Family

variable {Xs : Type} [Group Xs] {ι : Type} (F : ι → Subgroup Xs)
  (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y)

include hc

theorem exists_decomp_of_commuting_iSup (i : ι) {b : Xs} (hb : b ∈ ⨆ j, F j) :
    ∃ bi ∈ F i, ∃ w : Xs, (∀ m ∈ F i, w * m = m * w) ∧ b = bi * w := by
  refine Subgroup.iSup_induction F (C := fun b => ∃ bi ∈ F i, ∃ w : Xs,
    (∀ m ∈ F i, w * m = m * w) ∧ b = bi * w) hb ?_ ?_ ?_
  · intro j x hx
    by_cases hji : j = i
    · subst hji
      exact ⟨x, hx, 1, fun m _ => by simp, by simp⟩
    · exact ⟨1, (F i).one_mem, x, fun m hm => (hc j i hji x hx m hm).eq, by simp⟩
  · exact ⟨1, (F i).one_mem, 1, fun m _ => by simp, by simp⟩
  · rintro x y ⟨xi, hxi, wx, hwx, rfl⟩ ⟨yi, hyi, wy, hwy, rfl⟩
    refine ⟨xi * yi, (F i).mul_mem hxi hyi, wx * wy, fun m hm => ?_, ?_⟩
    · rw [mul_assoc, hwy m hm, ← mul_assoc, hwx m hm, mul_assoc]
    · have h1 : wx * yi = yi * wx := hwx yi hyi
      calc xi * wx * (yi * wy) = xi * (wx * yi) * wy := by group
        _ = xi * (yi * wx) * wy := by rw [h1]
        _ = xi * yi * (wx * wy) := by group

theorem conj_mem_commutator_of_orbit_family (i : ι) :
    ∀ c ∈ ⨆ j, F j, ∀ g ∈ ⁅F i, F i⁆, c * g * c⁻¹ ∈ ⁅F i, F i⁆ := by
  intro c hc' g hg
  refine Subgroup.iSup_induction F (C := fun c => ∀ g ∈ ⁅F i, F i⁆, c * g * c⁻¹ ∈ ⁅F i, F i⁆)
    hc' ?_ ?_ ?_ g hg
  · intro j x hx g hg
    by_cases hji : j = i
    · subst hji
      exact conj_mem_commutator_self hx hg
    · have hgF : g ∈ F i := commutator_self_le (F i) hg
      rw [(hc j i hji x hx g hgF).eq, mul_inv_cancel_right]
      exact hg
  · intro g hg
    simpa using hg
  · intro u v hu hv g hg
    have e : u * v * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹ := by group
    rw [e]
    exact hu _ (hv g hg)

omit hc in
private def dsubOrb (H : Subgroup Xs) : ℕ → Subgroup Xs
  | 0 => H
  | n + 1 => ⁅dsubOrb H n, dsubOrb H n⁆

omit hc in
private theorem dsubOrb_succ_le (H : Subgroup Xs) (n : ℕ) : dsubOrb H (n + 1) ≤ dsubOrb H n :=
  commutator_self_le _

omit hc in
private theorem dsubOrb_anti (H : Subgroup Xs) : Antitone (dsubOrb H) :=
  antitone_nat_of_succ_le (dsubOrb_succ_le H)

omit hc in
private theorem map_subtype_derivedSeries_orb (H : Subgroup Xs) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = dsubOrb H n := by
  induction n with
  | zero => rw [derivedSeries_zero, dsubOrb, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, dsubOrb, Subgroup.map_commutator, ih]

private theorem dsubOrb_iSup (n : ℕ) : dsubOrb (⨆ i, F i) n = ⨆ i, dsubOrb (F i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsubOrb, ih]
    exact commutator_iSup_commuting (fun i => dsubOrb (F i) n)
      (fun i j hij a ha b hb => hc i j hij a (dsubOrb_anti (F i) (Nat.zero_le n) ha) b
        (dsubOrb_anti (F j) (Nat.zero_le n) hb))

omit hc in
private theorem dsubOrb_eq_bot_of_solvable {H : Subgroup Xs} (hH : Group.IsSolvable ↥H) :
    ∃ d : ℕ, dsubOrb H d = ⊥ := by
  obtain ⟨d, hd⟩ := hH.solvable
  refine ⟨d, ?_⟩
  rw [← map_subtype_derivedSeries_orb, hd, Subgroup.map_bot]

theorem derived_le_join_of_orbit_family [Finite ι]
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅F i, F i⁆ ∨ Group.IsSolvable ↥(F i)) :
    ∃ k : ℕ, ∀ g ∈ derivedSeries ↥(⨆ i, F i) k,
      (g : Xs) ∈ ⨆ i : {i // CFSG.IsQuasisimple ↥⁅F i, F i⁆}, ⁅F i.1, F i.1⁆ := by
  classical
  have hd : ∀ i, ∃ d : ℕ, ¬ CFSG.IsQuasisimple ↥⁅F i, F i⁆ → dsubOrb (F i) d = ⊥ := by
    intro i
    by_cases hq : CFSG.IsQuasisimple ↥⁅F i, F i⁆
    · exact ⟨0, fun h => absurd hq h⟩
    · obtain ⟨d, hd⟩ := dsubOrb_eq_bot_of_solvable ((htame i).resolve_left hq)
      exact ⟨d, fun _ => hd⟩
  choose d hd using hd
  cases nonempty_fintype ι
  refine ⟨Finset.univ.sup d + 1, fun g hg => ?_⟩
  have hg' : (g : Xs) ∈ dsubOrb (⨆ i, F i) (Finset.univ.sup d + 1) := by
    rw [← map_subtype_derivedSeries_orb]
    exact ⟨g, hg, rfl⟩
  rw [dsubOrb_iSup F hc] at hg'
  refine (iSup_le (fun i => ?_) : ⨆ i, dsubOrb (F i) (Finset.univ.sup d + 1) ≤ _) hg'
  by_cases hq : CFSG.IsQuasisimple ↥⁅F i, F i⁆
  · exact (dsubOrb_anti (F i) (Nat.le_add_left 1 _)).trans
      (le_iSup (fun i : {i // CFSG.IsQuasisimple ↥⁅F i, F i⁆} => ⁅F i.1, F i.1⁆) ⟨i, hq⟩)
  · have : dsubOrb (F i) (Finset.univ.sup d + 1) = ⊥ := by
      rw [eq_bot_iff]
      calc dsubOrb (F i) (Finset.univ.sup d + 1) ≤ dsubOrb (F i) (d i) :=
            dsubOrb_anti (F i) ((Finset.le_sup (f := d) (Finset.mem_univ i)).trans (Nat.le_succ _))
        _ = ⊥ := hd i hq
        _ ≤ _ := le_rfl
    rw [this]
    exact bot_le

end Family

section Blocks

variable {Xs : Type} [Group Xs] [Finite Xs]

theorem lift_blocks_of_orbit_family (q : ℕ) (a : Xs) {ι : Type} [Finite ι] (F : ι → Subgroup Xs)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, Commute x y)
    (hjoin : ⨆ i, F i = Subgroup.centralizer ({a} : Set Xs))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅F i, F i⁆ ∨ Group.IsSolvable ↥(F i))
    (key : ∀ i, CFSG.IsQuasisimple ↥⁅F i, F i⁆ → IsTypeL2 q ↥⁅F i, F i⁆ →
      ∀ b ∈ F i, (∀ m ∈ F i, b ^ 3 * m = m * b ^ 3) →
        ∃ s ∈ ⁅F i, F i⁆, ∀ m ∈ ⁅F i, F i⁆, b * m * b⁻¹ = s * m * s⁻¹) :
    ∃ (ι' : Type) (_ : Finite ι') (N : ι' → Subgroup Xs),
      (∀ i, N i ≤ Subgroup.centralizer ({a} : Set Xs)) ∧
      (∀ i, ∀ g ∈ Subgroup.centralizer ({a} : Set Xs), ∀ m ∈ N i, g * m * g⁻¹ ∈ N i) ∧
      (∀ i, CFSG.IsQuasisimple (N i)) ∧
      (∃ k : ℕ, ∀ g ∈ derivedSeries ↥(Subgroup.centralizer ({a} : Set Xs)) k,
        (g : Xs) ∈ ⨆ i, N i) ∧
      (∀ i, IsTypeL2 q (N i) → ∀ b ∈ Subgroup.centralizer ({a} : Set Xs), b ^ 3 = 1 →
        ∃ s ∈ N i, ∀ m ∈ N i, b * m * b⁻¹ = s * m * s⁻¹) := by
  classical
  refine ⟨{i // CFSG.IsQuasisimple ↥⁅F i, F i⁆}, inferInstance, fun i => ⁅F i.1, F i.1⁆,
    fun i => ?_, fun i g hg m hm => ?_, fun i => i.2, ?_, fun i hT b hb hb3 => ?_⟩
  · rw [← hjoin]
    exact (commutator_self_le (F i.1)).trans (le_iSup F i.1)
  · rw [← hjoin] at hg
    exact conj_mem_commutator_of_orbit_family F hc i.1 g hg m hm
  · rw [← hjoin]
    exact derived_le_join_of_orbit_family F hc htame
  · rw [← hjoin] at hb
    obtain ⟨bi, hbi, w, hw, rfl⟩ := exists_decomp_of_commuting_iSup F hc i.1 hb
    have hbw : bi * w = w * bi := (hw bi hbi).symm
    have hb3' : bi ^ 3 * w ^ 3 = 1 := by
      rw [← (Commute.mul_pow (show Commute bi w from hbw)), hb3]
    have hbi3 : bi ^ 3 = (w ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left hb3'
    have hcomm3 : ∀ m ∈ F i.1, bi ^ 3 * m = m * bi ^ 3 := by
      intro m hm
      have hwm : w * m = m * w := hw m hm
      have hw3 : w ^ 3 * m = m * w ^ 3 := by
        have : Commute w m := hwm
        exact (this.pow_left 3).eq
      rw [hbi3]
      have : Commute (w ^ 3) m := (hw3 : w ^ 3 * m = m * w ^ 3)
      exact (this.inv_left).eq
    obtain ⟨s, hs, hsm⟩ := key i.1 i.2 hT bi hbi hcomm3
    refine ⟨s, hs, fun m hm => ?_⟩
    have hmF : m ∈ F i.1 := commutator_self_le (F i.1) hm
    have hwm : w * m = m * w := hw m hmF
    calc bi * w * m * (bi * w)⁻¹ = bi * (w * m * w⁻¹) * bi⁻¹ := by group
      _ = bi * m * bi⁻¹ := by rw [hwm]; group
      _ = s * m * s⁻¹ := hsm m hm

end Blocks

end CFSG.HardMathSupport.Dickson.Sec6.I1431
