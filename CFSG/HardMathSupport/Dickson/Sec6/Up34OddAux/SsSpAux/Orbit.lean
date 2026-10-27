module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.CoreQuot
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.SsSp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Dickson.Sec6
open scoped commutatorElement

section DerivedJoin

variable {G : Type*} [Group G]

private def dsub (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅dsub H n, dsub H n⁆

private theorem commutator_le_self' (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem dsub_anti (H : Subgroup G) : Antitone (dsub H) :=
  antitone_nat_of_succ_le fun n => commutator_le_self' (dsub H n)

private theorem dsub_le_self (H : Subgroup G) (n : ℕ) : dsub H n ≤ H := dsub_anti H (Nat.zero_le n)

private theorem map_subtype_derivedSeries (H : Subgroup G) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = dsub H n := by
  induction n with
  | zero => rw [derivedSeries_zero, dsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, dsub, Subgroup.map_commutator, ih]

private theorem dsub_iSup {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (n : ℕ) :
    dsub (⨆ i, A i) n = ⨆ i, dsub (A i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsub, ih]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_iSup_commuting (fun i => dsub (A i) n)
      (fun i j hij a ha b hb => hc i j hij a (dsub_le_self _ n ha) b (dsub_le_self _ n hb))

private theorem isSolvable_quotient_of_orbit_family {ι : Type*} [Finite ι] (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (P : ι → Prop)
    (hP : ∀ i, ¬ P i → Group.IsSolvable ↥(A i)) {C N : Subgroup G} (hCA : ⨆ i, A i = C)
    (hN : ∀ i, P i → ⁅A i, A i⁆ ≤ N) [(N.subgroupOf C).Normal] :
    Group.IsSolvable (↥C ⧸ N.subgroupOf C) := by
  classical
  subst hCA
  have hk : ∀ i, ∃ k : ℕ, ¬ P i → dsub (A i) k = ⊥ := by
    intro i
    by_cases hi : P i
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨k, hk⟩ := (hP i hi).solvable
      refine ⟨k, fun _ => ?_⟩
      rw [← map_subtype_derivedSeries, hk, Subgroup.map_bot]
  choose k hk using hk
  cases nonempty_fintype ι
  refine ⟨⟨Finset.univ.sup k + 1, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (N.subgroupOf (⨆ i, A i))),
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.subgroupOf,
    ← Subgroup.map_le_iff_le_comap, map_subtype_derivedSeries, dsub_iSup A hc]
  refine iSup_le fun i => ?_
  by_cases hi : P i
  · exact (dsub_anti (A i) (Nat.le_add_left 1 _)).trans (hN i hi)
  · have h1 : dsub (A i) (Finset.univ.sup k + 1) ≤ dsub (A i) (k i) :=
      dsub_anti (A i) ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
    exact (h1.trans (hk i hi).le).trans bot_le

end DerivedJoin

section Assembly

variable {X T : Type} [Group X] [Group T] [Finite X] [Finite T]

theorem noL34Layer_conj_of_orbit_family (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (x : X) {ι : Type*} [Finite ι] (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i))
    (hno : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ →
      ¬ IsLThreeFour (↥⁅A i, A i⁆ ⧸ Subgroup.center ↥⁅A i, A i⁆)) :
    NoL34Layer (MulAut.conj (π x)) := by
  classical
  have hfix : ⨆ i, A i = fixSubgroup (MulAut.conj x) := by
    rw [hjoin, fixSubgroup_conj_eq_centralizer]
  have hnormA : ∀ i, ∀ c ∈ ⨆ j, A j, ∀ g ∈ A i, c * g * c⁻¹ ∈ A i := by
    intro i c hc'
    refine Subgroup.iSup_induction A (C := fun c => ∀ g ∈ A i, c * g * c⁻¹ ∈ A i) hc' ?_ ?_ ?_
    · intro j y hy g hg
      by_cases hji : j = i
      · subst hji
        exact (A j).mul_mem ((A j).mul_mem hy hg) ((A j).inv_mem hy)
      · rw [(hc j i hji y hy g hg).eq, mul_inv_cancel_right]
        exact hg
    · intro g hg
      simpa using hg
    · intro u v hu hv g hg
      have e : u * v * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹ := by group
      rw [e]
      exact hu _ (hv g hg)
  have hnormD : ∀ i, ∀ c ∈ ⨆ j, A j, ∀ g ∈ ⁅A i, A i⁆, c * g * c⁻¹ ∈ ⁅A i, A i⁆ := by
    intro i c hc' g hg
    have hmap : (A i).map (MulAut.conj c).toMonoidHom ≤ A i := by
      rintro _ ⟨y, hy, rfl⟩
      exact hnormA i c hc' y hy
    have h1 : (⁅A i, A i⁆).map (MulAut.conj c).toMonoidHom ≤ ⁅A i, A i⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact h1 ⟨g, hg, rfl⟩
  let F : {i : ι // CFSG.IsQuasisimple ↥⁅A i, A i⁆} → Subgroup X := fun i => ⁅A i.1, A i.1⁆
  have hFn : ∀ i, ∀ c ∈ fixSubgroup (MulAut.conj x), ∀ g ∈ F i, c * g * c⁻¹ ∈ F i :=
    fun i c hc' g hg => hnormD i.1 c (hfix ▸ hc') g hg
  have hNn := up34_conj_mem_iSup (A := fixSubgroup (MulAut.conj x)) F hFn
  haveI : ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  haveI hsol : Group.IsSolvable (↥(fixSubgroup (MulAut.conj x)) ⧸
      (⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))) := by
    refine isSolvable_quotient_of_orbit_family A hc (fun i => CFSG.IsQuasisimple ↥⁅A i, A i⁆)
      (fun i hi => (htame i).resolve_left hi) hfix fun i hi => ?_
    exact le_iSup F ⟨i, hi⟩
  refine noL34Layer_of_centralQuotient π hπ hker (MulAut.conj x) (MulAut.conj (π x))
    (fun g => by simp [MulAut.conj_apply]) F
    (fun i => (commutator_le_self' _).trans ((le_iSup A i.1).trans hfix.le)) hFn (fun i => i.2)
    (QuotientGroup.mk' ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x)))) (fun g hg => ?_)
    (fun i => hno i.1 i.2)
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg

end Assembly

end CFSG.HardMathSupport.Dickson.Sec6.SsSp
