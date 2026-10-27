module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace Up34Chev2

section DerivedJoin

variable {G : Type*} [Group G]

def dsubOrb (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅dsubOrb H n, dsubOrb H n⁆

theorem commutator_le_self_orb (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

theorem dsubOrb_anti (H : Subgroup G) : Antitone (dsubOrb H) :=
  antitone_nat_of_succ_le fun n => commutator_le_self_orb (dsubOrb H n)

theorem dsubOrb_le_self (H : Subgroup G) (n : ℕ) : dsubOrb H n ≤ H :=
  dsubOrb_anti H (Nat.zero_le n)

theorem map_subtype_derivedSeries_orb (H : Subgroup G) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = dsubOrb H n := by
  induction n with
  | zero => rw [derivedSeries_zero, dsubOrb, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, dsubOrb, Subgroup.map_commutator, ih]

theorem dsubOrb_iSup {ι : Type*} (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (n : ℕ) :
    dsubOrb (⨆ i, A i) n = ⨆ i, dsubOrb (A i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsubOrb, ih]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_iSup_commuting (fun i => dsubOrb (A i) n)
      (fun i j hij a ha b hb => hc i j hij a (dsubOrb_le_self _ n ha) b (dsubOrb_le_self _ n hb))

theorem isSolvable_quotient_of_orbit_family_orb {ι : Type*} [Finite ι] (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (P : ι → Prop)
    (hP : ∀ i, ¬ P i → Group.IsSolvable ↥(A i)) {C N : Subgroup G} (hCA : ⨆ i, A i = C)
    (hN : ∀ i, P i → ⁅A i, A i⁆ ≤ N) [(N.subgroupOf C).Normal] :
    Group.IsSolvable (↥C ⧸ N.subgroupOf C) := by
  classical
  subst hCA
  have hk : ∀ i, ∃ k : ℕ, ¬ P i → dsubOrb (A i) k = ⊥ := by
    intro i
    by_cases hi : P i
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨k, hk⟩ := (hP i hi).solvable
      refine ⟨k, fun _ => ?_⟩
      rw [← map_subtype_derivedSeries_orb, hk, Subgroup.map_bot]
  choose k hk using hk
  cases nonempty_fintype ι
  refine ⟨⟨Finset.univ.sup k + 1, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (N.subgroupOf (⨆ i, A i))),
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', Subgroup.subgroupOf,
    ← Subgroup.map_le_iff_le_comap, map_subtype_derivedSeries_orb, dsubOrb_iSup A hc]
  refine iSup_le fun i => ?_
  by_cases hi : P i
  · exact (dsubOrb_anti (A i) (Nat.le_add_left 1 _)).trans (hN i hi)
  · have h1 : dsubOrb (A i) (Finset.univ.sup k + 1) ≤ dsubOrb (A i) (k i) :=
      dsubOrb_anti (A i) ((Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
    exact (h1.trans (hk i hi).le).trans bot_le

end DerivedJoin

section Assembly

variable {X T : Type} [Group X] [Group T] [Finite X] [Finite T]

theorem fixSubgroup_conj_eq_centralizer_orb (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem noL34Layer_conj_of_orbit_family (π : X →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center X) (x : X) {ι : Type*} [Finite ι] (A : ι → Subgroup X)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b)
    (hjoin : ⨆ i, A i = Subgroup.centralizer ({x} : Set X))
    (htame : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i))
    (hno : ∀ i, CFSG.IsQuasisimple ↥⁅A i, A i⁆ →
      IsLThreeFour (↥⁅A i, A i⁆ ⧸ Subgroup.center ↥⁅A i, A i⁆) →
        ∃ z : X, z ∈ ⁅A i, A i⁆ ∧ (∀ g ∈ ⁅A i, A i⁆, g * z = z * g) ∧ z ^ 3 = 1 ∧ π z ≠ 1) :
    NoL34Layer (MulAut.conj (π x)) := by
  classical
  have hfix : ⨆ i, A i = fixSubgroup (MulAut.conj x) := by
    rw [hjoin, fixSubgroup_conj_eq_centralizer_orb]
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
  have hNn := conj_mem_iSup_c2 (A := fixSubgroup (MulAut.conj x)) F hFn
  haveI : ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  haveI hsol : Group.IsSolvable (↥(fixSubgroup (MulAut.conj x)) ⧸
      (⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x))) := by
    refine isSolvable_quotient_of_orbit_family_orb A hc (fun i => CFSG.IsQuasisimple ↥⁅A i, A i⁆)
      (fun i hi => (htame i).resolve_left hi) hfix fun i hi => ?_
    exact le_iSup F ⟨i, hi⟩
  refine noL34Layer_of_centralQuotient_two π hπ hker (MulAut.conj x) (MulAut.conj (π x))
    (fun g => by simp [MulAut.conj_apply]) F
    (fun i => (commutator_le_self_orb _).trans ((le_iSup A i.1).trans hfix.le)) hFn (fun i => i.2)
    (QuotientGroup.mk' ((⨆ i, F i).subgroupOf (fixSubgroup (MulAut.conj x)))) (fun g hg => ?_)
    (fun i => hno i.1 i.2)
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg

end Assembly

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
