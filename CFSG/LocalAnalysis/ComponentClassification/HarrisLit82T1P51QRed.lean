module

public import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

theorem quat_mul_self : ∀ x : QuaternionGroup 2, x * x = 1 → x = 1 ∨ x = QuaternionGroup.a 2 := by
  decide

theorem quat_noncomm : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 ≠
    QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by
  decide

theorem card_quat : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem isSolvable_quat : Group.IsSolvable (QuaternionGroup 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card (n := 3) (by rw [card_quat]; rfl)
  have := hp.isNilpotent
  infer_instance

@[expose] def sl23i : SL(2, ZMod 3) := ⟨!![0, 1; -1, 0], by decide⟩

@[expose] def sl23j : SL(2, ZMod 3) := ⟨!![1, 1; 1, -1], by decide⟩

theorem sl23_mul_self : ∀ g : SL(2, ZMod 3), g * g = 1 → g = 1 ∨ g = -1 := by
  decide

theorem sl23_pow_eight : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g = 1 ∨ g = -1 ∨ g = sl23i ∨
    g = -sl23i ∨ g = sl23j ∨ g = -sl23j ∨ g = sl23i * sl23j ∨ g = -(sl23i * sl23j) := by
  decide

theorem sl23_noncomm : sl23i * sl23j ≠ sl23j * sl23i := by
  decide

theorem card_sl23 : Nat.card (SL(2, ZMod 3)) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem isSolvable_sl23 : Group.IsSolvable (SL(2, ZMod 3)) :=
  CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by decide)

theorem mem_of_card_eq_eight {P : Subgroup (SL(2, ZMod 3))} (hP : Nat.card P = 8) :
    sl23i ∈ P ∧ sl23j ∈ P := by
  classical
  set L : Finset (SL(2, ZMod 3)) := {1, -1, sl23i, -sl23i, sl23j, -sl23j, sl23i * sl23j,
    -(sl23i * sl23j)} with hL
  have hLcard : L.card = 8 := by
    rw [hL]
    decide
  have hsub : ∀ g ∈ P, g ∈ L := by
    intro g hg
    have h8 : g ^ 8 = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := ⟨g, hg⟩)
      rw [hP] at this
      exact congrArg Subtype.val this
    rcases sl23_pow_eight g h8 with h | h | h | h | h | h | h | h <;> simp [hL, h]
  have hPcard : (Finset.univ.filter (· ∈ P)).card = 8 := by
    rw [← hP, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  have heq : Finset.univ.filter (· ∈ P) = L := by
    refine Finset.eq_of_subset_of_card_le (fun g hg => hsub g (Finset.mem_filter.mp hg).2) ?_
    rw [hLcard, hPcard]
  have hmem : ∀ g ∈ L, g ∈ P := fun g hg => by
    rw [← heq] at hg
    exact (Finset.mem_filter.mp hg).2
  exact ⟨hmem _ (by simp [hL]), hmem _ (by simp [hL])⟩

theorem eq_bot_of_perfect {T : Type*} [Group T] [hT : Group.IsSolvable T] (P : Subgroup T)
    (hP : ⁅P, P⁆ = P) : P = ⊥ := by
  obtain ⟨n, hn⟩ := hT.solvable
  have key : ∀ k : ℕ, P ≤ derivedSeries T k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hP]
      exact commutator_mono ih ih
  exact eq_bot_iff.mpr (hn ▸ key n)

theorem commute_of_isComponent {X : Type} [Group X] [Finite X] {C R : Subgroup X} (hRC : R ≤ C)
    (hR : (R.subgroupOf C).IsSubnormal) (hsolv : Group.IsSolvable (↥R ⧸ pPrimeCore 2 ↥R))
    {K : Subgroup C} (hK : IsComponent K) (hKe : Even (Nat.card K)) :
    ∀ k ∈ K, ∀ r ∈ R, (k : X) * r = r * k := by
  rcases LocalCores.component_subnormal_subgroup hK hR with hKR | hKR
  · exfalso
    have hKle : K.map C.subtype ≤ R := by
      rintro _ ⟨k, hk, rfl⟩
      exact mem_subgroupOf.mp (hKR hk)
    set K₂ : Subgroup R := (K.map C.subtype).subgroupOf R with hK₂
    have e : ↥K ≃* ↥K₂ := (K.equivMapOfInjective C.subtype C.subtype_injective).trans
      (subgroupOfEquivOfLe hKle).symm
    have := hK.1.1
    have hperf : Group.IsPerfect K₂ := Group.IsPerfect.ofSurjective (f := e.toMonoidHom)
      e.surjective
    have hK₂perf : ⁅K₂, K₂⁆ = K₂ := Subgroup.isPerfect_iff.mp hperf
    set P := K₂.map (QuotientGroup.mk' (pPrimeCore 2 ↥R)) with hPdef
    have hPperf : ⁅P, P⁆ = P := by rw [hPdef, ← map_commutator, hK₂perf]
    have hP : P = ⊥ := eq_bot_of_perfect P hPperf
    have hle : K₂ ≤ pPrimeCore 2 ↥R := by
      intro k hk
      have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥R) k ∈ P := mem_map_of_mem _ hk
      rw [hP, mem_bot] at h1
      exact (QuotientGroup.eq_one_iff k).mp h1
    have hdvd : Nat.card K₂ ∣ Nat.card (pPrimeCore 2 ↥R) := card_dvd_of_le hle
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥R)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    rw [← Nat.card_congr e.toEquiv] at hdvd
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat hdvd)) hKe
  · intro k hk r hr
    have h1 : ⁅k, (⟨r, hRC hr⟩ : C)⁆ ∈ ⁅K, R.subgroupOf C⁆ :=
      commutator_mem_commutator hk (mem_subgroupOf.mpr hr)
    rw [hKR, mem_bot] at h1
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    exact congrArg Subtype.val h2

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
