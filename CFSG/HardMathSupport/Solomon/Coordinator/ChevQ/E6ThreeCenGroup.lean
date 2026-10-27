module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false

section Group

variable {G : Type*} [Group G]

theorem e6Cen_zpow_eq_pow_lt {g : G} (hg : g ^ 3 = 1) (m : ℤ) :
    ∃ k : ℕ, k < 3 ∧ g ^ m = g ^ k := by
  have hg' : g ^ (3 : ℤ) = 1 := by exact_mod_cast hg
  have h0 : 0 ≤ m % 3 := Int.emod_nonneg m (by decide)
  refine ⟨(m % 3).toNat, by omega, ?_⟩
  rw [zpow_eq_zpow_emod m hg', ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem e6Cen_mem_closure_pair_zpow {a b v : G} (hab : a * b = b * a)
    (hv : v ∈ Subgroup.closure {a, b}) : ∃ m n : ℤ, v = a ^ m * b ^ n := by
  have hc : Commute a b := hab
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by rw [zpow_one, zpow_zero, mul_one]⟩
    · exact ⟨0, 1, by rw [zpow_one, zpow_zero, one_mul]⟩
  | one => exact ⟨0, 0, by rw [zpow_zero, zpow_zero, mul_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨m, n, rfl⟩ := hx
    obtain ⟨m', n', rfl⟩ := hy
    refine ⟨m + m', n + n', ?_⟩
    have e : b ^ n * a ^ m' = a ^ m' * b ^ n := (hc.symm.zpow_zpow n m').eq
    calc a ^ m * b ^ n * (a ^ m' * b ^ n') = a ^ m * (b ^ n * a ^ m') * b ^ n' := by group
      _ = a ^ (m + m') * b ^ (n + n') := by rw [e]; group
  | inv x _ hx =>
    obtain ⟨m, n, rfl⟩ := hx
    refine ⟨-m, -n, ?_⟩
    have e : b ^ (-n) * a ^ (-m) = a ^ (-m) * b ^ (-n) := (hc.symm.zpow_zpow (-n) (-m)).eq
    calc (a ^ m * b ^ n)⁻¹ = b ^ (-n) * a ^ (-m) := by group
      _ = a ^ (-m) * b ^ (-n) := e

theorem e6Cen_mem_closure_pair {a b v : G} (hab : a * b = b * a) (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hv : v ∈ Subgroup.closure {a, b}) :
    ∃ m n : ℕ, m < 3 ∧ n < 3 ∧ v = a ^ m * b ^ n := by
  obtain ⟨m, n, rfl⟩ := e6Cen_mem_closure_pair_zpow hab hv
  obtain ⟨m', hm', e⟩ := e6Cen_zpow_eq_pow_lt ha m
  obtain ⟨n', hn', e'⟩ := e6Cen_zpow_eq_pow_lt hb n
  exact ⟨m', n', hm', hn', by rw [e, e']⟩

end Group

section Field

variable {K : Type} [Field K] {ω : Kˣ}

theorem e6Cen_one_add_add_sq (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) : (1 : K) + ω + (ω : K) ^ 2 = 0 := by
  have h1' : (ω : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => h1 (Units.ext h)
  have h3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have e : ((ω : K) - 1) * (1 + ω + (ω : K) ^ 2) = 0 := by linear_combination h3'
  exact (mul_eq_zero.1 e).resolve_left h1'

theorem e6Cen_three_ne_zero (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) : (3 : K) ≠ 0 := by
  intro h
  have hs := e6Cen_one_add_add_sq h3 h1
  have e : ((ω : K) - 1) ^ 2 = 0 := by linear_combination hs - (ω : K) * h
  exact h1 (Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 e)))

theorem e6Cen_ringChar_ne_three (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) : ringChar K ≠ 3 := by
  intro h
  have e := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at e
  exact e6Cen_three_ne_zero h3 h1 (by exact_mod_cast e)

end Field

section Conj

variable
  {K : Type} [Field K] [Finite K]

theorem e6Cen_conj_injective (hK4 : 4 ≤ Nat.card K) :
    Function.Injective
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) := by
  have hs : ∀ s : adjointGroup Tag.E6 K, MulAut.conj s =
      e6InndiagConj K ⟨s, adjointGroup_le_e6InndiagGL K s.2⟩ := fun s =>
    MulEquiv.ext fun h => Subtype.ext (by rw [e6InndiagConj_apply]; rfl)
  intro s t h
  have h' : e6InndiagConj K ⟨s, adjointGroup_le_e6InndiagGL K s.2⟩ =
      e6InndiagConj K ⟨t, adjointGroup_le_e6InndiagGL K t.2⟩ := by
    rw [← hs, ← hs]
    exact h
  have h2 := congrArg Subtype.val (e6InndiagConj_injective K hK4 h')
  exact Subtype.ext h2

theorem e6Cen_pow_three_of_conj (hK4 : 4 ≤ Nat.card K) {s : adjointGroup Tag.E6 K}
    (h : MulAut.conj s ^ 3 = 1) : s ^ 3 = 1 :=
  e6Cen_conj_injective hK4 (by rw [map_pow, h, map_one])

end Conj

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
