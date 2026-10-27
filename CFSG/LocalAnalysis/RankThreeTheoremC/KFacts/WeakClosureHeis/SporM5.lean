module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporDispatch
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGood
public import CFSG.Certificates.Kernel.MonsterPcFive.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Blueprint
open scoped commutatorElement

namespace SporM5

section ClassTwo

variable {G : Type*} [Group G]

theorem class_two_pow_aux (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * (x * y ^ n) := by
  have hc : y * x = ⁅y, x⁆ * (x * y) := by
    rw [commutatorElement_def]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : y * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * y := (hy.symm.pow_right n).eq
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by rw [pow_succ', mul_assoc]
      _ = y * (⁅y, x⁆ ^ n * (x * y ^ n)) := by rw [ih]
      _ = ⁅y, x⁆ ^ n * (y * x) * y ^ n := by rw [← mul_assoc, h1]; group
      _ = ⁅y, x⁆ ^ n * (⁅y, x⁆ * (x * y)) * y ^ n := by rw [hc]
      _ = ⁅y, x⁆ ^ (n + 1) * (x * y ^ (n + 1)) := by rw [pow_succ, pow_succ']; group

theorem class_two_pow (x y : G) (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * y ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x ^ n * ⁅y, x⁆ ^ n = ⁅y, x⁆ ^ n * x ^ n := ((hx.pow_pow n n).symm).eq
    have h2 : (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
    have h3 : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := h2
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (y ^ n * x) * y) := by rw [ih]; group
      _ = ⁅y, x⁆ ^ n.choose 2 * (x ^ n * (⁅y, x⁆ ^ n * (x * y ^ n)) * y) := by
        rw [class_two_pow_aux x y hx hy n]
      _ = ⁅y, x⁆ ^ n.choose 2 * (⁅y, x⁆ ^ n * (x ^ n * (x * y ^ n)) * y) := by
        rw [← mul_assoc (x ^ n), h1]; group
      _ = ⁅y, x⁆ ^ (n + 1).choose 2 * (x ^ (n + 1) * y ^ (n + 1)) := by
        rw [h3]; group

theorem class_two_pow_prime {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (x y : G)
    (hx : Commute ⁅y, x⁆ x) (hy : Commute ⁅y, x⁆ y) (hc : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  rw [class_two_pow x y hx hy p]
  obtain ⟨k, hk⟩ := hp.dvd_choose_self (by norm_num : 2 ≠ 0) hp3
  rw [hk, pow_mul, hc, one_pow, one_mul]

theorem pow_eq_one_closure {p : ℕ} (hp : p.Prime) (hp3 : 2 < p) (S : Set G) (Z : Subgroup G)
    (hZS : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z)
    (hSS : ∀ a ∈ S, ∀ b ∈ S, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hZp : ∀ z ∈ Z, z ^ p = 1) (hS : ∀ s ∈ S, s ^ p = 1) :
    ∀ g ∈ Subgroup.closure S, g ^ p = 1 := by
  have hZc : ∀ z ∈ Z, ∀ g ∈ Subgroup.closure S, z * g = g * z := by
    intro z hz g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hZS z hz x hx
    | one => simp
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx =>
      calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
        _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * z := by group
  have hcomm : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x hx y hy
    induction hx, hy using Subgroup.closure_induction₂ with
    | mem x y hx hy => exact hSS x hx y hy
    | one_left y hy => simpa using Z.one_mem
    | one_right x hx => simpa using Z.one_mem
    | mul_left x y z hx hy hz h1 h2 =>
      have key : x * y * z * (x * y)⁻¹ * z⁻¹ =
          (x * (y * z * y⁻¹ * z⁻¹) * x⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group
      have hconj : x * (y * z * y⁻¹ * z⁻¹) * x⁻¹ = y * z * y⁻¹ * z⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]; exact (hZc _ h2 x hx).symm
      rw [key, hconj]
      exact Z.mul_mem h2 h1
    | mul_right y z x hy hz hx h1 h2 =>
      have key : x * (y * z) * x⁻¹ * (y * z)⁻¹ =
          (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
      have hconj : y * (x * z * x⁻¹ * z⁻¹) * y⁻¹ = x * z * x⁻¹ * z⁻¹ := by
        rw [mul_inv_eq_iff_eq_mul]; exact (hZc _ h2 y hy).symm
      rw [key, hconj]
      exact Z.mul_mem h1 h2
    | inv_left x y hx hy h =>
      have key : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x := by group
      have hconj : x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
        rw [mul_assoc, hZc _ (Z.inv_mem h) x hx, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [key, hconj]
      exact Z.inv_mem h
    | inv_right x y hx hy h =>
      have key : x * y⁻¹ * x⁻¹ * y⁻¹⁻¹ = y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y := by group
      have hconj : y⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * y = (x * y * x⁻¹ * y⁻¹)⁻¹ := by
        rw [mul_assoc, hZc _ (Z.inv_mem h) y hy, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [key, hconj]
      exact Z.inv_mem h
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => simp
  | mul x y hx hy h1 h2 =>
    have hc : ⁅y, x⁆ ∈ Z := by
      rw [commutatorElement_def]; exact hcomm y hy x hx
    have hcx : Commute ⁅y, x⁆ x := hZc _ hc x hx
    have hcy : Commute ⁅y, x⁆ y := hZc _ hc y hy
    rw [class_two_pow_prime hp hp3 x y hcx hcy (hZp _ hc), h1, h2, one_mul]
  | inv x hx h => rw [inv_pow, h, inv_one]

end ClassTwo

open _root_.Timmesfeld.PcFive _root_.Timmesfeld.PcReg
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular

section Gmat

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated

theorem rSub_pow_five {G : Type*} [Group G] {b : Fin 6 → G} {x : G}
    (h : CFSG.KC.MonPcFive.RRel CFSG.KC.MonPcFive.cmM b x) :
    ∀ u ∈ Subgroup.closure (Set.range b), u ^ 5 = 1 := by
  refine pow_eq_one_closure Nat.prime_five (by norm_num) (Set.range b) (Subgroup.zpowers x)
    ?_ ?_ ?_ ?_
  · rintro z hz _ ⟨i, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact (Commute.zpow_left (h.xc i : Commute x (b i)) n).eq
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    have hk : (b i)⁻¹ * (b j)⁻¹ * b i * b j = x ^ (CFSG.KC.MonPcFive.Mz i j).val :=
      h.bcomm_eq i j
    have hxc : Commute x (b i * b j) :=
      Commute.mul_right (a := x) (h.xc i : Commute x (b i)) (h.xc j : Commute x (b j))
    have e : b i * b j * (b i)⁻¹ * (b j)⁻¹ = x ^ (CFSG.KC.MonPcFive.Mz i j).val := by
      calc b i * b j * (b i)⁻¹ * (b j)⁻¹
          = (b i * b j) * ((b i)⁻¹ * (b j)⁻¹ * b i * b j) * (b i * b j)⁻¹ := by group
        _ = (b i * b j) * x ^ (CFSG.KC.MonPcFive.Mz i j).val * (b i * b j)⁻¹ := by rw [hk]
        _ = x ^ (CFSG.KC.MonPcFive.Mz i j).val := by
          rw [((hxc.pow_left _).eq).symm]
          group
    rw [e]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _
  · intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.x5, one_zpow]
  · rintro _ ⟨i, rfl⟩
    exact h.b5 i

set_option maxRecDepth 100000 in
theorem fivePw_eq_pw : fivePw = _root_.Timmesfeld.PcFive.pw := by decide +kernel

set_option maxRecDepth 100000 in
theorem fiveCw_eq_cw : fiveCw = _root_.Timmesfeld.PcFive.cw := by decide +kernel

theorem rSub_Gmat [Finite Gmat] :
    ∃ U : Subgroup Gmat, IsPGroup 5 U ∧ (∀ u ∈ U, u ^ 5 = 1) ∧ 5 ^ 5 ≤ Nat.card U := by
  let g : Fin 9 → Gmat := fun i => gw fiveGens[i.val]!
  have hrel : ∀ r ∈ relSet 5 (pwF 9 _root_.Timmesfeld.PcFive.pw) (cwF 9 _root_.Timmesfeld.PcFive.cw),
      FreeGroup.lift g r = 1 := by
    rw [← fivePw_eq_pw, ← fiveCw_eq_cw]
    exact fiveRels_holds
  obtain ⟨hp, hc⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus.rel_of_relSet g hrel
  have H := CFSG.KC.MonPcFive.pcHyp_of_rel hp hc
  have hexp := rSub_pow_five H.rel
  have hcard := H.rel.card_R (x := g 8) fiveGen_eight_ne_one
  refine ⟨_, fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩, hexp, ?_⟩
  rw [hcard]
  norm_num

theorem sylowDichotomyAt_Gmat_five [Finite Gmat] :
    SylowDichotomyAt Gmat 5 := by
  obtain ⟨U, hU, hexp, hcard⟩ := rSub_Gmat
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact SylowDichotomyAt.of_exponent (U := U) hU hexp hcard

end Gmat

end SporM5

section Certs

theorem sdSpor_M5 : SDSporAt .M 5 := by
  intro K _ _ ⟨e⟩
  haveI : IsSimpleGroup (NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨e'⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := NativeSporadic.Carrier .M) (MulEquiv.refl _)
  haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv K (e.trans e').toEquiv
  exact SylowDichotomyAt.of_mulEquiv Nat.prime_five (e.trans e') SporM5.sylowDichotomyAt_Gmat_five

end Certs

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
