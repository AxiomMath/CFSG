module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusInvolutionDerived
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.GorensteinWalter

open scoped commutatorElement

variable {E : Type*} [Group E]

theorem card_sup_zpowers_of_inv [Finite E] {U : Subgroup E} {w : E} (hwU : w ∉ U)
    (hw2 : w * w = 1) (hinv : ∀ u ∈ U, w * u * w⁻¹ = u⁻¹) :
    Nat.card (U ⊔ Subgroup.zpowers w : Subgroup E) = 2 * Nat.card U := by
  classical
  have hwi : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw2).symm
  let X : Subgroup E :=
    { carrier := {x | x ∈ U ∨ x * w ∈ U}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (U.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact U.mul_mem ha hb)
        · right
          have hbw : w⁻¹ * b * w ∈ U := by
            have := hinv b hb
            rw [hwi] at this ⊢
            rw [this]
            exact U.inv_mem hb
          have : a * b * w = a * w * (w⁻¹ * b * w) := by group
          rw [this]
          exact U.mul_mem ha hbw
        · left
          have hbw : w⁻¹ * (b * w) * w⁻¹ ∈ U := by
            have := hinv (b * w) hb
            rw [hwi] at this ⊢
            rw [this]
            exact U.inv_mem hb
          have : a * b = a * w * (w⁻¹ * (b * w) * w⁻¹) := by group
          rw [this]
          exact U.mul_mem ha hbw
      one_mem' := Or.inl U.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (U.inv_mem ha)
        · right
          have : a⁻¹ * w = w * (a * w)⁻¹ * w⁻¹ := by rw [hwi]; group
          rw [this, hinv _ (U.inv_mem ha), inv_inv]
          exact ha }
  have hXeq : U ⊔ Subgroup.zpowers w = X := by
    apply le_antisymm
    · refine sup_le (fun u hu => Or.inl hu) ?_
      rw [Subgroup.zpowers_le]
      right
      rw [hw2]
      exact U.one_mem
    · rintro x (hx | hx)
      · exact Subgroup.mem_sup_left hx
      · have : x = x * w * w⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w)))
  have hUX : U ≤ U ⊔ Subgroup.zpowers w := le_sup_left
  have hwX : w ∈ U ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hindex : (U.subgroupOf (U ⊔ Subgroup.zpowers w)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨w, hwX⟩, fun b => ?_⟩
    have hb : (b : E) ∈ X := hXeq ▸ b.2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rcases hb with hb | hb
    · refine Or.inr ⟨hb, ?_⟩
      intro hbw
      apply hwU
      have : w = (b : E)⁻¹ * ((b : E) * w) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem hb) hbw
    · refine Or.inl ⟨hb, ?_⟩
      intro hbU
      apply hwU
      have : w = (b : E)⁻¹ * ((b : E) * w) := by group
      rw [this]
      exact U.mul_mem (U.inv_mem hbU) hb
  have h := Subgroup.card_mul_index (U.subgroupOf (U ⊔ Subgroup.zpowers w))
  rw [hindex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv] at h
  rw [← h, mul_comm]

theorem involution_not_mem_of_odd_half [Finite E] {R U : Subgroup E} (hR : R.index = 2)
    (hUR : ¬ U ≤ R) {m : ℕ} (hU : Nat.card U = 2 * m) (hm : Odd m) {x : E} (hxU : x ∈ U)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x ∉ R := by
  classical
  intro hxR
  obtain ⟨u₀, hu₀U, hu₀R⟩ := Set.not_subset.mp hUR
  have hu₀R' : u₀ ∉ R := hu₀R
  have hindex : (R.subgroupOf U).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨u₀, hu₀U⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    have h := Subgroup.mul_mem_iff_of_index_two hR (a := (b : E)) (b := u₀)
    by_cases hb : (b : E) ∈ R
    · refine Or.inr ⟨hb, ?_⟩
      rw [h]
      simp [hb, hu₀R']
    · refine Or.inl ⟨?_, hb⟩
      rw [h]
      simp [hb, hu₀R']
  have hcard := Subgroup.card_mul_index (R.subgroupOf U)
  rw [hindex, hU] at hcard
  have hRU : Nat.card (R.subgroupOf U) = m := by omega
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hdvd : orderOf (⟨x, hxU⟩ : U) ∣ Nat.card (R.subgroupOf U) := by
    have := Subgroup.orderOf_dvd_natCard (R.subgroupOf U) (x := ⟨x, hxU⟩)
      (Subgroup.mem_subgroupOf.mpr hxR)
    exact this
  rw [Subgroup.orderOf_mk, hxo, hRU] at hdvd
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdvd)

variable (K : Type*) [Field K] [Finite K]

theorem eq_pslRange_of_index_eq_two (hK : IsOddPrimePower (Nat.card K)) (hq : 3 < Nat.card K)
    (M : Subgroup (PGL2 K)) (hM : M.index = 2) :
    M = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hcomm : commutator (PGL2 K) ≤ M := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨x, y, rfl⟩
    have hxy := Subgroup.mul_mem_iff_of_index_two hM (a := x * y) (b := x⁻¹ * y⁻¹)
    have hx := Subgroup.mul_mem_iff_of_index_two hM (a := x) (b := y)
    have hxi := Subgroup.mul_mem_iff_of_index_two hM (a := x⁻¹) (b := y⁻¹)
    have hinvx : x⁻¹ ∈ M ↔ x ∈ M := Subgroup.inv_mem_iff M
    have hinvy : y⁻¹ ∈ M ↔ y ∈ M := Subgroup.inv_mem_iff M
    have h1 : x * y * (x⁻¹ * y⁻¹) ∈ M := by
      rw [hxy, hx, hxi, hinvx, hinvy]
    have : ⁅x, y⁆ = x * y * (x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact h1
  rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hq] at *
  have hidx := pgl2_psl2Range_index_eq_two K hK
  rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hq] at hidx
  symm
  apply Subgroup.eq_of_le_of_card_ge hcomm
  have h1 := Subgroup.card_mul_index M
  have h2 := Subgroup.card_mul_index (commutator (PGL2 K))
  rw [hM] at h1
  rw [hidx] at h2
  omega

omit [Field K] [Finite K] in
theorem odd_card_of_isOddPrimePower (hK : IsOddPrimePower (Nat.card K)) : Odd (Nat.card K) := by
  rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
  rw [hcard]
  exact hpodd.pow

theorem commutator_index_eq_two (hK : IsOddPrimePower (Nat.card K)) (hq : 3 < Nat.card K) :
    (commutator (PGL2 K)).index = 2 := by
  rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hq]
  exact pgl2_psl2Range_index_eq_two K hK

theorem inner_torus (hK : IsOddPrimePower (Nat.card K)) (hq : 3 < Nat.card K) :
    ∃ (U : Subgroup (PGL2 K)) (x w : PGL2 K), IsCyclic U ∧
      (Nat.card U : ℤ) = Nat.card K - (if Nat.card K % 4 = 1 then 1 else -1) ∧
      x ∈ U ∧ x * x = 1 ∧ x ≠ 1 ∧ w ∉ U ∧ w * w = 1 ∧ (∀ u ∈ U, w * u * w⁻¹ = u⁻¹) ∧
      Subgroup.centralizer ({x} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w ∧
      x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  have hodd := odd_card_of_isOddPrimePower K hK
  have hJ := commutator_index_eq_two K hK hq
  have hJR := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hq
  obtain ⟨k, hk⟩ := hodd
  by_cases h1 : Nat.card K % 4 = 1
  · obtain ⟨U, x, w, hUc, hUcard, hxU, hx2, hx1, hwU, hw2, hinv, hC, hUR⟩ :=
      pgl2_split_torus_centralizer_data K ⟨k, hk⟩
    have hUJ : ¬ U ≤ commutator (PGL2 K) := by rw [hJR]; exact hUR ⟨k, hk⟩
    have hm : Even k := by
      refine ⟨k / 2, ?_⟩
      omega
    have hUcard' : Nat.card U = 2 * k := by rw [hUcard]; omega
    have hxJ := pgl2_torus_involution_mem_commutator hJ U hUc hxU hx2 hx1 hUcard' hm hUJ
    refine ⟨U, x, w, hUc, ?_, hxU, hx2, hx1, hwU, hw2, hinv, hC, hJR ▸ hxJ⟩
    rw [show (if Nat.card K % 4 = 1 then (1 : ℤ) else -1) = 1 by simp [h1], hUcard]
    push_cast [show 1 ≤ Nat.card K by omega]
    ring
  · obtain ⟨U, x, w, hUc, hUcard, hxU, hx2, hx1, hwU, hw2, hinv, hC, hUR⟩ :=
      pgl2_nonsplit_torus_centralizer_data K ⟨k, hk⟩
    have hUJ : ¬ U ≤ commutator (PGL2 K) := by rw [hJR]; exact hUR ⟨k, hk⟩
    have hm : Even (k + 1) := by
      refine ⟨(k + 1) / 2, ?_⟩
      omega
    have hUcard' : Nat.card U = 2 * (k + 1) := by rw [hUcard]; omega
    have hxJ := pgl2_torus_involution_mem_commutator hJ U hUc hxU hx2 hx1 hUcard' hm hUJ
    refine ⟨U, x, w, hUc, ?_, hxU, hx2, hx1, hwU, hw2, hinv, hC, hJR ▸ hxJ⟩
    rw [show (if Nat.card K % 4 = 1 then (1 : ℤ) else -1) = -1 by simp [h1], hUcard]
    push_cast
    ring

theorem outer_torus (hK : IsOddPrimePower (Nat.card K)) (hq : 3 < Nat.card K) :
    ∃ (U : Subgroup (PGL2 K)) (x w : PGL2 K), IsCyclic U ∧
      (Nat.card U : ℤ) = Nat.card K + (if Nat.card K % 4 = 1 then 1 else -1) ∧
      x ∈ U ∧ x * x = 1 ∧ x ≠ 1 ∧ w ∉ U ∧ w * w = 1 ∧ (∀ u ∈ U, w * u * w⁻¹ = u⁻¹) ∧
      Subgroup.centralizer ({x} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w ∧
      x ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hodd := odd_card_of_isOddPrimePower K hK
  have hR := pgl2_psl2Range_index_eq_two K hK
  obtain ⟨k, hk⟩ := hodd
  by_cases h1 : Nat.card K % 4 = 1
  · obtain ⟨U, x, w, hUc, hUcard, hxU, hx2, hx1, hwU, hw2, hinv, hC, hUR⟩ :=
      pgl2_nonsplit_torus_centralizer_data K ⟨k, hk⟩
    have hm : Odd (k + 1) := by
      refine ⟨k / 2, ?_⟩
      omega
    have hUcard' : Nat.card U = 2 * (k + 1) := by rw [hUcard]; omega
    refine ⟨U, x, w, hUc, ?_, hxU, hx2, hx1, hwU, hw2, hinv, hC,
      involution_not_mem_of_odd_half hR (hUR ⟨k, hk⟩) hUcard' hm hxU hx2 hx1⟩
    rw [show (if Nat.card K % 4 = 1 then (1 : ℤ) else -1) = 1 by simp [h1], hUcard]
    push_cast
    ring
  · obtain ⟨U, x, w, hUc, hUcard, hxU, hx2, hx1, hwU, hw2, hinv, hC, hUR⟩ :=
      pgl2_split_torus_centralizer_data K ⟨k, hk⟩
    have hm : Odd k := by
      refine ⟨k / 2, ?_⟩
      omega
    have hUcard' : Nat.card U = 2 * k := by rw [hUcard]; omega
    refine ⟨U, x, w, hUc, ?_, hxU, hx2, hx1, hwU, hw2, hinv, hC,
      involution_not_mem_of_odd_half hR (hUR ⟨k, hk⟩) hUcard' hm hxU hx2 hx1⟩
    rw [show (if Nat.card K % 4 = 1 then (1 : ℤ) else -1) = -1 by simp [h1], hUcard]
    push_cast [show 1 ≤ Nat.card K by omega]
    ring

omit [Field K] [Finite K] in
theorem centralizer_conj {X : Type*} [Group X] (g x : X) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set X) =
      (Subgroup.centralizer ({x} : Set X)).map (MulAut.conj g).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [h]
      _ = x * (g⁻¹ * y * g) := by group
  · intro h
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * y := by group

theorem card_centralizer_of_involution_mem (hK : IsOddPrimePower (Nat.card K))
    (hq : 3 < Nat.card K) {x : PGL2 K} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxR : x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) :
    (Nat.card (Subgroup.centralizer ({x} : Set (PGL2 K))) : ℤ) =
      2 * (Nat.card K - (if Nat.card K % 4 = 1 then 1 else -1)) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨U, y, w, hUc, hUcard, hyU, hy2, hy1, hwU, hw2, hinv, hC, hyR⟩ := inner_torus K hK hq
  have hJR := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hq
  obtain ⟨g, -, hg⟩ := pgl2_inner_involutions_conjugate hK hq (x := y) (y := x)
    (hJR ▸ hyR) ⟨hy1, by rw [pow_two]; exact hy2⟩ (hJR ▸ hxR) ⟨hx1, by rw [pow_two]; exact hx2⟩
  rw [← hg, centralizer_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective, hC,
    card_sup_zpowers_of_inv hwU hw2 hinv]
  push_cast
  rw [hUcard]

theorem centralizer_of_involution_not_mem (hK : IsOddPrimePower (Nat.card K))
    (hq : 3 < Nat.card K) {x : PGL2 K} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxR : x ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) :
    ∃ (U : Subgroup (PGL2 K)) (w : PGL2 K), IsCyclic U ∧
      (Nat.card U : ℤ) = Nat.card K + (if Nat.card K % 4 = 1 then 1 else -1) ∧
      x ∈ U ∧ w ∉ U ∧ w * w = 1 ∧ (∀ u ∈ U, w * u * w⁻¹ = u⁻¹) ∧
      Subgroup.centralizer ({x} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨U, y, w, hUc, hUcard, hyU, hy2, hy1, hwU, hw2, hinv, hC, hyR⟩ := outer_torus K hK hq
  have hJR := pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hq
  have hconj := pgl2_outer_involutions_conjugate K hK hq (a := y) (b := x)
    ⟨hy1, by rw [pow_two]; exact hy2⟩ ⟨hx1, by rw [pow_two]; exact hx2⟩ (hJR ▸ hyR) (hJR ▸ hxR)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  set φ := (MulAut.conj g).toMonoidHom
  refine ⟨U.map φ, g * w * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isCyclic_of_surjective ((U.equivMapOfInjective φ (MulAut.conj g).injective).toMonoidHom)
      (U.equivMapOfInjective φ (MulAut.conj g).injective).surjective
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hUcard
  · rw [← hg]
    exact ⟨y, hyU, rfl⟩
  · rintro ⟨u, hu, hu'⟩
    apply hwU
    have : u = w := by
      have h' : g * u * g⁻¹ = g * w * g⁻¹ := hu'
      simpa using h'
    exact this ▸ hu
  · calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  · rintro _ ⟨u, hu, rfl⟩
    change g * w * g⁻¹ * (g * u * g⁻¹) * (g * w * g⁻¹)⁻¹ = (g * u * g⁻¹)⁻¹
    calc g * w * g⁻¹ * (g * u * g⁻¹) * (g * w * g⁻¹)⁻¹ = g * (w * u * w⁻¹) * g⁻¹ := by group
      _ = (g * u * g⁻¹)⁻¹ := by rw [hinv u hu]; group
  · rw [← hg, centralizer_conj, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl

theorem card_mod_eight_of_not_dvd {q : ℕ} (hq : Odd q) (h16 : ¬ 16 ∣ q * (q ^ 2 - 1)) :
    q % 8 = 3 ∨ q % 8 = 5 := by
  obtain ⟨k, rfl⟩ := hq
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  ·
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exfalso
      apply h16
      refine ⟨(8 * i + 1) * (4 * i * i + i), ?_⟩
      have h : (2 * (i + i + (i + i)) + 1) ^ 2 - 1 = 16 * (4 * i * i + i) := by
        rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
        ring
      rw [h]
      ring
    · right
      omega
  · rcases Nat.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · left
      omega
    · exfalso
      apply h16
      refine ⟨(8 * i + 7) * (4 * i * i + 7 * i + 3), ?_⟩
      have h : (2 * (2 * (2 * i + 1) + 1) + 1) ^ 2 - 1 = 16 * (4 * i * i + 7 * i + 3) := by
        rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
        ring
      rw [h]
      ring

end CFSG.Semidihedral.FixedCoreNontrivial
