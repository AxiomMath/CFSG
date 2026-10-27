module

public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3Y2Wire
public import CFSG.ClassicalInvolution.Q3.Q3Y2Twin
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinStmt
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3Y2
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinDatumOn TwinMFGenerationOn)
open scoped MatrixGroups


section Model

theorem eq_sl2Inv_of_central3 {M : Type} [Group M] {R₀ : Subgroup M}
    (e : R₀ ≃* SL(2, GaloisField 3 1)) {y : M} (hy : y ∈ R₀) (hc : ∀ r ∈ R₀, y * r = r * y)
    (hy1 : y ≠ 1) : y = sl2Inv e := by
  have hcR : (⟨y, hy⟩ : R₀) ∈ Subgroup.center R₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hcR) with h1 | h1
  · have h2 : (⟨y, hy⟩ : R₀) = 1 := e.injective (h1.trans (map_one e).symm)
    exact absurd (congrArg Subtype.val h2) hy1
  · exact congrArg Subtype.val (e.eq_symm_apply.mpr h1)

theorem twinMFGenerationOn3_of_strong {t : StatedLieTag} {n : ℕ} (hft : IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hne : ¬ (t = .PSL ∧ n = 2))
    (h : TwinStrong3 (fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D))
    (hdiff : ∀ {R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K}
      {x x' : (modelUniv t n 3 1 Nat.prime_three).K},
      TwinDatumOn t (modelUniv t n 3 1 Nat.prime_three) R R' x x' → x ≠ x') :
    TwinMFGenerationOn t (modelUniv t n 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R R' x x' hd a ha a' ha' hax ha'x' S hS
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
    (by norm_num) hft hadm hG2 hD4 hd.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
    (by norm_num) hft hadm hG2 hD4 hd.mem'
  have hx : x = sl2Inv e₁ := eq_sl2Inv_of_central3 e₁ hd.hx hd.cx hd.nx
  have hx' : x' = sl2Inv e₂ := eq_sl2Inv_of_central3 e₂ hd.hx' hd.cx' hd.nx'
  have hnc : ∀ {R₀ : Subgroup (modelUniv t n 3 1 Nat.prime_three).K},
      R₀ ∈ fundamentalSubgroups t (modelUniv t n 3 1 Nat.prime_three).D →
      ∀ r ∈ R₀, r ∈ Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K → r = 1 := by
    intro R₀ hR₀ r hr hrc
    refine ModelFacts.fundNoncentral_generic 3 t n 1 hft hadm hne R₀ hR₀ r hr fun y => ?_
    have := Subgroup.mem_center_iff.mp hrc y
    have e : r * y * r⁻¹ * y⁻¹ = 1 := by
      calc r * y * r⁻¹ * y⁻¹ = y * r * r⁻¹ * y⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e]
    exact one_mem _
  have hsq : a * a = x := by
    have hmem : a * a * x⁻¹ ∈ R := R.mul_mem (R.mul_mem ha ha) (R.inv_mem hd.hx)
    have h1 := hnc hd.mem _ hmem hax
    calc a * a = a * a * x⁻¹ * x := by group
      _ = x := by rw [h1, one_mul]
  have hsq' : a' * a' = x' := by
    have hmem : a' * a' * x'⁻¹ ∈ R' := R'.mul_mem (R'.mul_mem ha' ha') (R'.inv_mem hd.hx')
    have h1 := hnc hd.mem' _ hmem ha'x'
    calc a' * a' = a' * a' * x'⁻¹ * x' := by group
      _ = x' := by rw [h1, one_mul]
  have hsame : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈
      Subgroup.center (modelUniv t n 3 1 Nat.prime_three).K := by
    rw [← hx, ← hx']
    have e : x' * x⁻¹ = (x * x'⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hd.same
  have hne12 : sl2Inv e₂ * (sl2Inv e₁)⁻¹ ≠ 1 := by
    intro h1
    rw [← hx, ← hx'] at h1
    apply hdiff hd
    calc x = x' * x⁻¹ * x := by rw [h1]; group
      _ = x' := by group
  have key := h R hd.mem R' hd.mem' e₁ e₂ hd.ne hd.comm hsame hne12 a ha a' ha'
    (by rw [← hx]; exact hsq)
    (by rw [← hx']; exact hsq')
  rw [← hx] at key
  exact (le_top : S ≤ ⊤).trans key

theorem twinDatum_ne_psp2 {R R' : Subgroup (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    {x x' : (modelUniv .PSp 2 3 1 Nat.prime_three).K}
    (hd : TwinDatumOn .PSp (modelUniv .PSp 2 3 1 Nat.prime_three) R R' x x') : x ≠ x' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .PSp 2 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, fun h => by
      have : (3 : ℕ) ^ 1 = 2 := congrArg Prod.snd h
      omega⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hR := (Models.SymplecticPairs.exists_isLongRootSp2_iff h2 R).mpr
    ((Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm R).mp hd.mem)
  have hR' := (Models.SymplecticPairs.exists_isLongRootSp2_iff h2 R').mpr
    ((Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff hadm R').mp hd.mem')
  have hx2 : x * x = 1 := RouteD.SCRSp4.sp4_mul_self_eq_one_of_center hR hd.hx hd.cx
  have hx'2 : x' * x' = 1 := RouteD.SCRSp4.sp4_mul_self_eq_one_of_center hR' hd.hx' hd.cx'
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two h2 hd.hx
    (orderOf_eq_prime ((sq x).trans hx2) hd.nx)
  have hxi' : x' = i' := hi'.eq_of_orderOf_eq_two h2 hd.hx'
    (orderOf_eq_prime ((sq x').trans hx'2) hd.nx')
  intro hxx
  apply hd.ne
  rw [hi.eq_longRootGroup h2, hi'.eq_longRootGroup h2, ← hxi, ← hxi', hxx]

theorem twinMFGenerationOn3_psp2 :
    TwinMFGenerationOn .PSp (modelUniv .PSp 2 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : StatedLieAdmissible .PSp 2 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, fun h => by
      have : (3 : ℕ) ^ 1 = 2 := congrArg Prod.snd h
      omega⟩
  exact twinMFGenerationOn3_of_strong trivial hadm (by decide) (by decide) (by decide)
    (Q3Y2.twinStrong3_psp hadm) fun hd => twinDatum_ne_psp2 hd

end Model

end CFSG.ClassicalInvolution.Q3.Q3TLK
