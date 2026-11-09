module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYGrp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSFiveLocal
public import Certificates.Certificate27261

public section

namespace CFSG.EvenSporadicStandard.HSStd.FiveY

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure X3Facts : Prop where
  «gens» : allLt hsGens.size (fun k => validA 100 hsGens[k]!) = true
  valid : validA 100 x3 = true
  cube : eqA 100 (compA 100 x3 (compA 100 x3 x3)) (idA 100) = true
  ne : (!eqA 100 x3 (idA 100)) = true

theorem x3Facts_of_check (h : x3OK = true) : X3Facts := by
  simp only [x3OK, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

noncomputable abbrev X3 : Equiv.Perm (Fin 100) := permOfArr 100 x3

theorem X3Facts.gens_valid (f : X3Facts) : ∀ k < hsGens.size, validA 100 hsGens[k]! = true :=
  fun _ hk => allLt_spec f.gens hk

theorem X3Facts.mem (f : X3Facts) : X3 ∈ hs100R := by
  have h0 := f.gens_valid 0 (by decide)
  have h1 := f.gens_valid 2 (by decide)
  have ra : Rep 100 (hs100Arr 0) hs100A := rep_of_validA h0
  have ru : Rep 100 (hs100Arr 15) hs100U := rep_of_validA h1
  have hx : Rep 100 x3 ((hs100A * hs100U) * (hs100A * hs100U)) :=
    rep_compA (rep_compA ra ru) (rep_compA ra ru)
  rw [X3, permOfArr_eq_of_rep hx]
  have hA : hs100A ∈ hs100R := Subgroup.subset_closure (by simp)
  have hU : hs100U ∈ hs100R := Subgroup.subset_closure (by simp)
  exact mul_mem (mul_mem hA hU) (mul_mem hA hU)

theorem X3Facts.order (f : X3Facts) : orderOf X3 = 3 := by
  have hr : Rep 100 x3 X3 := rep_of_validA f.valid
  have h3 : X3 * (X3 * X3) = 1 :=
    (eqA_iff (rep_compA hr (rep_compA hr hr)) rep_idA).1 f.cube
  have hne : X3 ≠ 1 := by
    intro h1
    have h2 := (eqA_iff hr rep_idA).2 h1
    have h4 := f.ne
    rw [h2] at h4
    exact absurd h4 (by simp)
  have hpow : X3 ^ 3 = 1 := by
    rw [pow_succ, pow_two]
    simpa [mul_assoc] using h3
  exact orderOf_eq_prime hpow hne

theorem X3Facts.card (f : X3Facts) :
    Nat.card ↥(hs100R ⊓ centralizer ({X3} : Set (Equiv.Perm (Fin 100)))) = 720 := by
  have ra : Rep 100 (hs100Arr 0) hs100A := rep_of_validA (f.gens_valid 0 (by decide))
  have ru : Rep 100 (hs100Arr 15) hs100U := rep_of_validA (f.gens_valid 2 (by decide))
  have hx : Rep 100 x3 ((hs100A * hs100U) * (hs100A * hs100U)) :=
    rep_compA (rep_compA ra ru) (rep_compA ra ru)
  rw [X3, permOfArr_eq_of_rep hx]
  exact Certificates.card_centralizer_X3

theorem X3Facts.card_P360 (f : X3Facts) :
    Nat.card ↥(hs100P ⊓ centralizer ({X3} : Set (Equiv.Perm (Fin 100)))) = 360 := by
  have ra : Rep 100 (hs100Arr 0) hs100A := rep_of_validA (f.gens_valid 0 (by decide))
  have ru : Rep 100 (hs100Arr 15) hs100U := rep_of_validA (f.gens_valid 2 (by decide))
  have hx : Rep 100 x3 ((hs100A * hs100U) * (hs100A * hs100U)) :=
    rep_compA (rep_compA ra ru) (rep_compA ra ru)
  rw [X3, permOfArr_eq_of_rep hx]
  exact Certificates.card_centralizer_X3P

section Conj


theorem hs100P_subgroupOf_index : (hs100P.subgroupOf hs100R).index = 2 := by
  have h1 := Subgroup.card_mul_index (hs100P.subgroupOf hs100R)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs100P_le_R).toEquiv, card_hs100P,
    card_hs100R] at h1
  omega

theorem mem_hs100P_of_order_three {x : Equiv.Perm (Fin 100)} (hxR : x ∈ hs100R)
    (hx : orderOf x = 3) : x ∈ hs100P := by
  have hn : (hs100P.subgroupOf hs100R).Normal := hs100P_normal_R
  have h2 := Subgroup.pow_index_mem (hs100P.subgroupOf hs100R) (⟨x, hxR⟩ : ↥hs100R)
  rw [hs100P_subgroupOf_index, mem_subgroupOf] at h2
  have h4 : x = (x ^ 2) ^ 2 := by
    rw [← pow_mul]
    calc x = x ^ 3 * x := by rw [← hx, pow_orderOf_eq_one, one_mul]
      _ = x ^ 4 := by rw [← pow_succ]
  rw [h4]
  exact pow_mem h2 2

theorem exists_conj_hs100R_three {a b : ↥hs100R} (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ c : ↥hs100R, c * a * c⁻¹ = b := by
  have hL : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  have ha' : orderOf (a : Equiv.Perm (Fin 100)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact ha
  have hb' : orderOf (b : Equiv.Perm (Fin 100)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hb
  obtain ⟨l, hl, hlab⟩ := Zassenhaus.hs_three_conj hL (mem_hs100P_of_order_three a.2 ha')
    (mem_hs100P_of_order_three b.2 hb') ha' hb'
  exact ⟨⟨l, hs100P_le_R hl⟩, Subtype.ext hlab⟩

theorem card_centralizer_hs100R_three {x : ↥hs100R}
    (hx : orderOf x = 3) : Nat.card ↥(centralizer ({x} : Set ↥hs100R)) = 720 := by
  have f := x3Facts_of_check Certificates.certificate27261
  set x₀ : ↥hs100R := ⟨X3, f.mem⟩ with hx₀
  have hx₀ord : orderOf x₀ = 3 := (Subgroup.orderOf_coe x₀).symm.trans f.order
  obtain ⟨c, hc⟩ := exists_conj_hs100R_three hx₀ord hx
  rw [← hc, card_centralizer_conj, card_centralizer_subtype]
  exact f.card

theorem card_centralizer_hs100P_three {x : Equiv.Perm (Fin 100)} (hxP : x ∈ hs100P)
    (hx : orderOf x = 3) : Nat.card ↥(hs100P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 100)))) =
      360 := by
  have f := x3Facts_of_check Certificates.certificate27261
  have hL : IsSporadic ↥hs100P .HS := ⟨hs100Equiv.symm⟩
  have hXP := mem_hs100P_of_order_three f.mem f.order
  obtain ⟨l, hl, hlx⟩ := Zassenhaus.hs_three_conj hL hXP hxP f.order hx
  have hc : (⟨l, hl⟩ : ↥hs100P) * ⟨X3, hXP⟩ * (⟨l, hl⟩ : ↥hs100P)⁻¹ = ⟨x, hxP⟩ := Subtype.ext hlx
  rw [← card_centralizer_subtype hs100P ⟨x, hxP⟩, ← hc, card_centralizer_conj,
    card_centralizer_subtype]
  exact f.card_P360

end Conj

end CFSG.EvenSporadicStandard.HSStd.FiveY
