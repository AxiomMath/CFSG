module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5SH8Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8PslChar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8PslField
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8PslContra

public section

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GH74.GLS.IVK
open CFSG.GorensteinWalter

theorem sec5pe8_psl2_trivial
    {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y) {F : Type} [Field F] [Finite F]
    {J : Subgroup Y} (hJ : Sec5SH8Linear P F J) {tb : Y} (htb : tb ∈ (P : Subgroup Y))
    (htb2 : orderOf tb = 2) (htbc : ∀ g ∈ (P : Subgroup Y), tb * g = g * tb)
    (κ : MulAut Y) (hodd : Odd (orderOf κ)) (hκP : ∀ x ∈ (P : Subgroup Y), κ x = x)
    (hfix : ∀ w ∈ J, w * tb = tb * w → Nat.Coprime (orderOf w) 6 → κ w = w) : κ = 1 := by
  classical
  haveI hJn : J.Normal := hJ.normal
  have hF : L2Field F := by
    refine ⟨?_, by have := hJ.five_le_card; omega⟩
    obtain ⟨p, n, hp, hpo, hn, hq⟩ := hJ.isOddPrimePower_card
    rw [hq]; exact hpo.pow
  have hJL : Nonempty (↥J ≃* L2 F) := by
    obtain ⟨ePSL⟩ := hJ.nonempty_equiv
    exact ⟨ePSL.trans (L2.equivPSL F).symm⟩
  haveI : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by have := hJ.five_le_card; omega)
  haveI : IsSimpleGroup (L2 F) := (L2.equivPSL F).isSimpleGroup
  haveI : IsSimpleGroup ↥J := hJL.some.isSimpleGroup
  by_contra hκne
  obtain ⟨κJ, hκJ, hord, hκ1⟩ := sec5pe8_restrict J hJ.centralizer_eq_bot κ
  have hκJne : κJ ≠ 1 := fun h => hκne (hκ1 h)
  have hoddJ : Odd (orderOf κJ) := Odd.of_dvd_nat hodd hord
  have hfixJ : ∀ x : ↥J, (x : Y) ∈ (P : Subgroup Y) → κJ x = x := by
    intro x hx
    apply Subtype.ext
    rw [hκJ x, hκP x hx]
  obtain ⟨e', r, x, hr, hr2, hx, hxr, hout⟩ :=
    sec5pe8_field_power hF P J hJL κJ hoddJ hfixJ hκJne
  have htbJ : tb ∈ J := hJ.central_involution_mem tb htb htb2 htbc
  let tJ : ↥J := ⟨tb, htbJ⟩
  let y : MulAut ↥J := MulAut.conj tJ
  have hy : y ∈ innDiagSub e' := innAut_le_innDiagSub e' ⟨tJ, rfl⟩
  have hy2sq : y ^ 2 = 1 := by
    have ho : orderOf tJ = 2 := by rw [← Subgroup.orderOf_coe tJ]; exact htb2
    have htJ2 : tJ * tJ = 1 := by rw [← sq, ← ho, pow_orderOf_eq_one]
    change (MulAut.conj tJ) ^ 2 = 1
    rw [sq, ← map_mul, htJ2, map_one]
  have hyne : y ≠ 1 := by
    intro hy1
    have hconj_all : ∀ j : ↥J, MulAut.conj tJ j = j := by
      intro j
      have := congrArg (fun f : MulAut ↥J => f j) hy1
      simpa [y] using this
    have htb_cent : tb ∈ Subgroup.centralizer (J : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h := hconj_all ⟨j, hj⟩
      rw [MulAut.conj_apply] at h
      have h' : (⟨j, hj⟩ : ↥J) * tJ = tJ * ⟨j, hj⟩ := by
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h.symm
      have := congrArg (fun z : ↥J => (z : Y)) h'
      simpa [Subgroup.coe_mul] using this
    have htb1 : tb = 1 := by
      rw [hJ.centralizer_eq_bot] at htb_cent
      exact Subgroup.mem_bot.mp htb_cent
    have : orderOf tb = 1 := by rw [htb1, orderOf_one]
    omega
  have hy2 : orderOf y = 2 := orderOf_eq_prime hy2sq hyne
  have hfix' : ∀ w : ↥J, Nat.Coprime (orderOf w) 6 → y w = w → κJ w = w := by
    intro w hcop hyw
    have hconj : MulAut.conj tJ w = w := by simpa [y] using hyw
    rw [MulAut.conj_apply] at hconj
    have htw : tJ * w = w * tJ := by
      rw [mul_inv_eq_iff_eq_mul] at hconj
      exact hconj
    have hcommY : (w : Y) * tb = tb * (w : Y) := by
      have := congrArg (fun z : ↥J => (z : Y)) htw
      simpa [Subgroup.coe_mul] using this.symm
    have hcopY : Nat.Coprime (orderOf (w : Y)) 6 := by
      rw [Subgroup.orderOf_coe]; exact hcop
    have hw := hfix (w : Y) w.2 hcommY hcopY
    apply Subtype.ext
    rw [hκJ w]
    exact hw
  exact (sec5pe8_contra hF e' hy hy2 hr hr2 hx hxr hout hfix').elim

end CFSG.OddStandard.SmallF3.Omega
