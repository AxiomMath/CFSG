module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23CtBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56YExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf5Trans
public import CFSG.GH74.GLS.Bg.Statements

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

section Data


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem ct_data (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    IsPGroup 2 ↥(tightCore R) ∧ IsPGroup 2 ↥K' ∧ Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) ∧
      Nonempty (↥K' ≃* QuaternionGroup 2) ∧
      (∀ k ∈ tightCore R, ∀ k' ∈ K', k * k' = k' * k) ∧
      tightCore R ≤ Subgroup.centralizer ({e} : Set Y) ∧ K' ≤ Subgroup.centralizer ({e} : Set Y) ∧
      IsPGroup 2 ↥(tightCore R ⊔ K') := by
  have h2 := p23_members_isPGroup hP hc hno hα
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  obtain ⟨A, A', hA, hA', hAe, hA'e, hAA', -, -⟩ := exists_std_t hc
  have hAK : A = tightCore R :=
    (hA.2.2 (tightCore R) le_rfl (h2 _ hK) hA.1).symm
  have hAK' : A' = K' := (hA'.2.2 K' le_rfl (h2 _ hK') hA'.1).symm
  subst hAK hAK'
  exact ⟨h2 _ hK, h2 _ hK', lc_members_q8 hP hc hno hα _ hK, lc_members_q8 hP hc hno hα _ hK',
    lc_twins_commute hP hc hno hα, hAe, hA'e, hAA'⟩

theorem isSylow2In_self {J : Subgroup Y} (hJ : IsPGroup 2 ↥J) : IsSylow2In J J :=
  ⟨le_rfl, hJ, fun V' hV' _ h => le_antisymm hV' h⟩

theorem ct_htrans (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e)
    (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    ∀ a ∈ tightCore R, ∀ x ∈ tightCore R, ∀ b ∈ K', ∀ y ∈ K', a * a = t → x * x = t → b * b = t →
      y * y = t → ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g ∈ Subgroup.centralizer ({e} : Set Y) ∧
        g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y := by
  obtain ⟨h2K, h2K', -, -, -, hKe, hK'e, h2⟩ := ct_data hP hc hno hα
  intro a ha x hx b hb y hy haa hxx hbb hyy
  obtain ⟨g, hgt, hge, h1, h2'⟩ := fuse_stdC hP hc.std.perp hc.std.hK' hc.std.hne hc.data.he2
    hc.data.he1 hno (isSylow2In_self h2K) (isSylow2In_self h2K') hKe hK'e h2 ha hx hb hy haa hxx hbb
    hyy
  exact ⟨g, hgt, hge, h1, h2'⟩

theorem ct_hperm (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (conjSub c (tightCore R) = tightCore R ∨ conjSub c (tightCore R) = K') ∧
      (conjSub c K' = tightCore R ∨ conjSub c K' = K') := fun _ hc' => lc_perm hc hc'

end Data

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec
