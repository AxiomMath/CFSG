module

public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Quasithin.Recognition.CertU33Simple
public import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.Open.StatedDefs
public import CFSG.Blueprint.Catalog
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.Quasithin

theorem nonempty_mulEquiv_u33G_of_statedClassicalModel
    {K : Type} [Group K] (h : CFSG.Open.StatedClassicalModel K .PSU 3 3 1) :
    Nonempty (K ≃* U33G) := by
  have hL : CFSG.Blueprint.LieModel K .PSU 3 3 1 :=
    Or.inl ⟨by decide, (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 3 1)⟩
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel hL
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  exact ⟨e1.trans e2.symm⟩

theorem relIndex_inn_le_two_of_statedClassicalModel_psu33
    {K : Type} [Group K] (h : CFSG.Open.StatedClassicalModel K .PSU 3 3 1) :
    ((MulAut.conj : K →* MulAut K).range).relIndex ⊤ ≤ 2 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_u33G_of_statedClassicalModel h
  have hsimp : IsSimpleGroup K := by
    have := isSimpleGroup_u33Pres
    exact e.isSimpleGroup
  have hcard : Nat.card K = 6048 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_u33Pres
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcenter : Subgroup.center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hc | hc
    · exact hc
    · exfalso
      let _ : CommGroup K := Group.commGroupOfCenterEqTop hc
      have := IsSimpleGroup.prime_card (α := K)
      rw [hcard] at this
      norm_num at this
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    intro a b hab
    have hz : b⁻¹ * a ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h0 := congrArg (fun φ : MulAut K => φ g) hab
      simp only [MulAut.conj_apply] at h0
      have h1 : a * g = b * g * b⁻¹ * a := by rwa [mul_inv_eq_iff_eq_mul] at h0
      calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹ * a) := by group
        _ = b⁻¹ * (a * g) := by rw [h1]
        _ = b⁻¹ * a * g := by group
    rw [hcenter, Subgroup.mem_bot] at hz
    exact (inv_mul_eq_one.mp hz).symm
  have hI : Nat.card ((MulAut.conj : K →* MulAut K).range) = 6048 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]
  have hA : Nat.card (MulAut K) ≤ 12096 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact card_mulAut_u33Pres_le
  have h1 := Subgroup.card_mul_index (MulAut.conj : K →* MulAut K).range
  rw [Subgroup.relIndex_top_right]
  rw [hI] at h1
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
