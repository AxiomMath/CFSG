module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoCase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9


public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo

section Act


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z : Subgroup Y}

theorem conj_mem_rLayer {a : Y} (haC : a ∈ Subgroup.centralizer ({e} : Set Y)) {b : Y}
    (hb : b ∈ rLayer (Om R) e) : a * b * a⁻¹ ∈ rLayer (Om R) e := by
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp haC
  have h2 : a * e * a⁻¹ = e := by rw [h1]; group
  have h3 : a * b * a⁻¹ ∈ conjSub a (rLayer (Om R) e) := conj_mem_conjSub hb
  rwa [← rLayer_conj, h2] at h3

@[expose] noncomputable def actHom (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) :
    ↥Z →* MulAut (SecQ R e) where
  toFun a := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨(a : Y), hZ.le_cent hZ.he a.2⟩
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ q
    exact TwinExitPf6.secAut_mk (hΩ_of hc) (hc2e_of hc) _ h h (by
      show _ = (1 : ↥(Subgroup.centralizer ({e} : Set Y))) * _ *
        (1 : ↥(Subgroup.centralizer ({e} : Set Y)))⁻¹
      group)
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    exact secAut_mul hc ⟨(a : Y), hZ.le_cent hZ.he a.2⟩ ⟨(b : Y), hZ.le_cent hZ.he b.2⟩ q

theorem centModE_of_act_eq_one (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z) {a : ↥Z}
    (ha : actHom hc hZ a = 1) : CentModE R e (a : Y) := by
  intro b hb
  have haC : (a : Y) ∈ Subgroup.centralizer ({e} : Set Y) := hZ.le_cent hZ.he a.2
  have hcb : (a : Y) * b * (a : Y)⁻¹ ∈ rLayer (Om R) e := conj_mem_rLayer haC hb
  have h1 := secAut_piE hc haC ⟨b, hb⟩ hcb
  have h2 : TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨(a : Y), haC⟩ (piE hc ⟨b, hb⟩) =
      piE hc ⟨b, hb⟩ := by
    have := congrArg (fun σ : MulAut (SecQ R e) => σ (piE hc ⟨b, hb⟩)) ha
    exact this
  rw [h2] at h1
  have h3 : piE hc (⟨(a : Y) * b * (a : Y)⁻¹, hcb⟩ * (⟨b, hb⟩ : ↥(rLayer (Om R) e))⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  exact (piE_eq_one_iff hc _).mp h3

theorem exists_cent_w (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {β : Finset (Fin 6)} {hβ : β.card = 4} {b₀ : Bool}
    (hlA : (secImg (Om R) e (tightCore R)).map D.φ = memBar β hβ b₀)
    (hlA' : (secImg (Om R) e K').map D.φ = memBar β hβ (!b₀)) (hz : D.φ (tbar hc) = zBar β hβ)
    (htA : tbar hc ∈ secImg (Om R) e (tightCore R)) (htA' : tbar hc ∈ secImg (Om R) e K') {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y)) (hyt : y * t = t * y)
    (hfield : ∀ l ∈ tightCore R ⊔ K', y * l * y⁻¹ * l⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :
    ∃ w : Wr 6, D.toAEData.Acts (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) w ∧
      ∀ (b : Bool), ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
  classical
  set σy := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ with hσy
  have hσΦ : ∀ L ∈ TwinDisc.secFam (Om R) e,
      L.map σy.toMonoidHom ∈ TwinDisc.secFam (Om R) e :=
    fun L hL => secAut_preserves hc ⟨y, hyC⟩ hL
  have hKtq := (twins_tq hc).1
  have hK'tq := (twins_tq hc).2
  have hA := secImg_mem_secFam hKtq
  have hA' := secImg_mem_secFam hK'tq
  have hE := (t_e_mem_rLayer hc).1
  have hσt : σy (tbar hc) = tbar hc := by
    have hyt' : y * t * y⁻¹ = t := by rw [hyt]; group
    have hcx : y * t * y⁻¹ ∈ rLayer (Om R) e := by rw [hyt']; exact hE
    have h1 := secAut_piE hc hyC ⟨t, hE⟩ hcx
    have h2 : (⟨y * t * y⁻¹, hcx⟩ : ↥(rLayer (Om R) e)) = ⟨t, hE⟩ := Subtype.ext hyt'
    exact h1.trans (congrArg (piE hc) h2)
  have hP2 := D.isPGroup_twin_sup hA hA' hlA hlA'
  have hσA := D.map_twin_mem hσΦ hσt hA hA' hlA hlA' hz (Or.inl rfl) htA
  have hσA' := D.map_twin_mem hσΦ hσt hA hA' hlA hlA' hz (Or.inr rfl) htA'
  have hfixA := secAut_fix_member hc hyC hfield (K := tightCore R) le_sup_left hP2 le_sup_left (by
    rcases hσA with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right)
  have hfixA' := secAut_fix_member hc hyC hfield (K := K') le_sup_right hP2 le_sup_right (by
    rcases hσA' with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right)
  obtain ⟨w, hw⟩ := D.toAEData.exists_wr σy hσΦ
  refine ⟨w, hw, fun b x hx => ?_⟩
  have key : ∀ (L : Subgroup (SecQ R e)), (∀ a ∈ L, σy a = a) → x ∈ L.map D.φ →
      mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    intro L hL hxL
    obtain ⟨a, ha, rfl⟩ := hxL
    rw [← hw a, hL a ha]
  by_cases hb : b = b₀
  · subst hb
    exact key _ hfixA (by rw [hlA]; exact hx)
  · have hb' : b = !b₀ := by cases b <;> cases b₀ <;> simp_all
    subst hb'
    exact key _ hfixA' (by rw [hlA']; exact hx)

end Act

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
