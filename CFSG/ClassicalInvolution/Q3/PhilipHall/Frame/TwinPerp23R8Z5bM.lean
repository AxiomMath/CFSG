module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z5bRed
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZGen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Cov
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Members
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z5bSwap
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsOD8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z6Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoKF
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoY

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ZTwo CFSG.ClassicalInvolution.Balance


namespace Z5b

section Cent

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem comm_e_of_cent (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hodd : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) {x : Y}
    (hx : ∀ l ∈ tightCore R ⊔ K', x * l = l * x) : x * e = e * x := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hx t (Subgroup.mem_sup_left hz.mem))
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (e_comm_t hc)
  have h1 : ∀ a ∈ ((tightCore R).subgroupOf C).map (F7I.piC C),
      F7I.piC C ⟨x, hxC⟩ * a = a * F7I.piC C ⟨x, hxC⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx k (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hk)))
  have h2 : ∀ a ∈ (K'.subgroupOf C).map (F7I.piC C),
      F7I.piC C ⟨x, hxC⟩ * a = a * F7I.piC C ⟨x, hxC⟩ := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hx k (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hk)))
  have hm := (p23MBar_proved (n := n)) hcit hP Y R S t K' W u e g hc (R56.p23_zstar_cu hT hc hZ)
    ⟨e, heC⟩ rfl (F7I.piC C ⟨x, hxC⟩) h1 h2
  have h3 : F7I.piC C (⟨x, hxC⟩ * ⟨e, heC⟩ * (⟨x, hxC⟩ : ↥C)⁻¹ * (⟨e, heC⟩ : ↥C)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hm' : F7I.piC C ⟨x, hxC⟩ * F7I.piC C ⟨e, heC⟩ = F7I.piC C ⟨e, heC⟩ * F7I.piC C ⟨x, hxC⟩ := hm
    rw [hm']
    group
  have h4 := (F7I.piC_eq_one_iff _).mp h3
  have h5 : oddCoreOf C = ⊥ := hodd
  rw [h5, Subgroup.mem_bot] at h4
  have h6 : x * e * x⁻¹ * e⁻¹ = 1 := by simpa using h4
  calc x * e = x * e * x⁻¹ * e⁻¹ * (e * x) := by group
    _ = e * x := by rw [h6, one_mul]

theorem le_rLayer_of_cent (hc : P23Cfg n Y R S t K' W u e g) {y : Y} (hy2 : y * y = 1) {J : Subgroup Y}
    (hJ : J ∈ Om R) (hJy : ∀ l ∈ J, y * l = l * y) : J ≤ rLayer (Om R) y := by
  have hJc : J ≤ Subgroup.centralizer ({y} : Set Y) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hJy l hl).symm
  have h := TwinDisc.coreAt_le_rLayer (hΩ_of hc) (ExactLayer.isPGroup_zpowers_of_sq_eq_one hy2)
    (mem_tqMembers3_of_le_centralizer hJ hJc)
  rwa [coreAt_eq_of_le_centralizer hJ hJc] at h

theorem cent_le_cent_s (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n) (hT : Thm4RTwinBelow 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hZ : u * e ∈ zStarOf (rLayer (Om R) u))
    (hodd : oddCoreIn (Subgroup.centralizer ({t} : Set Y)) = ⊥) {c' : Y}
    (hy2 : (c' * e * c'⁻¹) * (c' * e * c'⁻¹) = 1)
    (hyK : ∀ l ∈ tightCore R ⊔ K', (c' * e * c'⁻¹) * l = l * (c' * e * c'⁻¹)) {q : Y}
    (hq : q ∈ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y)) :
    q * (c'⁻¹ * (u * e) * c') = (c'⁻¹ * (u * e) * c') * q := by
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hKK : tightCore R ⊔ K' ≤ rLayer (Om R) (c' * e * c'⁻¹) :=
    sup_le (le_rLayer_of_cent hc hy2 hK fun l hl => hyK l (Subgroup.mem_sup_left hl))
      (le_rLayer_of_cent hc hy2 hc.std.hK'.1 fun l hl => hyK l (Subgroup.mem_sup_right hl))
  set x := c' * q * c'⁻¹ with hxdef
  have hxE : ∀ m ∈ rLayer (Om R) (c' * e * c'⁻¹), x * m = m * x := by
    intro m hm
    rw [rLayer_conj (R := R) c' e, mem_conjSub_iff] at hm
    have h1 := Subgroup.mem_centralizer_iff.mp hq _ hm
    calc x * m = c' * (q * (c'⁻¹ * m * c')) * c'⁻¹ := by rw [hxdef]; group
      _ = c' * ((c'⁻¹ * m * c') * q) * c'⁻¹ := by rw [h1]
      _ = m * x := by rw [hxdef]; group
  have hxe : x * e = e * x := comm_e_of_cent hcit hP hT hc hZ hodd fun l hl => hxE l (hKK hl)
  have hxu : x * u = u * x := hxE u (hKK hc.data.hu)
  have hxue : x * (u * e) = (u * e) * x := by
    calc x * (u * e) = (x * u) * e := by group
      _ = u * (x * e) := by rw [hxu]; group
      _ = (u * e) * x := by rw [hxe]; group
  have hq' : q = c'⁻¹ * x * c' := by rw [hxdef]; group
  rw [hq']
  calc c'⁻¹ * x * c' * (c'⁻¹ * (u * e) * c') = c'⁻¹ * (x * (u * e)) * c' := by group
    _ = c'⁻¹ * ((u * e) * x) * c' := by rw [hxue]
    _ = c'⁻¹ * (u * e) * c' * (c'⁻¹ * x * c') := by group

end Cent

section Act

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem y_act (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y)) (hyt : y * t = t * y)
    (hfield : ∀ l ∈ tightCore R ⊔ K', y * l * y⁻¹ * l⁻¹ ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)))
    {β : Finset (Fin 6)} {hβ : β.card = 4} {b₀ : Bool}
    (hlA : (secImg (Om R) e (tightCore R)).map D.φ = memBar β hβ b₀)
    (hlA' : (secImg (Om R) e K').map D.φ = memBar β hβ (!b₀)) (hz : D.φ (tbar hc) = zBar β hβ)
    (htA : tbar hc ∈ secImg (Om R) e (tightCore R)) (htA' : tbar hc ∈ secImg (Om R) e K') :
    ∃ w : Wr 6, D.toAEData.Acts (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) w ∧
      ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
  classical
  set σy := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ with hσy
  have hσΦ : ∀ L ∈ TwinDisc.secFam (Om R) e,
      L.map σy.toMonoidHom ∈ TwinDisc.secFam (Om R) e :=
    fun L hL => secAut_preserves hc ⟨y, hyC⟩ hL
  have hA := secImg_mem_secFam (twins_tq hc).1
  have hA' := secImg_mem_secFam (twins_tq hc).2
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
  · have hb' : b = !b₀ := by revert hb; cases b <;> cases b₀ <;> decide
    subst hb'
    exact key _ hfixA' (by rw [hlA']; exact hx)

theorem sq_centralizes (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y)) (hy2 : y * y = 1) {w : Wr 6}
    (hw : D.toAEData.Acts (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) w) :
    ∀ x ∈ TwinThinPf8.Hn 6, mkQ 6 (w * w) * x * (mkQ 6 (w * w))⁻¹ = x := by
  intro x hx
  rw [← D.range_eq] at hx
  obtain ⟨q, rfl⟩ := hx
  have h1 := (AEData.Acts.comp D.toAEData hw hw) q
  have h2 : (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ ∘
      TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) q = q := by
    show TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩
      (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ q) = q
    rw [← secAut_mul hc]
    have h3 : (⟨y, hyC⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) * ⟨y, hyC⟩ = 1 := Subtype.ext hy2
    rw [h3]
    exact secAut_one hc q
  rw [h2] at h1
  exact h1.symm

theorem conj_ne_of_swap (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {y : Y}
    (hyC : y ∈ Subgroup.centralizer ({e} : Set Y)) {w : Wr 6}
    (hw : D.toAEData.Acts (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) w)
    {J : Subgroup Y} {γ : Finset (Fin 6)} {hγ : γ.card = 4} {b₁ : Bool}
    (hlab : (secImg (Om R) e J).map D.φ = memBar γ hγ b₁)
    (hswap : (memBar γ hγ b₁).map (MulAut.conj (mkQ 6 w)).toMonoidHom = memBar γ hγ (!b₁)) :
    conjSub y J ≠ J := by
  intro h
  set σy := TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ with hσy
  have h1 : (secImg (Om R) e J).map σy.toMonoidHom = secImg (Om R) e J := by
    rw [hσy, TwinExitPf10.secImg_conj (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ J]
    show secImg (Om R) e (conjSub y J) = secImg (Om R) e J
    rw [h]
  have hcomp : D.φ.comp σy.toMonoidHom = (MulAut.conj (mkQ 6 w)).toMonoidHom.comp D.φ :=
    MonoidHom.ext fun a => by
      show D.φ (σy a) = mkQ 6 w * D.φ a * (mkQ 6 w)⁻¹
      exact hw a
  have h2 : ((secImg (Om R) e J).map σy.toMonoidHom).map D.φ =
      ((secImg (Om R) e J).map D.φ).map (MulAut.conj (mkQ 6 w)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  rw [h1, hlab, hswap] at h2
  cases b₁
  · exact memBar_true_ne_false (by norm_num) γ hγ h2.symm
  · exact memBar_true_ne_false (by norm_num) γ hγ h2

end Act

section Label

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem label_conj_g (hc : P23Cfg n Y R S t K' W u e g)
    (D : AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) {β : Finset (Fin 6)} {hβ : β.card = 4}
    {b₀ : Bool} (hlA : (secImg (Om R) e (tightCore R)).map D.φ = memBar β hβ b₀)
    (hlA' : (secImg (Om R) e K').map D.φ = memBar β hβ (!b₀)) :
    conjSub g (tightCore R) ∈ tqMembers3 (Om R) e ∧
      ∃ (γ : Finset (Fin 6)) (hγ : γ.card = 4) (b₁ : Bool),
        (secImg (Om R) e (conjSub g (tightCore R))).map D.φ = memBar γ hγ b₁ ∧
        zBar γ hγ ∈ memBar β hβ true ⊔ memBar β hβ false ∧ γ ≠ β := by
  classical
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers e) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, -, hb₁R, hb'R', -, -, hub, hne_ue⟩ := e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hKtq := (twins_tq hc).1
  have hK'tq := (twins_tq hc).2
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := by
    have : (⨆ X ∈ DSet (Om R) W, X) ≤ Subgroup.normalizer (W : Set Y) :=
      iSup₂_le fun X hX => hX.2
    exact this hd.hg
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := hNe hgN
  have hJ₃ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃e : conjSub g R₁ ≤ Subgroup.centralizer ({e} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgC (hR₁e hx)) (Subgroup.inv_mem _ hgC)
  have hJ₃tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) e :=
    ⟨hJ₃, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₃ ⟨conjSub g R₁, hR₃, hR₃e⟩⟩
  refine ⟨hJ₃tq, ?_⟩
  have hτ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hcoreB : b₁ ∈ TwinADescent.coreAt e (tightCore R) :=
    le_tightCore_of_isPGroup (le_inf hR₁.1 hR₁e) hR₁.2.1 hb₁R
  have hcoreB' : b' ∈ TwinADescent.coreAt e K' :=
    le_tightCore_of_isPGroup (le_inf hR₁'.1 hR₁'e) hR₁'.2.1 hb'R'
  have hztR : t ∈ R₁ := involution_mem_sylow hΩ hK hz hR₁
  have hcoreτ : u * e ∈ TwinADescent.coreAt e (conjSub g (tightCore R)) := by
    have := le_tightCore_of_isPGroup (le_inf hR₃.1 hR₃e) hR₃.2.1
      (conj_mem_conjSub hztR : g * t * g⁻¹ ∈ conjSub g R₁)
    rwa [hd.hgt] at this
  obtain ⟨b₁H, hb₁Hv, hb₁Hm⟩ := exists_hull_elt hKtq hcoreB
  obtain ⟨b'H, hb'Hv, hb'Hm⟩ := exists_hull_elt hK'tq hcoreB'
  obtain ⟨τH, hτHv, -⟩ := exists_hull_elt hJ₃tq hcoreτ
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) e) with hN
  have hv : ∀ x y : ↥(coreHull (Om R) e),
      (((x * y : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) *
          ((y : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) := fun _ _ => rfl
  have hext : ∀ x y : ↥(coreHull (Om R) e),
      ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        ((y : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  obtain ⟨eH, heH⟩ : ∃ eH : ↥(coreHull (Om R) e), eH = (b₁H * b'H)⁻¹ * τH := ⟨_, rfl⟩
  have heHv : ((eH : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = e := by
    have h1 : (((b₁H * b'H : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        b₁ * b' := by rw [hv, hb₁Hv, hb'Hv]
    have h2 : ((((b₁H * b'H)⁻¹ : ↥(coreHull (Om R) e)) :
        ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = (b₁ * b')⁻¹ := by rw [← h1]; rfl
    rw [heH]
    show ((((b₁H * b'H)⁻¹ : ↥(coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) *
      ((τH : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = e
    rw [h2, hτHv, hub]
    group
  have hrelH : τH = b₁H * b'H * eH := by
    rw [heH]; group
  have hecen : QuotientGroup.mk' N eH ∈ Subgroup.center (↥(coreHull (Om R) e) ⧸ N) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_mul, ← map_mul]
    congr 1
    apply hext
    rw [hv, hv, heHv]
    exact Subgroup.mem_centralizer_singleton_iff.mp y.1.2
  obtain ⟨htC, htY, hzA⟩ := isUniqueInvolution_secImg hΩ hc2' hKtq hz
  obtain ⟨htC', htY', hzA'⟩ := isUniqueInvolution_secImg hΩ hc2' hK'tq hz'
  obtain ⟨hτC, hτY, hτA⟩ := isUniqueInvolution_secImg hΩ hc2' hJ₃tq hτ
  have hτHeq : τH = ⟨⟨u * e, hτC⟩, hτY⟩ := hext _ _ hτHv
  have hτA' : IsUniqueInvolution (secImg (Om R) e (conjSub g (tightCore R))) (QuotientGroup.mk' N τH) := by
    rw [hτHeq]; exact hτA
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hc.std.hW
  have heW : e ∈ W := by
    have he : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) := by
      rw [← hd.he]; exact Subgroup.subset_closure rfl
    exact he.1
  have htτ : t * (u * e) = (u * e) * t := hWab t hd.hzW (u * e) (W.mul_mem hd.huW heW)
  have hτne : QuotientGroup.mk' N τH ≠ QuotientGroup.mk' N ⟨⟨t, htC⟩, htY⟩ := by
    intro h
    have := eq_of_mk_eq_of_involutions (x := τH) (y := ⟨⟨t, htC⟩, htY⟩)
      (hext _ _ (by rw [hv, hτHv]; exact hτ.sq)) (hext _ _ (by rw [hv]; exact hz.sq))
      (hext _ _ (by rw [hv, hv, hτHv]; exact htτ.symm)) h
    have hval := congrArg
      (fun x : ↥(coreHull (Om R) e) => ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) this
    exact hne_ue (hτHv.symm.trans hval)
  have hz'' : IsUniqueInvolution (secImg (Om R) e K') (QuotientGroup.mk' N ⟨⟨t, htC⟩, htY⟩) := by
    have : (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull (Om R) e)) = ⟨⟨t, htC'⟩, htY'⟩ := rfl
    rw [this]; exact hzA'
  have hB := secImg_mem_secFam hJ₃tq
  have hA := secImg_mem_secFam hKtq
  have hA' := secImg_mem_secFam hK'tq
  obtain ⟨γ, hγ, c, hlabB⟩ := D.label _ hB
  refine ⟨γ, hγ, c, hlabB, ?_, ?_⟩
  · have hφτ : D.φ (QuotientGroup.mk' N τH) = zBar γ hγ := D.map_eq_zBar hB hlabB hτA'
    have hφe : D.φ (QuotientGroup.mk' N eH) = 1 := D.toAEData.center_le_ker hecen
    have h1 : D.φ (QuotientGroup.mk' N b₁H) ∈ memBar β hβ b₀ := by
      rw [← hlA]; exact ⟨_, hb₁Hm, rfl⟩
    have h2' : D.φ (QuotientGroup.mk' N b'H) ∈ memBar β hβ (!b₀) := by
      rw [← hlA']; exact ⟨_, hb'Hm, rfl⟩
    have hprod : zBar γ hγ = D.φ (QuotientGroup.mk' N b₁H) * D.φ (QuotientGroup.mk' N b'H) := by
      rw [← hφτ, hrelH]
      simp only [map_mul, hφe, mul_one]
    rw [hprod]
    cases b₀
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left h2')
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right h2')
  · rintro rfl
    by_cases hcb : c = b₀
    · subst hcb
      have hBA := D.label_inj _ hB _ hA (hlabB.trans hlA.symm)
      rw [hBA] at hτA'
      exact hτne (hτA'.eq hzA)
    · have hcb' : c = !b₀ := by revert hcb; cases c <;> cases b₀ <;> decide
      subst hcb'
      have hBA := D.label_inj _ hB _ hA' (hlabB.trans hlA'.symm)
      rw [hBA] at hτA'
      exact hτne (hτA'.eq hz'')

end Label

end Z5b

section Final

variable {n : ℕ}

theorem p23E8ZCE_of_normT (hE : TwinThmEW.ThmEQ8) (hT : Thm4RTwinBelow 3 n)
    (hα : P23Alpha n) (hN : P23E8ZNormT n) (hG : P23E8ZGen n) :
    P23E8ZCE n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hZ hA6 Q hQ hQE
  have hTwo : P23Two n := p23Two_of_thmEQ8 hE hcit hP
  obtain ⟨hodd, -⟩ := p23E8Z_oddC_of_normT hE hT hα hN hcit hP hc hno hZ hA6
  obtain ⟨c', hc'C, hyc, hne, hfield⟩ := ZTwo.exists_y hT hcit hP hTwo hα hc hno hZ hA6
  obtain ⟨D⟩ := ZTwo.exists_cover hc hA6
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  set y := c' * e * c'⁻¹ with hydef
  have hyC : y ∈ Subgroup.centralizer ({e} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hyc
  have hy2 : y * y = 1 := by
    calc y * y = c' * (e * e) * c'⁻¹ := by rw [hydef]; group
      _ = 1 := by rw [hd.he2]; group
  have hct : c' * t * c'⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hc'C]
    group
  have hyt : y * t = t * y := by
    calc y * t = c' * e * c'⁻¹ * (c' * t * c'⁻¹) := by rw [hct]
      _ = c' * (e * t) * c'⁻¹ := by group
      _ = c' * (t * e) * c'⁻¹ := by rw [e_comm_t hc]
      _ = (c' * t * c'⁻¹) * (c' * e * c'⁻¹) := by group
      _ = t * y := by rw [hct]
  have hyK : ∀ l ∈ tightCore R ⊔ K', y * l = l * y := by
    intro l hl
    have h1 := hfield l hl
    have h2 : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥ := hodd
    rw [h2, Subgroup.mem_bot] at h1
    calc y * l = y * l * y⁻¹ * l⁻¹ * (l * y) := by group
      _ = l * y := by rw [h1, one_mul]
  have hQs : Q ≤ Subgroup.centralizer ({c'⁻¹ * (u * e) * c'} : Set Y) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Z5b.cent_le_cent_s hcit hP hT hc hZ hodd hy2 hyK (hQE hq))
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hJ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hL : conjSub c'⁻¹ (conjSub g (tightCore R)) ∈ Om R := hΩ.conjInvariant c'⁻¹ _ hJ
  have hτ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hs : IsUniqueInvolution (conjSub c'⁻¹ (conjSub g (tightCore R))) (c'⁻¹ * (u * e) * c') := by
    have := hτ.conj c'⁻¹
    rwa [inv_inv] at this
  have hyu : y * u = u * y := hyK u hd.hu
  have hse : (c'⁻¹ * (u * e) * c') * e = e * (c'⁻¹ * (u * e) * c') := by
    have h1 : (u * e) * y = y * (u * e) := by
      calc (u * e) * y = u * (y * e) := by rw [mul_assoc, ← hyc]
        _ = y * (u * e) := by rw [← mul_assoc, ← hyu, mul_assoc]
    have hey : e = c'⁻¹ * y * c' := by rw [hydef]; group
    calc (c'⁻¹ * (u * e) * c') * e = (c'⁻¹ * (u * e) * c') * (c'⁻¹ * y * c') := by rw [← hey]
      _ = c'⁻¹ * ((u * e) * y) * c' := by group
      _ = c'⁻¹ * (y * (u * e)) * c' := by rw [h1]
      _ = (c'⁻¹ * y * c') * (c'⁻¹ * (u * e) * c') := by group
      _ = e * (c'⁻¹ * (u * e) * c') := by rw [← hey]
  obtain ⟨β, hβ, b₀, hlA, hlA', hzβ, htA, htA', -⟩ := ZTwo.twin_labels hc D
  obtain ⟨w, hw, hcent⟩ := Z5b.y_act hc D hyC hyt hfield hlA hlA' hzβ htA htA'
  have hsign : Equiv.Perm.sign w.perm = -1 := by
    rcases ZTwo.classify hβ w hcent with h | hT1 | ⟨c₀, hc₀, hcen⟩
    · exact h
    · exfalso
      have hφ : ∀ q, D.φ (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩ q) = D.φ q := by
        intro q
        rw [hw q, hT1, one_mul, inv_one, mul_one]
      have hid := ZTwo.eq_of_trivial_mod_ker D.perfect
        (TwinExitPf6.secAut (Om R) e (hΩ_of hc) (hc2e_of hc) ⟨y, hyC⟩) (fun q => by
          apply D.toAEData.ker_le
          rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel])
      exact ZTwo.false_of_trivial hc D hyC hy2 hne hid
    · exact (ZTwo.false_of_zv hT hc hZ D hc'C hyC hy2 hyt hw hzβ hc₀ hcen).elim
  have hsq : mkQ 6 (w * w) = 1 := ClsO.mkQ_eq_one_of_centralizes _ (Z5b.sq_centralizes hc D hyC hy2 hw)
  obtain ⟨-, γ, hγ, b₁, hlabJ, hzγ, hγβ⟩ := Z5b.label_conj_g hc D hlA hlA'
  have hγ' : ∀ i, i ∉ β → i ∈ γ := (ZTwo.eq_or_subset_of_zBar_mem hβ hγ hzγ).resolve_left hγβ
  have hyJ : conjSub y (conjSub g (tightCore R)) ≠ conjSub g (tightCore R) :=
    Z5b.conj_ne_of_swap hc D hyC hw hlabJ (ZTwo.map_conj_memBar_of_odd hβ hγ w hcent hsign hsq hγ' b₁)
  have hLe : conjSub e (conjSub c'⁻¹ (conjSub g (tightCore R))) ≠
      conjSub c'⁻¹ (conjSub g (tightCore R)) := by
    intro h
    apply hyJ
    rw [hydef, conjSub_mul, conjSub_mul, h, conjSub_conjSub_inv]
  exact Z5b.p23_card_le_two hc (hG hcit hP Y R S t K' W u e g hc hno hZ hA6)
    (L7.omegaOneCenter_of_cover hc D) hL hs hse hLe hQ hQE hQs

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
