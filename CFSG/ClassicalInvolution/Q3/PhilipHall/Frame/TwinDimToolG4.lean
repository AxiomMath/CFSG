module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolG3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolG1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolG2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement



section G4

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

abbrev CU (u : Y) : Subgroup Y := Subgroup.centralizer ({u} : Set Y)

theorem gamma_u (hT : Thm4RTwinBelow 3 n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R u) (hYo : YOrth R u) :
    CU u ≤ gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (CU u) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨τH, vH, v', A, A', a₀, b₀, hτHv, hvHv, hv'form, hzv, T, J₁, hJ₁tq, hτ₁, hzA₁⟩ :=
    u_frame_full hc hP hno
  have hS := p23_q8Section hc.std.perp hd.hu2
  have hlt := secQ_card_lt hc.std.perp hd.hu1
  obtain ⟨-, hl, -⟩ := lifts_of_noExit hP hlt hS hno
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam (TwinDisc.secFam (Om R) u)) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgen : omegaGen (liftFam (TwinDisc.secFam (Om R) u)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u', hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  obtain ⟨tag, k, e', ⟨M⟩, hE4⟩ := e4_data_of_yOrth hΛ hgen hYo
  have hsplit := Q3T8.Asc77.T7L.e4_gen_of_model Q3T8.Asc77.e4TwinGen3_proved hΛ M hE4 T
  rw [← map_mul] at hsplit
  have hBel := B_isElemAbelian hc
  have hsq : ∀ x ∈ Subgroup.closure ({u * e, u, t} : Set Y), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  have huB : u ∈ Subgroup.closure ({u * e, u, t} : Set Y) := T7K.u_mem_B t u e
  have htB : t ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  have hueB : u * e ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.subset_closure (by simp)
  obtain ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩, ⟨hc1, hc2⟩, ⟨hd1, hd2⟩, ⟨he1, he2⟩⟩ := B_ne hc
  have hv'cases : v' = t ∨ v' = u * t := by
    rcases hzv with h | h
    · exact Or.inl h.symm
    · right
      rw [h, ← mul_assoc, hd.hu2, one_mul]
  have hv'B : v' ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rcases hv'cases with h | h <;> rw [h]
    · exact htB
    · exact Subgroup.mul_mem _ huB htB
  have hv'1 : v' ≠ 1 ∧ v' ≠ u := by
    rcases hv'cases with h | h <;> rw [h]
    · exact ⟨hb1, hb2⟩
    · exact ⟨hc1, hc2⟩
  have hτv1 : u * e * v' ≠ 1 ∧ u * e * v' ≠ u := by
    rcases hv'cases with h | h <;> rw [h]
    · exact ⟨hd1, hd2⟩
    · exact ⟨he1, he2⟩
  have hτvB : u * e * v' ∈ Subgroup.closure ({u * e, u, t} : Set Y) := Subgroup.mul_mem _ hueB hv'B
  have hτHv' : ((τH : ↥(CU u)) : Y) = u * e := hτHv
  have hvHv' : ((vH : ↥(CU u)) : Y) = v' := hvHv
  have hτvHv : (((τH * vH : ↥(coreHull (Om R) u)) : ↥(CU u)) : Y) = u * e * v' := by
    show ((τH : ↥(CU u)) : Y) * ((vH : ↥(CU u)) : Y) = u * e * v'
    rw [hτHv', hvHv']
  have hlayer := Asc77.T7L.layer_le_of_quot_gen (G := ↥(CU u)) (Y := coreHull (Om R) u)
    (s₁ := (τH : ↥(CU u))) (s₂ := (vH : ↥(CU u)))
    (s₃ := ((τH * vH : ↥(coreHull (Om R) u)) : ↥(CU u))) τH.2 vH.2 (τH * vH).2
    (Subtype.ext (by show ((τH : ↥(CU u)) : Y) * ((τH : ↥(CU u)) : Y) = 1
                     rw [hτHv']; exact hsq _ hueB))
    (Subtype.ext (by show ((vH : ↥(CU u)) : Y) * ((vH : ↥(CU u)) : Y) = 1
                     rw [hvHv']; exact hsq _ hv'B))
    (Subtype.ext (by
      show (((τH * vH : ↥(coreHull (Om R) u)) : ↥(CU u)) : Y) *
        (((τH * vH : ↥(coreHull (Om R) u)) : ↥(CU u)) : Y) = 1
      rw [hτvHv]; exact hsq _ hτvB))
    (fun h => ha1 (by have := congrArg Subtype.val h; rw [hτHv'] at this; exact this))
    (fun h => hv'1.1 (by have := congrArg Subtype.val h; rw [hvHv'] at this; exact this))
    (fun h => hτv1.1 (by have := congrArg Subtype.val h; rw [hτvHv] at this; exact this))
    hsplit
  have hodd : oddCoreOf (coreHull (Om R) u) ≤
      (gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (CU u)).comap (CU u).subtype := by
    rintro y ⟨m, hm, rfl⟩
    exact oddCore_C_le_gamma2 hc (oddCore_coreHull_le hΩ hc2' hm)
  have hpiece : ∀ {s : ↥(CU u)} {x : Y}, ((s : ↥(CU u)) : Y) = x →
      x ∈ Subgroup.closure ({u * e, u, t} : Set Y) → x ≠ 1 → x ≠ u →
      coreHull (Om R) u ⊓ Subgroup.centralizer ({s} : Set ↥(CU u)) ≤
        (gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (CU u)).comap (CU u).subtype := by
    intro s x hsx hxB hx1 hxu y hy
    have hcomm : ((y : ↥(CU u)) : Y) * x = x * ((y : ↥(CU u)) : Y) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hy.2
      rw [← hsx]
      exact congrArg Subtype.val this
    exact inf_cent_le_gamma2 hc hxB hx1 hxu
      ⟨(y : ↥(CU u)).2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hYΓ : coreHull (Om R) u ≤
      (gamma2 (Subgroup.closure ({u * e, u, t} : Set Y)) (CU u)).comap (CU u).subtype := by
    refine hlayer.trans ?_
    exact sup_le (sup_le (sup_le hodd (hpiece hτHv' hueB ha1 ha2))
      (hpiece hvHv' hv'B hv'1.1 hv'1.2)) (hpiece hτvHv hτvB hτv1.1 hτv1.2)
  have htrans := u_trans hT hc hno
  intro h hh
  have hJh : conjSub h J₁ ∈ tqMembers3 (Om R) u :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hh hJ₁tq
  have hτh : IsUniqueInvolution (conjSub h J₁) (h * (u * e) * h⁻¹) := hτ₁.conj h
  obtain ⟨hhC, hhY, hzh⟩ := isUniqueInvolution_secImg hΩ hc2' hJh hτh
  obtain ⟨x, hx⟩ := htrans _ (secImg_mem_secFam hJ₁tq) _ (secImg_mem_secFam hJh)
  have hxi : IsUniqueInvolution (secImg (Om R) u (conjSub h J₁))
      (x * QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) τH * x⁻¹) := by
    rw [← hx]; exact hzA₁.conj x
  have hconj := hxi.eq hzh
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(coreHull (Om R) u)) x
  have hcong := Asc77.T7L.mem_oddCore_of_mk_conj (G := ↥(CU u)) (Y := coreHull (Om R) u) τH.2
    (⟨⟨h * (u * e) * h⁻¹, hhC⟩, hhY⟩ : ↥(coreHull (Om R) u)).2 y hconj
  have ht'eq : (((⟨⟨h * (u * e) * h⁻¹, hhC⟩, hhY⟩ : ↥(coreHull (Om R) u)) : ↥(CU u))) =
      (⟨h, hh⟩ : ↥(CU u)) * (τH : ↥(CU u)) * (⟨h, hh⟩ : ↥(CU u))⁻¹ := by
    apply Subtype.ext
    show h * (u * e) * h⁻¹ = h * ((τH : ↥(CU u)) : Y) * h⁻¹
    rw [hτHv']
  rw [ht'eq] at hcong
  obtain ⟨y', hy', c, hc', hhc⟩ := Asc77.T7L.eq_mul_of_conj_mod (G := ↥(CU u)) (H := ⊤)
    (Y := coreHull (Om R) u) (N := oddCoreOf (coreHull (Om R) u)) le_top (oddCoreIn_le _)
    (oddCoreOf_odd_natCard _) (fun y hy => normalizer_oddCoreIn _ hy) τH.2
    (Subtype.ext (by show ((τH : ↥(CU u)) : Y) * ((τH : ↥(CU u)) : Y) = 1
                     rw [hτHv']; exact hsq _ hueB))
    (fun h1 => ha1 (by have := congrArg Subtype.val h1; rw [hτHv'] at this; exact this))
    (Set.mem_univ _ : (⟨h, hh⟩ : ↥(CU u)) ∈ (⊤ : Subgroup ↥(CU u))) y.2 hcong
  have hh' : h = ((y' : ↥(CU u)) : Y) * ((c : ↥(CU u)) : Y) := by
    have := congrArg Subtype.val hhc
    exact this
  rw [hh']
  refine Subgroup.mul_mem _ (hYΓ hy') ?_
  have hcomm : ((c : ↥(CU u)) : Y) * (u * e) = (u * e) * ((c : ↥(CU u)) : Y) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hc'.2
    rw [← hτHv']
    exact congrArg Subtype.val this
  exact inf_cent_le_gamma2 hc hueB ha1 ha2
    ⟨(c : ↥(CU u)).2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩

end G4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
