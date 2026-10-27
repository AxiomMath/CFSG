module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AXV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8AYMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ZTwoCase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8UE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Not9
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf11Vec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6bOdd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf22AE5Core

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
open CFSG.ClassicalInvolution.Balance


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

namespace AXV

section Odd

theorem e_quiet (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (heu : e ∈ Subgroup.centralizer ({u} : Set Y)) :
    ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨e, heu⟩ * y = y * oddQuotMk u ⟨e, heu⟩ := by
  obtain ⟨x, -, -, ψ, p, -, hxv, -, -, -, -, hψinj, -, hψx, -, -⟩ := AY.frame_psi hc hA5
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hHn : (coreHull (Om R) u).Normal := ⟨fun a ha g' => by
    have h := conj_mem_conjSub (n := g') ha
    rwa [conjSub_coreHull hΩ hc2 g'] at h⟩
  have hHs : IsSubnormal (coreHull (Om R) u) ⊤ :=
    CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hHn.isSubnormal
  have hVn : ((AE.vecSub 5).map (AE.mkQ 5)).Normal :=
    (AE.vecSub_normal (n := 5)).map (AE.mkQ 5) (QuotientGroup.mk'_surjective _)
  have hV2 : IsPGroup 2 ↥((AE.vecSub 5).map (AE.mkQ 5)) := by
    rintro ⟨_, a, ha, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    show (AE.mkQ 5 a) ^ 2 ^ 1 = 1
    rw [pow_one, pow_two, ← map_mul, AE.vecSub_mul_self ha, map_one]
  have hO2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u))
      (⟨(x : ↥(Subgroup.centralizer ({u} : Set Y))), x.2⟩ : ↥(coreHull (Om R) u))) := by
    refine ⟨((AE.vecSub 5).map (AE.mkQ 5)).comap ψ, hVn.comap ψ,
      hV2.comap_of_injective ψ hψinj, ?_⟩
    show ψ (QuotientGroup.mk x) ∈ (AE.vecSub 5).map (AE.mkQ 5)
    rw [hψx]
    exact Subgroup.mem_map_of_mem _ (AE.zOf_perm _)
  have hxC : u * e ∈ Subgroup.centralizer ({u} : Set Y) := by
    rw [← hxv]
    exact YGam.hcoeHom_mem_centralizer (Om R) u x
  have hxeq : (x : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨u * e, hxC⟩ := Subtype.ext hxv
  have hq : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      ∀ y ∈ L, oddQuotMk u ⟨u * e, hxC⟩ * y = y * oddQuotMk u ⟨u * e, hxC⟩ := by
    intro L hL
    have h := TL4.quiet_of_inO2_sub hHs x.2 hO2 L hL
    rw [hxeq] at h
    exact h
  have huC : u ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hucen : ∀ y : OddQuot u, oddQuotMk u ⟨u, huC⟩ * y = y * oddQuotMk u ⟨u, huC⟩ := by
    intro y
    obtain ⟨c, rfl⟩ : ∃ c, oddQuotMk u c = y := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm
  have he' : (⟨e, heu⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) = ⟨u, huC⟩ * ⟨u * e, hxC⟩ :=
    Subtype.ext (by show e = u * (u * e); rw [← mul_assoc, hd.hu2, one_mul])
  intro L hL y hy
  rw [he', map_mul, mul_assoc, hq L hL y hy, ← mul_assoc, hucen y, mul_assoc]

theorem alpha_eu (hα : P23Alpha n) (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    alphaOf (Subgroup.closure ({e, u} : Set Y)) = ⊥ := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have ht1 : t ≠ 1 := (Inner.isUniqueInvolution_core hC.datum).ne_one
  have heu : e ≠ u := by
    intro h
    apply ht1
    have h1 : g * t * g⁻¹ = 1 := by rw [hd.hgt, h, hd.hu2]
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hA : Subgroup.closure ({e, u} : Set Y) ≤ Subgroup.closure ({u * e, u, t} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · have h1 : u * x ∈ Subgroup.closure ({u * x, u, t} : Set Y) :=
        Subgroup.subset_closure (by simp)
      have h2 : u ∈ Subgroup.closure ({u * x, u, t} : Set Y) := Subgroup.subset_closure (by simp)
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
      rwa [inv_mul_cancel_left] at this
    · exact Subgroup.subset_closure (by simp)
  have hA2 := T7A.isElemAbelian2_closure_pair hd.he2 hd.hu2 hd.he1 hd.hu1 heu
    (hWab e heW u hd.huW)
  rw [(hα Y R S t K' W u e g hc (Or.inr (Or.inr (Or.inr hA5)))).2 _ hA hA2, hαb]

theorem ce_bot (hE : TwinThmEW.ThmEQ8) (hα : P23Alpha n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥) :
    oddCoreOf (Subgroup.centralizer ({e} : Set Y)) = ⊥ := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have heu : e ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab e heW u hd.huW)
  have hq := e_quiet hc hA5 heu
  have h1 : Balance.oddCoreIn (Subgroup.centralizer ({e} : Set Y)) ≤
      Balance.oddCoreIn (Subgroup.centralizer ({u} : Set Y)) :=
    TwinOdd.oddCent_le_of_alpha heu hd.he2 hd.he1 (alpha_eu hα hc hA5 hαb)
      fun L hL _ ⟨y, hy, hne⟩ => (hne (hq L hL y hy)).elim
  have h2 : Balance.oddCoreIn (Subgroup.centralizer ({u} : Set Y)) = ⊥ := by
    rw [← p23E8A_oddCoreIn_eq hc hA5 hαb]
    exact p23E8A_oddCoreIn_eq_bot hE hcit hP hc hA5 hαb
  exact le_bot_iff.mp (h2 ▸ h1)

theorem layer_bot {c : Y} (hΩ : HypOmegaGen (Om R))
    (hO : oddCoreOf (Subgroup.centralizer ({c} : Set Y)) = ⊥) :
    oddCoreOf (rLayer (Om R) c) = ⊥ := by
  have h := TwinDisc.oddCoreOf_le_of_normalizes (rLayer_le_centralizer (Om R) c)
    (fun g hg => conjSub_rLayer_eq hΩ hg)
  rw [hO] at h
  exact le_bot_iff.mp h

theorem hull_bot {c : Y} (hΩ : HypOmegaGen (Om R)) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hO : oddCoreOf (rLayer (Om R) c) = ⊥) :
    classicalInvolutionOddCore ↥(coreHull (Om R) c) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  have h1 := mem_oddCoreOf_coreLayer hΩ hc2 hh
  rw [show coreLayer (Om R) c = rLayer (Om R) c from
    TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2 h2, hO, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Subtype.ext h1)

end Odd

section Gen

theorem oddCoreIn_bot {J : Subgroup Y} (h2 : IsPGroup 2 J) : Balance.oddCoreIn J = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply TwinExitPf6.eq_one_of_odd_orderOf h2 (Balance.oddCoreIn_le J hx)
  exact (Balance.odd_card_oddCoreIn J).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)

theorem le_cent_of_tq {c : Y} {J : Subgroup Y} (hJ : J ∈ tqMembers3 (Om R) c)
    (h2 : IsPGroup 2 J) : J ≤ Subgroup.centralizer ({c} : Set Y) := by
  intro x hx
  have h := hJ.2.2 x hx
  rw [oddCoreIn_bot h2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact Subgroup.mem_centralizer_singleton_iff.mpr h.symm

theorem tq_of_le_cent {c : Y} {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJc : J ≤ Subgroup.centralizer ({c} : Set Y)) : J ∈ tqMembers3 (Om R) c :=
  ⟨hJ, CFSG.ClassicalInvolution.Asc77.ExactLayer.mem_trivialOnQuot_of_le_centralizer hJc⟩

theorem bool_eq_of_not_eq_not {b b' : Bool} (h : ¬ b' = !b) : b' = b := by
  cases b <;> cases b' <;> simp_all

theorem bool_eq_not_of_ne {b b' : Bool} (h : ¬ b' = b) : b' = !b := by
  cases b <;> cases b' <;> simp_all

end Gen

section Y3

theorem conj_e_comm (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e) (hA5 : SecAE R u 5)
    (hA6 : SecAE R e 6) (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥) {c d : Y}
    (hcC : c ∈ Subgroup.centralizer ({t} : Set Y))
    (hdC : d ∈ Subgroup.centralizer ({t} : Set Y)) :
    (c * e * c⁻¹) * (d * e * d⁻¹) = (d * e * d⁻¹) * (c * e * c⁻¹) := by
  have hΦ := p23E8PhiAE_of_comm p23E8UEComm_proved hcit hP Y R S t K' W u e g hc hno hA5 hA6
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hWab e heW t hd.hzW)
  have hmem_gen : ∀ x : ↥C, (∃ c ∈ C, (x : Y) = c * (1 * e) * c⁻¹) →
      F7I.piC C x ∈ p23ABar t 1 e :=
    fun x hx => Subgroup.subset_closure ⟨x, hx, rfl⟩
  set xc : ↥C := ⟨c * e * c⁻¹, C.mul_mem (C.mul_mem hcC heC) (C.inv_mem hcC)⟩ with hxc
  set xd : ↥C := ⟨d * e * d⁻¹, C.mul_mem (C.mul_mem hdC heC) (C.inv_mem hdC)⟩ with hxd
  have h1 := hmem_gen xc ⟨c, hcC, by simp [xc]⟩
  have h2 := hmem_gen xd ⟨d, hdC, by simp [xd]⟩
  have hcomm := hΦ _ h1 _ h2
  have h4 : F7I.piC C (xc * xd * xc⁻¹ * xd⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have h5 := (F7I.piC_eq_one_iff _).mp h4
  rw [hOt, Subgroup.mem_bot] at h5
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h5
  exact commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact h5)

theorem y_spec (hZ8 : P23E8AZ8 n) (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e) (hA5 : SecAE R u 5)
    (hA6 : SecAE R e 6) (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    ∃ y ∈ rLayer (Om R) u, y * t = t * y ∧ IsPGroup 3 (Subgroup.zpowers y) ∧
      y * e * y⁻¹ ≠ e ∧ y ^ 3 * e = e * y ^ 3 := by
  obtain ⟨y, hyY, hyt, hy3, hmove⟩ := AY.exists_y hc hA5
  obtain ⟨y₀, -, -, -, hcls⟩ := hZ8 hcit hP Y R S t K' W u e g hc hno hA5 hA6
  have hyC : y ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have h1 : y * e * y⁻¹ ≠ e := by
    have := hmove 1 (Subgroup.one_mem _)
    simpa using this
  have hS : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), c * e * c⁻¹ = e ∨
      c * e * c⁻¹ = y₀ * e * y₀⁻¹ ∨ c * e * c⁻¹ = y₀ ^ 2 * e * (y₀ ^ 2)⁻¹ := by
    intro c hc'
    obtain ⟨i, hi, o, ho, he⟩ := hcls c hc'
    rw [hOt, Subgroup.mem_bot] at ho
    subst ho
    simp only [one_mul, inv_one, mul_one] at he
    interval_cases i
    · left; simpa using he
    · right; left; simpa using he
    · right; right; exact he
  have hodd : Odd (orderOf y) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hy3 ⟨y, Subgroup.mem_zpowers y⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have hy2 : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have hf1 : y * e * y⁻¹ ≠ e := h1
  have hf2 : y ^ 2 * e * (y ^ 2)⁻¹ ≠ y * e * y⁻¹ := by
    intro h
    apply h1
    have h' : y⁻¹ * (y ^ 2 * e * (y ^ 2)⁻¹) * y = y⁻¹ * (y * e * y⁻¹) * y := by rw [h]
    calc y * e * y⁻¹ = y⁻¹ * (y ^ 2 * e * (y ^ 2)⁻¹) * y := by group
      _ = y⁻¹ * (y * e * y⁻¹) * y := h'
      _ = e := by group
  have hf3 : y ^ 2 * e * (y ^ 2)⁻¹ ≠ e := by
    intro h
    apply h1
    have hc2 : y ^ 2 * e = e * y ^ 2 := by
      calc y ^ 2 * e = y ^ 2 * e * (y ^ 2)⁻¹ * y ^ 2 := by group
        _ = e * y ^ 2 := by rw [h]
    have hcm : Commute (y ^ 2) e := hc2
    have hcy : Commute y e := by rw [hy2]; exact hcm.pow_left _
    rw [hcy.eq, mul_inv_cancel_right]
  have hf4 : y ^ 3 * e * (y ^ 3)⁻¹ ≠ y * e * y⁻¹ := by
    intro h
    apply hf3
    have h' : y⁻¹ * (y ^ 3 * e * (y ^ 3)⁻¹) * y = y⁻¹ * (y * e * y⁻¹) * y := by rw [h]
    calc y ^ 2 * e * (y ^ 2)⁻¹ = y⁻¹ * (y ^ 3 * e * (y ^ 3)⁻¹) * y := by group
      _ = y⁻¹ * (y * e * y⁻¹) * y := h'
      _ = e := by group
  have hf5 : y ^ 3 * e * (y ^ 3)⁻¹ ≠ y ^ 2 * e * (y ^ 2)⁻¹ := by
    intro h
    apply hf2
    have h' : y⁻¹ * (y ^ 3 * e * (y ^ 3)⁻¹) * y = y⁻¹ * (y ^ 2 * e * (y ^ 2)⁻¹) * y := by rw [h]
    calc y ^ 2 * e * (y ^ 2)⁻¹ = y⁻¹ * (y ^ 3 * e * (y ^ 3)⁻¹) * y := by group
      _ = y⁻¹ * (y ^ 2 * e * (y ^ 2)⁻¹) * y := h'
      _ = y * e * y⁻¹ := by group
  have hy3e : y ^ 3 * e * (y ^ 3)⁻¹ = e := by
    rcases hS _ hyC with h1' | h1' | h1' <;>
    rcases hS _ (Subgroup.pow_mem _ hyC 2) with h2' | h2' | h2' <;>
    rcases hS _ (Subgroup.pow_mem _ hyC 3) with h3' | h3' | h3' <;>
    first
    | exact h3'
    | exact absurd h1' hf1
    | exact absurd h2' hf3
    | exact absurd (h3'.trans h1'.symm) hf4
    | exact absurd (h3'.trans h2'.symm) hf5
    | exact absurd (h2'.trans h1'.symm) hf2
  refine ⟨y, hyY, hyt, hy3, h1, ?_⟩
  calc y ^ 3 * e = y ^ 3 * e * (y ^ 3)⁻¹ * y ^ 3 := by group
    _ = e * y ^ 3 := by rw [hy3e]

theorem conj_e_cent_twins (hc : P23Cfg n Y R S t K' W u e g)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) {c : Y} (hcC : c ∈ Subgroup.centralizer ({t} : Set Y)) :
    ∀ k ∈ tightCore R ⊔ K', (c * e * c⁻¹) * k = k * (c * e * c⁻¹) := by
  obtain ⟨hK, hK'⟩ := ZTwo.twins_tq hc
  have heK := le_cent_of_tq hK (h2grp _ hK.1)
  have heK' := le_cent_of_tq hK' (h2grp _ hK'.1)
  have key : ∀ k : Y, (c⁻¹ * k * c ∈ tightCore R ∨ c⁻¹ * k * c ∈ K') →
      k ∈ Subgroup.centralizer ({c * e * c⁻¹} : Set Y) := by
    intro k hk
    have h1 : (c⁻¹ * k * c) * e = e * (c⁻¹ * k * c) := by
      rcases hk with hk | hk
      · exact Subgroup.mem_centralizer_singleton_iff.mp (heK hk)
      · exact Subgroup.mem_centralizer_singleton_iff.mp (heK' hk)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k * (c * e * c⁻¹) = c * ((c⁻¹ * k * c) * e) * c⁻¹ := by group
      _ = c * (e * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
      _ = c * e * c⁻¹ * k := by group
  have hmem : ∀ (H : Subgroup Y) (k : Y), k ∈ H → c⁻¹ * k * c ∈ conjSub c⁻¹ H := by
    intro H k hk
    have := conj_mem_conjSub (n := c⁻¹) hk
    simpa using this
  have hle : tightCore R ⊔ K' ≤ Subgroup.centralizer ({c * e * c⁻¹} : Set Y) := by
    refine sup_le (fun k hk => key k ?_) (fun k hk => key k ?_)
    · rcases p23_conj_twins hc (Subgroup.inv_mem _ hcC) with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; rw [← h1]; exact hmem _ k hk
      · right; rw [← h1]; exact hmem _ k hk
    · rcases p23_conj_twins hc (Subgroup.inv_mem _ hcC) with ⟨-, h1⟩ | ⟨-, h1⟩
      · right; rw [← h1]; exact hmem _ k hk
      · left; rw [← h1]; exact hmem _ k hk
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm

end Y3

section ZSub

@[expose] def zSub (t e y : Y) : Subgroup Y :=
  Subgroup.closure ({t, e, y * e * y⁻¹, y⁻¹ * e * y} : Set Y)

theorem gen_mem_zSub {t e y : Y} :
    t ∈ zSub t e y ∧ e ∈ zSub t e y ∧ y * e * y⁻¹ ∈ zSub t e y ∧ y⁻¹ * e * y ∈ zSub t e y :=
  ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩

theorem zSub_props (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e) (hA5 : SecAE R u 5)
    (hA6 : SecAE R e 6) (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) {y : Y} (hyt : y * t = t * y)
    (hy3 : y ^ 3 * e = e * y ^ 3) :
    (∀ a ∈ zSub t e y, ∀ b ∈ zSub t e y, a * b = b * a) ∧ (∀ a ∈ zSub t e y, a * a = 1) ∧
      zSub t e y ≤ Subgroup.centralizer ({t} : Set Y) ∧
      zSub t e y ≤ Subgroup.centralizer ({e} : Set Y) ∧
      (∀ z ∈ zSub t e y, y * z * y⁻¹ ∈ zSub t e y) ∧
      (∀ z ∈ zSub t e y, y⁻¹ * z * y ∈ zSub t e y) ∧
      (∀ z ∈ zSub t e y, ∀ k ∈ tightCore R ⊔ K', z * k = k * z) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
  have hyC' : y⁻¹ ∈ C := C.inv_mem hyC
  have h1C : (1 : Y) ∈ C := C.one_mem
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have heC : e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hWab e heW t hd.hzW)
  set X : Set Y := {t, e, y * e * y⁻¹, y⁻¹ * e * y} with hXdef
  have hgen : ∀ x ∈ X, x = t ∨ ∃ c ∈ C, x = c * e * c⁻¹ := by
    rintro x (rfl | rfl | rfl | rfl)
    · left; rfl
    · right; exact ⟨1, h1C, by group⟩
    · right; exact ⟨y, hyC, rfl⟩
    · right; exact ⟨y⁻¹, hyC', by group⟩
  have htcen : ∀ x ∈ X, x ∈ C := by
    intro x hx
    rcases hgen x hx with rfl | ⟨c, hc', rfl⟩
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact C.mul_mem (C.mul_mem hc' heC) (C.inv_mem hc')
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    intro a ha b hb
    rcases hgen a ha with rfl | ⟨c, hc', rfl⟩
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (htcen b hb)).symm
    · rcases hgen b hb with rfl | ⟨d, hd', rfl⟩
      · exact Subgroup.mem_centralizer_singleton_iff.mp (htcen _ ha)
      · exact conj_e_comm hcit hP hc hno hA5 hA6 hOt hc' hd'
  have hX2 : ∀ a ∈ X, a * a = 1 := by
    intro a ha
    rcases hgen a ha with rfl | ⟨c, -, rfl⟩
    · exact hz.sq
    · calc c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ := by group
        _ = 1 := by rw [hd.he2, mul_one, mul_inv_cancel]
  have hab : ∀ a ∈ zSub t e y, ∀ b ∈ zSub t e y, a * b = b * a := F7I.closure_comm hXc
  have hsq : ∀ a ∈ zSub t e y, a * a = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem x hx => exact hX2 x hx
    | one => simp
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab b hb a ha]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a _ iha =>
      rw [← mul_inv_rev, iha, inv_one]
  have heZ : e ∈ zSub t e y := gen_mem_zSub.2.1
  have hZC : zSub t e y ≤ C := (Subgroup.closure_le _).mpr htcen
  have hZe : zSub t e y ≤ Subgroup.centralizer ({e} : Set Y) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hab a ha e heZ)
  have hy3' : y * (y * (y * e)) = e * (y * (y * y)) := by
    simpa [pow_succ, mul_assoc] using hy3
  have hy2 : y * (y * e * y⁻¹) * y⁻¹ = y⁻¹ * e * y := by
    calc y * (y * e * y⁻¹) * y⁻¹ = y⁻¹ * (y * (y * (y * e))) * (y⁻¹ * (y⁻¹ * y⁻¹)) * y := by
          group
      _ = y⁻¹ * (e * (y * (y * y))) * (y⁻¹ * (y⁻¹ * y⁻¹)) * y := by rw [hy3']
      _ = y⁻¹ * e * y := by group
  have hy2' : y⁻¹ * (y⁻¹ * e * y) * y = y * e * y⁻¹ := by
    calc y⁻¹ * (y⁻¹ * e * y) * y = y * (y⁻¹ * (y⁻¹ * y⁻¹)) * (e * (y * (y * y))) * y⁻¹ := by
          group
      _ = y * (y⁻¹ * (y⁻¹ * y⁻¹)) * (y * (y * (y * e))) * y⁻¹ := by rw [hy3']
      _ = y * e * y⁻¹ := by group
  have hyt' : y * t * y⁻¹ = t := by rw [hyt, mul_inv_cancel_right]
  have hyt'' : y⁻¹ * t * y = t := by
    calc y⁻¹ * t * y = y⁻¹ * (t * y) := by group
      _ = y⁻¹ * (y * t) := by rw [hyt]
      _ = t := by group
  have hconj : ∀ c : Y, (∀ x ∈ X, c * x * c⁻¹ ∈ zSub t e y) →
      ∀ z ∈ zSub t e y, c * z * c⁻¹ ∈ zSub t e y := by
    intro c hcX z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx => exact hcX x hx
    | one => simp [Subgroup.one_mem]
    | mul a b _ _ ha hb =>
      have := Subgroup.mul_mem _ ha hb
      rwa [show c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ by group] at this
    | inv a _ ha =>
      have := Subgroup.inv_mem _ ha
      rwa [show (c * a * c⁻¹)⁻¹ = c * a⁻¹ * c⁻¹ by group] at this
  obtain ⟨htZ, -, heyZ, heyZ'⟩ := (gen_mem_zSub : t ∈ zSub t e y ∧ _)
  have hyZ : ∀ z ∈ zSub t e y, y * z * y⁻¹ ∈ zSub t e y := by
    refine hconj y ?_
    intro x hx
    simp only [hXdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h <;> rw [h]
    · rw [hyt']; exact htZ
    · exact heyZ
    · rw [hy2]; exact heyZ'
    · rw [show y * (y⁻¹ * e * y) * y⁻¹ = e by group]; exact heZ
  have hyZ' : ∀ z ∈ zSub t e y, y⁻¹ * z * y ∈ zSub t e y := by
    have h := hconj y⁻¹ ?_
    · intro z hz; simpa using h z hz
    intro x hx
    simp only [hXdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h <;> rw [h, inv_inv]
    · rw [hyt'']; exact htZ
    · exact heyZ'
    · rw [show y⁻¹ * (y * e * y⁻¹) * y = e by group]; exact heZ
    · rw [hy2']; exact heyZ
  have hKt : tightCore R ⊔ K' ≤ C :=
    sup_le (le_centralizer_of_unique hz) (le_centralizer_of_unique hz')
  have hcentK : ∀ x ∈ X, ∀ k ∈ tightCore R ⊔ K', x * k = k * x := by
    intro x hx k hk
    rcases hgen x hx with rfl | ⟨c, hc', rfl⟩
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hKt hk)).symm
    · exact conj_e_cent_twins hc h2grp hc' k hk
  have hZK : ∀ z ∈ zSub t e y, ∀ k ∈ tightCore R ⊔ K', z * k = k * z := by
    intro z hz k hk
    have hle : zSub t e y ≤ Subgroup.centralizer ({k} : Set Y) := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcentK x hx k hk)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hz)
  exact ⟨hab, hsq, hZC, hZe, hyZ, hyZ', hZK⟩

end ZSub

section Cover

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TC.Thin

abbrev vBar : Subgroup (AEQ 6) := (vecSub 6).map (mkQ 6)

theorem vBar_normal : vBar.Normal :=
  (vecSub_normal (n := 6)).map (mkQ 6) (QuotientGroup.mk'_surjective _)

theorem vBar_sq {m : AEQ 6} (hm : m ∈ vBar) : m * m = 1 := by
  obtain ⟨a, ha, rfl⟩ := hm
  rw [← map_mul, vecSub_mul_self ha, map_one]

theorem zBar_mem_vBar (γ : Finset (Fin 6)) (hγ : γ.card = 4) : zBar γ hγ ∈ vBar :=
  Subgroup.mem_map_of_mem _ (zOf_perm _)

noncomputable def phiE (hc : P23Cfg n Y R S t K' W u e g)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) :
    ↥(rLayer (Om R) e) →* AEQ 6 :=
  D.φ.comp (ZTwo.piE hc)

noncomputable def qE (hc : P23Cfg n Y R S t K' W u e g)
    (D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)) : Subgroup Y :=
  (vBar.comap (phiE hc D)).map (rLayer (Om R) e).subtype

variable {hc : P23Cfg n Y R S t K' W u e g}
  {D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)}

theorem mem_qE {x : Y} :
    x ∈ qE hc D ↔ ∃ hx : x ∈ rLayer (Om R) e, D.φ (ZTwo.piE hc ⟨x, hx⟩) ∈ vBar := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem qE_le : qE hc D ≤ rLayer (Om R) e := Subgroup.map_subtype_le _

theorem piE_inj (hOE : oddCoreOf (rLayer (Om R) e) = ⊥) : Function.Injective (ZTwo.piE hc) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker, ZTwo.piE_eq_one_iff, hOE, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (Subtype.ext hx)

theorem ker_sq {Q : Type} [Group Q] {Φ : Set (Subgroup Q)} [Finite Q]
    (D' : ZTwo.AECover Q Φ) : ∀ k ∈ D'.φ.ker, k * k = 1 := by
  intro k hk
  have hcard := D'.ker_card
  have hpos : 0 < Nat.card D'.φ.ker := Nat.card_pos
  have h1 : (⟨k, hk⟩ : D'.φ.ker) ^ Nat.card D'.φ.ker = 1 := pow_card_eq_one'
  have h2 : Nat.card D'.φ.ker = 1 ∨ Nat.card D'.φ.ker = 2 := by omega
  rcases h2 with h2 | h2
  · rw [h2, pow_one] at h1
    have : k = 1 := congrArg Subtype.val h1
    rw [this, one_mul]
  · rw [h2, pow_two] at h1
    exact congrArg Subtype.val h1

theorem piE_e_central (q : SecQ R e) :
    ZTwo.piE hc ⟨e, (ZTwo.t_e_mem_rLayer hc).2⟩ * q =
      q * ZTwo.piE hc ⟨e, (ZTwo.t_e_mem_rLayer hc).2⟩ := by
  obtain ⟨x, rfl⟩ := ZTwo.piE_surjective hc q
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show e * (x : Y) = (x : Y) * e
  exact (Subgroup.mem_centralizer_singleton_iff.mp (rLayer_le_centralizer (Om R) e x.2)).symm

theorem piE_e_ne_one (hOE : oddCoreOf (rLayer (Om R) e) = ⊥) :
    ZTwo.piE hc ⟨e, (ZTwo.t_e_mem_rLayer hc).2⟩ ≠ 1 := by
  intro h
  apply hc.data.he1
  have := piE_inj hOE (h.trans (map_one _).symm)
  exact congrArg Subtype.val this

theorem ker_phi (hOE : oddCoreOf (rLayer (Om R) e) = ⊥) {x : ↥(rLayer (Om R) e)}
    (hx : D.φ (ZTwo.piE hc x) = 1) : (x : Y) = 1 ∨ (x : Y) = e := by
  have heE := (ZTwo.t_e_mem_rLayer hc).2
  by_cases h1 : ZTwo.piE hc x = 1
  · left
    have := piE_inj hOE (h1.trans (map_one _).symm)
    exact congrArg Subtype.val this
  · right
    have hcen : ZTwo.piE hc x ∈ Subgroup.center (SecQ R e) := D.ker_le hx
    have hecen : ZTwo.piE hc ⟨e, heE⟩ ∈ Subgroup.center (SecQ R e) := by
      rw [Subgroup.mem_center_iff]
      intro q
      exact (piE_e_central q).symm
    have he2 : ZTwo.piE hc ⟨e, heE⟩ * ZTwo.piE hc ⟨e, heE⟩ = 1 := by
      rw [← map_mul]
      have : (⟨e, heE⟩ : ↥(rLayer (Om R) e)) * ⟨e, heE⟩ = 1 := Subtype.ext hc.data.he2
      rw [this, map_one]
    have h3 := ZTwo.AECover.eq_of_central_involutions D hecen hcen he2 (piE_e_ne_one hOE) h1
    have := piE_inj hOE h3
    exact (congrArg Subtype.val this).symm

theorem qE_isPGroup (hOE : oddCoreOf (rLayer (Om R) e) = ⊥) : IsPGroup 2 (qE hc D) := by
  rintro ⟨q, hq⟩
  obtain ⟨hqE, hφ⟩ := mem_qE.mp hq
  set x : ↥(rLayer (Om R) e) := ⟨q, hqE⟩ with hxdef
  have h1 : D.φ (ZTwo.piE hc (x * x)) = 1 := by
    rw [map_mul, map_mul]
    exact vBar_sq hφ
  have h2 := ker_sq D (ZTwo.piE hc (x * x)) h1
  have h3 : x * x * (x * x) = 1 := piE_inj hOE (by rw [map_mul, h2, map_one])
  have h4 : q * q * (q * q) = 1 := congrArg Subtype.val h3
  refine ⟨2, ?_⟩
  ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  calc q ^ 2 ^ 2 = q * q * (q * q) := by
        rw [show 2 ^ 2 = 4 from rfl]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := h4

theorem qE_conj_E {x : Y} (hx : x ∈ rLayer (Om R) e) {q : Y} (hq : q ∈ qE hc D) :
    x * q * x⁻¹ ∈ qE hc D := by
  obtain ⟨hqE, hφ⟩ := mem_qE.mp hq
  have hm : x * q * x⁻¹ ∈ rLayer (Om R) e :=
    (rLayer (Om R) e).mul_mem ((rLayer (Om R) e).mul_mem hx hqE) ((rLayer (Om R) e).inv_mem hx)
  refine mem_qE.mpr ⟨hm, ?_⟩
  have : (⟨x * q * x⁻¹, hm⟩ : ↥(rLayer (Om R) e)) = ⟨x, hx⟩ * ⟨q, hqE⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  exact vBar_normal.conj_mem _ hφ _

theorem conj_mem_E (hΩ : HypOmegaGen (Om R)) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {x : Y}
    (hx : x ∈ rLayer (Om R) e) : c * x * c⁻¹ ∈ rLayer (Om R) e := by
  have := conj_mem_conjSub (n := c) hx
  rwa [conjSub_rLayer_eq hΩ hcC] at this

theorem qE_conj_C {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {q : Y} (hq : q ∈ qE hc D) :
    c * q * c⁻¹ ∈ qE hc D := by
  obtain ⟨hqE, hφ⟩ := mem_qE.mp hq
  obtain ⟨w, hw⟩ := D.toAEData.exists_wr _ (fun L hL => ZTwo.secAut_preserves hc ⟨c, hcC⟩ hL)
  have hcx : c * q * c⁻¹ ∈ rLayer (Om R) e := conj_mem_E (ZTwo.hΩ_of hc) hcC hqE
  refine mem_qE.mpr ⟨hcx, ?_⟩
  rw [← ZTwo.secAut_piE hc hcC ⟨q, hqE⟩ hcx, hw (ZTwo.piE hc ⟨q, hqE⟩)]
  exact vBar_normal.conj_mem _ hφ _

theorem comm_qE {c : Y} (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {w : Wr 6}
    (hw : D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩) w)
    (hwp : w.perm = 1) {x : Y} (hx : x ∈ rLayer (Om R) e) : x * c * x⁻¹ * c⁻¹ ∈ qE hc D := by
  have hxi : x⁻¹ ∈ rLayer (Om R) e := (rLayer (Om R) e).inv_mem hx
  have hcx : c * x⁻¹ * c⁻¹ ∈ rLayer (Om R) e := conj_mem_E (ZTwo.hΩ_of hc) hcC hxi
  have hm : x * c * x⁻¹ * c⁻¹ ∈ rLayer (Om R) e := by
    have := (rLayer (Om R) e).mul_mem hx hcx
    rwa [show x * (c * x⁻¹ * c⁻¹) = x * c * x⁻¹ * c⁻¹ by group] at this
  refine mem_qE.mpr ⟨hm, ?_⟩
  have hsplit : (⟨x * c * x⁻¹ * c⁻¹, hm⟩ : ↥(rLayer (Om R) e)) =
      ⟨x, hx⟩ * ⟨c * x⁻¹ * c⁻¹, hcx⟩ := Subtype.ext (by show _ = x * (c * x⁻¹ * c⁻¹); group)
  have hinv : (⟨x⁻¹, hxi⟩ : ↥(rLayer (Om R) e)) = (⟨x, hx⟩)⁻¹ := rfl
  have h2 : D.φ (ZTwo.piE hc ⟨c * x⁻¹ * c⁻¹, hcx⟩) =
      mkQ 6 w * (D.φ (ZTwo.piE hc ⟨x, hx⟩))⁻¹ * (mkQ 6 w)⁻¹ := by
    rw [← ZTwo.secAut_piE hc hcC ⟨x⁻¹, hxi⟩ hcx, hw (ZTwo.piE hc ⟨x⁻¹, hxi⟩), hinv, map_inv,
      map_inv]
  have hmw : mkQ 6 w ∈ vBar := Subgroup.mem_map_of_mem _ hwp
  rw [hsplit, map_mul, map_mul, h2]
  have := vBar.mul_mem (vBar_normal.conj_mem _ hmw (D.φ (ZTwo.piE hc ⟨x, hx⟩))) (vBar.inv_mem hmw)
  rwa [show D.φ (ZTwo.piE hc ⟨x, hx⟩) * mkQ 6 w * (D.φ (ZTwo.piE hc ⟨x, hx⟩))⁻¹ * (mkQ 6 w)⁻¹ =
    D.φ (ZTwo.piE hc ⟨x, hx⟩) * (mkQ 6 w * (D.φ (ZTwo.piE hc ⟨x, hx⟩))⁻¹ * (mkQ 6 w)⁻¹) by
    group] at this

theorem member_inv (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJe : J ≤ Subgroup.centralizer ({e} : Set Y)) {z : Y} (hz : IsUniqueInvolution J z) :
    ∃ hzE : z ∈ rLayer (Om R) e, ∃ (γ : Finset (Fin 6)) (hγ : γ.card = 4) (b : Bool),
      (secImg (Om R) e J).map D.φ = memBar γ hγ b ∧
        D.φ (ZTwo.piE hc ⟨z, hzE⟩) = zBar γ hγ := by
  have hJtq := tq_of_le_cent hJ hJe
  obtain ⟨htC, htY, hzA⟩ := isUniqueInvolution_secImg (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) hJtq hz
  have hL := secImg_mem_secFam hJtq
  obtain ⟨γ, hγ, b, hlab⟩ := D.label _ hL
  have hzE : z ∈ rLayer (Om R) e := TwinPerpV3.A6b.le_rLayer_of_mem hJ (h2grp J hJ) hJe hz.mem
  refine ⟨hzE, γ, hγ, b, hlab, ?_⟩
  calc D.φ (ZTwo.piE hc ⟨z, hzE⟩) =
      D.φ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) ⟨⟨z, htC⟩, htY⟩) :=
        congrArg D.φ (ZTwo.piE_mk hc ⟨⟨z, htC⟩, htY⟩ hzE)
    _ = zBar γ hγ := D.map_eq_zBar hL hlab hzA

theorem member_inv_mem_qE (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJe : J ≤ Subgroup.centralizer ({e} : Set Y)) {z : Y} (hz : IsUniqueInvolution J z) :
    z ∈ qE hc D := by
  obtain ⟨hzE, γ, hγ, -, -, hφ⟩ := member_inv (hc := hc) (D := D) h2grp hJ hJe hz
  exact mem_qE.mpr ⟨hzE, hφ ▸ zBar_mem_vBar γ hγ⟩

include hc D in
theorem conj_ne (hOE : oddCoreOf (rLayer (Om R) e) = ⊥) {b : Y} (hb : b * e * b⁻¹ ≠ e) :
    conjSub b (rLayer (Om R) e) ≠ rLayer (Om R) e := by
  intro h
  have heE := (ZTwo.t_e_mem_rLayer hc).2
  have hbE : b * e * b⁻¹ ∈ rLayer (Om R) e := h ▸ conj_mem_conjSub heE
  have hbC : rLayer (Om R) e ≤ Subgroup.centralizer ({b * e * b⁻¹} : Set Y) := by
    rw [← h, ← rLayer_conj]
    exact rLayer_le_centralizer _ _
  have hcen : ZTwo.piE hc ⟨b * e * b⁻¹, hbE⟩ ∈ Subgroup.center (SecQ R e) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨x, rfl⟩ := ZTwo.piE_surjective hc q
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hbC x.2)
  have hecen : ZTwo.piE hc ⟨e, heE⟩ ∈ Subgroup.center (SecQ R e) := by
    rw [Subgroup.mem_center_iff]
    intro q
    exact (piE_e_central q).symm
  have he2 : ZTwo.piE hc ⟨e, heE⟩ * ZTwo.piE hc ⟨e, heE⟩ = 1 := by
    rw [← map_mul]
    have : (⟨e, heE⟩ : ↥(rLayer (Om R) e)) * ⟨e, heE⟩ = 1 := Subtype.ext hc.data.he2
    rw [this, map_one]
  have hb1 : ZTwo.piE hc ⟨b * e * b⁻¹, hbE⟩ ≠ 1 := by
    intro h1
    have := piE_inj hOE (h1.trans (map_one _).symm)
    have h2 : b * e * b⁻¹ = 1 := congrArg Subtype.val this
    apply hc.data.he1
    calc e = b⁻¹ * (b * e * b⁻¹) * b := by group
      _ = 1 := by rw [h2]; group
  have h3 := ZTwo.AECover.eq_of_central_involutions D hecen hcen he2 (piE_e_ne_one hOE) hb1
  exact hb (congrArg Subtype.val (piE_inj hOE h3)).symm

end Cover

section U

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.TC.Thin

theorem conj_le_cent {K : Subgroup Y} {a : Y} (hK : K ≤ Subgroup.centralizer ({a} : Set Y))
    (m : Y) : conjSub m K ≤ Subgroup.centralizer ({m * a * m⁻¹} : Set Y) := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := Subgroup.mem_centralizer_singleton_iff.mp (hK hx)
  calc x * (m * a * m⁻¹) = m * ((m⁻¹ * x * m) * a) * m⁻¹ := by group
    _ = m * (a * (m⁻¹ * x * m)) * m⁻¹ := by rw [this]
    _ = m * a * m⁻¹ * x := by group

theorem le_cent_mul {L : Subgroup Y} {a b : Y} (ha : L ≤ Subgroup.centralizer ({a} : Set Y))
    (hb : L ≤ Subgroup.centralizer ({b} : Set Y)) :
    L ≤ Subgroup.centralizer ({a * b} : Set Y) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (ha hx)
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hb hx)
  calc x * (a * b) = (x * a) * b := by group
    _ = a * (x * b) := by rw [h1]; group
    _ = a * (b * x) := by rw [h2]
    _ = a * b * x := by group

theorem g_te (hc : P23Cfg n Y R S t K' W u e g) : g * (t * e) * g⁻¹ = u := by
  have hd := hc.data
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) :=
    normalizer_le_centralizer_e hd (T7K.g_mem_normalizer hd)
  have hge : g * e * g⁻¹ = e := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]
  calc g * (t * e) * g⁻¹ = (g * t * g⁻¹) * (g * e * g⁻¹) := by group
    _ = u * e * e := by rw [hd.hgt, hge]
    _ = u := by rw [mul_assoc, hd.he2, mul_one]

theorem twins_u (hc : P23Cfg n Y R S t K' W u e g) (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) :
    conjSub g (tightCore R) ∈ tqMembers3 (Om R) u ∧ conjSub g K' ∈ tqMembers3 (Om R) u ∧
      conjSub g K' ≠ conjSub g (tightCore R) ∧
      IsUniqueInvolution (conjSub g (tightCore R)) (u * e) ∧
      IsUniqueInvolution (conjSub g K') (u * e) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨hKe, hK'e⟩ := ZTwo.twins_tq hc
  have hKu : conjSub g (tightCore R) ≤ Subgroup.centralizer ({u} : Set Y) := by
    have := conj_le_cent (le_cent_mul (le_centralizer_of_unique hz)
      (le_cent_of_tq hKe (h2grp _ hKe.1))) g
    rwa [g_te hc] at this
  have hK'u : conjSub g K' ≤ Subgroup.centralizer ({u} : Set Y) := by
    have := conj_le_cent (le_cent_mul (le_centralizer_of_unique hz')
      (le_cent_of_tq hK'e (h2grp _ hK'e.1))) g
    rwa [g_te hc] at this
  refine ⟨tq_of_le_cent (hΩ.conjInvariant g _ hK) hKu,
    tq_of_le_cent (hΩ.conjInvariant g _ hc.std.hK'.1) hK'u, ?_, ?_, ?_⟩
  · intro h
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  · have := hz.conj g
    rwa [hd.hgt] at this
  · have := hz'.conj g
    rwa [hd.hgt] at this

theorem hSu (hc : P23Cfg n Y R S t K' W u e g) :
    TwinDisc.Q8Section (SecQ R u) (TwinDisc.secFam (Om R) u) :=
  TwinPerpV3.layer_q8Section hc.std.perp hc.data.hu2

noncomputable def psiU (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    SecQ R u →* AEQ 5 :=
  TwinThmEW.psiOfF (TwinDisc.AE5.q8Fam_of_aeIdent_n (le_refl 5) (hSu hc) hA5.some) hA5.some

theorem psiU_map (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (L : Subgroup (SecQ R u)) :
    L.map (psiU hc hA5) =
      (L.subgroupOf (pSpan (TwinDisc.secFam (Om R) u))).map hA5.some.φ :=
  TwinThmEW.psi_map_eq _ _ L

theorem psiU_label (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    {L : Subgroup (SecQ R u)} (hL : L ∈ TwinDisc.secFam (Om R) u) :
    ∃ (γ : Finset (Fin 5)) (hγ : γ.card = 4) (b : Bool), L.map (psiU hc hA5) = memBar γ hγ b := by
  obtain ⟨γ, hγ, b, hl⟩ := hA5.some.label L hL
  exact ⟨γ, hγ, b, (psiU_map hc hA5 L).trans hl⟩

theorem psiU_surj (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (γ : Finset (Fin 5)) (hγ : γ.card = 4) (b : Bool) :
    ∃ L ∈ TwinDisc.secFam (Om R) u, L.map (psiU hc hA5) = memBar γ hγ b := by
  obtain ⟨L, hL, hl⟩ := hA5.some.label_surj γ hγ b
  exact ⟨L, hL, (psiU_map hc hA5 L).trans hl⟩

theorem psiU_range (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5) :
    (psiU hc hA5).range = TwinThinPf8.Hn 5 := by
  ext q
  constructor
  · rintro ⟨y, rfl⟩
    have : psiU hc hA5 y ∈ hA5.some.φ.range := ⟨_, rfl⟩
    rwa [hA5.some.range_eq] at this
  · intro hq
    rw [TwinThinPf8.Hn, ← hA5.some.range_eq] at hq
    obtain ⟨z, rfl⟩ := hq
    exact ⟨z.1, rfl⟩

theorem psiU_inj (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) : Function.Injective (psiU hc hA5) := by
  obtain ⟨hJ₁, hJ₂, hne, hz₁, hz₂⟩ := twins_u hc h2grp
  have hΩ := ZTwo.hΩ_of hc
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.hu2
  obtain ⟨htC, htY, hU₁⟩ := isUniqueInvolution_secImg hΩ hc2u hJ₁ hz₁
  obtain ⟨htC₂, htY₂, hU₂⟩ := isUniqueInvolution_secImg hΩ hc2u hJ₂ hz₂
  have hne' : secImg (Om R) u (conjSub g K') ≠ secImg (Om R) u (conjSub g (tightCore R)) :=
    fun h => secImg_ne_of_twins hΩ hc2u hJ₁ hJ₂ hne hz₁ hz₂ h.symm
  have hker : hA5.some.φ.ker = ⊥ :=
    TwinThmEW.Ae5Q8.ae5_ker_bot (hSu hc) hA5.some (secImg_mem_secFam hJ₁)
      (secImg_mem_secFam hJ₂) hne' hU₁ hU₂
  have hinjφ : Function.Injective hA5.some.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  intro a b hab
  exact congrArg Subtype.val (hinjφ hab)

theorem zbar_of_inj {X : Type*} [Group X] {m : ℕ} (hm : 5 ≤ m) {f : X →* AEQ m}
    (hf : Function.Injective f) {L : Subgroup X} {γ : Finset (Fin m)} {hγ : γ.card = 4}
    {b : Bool} (hl : L.map f = memBar γ hγ b) {z : X} (hz : IsUniqueInvolution L z) :
    f z = zBar γ hγ := by
  have hmem : f z ∈ memBar γ hγ b := by
    rw [← hl]
    exact Subgroup.mem_map_of_mem f hz.mem
  have hsq : f z * f z = 1 := by rw [← map_mul, hz.sq, map_one]
  rcases eq_of_mem_memBar_mul_self hm hmem hsq with h1 | h1
  · exact absurd (hf (h1.trans (map_one f).symm)) hz.ne_one
  · exact h1

theorem mk_inj_of_bot {X : Type*} [Group X] {N : Subgroup X} (hN : N = ⊥) {a b : X}
    (h : (QuotientGroup.mk a : X ⧸ N) = QuotientGroup.mk b) : a = b := by
  have := QuotientGroup.eq.mp h
  rw [hN, Subgroup.mem_bot, inv_mul_eq_one] at this
  exact this

theorem u_twin_label (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) :
    ∃ (β : Finset (Fin 5)) (hβ : β.card = 4) (b₁ : Bool)
      (hxC : u * e ∈ Subgroup.centralizer ({u} : Set Y))
      (hxY : (⟨u * e, hxC⟩ : ↥(Subgroup.centralizer ({u} : Set Y))) ∈ coreHull (Om R) u),
      (secImg (Om R) u (conjSub g (tightCore R))).map (psiU hc hA5) = memBar β hβ b₁ ∧
      (secImg (Om R) u (conjSub g K')).map (psiU hc hA5) = memBar β hβ (!b₁) ∧
      psiU hc hA5 (QuotientGroup.mk ⟨⟨u * e, hxC⟩, hxY⟩) = zBar β hβ := by
  obtain ⟨hJ₁, hJ₂, hne, hz₁, hz₂⟩ := twins_u hc h2grp
  have hΩ := ZTwo.hΩ_of hc
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.hu2
  obtain ⟨htC, htY, hU₁⟩ := isUniqueInvolution_secImg hΩ hc2u hJ₁ hz₁
  obtain ⟨htC₂, htY₂, hU₂⟩ := isUniqueInvolution_secImg hΩ hc2u hJ₂ hz₂
  have hψinj := psiU_inj hc hA5 h2grp
  obtain ⟨β, hβ, b₁, hl₁⟩ := psiU_label hc hA5 (secImg_mem_secFam hJ₁)
  obtain ⟨β', hβ', b₂, hl₂⟩ := psiU_label hc hA5 (secImg_mem_secFam hJ₂)
  have hx₁ := zbar_of_inj (le_refl 5) hψinj hl₁ hU₁
  have hx₂ := zbar_of_inj (le_refl 5) hψinj hl₂ hU₂
  have hββ : β' = β := eq_of_zBar_eq (by norm_num) (hx₂.symm.trans hx₁)
  subst hββ
  have hb : b₂ = !b₁ := by
    by_contra h
    have hb' : b₂ = b₁ := bool_eq_of_not_eq_not h
    subst hb'
    exact secImg_ne_of_twins hΩ hc2u hJ₁ hJ₂ hne hz₁ hz₂
      (Subgroup.map_injective hψinj (hl₁.trans hl₂.symm))
  subst hb
  exact ⟨_, _, b₁, htC, htY, hl₁, hl₂, hx₁⟩

theorem s2_u (hc : P23Cfg n Y R S t K' W u e g)
    (hA5 : SecAE R u 5) (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({u} : Set Y))
    (hcJ : ∀ k ∈ conjSub g (tightCore R) ⊔ conjSub g K', c * k = k * c) :
    (∀ h ∈ rLayer (Om R) u, c * h = h * c) ∨
      (∀ h ∈ rLayer (Om R) u, (u * e * c) * h = h * (u * e * c)) := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ := ZTwo.hΩ_of hc
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  obtain ⟨β, hβ, b₁, hxC, hxY, hl₁, hl₂, hx⟩ := u_twin_label hc hA5 h2grp
  set ψ := psiU hc hA5 with hψdef
  have hψinj : Function.Injective ψ := psiU_inj hc hA5 h2grp
  set σ := TwinExitPf6.secAut (Om R) u hΩ hc2u ⟨c, hcC⟩ with hσdef
  set e₀ : SecQ R u ≃* ↥ψ.range := MonoidHom.ofInjective hψinj with he₀
  set σ' : ↥ψ.range →* ↥ψ.range := (e₀.symm.trans (σ.trans e₀)).toMonoidHom with hσ'
  have hσ'bij : Function.Bijective σ' := (e₀.symm.trans (σ.trans e₀)).bijective
  have hσ'app : ∀ q, σ' (e₀ q) = e₀ (σ q) := fun q => by
    show e₀ (σ (e₀.symm (e₀ q))) = e₀ (σ q)
    rw [MulEquiv.symm_apply_apply]
  have hperm : TwinThinPf8.PermMembers ψ.range σ' := by
    intro γ hγ b
    obtain ⟨L, hL, hLl⟩ := psiU_surj hc hA5 γ hγ b
    obtain ⟨γ', hγ', b', hl'⟩ :=
      psiU_label hc hA5 (TwinExitPf10.secAut_map_secFam hΩ hc2u ⟨c, hcC⟩ hL)
    refine ⟨γ', hγ', b', fun x hx => ?_⟩
    rw [← hLl] at hx
    obtain ⟨l, hl, hlx⟩ := hx
    have hxe : x = e₀ l := Subtype.ext hlx.symm
    rw [hxe, hσ'app, ← hl']
    exact ⟨σ l, ⟨l, hl, rfl⟩, rfl⟩
  obtain ⟨w, hw⟩ := TwinThin.Cross.aeAut_of_five_le (le_refl 5) ψ.range (psiU_range hc hA5) σ'
    hσ'bij hperm
  have hψσ : ∀ q, ψ (σ q) = mkQ 5 w * ψ q * (mkQ 5 w)⁻¹ := by
    intro q
    have := hw (e₀ q)
    rw [hσ'app] at this
    exact this
  have hfix : ∀ J : Subgroup Y, J ≤ conjSub g (tightCore R) ⊔ conjSub g K' →
      ∀ q ∈ secImg (Om R) u J, σ q = q := by
    intro J hJK q hq
    obtain ⟨h, hh, rfl⟩ := hq
    have hhJ : ((h : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) ∈ J :=
      TwinADescent.coreAt_le_left u J
        (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh))
    have hcomm := hcJ _ (hJK hhJ)
    exact TwinExitPf6.secAut_mk hΩ hc2u ⟨c, hcC⟩ h h (Subtype.ext (by
      show ((h : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) =
        c * ((h : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * c⁻¹
      rw [hcomm, mul_inv_cancel_right]))
  have hwB : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 5 w * x * (mkQ 5 w)⁻¹ = x := by
    intro b x hx
    have key : ∀ J : Subgroup Y, J ≤ conjSub g (tightCore R) ⊔ conjSub g K' →
        x ∈ (secImg (Om R) u J).map ψ → mkQ 5 w * x * (mkQ 5 w)⁻¹ = x := by
      intro J hJ hxJ
      obtain ⟨q, hq, rfl⟩ := hxJ
      rw [← hψσ q, hfix J hJ q hq]
    by_cases hb : b = b₁
    · subst hb
      exact key _ le_sup_left (by rw [hl₁]; exact hx)
    · have hb' : b = !b₁ := bool_eq_not_of_ne hb
      subst hb'
      exact key _ le_sup_right (by rw [hl₂]; exact hx)
  obtain ⟨c', e', hwce, he', hc'⟩ :=
    TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w hwB
  have hcβ : ∀ i ∈ β, c'.vec i = 0 ∧ c'.perm i = i := by
    intro i hi
    apply hc'
    rw [Set.mem_compl_iff, not_not, range_emb]
    exact hi
  have hc'p : c'.perm = 1 :=
    TwinThinPf18.perm_eq_one_of_fix_four_fin5 c'.perm β hβ (fun i hi => (hcβ i hi).2)
  have he'p : e'.perm = 1 := by
    rcases he' with rfl | rfl
    · rfl
    · exact zOf_perm _
  have hwp : w.perm = 1 := by rw [hwce, mul_perm, hc'p, he'p, mul_one]
  have hwv : ∀ i, w.vec i = c'.vec i + e'.vec i := by
    intro i
    rw [hwce, mul_vec, hc'p]
    rfl
  have he'c : ∀ i ∈ β, ∀ j ∈ β, e'.vec i = e'.vec j := by
    intro i hi j hj
    rcases he' with rfl | rfl
    · rfl
    · rw [zOf_vec_apply, zOf_vec_apply,
        if_pos (show i ∈ Set.range (emb β hβ) by rw [range_emb]; exact hi),
        if_pos (show j ∈ Set.range (emb β hβ) by rw [range_emb]; exact hj)]
  have hwc : ∀ i ∈ β, ∀ j ∈ β, w.vec i = w.vec j := by
    intro i hi j hj
    rw [hwv, hwv, (hcβ i hi).1, (hcβ j hj).1, he'c i hi j hj]
  obtain ⟨q₀, hq₀⟩ : β.Nonempty := Finset.card_pos.mp (by rw [hβ]; norm_num)
  have hout : ∀ i j, i ∉ β → j ∉ β → i = j := by
    intro i j hi hj
    have hc1 : βᶜ.card = 1 := by rw [Finset.card_compl, hβ]; rfl
    exact Finset.card_le_one.mp hc1.le i (by simpa using hi) j (by simpa using hj)
  have hdich : mkQ 5 w = 1 ∨ mkQ 5 w = zBar β hβ := by
    by_cases hall : ∀ i, w.vec i = w.vec q₀
    · left
      exact ZTwo.mkQ_eq_one_of_const w hwp _ hall
    · right
      push Not at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hi₀β : i₀ ∉ β := fun h => hi₀ (hwc i₀ h q₀ hq₀)
      have hz : (w * zOf (emb β hβ)).perm = 1 := by rw [mul_perm, hwp, zOf_perm, mul_one]
      have hconst : ∀ i, (w * zOf (emb β hβ)).vec i = w.vec q₀ + 1 := by
        intro i
        rw [mul_vec, hwp]
        show w.vec i + (zOf (emb β hβ)).vec i = w.vec q₀ + 1
        rw [zOf_vec_apply]
        by_cases hi : i ∈ β
        · rw [if_pos (show i ∈ Set.range (emb β hβ) by rw [range_emb]; exact hi),
            hwc i hi q₀ hq₀]
        · rw [if_neg (show i ∉ Set.range (emb β hβ) by rw [range_emb]; exact hi), add_zero,
            hout i i₀ hi hi₀β]
          generalize w.vec i₀ = a at hi₀ ⊢
          generalize w.vec q₀ = b at hi₀ ⊢
          revert a b
          decide
      have h1 := ZTwo.mkQ_eq_one_of_const _ hz _ hconst
      rw [map_mul] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_eq_of_mul_eq_one_right (zBar_mul_self β hβ)
  have hmap := TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2u (ZTwo.h2_of hc)
  have hnorm := TwinExitPf6.normal_coreHull hΩ hc2u
  have hlift : ∀ h ∈ rLayer (Om R) u, ∃ k : ↥(coreHull (Om R) u),
      ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = h := by
    intro h hh
    rw [← hmap] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact ⟨⟨k, hk⟩, rfl⟩
  have hσk : ∀ k : ↥(coreHull (Om R) u),
      σ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) k) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u))
          ⟨⟨c, hcC⟩ * (k : ↥(Subgroup.centralizer ({u} : Set Y))) * ⟨c, hcC⟩⁻¹,
            hnorm.conj_mem _ k.2 _⟩ :=
    fun k => TwinExitPf6.secAut_mk hΩ hc2u ⟨c, hcC⟩ k _ rfl
  rcases hdich with h1 | h1
  · left
    intro h hh
    obtain ⟨k, rfl⟩ := hlift h hh
    have h2 : σ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) k) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) k := by
      apply hψinj
      rw [hψσ, h1, one_mul, inv_one, mul_one]
    rw [hσk] at h2
    have h3 := mk_inj_of_bot hOu h2
    have h4 : c * ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * c⁻¹ =
        ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) :=
      congrArg (fun z : ↥(coreHull (Om R) u) =>
        ((z : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)) h3
    calc c * ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) =
        c * ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * c⁻¹ * c := by group
      _ = ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * c := by rw [h4]
  · right
    intro h hh
    obtain ⟨k, rfl⟩ := hlift h hh
    set x₀ : ↥(coreHull (Om R) u) := ⟨⟨u * e, hxC⟩, hxY⟩ with hx₀
    have h2 : σ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) k) =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) (x₀ * k * x₀⁻¹) := by
      apply hψinj
      rw [hψσ, h1, ← hx]
      simp only [map_mul, map_inv]
      rfl
    rw [hσk] at h2
    have h3 := mk_inj_of_bot hOu h2
    have h4 : c * ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * c⁻¹ =
        (u * e) * ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * (u * e)⁻¹ :=
      congrArg (fun z : ↥(coreHull (Om R) u) =>
        ((z : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)) h3
    have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a :=
      Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
    have heW : e ∈ W := (T7K.e_mem_inf hd).1
    have hue2 : (u * e) * (u * e) = 1 := by
      calc (u * e) * (u * e) = u * (e * u) * e := by group
        _ = u * (u * e) * e := by rw [hWab e heW u hd.huW]
        _ = (u * u) * (e * e) := by group
        _ = 1 := by rw [hd.hu2, hd.he2, one_mul]
    set hY := ((k : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)
    calc u * e * c * hY = (u * e) * (c * hY * c⁻¹) * c := by group
      _ = (u * e) * ((u * e) * hY * (u * e)⁻¹) * c := by rw [h4]
      _ = ((u * e) * (u * e)) * hY * (u * e)⁻¹ * c := by group
      _ = hY * (u * e)⁻¹ * c := by rw [hue2, one_mul]
      _ = hY * (u * e * c) := by rw [inv_eq_of_mul_eq_one_right hue2]; group

theorem u_other (hc : P23Cfg n Y R S t K' W u e g) (hA5 : SecAE R u 5)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥) :
    ∃ M ∈ Om R, ∃ M' ∈ Om R, M ≤ Subgroup.centralizer ({u} : Set Y) ∧
      M' ≤ Subgroup.centralizer ({u} : Set Y) ∧ M ≠ M' ∧
      ∃ z : Y, IsUniqueInvolution M z ∧ IsUniqueInvolution M' z ∧ z ≠ u * e := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ := ZTwo.hΩ_of hc
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  obtain ⟨β, hβ, b₁, hxC, hxY, -, -, hx⟩ := u_twin_label hc hA5 h2grp
  have hψinj := psiU_inj hc hA5 h2grp
  obtain ⟨γ, hγ, hγβ⟩ : ∃ γ : Finset (Fin 5), γ.card = 4 ∧ γ ≠ β := by
    by_cases hb : β = {0, 1, 2, 3}
    · exact ⟨{1, 2, 3, 4}, rfl, by rw [hb]; decide⟩
    · exact ⟨{0, 1, 2, 3}, rfl, fun h => hb h.symm⟩
  obtain ⟨L, hL, hLl⟩ := psiU_surj hc hA5 γ hγ true
  obtain ⟨L', hL', hLl'⟩ := psiU_surj hc hA5 γ hγ false
  obtain ⟨M, hMtq, rfl⟩ := exists_of_mem_secFam hL
  obtain ⟨M', hM'tq, rfl⟩ := exists_of_mem_secFam hL'
  have hMΩ := hMtq.1
  have hM'Ω := hM'tq.1
  obtain ⟨m, hm⟩ := hMΩ
  obtain ⟨m', hm'⟩ := hM'Ω
  have hzM : IsUniqueInvolution M (m * t * m⁻¹) := hm ▸ hz.conj m
  have hzM' : IsUniqueInvolution M' (m' * t * m'⁻¹) := hm' ▸ hz.conj m'
  obtain ⟨hC1, hY1, hU1⟩ := isUniqueInvolution_secImg hΩ hc2u hMtq hzM
  obtain ⟨hC2, hY2, hU2⟩ := isUniqueInvolution_secImg hΩ hc2u hM'tq hzM'
  have h1 := zbar_of_inj (le_refl 5) hψinj hLl hU1
  have h2 := zbar_of_inj (le_refl 5) hψinj hLl' hU2
  have hzz : m * t * m⁻¹ = m' * t * m'⁻¹ := by
    have := mk_inj_of_bot hOu (hψinj (h1.trans h2.symm))
    exact congrArg (fun z : ↥(coreHull (Om R) u) =>
      ((z : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)) this
  refine ⟨M, hMtq.1, M', hM'tq.1, le_cent_of_tq hMtq (h2grp _ hMtq.1),
    le_cent_of_tq hM'tq (h2grp _ hM'tq.1), ?_, m * t * m⁻¹, hzM, by rw [hzz]; exact hzM', ?_⟩
  · intro h
    apply memBar_true_ne_false (le_refl 5) γ hγ
    rw [← hLl, ← hLl', h]
  · intro h
    apply hγβ
    apply eq_of_zBar_eq (by norm_num : (5 : ℕ) ≠ 8)
    rw [← h1, ← hx]
    congr 2
    exact Subtype.ext (Subtype.ext h)

end U

section E6

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.TC.Thin

variable {hc : P23Cfg n Y R S t K' W u e g}
  {D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)}

theorem fix_of_cent {c : Y} (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {J : Subgroup Y}
    (hcJ : ∀ k ∈ J, c * k = k * c) :
    ∀ q ∈ secImg (Om R) e J,
      TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩ q = q := by
  intro q hq
  obtain ⟨h, hh, rfl⟩ := hq
  have hhJ : ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ J :=
    TwinADescent.coreAt_le_left e J (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hh))
  have hcomm := hcJ _ hhJ
  exact TwinExitPf6.secAut_mk (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩ h h (Subtype.ext (by
    show ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
      c * ((h : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) * c⁻¹
    rw [hcomm, mul_inv_cancel_right]))

theorem cent_of_fix (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {J : Subgroup Y} (hJ : J ∈ Om R)
    (hJe : J ≤ Subgroup.centralizer ({e} : Set Y))
    (hfix : ∀ q ∈ secImg (Om R) e J,
      TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩ q = q) :
    ∀ j ∈ J, c * j = j * c := by
  intro j hj
  have hjC : j ∈ Subgroup.centralizer ({e} : Set Y) := hJe hj
  have hJtq := tq_of_le_cent hJ hJe
  have hjcore : j ∈ TwinADescent.coreAt e J := by
    show j ∈ tightCore (J ⊓ Subgroup.centralizer ({e} : Set Y))
    exact Subgroup.subset_closure ⟨⟨hj, hjC⟩,
      (h2grp J hJ).to_le (Subgroup.zpowers_le.mpr hj)⟩
  have hjY : (⟨j, hjC⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) ∈ coreHull (Om R) e :=
    le_coreHull hJtq (Subgroup.mem_subgroupOf.mpr hjcore)
  have hnorm := TwinExitPf6.normal_coreHull (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc)
  set h : ↥(coreHull (Om R) e) := ⟨⟨j, hjC⟩, hjY⟩ with hhdef
  have hq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e)) h ∈
      secImg (Om R) e J :=
    ⟨h, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hjcore), rfl⟩
  have h1 := hfix _ hq
  rw [TwinExitPf6.secAut_mk (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩ h
    ⟨⟨c, hcC⟩ * (h : ↥(Subgroup.centralizer ({e} : Set Y))) * ⟨c, hcC⟩⁻¹,
      hnorm.conj_mem _ h.2 _⟩ rfl] at h1
  have h2 := mk_inj_of_bot hOe h1
  have h3 : c * j * c⁻¹ = j := congrArg (fun z : ↥(coreHull (Om R) e) =>
    ((z : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) h2
  calc c * j = c * j * c⁻¹ * c := by group
    _ = j * c := by rw [h3]

theorem fix_of_acts {σ : SecQ R e ≃* SecQ R e}
    (hσΦ : ∀ L ∈ TwinDisc.secFam (Om R) e, L.map σ.toMonoidHom ∈ TwinDisc.secFam (Om R) e)
    {w : Wr 6} (hw : D.toAEData.Acts σ w) {L : Subgroup (SecQ R e)}
    (hL : L ∈ TwinDisc.secFam (Om R) e) {γ : Finset (Fin 6)} {hγ : γ.card = 4} {b : Bool}
    (hl : L.map D.φ = memBar γ hγ b)
    (hwc : ∀ x ∈ memBar γ hγ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) :
    ∀ q ∈ L, σ q = q := by
  have h1 : ∀ l ∈ L, D.φ (σ l) = D.φ l := by
    intro l hl'
    rw [hw l]
    exact hwc _ (by rw [← hl]; exact ⟨l, hl', rfl⟩)
  have himg : (L.map σ.toMonoidHom).map D.φ = L.map D.φ := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨l, hl', rfl⟩, rfl⟩
      exact ⟨l, hl', (h1 l hl').symm⟩
    · rintro _ ⟨l, hl', rfl⟩
      exact ⟨σ l, ⟨l, hl', rfl⟩, h1 l hl'⟩
  have hσL : L.map σ.toMonoidHom = L := D.label_inj _ (hσΦ L hL) _ hL himg
  intro q hq
  have hσq : σ q ∈ L := by rw [← hσL]; exact ⟨q, hq, rfl⟩
  exact D.inj L hL (σ q) hσq q hq (h1 q hq)

theorem exists_acts {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) :
    ∃ w : Wr 6, D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩) w :=
  D.toAEData.exists_wr _ (fun L hL => ZTwo.secAut_preserves hc ⟨c, hcC⟩ hL)

end E6

section E6b

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.TC.Thin

theorem perm_fix_of_cent {α : Finset (Fin 6)} (hα : α.card = 4) {w : Wr 6}
    (hB : ∀ b : Bool, ∀ x ∈ memBar α hα b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) :
    ∀ i ∈ α, w.perm i = i := by
  obtain ⟨c, e', hw, he', hc'⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) α hα w hB
  have he'p : e'.perm = 1 := by
    rcases he' with rfl | rfl
    · rfl
    · exact zOf_perm _
  intro i hi
  rw [hw, mul_perm, he'p, mul_one]
  exact (hc' i (by rw [Set.mem_compl_iff, not_not, range_emb]; exact hi)).2

theorem perm_one_of_two {β γ : Finset (Fin 6)} (hβ : β.card = 4) (hγ : γ.card = 4) (hne : γ ≠ β)
    {w : Wr 6} (hB : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x)
    (hC : ∀ b : Bool, ∀ x ∈ memBar γ hγ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) : w.perm = 1 := by
  obtain ⟨a, b, hab, ha, hb, hout⟩ := ZTwo.exists_compl_pair hβ
  rcases ZTwo.perm_dichotomy hab ha hb hout w.perm (perm_fix_of_cent hβ hB) with h | h
  · exact h
  · exfalso
    have hsub : ¬ γ ⊆ β := fun h' =>
      hne (Finset.eq_of_subset_of_card_le h' (by rw [hβ, hγ]))
    obtain ⟨x, hxγ, hxβ⟩ := Finset.not_subset.mp hsub
    have hfix := perm_fix_of_cent hγ hC x hxγ
    rw [h] at hfix
    rcases hout x hxβ with rfl | rfl
    · rw [Equiv.swap_apply_left] at hfix
      exact hab hfix.symm
    · rw [Equiv.swap_apply_right] at hfix
      exact hab hfix

variable {hc : P23Cfg n Y R S t K' W u e g}
  {D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)}

theorem perm_one (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({e} : Set Y))
    (hcK : ∀ k ∈ tightCore R ⊔ K', c * k = k * c) {J J' : Subgroup Y} (hJ : J ∈ Om R)
    (hJ' : J' ∈ Om R) (hJe : J ≤ Subgroup.centralizer ({e} : Set Y))
    (hJ'e : J' ≤ Subgroup.centralizer ({e} : Set Y)) (hne : J' ≠ J) {z : Y}
    (hz : IsUniqueInvolution J z) (hz' : IsUniqueInvolution J' z) (hzt : z ≠ t)
    (hcJ : ∀ k ∈ J, c * k = k * c) (hcJ' : ∀ k ∈ J', c * k = k * c) {w : Wr 6}
    (hw : D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩) w) :
    w.perm = 1 := by
  classical
  have hΩ := ZTwo.hΩ_of hc
  have hc2e := ZTwo.hc2e_of hc
  have hC := CoreData.of_S hc.std.perp.core
  have hzt0 : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  set σ := TwinExitPf6.secAut (Om R) e hΩ hc2e ⟨c, hcC⟩ with hσ
  have hcen : ∀ (L : Subgroup Y), (∀ k ∈ L, c * k = k * c) → ∀ b : Bool, ∀ γ : Finset (Fin 6),
      ∀ hγ : γ.card = 4, (secImg (Om R) e L).map D.φ = memBar γ hγ b →
        ∀ x ∈ memBar γ hγ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    intro L hcL b γ hγ hl x hx
    rw [← hl] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    rw [← hw q, fix_of_cent (hc := hc) hcC hcL q hq]
  obtain ⟨β, hβ, b₀, hlA, hlA', -, -, -, -⟩ := ZTwo.twin_labels hc D
  have hB : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact hcen _ (fun k hk => hcK k (Subgroup.mem_sup_left hk)) _ β hβ hlA
    · have hb' : b = !b₀ := bool_eq_not_of_ne hb
      subst hb'
      exact hcen _ (fun k hk => hcK k (Subgroup.mem_sup_right hk)) _ β hβ hlA'
  have hJtq := tq_of_le_cent hJ hJe
  have hJ'tq := tq_of_le_cent hJ' hJ'e
  obtain ⟨hzE, γ, hγ, b, hlJ, hzγ⟩ := member_inv (hc := hc) (D := D) h2grp hJ hJe hz
  obtain ⟨hzE', γ', hγ', b', hlJ', hzγ'⟩ := member_inv (hc := hc) (D := D) h2grp hJ' hJ'e hz'
  have hγγ : γ' = γ := eq_of_zBar_eq (by norm_num) (hzγ'.symm.trans hzγ)
  subst hγγ
  have hneJ := secImg_ne_of_twins hΩ hc2e hJtq hJ'tq hne hz hz'
  have hbb : b' = !b := by
    by_contra h
    have : b' = b := bool_eq_of_not_eq_not h
    subst this
    exact hneJ (D.label_inj _ (secImg_mem_secFam hJtq) _ (secImg_mem_secFam hJ'tq)
      (hlJ.trans hlJ'.symm))
  subst hbb
  have hCγ : ∀ b'' : Bool, ∀ x ∈ memBar γ' hγ' b'', mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
    intro b''
    by_cases hb : b'' = b
    · subst hb
      exact hcen J hcJ _ γ' hγ' hlJ
    · have hb' : b'' = !b := bool_eq_not_of_ne hb
      subst hb'
      exact hcen J' hcJ' _ γ' hγ' hlJ'
  have hγβ : γ' ≠ β := by
    intro hγβ
    subst hγβ
    obtain ⟨htC, htY, hU0⟩ := isUniqueInvolution_secImg hΩ hc2e (ZTwo.twins_tq hc).1 hzt0
    obtain ⟨htC', htY', hU0'⟩ := isUniqueInvolution_secImg hΩ hc2e (ZTwo.twins_tq hc).2
      (isUniqueInvolution_of_mem_twinSet hzt0 hc.std.hK')
    obtain ⟨hzC, hzY, hUJ⟩ := isUniqueInvolution_secImg hΩ hc2e hJtq hz
    have key : ∀ {M : Subgroup Y} (hMtq : M ∈ tqMembers3 (Om R) e) (htC₀ htY₀),
        IsUniqueInvolution (secImg (Om R) e M)
          (QuotientGroup.mk (⟨⟨t, htC₀⟩, htY₀⟩ : ↥(coreHull (Om R) e))) →
        secImg (Om R) e J = secImg (Om R) e M → False := by
      intro M hMtq htC₀ htY₀ hUM hJM
      rw [hJM] at hUJ
      have h1 := mk_inj_of_bot hOe (hUJ.eq hUM)
      exact hzt (congrArg (fun x : ↥(coreHull (Om R) e) =>
        ((x : ↥(Subgroup.centralizer ({e} : Set Y))) : Y)) h1)
    by_cases hb : b = b₀
    · subst hb
      exact key (ZTwo.twins_tq hc).1 htC htY hU0 (D.label_inj _ (secImg_mem_secFam hJtq) _
        (secImg_mem_secFam (ZTwo.twins_tq hc).1) (hlJ.trans hlA.symm))
    · have hb' : b = !b₀ := bool_eq_not_of_ne hb
      subst hb'
      exact key (ZTwo.twins_tq hc).2 htC' htY' hU0' (D.label_inj _ (secImg_mem_secFam hJtq) _
        (secImg_mem_secFam (ZTwo.twins_tq hc).2) (hlJ.trans hlA'.symm))
  exact perm_one_of_two hβ hγ' hγβ hB hCγ

theorem vec_type {β : Finset (Fin 6)} (hβ : β.card = 4) {w : Wr 6} (hwp : w.perm = 1)
    (hB : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x) :
    (∃ d : Fin 6, ∀ i j, i ≠ d → j ≠ d → w.vec i = w.vec j) ∨ mkQ 6 w = zBar β hβ := by
  classical
  obtain ⟨c, e', hw, he', hc'⟩ := TwinThinPf10.exists_split (by norm_num) (by norm_num) β hβ w hB
  have hcβ : ∀ i ∈ β, c.vec i = 0 ∧ c.perm i = i := by
    intro i hi
    apply hc'
    rw [Set.mem_compl_iff, not_not, range_emb]
    exact hi
  have he'p : e'.perm = 1 := by
    rcases he' with rfl | rfl
    · rfl
    · exact zOf_perm _
  have hcp : c.perm = 1 := by
    have := hwp
    rw [hw, mul_perm, he'p, mul_one] at this
    exact this
  have hwv : ∀ i, w.vec i = c.vec i + e'.vec i := by
    intro i
    rw [hw, mul_vec, hcp]
    rfl
  have he'c : ∀ i ∈ β, ∀ j ∈ β, e'.vec i = e'.vec j := by
    intro i hi j hj
    rcases he' with rfl | rfl
    · rfl
    · rw [zOf_vec_apply, zOf_vec_apply,
        if_pos (show i ∈ Set.range (emb β hβ) by rw [range_emb]; exact hi),
        if_pos (show j ∈ Set.range (emb β hβ) by rw [range_emb]; exact hj)]
  have hwc : ∀ i ∈ β, ∀ j ∈ β, w.vec i = w.vec j := by
    intro i hi j hj
    rw [hwv, hwv, (hcβ i hi).1, (hcβ j hj).1, he'c i hi j hj]
  obtain ⟨q₀, hq₀⟩ : β.Nonempty := Finset.card_pos.mp (by rw [hβ]; norm_num)
  obtain ⟨a, b, hab, ha, hb, hout⟩ := ZTwo.exists_compl_pair hβ
  have off : ∀ d d' : Fin 6, d' ∉ β → (∀ i, i ∉ β → i = d ∨ i = d') →
      w.vec d' = w.vec q₀ → ∃ d : Fin 6, ∀ i j, i ≠ d → j ≠ d → w.vec i = w.vec j := by
    intro d d' hd' hout' hval
    refine ⟨d, fun i j hi hj => ?_⟩
    have hall : ∀ k, k ≠ d → w.vec k = w.vec q₀ := by
      intro k hk
      by_cases hkβ : k ∈ β
      · exact hwc k hkβ q₀ hq₀
      · rcases hout' k hkβ with rfl | rfl
        · exact absurd rfl hk
        · exact hval
    rw [hall i hi, hall j hj]
  by_cases hva : w.vec a = w.vec q₀
  · left
    exact off b a ha (fun i hi => (hout i hi).symm) hva
  · by_cases hvb : w.vec b = w.vec q₀
    · left
      exact off a b hb hout hvb
    · right
      have hz : (w * zOf (emb β hβ)).perm = 1 := by rw [mul_perm, hwp, zOf_perm, mul_one]
      have flip : ∀ x y : ZMod 2, x ≠ y → x = y + 1 := by decide
      have hconst : ∀ i, (w * zOf (emb β hβ)).vec i = w.vec q₀ + 1 := by
        intro i
        rw [mul_vec, hwp]
        show w.vec i + (zOf (emb β hβ)).vec i = w.vec q₀ + 1
        rw [zOf_vec_apply]
        by_cases hi : i ∈ β
        · rw [if_pos (show i ∈ Set.range (emb β hβ) by rw [range_emb]; exact hi),
            hwc i hi q₀ hq₀]
        · rw [if_neg (show i ∉ Set.range (emb β hβ) by rw [range_emb]; exact hi), add_zero]
          rcases hout i hi with rfl | rfl
          · exact flip _ _ hva
          · exact flip _ _ hvb
      have h1 := ZTwo.mkQ_eq_one_of_const _ hz _ hconst
      rw [map_mul] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_eq_of_mul_eq_one_right (zBar_mul_self β hβ)

theorem cent_of_const {w : Wr 6} (hwp : w.perm = 1) {d : Fin 6}
    (hd : ∀ i j, i ≠ d → j ≠ d → w.vec i = w.vec j) {γ : Finset (Fin 6)} (hγ : γ.card = 4)
    (hdγ : d ∉ γ) (b : Bool) : ∀ x ∈ memBar γ hγ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
  rintro _ ⟨a', ha', rfl⟩
  have hcomm : w * a' = a' * w := by
    have hw : w = ofVec w.vec := Wr.ext rfl hwp
    rw [hw]
    refine ZTwo.ofVec_comm_of_const _ a' (Set.range (emb γ hγ)) (supportedOn_of_mem_memAt ha') ?_
    intro i hi j hj
    rw [range_emb] at hi hj
    refine hd i j ?_ ?_
    · rintro rfl; exact hdγ hi
    · rintro rfl; exact hdγ hj
  calc mkQ 6 w * mkQ 6 a' * (mkQ 6 w)⁻¹ = mkQ 6 (w * a') * (mkQ 6 w)⁻¹ := by rw [map_mul]
    _ = mkQ 6 (a' * w) * (mkQ 6 w)⁻¹ := by rw [hcomm]
    _ = mkQ 6 a' := by rw [map_mul, mul_assoc, mul_inv_cancel, mul_one]

end E6b

section Misc

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.TC.Thin

theorem eq_of_perfect {Q : Type*} [Group Q] (hQ : Group.IsPerfect Q) (σ : Q →* Q)
    (h : ∀ q, σ q * q⁻¹ ∈ Subgroup.center Q) : ∀ q, σ q = q := by
  have hmul : ∀ a b : Q, σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
    intro a b
    have hb := Subgroup.mem_center_iff.mp (h b)
    calc σ (a * b) * (a * b)⁻¹ = σ a * (σ b * b⁻¹ * a⁻¹) := by rw [map_mul]; group
      _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [hb a⁻¹]
      _ = (σ a * a⁻¹) * (σ b * b⁻¹) := by group
  let f : Q →* ↥(Subgroup.center Q) :=
    { toFun := fun q => ⟨σ q * q⁻¹, h q⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; exact hmul a b }
  have hker : commutator Q ≤ f.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.mp (f y).2 (f x))
  intro q
  have hq : q ∈ f.ker := hker (by rw [hQ.commutator_eq_top]; exact Subgroup.mem_top q)
  have : σ q * q⁻¹ = 1 := congrArg Subtype.val (hq : f q = 1)
  exact mul_inv_eq_one.mp this

theorem card_conjSub (m : Y) (H : Subgroup Y) : Nat.card (conjSub m H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj m).injective

theorem conjSub_eq_of_le {m : Y} {H : Subgroup Y} (h : H ≤ conjSub m H) : conjSub m H = H :=
  (Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSub])).symm

theorem rLayer_le_rLayer {f f' : Y}
    (h : rLayer (Om R) f ≤ Subgroup.centralizer ({f'} : Set Y)) :
    rLayer (Om R) f ≤ rLayer (Om R) f' := by
  show (⨆ R' ∈ RSet (Om R), ⨆ (_ : R' ≤ Subgroup.centralizer ({f} : Set Y)), R') ≤ _
  refine iSup₂_le fun R' hR' => iSup_le fun hR'C => ?_
  exact F7C.le_rLayer hR' ((F7C.le_rLayer hR' hR'C).trans h)

theorem conj_mem_cent {a x : Y} (hx : x ∈ Subgroup.centralizer ({a} : Set Y)) (m : Y) :
    m * x * m⁻¹ ∈ Subgroup.centralizer ({m * a * m⁻¹} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc m * x * m⁻¹ * (m * a * m⁻¹) = m * (x * a) * m⁻¹ := by group
    _ = m * (a * x) * m⁻¹ := by rw [hx]
    _ = m * a * m⁻¹ * (m * x * m⁻¹) := by group

theorem conj_mem_sup {A B : Subgroup Y} {c : Y} (hA : ∀ a ∈ A, c * a * c⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, c * b * c⁻¹ ∈ A ⊔ B) : ∀ v ∈ A ⊔ B, c * v * c⁻¹ ∈ A ⊔ B := by
  intro v hv
  rw [Subgroup.sup_eq_closure] at hv
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA x hx
    · exact hB x hx
  | one => simp [Subgroup.one_mem]
  | mul a b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    rwa [show c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ by group] at this
  | inv a _ ha =>
    have := Subgroup.inv_mem _ ha
    rwa [show (c * a * c⁻¹)⁻¹ = c * a⁻¹ * c⁻¹ by group] at this

theorem conj_mem_closure {X : Set Y} {H : Subgroup Y} {c : Y} (hX : ∀ x ∈ X, c * x * c⁻¹ ∈ H) :
    ∀ v ∈ Subgroup.closure X, c * v * c⁻¹ ∈ H := by
  intro v hv
  induction hv using Subgroup.closure_induction with
  | mem x hx => exact hX x hx
  | one => simp [Subgroup.one_mem]
  | mul a b _ _ ha hb =>
    have := Subgroup.mul_mem _ ha hb
    rwa [show c * a * c⁻¹ * (c * b * c⁻¹) = c * (a * b) * c⁻¹ by group] at this
  | inv a _ ha =>
    have := Subgroup.inv_mem _ ha
    rwa [show (c * a * c⁻¹)⁻¹ = c * a⁻¹ * c⁻¹ by group] at this

theorem mem_normalizer_of_conj {H : Subgroup Y} {c : Y} (h1 : ∀ v ∈ H, c * v * c⁻¹ ∈ H)
    (h2 : ∀ v ∈ H, c⁻¹ * v * c ∈ H) : c ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => h1 v hv, fun hv => ?_⟩
  have := h2 _ hv
  simpa [mul_assoc] using this

theorem zOf_eq_ofVec_ind {m : ℕ} (γ : Finset (Fin m)) (hγ : γ.card = 4) :
    zOf (emb γ hγ) = ofVec (fun i => if i ∈ γ then 1 else 0) := by
  classical
  refine Wr.ext (funext fun i => ?_) (zOf_perm _)
  rw [zOf_vec_apply]
  show (if i ∈ Set.range (emb γ hγ) then (1 : ZMod 2) else 0) = if i ∈ γ then 1 else 0
  simp only [range_emb, Finset.mem_coe]

theorem pair_add_ind : ∀ d x : Fin 6, d ≠ x → ∀ i : Fin 6,
    TwinThinPf10.pairVec d x i +
      (if i ∈ (Finset.univ.erase d).erase x then (1 : ZMod 2) else 0) = 1 := by
  decide

theorem card_erase_erase : ∀ d x : Fin 6, d ≠ x → ((Finset.univ.erase d).erase x).card = 4 := by
  decide

theorem even_le_closure (d : Fin 6) :
    TwinThinPf11.evenVec 6 ≤ (Subgroup.closure {x : AEQ 6 | ∃ (γ : Finset (Fin 6))
      (hγ : γ.card = 4), d ∉ γ ∧ x = zBar γ hγ}).comap (mkQ 6) := by
  classical
  set H := Subgroup.closure {x : AEQ 6 | ∃ (γ : Finset (Fin 6)) (hγ : γ.card = 4),
    d ∉ γ ∧ x = zBar γ hγ} with hH
  have hd : ∀ x : Fin 6, ofVec (TwinThinPf10.pairVec d x) ∈ H.comap (mkQ 6) := by
    intro x
    by_cases hdx : d = x
    · subst hdx
      rw [TwinThinPf11.pairVec_self]
      exact Subgroup.one_mem _
    · set γ := (Finset.univ.erase d).erase x with hγdef
      have hγ : γ.card = 4 := card_erase_erase d x hdx
      have hdγ : d ∉ γ := by simp [γ]
      have hprod : ofVec (TwinThinPf10.pairVec d x) * zOf (emb γ hγ) = allOnes 6 := by
        rw [zOf_eq_ofVec_ind, ← TwinThinPf11.ofVec_add]
        refine Wr.ext (funext fun i => ?_) rfl
        exact pair_add_ind d x hdx i
      have h1 : mkQ 6 (ofVec (TwinThinPf10.pairVec d x)) * zBar γ hγ = 1 := by
        rw [show zBar γ hγ = mkQ 6 (zOf (emb γ hγ)) from rfl, ← map_mul, hprod]
        exact (QuotientGroup.eq_one_iff _).mpr (mem_piSub.mpr (Or.inr rfl))
      have hmk : mkQ 6 (ofVec (TwinThinPf10.pairVec d x)) = zBar γ hγ := by
        rw [eq_inv_of_mul_eq_one_left h1]
        exact inv_eq_of_mul_eq_one_right (zBar_mul_self γ hγ)
      show mkQ 6 (ofVec (TwinThinPf10.pairVec d x)) ∈ H
      rw [hmk]
      exact Subgroup.subset_closure ⟨γ, hγ, hdγ, rfl⟩
  refine TwinThinPf11.evenVec_le_closure _ fun x y => ?_
  rw [TwinThinPf11.pairVec_trans x y d, TwinThinPf11.ofVec_add, TwinThinPf11.pairVec_comm x d]
  exact Subgroup.mul_mem _ (hd x) (hd y)

end Misc

section Steps

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.TC.Thin

theorem conjSub_eq_of_ge {m : Y} {H : Subgroup Y} (h : conjSub m H ≤ H) : conjSub m H = H :=
  Subgroup.eq_of_le_of_card_ge h (by rw [card_conjSub])

theorem y_sq_conj {y : Y} (hy3 : y ^ 3 * e = e * y ^ 3) :
    y * (y * e * y⁻¹) * y⁻¹ = y⁻¹ * e * y ∧ y⁻¹ * (y⁻¹ * e * y) * y = y * e * y⁻¹ := by
  have hy3' : y * (y * (y * e)) = e * (y * (y * y)) := by
    simpa [pow_succ, mul_assoc] using hy3
  constructor
  · calc y * (y * e * y⁻¹) * y⁻¹ = y⁻¹ * (y * (y * (y * e))) * (y⁻¹ * (y⁻¹ * y⁻¹)) * y := by
          group
      _ = y⁻¹ * (e * (y * (y * y))) * (y⁻¹ * (y⁻¹ * y⁻¹)) * y := by rw [hy3']
      _ = y⁻¹ * e * y := by group
  · calc y⁻¹ * (y⁻¹ * e * y) * y = y * (y⁻¹ * (y⁻¹ * y⁻¹)) * (e * (y * (y * y))) * y⁻¹ := by
          group
      _ = y * (y⁻¹ * (y⁻¹ * y⁻¹)) * (y * (y * (y * e))) * y⁻¹ := by rw [hy3']
      _ = y * e * y⁻¹ := by group

theorem cent_te (hB : P23E8ACaseB n) (hcit : CIT3Below n)
    (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : ¬ SecNoExit R e)
    (hA5 : SecAE R u 5) (hA6 : SecAE R e 6)
    (hαb : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥)
    (hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥) {y' : Y}
    (hy'Y : y' ∈ rLayer (Om R) u) (hy't : y' * t = t * y')
    (hy'3 : IsPGroup 3 (Subgroup.zpowers y')) (hy'e : y' * e * y'⁻¹ ≠ e)
    (hzt : (y' * e * y'⁻¹) * t = t * (y' * e * y'⁻¹))
    (hze : (y' * e * y'⁻¹) * e = e * (y' * e * y'⁻¹))
    (hzK : ∀ k ∈ tightCore R ⊔ K', (y' * e * y'⁻¹) * k = k * (y' * e * y'⁻¹)) :
    rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({y' * e * y'⁻¹} : Set Y) := by
  set z' := y' * e * y'⁻¹ with hz'
  have hz'te : z' ∈ Subgroup.centralizer ({t * e} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z' * (t * e) = (z' * t) * e := by group
      _ = t * (z' * e) := by rw [hzt]; group
      _ = t * (e * z') := by rw [hze]
      _ = t * e * z' := by group
  have hcC : g * z' * g⁻¹ ∈ Subgroup.centralizer ({u} : Set Y) := by
    have := conj_mem_cent hz'te g
    rwa [g_te hc] at this
  have hKz : tightCore R ⊔ K' ≤ Subgroup.centralizer ({z'} : Set Y) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzK k hk).symm
  have hle : conjSub g (tightCore R) ⊔ conjSub g K' ≤
      Subgroup.centralizer ({g * z' * g⁻¹} : Set Y) :=
    sup_le (conj_le_cent (le_sup_left.trans hKz) g) (conj_le_cent (le_sup_right.trans hKz) g)
  have hcJ : ∀ k ∈ conjSub g (tightCore R) ⊔ conjSub g K',
      (g * z' * g⁻¹) * k = k * (g * z' * g⁻¹) :=
    fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm
  have hte : g⁻¹ * u * g⁻¹⁻¹ = t * e := by
    rw [← g_te hc]
    group
  have hlay : rLayer (Om R) (t * e) = conjSub g⁻¹ (rLayer (Om R) u) := by
    rw [← hte]
    exact rLayer_conj g⁻¹ u
  have hmem : ∀ x ∈ rLayer (Om R) (t * e), g * x * g⁻¹ ∈ rLayer (Om R) u := by
    intro x hx
    rw [hlay, mem_conjSub_iff, inv_inv] at hx
    exact hx
  have hcancel : ∀ a b : Y, g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹) →
      a * b = b * a := by
    intro a b h
    have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    calc a * b = g⁻¹ * (g * (a * b) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (b * a) * g⁻¹) * g := by rw [h2]
      _ = b * a := by group
  rcases s2_u hc hA5 h2grp hOu hcC hcJ with hA | hcase
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcancel _ _ (hA _ (hmem x hx))).symm
  · exfalso
    apply hB hcit hP Y R S t K' W u e g hc hno hA5 hA6 hαb y' hy'Y hy't hy'3 (fun o ho => by
      rw [hOt, Subgroup.mem_bot] at ho
      subst ho
      simpa using hy'e)
    intro x hx
    have h1 := hcase _ (hmem x hx)
    have hue : u * e * (g * z' * g⁻¹) = g * (t * z') * g⁻¹ := by
      rw [← hc.data.hgt]
      group
    rw [hue] at h1
    exact hcancel _ _ h1

variable {hc : P23Cfg n Y R S t K' W u e g}
  {D : ZTwo.AECover (SecQ R e) (TwinDisc.secFam (Om R) e)}

theorem acts_cent {c : Y} (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {w : Wr 6}
    (hw : D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩) w)
    {L : Subgroup Y} (hcL : ∀ k ∈ L, c * k = k * c) {γ : Finset (Fin 6)} {hγ : γ.card = 4}
    {b : Bool} (hl : (secImg (Om R) e L).map D.φ = memBar γ hγ b) :
    ∀ x ∈ memBar γ hγ b, mkQ 6 w * x * (mkQ 6 w)⁻¹ = x := by
  intro x hx
  rw [← hl] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  rw [← hw q, fix_of_cent (hc := hc) hcC hcL q hq]

theorem not_zbar (hOE : oddCoreOf (rLayer (Om R) e) = ⊥) {y : Y}
    (hte : rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y))
    (hy3 : y ^ 3 * e = e * y ^ 3) (hyt : y * t = t * y) (hye : y * e * y⁻¹ ≠ e)
    {β : Finset (Fin 6)} {hβ : β.card = 4} (hzt : D.φ (ZTwo.tbar hc) = zBar β hβ)
    (hcC : y⁻¹ * e * y ∈ Subgroup.centralizer ({e} : Set Y)) {w : Wr 6}
    (hw : D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨y⁻¹ * e * y, hcC⟩) w) :
    mkQ 6 w ≠ zBar β hβ := by
  intro hwz
  have htE := (ZTwo.t_e_mem_rLayer hc).1
  have htC : t ∈ Subgroup.centralizer ({e} : Set Y) := rLayer_le_centralizer (Om R) e htE
  set a := t * (y⁻¹ * e * y) with ha
  have haC : a ∈ Subgroup.centralizer ({e} : Set Y) := Subgroup.mul_mem _ htC hcC
  set σa := TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨a, haC⟩ with hσa
  have hσa' : ∀ q, σa q = ZTwo.tbar hc *
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨y⁻¹ * e * y, hcC⟩ q) *
      (ZTwo.tbar hc)⁻¹ := by
    intro q
    have h1 := ZTwo.secAut_mul hc ⟨t, htC⟩ ⟨y⁻¹ * e * y, hcC⟩ q
    rw [show (⟨t, htC⟩ : ↥(Subgroup.centralizer ({e} : Set Y))) * ⟨y⁻¹ * e * y, hcC⟩ =
      ⟨a, haC⟩ from rfl] at h1
    rw [h1, ZTwo.secAut_t hc htC]
  have hm2 : mkQ 6 w * mkQ 6 w = 1 := by rw [hwz]; exact zBar_mul_self β hβ
  have hfix : ∀ q, σa q = q := by
    apply eq_of_perfect D.perfect σa.toMonoidHom
    intro q
    apply D.ker_le
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    show D.φ (σa q) * (D.φ q)⁻¹ = 1
    rw [hσa' q, map_mul, map_mul, map_inv, hw q, hzt, ← hwz]
    calc mkQ 6 w * (mkQ 6 w * D.φ q * (mkQ 6 w)⁻¹) * (mkQ 6 w)⁻¹ * (D.φ q)⁻¹ =
        (mkQ 6 w * mkQ 6 w) * D.φ q * (mkQ 6 w * mkQ 6 w)⁻¹ * (D.φ q)⁻¹ := by group
      _ = 1 := by rw [hm2]; group
  have haE : rLayer (Om R) e ≤ Subgroup.centralizer ({a} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hax : a * x * a⁻¹ ∈ rLayer (Om R) e := conj_mem_E (ZTwo.hΩ_of hc) haC hx
    have h1 := ZTwo.secAut_piE hc haC ⟨x, hx⟩ hax
    rw [hfix] at h1
    have h3 : x = a * x * a⁻¹ := congrArg Subtype.val (piE_inj hOE h1)
    calc x * a = a * x * a⁻¹ * a := by rw [← h3]
      _ = a * x := by group
  have hEa : rLayer (Om R) e ≤ rLayer (Om R) a := rLayer_le_rLayer haE
  have hyt' : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have ha_eq : y⁻¹ * (t * e) * y⁻¹⁻¹ = a := by
    rw [inv_inv, ha]
    calc y⁻¹ * (t * e) * y = (y⁻¹ * t) * e * y := by group
      _ = t * y⁻¹ * e * y := by rw [hyt']
      _ = t * (y⁻¹ * e * y) := by group
  have hlaya : rLayer (Om R) a = conjSub y⁻¹ (rLayer (Om R) (t * e)) := by
    rw [← ha_eq]
    exact rLayer_conj y⁻¹ (t * e)
  have hEy : rLayer (Om R) e ≤ Subgroup.centralizer ({y * e * y⁻¹} : Set Y) := by
    have h1 := conj_le_cent hte y⁻¹
    rw [inv_inv, (y_sq_conj hy3).2] at h1
    exact hEa.trans (by rw [hlaya]; exact h1)
  have hEE : rLayer (Om R) e ≤ conjSub y (rLayer (Om R) e) := by
    rw [← rLayer_conj]
    exact rLayer_le_rLayer hEy
  exact conj_ne (hc := hc) (D := D) hOE hye (conjSub_eq_of_le hEE)

theorem members_off (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J)
    (hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)) {w : Wr 6}
    (hw : D.toAEData.Acts
      (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩) w)
    (hwp : w.perm = 1) {d : Fin 6} (hd : ∀ i j, i ≠ d → j ≠ d → w.vec i = w.vec j)
    {γ : Finset (Fin 6)} (hγ : γ.card = 4) (hdγ : d ∉ γ) :
    ∃ J ∈ Om R, J ≤ Subgroup.centralizer ({e} : Set Y) ∧
      J ≤ Subgroup.centralizer ({c} : Set Y) ∧ ∃ z : Y, IsUniqueInvolution J z ∧
        ∃ hzE : z ∈ rLayer (Om R) e, D.φ (ZTwo.piE hc ⟨z, hzE⟩) = zBar γ hγ := by
  obtain ⟨L, hL, hl⟩ := D.label_surj γ hγ true
  obtain ⟨J, hJtq, rfl⟩ := exists_of_mem_secFam hL
  have hJe := le_cent_of_tq hJtq (h2grp _ hJtq.1)
  have hfix := fix_of_acts (fun L hL => ZTwo.secAut_preserves hc ⟨c, hcC⟩ hL) hw hL hl
    (cent_of_const hwp hd hγ hdγ true)
  have hcJ := cent_of_fix (hc := hc) h2grp hOe hcC hJtq.1 hJe hfix
  obtain ⟨m, hm⟩ := hJtq.1
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution J (m * t * m⁻¹) :=
    hm ▸ (Inner.isUniqueInvolution_core hC.datum).conj m
  obtain ⟨hzC, hzY, hzA⟩ := isUniqueInvolution_secImg (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) hJtq hz
  have hzE : m * t * m⁻¹ ∈ rLayer (Om R) e :=
    TwinPerpV3.A6b.le_rLayer_of_mem hJtq.1 (h2grp _ hJtq.1) hJe hz.mem
  refine ⟨J, hJtq.1, hJe, fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hcJ k hk).symm,
    m * t * m⁻¹, hz, hzE, ?_⟩
  calc D.φ (ZTwo.piE hc ⟨m * t * m⁻¹, hzE⟩) =
      D.φ (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) e))
        ⟨⟨m * t * m⁻¹, hzC⟩, hzY⟩) :=
        congrArg D.φ (ZTwo.piE_mk hc ⟨⟨m * t * m⁻¹, hzC⟩, hzY⟩ hzE)
    _ = zBar γ hγ := D.map_eq_zBar hL hl hzA

theorem qE_conj (h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J) (hOE : oddCoreOf (rLayer (Om R) e) = ⊥)
    {y : Y} {d : Fin 6}
    (hoff : ∀ (γ : Finset (Fin 6)) (hγ : γ.card = 4), d ∉ γ →
      ∃ J ∈ Om R, J ≤ Subgroup.centralizer ({e} : Set Y) ∧
        J ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y) ∧ ∃ z : Y, IsUniqueInvolution J z ∧
          ∃ hzE : z ∈ rLayer (Om R) e, D.φ (ZTwo.piE hc ⟨z, hzE⟩) = zBar γ hγ) :
    ∀ q ∈ qE hc D, y * q * y⁻¹ ∈ Subgroup.closure {y * e * y⁻¹} ⊔ qE hc D := by
  intro q hq
  obtain ⟨hqE, hφ⟩ := mem_qE.mp hq
  have hΩ := ZTwo.hΩ_of hc
  set T := Subgroup.closure {s : Y | ∃ J ∈ Om R, J ≤ Subgroup.centralizer ({e} : Set Y) ∧
    J ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y) ∧ IsUniqueInvolution J s} with hT
  have hyT : ∀ s ∈ T, y * s * y⁻¹ ∈ qE hc D := by
    refine conj_mem_closure ?_
    rintro s ⟨J, hJ, -, hJy, hs⟩
    have hJye : conjSub y J ≤ Subgroup.centralizer ({e} : Set Y) := by
      have := conj_le_cent hJy y
      rwa [show y * (y⁻¹ * e * y) * y⁻¹ = e by group] at this
    exact member_inv_mem_qE (hc := hc) (D := D) h2grp (hΩ.conjInvariant y J hJ) hJye (hs.conj y)
  have hφT : D.φ (ZTwo.piE hc ⟨q, hqE⟩) ∈ (T.subgroupOf (rLayer (Om R) e)).map (phiE hc D) := by
    have hr : D.φ (ZTwo.piE hc ⟨q, hqE⟩) ∈ TwinThinPf8.Hn 6 := by
      rw [← D.range_eq]
      exact ⟨_, rfl⟩
    obtain ⟨a, ha, hae⟩ := hr
    obtain ⟨v, hv, hve⟩ := hφ
    have hvp : v.perm = 1 := hv
    have hap : a.perm = 1 := by
      rcases mkQ_eq_iff.mp (hae.trans hve.symm) with h | h
      · have := congrArg Wr.perm h
        rw [mul_perm, inv_perm, hvp, mul_one, one_perm] at this
        exact inv_eq_one.mp this
      · have := congrArg Wr.perm h
        rw [mul_perm, inv_perm, hvp, mul_one] at this
        exact inv_eq_one.mp this
    have haev : a ∈ TwinThinPf11.evenVec 6 := ⟨hap, ha.1⟩
    have h1 := even_le_closure d haev
    rw [Subgroup.mem_comap] at h1
    rw [← hae]
    refine (Subgroup.closure_le _).mpr ?_ h1
    rintro _ ⟨γ, hγ, hdγ, rfl⟩
    obtain ⟨J, hJ, hJe, hJy, z, hz, hzE, hzφ⟩ := hoff γ hγ hdγ
    exact ⟨⟨z, hzE⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.subset_closure ⟨J, hJ, hJe, hJy, hz⟩), hzφ⟩
  obtain ⟨s, hsT, hsφ⟩ := hφT
  have hsT' : (s : Y) ∈ T := Subgroup.mem_subgroupOf.mp hsT
  have hk : D.φ (ZTwo.piE hc (s⁻¹ * ⟨q, hqE⟩)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv]
    have : D.φ (ZTwo.piE hc s) = D.φ (ZTwo.piE hc ⟨q, hqE⟩) := hsφ
    rw [this, inv_mul_cancel]
  rcases ker_phi hOE hk with h1 | h1
  · have hqs : q = (s : Y) := by
      have h2 : (s : Y)⁻¹ * q = 1 := h1
      calc q = (s : Y) * ((s : Y)⁻¹ * q) := by group
        _ = (s : Y) := by rw [h2, mul_one]
    rw [hqs]
    exact Subgroup.mem_sup_right (hyT _ hsT')
  · have hqs : q = (s : Y) * e := by
      have h2 : (s : Y)⁻¹ * q = e := h1
      calc q = (s : Y) * ((s : Y)⁻¹ * q) := by group
        _ = (s : Y) * e := by rw [h2]
    rw [hqs, show y * ((s : Y) * e) * y⁻¹ = (y * (s : Y) * y⁻¹) * (y * e * y⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hyT _ hsT'))
      (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))

end Steps








end AXV

section Main

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.TC.Thin

theorem p23E8AXV_of_caseB (hE : TwinThmEW.ThmEQ8)
    (hα : P23Alpha n) (hZ8 : P23E8AZ8 n) (hB : P23E8ACaseB n) : P23E8AXV n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hA5 hA6 hαb
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have h2grp : ∀ J ∈ Om R, IsPGroup 2 ↥J := p23E8A_members_isPGroup hE hcit hP hc hA5 hαb
  have hOt : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    p23E8A_oddCoreIn_eq_bot hE hcit hP hc hA5 hαb
  have hOCu : oddCoreOf (Subgroup.centralizer ({u} : Set Y)) = ⊥ := by
    have h := p23E8A_oddCoreIn_eq_bot hE hcit hP hc hA5 hαb
    rw [p23E8A_oddCoreIn_eq hc hA5 hαb] at h
    exact h
  have hOE : oddCoreOf (rLayer (Om R) e) = ⊥ :=
    AXV.layer_bot hΩ (AXV.ce_bot hE hα hcit hP hc hA5 hαb)
  have hOe : classicalInvolutionOddCore ↥(coreHull (Om R) e) = ⊥ :=
    AXV.hull_bot hΩ (ZTwo.hc2e_of hc) (ZTwo.h2_of hc) hOE
  have hc2u : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hOu : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥ :=
    AXV.hull_bot hΩ hc2u (ZTwo.h2_of hc) (AXV.layer_bot hΩ hOCu)
  obtain ⟨D⟩ := ZTwo.exists_cover hc hA6
  obtain ⟨y, hyY, hyt, hy3, hye, hy3e⟩ := AXV.y_spec hZ8 hcit hP hc hno hA5 hA6 hOt
  obtain ⟨hZab, hZsq, -, hZe, hyZ, -, hZK⟩ :=
    AXV.zSub_props hcit hP hc hno hA5 hA6 hOt h2grp hyt hy3e
  obtain ⟨htZ, heZ, heyZ, heyZ'⟩ := AXV.gen_mem_zSub (t := t) (e := e) (y := y)
  set Z := AXV.zSub t e y with hZdef
  obtain ⟨hy2a, hy2b⟩ := AXV.y_sq_conj hy3e
  have hyt' : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have hye' : y⁻¹ * e * y⁻¹⁻¹ ≠ e := by
    rw [inv_inv]
    intro h
    apply hye
    calc y * e * y⁻¹ = y * (y⁻¹ * e * y) * y⁻¹ := by rw [h]
      _ = e := by group
  have hy3' : IsPGroup 3 (Subgroup.zpowers y⁻¹) := by rw [Subgroup.zpowers_inv]; exact hy3
  have hT1 : rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({y * e * y⁻¹} : Set Y) :=
    AXV.cent_te hB hcit hP hc hno hA5 hA6 hαb h2grp hOt hOu hyY hyt hy3 hye
      (hZab _ heyZ _ htZ) (hZab _ heyZ _ heZ) (hZK _ heyZ)
  have hT2 : rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({y⁻¹ * e * y} : Set Y) := by
    have h := AXV.cent_te hB hcit hP hc hno hA5 hA6 hαb h2grp hOt hOu
      (Subgroup.inv_mem _ hyY) hyt' hy3' hye'
      (by rw [inv_inv]; exact hZab _ heyZ' _ htZ) (by rw [inv_inv]; exact hZab _ heyZ' _ heZ)
      (by rw [inv_inv]; exact hZK _ heyZ')
    rwa [inv_inv] at h
  obtain ⟨M, hM, M', hM', hMu, hM'u, hMM', zM, hzM, hzM', hzMue⟩ :=
    AXV.u_other hc hA5 h2grp hOu
  have hgte : g⁻¹ * u * g⁻¹⁻¹ = t * e := by
    rw [← AXV.g_te hc]
    group
  have hJ₀te : conjSub g⁻¹ M ≤ Subgroup.centralizer ({t * e} : Set Y) := by
    have := AXV.conj_le_cent hMu g⁻¹
    rwa [hgte] at this
  have hJ₀'te : conjSub g⁻¹ M' ≤ Subgroup.centralizer ({t * e} : Set Y) := by
    have := AXV.conj_le_cent hM'u g⁻¹
    rwa [hgte] at this
  have hJ₀Ω : conjSub g⁻¹ M ∈ Om R := hΩ.conjInvariant g⁻¹ M hM
  have hJ₀'Ω : conjSub g⁻¹ M' ∈ Om R := hΩ.conjInvariant g⁻¹ M' hM'
  have hJ₀L := TwinPerpV3.A6b.le_rLayer_of_mem hJ₀Ω (h2grp _ hJ₀Ω) hJ₀te
  have hJ₀'L := TwinPerpV3.A6b.le_rLayer_of_mem hJ₀'Ω (h2grp _ hJ₀'Ω) hJ₀'te
  have hz₀ := hzM.conj g⁻¹
  have hz₀' := hzM'.conj g⁻¹
  have hz₀t : g⁻¹ * zM * g⁻¹⁻¹ ≠ t := by
    intro h
    apply hzMue
    calc zM = g * (g⁻¹ * zM * g⁻¹⁻¹) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [h]
      _ = u * e := hd.hgt
  have hJ₀ne : conjSub g⁻¹ M' ≠ conjSub g⁻¹ M := by
    intro h
    apply hMM'
    have := congrArg (conjSub g) h
    rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
    exact this.symm
  have hc₁C : y⁻¹ * e * y ∈ Subgroup.centralizer ({e} : Set Y) := hZe heyZ'
  have hc₂C : y * e * y⁻¹ ∈ Subgroup.centralizer ({e} : Set Y) := hZe heyZ
  have key_perm : ∀ (m c : Y) (hcC : c ∈ Subgroup.centralizer ({e} : Set Y)),
      (∀ k ∈ tightCore R ⊔ K', c * k = k * c) →
      conjSub m (conjSub g⁻¹ M) ≤ Subgroup.centralizer ({e} : Set Y) →
      conjSub m (conjSub g⁻¹ M') ≤ Subgroup.centralizer ({e} : Set Y) →
      conjSub m (conjSub g⁻¹ M) ≤ Subgroup.centralizer ({c} : Set Y) →
      conjSub m (conjSub g⁻¹ M') ≤ Subgroup.centralizer ({c} : Set Y) →
      m * t * m⁻¹ = t → ∀ w : Wr 6, D.toAEData.Acts
        (TwinExitPf6.secAut (Om R) e (ZTwo.hΩ_of hc) (ZTwo.hc2e_of hc) ⟨c, hcC⟩) w →
        w.perm = 1 := by
    intro m c hcC hcK h1 h2 h3 h4 hmt w hw
    have hne : conjSub m (conjSub g⁻¹ M') ≠ conjSub m (conjSub g⁻¹ M) := by
      intro h
      apply hJ₀ne
      have := congrArg (conjSub m⁻¹) h
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    have hzt' : m * (g⁻¹ * zM * g⁻¹⁻¹) * m⁻¹ ≠ t := by
      intro h
      apply hz₀t
      calc g⁻¹ * zM * g⁻¹⁻¹ = m⁻¹ * (m * (g⁻¹ * zM * g⁻¹⁻¹) * m⁻¹) * m := by group
        _ = m⁻¹ * t * m := by rw [h]
        _ = m⁻¹ * (m * t * m⁻¹) * m := by rw [hmt]
        _ = t := by group
    exact AXV.perm_one (hc := hc) (D := D) h2grp hOe hcC hcK (hΩ.conjInvariant m _ hJ₀Ω)
      (hΩ.conjInvariant m _ hJ₀'Ω) h1 h2 hne (hz₀.conj m) (hz₀'.conj m) hzt'
      (fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (h3 hk)).symm)
      (fun k hk => (Subgroup.mem_centralizer_singleton_iff.mp (h4 hk)).symm) hw
  obtain ⟨w₁, hw₁⟩ := AXV.exists_acts (hc := hc) (D := D) hc₁C
  obtain ⟨w₂, hw₂⟩ := AXV.exists_acts (hc := hc) (D := D) hc₂C
  have hw₁p : w₁.perm = 1 := by
    refine key_perm y _ hc₁C (hZK _ heyZ') ?_ ?_ ?_ ?_ (by rw [hyt, mul_inv_cancel_right]) w₁ hw₁
    · have := AXV.conj_le_cent (hJ₀L.trans hT2) y
      rwa [show y * (y⁻¹ * e * y) * y⁻¹ = e by group] at this
    · have := AXV.conj_le_cent (hJ₀'L.trans hT2) y
      rwa [show y * (y⁻¹ * e * y) * y⁻¹ = e by group] at this
    · have := AXV.conj_le_cent (hJ₀L.trans hT1) y
      rwa [hy2a] at this
    · have := AXV.conj_le_cent (hJ₀'L.trans hT1) y
      rwa [hy2a] at this
  have hw₂p : w₂.perm = 1 := by
    refine key_perm y⁻¹ _ hc₂C (hZK _ heyZ) ?_ ?_ ?_ ?_
      (by rw [inv_inv, hyt', inv_mul_cancel_right]) w₂ hw₂
    · have := AXV.conj_le_cent (hJ₀L.trans hT1) y⁻¹
      rwa [show y⁻¹ * (y * e * y⁻¹) * y⁻¹⁻¹ = e by group] at this
    · have := AXV.conj_le_cent (hJ₀'L.trans hT1) y⁻¹
      rwa [show y⁻¹ * (y * e * y⁻¹) * y⁻¹⁻¹ = e by group] at this
    · have := AXV.conj_le_cent (hJ₀L.trans hT2) y⁻¹
      rwa [inv_inv, hy2b] at this
    · have := AXV.conj_le_cent (hJ₀'L.trans hT2) y⁻¹
      rwa [inv_inv, hy2b] at this
  set Q := AXV.qE hc D with hQdef
  set V₀ := Z ⊔ Q with hV₀def
  obtain ⟨β, hβ, b₀, hlA, hlA', hzt, -, -, -⟩ := ZTwo.twin_labels hc D
  have htE := (ZTwo.t_e_mem_rLayer hc).1
  have heE := (ZTwo.t_e_mem_rLayer hc).2
  have htQ : t ∈ Q := by
    refine AXV.mem_qE.mpr ⟨htE, ?_⟩
    have h : D.φ (ZTwo.piE hc ⟨t, htE⟩) = zBar β hβ := hzt
    rw [h]
    exact AXV.zBar_mem_vBar β hβ
  have hgenE : ∀ x ∈ rLayer (Om R) e, ∀ s ∈ ({t, e, y * e * y⁻¹, y⁻¹ * e * y} : Set Y),
      x * s * x⁻¹ ∈ V₀ := by
    intro x hx s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with h | h | h | h <;> rw [h]
    · exact Subgroup.mem_sup_right (AXV.qE_conj_E hx htQ)
    · have hxe : x * e * x⁻¹ = e := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp (rLayer_le_centralizer (Om R) e hx),
          mul_inv_cancel_right]
      rw [hxe]
      exact Subgroup.mem_sup_left heZ
    · have h1 := AXV.comm_qE (hc := hc) (D := D) hc₂C hw₂ hw₂p hx
      rw [show x * (y * e * y⁻¹) * x⁻¹ =
        (x * (y * e * y⁻¹) * x⁻¹ * (y * e * y⁻¹)⁻¹) * (y * e * y⁻¹) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left heyZ)
    · have h1 := AXV.comm_qE (hc := hc) (D := D) hc₁C hw₁ hw₁p hx
      rw [show x * (y⁻¹ * e * y) * x⁻¹ =
        (x * (y⁻¹ * e * y) * x⁻¹ * (y⁻¹ * e * y)⁻¹) * (y⁻¹ * e * y) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left heyZ')
  have hVE : ∀ x ∈ rLayer (Om R) e, ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀ := fun x hx =>
    AXV.conj_mem_sup (AXV.conj_mem_closure (hgenE x hx))
      (fun q hq => Subgroup.mem_sup_right (AXV.qE_conj_E hx hq))
  have hw₁B : ∀ b : Bool, ∀ x ∈ memBar β hβ b, mkQ 6 w₁ * x * (mkQ 6 w₁)⁻¹ = x := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact AXV.acts_cent (hc := hc) hc₁C hw₁
        (fun k hk => hZK _ heyZ' k (Subgroup.mem_sup_left hk)) hlA
    · have hb' := AXV.bool_eq_not_of_ne hb
      subst hb'
      exact AXV.acts_cent (hc := hc) hc₁C hw₁
        (fun k hk => hZK _ heyZ' k (Subgroup.mem_sup_right hk)) hlA'
  obtain ⟨dd, hdd⟩ : ∃ d : Fin 6, ∀ i j, i ≠ d → j ≠ d → w₁.vec i = w₁.vec j := by
    rcases AXV.vec_type hβ hw₁p hw₁B with h | h
    · exact h
    · exact absurd h (AXV.not_zbar (hc := hc) (D := D) hOE hT2 hy3e hyt hye hzt hc₁C hw₁)
  have hQy : ∀ q ∈ Q, y * q * y⁻¹ ∈ V₀ := by
    intro q hq
    have h1 := AXV.qE_conj (hc := hc) (D := D) h2grp hOE
      (fun γ hγ hdγ => AXV.members_off (hc := hc) (D := D) h2grp hOe hc₁C hw₁ hw₁p hdd hγ hdγ)
      q hq
    have hle : Subgroup.closure {y * e * y⁻¹} ⊔ Q ≤ V₀ :=
      sup_le_sup_right ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr heyZ)) Q
    exact hle h1
  have hyV : ∀ v ∈ V₀, y * v * y⁻¹ ∈ V₀ :=
    AXV.conj_mem_sup (fun z hz => Subgroup.mem_sup_left (hyZ z hz)) hQy
  have hcV : conjSub y V₀ = V₀ := AXV.conjSub_eq_of_ge (by
    rintro _ ⟨v, hv, rfl⟩
    exact hyV v hv)
  have hyV' : ∀ v ∈ V₀, y⁻¹ * v * y ∈ V₀ := by
    intro v hv
    rw [← hcV, mem_conjSub_iff] at hv
    exact hv
  have hVEy : ∀ x ∈ conjSub y (rLayer (Om R) e), ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀ := by
    intro x hx v hv
    rw [mem_conjSub_iff] at hx
    have h2 := hyV _ (hVE _ hx _ (hyV' v hv))
    rwa [show y * (y⁻¹ * x * y * (y⁻¹ * v * y) * (y⁻¹ * x * y)⁻¹) * y⁻¹ = x * v * x⁻¹ by
      group] at h2
  have hXN : p23XE R e y ≤ Subgroup.normalizer (V₀ : Set Y) := by
    show rLayer (Om R) e ⊔ conjSub y (rLayer (Om R) e) ≤ _
    refine sup_le (fun x hx => AXV.mem_normalizer_of_conj (hVE x hx) fun v hv => ?_)
      (fun x hx => AXV.mem_normalizer_of_conj (hVEy x hx) fun v hv => ?_)
    · simpa using hVE x⁻¹ (Subgroup.inv_mem _ hx) v hv
    · simpa using hVEy x⁻¹ (Subgroup.inv_mem _ hx) v hv
  have hZ2 : IsPGroup 2 Z := by
    intro a
    refine ⟨1, ?_⟩
    ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
    exact hZsq a a.2
  have hQ2 := AXV.qE_isPGroup (hc := hc) (D := D) hOE
  have hZQ : Z ≤ Subgroup.normalizer (Q : Set Y) := fun z hz =>
    AXV.mem_normalizer_of_conj (fun q hq => AXV.qE_conj_C (hZe hz) hq)
      (fun q hq => by simpa using AXV.qE_conj_C (Subgroup.inv_mem _ (hZe hz)) hq)
  have hV2 : IsPGroup 2 V₀ := hZ2.to_sup_of_normal_right' hQ2 hZQ
  have hK₀Ω : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK₀e := AXV.le_cent_of_tq (ZTwo.twins_tq hc).1 (h2grp _ hK₀Ω)
  have hXE : rLayer (Om R) e ≤ p23XE R e y := le_sup_left
  have hXEy : conjSub y (rLayer (Om R) e) ≤ p23XE R e y := le_sup_right
  refine ⟨y, V₀ ⊓ p23XE R e y, inf_le_right, ?_, hV2.to_le inf_le_left,
    ⟨Subgroup.mem_sup_left htZ, hXE htE⟩, ⟨Subgroup.mem_sup_left heZ, hXE heE⟩,
    ⟨Subgroup.mem_sup_left heyZ, hXEy (conj_mem_conjSub heE)⟩,
    AXV.conj_ne (hc := hc) (D := D) hOE hye, tightCore R, hK₀Ω,
    TwinPerpV3.A6b.le_rLayer_of_mem hK₀Ω (h2grp _ hK₀Ω) hK₀e, ?_⟩
  · intro x hx v hv
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXN hx) v).mp hv.1, ?_⟩
    exact (p23XE R e y).mul_mem ((p23XE R e y).mul_mem hx hv.2) ((p23XE R e y).inv_mem hx)
  · rw [← rLayer_conj]
    exact TwinPerpV3.A6b.le_rLayer_of_mem hK₀Ω (h2grp _ hK₀Ω) (fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hZK _ heyZ k (Subgroup.mem_sup_left hk)).symm)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
