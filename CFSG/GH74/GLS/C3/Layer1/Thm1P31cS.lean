module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cG
public import CFSG.GH74.GLS.C3.Layer1.St1P41Lift
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cTw
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cY
public import CFSG.GH74.GLS.TwoThin.G.C2Vertical

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  CFSG.GH74.GLS.EvenSelP CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P31c

section Orders

theorem card_hasL2Model_odd {J : Type} [Group J] (h : HasL2Model J Odd) :
    ∃ k : ℕ, 2 ≤ k ∧ Nat.card J = 2 * k * (k + 1) * (2 * k + 1) := by
  obtain ⟨p, f, hp, hf, hodd, hL⟩ := h
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hodd
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  obtain ⟨hodd', h3⟩ := three_lt_of_lieModel_psl_two hp2 hL
  obtain ⟨k, hk⟩ := hodd'
  refine ⟨k, by omega, ?_⟩
  rw [card_of_lieModel_psl2' hL, hk]
  exact PumpClass.ordA_one_odd k

theorem sixty_le_card_of_hasL2Model_odd {J : Type} [Group J] (h : HasL2Model J Odd) :
    60 ≤ Nat.card J := by
  obtain ⟨k, hk, hc⟩ := card_hasL2Model_odd h
  rw [hc]
  have h1 : 2 * 2 * (2 + 1) * (2 * 2 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr
  omega

theorem three_dvd_card_of_hasL2Model_odd {J : Type} [Group J] (h : HasL2Model J Odd) :
    3 ∣ Nat.card J := by
  obtain ⟨k, hk, hc⟩ := card_hasL2Model_odd h
  rw [hc]
  have : (2 * k * (k + 1) * (2 * k + 1)) % 3 = 0 := by
    have h3 := Nat.mod_lt k (by norm_num : 0 < 3)
    interval_cases hr : k % 3 <;> simp [Nat.mul_mod, Nat.add_mod, hr]
  exact Nat.dvd_of_mod_eq_zero this

end Orders

section Stable

variable {G : Type} [Group G] [Finite G] {x w z b p : G} {K Λ : Subgroup G}

theorem orderOf_barMk_wY (hw2 : orderOf w = 2) :
    orderOf (barMk ↥(centralizer ({w} : Set G)) (wY w)) = 2 :=
  orderOf_barMk (orderOf_mk_centralizer (mem_centralizer_singleton_iff.2 rfl) hw2)

omit [Finite G] in
theorem PumpHyp.hΛC (H : PumpHyp x w z b p K Λ) :
    Λ.subgroupOf (centralizer ({w} : Set G)) ≤
      centralizer ({(⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G)))} : Set ↥(centralizer ({w} : Set G))) :=
  le_centralizer_mk H.hΛW H.hxY

theorem PumpHyp.hΛ2 (H : PumpHyp x w z b p K Λ) :
    TwoComponents.IsTwoComponent
      ((Λ.subgroupOf (centralizer ({w} : Set G))).subgroupOf
        (centralizer ({(⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G)))} :
          Set ↥(centralizer ({w} : Set G))))) :=
  isTwoComponent_centralizer_mk H.hΛ H.hxY

theorem PumpHyp.bar_perfect (H : PumpHyp x w z b p K Λ) : ⁅bar w Λ, bar w Λ⁆ = bar w Λ := by
  have hperfY : ⁅Λ.subgroupOf (centralizer ({w} : Set G)), Λ.subgroupOf (centralizer ({w} : Set G))⁆ =
      Λ.subgroupOf (centralizer ({w} : Set G)) := commutator_self_of_isTwoComponent H.hΛC H.hΛ2
  unfold bar
  rw [← Subgroup.map_commutator, hperfY]

theorem PumpHyp.bar_ne_bot (H : PumpHyp x w z b p K Λ) : bar w Λ ≠ ⊥ :=
  map_barMk_ne_bot_of_perfect (commutator_self_of_isTwoComponent H.hΛC H.hΛ2)
    (ne_bot_of_isTwoComponent H.hΛ2)

theorem PumpHyp.bar_subnormal (H : PumpHyp x w z b p K Λ) :
    ((bar w Λ).subgroupOf (centralizer ({sbar x H.hxY} : Set _))).IsSubnormal := by
  have hmap2 := isTwoComponent_map_barMk H.hsO H.hΛC H.hΛ2
  exact Components.mathlib_subnormal_of_chain hmap2.1 Subgroup.IsSubnormal.top

omit [Finite G] in
theorem PumpHyp.bar_fixed (H : PumpHyp x w z b p K Λ) :
    ∀ m ∈ bar w Λ, sbar x H.hxY * m * (sbar x H.hxY)⁻¹ = m := by
  rintro _ ⟨a, ha, rfl⟩
  have hax : (a : G) * x = x * (a : G) :=
    mem_centralizer_singleton_iff.1 (H.hΛW (Subgroup.mem_subgroupOf.1 ha)).1
  have : (⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G))) * a * (⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G)))⁻¹ = a := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc x * (a : G) * x⁻¹ = (a : G) * x * x⁻¹ := by rw [← hax]
      _ = a := by group
  simp only [sbar]
  rw [← map_inv, ← map_mul, ← map_mul, this]

theorem PumpHyp.exists_phi' (H : PumpHyp x w z b p K Λ) :
    ∃ φ : ↥(bar w Λ) →* kBar Λ, Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
  obtain ⟨φ, hφs, hφo, -⟩ := exists_phi (le_refl Λ) H.hΛY
    (fun k hk => ⟨k, hk, 1, (pPrimeCoreOf 2 Λ).one_mem, (mul_one k).symm⟩)
  exact ⟨φ, hφs, hφo⟩

structure StableData (H : PumpHyp x w z b p K Λ)
    (L : Subgroup (barQ ↥(centralizer ({w} : Set G)))) : Prop where
  hL : CFSG.IsComponent L
  hst : conjSub (barMk ↥(centralizer ({w} : Set G)) ⟨x, H.hxY⟩)⁻¹ L = L
  hΛL : bar w Λ ≤ L
  hwL : barMk ↥(centralizer ({w} : Set G)) (wY w) ∈ L
  hwc : ∀ l ∈ L, barMk ↥(centralizer ({w} : Set G)) (wY w) * l =
    l * barMk ↥(centralizer ({w} : Set G)) (wY w)

variable {H : PumpHyp x w z b p K Λ} {L : Subgroup (barQ ↥(centralizer ({w} : Set G)))}

theorem StableData.center_ne_bot (S : StableData H L) : Subgroup.center ↥L ≠ ⊥ := by
  intro hcen
  have hmem : (⟨barMk ↥(centralizer ({w} : Set G)) (wY w), S.hwL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (S.hwc g g.2).symm
  rw [hcen, Subgroup.mem_bot] at hmem
  have h1 : barMk ↥(centralizer ({w} : Set G)) (wY w) = 1 := congrArg Subtype.val hmem
  have h2 := orderOf_barMk_wY (G := G) H.hw2
  rw [h1, orderOf_one] at h2
  omega

theorem StableData.hN (S : StableData H L) : sbar x H.hxY ∈ normalizer (L : Set _) := by
  have hs2 : orderOf (sbar x H.hxY) = 2 := orderOf_sbar H.hx2 H.hxY
  have hsinv : (barMk ↥(centralizer ({w} : Set G)) ⟨x, H.hxY⟩)⁻¹ =
      barMk ↥(centralizer ({w} : Set G)) ⟨x, H.hxY⟩ := inv_eq_self_of_orderOf_eq_two hs2
  have h := S.hst
  rw [hsinv] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

@[expose] noncomputable def StableData.sigma (S : StableData H L) : MulAut ↥L := conjAut S.hN

theorem StableData.sigma_sq (S : StableData H L) : S.sigma * S.sigma = 1 := by
  have hs2 : orderOf (sbar x H.hxY) = 2 := orderOf_sbar H.hx2 H.hxY
  have hsq : sbar x H.hxY * sbar x H.hxY = 1 := by
    have := pow_orderOf_eq_one (sbar x H.hxY)
    rwa [hs2, pow_two] at this
  refine MulEquiv.ext fun l => Subtype.ext ?_
  show sbar x H.hxY * (sbar x H.hxY * (l : barQ ↥(centralizer ({w} : Set G))) *
      (sbar x H.hxY)⁻¹) * (sbar x H.hxY)⁻¹ = l
  calc sbar x H.hxY * (sbar x H.hxY * (l : barQ ↥(centralizer ({w} : Set G))) *
        (sbar x H.hxY)⁻¹) * (sbar x H.hxY)⁻¹
      = (sbar x H.hxY * sbar x H.hxY) * (l : barQ ↥(centralizer ({w} : Set G))) *
        (sbar x H.hxY * sbar x H.hxY)⁻¹ := by group
    _ = l := by rw [hsq]; group

theorem StableData.sigma_ne_one (S : StableData H L) : S.sigma ≠ 1 := by
  intro hσ1
  have hfix : ∀ l ∈ L, sbar x H.hxY * l * (sbar x H.hxY)⁻¹ = l := fun l hl => by
    have := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : barQ ↥(centralizer ({w} : Set G)))) hσ1
    exact this
  have hLC : L ≤ centralizer ({sbar x H.hxY} : Set _) := fun l hl =>
    mem_centralizer_singleton_iff.2 (by
      have := hfix l hl
      calc l * sbar x H.hxY = (sbar x H.hxY * l * (sbar x H.hxY)⁻¹) * sbar x H.hxY := by rw [this]
        _ = sbar x H.hxY * l := by group)
  have hsub : ((bar w Λ).subgroupOf L).IsSubnormal := isSubnormal_inf_subgroupOf H.bar_subnormal hLC
  have hEq : bar w Λ = L :=
    eq_of_perfect_subnormal S.hΛL S.hL.1 H.bar_perfect H.bar_ne_bot hsub
  obtain ⟨φ, hφs, hφo⟩ := H.exists_phi'
  have hwΛ : barMk ↥(centralizer ({w} : Set G)) (wY w) ∈ bar w Λ := hEq ▸ S.hwL
  let a : ↥(bar w Λ) := ⟨barMk ↥(centralizer ({w} : Set G)) (wY w), hwΛ⟩
  have hac : ∀ m : ↥(bar w Λ), a * m = m * a := fun m =>
    Subtype.ext (S.hwc m (hEq ▸ m.2))
  have hφa : φ a ∈ Subgroup.center (kBar Λ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨m, rfl⟩ := hφs g
    rw [← map_mul, ← map_mul, hac m]
  rw [H.hΛcen, Subgroup.mem_bot] at hφa
  have hker : a ∈ φ.ker := hφa
  have h2 : orderOf (⟨a, hker⟩ : ↥φ.ker) = 2 := by
    rw [Subgroup.orderOf_mk]
    show orderOf (⟨barMk ↥(centralizer ({w} : Set G)) (wY w), hwΛ⟩ : ↥(bar w Λ)) = 2
    rw [Subgroup.orderOf_mk]
    exact orderOf_barMk_wY H.hw2
  have hdvd := orderOf_dvd_natCard (⟨a, hker⟩ : ↥φ.ker)
  rw [h2] at hdvd
  exact (Nat.not_even_iff_odd.2 hφo) (even_iff_two_dvd.2 hdvd)

@[expose] def Psub (w : G) (Λ : Subgroup G) (L : Subgroup (barQ ↥(centralizer ({w} : Set G)))) :
    Subgroup ↥L := (bar w Λ).subgroupOf L

theorem StableData.P_perfect (S : StableData H L) : ⁅Psub w Λ L, Psub w Λ L⁆ = Psub w Λ L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_commutator, Psub, Subgroup.map_subgroupOf_eq_of_le S.hΛL, H.bar_perfect]

theorem StableData.P_fixed (S : StableData H L) : ∀ l ∈ Psub w Λ L, S.sigma l = l := by
  intro l hl
  exact Subtype.ext (H.bar_fixed _ (Subgroup.mem_subgroupOf.1 hl))

theorem StableData.exists_phiP (S : StableData H L) :
    ∃ φ : ↥(Psub w Λ L) →* kBar Λ, Function.Surjective φ := by
  obtain ⟨φ, hφs, -⟩ := H.exists_phi'
  exact ⟨φ.comp (Subgroup.subgroupOfEquivOfLe S.hΛL).toMonoidHom,
    hφs.comp (Subgroup.subgroupOfEquivOfLe S.hΛL).surjective⟩

theorem StableData.card_dvd_L (S : StableData H L) : Nat.card (kBar Λ) ∣ Nat.card ↥L := by
  obtain ⟨φ, hφ⟩ := S.exists_phiP
  exact card_dvd_of_section φ hφ

theorem StableData.sixty_le_card_P (S : StableData H L) : 60 ≤ Nat.card ↥(Psub w Λ L) := by
  obtain ⟨φ, hφ⟩ := S.exists_phiP
  have hdvd : Nat.card (kBar Λ) ∣ Nat.card ↥(Psub w Λ L) :=
    Subgroup.card_dvd_of_surjective (f := φ) hφ
  exact (sixty_le_card_of_hasL2Model_odd H.hΛU).trans (Nat.le_of_dvd Nat.card_pos hdvd)

theorem StableData.false_of_sz8
    (S : StableData H L) (h : Shape2Sz8 ↥L) : False := by
  obtain ⟨-, hc2, hSz⟩ := h
  have hcard : Nat.card ↥L = 58240 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L), hc2,
      card_of_lieModel_twistedB2 hSz, ordSuzuki_eight]
  have h3 := (three_dvd_card_of_hasL2Model_odd H.hΛU).trans (hcard ▸ S.card_dvd_L)
  revert h3
  norm_num

omit [Finite G] in
theorem cmap_centralizer_eq {x w e : G} (hex : e * x * e⁻¹ = w) :
    Stage1.Thm3.Sec4.cmap e⁻¹ (centralizer ({w} : Set G)) = centralizer ({x} : Set G) := by
  ext g
  rw [Stage1.Thm3.Sec4.mem_cmap, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    inv_inv, ← hex]
  constructor
  · intro h
    have h1 : e * (g * x) * e⁻¹ = e * (x * g) * e⁻¹ := by
      calc e * (g * x) * e⁻¹ = (e * g * e⁻¹) * (e * x * e⁻¹) := by group
        _ = (e * x * e⁻¹) * (e * g * e⁻¹) := h
        _ = e * (x * g) * e⁻¹ := by group
    have := mul_left_cancel (mul_right_cancel h1)
    exact this
  · intro h
    calc e * g * e⁻¹ * (e * x * e⁻¹) = e * (g * x) * e⁻¹ := by group
      _ = e * (x * g) * e⁻¹ := by rw [h]
      _ = e * x * e⁻¹ * (e * g * e⁻¹) := by group

theorem StableData.false_of_2M12
    (S : StableData H L) (hsh : Shape2M12 ↥L) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t₁ : ↥L := ⟨barMk ↥(centralizer ({w} : Set G)) (wY w), S.hwL⟩
  have ht₁2 : orderOf t₁ = 2 := by rw [Subgroup.orderOf_mk]; exact orderOf_barMk_wY H.hw2
  have ht₁c : t₁ ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (S.hwc g g.2).symm
  have hP2 : 2 < Nat.card ↥(Psub w Λ L) := by have := S.sixty_le_card_P; omega
  obtain ⟨l, hl⟩ := PumpElim.exists_twisted_commutator_central hsh S.sigma S.sigma_sq
    S.sigma_ne_one S.P_perfect hP2 S.P_fixed ht₁2 ht₁c
  have hlt : (l : barQ ↥(centralizer ({w} : Set G))) *
      (sbar x H.hxY * (l : barQ ↥(centralizer ({w} : Set G))) * (sbar x H.hxY)⁻¹)⁻¹ =
        barMk ↥(centralizer ({w} : Set G)) (wY w) := congrArg Subtype.val hl
  obtain ⟨g₀, hg₀⟩ := barMk_surjective (Y := ↥(centralizer ({w} : Set G)))
    (l : barQ ↥(centralizer ({w} : Set G)))
  have hab : barMk ↥(centralizer ({w} : Set G)) (g₀ * (⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G))) * g₀⁻¹) =
      barMk ↥(centralizer ({w} : Set G)) (wY w * ⟨x, H.hxY⟩) := by
    rw [map_mul, map_mul, map_inv, hg₀, map_mul]
    show (l : barQ ↥(centralizer ({w} : Set G))) * sbar x H.hxY * (l : barQ ↥(centralizer ({w} : Set G)))⁻¹ = _
    calc (l : barQ ↥(centralizer ({w} : Set G))) * sbar x H.hxY * (l : barQ ↥(centralizer ({w} : Set G)))⁻¹
        = ((l : barQ ↥(centralizer ({w} : Set G))) *
            (sbar x H.hxY * (l : barQ ↥(centralizer ({w} : Set G))) * (sbar x H.hxY)⁻¹)⁻¹) *
            sbar x H.hxY := by group
      _ = barMk ↥(centralizer ({w} : Set G)) (wY w) * sbar x H.hxY := by rw [hlt]
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [H.hx2, sq] at this
  have hA2 : orderOf ((g₀ : G) * x * (g₀ : G)⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj (g₀ : G)) x
    simpa [MulAut.conj_apply, H.hx2] using this
  have hwx1 : w * x ≠ 1 := by
    intro h
    apply H.hwx
    have h1 : w = x⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hxx
  have hB2 : orderOf (w * x) = 2 :=
    Thm1.orderOf_mul_eq_two_of_commute H.hw2 H.hx2 H.hxw.symm hwx1
  have hAM : (g₀ : G) * x * (g₀ : G)⁻¹ ∈ centralizer ({w} : Set G) :=
    (g₀ * (⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G))) * g₀⁻¹).2
  have hBM : w * x ∈ centralizer ({w} : Set G) :=
    (wY w * (⟨x, H.hxY⟩ : ↥(centralizer ({w} : Set G)))).2
  have hmod : ((g₀ : G) * x * (g₀ : G)⁻¹)⁻¹ * (w * x) ∈ pPrimeCoreOf 2 (centralizer ({w} : Set G)) := by
    refine Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hAM) hBM, ?_⟩
    have h1 := QuotientGroup.eq.1 hab
    exact h1
  obtain ⟨o, ho, hoA⟩ := PumpLift.exists_conj_of_involutions_mod_odd
    (M := centralizer ({w} : Set G)) hAM hBM hA2 hB2 hmod
  have hcx : (o * (g₀ : G)) * x * (o * (g₀ : G))⁻¹ = w * x := by
    calc (o * (g₀ : G)) * x * (o * (g₀ : G))⁻¹ = o * ((g₀ : G) * x * (g₀ : G)⁻¹) * o⁻¹ := by group
      _ = w * x := hoA
  have hex : (p⁻¹ * (o * (g₀ : G))) * x * (p⁻¹ * (o * (g₀ : G)))⁻¹ = w := by
    calc (p⁻¹ * (o * (g₀ : G))) * x * (p⁻¹ * (o * (g₀ : G)))⁻¹
        = p⁻¹ * ((o * (g₀ : G)) * x * (o * (g₀ : G))⁻¹) * p := by group
      _ = p⁻¹ * (w * x) * p := by rw [hcx]
      _ = p⁻¹ * (x * w) * p := by rw [← H.hxw]
      _ = p⁻¹ * (p * w * p⁻¹) * p := by rw [H.hp]
      _ = w := by group
  obtain ⟨L', hL'c, hbar⟩ := exists_lift_component S.hL
  have hK' : IsPCompIn 2 (centralizer ({x} : Set G))
      (Stage1.Thm3.Sec4.cmap (p⁻¹ * (o * (g₀ : G)))⁻¹ L') := by
    have := Stage1.Thm3.Sec4.isPCompIn_cmap hL'c (p⁻¹ * (o * (g₀ : G)))⁻¹
    rwa [cmap_centralizer_eq hex] at this
  have hKeq := H.huniq _ hK'
  have hcenK := H.hKcen
  subst hKeq
  obtain ⟨e1⟩ := kBar_equiv_bar hL'c
  let e2 : kBar (Stage1.Thm3.Sec4.cmap (p⁻¹ * (o * (g₀ : G)))⁻¹ L') ≃* kBar L' :=
    (QuotientGroup.congr _ _ ((MulAut.conj (p⁻¹ * (o * (g₀ : G)))⁻¹).subgroupMap L')
      (pPrimeCore_map_iso 2 _)).symm
  let e3 : kBar (Stage1.Thm3.Sec4.cmap (p⁻¹ * (o * (g₀ : G)))⁻¹ L') ≃* ↥L :=
    e2.trans (e1.trans (MulEquiv.subgroupCongr hbar))
  have h1 : (Subgroup.center (kBar (Stage1.Thm3.Sec4.cmap (p⁻¹ * (o * (g₀ : G)))⁻¹ L'))).map
      e3.toMonoidHom = Subgroup.center ↥L := Subgroup.map_center_eq e3
  rw [hcenK, Subgroup.map_bot] at h1
  exact S.center_ne_bot h1.symm

theorem PumpHyp.stable_false
    (hGKF : GenericKnownFacts) (hF : E2ComponentFacts) (H : PumpHyp x w z b p K Λ) (hG : C3Hyp G)
    {L : Subgroup (barQ ↥(centralizer ({w} : Set G)))} (S : StableData H L) : False := by
  rcases Bk.B810.shape_of_center_ne_bot hGKF hF (gen4_barQ hG.gen4 w)
      (hG.lt2o.2 w H.hw2 L S.hL) S.center_ne_bot with h | h
  · exact S.false_of_2M12 h
  · exact S.false_of_sz8 h

theorem PumpHyp.false
    (hGKF : GenericKnownFacts) (hF : E2ComponentFacts) (hC2 : C2Facts) (H : PumpHyp x w z b p K Λ)
    (hG : C3Hyp G) : False := by
  have hxY := H.hxY
  have hzY : z ∈ centralizer ({w} : Set G) := H.hΛY H.hzΛ
  have hbY : b ∈ centralizer ({w} : Set G) := mem_centralizer_singleton_iff.2 H.hbw
  have hcenY : Subgroup.center (kBar (Λ.subgroupOf (centralizer ({w} : Set G)))) = ⊥ := by
    obtain ⟨e⟩ := hat_equiv_subgroupOf H.hΛY
    have h1 : (Subgroup.center (kBar Λ)).map e.toMonoidHom =
        Subgroup.center (kBar (Λ.subgroupOf (centralizer ({w} : Set G)))) := Subgroup.map_center_eq e
    rw [H.hΛcen, Subgroup.map_bot] at h1
    exact h1.symm
  have hwc : ∀ y : ↥(centralizer ({w} : Set G)), wY w * y = y * wY w := fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2).symm
  obtain ⟨L, hL, hcases⟩ := pump_dichotomy (Y := ↥(centralizer ({w} : Set G)))
    (s := (⟨x, hxY⟩ : ↥(centralizer ({w} : Set G)))) (w := wY w)
    (z := (⟨z, hzY⟩ : ↥(centralizer ({w} : Set G)))) (b := (⟨b, hbY⟩ : ↥(centralizer ({w} : Set G))))
    H.hsO hwc H.hΛC H.hΛ2 hcenY (Subgroup.mem_subgroupOf.2 H.hzΛ)
    (orderOf_mk_centralizer hzY H.hz2) (Subtype.ext H.hb)
  rcases hcases with ⟨hst, hΛL, hwL, hwc'⟩ | ⟨hne, hAB, hΛΔ⟩
  · exact H.stable_false hGKF hF hG ⟨hL, hst, hΛL, hwL, hwc'⟩
  · exact H.diag_false hF hC2 hG hL hne hAB hΛΔ

end Stable

end CFSG.GH74.GLS.C3.Layer1.Thm1P31c
