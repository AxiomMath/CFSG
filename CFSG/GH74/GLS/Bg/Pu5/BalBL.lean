module

public import CFSG.GH74.GLS.Bg.Pu5.BalBBasic
public import CFSG.GH74.GLS.Bg.Pu5.BalBDiag
public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
public import CFSG.GH74.GLS.Bg.Pu5.BalStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Bg.Iii2 CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.PumpRigid
  CFSG.GH74.GLS.C3.Layer1.PumpCalc
open scoped commutatorElement

theorem comm_of_unique_involution {H : Type*} [Group H] {A : Subgroup H}
    (hu : ∀ u v : ↥A, orderOf u = 2 → orderOf v = 2 → u = v) {y : H} (hy : y ∈ A)
    (hy2 : orderOf y = 2) : ∀ x ∈ A, x * y = y * x := by
  intro x hx
  have hc : orderOf ((⟨x, hx⟩ : ↥A) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥A)⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj (⟨x, hx⟩ : ↥A)).toMonoidHom
      (MulAut.conj (⟨x, hx⟩ : ↥A)).injective (⟨y, hy⟩ : ↥A)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rw [this, Subgroup.orderOf_mk, hy2]
  have h2 := hu _ ⟨y, hy⟩ hc (by rw [Subgroup.orderOf_mk]; exact hy2)
  have h3 : x * y * x⁻¹ = y := congrArg Subtype.val h2
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [h3]

theorem diag_centralizes {H : Type} [Group H] [Finite H] {s : H} {A : Subgroup H}
    (hAB : ⁅A, conjSub s⁻¹ A⁆ = ⊥)
    (hu : ∀ u v : ↥A, orderOf u = 2 → orderOf v = 2 → u = v)
    (hcen : Nat.card (center ↥A) = 2)
    {P : Subgroup H} (hperf : ⁅P, P⁆ = P)
    (hP1 : ∀ u v : H, u ∈ P → v ∈ P → orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (hPD : P ≤ (swapDiag hAB).range) {y : H} (hy : y ∈ P) (hy2 : orderOf y = 2) :
    ∀ x ∈ A, x * y = y * x := by
  obtain ⟨l, hl⟩ := hPD hy
  have hk : ∀ z : ↥A, swapDiag hAB z = 1 → z * z = 1 := by
    intro z hz
    have hzc : z ∈ center ↥A := ker_swapDiag_le_center hAB hz
    have : (⟨z, hzc⟩ : ↥(center ↥A)) ^ Nat.card (center ↥A) = 1 := pow_card_eq_one'
    rw [hcen, pow_two] at this
    exact congrArg Subtype.val this
  have hl2 : orderOf l = 2 :=
    orderOf_eq_two_of_diag (swapDiag hAB) hu hk hperf hP1 (fun p hp => hPD hp) (l := l)
      (by rw [hl]; exact hy) (by rw [hl]; exact hy2)
  intro x hx
  have hlA : (l : H) ∈ A := l.2
  have hl2' : orderOf (l : H) = 2 := by rw [Subgroup.orderOf_coe]; exact hl2
  have hxl : x * (l : H) = (l : H) * x := comm_of_unique_involution hu hlA hl2' x hx
  have hxl' : x * (s⁻¹ * (l : H) * s) = (s⁻¹ * (l : H) * s) * x :=
    commute_of_commutator_conj_eq_bot hAB hx (conj_mem_conjSub l.2)
  rw [← hl, swapDiag_apply]
  calc x * ((l : H) * (s⁻¹ * (l : H) * s)) = (x * (l : H)) * (s⁻¹ * (l : H) * s) := by group
    _ = (l : H) * (x * (s⁻¹ * (l : H) * s)) := by rw [hxl]; group
    _ = (l : H) * ((s⁻¹ * (l : H) * s) * x) := by rw [hxl']
    _ = ((l : H) * (s⁻¹ * (l : H) * s)) * x := by group


theorem bar_comm_of_cases {H : Type} [Group H] [Finite H] {s : H} (hss : s * s = 1)
    {Rb Lc : Subgroup H} (hRb : CFSG.IsComponent Rb) (hLc : CFSG.IsComponent Lc)
    (hu : ∀ u v : ↥Rb, orderOf u = 2 → orderOf v = 2 → u = v)
    (hcen : Nat.card (center ↥Rb) = 2)
    {P : Subgroup H} (hperf : ⁅P, P⁆ = P)
    (hP1 : ∀ u v : H, u ∈ P → v ∈ P → orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (hcases : (conjSub s⁻¹ Lc = Lc ∧ P ≤ Lc) ∨
      (conjSub s⁻¹ Lc ≠ Lc ∧ ∃ hAB : ⁅Lc, conjSub s⁻¹ Lc⁆ = ⊥, P ≤ (swapDiag hAB).range))
    {y : H} (hy : y ∈ P) (hy2 : orderOf y = 2) : ∀ x ∈ Rb, x * y = y * x := by
  intro x hx
  rcases hcases with ⟨-, hPL⟩ | ⟨hne, hAB, hPD⟩
  · have hyL : y ∈ Lc := hPL hy
    rcases CFSG.LocalCores.distinct_components_commute hRb hLc with hRL | hcomm
    · subst hRL
      exact comm_of_unique_involution hu hyL hy2 x hx
    · have := Subgroup.commutator_mem_commutator hx hyL
      rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
  · have hss' : s⁻¹ * s⁻¹ = 1 := by
      rw [← mul_inv_rev, hss, inv_one]
    have hLc' : CFSG.IsComponent (conjSub s⁻¹ Lc) := isComponent_conjSub hLc _
    have hconj2 : conjSub s⁻¹ (conjSub s⁻¹ Lc) = Lc := by
      rw [← conjSub_mul, hss']
      ext z
      simp [conjSub, Subgroup.mem_map]
    rcases CFSG.LocalCores.distinct_components_commute hRb hLc with hRL | hc1
    · subst hRL
      exact diag_centralizes hAB hu hcen hperf hP1 hPD hy hy2 x hx
    · rcases CFSG.LocalCores.distinct_components_commute hRb hLc' with hRL' | hc2
      ·
        have hAB' : ⁅conjSub s⁻¹ Lc, conjSub s⁻¹ (conjSub s⁻¹ Lc)⁆ = ⊥ := by
          rw [hconj2, Subgroup.commutator_comm]
          exact hAB
        have hrange := range_swapDiag_conj hss hAB hAB'
        rw [hRL'] at hu hcen hx
        refine diag_centralizes (A := conjSub s⁻¹ Lc) hAB' hu hcen hperf hP1 ?_ hy hy2 x hx
        rw [hrange]
        exact hPD
      · obtain ⟨l, hl⟩ := hPD hy
        have h1 : x * (l : H) = (l : H) * x := by
          have := Subgroup.commutator_mem_commutator hx l.2
          rw [hc1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this
        have h2 : x * (s⁻¹ * (l : H) * s) = (s⁻¹ * (l : H) * s) * x := by
          have := Subgroup.commutator_mem_commutator hx (conj_mem_conjSub (t := s) l.2)
          rw [hc2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
          exact this
        rw [← hl, swapDiag_apply]
        calc x * ((l : H) * (s⁻¹ * (l : H) * s)) = (x * (l : H)) * (s⁻¹ * (l : H) * s) := by group
          _ = (l : H) * (x * (s⁻¹ * (l : H) * s)) := by rw [h1]; group
          _ = (l : H) * ((s⁻¹ * (l : H) * s) * x) := by rw [h2]
          _ = ((l : H) * (s⁻¹ * (l : H) * s)) * x := by group


section BarSec

variable {G : Type} [Group G] [Finite G]

theorem mem_cSec_of_bar_comm {b y : G} {R : Subgroup G}
    (hR : IsPCompIn 2 (centralizer ({b} : Set G)) R)
    (hyL : y ∈ pLayerOf 2 (centralizer ({b} : Set G))) (hyb : y ∈ centralizer ({b} : Set G))
    (hcomm : ∀ x ∈ bar b R, x * TwoThin.barMk ↥(centralizer ({b} : Set G)) ⟨y, hyb⟩ =
      TwoThin.barMk ↥(centralizer ({b} : Set G)) ⟨y, hyb⟩ * x) : y ∈ cSec R := by
  have hyN : y ∈ normalizer (R : Set G) := pLayerOf_le_normalizer hR hyL
  refine ⟨hyN, TwoThin.mem_normalizer_pPrimeCoreOf hyN, fun k hk => ?_⟩
  have hkb : k ∈ centralizer ({b} : Set G) := hR.1 hk
  have hcR : ⁅k, y⁆ ∈ R := by
    have e : ⁅k, y⁆ = k * (y * k⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact R.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hyN k⁻¹).mp (R.inv_mem hk))
  have hcb : ⁅k, y⁆ ∈ centralizer ({b} : Set G) :=
    mul_mem (mul_mem (mul_mem hkb hyb) (inv_mem hkb)) (inv_mem hyb)
  refine TwoThin.mem_pPrimeCoreOf_of_barMk_eq_one hR.1 (subnormal_of_isPCompIn hR) hcR hcb ?_
  have hx : TwoThin.barMk ↥(centralizer ({b} : Set G)) ⟨k, hkb⟩ ∈ bar b R :=
    ⟨⟨k, hkb⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  have h := hcomm _ hx
  have h2 : (⟨⁅k, y⁆, hcb⟩ : ↥(centralizer ({b} : Set G))) = ⁅(⟨k, hkb⟩ : ↥(centralizer ({b} : Set G))), ⟨y, hyb⟩⁆ :=
    Subtype.ext rfl
  rw [h2, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 h

theorem bar_unique_involution (h44 : II4_44) (hG : IsKProperSimple G) {b : G} {R : Subgroup G}
    (hR : IsRigidRankOneComp b R) :
    (∀ u v : ↥(bar b R), orderOf u = 2 → orderOf v = 2 → u = v) ∧
      Nat.card (center ↥(bar b R)) = 2 := by
  have hQ := h44 G hG b (rr_ord hR) R (rr_pcomp hR) hR.2
  obtain ⟨e1⟩ := TwoThin.hat_equiv_subgroupOf (rr_pcomp hR).1
  obtain ⟨e2⟩ := TwoThin.hat_equiv_map (subnormal_of_isPCompIn (rr_pcomp hR))
  let e := e1.trans e2
  refine ⟨fun u v hu hv => ?_, ?_⟩
  · have h1 : orderOf (e.symm u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu
    have h2 : orderOf (e.symm v) = 2 := by rw [MulEquiv.orderOf_eq]; exact hv
    exact e.symm.injective (IVK.Lifted.unique_involution_of_sl2or2a7 hQ h1 h2)
  · have hc : Nat.card (center ↥(bar b R)) = Nat.card (center (↥R ⧸ pPrimeCore 2 ↥R)) := by
      have h1 := Subgroup.map_center_eq e
      have h2 := Subgroup.card_map_of_injective (f := e.toMonoidHom) (K := center (↥R ⧸ pPrimeCore 2 ↥R))
        e.injective
      rw [← h1]
      exact h2
    rw [hc]
    exact hQ.2

theorem pRank_range_eq_of_odd_ker {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (g : A →* B) (hodd : Odd (Nat.card g.ker)) : pRank 2 ↥g.range = pRank 2 A :=
  (pRank_eq_of_mulEquiv' (QuotientGroup.quotientKerEquivRange g)).symm.trans
    (CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two g.ker
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)))

theorem bl_of (h44 : II4_44) : BLS := by
  intro G _ _ hG a b ha _ hab Λ hΛ hrk y hyΛ hy2 R hR
  have hba : a ∈ centralizer ({b} : Set G) := TwoThin.mem_centralizer_symm hab
  set Y : Subgroup G := centralizer ({b} : Set G) with hY
  have hyb : y ∈ Y := (Subgroup.mem_inf.mp (hΛ.1 hyΛ)).2
  have hyL : y ∈ pLayerOf 2 Y := le_pLayerOf_of_isPCompIn_inf ha hba hΛ hyΛ
  have hRc : IsPCompIn 2 Y R := rr_pcomp hR
  refine mem_cSec_of_bar_comm hRc hyL hyb ?_
  have hso : orderOf (⟨a, hba⟩ : ↥Y) = 2 := TwoThin.orderOf_mk_centralizer hba ha
  have hs2 : orderOf (TwoThin.barMk ↥Y ⟨a, hba⟩) = 2 := TwoThin.orderOf_barMk hso
  have hss : TwoThin.barMk ↥Y ⟨a, hba⟩ * TwoThin.barMk ↥Y ⟨a, hba⟩ = 1 := by
    have := pow_orderOf_eq_one (TwoThin.barMk ↥Y ⟨a, hba⟩)
    rwa [hs2, pow_two] at this
  have hΛC := TwoThin.le_centralizer_mk (TwoThin.isPCompIn_two_iff.mp hΛ).1 hba
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hΛ hba
  obtain ⟨-, -, Lc, hLc, hcases, -⟩ := TwoThin.pumpupY_structure hso hΛC hΛ2
  have hRb : CFSG.IsComponent (bar b R) := isComponent_bar hRc
  obtain ⟨hu, hcen⟩ := bar_unique_involution h44 hG hR
  have hperf : ⁅bar b Λ, bar b Λ⁆ = bar b Λ := by
    have h1 : ⁅Λ.subgroupOf Y, Λ.subgroupOf Y⁆ = Λ.subgroupOf Y :=
      TwoThin.commutator_self_of_isTwoComponent hΛC hΛ2
    show ⁅(Λ.subgroupOf Y).map (TwoThin.barMk ↥Y), (Λ.subgroupOf Y).map (TwoThin.barMk ↥Y)⁆ =
      (Λ.subgroupOf Y).map (TwoThin.barMk ↥Y)
    rw [← Subgroup.map_commutator, h1]
  have hrank : pRank 2 ↥(bar b Λ) = 1 := by
    let f₀ : ↥(Λ.subgroupOf Y) →* TwoThin.barQ ↥Y :=
      (TwoThin.barMk ↥Y).comp (Λ.subgroupOf Y).subtype
    have hodd : Odd (Nat.card f₀.ker) :=
      CFSG.ComponentClassification.OddKernel.odd_card_restriction_kernel (TwoThin.barMk ↥Y) TwoThin.odd_card_ker_barMk
        (Λ.subgroupOf Y)
    have hrange : f₀.range = bar b Λ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, pRank_range_eq_of_odd_ker f₀ hodd,
      pRank_eq_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe (hΛ.1.trans inf_le_right))]
    exact hrk
  have hP1 : ∀ u v : TwoThin.barQ ↥Y, u ∈ bar b Λ → v ∈ bar b Λ → orderOf u = 2 →
      orderOf v = 2 → u * v = v * u → u = v :=
    fun u v hu hv hu2 hv2 huv => eq_of_pRank_one hrank hu hv hu2 hv2 huv
  have hyP : TwoThin.barMk ↥Y ⟨y, hyb⟩ ∈ bar b Λ :=
    ⟨⟨y, hyb⟩, Subgroup.mem_subgroupOf.mpr hyΛ, rfl⟩
  have hy2' : orderOf (TwoThin.barMk ↥Y ⟨y, hyb⟩) = 2 :=
    TwoThin.orderOf_barMk (TwoThin.orderOf_mk_centralizer hyb hy2)
  exact fun x hx => bar_comm_of_cases hss hRb hLc hu hcen hperf hP1 hcases hyP hy2' x hx

end BarSec

end CFSG.GH74.GLS.Bg.Pu5
