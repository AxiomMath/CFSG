module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.LeafL77
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf

section Layer

variable {G : Type} [Group G]

theorem comm_mul_left_central {u x y : G} (hux : u * x = x * u) (huy : u * y = y * u) :
    ⁅u * x, y⁆ = ⁅x, y⁆ := by
  have hw : u * (x * y * x⁻¹) = (x * y * x⁻¹) * u := by
    have h1 : u * x⁻¹ = x⁻¹ * u := by
      calc u * x⁻¹ = x⁻¹ * (x * u) * x⁻¹ := by group
        _ = x⁻¹ * (u * x) * x⁻¹ := by rw [hux]
        _ = x⁻¹ * u := by group
    calc u * (x * y * x⁻¹) = (u * x) * y * x⁻¹ := by group
      _ = (x * u) * y * x⁻¹ := by rw [hux]
      _ = x * (u * y) * x⁻¹ := by group
      _ = x * (y * u) * x⁻¹ := by rw [huy]
      _ = x * y * (u * x⁻¹) := by group
      _ = x * y * (x⁻¹ * u) := by rw [h1]
      _ = (x * y * x⁻¹) * u := by group
  simp only [commutatorElement_def]
  calc u * x * y * (u * x)⁻¹ * y⁻¹ = (u * (x * y * x⁻¹) * u⁻¹) * y⁻¹ := by group
    _ = (x * y * x⁻¹) * y⁻¹ := by rw [hw, mul_inv_cancel_right]
    _ = x * y * x⁻¹ * y⁻¹ := rfl

theorem comm_mul_right_central {v x y : G} (hvx : v * x = x * v) (hvy : v * y = y * v) :
    ⁅x, v * y⁆ = ⁅x, y⁆ := by
  have h1 : ⁅v * y, x⁆ = ⁅y, x⁆ := comm_mul_left_central hvy hvx
  rw [← commutatorElement_inv, h1, commutatorElement_inv]

end Layer

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem comm_le_Oz {L : Subgroup G} (hLM : L ≤ zpowers z ⊔ Oz z) : ⁅L, L⁆ ≤ Oz z := by
  have hzC : zpowers z ≤ Cz z := zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hOC : Oz z ≤ Cz z := TwoThin.pPrimeCoreOf_le _
  have hnorm : zpowers z ≤ normalizer (Oz z : Set G) := le_normalizer_Oz hzC
  have hsplit : ∀ a ∈ L, ∃ u ∈ zpowers z, ∃ n ∈ Oz z, a = u * n := fun a ha =>
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_le_normalizer hnorm (hLM ha)
  have hcen : ∀ u ∈ zpowers z, ∀ x ∈ Cz z, u * x = x * u := by
    intro u hu x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 hx
    exact ((show Commute x z from hxz).zpow_right i).eq.symm
  rw [Subgroup.commutator_def]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  obtain ⟨u, hu, n, hn, rfl⟩ := hsplit a ha
  obtain ⟨v, hv, m, hm, rfl⟩ := hsplit b hb
  have hnC : n ∈ Cz z := hOC hn
  have hmC : m ∈ Cz z := hOC hm
  have hvmC : v * m ∈ Cz z := mul_mem (hzC hv) hmC
  rw [comm_mul_left_central (hcen u hu n hnC) (hcen u hu _ hvmC),
    comm_mul_right_central (hcen v hv n hnC).symm.symm (hcen v hv m hmC)]
  have : ⁅n, m⁆ = n * (m * n⁻¹ * m⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem hn (Oz_conj hmC (inv_mem hn))

theorem pLayerOf_Cz_le (hII : II4_4_4_center) (hF : FStar_C) (h : Std4 G z S K₁ K₂)
    (hQ : Qz S z = zpowers z) : pLayerOf 2 (centralizer ({z} : Set G)) ≤ K₁ ⊔ K₂ := by
  have hM := m4_of_std hII h
  refine sSup_le fun L hL => ?_
  by_cases h1 : L = K₁
  · subst h1; exact le_sup_left
  by_cases h2 : L = K₂
  · subst h2; exact le_sup_right
  exfalso
  have hK₁ := h.comp_isPCompIn (Or.inl rfl)
  have hK₂ := h.comp_isPCompIn (Or.inr rfl)
  have hc1 : L ≤ cSec K₁ := le_cSec_of_ne hL hK₁ h1
  have hc2 : L ≤ cSec K₂ := le_cSec_of_ne hL hK₂ h2
  have hLC : L ≤ Cz z := hL.1
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hP1 : pPrimeCoreOf 2 K₁ ≤ Oz z := pPrimeCoreOf_le_Oz hK₁
  have hP2 : pPrimeCoreOf 2 K₂ ≤ Oz z := pPrimeCoreOf_le_Oz hK₂
  have hLM : L ≤ zpowers z ⊔ Oz z := by
    intro c hc
    have hcC : c ∈ Cz z := hLC hc
    have hcomm' : ∀ k' ∈ K₁ ⊔ K₂, ⁅k', c⁆ ∈ Oz z :=
      forall_comm_mem_sup hK₁C hK₂C (fun x hx n hn => Oz_conj hx hn)
        (fun k' hk' => hP1 ((hc1 hc).2.2 k' hk')) (fun k' hk' => hP2 ((hc2 hc).2.2 k' hk'))
    exact hF G z S K₁ K₂ h hQ c hcC hcomm'
  obtain ⟨-, hL2⟩ := TwoThin.isPCompIn_two_iff.1 hL
  have hperf : ⁅L, L⁆ = L := TwoThin.commutator_self_of_isTwoComponent hLC hL2
  have hLO : L ≤ Oz z := hperf ▸ comm_le_Oz hLM
  have hodd : Odd (Nat.card ↥L) :=
    Odd.of_dvd_nat card_Oz_odd (Subgroup.card_dvd_of_le hLO)
  have hsolv : Group.IsSolvable ↥L := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hne : L ≠ ⊥ := TwoThin.ne_bot_of_isTwoComponent hL2
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hne
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
  exact Group.IsPerfect.not_isSolvable ↥L hsolv

omit [Finite G] in
theorem conjugate_inj {K K' : Subgroup G} {g : G} (h : conjugate K g = conjugate K' g) : K = K' := by
  have e : ∀ H : Subgroup G, cmap g (conjugate H g) = H := fun H => cmap_cancel g H
  rw [← e K, ← e K', h]

theorem ig_diag_balance (hII : II4_4_4_center) (h327 : IG_3_27) (h41 : Prop4_1)
    (hF : FStar_C) : IG_diag_balance := by
  intro G _ _ z S K₁ K₂ h q hq hq5 hK₁ hK₂ t₁ ht₁C ht₁o hconj hswap g hg
  obtain ⟨hQ, -, hc⟩ := h41 G z S K₁ K₂ h
  have hM := m4_of_std hII h
  have hint : IsIntrinsic t₁ (conjugate K₁ g) := by
    have := isIntrinsic_cj hg (intrinsic_of_comp hM h (Or.inl rfl))
    rwa [cj_eq_conjugate] at this
  have hz_int := hc t₁ ht₁C hconj hswap g hg
  have hzn : z ∉ normalizer (conjugate K₁ g : Set G) := by
    intro hzn
    have h1 : conjugate (conjugate K₁ g) z = conjugate K₁ g := by
      rw [← cj_eq_conjugate]; exact M.cj_eq_iff_normalizer.2 hzn
    exact h.ne (conjugate_inj (h1.symm.trans hz_int.1))
  have hcomm : Commute t₁ z := Subgroup.mem_centralizer_singleton_iff.1 ht₁C
  obtain ⟨hI, -⟩ := h327 G h.simple t₁ z ht₁o h.orderOf_z hcomm (conjugate K₁ g) hint hzn
  exact (le_pLayerOf_of_isPCompIn_inf ht₁o ht₁C hI).trans (pLayerOf_Cz_le hII hF h hQ)

theorem l77_no_conj_of_closed (hII : II4_4_4_center) (h73 : Lemma7_3) (h327 : IG_3_27)
    (h41 : Prop4_1) (hF : FStar_C) (hB : IVK_3_1b_diag) : L77_no_conj :=
  l77_no_conj hII h73 (ig_diag_balance hII h327 h41 hF) hB

end Main

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Leaf
