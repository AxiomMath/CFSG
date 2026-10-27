module

public import CFSG.Quasithin.H13.L32NLem14330e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14330d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open Ctx
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem conj_V1_le_F4 : CFSG.conjugate (fsuV1 T V) g ≤ V₂ :=
  (conjugate_mono C.plane.2 g).trans (conjugate_eq_self (g_mem_normalizer C.plane C.gP)).le

theorem eq_one_of_rho_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) (h1 : D.ρ ⟨x, hxN⟩ = 1) : x = 1 := by
  have hxH : x ∈ l32nH T V := L14332.conj_zU_le_F4 h12813 C.setting C.gP C.gN hx.1
  have hmod : ∀ {Y : Subgroup G}, x ∈ Y →
      x ∈ Y ⊓ centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) := fun hY =>
    ⟨hY, hxH, L14332.normalizer_le_normalizer_centerOf _ hxN,
      (L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).mp h1⟩

  obtain ⟨-, -, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := h6
  have hx1 := hmod hx.1
  rw [e1, e2, e3, e4, e5] at hx1
  have hle1 : centerOf (i128 T L V (fsuV1 T V)) ⊔ CFSG.conjugate (fsuV1 T V) g ≤
      centerOf (fsuU T V) ⊔ V₂ :=
    sup_le_sup (by rw [C.zI]; exact inf_le_left) C.conj_V1_le_F4

  obtain ⟨T', V₂', k, hs', hmem', hkP, hkN, hkz, hkl⟩ := C.exists_second_zU_F4 h1222
  obtain ⟨-, f2, -, -, -, h6'⟩ := h12810 G T' L V 3 (fsuV1 T V) V₂' hs' k⁻¹ hkP hkN
  obtain ⟨f1, f2', f3, f4, f5, -⟩ := h6'
  have hx2 := hmod (hkl ▸ hx.2 : x ∈ CFSG.conjugate (centerOf (fsuU T V)) k⁻¹)
  rw [f1, f2', f3, f4, f5] at hx2
  have hle2 : centerOf (i128 T' L V (fsuV1 T V)) ⊔ CFSG.conjugate (fsuV1 T V) k⁻¹ ≤
      centerOf (fsuU T V) ⊔ V₂' := by
    refine sup_le_sup (by rw [← f2]; exact inf_le_left) fun y hy => ?_
    rw [conjugate_inv_mem_iff] at hy
    rcases C.S.eq_of_mem_V1_F4 C.z_mem C.z_ne hy with h | h
    · rw [show y = k * (k⁻¹ * y * k) * k⁻¹ by group, h, mul_one, mul_inv_cancel]
      exact one_mem _
    · rw [show y = k * (k⁻¹ * y * k) * k⁻¹ by group, h, hkz]
      exact (hmem' _).mpr (Or.inr (Or.inr (Or.inl rfl)))

  have hxU : x ∈ fsuU T V := sup_le inf_le_left (C.plane.1.1.trans V_le_U) (hle1 hx1)
  have hπ : D.π x = 0 := by
    rcases C.pi_sup_V2_F4 D (hle1 hx1) with h | h
    · exact h
    · rcases C.pi_sup_V2'_F4 D hmem' (hle2 hx2) with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') (C.pi_a_ne_pi_zb_F4 D h1222 h12213)
  have hxZ := (L128A.HatU.π_eq_zero_iff D hxU).mp hπ
  have hmem : x ∈ centerOf (fsuU T V) ⊓ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := ⟨⟨hxZ, hx.1⟩, hx.2⟩
  rw [C.zU_inf_eq_bot_F4 h14325 h1222] at hmem
  exact (Subgroup.mem_bot).mp hmem

theorem rho_eq_of_ne_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hx1 : x ≠ 1) :
    ∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨x, hxN⟩ ≠ 1 ∧ ∀ v,
      D.ρ ⟨x, hxN⟩ v = v + (D.B v (D.π (g⁻¹ * z * g)) • D.π (z * b) +
        D.B v (D.π (z * b)) • D.π (g⁻¹ * z * g)) := by
  obtain ⟨hxN, ε, hε⟩ := C.rho_eq_F4 D h1222 h12213 h12810 h12813 hx
  have hne : D.ρ ⟨x, hxN⟩ ≠ 1 := fun h1 =>
    hx1 (C.eq_one_of_rho_F4 D h14325 h1222 h12213 h12810 h12813 hx hxN h1)
  refine ⟨hxN, hne, fun v => ?_⟩
  have hε1 : ε = 1 := by
    have hcases : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    rcases hcases ε with h0 | h0
    · exact absurd (LinearEquiv.ext fun w => by rw [hε, h0, zero_smul, add_zero]; rfl) hne
    · exact h0
  rw [hε, hε1, one_smul]

theorem rho_fix_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12810 : Lemma12_8_10_F4)
    (h12813 : Lemma12_8_13_F4) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    D.ρ ⟨x, hxN⟩ (D.π (g⁻¹ * z * g)) = D.π (g⁻¹ * z * g) ∧
      D.ρ ⟨x, hxN⟩ (D.π (z * b)) = D.π (z * b) := by
  obtain ⟨hxN', ε, hε⟩ := C.rho_eq_F4 D h1222 h12213 h12810 h12813 hx
  have hab := C.B_ab_F4 D
  have hba : D.B (D.π (z * b)) (D.π (g⁻¹ * z * g)) = 0 := by
    rw [L128A.HatU.B_symm D]
    exact hab
  constructor
  · rw [hε]
    simp only [L128A.HatU.B_isAlt D, hab, zero_smul, add_zero, smul_zero]
  · rw [hε]
    simp only [L128A.HatU.B_isAlt D, hba, zero_smul, add_zero, smul_zero]

theorem comm_eq_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l)
    (hx1 : x ≠ 1) (hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G)) (w : D.V) :
    (∃ v, D.ρ ⟨x, hxN⟩ v = v + w) ↔
      w ∈ Submodule.span (ZMod 2) {D.π (g⁻¹ * z * g), D.π (z * b)} := by
  obtain ⟨hxN', -, hρ⟩ := C.rho_eq_of_ne_F4 D h14325 h1222 h12213 h12810 h12813 hx hx1
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨v, hv⟩
    rw [hρ] at hv
    have := add_left_cancel hv
    exact ⟨D.B v (D.π (z * b)), D.B v (D.π (g⁻¹ * z * g)), by rw [← this, add_comm]⟩
  · rintro ⟨c, d, rfl⟩
    obtain ⟨ua, ub, hα₁, hβ₁, hα₂, hβ₂⟩ := C.exists_dual_ab_F4 D h1222 h12213
    refine ⟨d • ua + c • ub, ?_⟩
    rw [hρ]
    congr 1
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hα₁,
      hβ₁, hα₂, hβ₂, mul_one, mul_zero, add_zero, zero_add]
    rw [add_comm]

theorem card_zI_le_F4 (h14325 : Lemma14325One_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4)
    (h12810 : Lemma12_8_10_F4) (h12813 : Lemma12_8_13_F4) :
    Nat.card ↥(centerOf (i128 T L V (fsuV1 T V))) ≤ 2 := by
  obtain ⟨D⟩ := C.setting.exists_hatModelU_F4 h1222 h12213
  have hcard : Nat.card ↥(CFSG.conjugate (centerOf (i128 T L V (fsuV1 T V))) l) =
      Nat.card ↥(centerOf (i128 T L V (fsuV1 T V))) := by
    rw [CFSG.conjugate]
    exact Subgroup.card_map_of_injective (MulAut.conj l⁻¹).injective
  rw [← hcard, C.zIl_eq_F4]
  refine card_le_two_of_eq fun x hx y hy hx1 hy1 => ?_
  obtain ⟨hxN, -, hρx⟩ := C.rho_eq_of_ne_F4 D h14325 h1222 h12213 h12810 h12813 hx hx1
  obtain ⟨hyN, -, hρy⟩ := C.rho_eq_of_ne_F4 D h14325 h1222 h12213 h12810 h12813 hy hy1
  have hxy : x * y⁻¹ ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      CFSG.conjugate (centerOf (fsuU T V)) l := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)
  have hN : x * y⁻¹ ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    (Subgroup.normalizer _).mul_mem hxN ((Subgroup.normalizer _).inv_mem hyN)
  have h1 : D.ρ ⟨x * y⁻¹, hN⟩ = 1 := by
    have e : (⟨x * y⁻¹, hN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨x, hxN⟩ * (⟨y, hyN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G)))⁻¹ := rfl
    rw [e, map_mul, map_inv, mul_inv_eq_one]
    exact LinearEquiv.ext fun v => by rw [hρx, hρy]
  exact mul_inv_eq_one.mp (C.eq_one_of_rho_F4 D h14325 h1222 h12213 h12810 h12813 hxy hN h1)

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
