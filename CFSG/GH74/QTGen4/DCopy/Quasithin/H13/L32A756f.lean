module

public import CFSG.Quasithin.H13.L32A756f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A756c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A756d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem exists_comm_of_fix_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (h13314 : A6.Stmt13_3_14_F4)
    (h1222 : Stmt12_2_2_F4) {w : G} (hwU : w ∈ conjClosure V (hz T V)) (hθ : C.θG e w ≠ 1)
    {h : G} (hh : h ∈ hz T V) (hfix : g2QAct (ZMod 2) (C.ΦG E h) (C.θG e w) = C.θG e w) :
    ∃ h' ∈ hz T V, h' * w = w * h' ∧ C.ΦG E h' = C.ΦG E h := by
  obtain ⟨z, hz1, hzne⟩ := C.exists_V1_ne
  have hw1 : w⁻¹ * (h * w * h⁻¹) ∈ fsuV1 T V :=
    C.mem_V1_of_θG E hh hwU (by rw [C.θG_conj E hh hwU, hfix])
  have hcomm_of : ∀ {c : G}, c * w * c⁻¹ = w → c * w = w * c := fun {c} hc => by
    calc c * w = (c * w * c⁻¹) * c := by group
      _ = w * c := by rw [hc]
  rcases M755.eq_one_or_eq_of_card_two C.card_V1 hz1 hzne hw1 with e1 | e1
  · refine ⟨h, hh, hcomm_of ?_, rfl⟩
    calc h * w * h⁻¹ = w * (w⁻¹ * (h * w * h⁻¹)) := by group
      _ = w := by rw [e1, mul_one]
  · obtain ⟨q, hq, hqw⟩ : ∃ q ∈ pCoreOf 2 (hz T V), q * w ≠ w * q := by
      by_contra hcon
      push Not at hcon
      exact hθ (C.θG_eq_one_of_comm_F4 E h13322 hMod h13314 h1222 hwU hcon)
    have hqH := pCoreOf_le 2 _ hq
    have hΦq : C.ΦG E q = 1 := by
      rw [C.ΦG_eq E hqH]
      exact (C.Φ_eq_one_iff E ⟨q, hqH⟩).2 hq
    have hq1 : w⁻¹ * (q * w * q⁻¹) ∈ fsuV1 T V := C.mem_V1_of_θG E hqH hwU (by
      rw [C.θG_conj E hqH hwU, hΦq, map_one, MulAut.one_apply])
    rcases M755.eq_one_or_eq_of_card_two C.card_V1 hz1 hzne hq1 with e2 | e2
    · exfalso
      apply hqw
      apply hcomm_of
      calc q * w * q⁻¹ = w * (w⁻¹ * (q * w * q⁻¹)) := by group
        _ = w := by rw [e2, mul_one]
    · have key : h * w * h⁻¹ = q * w * q⁻¹ := by
        calc h * w * h⁻¹ = w * (w⁻¹ * (h * w * h⁻¹)) := by group
          _ = w * (w⁻¹ * (q * w * q⁻¹)) := by rw [e1, e2]
          _ = q * w * q⁻¹ := by group
      refine ⟨q⁻¹ * h, mul_mem (inv_mem hqH) hh, hcomm_of ?_, ?_⟩
      · calc q⁻¹ * h * w * (q⁻¹ * h)⁻¹ = q⁻¹ * (h * w * h⁻¹) * q := by group
          _ = w := by rw [key]; group
      · rw [C.ΦG_mul E (inv_mem hqH) hh, C.ΦG_inv E hqH, hΦq, inv_one, one_mul]

theorem ΦX_norm_of_fix_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (h13314 : A6.Stmt13_3_14_F4)
    (h1222 : Stmt12_2_2_F4) {w : G} (hwU : w ∈ conjClosure V (hz T V)) (hθ : C.θG e w ≠ 1)
    {X : Subgroup G} (hXH : X ≤ hz T V)
    (hN : ∀ h ∈ hz T V, h * w = w * h → ∀ u ∈ X, h * u * h⁻¹ ∈ X) {h : G} (hh : h ∈ hz T V)
    (hfix : g2QAct (ZMod 2) (C.ΦG E h) (C.θG e w) = C.θG e w) {a : ↥(quasithinG2 (ZMod 2))}
    (ha : a ∈ C.ΦX E X) : C.ΦG E h * a * (C.ΦG E h)⁻¹ ∈ C.ΦX E X := by
  obtain ⟨h', hh', hcomm, hΦ⟩ := C.exists_comm_of_fix_F4 E h13322 hMod h13314 h1222 hwU hθ hh hfix
  obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E hXH).1 ha
  rw [C.mem_ΦX E hXH, ← hΦ]
  refine ⟨h' * u * h'⁻¹, hN h' hh' hcomm u hu, ?_⟩
  rw [C.ΦG_mul E (mul_mem hh' (hXH hu)) (inv_mem hh'), C.ΦG_mul E hh' (hXH hu), C.ΦG_inv E hh']

theorem class_p0_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {w : G} (hwU : w ∈ conjClosure V (hz T V))
    (hθ : C.θG e w = M755.ptQ 8) {X : Subgroup G} (hXH : X ≤ hz T V)
    (hXe : IsElemAbelian 2 X) (hX1 : C.ΦX E X ≠ ⊥)
    (hN : ∀ h ∈ hz T V, h * w = w * h → ∀ u ∈ X, h * u * h⁻¹ ∈ X) :
    C.ΦX E X ≤ sSubG ∧ ((∀ l, l ∈ idx (C.ΦX E X) ↔ l ∈ [0, 2, 4, 6]) ∨
      (∀ l, l ∈ idx (C.ΦX E X) ↔ l ∈ [0, 2, 4, 6, 8, 10, 12, 14])) := by
  have h8 : (8 : ℕ) ∈ M755.ptsQ := by decide
  have hθ1 : C.θG e w ≠ 1 := hθ ▸ M755.ptQ_ne_one h8
  obtain ⟨hX2, hXc⟩ := C.ΦX_elem E hXH hXe

  have hnorm : ∀ h ∈ hz T V, g2QAct (ZMod 2) (C.ΦG E h) (M755.ptQ 8) = M755.ptQ 8 →
      ∀ a ∈ C.ΦX E X, C.ΦG E h * a * (C.ΦG E h)⁻¹ ∈ C.ΦX E X := fun h hh hfix a ha =>
    C.ΦX_norm_of_fix_F4 E h13322 hMod h13314 h1222 hwU hθ1 hXH hN hh (by rw [hθ]; exact hfix) ha
  have hnormg : ∀ g : ↥(quasithinG2 (ZMod 2)), (∃ h ∈ hz T V, C.ΦG E h = g) →
      g2QAct (ZMod 2) g (M755.ptQ 8) = M755.ptQ 8 →
      g ∈ Subgroup.normalizer (C.ΦX E X : Set ↥(quasithinG2 (ZMod 2))) := by
    rintro g ⟨h, hh, rfl⟩ hfix
    have hfix' : g2QAct (ZMod 2) (C.ΦG E h⁻¹) (M755.ptQ 8) = M755.ptQ 8 := by
      rw [C.ΦG_inv E hh, map_inv]
      exact M755.inv_fix hfix
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨hnorm h hh hfix a, fun ha => ?_⟩
    have h1 := hnorm h⁻¹ (inv_mem hh) hfix' _ ha
    rw [C.ΦG_inv E hh] at h1
    have e1 : (C.ΦG E h)⁻¹ * (C.ΦG E h * a * (C.ΦG E h)⁻¹) * (C.ΦG E h)⁻¹⁻¹ = a := by group
    rwa [e1] at h1
  have hN0 : sSubG ⊓ g2Derived (ZMod 2) ≤
      Subgroup.normalizer (C.ΦX E X : Set ↥(quasithinG2 (ZMod 2))) := by
    intro g hg
    obtain ⟨k', hk', hke⟩ := C.exists_K_of_derived E hg.2
    exact hnormg g ⟨k', C.le_hz hk', hke⟩ (M755.sSubG_fix hg.1)
  have hN' : ¬ C.ΦX E X ≤ g2Derived (ZMod 2) →
      sSubG ≤ Subgroup.normalizer (C.ΦX E X : Set ↥(quasithinG2 (ZMod 2))) := by
    intro hnd g hg
    obtain ⟨a, ha, haD⟩ := IsConcreteLE.not_le_iff_exists.1 hnd
    obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E hXH).1 ha
    refine hnormg g ?_ (M755.sSubG_fix hg)
    by_cases hgD : g ∈ g2Derived (ZMod 2)
    · obtain ⟨k', hk', hke⟩ := C.exists_K_of_derived E hgD
      exact ⟨k', C.le_hz hk', hke⟩
    · have hga : g * (C.ΦG E u)⁻¹ ∈ g2Derived (ZMod 2) :=
        (Subgroup.mul_mem_iff_of_index_two (M755.index_derived hG)).2
          (iff_of_false hgD fun h' => haD (by simpa using inv_mem h'))
      obtain ⟨k', hk', hke⟩ := C.exists_K_of_derived E hga
      refine ⟨k' * u, mul_mem (C.le_hz hk') (hXH hu), ?_⟩
      rw [C.ΦG_mul E (C.le_hz hk') (hXH hu), hke, inv_mul_cancel_right]
  have hXp : IsPGroup 2 ↥(C.ΦX E X) := fun g =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hX2 g.1 g.2)⟩
  have hXS := M755.le_sSubG_of_norm hG hXp hN0 hN'
  have hN0' : ∀ i ∈ M755.innerS, ∀ x ∈ C.ΦX E X, sEltG i * x * (sEltG i)⁻¹ ∈ C.ΦX E X := by
    intro i hi x hx
    have hi64 := M755.innerS_lt i hi
    have hmem : sEltG i ∈ sSubG ⊓ g2Derived (ZMod 2) :=
      ⟨mem_sSubG.2 ⟨i, hi64, rfl⟩, (hG.inner_iff i hi64).2 hi⟩
    exact (Subgroup.mem_normalizer_iff.mp (hN0 hmem) x).mp hx
  have hNz : ∀ x ∈ C.ΦX E X, M755.z1 * x * M755.z1⁻¹ ∈ C.ΦX E X := by
    intro x hx
    obtain ⟨k', hk', hke⟩ := C.exists_K_of_derived E M755.z1_mem
    exact (Subgroup.mem_normalizer_iff.mp
      (hnormg _ ⟨k', C.le_hz hk', hke⟩ M755.g2QAct_z1) x).mp hx
  exact ⟨hXS, M755.idx_B0_or_A0 hXS hX2 hXc hX1 hN0' hNz⟩

theorem exists_l_of_V_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {v : G} (hv : v ∈ V) (hv1 : v ∉ fsuV1 T V) :
    ∃ l ∈ L, l ∈ hz T V ∧ g2QAct (ZMod 2) (C.ΦG E l) (M755.ptQ 8) = C.θG e v := by
  obtain ⟨l, hlL, hlH, w, hw, hw1, rfl⟩ := C.exists_pt_V_F4 h13322 hMod hV₂ hv hv1
  refine ⟨l, hlL, hlH, ?_⟩
  rw [C.θG_conj E hlH (le_conjClosure V _ (hV₂.2.1 hw)), C.θG_V2_F4 E hMod hVL hV₂ hw hw1]

theorem θ_zα_mem_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) {z : G}
    (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1)
    (hZU : conjSub ((k : G) * g) (fsuV1 T V) ≤ conjClosure V (hz T V)) :
    ∃ v ∈ V, v ∉ fsuV1 T V ∧ C.θG e (((k : G) * g) * z * ((k : G) * g)⁻¹) = C.θG e v := by
  set x := (k : G) * g with hx
  set zα := x * z * x⁻¹ with hzα
  have hθ := C.θ_zα_ne_one E hG N hz1 hzne hZU
  have hzαU : zα ∈ conjClosure V (hz T V) := hZU (mul_mem_conjSub hz1)
  have h8 : (8 : ℕ) ∈ M755.ptsQ := by decide
  obtain ⟨c, hcK, hc⟩ := C.exists_K_θG E (M755.ptQ_ne_one h8) hθ
  have hcH := C.le_hz hcK
  have hUαH := N.uα_le_hz C

  set w := c⁻¹ * zα * c⁻¹⁻¹ with hw
  have hwU : w ∈ conjClosure V (hz T V) :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) (inv_mem hcH)) _).mp
      hzαU
  have hθw : C.θG e w = M755.ptQ 8 := by
    rw [hw, C.θG_conj E (inv_mem hcH) hzαU, ← hc, C.ΦG_inv E hcH, map_inv,
      MulAut.inv_apply_self]
  have hXH : conjSub c⁻¹ (conjSub x (conjClosure V (hz T V))) ≤ hz T V := fun y hy => by
    have h1 : c⁻¹⁻¹ * y * c⁻¹ ∈ hz T V := hUαH (mem_conjSub.1 hy)
    have e1 : y = c⁻¹ * (c⁻¹⁻¹ * y * c⁻¹) * c := by group
    rw [e1]
    exact mul_mem (mul_mem (inv_mem hcH) h1) hcH
  have hXe : IsElemAbelian 2 (conjSub c⁻¹ (conjSub x (conjClosure V (hz T V)))) :=
    F7.isElemAbelian_conjSub (F7.isElemAbelian_conjSub C.hF98.F911_3)
  have hX1 := C.ΦX_conj_ne_bot E N hcH hXH

  have hN : ∀ h ∈ hz T V, h * w = w * h →
      ∀ u ∈ conjSub c⁻¹ (conjSub x (conjClosure V (hz T V))),
        h * u * h⁻¹ ∈ conjSub c⁻¹ (conjSub x (conjClosure V (hz T V))) := by
    intro h hh hhw u hu
    have hzw : zα = c * w * c⁻¹ := by rw [hw]; group
    have hcomm : (c * h * c⁻¹) * zα = zα * (c * h * c⁻¹) := by
      rw [hzw]
      calc c * h * c⁻¹ * (c * w * c⁻¹) = c * (h * w) * c⁻¹ := by group
        _ = c * (w * h) * c⁻¹ := by rw [hhw]
        _ = c * w * c⁻¹ * (c * h * c⁻¹) := by group
    have hGα := C.mem_Gα_of_comm (x := x) hz1 hzne hcomm
    have hNα := (Subgroup.mem_normalizer_iff.mp
      (conjSub_le_normalizer (le_normalizer_conjClosure V (hz T V)) x hGα))
    have hu' : c⁻¹⁻¹ * u * c⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := mem_conjSub.1 hu
    rw [inv_inv] at hu'
    have h1 := (hNα _).mp hu'
    refine mem_conjSub.2 ?_
    have e1 : c⁻¹⁻¹ * (h * u * h⁻¹) * c⁻¹ =
        c * h * c⁻¹ * (c * u * c⁻¹) * (c * h * c⁻¹)⁻¹ := by group
    rw [e1]
    exact h1
  obtain ⟨-, hcl⟩ := C.class_p0_F4 E hG h13322 hMod h13314 h1222 hwU hθw hXH hXe hX1 hN

  have hB0 : ∀ b ∈ [2, 4, 6],
      sEltG b ∈ C.ΦX E (conjSub c⁻¹ (conjSub x (conjClosure V (hz T V)))) := by
    intro b hb
    have hb' : b ∈ idx (C.ΦX E (conjSub c⁻¹ (conjSub x (conjClosure V (hz T V))))) := by
      rcases hcl with h | h
      · exact (h b).2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega)
      · exact (h b).2 (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega)
    exact (mem_idx.1 hb').2

  have hfixV : ∀ v ∈ V, ∀ b ∈ [2, 4, 6],
      g2QAct (ZMod 2) (sEltG b) ((g2QAct (ZMod 2) (C.ΦG E c))⁻¹ (C.θG e v)) =
        (g2QAct (ZMod 2) (C.ΦG E c))⁻¹ (C.θG e v) := by
    intro v hv b hb
    obtain ⟨u, hu, hub⟩ := (C.mem_ΦX E hXH).1 (hB0 b hb)
    have hu' : c⁻¹⁻¹ * u * c⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := mem_conjSub.1 hu
    have hR := (N.uα_le_R1 C) hu'
    have hfix := C.ΦG_fix_V E hR hv
    have hΦu : C.ΦG E u = (C.ΦG E c)⁻¹ * C.ΦG E (c⁻¹⁻¹ * u * c⁻¹) * C.ΦG E c := by
      rw [C.ΦG_mul E (mul_mem (inv_mem (inv_mem hcH)) (hXH hu)) (inv_mem hcH),
        C.ΦG_mul E (inv_mem (inv_mem hcH)) (hXH hu), C.ΦG_inv E (inv_mem hcH),
        C.ΦG_inv E hcH, inv_inv]
      group
    rw [← hub, hΦu, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv,
      MulAut.apply_inv_self, hfix]
  have hU0 : ∀ v ∈ V, M755.InU0 ((g2QAct (ZMod 2) (C.ΦG E c))⁻¹ (C.θG e v)) := by
    intro v hv
    obtain ⟨c', hc', hce⟩ := M755.exists_code ((g2QAct (ZMod 2) (C.ΦG E c))⁻¹ (C.θG e v))
    have hfix' : ∀ b ∈ [2, 4, 6], M755.actC b c' = c' := by
      intro b hb
      have hb64 : b < 64 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; omega
      have h1 := hfixV v hv b hb
      rw [← hce, M755.g2QAct_sEltG_code hb64 hc'] at h1
      exact M755.ptQ_inj (M755.actC_mem _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega) c' hc') hc' h1
    exact ⟨c', (M755.facts_CB0 c' hc').1 ⟨hfix' 2 (by simp), hfix' 4 (by simp),
      hfix' 6 (by simp)⟩, hce⟩

  obtain ⟨v₃₂, hv₃₂, hv₃₂1, hθ₃₂⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ (d := 32) (by simp)
  obtain ⟨v₄₀, hv₄₀, hv₄₀1, hθ₄₀⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ (d := 40) (by simp)
  obtain ⟨v₈, hv₈, hv₈1, hθ₈⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ (d := 8) (by simp)
  have hσp : ∀ {q : ModQ}, (g2QAct (ZMod 2) (C.ΦG E c))⁻¹ q = M755.ptQ 8 →
      C.θG e zα = q := fun {q} h => by
    rw [← hc, ← h, MulAut.apply_inv_self]
  obtain ⟨c₁, hc₁, hc₁e⟩ := hU0 v₃₂ hv₃₂
  obtain ⟨c₂, hc₂, hc₂e⟩ := hU0 v₄₀ hv₄₀
  rw [hθ₃₂] at hc₁e
  rw [hθ₄₀] at hc₂e
  by_cases h₁ : c₁ = 8
  · refine ⟨v₃₂, hv₃₂, hv₃₂1, ?_⟩
    rw [hθ₃₂]
    exact hσp (by rw [← hc₁e, h₁])
  by_cases h₂ : c₂ = 8
  · refine ⟨v₄₀, hv₄₀, hv₄₀1, ?_⟩
    rw [hθ₄₀]
    exact hσp (by rw [← hc₂e, h₂])

  have h32 : (32 : ℕ) ∈ M755.ptsQ := by decide
  have h40 : (40 : ℕ) ∈ M755.ptsQ := by decide
  have hne0 : ∀ {d c' : ℕ}, d ∈ M755.ptsQ →
      M755.ptQ c' = (g2QAct (ZMod 2) (C.ΦG E c))⁻¹ (M755.ptQ d) → c' ≠ 0 :=
    fun {d c'} hd h hc0 => M755.ptQ_ne_one hd (by
      rw [hc0, M755.ptQ_zero] at h
      have h' := congrArg (g2QAct (ZMod 2) (C.ΦG E c)) h
      rwa [MulAut.apply_inv_self, map_one, eq_comm] at h')
  obtain ⟨hp₁, hcoll₁⟩ := M755.u0_facts.2.2.2.2.1 c₁ hc₁ (hne0 h32 hc₁e) h₁
  obtain ⟨hp₂, hcoll₂⟩ := M755.u0_facts.2.2.2.2.1 c₂ hc₂ (hne0 h40 hc₂e) h₂
  have hC1 : M755.CollQ (M755.ptQ 8) (M755.ptQ c₁) := (M755.collQ_ptQ h8 hp₁).2 hcoll₁
  have hC2 : M755.CollQ (M755.ptQ 8) (M755.ptQ c₂) := (M755.collQ_ptQ h8 hp₂).2 hcoll₂
  have hC12 : M755.CollQ (M755.ptQ c₁) (M755.ptQ c₂) := by
    rw [hc₁e, hc₂e, ← map_inv, M755.collQ_act]
    have h3240 : M755.collT 32 40 = true := by decide
    exact (M755.collQ_ptQ h32 h40).2 h3240
  have htri := M755.collQ_tri hC12 hC1 hC2
  rw [hc₁e, hc₂e, ← map_mul, M755.ptQ_mul (by decide) (by decide)] at htri
  refine ⟨v₈, hv₈, hv₈1, ?_⟩
  rw [hσp htri.symm, hθ₈]
  rfl

end Ctx753

end CFSG.Quasithin.H13.L32A
