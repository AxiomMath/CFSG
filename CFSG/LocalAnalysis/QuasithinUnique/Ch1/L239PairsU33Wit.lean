module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Orb
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Abs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

open scoped commutatorElement

variable {F : Type} [Field F] (hF : Nat.card F = 9)

include hF in
theorem finite_K : Finite (StatedSU 3 3 F) :=
  Nat.finite_of_card_ne_zero (by rw [card_statedSU hF]; norm_num)

@[expose] noncomputable def tau0 : StatedSU 3 3 F :=
  (tauLine (unitaryFieldData_of_card hF) hF (Pt hF 0) : StatedSU 3 3 F)

@[expose] noncomputable def K1 : Subgroup (StatedSU 3 3 F) := Subgroup.centralizer {tau0 hF}

variable {hF}

theorem mem_K1_iff {g : StatedSU 3 3 F} : g ∈ K1 hF ↔ lineAct hF g (Pt hF 0) = Pt hF 0 :=
  (lineAct_eq_self_iff (h := unitaryFieldData_of_card hF) (hF := hF) g (Pt hF 0)).symm

theorem Pt_zero_val : (Pt hF 0).1 = F ∙ ![1, 0, 0] := by
  have : ev F 0 = ![1, 0, 0] := by
    ext k
    fin_cases k <;> simp [ev_apply]
  rw [Pt_val, this]

theorem card_K1 : Nat.card (K1 hF) = 96 :=
  card_centralizer_tauLine (h := unitaryFieldData_of_card hF) (hF := hF) (L₀ := Pt hF 0) Pt_zero_val

variable (hF)

@[expose] noncomputable def N1 : Subgroup (StatedSU 3 3 F) where
  carrier := {g | g ∈ K1 hF ∧ ∀ T : HexLine F, Pt hF 0 ∈ T.1 → lineActLin hF g T = T}
  one_mem' := ⟨(K1 hF).one_mem, fun T _ => lineActLin_one hF T⟩
  mul_mem' := fun {a b} ha hb => ⟨(K1 hF).mul_mem ha.1 hb.1, fun T hT => by
    rw [lineActLin_mul, hb.2 T hT]
    exact ha.2 T hT⟩
  inv_mem' := fun {a} ha => ⟨(K1 hF).inv_mem ha.1, fun T hT => by
    have := congrArg (lineActLin hF a⁻¹) (ha.2 T hT)
    rw [← lineActLin_mul, inv_mul_cancel, lineActLin_one] at this
    exact this.symm⟩

variable {hF}

theorem N1_le_K1 : N1 hF ≤ K1 hF := fun _ hg => hg.1

theorem N1_conj {g x : StatedSU 3 3 F} (hg : g ∈ K1 hF) (hx : x ∈ N1 hF) :
    g * x * g⁻¹ ∈ N1 hF := by
  refine ⟨(K1 hF).mul_mem ((K1 hF).mul_mem hg hx.1) ((K1 hF).inv_mem hg), fun T hT => ?_⟩
  have hgi : lineAct hF g⁻¹ (Pt hF 0) = Pt hF 0 := mem_K1_iff.1 ((K1 hF).inv_mem hg)
  have hT' : Pt hF 0 ∈ (lineActLin hF g⁻¹ T).1 := by
    have := (lineAct_mem_lineActLin hF g⁻¹ T (Pt hF 0)).2 hT
    rwa [hgi] at this
  rw [lineActLin_mul, lineActLin_mul, hx.2 _ hT', ← lineActLin_mul, mul_inv_cancel,
    lineActLin_one]

theorem conj_mem_of_comm {G : Type*} [Group G] (S : Subgroup G) {a g m1 m2 : G}
    (hg3 : g * g * g = 1) (h1 : a * g * a⁻¹ * g⁻¹ = m1) (h2 : m1 * g * m1⁻¹ * g⁻¹ = m2)
    (ha : a ∈ S) (hm1 : m1 ∈ S) (hm2 : m2 ∈ S) : g * a * g⁻¹ ∈ S ∧ g⁻¹ * a * g ∈ S := by
  have hgg : g * g = g⁻¹ := eq_inv_of_mul_eq_one_left hg3
  have hga : g * a * g⁻¹ = m1⁻¹ * a := by
    have : m1⁻¹ = g * a * g⁻¹ * a⁻¹ := by rw [← h1]; group
    rw [this]
    group
  have hgm : g * m1⁻¹ * g⁻¹ = m1⁻¹ * m2 := by rw [← h2]; group
  have e1 : g⁻¹ * g⁻¹ = g := by rw [← _root_.mul_inv_rev, hgg, inv_inv]
  have hga' : g⁻¹ * a * g = g * (g * a * g⁻¹) * g⁻¹ := by
    calc g⁻¹ * a * g = (g * g) * a * (g⁻¹ * g⁻¹) := by rw [hgg, e1]
      _ = g * (g * a * g⁻¹) * g⁻¹ := by group
  refine ⟨?_, ?_⟩
  · rw [hga]
    exact S.mul_mem (S.inv_mem hm1) ha
  · have h3 : g * (m1⁻¹ * a) * g⁻¹ = (g * m1⁻¹ * g⁻¹) * (g * a * g⁻¹) := by group
    rw [hga', hga, h3, hgm, hga]
    exact S.mul_mem (S.mul_mem (S.inv_mem hm1) hm2) (S.mul_mem (S.inv_mem hm1) ha)

section K1Witness

variable (d : Idata F)

theorem gEl_mem_K1 : gEl hF d ∈ K1 hF := mem_K1_iff.2 lineAct_gEl_zero

theorem aEl_mem_K1 : aEl hF d ∈ K1 hF := mem_K1_iff.2 lineAct_aEl_zero

theorem gEl_not_mem_N1 : gEl hF d ∉ N1 hF := fun h =>
  gEl_not_mem_stab0 (mem_stab0_iff.2 (h.2 (ell0 hF) (Pt_mem_ell0 0)))

theorem conj_aEl_mem_stab0 :
    gEl hF d * aEl hF d * (gEl hF d)⁻¹ ∈ stab0 hF ∧
      (gEl hF d)⁻¹ * aEl hF d * gEl hF d ∈ stab0 hF := by
  refine conj_mem_of_comm (stab0 hF) ?_ comm_aEl_gEl comm_m1El_gEl aEl_mem_stab0
    m1El_mem_stab0 m2El_mem_stab0
  rw [← pow_two, ← pow_succ]
  exact gEl_pow_three

theorem aEl_mem_N1 : aEl hF d ∈ N1 hF := by
  refine ⟨aEl_mem_K1 d, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := conj_aEl_mem_stab0 (hF := hF) d
  rcases mem_lines_through d T hT with rfl | rfl | rfl
  · exact mem_stab0_iff.1 aEl_mem_stab0
  · rw [← lineActLin_mul]
    have : aEl hF d * gEl hF d = gEl hF d * ((gEl hF d)⁻¹ * aEl hF d * gEl hF d) := by group
    rw [this, lineActLin_mul, mem_stab0_iff.1 h2]
  · rw [← lineActLin_mul]
    have : aEl hF d * (gEl hF d)⁻¹ = (gEl hF d)⁻¹ * (gEl hF d * aEl hF d * (gEl hF d)⁻¹) := by group
    rw [this, lineActLin_mul, mem_stab0_iff.1 h1]

include d in
theorem isPGroup_N1 : IsPGroup 2 (N1 hF) := by
  have := finite_K hF
  have hN : ((N1 hF).subgroupOf (K1 hF)).Normal :=
    normal_subgroupOf_of_conj fun g hg x hx => N1_conj hg hx
  have h23 : Order23 ↥(K1 hF) := ⟨5, by rw [card_K1]; norm_num⟩
  have hgK : (⟨gEl hF d, gEl_mem_K1 d⟩ : ↥(K1 hF)) ∉ (N1 hF).subgroupOf (K1 hF) :=
    gEl_not_mem_N1 d
  have h2 := isPGroup_two_of_normal h23 (N := (N1 hF).subgroupOf (K1 hF))
    (g := ⟨gEl hF d, gEl_mem_K1 d⟩) (by rw [Subgroup.orderOf_mk]; exact orderOf_gEl) hgK
  exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe N1_le_K1)

include d in
theorem witness_K1 : Witness (K1 hF) := by
  refine ⟨⟨5, by rw [card_K1]; norm_num⟩, ?_⟩
  refine ⟨gEl hF d, gEl_mem_K1 d, orderOf_gEl, N1 hF, N1_le_K1, fun g hg x hx => N1_conj hg hx,
    isPGroup_N1 d, aEl hF d, aEl_mem_N1 d, ?_⟩
  have e1 : ⁅aEl hF d, gEl hF d⁆ = m1El hF d := by
    rw [commutatorElement_def]
    exact comm_aEl_gEl
  have e2 : ⁅m1El hF d, gEl hF d⁆ = m2El hF := by
    rw [commutatorElement_def]
    exact comm_m1El_gEl
  rw [e1, e2]
  exact m2El_sq_ne_one (d := d)

end K1Witness

variable (hF)

@[expose] noncomputable def D0 : Subgroup (StatedSU 3 3 F) where
  carrier := {g | g ∈ stab0 hF ∧ ∀ j : Fin 3, lineAct hF g (Pt hF j) = Pt hF j}
  one_mem' := ⟨(stab0 hF).one_mem, fun j => lineAct_one hF _⟩
  mul_mem' := fun {a b} ha hb => ⟨(stab0 hF).mul_mem ha.1 hb.1, fun j => by
    rw [lineAct_mul, hb.2 j, ha.2 j]⟩
  inv_mem' := fun {a} ha => ⟨(stab0 hF).inv_mem ha.1, fun j => by
    have := congrArg (lineAct hF a⁻¹) (ha.2 j)
    rw [← lineAct_mul, inv_mul_cancel, lineAct_one] at this
    exact this.symm⟩

variable {hF}

theorem D0_le_stab0 : D0 hF ≤ stab0 hF := fun _ hg => hg.1

theorem D0_conj {g x : StatedSU 3 3 F} (hg : g ∈ stab0 hF) (hx : x ∈ D0 hF) :
    g * x * g⁻¹ ∈ D0 hF := by
  refine ⟨(stab0 hF).mul_mem ((stab0 hF).mul_mem hg hx.1) ((stab0 hF).inv_mem hg), fun j => ?_⟩
  obtain ⟨k, hk⟩ := exists_lineAct_Pt_of_mem_stab0 ((stab0 hF).inv_mem hg) j
  rw [lineAct_mul, lineAct_mul, hk, hx.2 k, ← hk, ← lineAct_mul, mul_inv_cancel, lineAct_one]

section Stab0Witness

variable (d : Idata F)

theorem cEl_not_mem_D0 : cEl hF ∉ D0 hF := by
  intro h
  have := h.2 0
  rw [lineAct_cEl] at this
  exact absurd (Pt_injective this) (by decide)

include d in
theorem isPGroup_D0 : IsPGroup 2 (D0 hF) := by
  have := finite_K hF
  have hN : ((D0 hF).subgroupOf (stab0 hF)).Normal :=
    normal_subgroupOf_of_conj fun g hg x hx => D0_conj hg hx
  have h23 : Order23 ↥(stab0 hF) := ⟨5, by rw [card_stab0 d]; norm_num⟩
  have hgK : (⟨cEl hF, cEl_mem_stab0⟩ : ↥(stab0 hF)) ∉ (D0 hF).subgroupOf (stab0 hF) :=
    cEl_not_mem_D0
  have h2 := isPGroup_two_of_normal h23 (N := (D0 hF).subgroupOf (stab0 hF))
    (g := ⟨cEl hF, cEl_mem_stab0⟩) (by rw [Subgroup.orderOf_mk]; exact orderOf_cEl) hgK
  exact h2.of_equiv (Subgroup.subgroupOfEquivOfLe D0_le_stab0)

theorem sEl_mem_D0 : sEl hF d ∈ D0 hF := ⟨sEl_mem_stab0, fun j => lineAct_sEl j⟩

include d in
theorem witness_stab0 : Witness (stab0 hF) := by
  refine ⟨⟨5, by rw [card_stab0 d]; norm_num⟩, ?_⟩
  refine ⟨cEl hF, cEl_mem_stab0, orderOf_cEl, D0 hF, D0_le_stab0, fun g hg x hx => D0_conj hg hx,
    isPGroup_D0 d, sEl hF d, sEl_mem_D0 d, ?_⟩
  have e1 : ⁅sEl hF d, cEl hF⁆ = u1El hF d := by
    rw [commutatorElement_def]
    exact comm_sEl_cEl
  have e2 : ⁅u1El hF d, cEl hF⁆ = u2El hF d := by
    rw [commutatorElement_def]
    exact comm_u1El_cEl
  rw [e1, e2]
  exact u2El_sq_ne_one

end Stab0Witness

end CFSG.QuasithinUnique.Vol2Native.L239.U33
