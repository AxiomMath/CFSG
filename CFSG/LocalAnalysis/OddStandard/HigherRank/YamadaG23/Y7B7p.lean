module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7m
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7o
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs5
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs7

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_inv_mul_mem_X0 (c : Ctx7 G L) (hb : B5Std c) {x m : G} (hx : x ∈ X7 c.s)
    (hm : m ∈ X7 c.s) (h : (⁅x, c.s.t⁆)⁻¹ * ⁅m, c.s.t⁆ ∈ M3 c.s) : m⁻¹ * x ∈ y7bX0 c.s := by
  haveI := y7b_M3_normal_BM c hb
  obtain ⟨θ, hθ, -⟩ := y7b_exists_theta c hb
  have hux : ⁅x, c.s.t⁆ ∈ y7bBM c.s := y7b_comm_t_mem_BM c hb x (y7b_X7_le_X c hx)
  let ux : ↥(y7bBM c.s) := ⟨⁅x, c.s.t⁆, hux⟩
  have hθx : θ ⟨x, hx⟩ = QuotientGroup.mk ux := by
    refine (hθ ⟨x, hx⟩ ux).mpr ?_
    rw [show (ux : G) = ⁅x, c.s.t⁆ from rfl, inv_mul_cancel]
    exact (M3 c.s).one_mem
  have hθm : θ ⟨m, hm⟩ = QuotientGroup.mk ux := by
    refine (hθ ⟨m, hm⟩ ux).mpr ?_
    rw [show (ux : G) = ⁅x, c.s.t⁆ from rfl]
    exact h
  have hmx : m⁻¹ * x ∈ X7 c.s := (X7 c.s).mul_mem ((X7 c.s).inv_mem hm) hx
  have hθ1 : θ ⟨m⁻¹ * x, hmx⟩ = QuotientGroup.mk (1 : ↥(y7bBM c.s)) := by
    have heq : (⟨m⁻¹ * x, hmx⟩ : ↥(X7 c.s)) = ⟨m, hm⟩⁻¹ * ⟨x, hx⟩ := by ext; simp
    rw [heq, map_mul, map_inv, hθm, hθx]
    simp
  have hmem : ⁅m⁻¹ * x, c.s.t⁆ ∈ M3 c.s := by
    have h := (hθ ⟨m⁻¹ * x, hmx⟩ 1).mp hθ1
    simpa using h
  rwa [y7b_X0_iff c hb hmx]

theorem y7b_theta_comm_onto (c : Ctx7 G L) (hb : B5Std c) {k : G}
    (hkN : k ∈ normIn L c.s.fr.B)
    (hfp : ∀ u ∈ y7bBM c.s, u⁻¹ * (k * u * k⁻¹) ∈ M3 c.s → u ∈ M3 c.s)
    {Y : Subgroup G} (hY : Y ≤ X7 c.s) (hkY : ∀ y ∈ Y, k * y * k⁻¹ ∈ Y)
    (honto : ∀ u ∈ y7bBM c.s, ∃ y ∈ Y, u⁻¹ * ⁅y, c.s.t⁆ ∈ M3 c.s) :
    ∀ u ∈ y7bBM c.s, ∃ z ∈ Y, u⁻¹ * ⁅⁅z, k⁆, c.s.t⁆ ∈ M3 c.s := by
  haveI := y7b_M3_normal_BM c hb
  obtain ⟨θ, hθ, hθeq⟩ := y7b_exists_theta c hb
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hkX : k ∈ y7bX c.s := y7b_N_le_X c hb hkNH
  have hnorm : ∀ u ∈ y7bBM c.s, ∀ m ∈ M3 c.s, u * m * u⁻¹ ∈ M3 c.s := by
    intro u hu m hm
    exact (Subgroup.mem_normalizer_iff.mp (y7b_W_le_NM3 c hb (y7b_BM_le_W c hb hu)) m).mp hm
  have hab : ∀ u ∈ y7bBM c.s, ∀ v ∈ y7bBM c.s, ⁅u, v⁆ ∈ M3 c.s :=
    y7b_comm_mem_of_sq_mem le_sup_right hnorm (y7b_BM_sq_mem_M3 c hb)
  have hkU : ∀ u ∈ y7bBM c.s, k * u * k⁻¹ ∈ y7bBM c.s :=
    fun u hu => y7b_X_norm_BM c hb k hkX u hu
  have hkM : ∀ m ∈ M3 c.s, k * m * k⁻¹ ∈ M3 c.s :=
    fun m hm => (Subgroup.mem_normalizer_iff.mp (y7b_N_le_NM3 c hb hkNH) m).mp hm
  intro v hv
  obtain ⟨w, hwU, hvw⟩ := y7b_fpf_onto le_sup_right hnorm hab hkU hkM hfp v hv
  obtain ⟨z, hzY, hwz⟩ := honto w hwU
  have hzX7 : z ∈ X7 c.s := hY hzY
  have hz'Y : k * z * k⁻¹ ∈ Y := hkY z hzY
  have hz'X7 : k * z * k⁻¹ ∈ X7 c.s := hY hz'Y
  have hzkY : ⁅z, k⁆ ∈ Y := by
    rw [show ⁅z, k⁆ = z * (k * z * k⁻¹)⁻¹ by rw [commutatorElement_def]; group]
    exact Y.mul_mem hzY (Y.inv_mem hz'Y)
  have hzkX7 : ⁅z, k⁆ ∈ X7 c.s := hY hzkY
  let u : ↥(y7bBM c.s) := ⟨w, hwU⟩
  let u' : ↥(y7bBM c.s) := ⟨k * w * k⁻¹, hkU w hwU⟩
  have hθw : θ ⟨z, hzX7⟩ = QuotientGroup.mk u :=
    (hθ ⟨z, hzX7⟩ u).mpr (by simpa [u] using hwz)
  have hθw' : θ ⟨k * z * k⁻¹, hz'X7⟩ = QuotientGroup.mk u' :=
    hθeq k hkNH ⟨z, hzX7⟩ ⟨k * z * k⁻¹, hz'X7⟩ rfl u u' rfl hθw
  have heq : (⟨⁅z, k⁆, hzkX7⟩ : ↥(X7 c.s)) = ⟨z, hzX7⟩ * ⟨k * z * k⁻¹, hz'X7⟩⁻¹ := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [commutatorElement_def]
    group
  have hθzk : θ ⟨⁅z, k⁆, hzkX7⟩ = QuotientGroup.mk (u * u'⁻¹) := by
    rw [heq, map_mul, map_inv, hθw, hθw', ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  have hmkv : (QuotientGroup.mk (u * u'⁻¹) :
        ↥(y7bBM c.s) ⧸ (M3 c.s).subgroupOf (y7bBM c.s)) =
      QuotientGroup.mk (⟨v, hv⟩ : ↥(y7bBM c.s)) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hX : (w * (k * w * k⁻¹)⁻¹)⁻¹ * v ∈ M3 c.s := by
      have h1 : (w * (k * w * k⁻¹)⁻¹)⁻¹ * v =
          (v⁻¹ * (w * (k * w * k⁻¹)⁻¹))⁻¹ := by group
      rw [h1]
      exact (M3 c.s).inv_mem hvw
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, u, u'] using hX
  refine ⟨z, hzY, ?_⟩
  have h := (hθ ⟨⁅z, k⁆, hzkX7⟩ ⟨v, hv⟩).mp (hθzk.trans hmkv)
  simpa using h

theorem y7b_theta_onto_C7 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ u ∈ y7bBM c.s, ∃ y ∈ C7 c.s, u⁻¹ * ⁅y, c.s.t⁆ ∈ M3 c.s := by
  obtain ⟨k, hkN, _, _, _, hfp, _⟩ := y7b_exists_k c hb
  have hkNH : k ∈ normIn c.s.H c.s.fr.B := ⟨s3_L_le_H c.s hb.hH.hS hkN.1, hkN.2⟩
  have hkY : ∀ y ∈ X7 c.s, k * y * k⁻¹ ∈ X7 c.s :=
    fun y hy => y7b_X7_normal c hb k (y7b_N_le_X c hb hkNH) y hy
  intro u hu
  obtain ⟨z, hz, hzmem⟩ :=
    y7b_theta_comm_onto (Y := X7 c.s) c hb hkN hfp le_rfl hkY
      (y7b_theta_onto_X7 c hb) u hu
  refine ⟨⁅z, k⁆, ?_, hzmem⟩
  rw [y7b_C7_eq c hb]
  exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hz hkNH)

theorem y7b_X7_eq_C7_X0 (c : Ctx7 G L) (hb : B5Std c) :
    ∀ y ∈ X7 c.s, ∃ x ∈ C7 c.s, ∃ a ∈ y7bX0 c.s, y = x * a := by
  intro y hy
  have hvBM : ⁅y, c.s.t⁆ ∈ y7bBM c.s := y7b_comm_t_mem_BM c hb y (y7b_X7_le_X c hy)
  obtain ⟨x, hxC7, hxmem⟩ := y7b_theta_onto_C7 c hb ⁅y, c.s.t⁆ hvBM
  have hxX7 : x ∈ X7 c.s := y7b_C7_le_X7 c hb hxC7
  exact ⟨x, hxC7, x⁻¹ * y, y7b_inv_mul_mem_X0 c hb hy hxX7 hxmem, by group⟩

theorem y7b_X7_eq_C7_of_R_eq_T (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R = c.s.T) :
    ∀ y ∈ X7 c.s, y ∈ C7 c.s := by
  intro y hy
  obtain ⟨x, hxC7, a, haX0, rfl⟩ := y7b_X7_eq_C7_X0 c hb y hy
  have haW : a ∈ y7bW c.s := by
    rw [← y7b_X0_eq_W_of_R_eq_T c hb hRT]
    exact haX0
  exact (C7 c.s).mul_mem hxC7 (y7b_W_le_C7 c hb haW)

theorem y7b_X7_cases_C7_g (c : Ctx7 G L) (hb : B5Std c) (hRT : c.s.R ≠ c.s.T) :
    ∀ y ∈ X7 c.s, y ∈ C7 c.s ∨ y * c.g ∈ C7 c.s := by
  have hg1 : c.g * c.g = 1 := y7b_g_mul_self c hb hRT
  have hgX7 : c.g ∈ X7 c.s := y7b_X0_le_X7 c hb (y7b_g_mem_X0 c hb hRT)
  intro y hy
  obtain ⟨x, hxC7, a, haX0, rfl⟩ := y7b_X7_eq_C7_X0 c hb y hy
  rcases y7b_X0_cases_g c hb hRT a haX0 with haW | hgaW
  · exact Or.inl ((C7 c.s).mul_mem hxC7 (y7b_W_le_C7 c hb haW))
  · refine Or.inr ?_
    have hconjC : c.g * (c.g * a) * c.g⁻¹ ∈ C7 c.s :=
      (y7b_C7_normal c hb).1 c.g hgX7 (c.g * a) (y7b_W_le_C7 c hb hgaW)
    have haeq : a * c.g = c.g * (c.g * a) * c.g⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hg1]
      calc a * c.g = (c.g * c.g) * a * c.g := by rw [hg1, one_mul]
        _ = c.g * (c.g * a) * c.g := by group
    rw [show x * a * c.g = x * (a * c.g) by group, haeq]
    exact (C7 c.s).mul_mem hxC7 hconjC

theorem y7b_exists_seed2 (c : Ctx7 G L) (hb : B5Std c) :
    ∃ u ∈ C7 c.s, ⁅u, c.s.t⁆ ∉ M3 c.s ∧ u ^ 2 ∈ M3 c.s ∧ (∀ v ∈ V2 c.e, u * v = v * u) ∧
      (c.s.R ≠ c.s.T → ⁅c.g, u⁆ ∈ M3 c.s) := by
  obtain ⟨m₀, hm₀M4, hm₀sq, _, hm₀tNM3⟩ := y7b_exists_seed c hb
  have hm₀X7 : m₀ ∈ X7 c.s := y7b_M4_le_X7 c hb hm₀M4
  have hM4comm : ∀ a ∈ M4 c.e, ∀ b ∈ M4 c.e, a * b = b * a :=
    fun a ha b hb' => congrArg Subtype.val ((hb.h72.2.1.1).is_comm.comm ⟨a, ha⟩ ⟨b, hb'⟩)
  have hm₀centV2 : ∀ v ∈ V2 c.e, m₀ * v = v * m₀ :=
    fun v hv => hM4comm m₀ hm₀M4 v (Subgroup.mem_inf.mp hv).2
  by_cases hRT : c.s.R = c.s.T
  · exact ⟨m₀, y7b_X7_eq_C7_of_R_eq_T c hb hRT m₀ hm₀X7, hm₀tNM3,
      by rw [hm₀sq]; exact (M3 c.s).one_mem, hm₀centV2, fun hne => absurd hRT hne⟩
  · rcases y7b_X7_cases_C7_g c hb hRT m₀ hm₀X7 with hm₀C7 | hm₀gC7
    · exact ⟨m₀, hm₀C7, hm₀tNM3, by rw [hm₀sq]; exact (M3 c.s).one_mem, hm₀centV2,
        fun _ => y7b_g_comm_M4 c hb hRT m₀ hm₀M4⟩
    · have hgt : c.g * c.s.t = c.s.t * c.g := s3_comm_t_of_mem_T c.s (c.g_spec hRT).1
      have hcgt : ⁅c.g, c.s.t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hgt
      have ht_eq : ⁅m₀ * c.g, c.s.t⁆ = ⁅m₀, c.s.t⁆ := by
        rw [commutatorElement_mul_left_eq_conj_mul, hcgt, mul_one, mul_inv_cancel, one_mul]
      have hsq : (m₀ * c.g) ^ 2 = (m₀ * ⁅c.g, m₀⁆ * m₀⁻¹) * m₀ ^ 2 := by
        rw [pow_two, pow_two, commutatorElement_def,
          inv_eq_of_mul_eq_one_right (y7b_g_mul_self c hb hRT)]
        group
      have hconj : m₀ * ⁅c.g, m₀⁆ * m₀⁻¹ ∈ M3 c.s :=
        (Subgroup.mem_normalizer_iff.mp (y7b_M4_le_NM3 c hb hm₀M4) ⁅c.g, m₀⁆).mp
          (y7b_g_comm_M4 c hb hRT m₀ hm₀M4)
      have hcommV2 : ∀ v ∈ V2 c.e, m₀ * c.g * v = v * (m₀ * c.g) := by
        intro v hv
        have hgv : c.g * v = v * c.g := by
          calc c.g * v = (c.g * v * c.g⁻¹) * c.g := by group
            _ = v * c.g := by rw [y7b_g_cent_V2 c hb hRT v hv]
        have hmv : m₀ * v = v * m₀ := hm₀centV2 v hv
        calc m₀ * c.g * v = m₀ * (c.g * v) := by group
          _ = m₀ * (v * c.g) := by rw [hgv]
          _ = (m₀ * v) * c.g := by group
          _ = (v * m₀) * c.g := by rw [hmv]
          _ = v * (m₀ * c.g) := by group
      refine ⟨m₀ * c.g, hm₀gC7, ?_, ?_, hcommV2, ?_⟩
      · rw [ht_eq]; exact hm₀tNM3
      · rw [hsq]
        exact (M3 c.s).mul_mem hconj (by rw [hm₀sq]; exact (M3 c.s).one_mem)
      · intro _
        have hgm : ⁅c.g, m₀⁆ ∈ M3 c.s := y7b_g_comm_M4 c hb hRT m₀ hm₀M4
        rw [commutatorElement_mul_right_eq_mul_conj, commutatorElement_self, mul_one]
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using hgm

end CFSG.OddStandard.HigherRank.YamadaG23
