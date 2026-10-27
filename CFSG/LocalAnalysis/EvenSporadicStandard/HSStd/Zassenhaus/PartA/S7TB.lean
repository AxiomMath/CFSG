module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7T
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7OddAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecOdd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusionHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerI1I2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S6
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.PSL2Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

set_option linter.unusedSectionVars false

open Subgroup

section Basic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem s7tb_zpow_sq {y : G} (hy : y * y = 1) (k : ℤ) : y ^ k * y ^ k = 1 := by
  rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hy, one_zpow]

theorem s7tb_sq_of_mem_sup_zpowers {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) {g : G} (hg : g ∈ zpowers x ⊔ zpowers y) : g * g = 1 := by
  have hc : ∀ a ∈ zpowers y, a * x = x * a := by
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute y x from hxy.symm) k).eq
  obtain ⟨n, a, ha, rfl⟩ := S5.exists_zpow_mul_of_mem_sup' hc hg
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  have h1 : y ^ k * x ^ n = x ^ n * y ^ k :=
    ((show Commute y x from hxy.symm).zpow_left k).zpow_right n |>.eq
  calc x ^ n * y ^ k * (x ^ n * y ^ k) = x ^ n * (y ^ k * x ^ n) * y ^ k := by
        simp only [mul_assoc]
    _ = x ^ n * (x ^ n * y ^ k) * y ^ k := by rw [h1]
    _ = (x ^ n * x ^ n) * (y ^ k * y ^ k) := by simp only [mul_assoc]
    _ = 1 := by rw [s7tb_zpow_sq hx, s7tb_zpow_sq hy, mul_one]

@[expose] def PA5.s7tb_V (hb : PAB G L t E W z) (a : PA5 L t E z) : Subgroup ↥a.s7_N₁ :=
  zpowers (a.s7_tT hb) ⊔ zpowers (a.s7_ubT hb)

@[expose] def PA5.s7tb_B (a : PA5 L t E z) : Subgroup ↥a.s7_N₁ := a.Abar.subgroupOf a.s7_N₁

@[expose] def PA5.s7tb_e (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ↥a.s7tb_B ≃* MulAut (alternatingGroup (Fin 6)) :=
  (subgroupOfEquivOfLe (a.s7_Abar_le_N₁ hb)).trans a.eAbar

theorem PA5.s7tb_mem_V (hb : PAB G L t E W z) (a : PA5 L t E z) (x : ↥a.s7_N₁) :
    x ∈ a.s7tb_V hb ↔ (x : G) ∈ Vsub t a.ub := by
  have h : (a.s7tb_V hb).map a.s7_N₁.subtype = Vsub t a.ub := by
    unfold PA5.s7tb_V Vsub
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  rw [← h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem PA5.s7tb_Vsub_comm_Abar (hb : PAB G L t E W z) (a : PA5 L t E z) {v x : G}
    (hv : v ∈ Vsub t a.ub) (hx : x ∈ a.Abar) : v * x = x * v := by
  have h1 : Vsub t a.ub ≤ centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
    · exact (S5.Abar_comm hb a.toPA0 hx).1.symm
    · exact (S5.ub_comm_Abar hb a.toPA0 a.ub_cases hx).symm
  exact mem_centralizer_singleton_iff.1 (h1 hv)

theorem PA5.s7_cent_VB (hb : PAB G L t E W z) (a : PA5 L t E z) {g : G} (hgt : g * t = t * g)
    (hgub : g * a.ub = a.ub * g) : ∃ v ∈ Vsub t a.ub, ∃ b ∈ a.Abar, g = v * b := by
  have htt := hb.t_mul_t
  have hut : a.u * t = t * a.u := S5.u_comm_t hb a.toPA0
  have hgu : g * a.u = a.u * g := by
    rcases a.ub_cases with h | h
    · rw [← h]; exact hgub
    · have hu : a.u = t * a.ub := by rw [h, ← mul_assoc, htt, one_mul]
      rw [hu]
      calc g * (t * a.ub) = (g * t) * a.ub := (mul_assoc _ _ _).symm
        _ = (t * g) * a.ub := by rw [hgt]
        _ = t * (g * a.ub) := mul_assoc _ _ _
        _ = t * (a.ub * g) := by rw [hgub]
        _ = t * a.ub * g := (mul_assoc _ _ _).symm
  have hg : g ∈ L ⊔ zpowers t := by
    rw [← hb.inner]
    exact mem_centralizer_singleton_iff.2 hgt
  rw [sup_comm] at hg
  obtain ⟨n, l, hl, rfl⟩ := S5.exists_zpow_mul_of_mem_sup' (A := L)
    (fun x hx => mem_centralizer_iff.1 hb.t_cent x hx) hg
  have hcu : a.u * t ^ n = t ^ n * a.u := ((show Commute a.u t from hut).zpow_right n).eq
  have hlu : l * a.u = a.u * l := by
    apply mul_left_cancel (a := t ^ n)
    calc t ^ n * (l * a.u) = (t ^ n * l) * a.u := (mul_assoc _ _ _).symm
      _ = a.u * (t ^ n * l) := hgu
      _ = (a.u * t ^ n) * l := (mul_assoc _ _ _).symm
      _ = (t ^ n * a.u) * l := by rw [hcu]
      _ = t ^ n * (a.u * l) := mul_assoc _ _ _
  have hl' : l ∈ L ⊓ Cen a.u := ⟨hl, mem_Cen.2 hlu⟩
  rw [a.Abar_comp] at hl'
  obtain ⟨j, b, hbA, rfl⟩ := S5.exists_zpow_mul_of_mem_sup' (A := a.Abar) (t := a.u)
    (fun x hx => (S5.Abar_comm hb a.toPA0 hx).2) hl'
  refine ⟨t ^ n * a.u ^ j, ?_, b, hbA, (mul_assoc _ _ _).symm⟩
  rw [a.s7_Vsub_ub_eq hb]
  exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers t) n))
    (mem_sup_right (zpow_mem (mem_zpowers a.u) j))

theorem PA5.s7_V_inf_Abar (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ x ∈ Vsub t a.ub, x ∈ a.Abar → x = 1 := by
  intro x hxV hxA
  have := isSimple_alt6
  have hz : a.eAbar ⟨x, hxA⟩ ∈ Subgroup.center (MulAut (alternatingGroup (Fin 6))) := by
    rw [Subgroup.mem_center_iff]
    intro f
    obtain ⟨b, rfl⟩ := a.eAbar.surjective f
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (a.s7tb_Vsub_comm_Abar hb hxV b.2).symm
  rw [center_mulAut_eq_bot alt6_nonabelian, mem_bot] at hz
  have h1 : (⟨x, hxA⟩ : ↥a.Abar) = 1 := a.eAbar.injective (by rw [hz, map_one])
  exact congrArg Subtype.val h1

theorem PA5.s7tb_V_pgroup (hb : PAB G L t E W z) (a : PA5 L t E z) :
    IsPGroup 2 ↥(a.s7tb_V hb) := by
  intro g
  refine ⟨1, ?_⟩
  have hsq : (g : ↥a.s7_N₁) * g = 1 :=
    s7tb_sq_of_mem_sup_zpowers (x := a.s7_tT hb) (y := a.s7_ubT hb)
      (Subtype.ext hb.t_mul_t) (Subtype.ext (a.s7_ub_sq hb))
      (Subtype.ext (a.s7_ub_t hb).symm) g.2
  rw [pow_one, pow_two]
  exact Subtype.ext hsq

theorem PA5.s7tb_hW (hb : PAB G L t E W z) (a : PA5 L t E z) (w : ↥a.s7_N₁)
    (hw : w * a.s7_tT hb = a.s7_tT hb * w) :
    ∃ v ∈ a.s7tb_V hb, ∃ b ∈ a.s7tb_B, w = v * b := by
  have hgt : (w : G) * t = t * w := congrArg Subtype.val hw
  have hgub : (w : G) * a.ub = a.ub * w := ((a.s7_mem_N₁).1 w.2).2
  obtain ⟨v, hv, b, hb', hvb⟩ := a.s7_cent_VB hb hgt hgub
  have hbN := a.s7_Abar_le_N₁ hb hb'
  have hvN : v ∈ a.s7_N₁ := by
    have : v = w * b⁻¹ := by rw [hvb]; exact (mul_inv_cancel_right v b).symm
    rw [this]
    exact mul_mem w.2 (inv_mem hbN)
  exact ⟨⟨v, hvN⟩, (a.s7tb_mem_V hb _).2 hv, ⟨b, hbN⟩, hb', Subtype.ext hvb⟩

theorem PA5.s7tb_inf_eq_bot (hb : PAB G L t E W z) (a : PA5 L t E z) :
    Open.fusionOddCore ↥a.s7_N₁ ⊓ centralizer ({a.s7_tT hb} : Set ↥a.s7_N₁) = ⊥ := by
  refine odd_normal_inf_eq_bot (centralizer ({a.s7_tT hb} : Set ↥a.s7_N₁)) (a.s7tb_V hb)
    a.s7tb_B (Open.fusionOddCore ↥a.s7_N₁) (a.s7tb_V_pgroup hb) ?_ ?_ ?_ ?_ (a.s7tb_e hb)
    (natCard_fusionOddCore_odd' _)
  · intro v hv b hb'
    exact Subtype.ext (a.s7tb_Vsub_comm_Abar hb ((a.s7tb_mem_V hb v).1 hv) hb')
  · refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (a.s7_ub_t hb)
  · intro b hb'
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (S5.Abar_comm hb a.toPA0 hb').1
  · intro w hw
    exact a.s7tb_hW hb w (mem_centralizer_singleton_iff.1 hw)

theorem PA5.s7tb_inv_comm (hb : PAB G L t E W z) (a : PA5 L t E z) :
    (∀ x ∈ Open.fusionOddCore ↥a.s7_N₁, a.s7_tT hb * x * (a.s7_tT hb)⁻¹ = x⁻¹) ∧
    ∀ x ∈ Open.fusionOddCore ↥a.s7_N₁, ∀ x' ∈ Open.fusionOddCore ↥a.s7_N₁, x * x' = x' * x := by
  refine inv_of_centralizer_eq_bot (O := Open.fusionOddCore ↥a.s7_N₁) (t := a.s7_tT hb)
    (Subtype.ext hb.t_mul_t) (fun o ho => Normal.conj_mem inferInstance o ho _) ?_
  intro o ho hc
  have h : o ∈ Open.fusionOddCore ↥a.s7_N₁ ⊓ centralizer ({a.s7_tT hb} : Set ↥a.s7_N₁) :=
    ⟨ho, mem_centralizer_singleton_iff.2 hc.symm⟩
  rw [a.s7tb_inf_eq_bot hb, mem_bot] at h
  exact h

theorem PA5.s7_hinv (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ x ∈ Open.fusionOddCore ↥a.s7_N₁, a.s7_tT hb * x * (a.s7_tT hb)⁻¹ = x⁻¹ :=
  (a.s7tb_inv_comm hb).1

theorem PA5.s7_core_comm (hb : PAB G L t E W z) (a : PA5 L t E z) :
    ∀ x ∈ Open.fusionOddCore ↥a.s7_N₁, ∀ x' ∈ Open.fusionOddCore ↥a.s7_N₁, x * x' = x' * x :=
  (a.s7tb_inv_comm hb).2

theorem PA5.s7_cent_xhat (hb : PAB G L t E W z) (a : PA5 L t E z) :
    orderOf (a.s7_κ (a.s7_tT hb)) = 2 ∧
      Nonempty (↥(centralizer ({a.s7_κ (a.s7_tT hb)} : Set
        ((↥a.s7_N₁ ⧸ a.s7_F) ⧸ Open.fusionOddCore (↥a.s7_N₁ ⧸ a.s7_F)))) ≃*
        Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) := by
  refine exists_mulEquiv_cent_xhat a.s7_F (Open.fusionOddCore ↥a.s7_N₁) (a.s7_tT hb)
    (a.s7_ubT hb) a.s7tb_B (a.s7tb_V hb) (a.s7tb_e hb) (Subtype.ext hb.t_mul_t)
    (Subtype.ext (a.s7_ub_sq hb))
    (fun g => Subtype.ext ((a.s7_mem_N₁).1 g.2).2)
    ((a.s7_mem_F _).2 (a.s7_ub_mem_F₀ hb))
    (fun h => a.s7_ub_ne_one (congrArg Subtype.val h))
    (fun h => a.s7_t_not_mem_F₀ hb ((a.s7_mem_F _).1 h))
    ?_ ?_ (natCard_fusionOddCore_odd' _) (a.s7_ker_le hb) (a.s7_F_comm_core hb)
    (a.s7_F_disj_core hb) (a.s7_F_pgroup hb) (a.s7_hinv hb) rfl ?_ (a.s7tb_hW hb) ?_
  · intro f hf hft
    have h1 : t * (f : G) * t⁻¹ = f := congrArg Subtype.val hft
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (a.s7_cent_F₀_t hb f hf h1)
    refine mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_zpow]
    exact hk
  · intro g hg
    obtain ⟨w, hw, hgw, hcase⟩ := a.s7_fusion_F₀ hb (g : G) hg
    have hwN : w ∈ a.s7_N₁ := by
      rcases hcase with rfl | ⟨hd, rfl⟩
      · exact g.2
      · exact mul_mem (a.s7_F₀_le_N₁ hb (a.s7_u₁_mem_F₀ hb hd)) g.2
    exact ⟨⟨w, hwN⟩, Subtype.ext hw, hgw⟩
  · intro b hb'
    exact Subtype.ext (S5.Abar_comm hb a.toPA0 hb').1
  · intro x hxV hxB
    exact Subtype.ext (a.s7_V_inf_Abar hb x ((a.s7tb_mem_V hb x).1 hxV) hxB)

end Basic

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
