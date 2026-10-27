module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4ZR

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped Pointwise

theorem conj_image_smul_coset {G : Type*} [Group G] {V : Subgroup G} {x : G}
    (hx : x ∈ normalizer (V : Set G)) (y : G) :
    (fun g => x * g * x⁻¹) '' (y • (V : Set G)) = (x * y * x⁻¹) • (V : Set G) := by
  ext g
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨x * v * x⁻¹, (mem_normalizer_iff.mp hx v).mp hv, ?_⟩
    simp only [smul_eq_mul]
    group
  · rintro ⟨v, hv, rfl⟩
    have hv' : x⁻¹ * v * x ∈ V := by
      have := (mem_normalizer_iff.mp (inv_mem hx) v).mp hv
      rwa [inv_inv] at this
    refine ⟨y * (x⁻¹ * v * x), ⟨x⁻¹ * v * x, hv', rfl⟩, ?_⟩
    simp only [smul_eq_mul]
    group

theorem mem_sup_zpowers_iff {G : Type*} [Group G] {K : Subgroup G} {t : G} (ht : t * t = 1)
    (hK : ∀ k ∈ K, t * k * t ∈ K) {x : G} : x ∈ K ⊔ zpowers t ↔ x ∈ K ∨ x * t ∈ K := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let S : Subgroup G :=
    { carrier := {x | x ∈ K ∨ x * t ∈ K}
      one_mem' := Or.inl (one_mem K)
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
        · refine Or.inr ?_
          rw [show x * y * t = (x * t) * (t * y * t) by
            rw [show (x * t) * (t * y * t) = x * (t * t) * y * t by group, ht, mul_one]]
          exact mul_mem hx (hK y hy)
        · refine Or.inl ?_
          rw [show x * y = (x * t) * (t * (y * t) * t) by
            rw [show (x * t) * (t * (y * t) * t) = x * (t * t) * y * (t * t) by group, ht,
              mul_one, mul_one]]
          exact mul_mem hx (hK _ hy)
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (inv_mem hx)
        · refine Or.inr ?_
          have := hK _ (inv_mem hx)
          rwa [show t * (x * t)⁻¹ * t = x⁻¹ * t by
            rw [mul_inv_rev, ht', ← mul_assoc, ht, one_mul]] at this }
  constructor
  · intro hx
    have hle : K ⊔ zpowers t ≤ S := sup_le (fun k hk => Or.inl hk)
      ((zpowers_le).2 (Or.inr (by rw [ht]; exact one_mem K)))
    exact hle hx
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · rw [show x = (x * t) * t⁻¹ by group]
      exact mul_mem (mem_sup_left hx) (inv_mem (mem_sup_right (mem_zpowers t)))

@[expose] def Data.AW {G : Type} [Group G] (d : Data G) : Subgroup G := d.A₁ ⊔ d.W

@[expose] def Data.AWT {G : Type} [Group G] (d : Data G) : Subgroup G := d.withT d.AW

@[expose] def Data.XW {G : Type} [Group G] (d : Data G) : Subgroup G :=
  normalizer (d.AWT : Set G) ⊓ normalizer (d.W : Set G)

@[expose] def Data.OmW {G : Type} [Group G] (d : Data G) : Set (Set G) :=
  {S | ∃ x ∈ d.XW, S = (x * d.t * x⁻¹) • (d.W : Set G)}

@[expose] def Data.CycW {G : Type} [Group G] (d : Data G) : Prop := ∃ w ∈ d.W, w * w ≠ 1

@[expose] def Data.ptW {G : Type} [Group G] (d : Data G) (k : Fin 27) : Set G :=
  (d.ι (orbSU k * b₀SU * (orbSU k)⁻¹) * d.t) • (d.W : Set G)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem z_mul_z : d.z * d.z = 1 := by
  rw [Data.z, ← map_mul, zSU_mul_self, map_one]

theorem A₁_comm_W
    (h : d.Hyp) {a w : G}
    (ha : a ∈ d.A₁) (hw : w ∈ d.W) : a * w = w * a :=
  mem_centralizer_iff.1 (h.sec4_9_W.2.2.2.2.2 hw) a ha

theorem t_comm_of_mem_L (h : d.Hyp) {a : G} (ha : a ∈ d.L) : a * d.t = d.t * a :=
  comm_of_mem_centralizer h.t_mem ha

theorem W_crossed_eq_z
    (h : d.Hyp) {w : G}
    (hw : w ∈ d.W) (hwz : w ∉ d.ZX₄) : w⁻¹ * d.t * w * d.t = d.z := by
  rcases eq_one_or_eq_z (h.W_crossed_mem_ZX₄ hw) with e | e
  · exfalso
    apply hwz
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2
      ((crossed_eq_one_iff h.t_mul_t).1 e)⟩
  · exact e

theorem mem_ZX₄_of_mem_W_of_mem_F
    (h : d.Hyp) {w : G} (hw : w ∈ d.W) (hwF : w ∈ d.F) :
    w ∈ d.ZX₄ := by
  rw [← h.W_inf_H]
  exact Subgroup.mem_inf.2 ⟨hw, h.withT_F_le_H (mem_sup_left hwF)⟩

theorem W_sq_mem
    (h : d.Hyp) {w : G}
    (hw : w ∈ d.W) : w * w ∈ d.ZX₄ :=
  h.mem_ZX₄_of_mem_W_of_mem_F (mul_mem hw hw) (h.U_sq (h.E₂_le_U (h.Y_eq_E₂ ▸ d.W_le_Y hw)))

theorem W_sq_of_cyc
    (h : d.Hyp)
    (hc : d.CycW) {w : G} (hw : w ∈ d.W) (hwz : w ∉ d.ZX₄) : w * w = d.z := by
  obtain ⟨w₀, hw₀, hw₀2⟩ := hc
  have hw₀z : w₀ ∉ d.ZX₄ := fun hz => hw₀2 (by
    rcases eq_one_or_eq_z hz with rfl | rfl
    · exact mul_one 1
    · exact z_mul_z)
  have hw₀sq : w₀ * w₀ = d.z := by
    rcases eq_one_or_eq_z (h.W_sq_mem hw₀) with e | e
    · exact absurd e hw₀2
    · exact e
  have hcw := h.W_crossed_eq_z hw hwz
  have hcw₀ := h.W_crossed_eq_z hw₀ hw₀z
  have hzc : ∀ {y}, y ∈ d.W → y * d.z = d.z * y := fun hy => h.W_comm_z hy
  have hinv : (w₀⁻¹)⁻¹ * d.t * w₀⁻¹ * d.t = d.z := by
    have e1 : d.t * w₀ * d.t = w₀ * d.z := by
      calc d.t * w₀ * d.t = w₀ * (w₀⁻¹ * d.t * w₀ * d.t) := by group
        _ = w₀ * d.z := by rw [hcw₀]
    have e2 : d.t * w₀⁻¹ * d.t = d.z * w₀⁻¹ := by
      have := congrArg (·⁻¹) e1
      simp only [mul_inv_rev, h.t_inv] at this
      rw [show d.z⁻¹ = d.z from inv_eq_of_mul_eq_one_right z_mul_z] at this
      rw [← this]
      group
    calc (w₀⁻¹)⁻¹ * d.t * w₀⁻¹ * d.t = w₀ * (d.t * w₀⁻¹ * d.t) := by group
      _ = w₀ * (d.z * w₀⁻¹) := by rw [e2]
      _ = d.z := by rw [← mul_assoc, hzc hw₀]; group
  have hU : ∀ {y}, y ∈ d.W → y ∈ d.U := fun hy => h.E₂_le_U (h.Y_eq_E₂ ▸ d.W_le_Y hy)
  have hcr : (w * w₀⁻¹)⁻¹ * d.t * (w * w₀⁻¹) * d.t = 1 := by
    rw [crossed_mul h.t_mul_t (h.U_comm_F (hU (inv_mem hw₀)) (h.U_crossed_mem_F (hU hw))).symm,
      hcw, hinv, z_mul_z]
  have hmem : w * w₀⁻¹ ∈ d.ZX₄ := by
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨mul_mem hw (inv_mem hw₀), mem_centralizer_singleton_iff.2
      ((crossed_eq_one_iff h.t_mul_t).1 hcr)⟩
  rcases eq_one_or_eq_z hmem with e | e
  · rw [show w = w₀ by rw [← mul_inv_eq_one, e]]
    exact hw₀sq
  · have hw' : w = d.z * w₀ := by rw [← e]; group
    rw [hw', show d.z * w₀ * (d.z * w₀) = d.z * (w₀ * d.z) * w₀ by group, hzc hw₀,
      show d.z * (d.z * w₀) * w₀ = (d.z * d.z) * (w₀ * w₀) by group, z_mul_z, one_mul, hw₀sq]

theorem t_conj_W_of_cyc
    (h : d.Hyp)
    (hc : d.CycW) {w : G} (hw : w ∈ d.W) : d.t * w * d.t = w⁻¹ := by
  by_cases hwz : w ∈ d.ZX₄
  · have hwL : w ∈ d.L := h.F_le_L (d.ZX₄_le_F hwz)
    rw [← h.t_comm_of_mem_L hwL, mul_assoc, h.t_mul_t, mul_one]
    rcases eq_one_or_eq_z hwz with rfl | rfl
    · rw [inv_one]
    · exact (inv_eq_of_mul_eq_one_right z_mul_z).symm
  · have hcw := h.W_crossed_eq_z hw hwz
    have hsq := h.W_sq_of_cyc hc hw hwz
    have h4 : w * w * (w * w) = 1 := by rw [hsq, z_mul_z]
    calc d.t * w * d.t = w * (w⁻¹ * d.t * w * d.t) := by group
      _ = w * d.z := by rw [hcw]
      _ = w * (w * w) := by rw [hsq]
      _ = w⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        rw [show w * (w * w) * w = w * w * (w * w) by group, h4]

theorem mul_t_mul_self_of_cyc
    (h : d.Hyp)
    (hc : d.CycW) {a w : G} (ha : a ∈ d.A₁) (hw : w ∈ d.W) :
    a * w * d.t * (a * w * d.t) = a * a := by
  have hat : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ ha)
  have haw : a * w = w * a := h.A₁_comm_W ha hw
  have htw := h.t_conj_W_of_cyc hc hw
  calc a * w * d.t * (a * w * d.t) = a * (w * (d.t * a) * w * d.t) := by group
    _ = a * (w * (a * d.t) * w * d.t) := by rw [hat]
    _ = a * ((w * a) * (d.t * w * d.t)) := by group
    _ = a * ((a * w) * w⁻¹) := by rw [htw, haw]
    _ = a * a := by group

theorem exists_eq_mul_of_mem_AW
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.AW) : ∃ a ∈ d.A₁, ∃ w ∈ d.W, a * w = x :=
  CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (fun _ ha _ hw => h.A₁_comm_W ha hw) hx

theorem AW_comm_W
    (h : d.Hyp) {x w : G}
    (hx : x ∈ d.AW) (hw : w ∈ d.W) : x * w = w * x := by
  obtain ⟨a, ha, w', hw', rfl⟩ := h.exists_eq_mul_of_mem_AW hx
  rw [mul_assoc, h.Y_comm (d.W_le_Y hw') (d.W_le_Y hw), ← mul_assoc, h.A₁_comm_W ha hw,
    mul_assoc]

theorem t_conj_AW
    (h : d.Hyp)
    (hc : d.CycW) {x : G} (hx : x ∈ d.AW) : d.t * x * d.t ∈ d.AW := by
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hx
  have hat : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ ha)
  rw [show d.t * (a * w) * d.t = (d.t * a) * (w * d.t) by group, ← hat,
    show a * d.t * (w * d.t) = a * (d.t * w * d.t) by group, h.t_conj_W_of_cyc hc hw]
  exact mul_mem (mem_sup_left ha) (mem_sup_right (inv_mem hw))

theorem mem_AWT_iff
    (h : d.Hyp)
    (hc : d.CycW) {x : G} : x ∈ d.AWT ↔ x ∈ d.AW ∨ x * d.t ∈ d.AW :=
  mem_sup_zpowers_iff h.t_mul_t fun _ hk => h.t_conj_AW hc hk

theorem exists_W_not_mem (_h : d.Hyp) (hc : d.CycW) : ∃ w ∈ d.W, w ∉ d.ZX₄ := by
  obtain ⟨w, hw, hw2⟩ := hc
  refine ⟨w, hw, fun hz => hw2 ?_⟩
  rcases eq_one_or_eq_z hz with rfl | rfl
  · exact mul_one 1
  · exact z_mul_z

theorem t_not_mem_AW
    (h : d.Hyp)
    (hc : d.CycW) : d.t ∉ d.AW := by
  intro ht
  obtain ⟨w, hw, hwz⟩ := h.exists_W_not_mem hc
  apply hwz
  rw [← h.W_inf_H]
  exact Subgroup.mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 (h.AW_comm_W ht hw).symm⟩

theorem mem_AW_of_comm
    (h : d.Hyp)
    (hc : d.CycW) {x : G} (hx : x ∈ d.AWT) (hxW : ∀ w ∈ d.W, x * w = w * x) : x ∈ d.AW := by
  rcases (h.mem_AWT_iff hc).1 hx with hx | hx
  · exact hx
  · exfalso
    apply h.t_not_mem_AW hc
    have : d.t = (x * d.t)⁻¹ * x := by rw [mul_inv_rev, h.t_inv]; group
    obtain ⟨w, hw, hwz⟩ := h.exists_W_not_mem hc
    exfalso
    apply hwz
    rw [← h.W_inf_H]
    refine Subgroup.mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    have e1 := hxW w hw
    have e2 := h.AW_comm_W hx hw
    calc w * d.t = w * ((x * d.t)⁻¹ * x) := by rw [← this]
      _ = (x * d.t)⁻¹ * (x * d.t * w) * (x * d.t)⁻¹ * x := by group
      _ = (x * d.t)⁻¹ * (w * (x * d.t)) * (x * d.t)⁻¹ * x := by rw [e2]
      _ = (x * d.t)⁻¹ * w * x := by group
      _ = (x * d.t)⁻¹ * x * w := by rw [mul_assoc, ← e1, ← mul_assoc]
      _ = d.t * w := by rw [← this]

theorem conj_mem_AW_of_mem_XW
    (h : d.Hyp)
    (hc : d.CycW) {x : G} (hx : x ∈ d.XW) {k : G} (hk : k ∈ d.AW) : x * k * x⁻¹ ∈ d.AW := by
  obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.1 hx
  refine h.mem_AW_of_comm hc ((mem_normalizer_iff.1 hxA k).1 (mem_sup_left hk)) fun w hw => ?_
  have hw' : x⁻¹ * w * x ∈ d.W := by
    have := (mem_normalizer_iff.1 (inv_mem hxW) w).1 hw
    rwa [inv_inv] at this
  have e := h.AW_comm_W hk hw'
  calc x * k * x⁻¹ * w = x * (k * (x⁻¹ * w * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * w * x) * k) * x⁻¹ := by rw [e]
    _ = w * (x * k * x⁻¹) := by group

theorem exists_of_mem_OmW
    (h : d.Hyp)
    (hc : d.CycW) {S : Set G} (hS : S ∈ d.OmW) :
    ∃ a ∈ d.A₁, a * a = 1 ∧ S = (a * d.t) • (d.W : Set G) := by
  obtain ⟨x, hx, rfl⟩ := hS
  obtain ⟨hxA, -⟩ := Subgroup.mem_inf.1 hx
  have htA : d.t ∈ d.AWT := mem_sup_right (mem_zpowers _)
  have hm : x * d.t * x⁻¹ ∈ d.AWT := (mem_normalizer_iff.1 hxA _).1 htA
  have hnot : x * d.t * x⁻¹ ∉ d.AW := fun hk => h.t_not_mem_AW hc (by
    have := h.conj_mem_AW_of_mem_XW hc (inv_mem hx) hk
    rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this)
  rcases (h.mem_AWT_iff hc).1 hm with hk | hk
  · exact absurd hk hnot
  · obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW hk
    have hxt : x * d.t * x⁻¹ = a * w * d.t := by
      calc x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t) * d.t := by
            rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
        _ = a * w * d.t := by rw [← e]
    refine ⟨a, ha, ?_, ?_⟩
    · rw [← h.mul_t_mul_self_of_cyc hc ha hw, ← hxt]
      exact h.conj_t_mul_self x
    · rw [hxt, leftCoset_eq_iff, show (a * w * d.t)⁻¹ * (a * d.t) = d.t⁻¹ * w⁻¹ * d.t by group,
        h.t_inv, h.t_conj_W_of_cyc hc (inv_mem hw), inv_inv]
      exact hw

theorem coset_eq_iff
    (h : d.Hyp) {a a' : G}
    (ha : a ∈ d.A₁) (ha' : a' ∈ d.A₁) :
    (a * d.t) • (d.W : Set G) = (a' * d.t) • (d.W : Set G) ↔ a⁻¹ * a' ∈ d.ZX₄ := by
  have hL : a⁻¹ * a' ∈ d.L := d.pull_le_L _ (mul_mem (inv_mem ha) ha')
  have e : (a * d.t)⁻¹ * (a' * d.t) = a⁻¹ * a' := by
    calc (a * d.t)⁻¹ * (a' * d.t) = d.t⁻¹ * ((a⁻¹ * a') * d.t) := by group
      _ = d.t⁻¹ * (d.t * (a⁻¹ * a')) := by rw [h.t_comm_of_mem_L hL]
      _ = a⁻¹ * a' := by group
  rw [leftCoset_eq_iff, e]
  constructor
  · intro hW
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨hW, h.L_le_H hL⟩
  · intro hZ
    rw [← h.W_inf_H] at hZ
    exact (Subgroup.mem_inf.1 hZ).1

theorem coset_ι_eq_iff
    (h : d.Hyp)
    {α α' : SU52} (hα : α ∈ A₁sub) (hα' : α' ∈ A₁sub) :
    (d.ι α * d.t) • (d.W : Set G) = (d.ι α' * d.t) • (d.W : Set G) ↔
      cvec (mat α) = cvec (mat α') := by
  rw [h.coset_eq_iff ⟨α, hα, rfl⟩ ⟨α', hα', rfl⟩, ← map_inv, ← map_mul, Data.ZX₄,
    d.ι_mem_pull_iff, inv_mul_mem_ZX₄sub_iff hα hα']

theorem orb_mem_A₁sub (k : Fin 27) : orbSU k * b₀SU * (orbSU k)⁻¹ ∈ A₁sub :=
  conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub (orbSU_mem_CzSub k)) b₀SU_mem_A₁sub

omit [Finite G] in
theorem tW_eq : d.t • (d.W : Set G) = (d.ι 1 * d.t) • (d.W : Set G) := by
  rw [map_one, one_mul]

theorem coset_cases
    (h : d.Hyp) {a : G}
    (ha : a ∈ d.A₁) (ha2 : a * a = 1) :
    (a * d.t) • (d.W : Set G) = d.t • (d.W : Set G) ∨
      ∃ k, (a * d.t) • (d.W : Set G) = d.ptW k := by
  obtain ⟨α, hα, rfl⟩ := ha
  have hα2 : α * α = 1 := d.ι_injective (by rw [map_mul, ha2, map_one])
  have hiso := (mul_self_eq_one_iff hα).1 hα2
  by_cases h0 : cvec (mat α) = 0
  · left
    rw [tW_eq]
    exact (h.coset_ι_eq_iff hα (one_mem _)).2 (by rw [h0, mat_one, cvec_one])
  · right
    obtain ⟨k, hk⟩ := orbV_complete _ hiso h0
    exact ⟨k, (h.coset_ι_eq_iff hα (orb_mem_A₁sub k)).2 (by rw [cvec_orb, hk])⟩

theorem ptW_injective
    (h : d.Hyp) :
    Function.Injective d.ptW := fun k k' e =>
  orbV_injective (by
    rw [← cvec_orb, ← cvec_orb]
    exact (h.coset_ι_eq_iff (orb_mem_A₁sub k) (orb_mem_A₁sub k')).1 e)

theorem ptW_ne_tW
    (h : d.Hyp) (k : Fin 27) :
    d.ptW k ≠ d.t • (d.W : Set G) := fun e => orbV_ne_zero k (by
  rw [← cvec_orb, ← cvec_one, ← mat_one]
  rw [tW_eq] at e
  exact (h.coset_ι_eq_iff (orb_mem_A₁sub k) (one_mem _)).1 e)

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
