module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4V2

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD

theorem commutator_mem_ZX₄sub_of_A₁ {α β : SU52} (hα : α ∈ A₁sub) (hβ : β ∈ A₁sub) :
    β⁻¹ * α * β * α⁻¹ ∈ ZX₄sub := by
  have hc : cvec (mat (β⁻¹ * α * β * α⁻¹)) = 0 := by
    have hβi := inv_mem hβ
    have hαi := inv_mem hα
    rw [cvec_mul (mul_mem (mul_mem hβi hα) hβ) hαi, cvec_mul (mul_mem hβi hα) hβ,
      cvec_mul hβi hα]
    have e1 : cvec (mat β⁻¹) + cvec (mat β) = 0 := by
      rw [← cvec_mul hβi hβ, inv_mul_cancel, mat_one, cvec_one]
    have e2 : cvec (mat α) + cvec (mat α⁻¹) = 0 := by
      rw [← cvec_mul hα hαi, mul_inv_cancel, mat_one, cvec_one]
    calc cvec (mat β⁻¹) + cvec (mat α) + cvec (mat β) + cvec (mat α⁻¹) =
        (cvec (mat β⁻¹) + cvec (mat β)) + (cvec (mat α) + cvec (mat α⁻¹)) := by abel
      _ = 0 := by rw [e1, e2, add_zero]
  exact mem_ZX₄sub_of_cvec_eq_zero
    (mul_mem (mul_mem (mul_mem (inv_mem hβ) hα) hβ) (inv_mem hα)) hc

@[expose] def Data.UA₁ {G : Type} [Group G] (d : Data G) : Subgroup G where
  carrier := {x | x ∈ d.XW ∧ ∀ a ∈ d.A₁, a⁻¹ * x * a * x⁻¹ ∈ d.W ∧ a⁻¹ * x⁻¹ * a * x ∈ d.W}
  one_mem' := ⟨one_mem _, fun _ _ => ⟨by simp, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hxa⟩ ⟨hy, hya⟩
    refine ⟨mul_mem hx hy, fun a ha => ⟨?_, ?_⟩⟩
    · rw [show a⁻¹ * (x * y) * a * (x * y)⁻¹ =
        (a⁻¹ * x * a * x⁻¹) * (x * (a⁻¹ * y * a * y⁻¹) * x⁻¹) by group]
      exact mul_mem (hxa a ha).1
        ((mem_normalizer_iff.1 (Subgroup.mem_inf.1 hx).2 _).1 (hya a ha).1)
    · rw [show a⁻¹ * (x * y)⁻¹ * a * (x * y) =
        (a⁻¹ * y⁻¹ * a * y) * (y⁻¹ * (a⁻¹ * x⁻¹ * a * x) * y⁻¹⁻¹) by group]
      exact mul_mem (hya a ha).2
        ((mem_normalizer_iff.1 (inv_mem (Subgroup.mem_inf.1 hy).2) _).1 (hxa a ha).2)
  inv_mem' := by
    rintro x ⟨hx, hxa⟩
    refine ⟨inv_mem hx, fun a ha => ⟨?_, ?_⟩⟩
    · rw [inv_inv]
      exact (hxa a ha).2
    · rw [inv_inv]
      exact (hxa a ha).1

@[expose] def Data.D₁ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  d.UA₁ ⊓ centralizer (d.W : Set G)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem mem_UA₁_iff {x : G} : x ∈ d.UA₁ ↔
    x ∈ d.XW ∧ ∀ a ∈ d.A₁, a⁻¹ * x * a * x⁻¹ ∈ d.W ∧ a⁻¹ * x⁻¹ * a * x ∈ d.W :=
  Iff.rfl

omit [Finite G] in
theorem D₁_le_XW : d.D₁ ≤ d.XW := fun _ hu => (mem_UA₁_iff.1 (Subgroup.mem_inf.1 hu).1).1

theorem t_conj_mem_AW
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.AW) : d.t * x * d.t ∈ d.AW := by
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hx
  have hat : a * d.t = d.t * a := h.t_comm_of_mem_L (d.pull_le_L _ ha)
  rw [show d.t * (a * w) * d.t = (d.t * a) * (w * d.t) by group, ← hat,
    show a * d.t * (w * d.t) = a * (d.t * w * d.t) by group]
  exact mul_mem (mem_sup_left ha) (mem_sup_right (h.t_conj_mem_W hw))

theorem mem_AWT_iff_or
    (h : d.Hyp) {x : G} :
    x ∈ d.AWT ↔ x ∈ d.AW ∨ x * d.t ∈ d.AW :=
  mem_sup_zpowers_iff h.t_mul_t fun _ hk => h.t_conj_mem_AW hk

theorem exists_mem_W_not_mem_ZX₄
    (h : d.Hyp) : ∃ w ∈ d.W, w ∉ d.ZX₄ := by
  by_contra hne
  have hle : d.W ≤ d.ZX₄ := fun w hw => by
    by_contra hwz
    exact hne ⟨w, hw, hwz⟩
  have := Subgroup.card_le_of_le hle
  rw [h.sec4_9_W.1, Data.ZX₄, d.card_pull, card_ZX₄sub] at this
  omega

theorem not_comm_t_W
    (h : d.Hyp) :
    ¬ ∀ w ∈ d.W, w * d.t = d.t * w := fun hall => by
  obtain ⟨w, hw, hwz⟩ := h.exists_mem_W_not_mem_ZX₄
  exact hwz ((h.mem_ZX₄_iff_W w).2 ⟨hw, hall w hw⟩)

theorem t_not_mem_AW_of_elem
    (h : d.Hyp) :
    d.t ∉ d.AW := fun ht => h.not_comm_t_W fun _ hw => (h.AW_comm_W ht hw).symm

theorem mem_AW_of_mem_AWT_of_comm
    (h : d.Hyp) {x : G} (hx : x ∈ d.AWT)
    (hxW : ∀ w ∈ d.W, x * w = w * x) : x ∈ d.AW := by
  rcases (h.mem_AWT_iff_or).1 hx with hx | hx
  · exact hx
  · exfalso
    apply h.not_comm_t_W
    intro w hw
    have e1 := hxW w hw
    have e2 := h.AW_comm_W hx hw
    have e3 : x⁻¹ * w = w * x⁻¹ := by
      calc x⁻¹ * w = x⁻¹ * (w * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * w) * x⁻¹ := by rw [e1]
        _ = w * x⁻¹ := by group
    symm
    calc d.t * w = x⁻¹ * ((x * d.t) * w) := by group
      _ = x⁻¹ * (w * (x * d.t)) := by rw [e2]
      _ = (x⁻¹ * w) * x * d.t := by group
      _ = (w * x⁻¹) * x * d.t := by rw [e3]
      _ = w * d.t := by group

theorem conj_mem_AW_of_mem_XW_of_elem
    (h : d.Hyp) {x : G} (hx : x ∈ d.XW) {k : G}
    (hk : k ∈ d.AW) : x * k * x⁻¹ ∈ d.AW := by
  obtain ⟨hxA, hxW⟩ := Subgroup.mem_inf.1 hx
  refine h.mem_AW_of_mem_AWT_of_comm ((mem_normalizer_iff.1 hxA k).1 (mem_sup_left hk))
    fun w hw => ?_
  have hw' : x⁻¹ * w * x ∈ d.W := by
    have := (mem_normalizer_iff.1 (inv_mem hxW) w).1 hw
    rwa [inv_inv] at this
  have e := h.AW_comm_W hk hw'
  calc x * k * x⁻¹ * w = x * (k * (x⁻¹ * w * x)) * x⁻¹ := by group
    _ = x * ((x⁻¹ * w * x) * k) * x⁻¹ := by rw [e]
    _ = w * (x * k * x⁻¹) := by group

theorem conj_t_mul_t_mem_AW
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.XW) : x * d.t * x⁻¹ * d.t ∈ d.AW := by
  have hm : x * d.t * x⁻¹ ∈ d.AWT :=
    (mem_normalizer_iff.1 (Subgroup.mem_inf.1 hx).1 _).1 (mem_sup_right (mem_zpowers _))
  rcases (h.mem_AWT_iff_or).1 hm with hk | hk
  · exfalso
    apply h.t_not_mem_AW_of_elem
    have := h.conj_mem_AW_of_mem_XW_of_elem (inv_mem hx) hk
    rwa [show x⁻¹ * (x * d.t * x⁻¹) * x⁻¹⁻¹ = d.t by group] at this
  · exact hk

omit [Finite G] in
theorem W_le_XW : d.W ≤ d.XW := fun _ hw =>
  Subgroup.mem_inf.2 ⟨(d.AWT).le_normalizer (mem_sup_left (mem_sup_right hw)),
    (d.W).le_normalizer hw⟩

theorem A₁_le_XW
    (h : d.Hyp) :
    d.A₁ ≤ d.XW := fun a ha =>
  Subgroup.mem_inf.2 ⟨(d.AWT).le_normalizer (mem_sup_left (mem_sup_left ha)),
    mem_normalizer_fintype fun w hw => by
      rw [h.A₁_comm_W ha hw, mul_inv_cancel_right]
      exact hw⟩

theorem mem_normalizer_A₁_of_mem_XW_of_mem_H
    (h : d.Hyp) {x : G} (hx : x ∈ d.XW) (hxH : x ∈ d.H) :
    x ∈ normalizer (d.A₁ : Set G) := by
  refine mem_normalizer_fintype fun a ha => ?_
  have hL : x * a * x⁻¹ ∈ d.L :=
    (mem_normalizer_iff.1 (h.H_le_normalizer hxH) a).1 (d.pull_le_L _ ha)
  obtain ⟨a', ha', w, hw, e⟩ :=
    h.exists_eq_mul_of_mem_AW (h.conj_mem_AW_of_mem_XW_of_elem hx (mem_sup_left ha))
  have hwL : w ∈ d.L := by
    rw [show w = a'⁻¹ * (x * a * x⁻¹) by rw [← e]; group]
    exact mul_mem (inv_mem (d.pull_le_L _ ha')) hL
  have hwZ : w ∈ d.ZX₄ := by
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨hw, h.L_le_H hwL⟩
  rw [← e]
  exact mul_mem ha' (ZX₄_le_A₁ hwZ)

theorem mem_W_of_mem_UA₁_of_mem_AW
    (h : d.Hyp) {x k : G} (hx : x ∈ d.UA₁) (hk : k ∈ d.AW) :
    k⁻¹ * x * k * x⁻¹ ∈ d.W ∧ k⁻¹ * x⁻¹ * k * x ∈ d.W := by
  obtain ⟨hxX, hxa⟩ := mem_UA₁_iff.1 hx
  have hxW := (Subgroup.mem_inf.1 hxX).2
  obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW hk
  refine ⟨?_, ?_⟩
  · rw [show (a * w)⁻¹ * x * (a * w) * x⁻¹ =
      w⁻¹ * (a⁻¹ * x * a * x⁻¹) * (x * w * x⁻¹) by group]
    exact mul_mem (mul_mem (inv_mem hw) (hxa a ha).1) ((mem_normalizer_iff.1 hxW w).1 hw)
  · rw [show (a * w)⁻¹ * x⁻¹ * (a * w) * x =
      w⁻¹ * (a⁻¹ * x⁻¹ * a * x) * (x⁻¹ * w * x⁻¹⁻¹) by group]
    exact mul_mem (mul_mem (inv_mem hw) (hxa a ha).2)
      ((mem_normalizer_iff.1 (inv_mem hxW) w).1 hw)

theorem conj_mem_UA₁
    (h : d.Hyp) {g x : G}
    (hg : g ∈ d.XW) (hx : x ∈ d.UA₁) : g * x * g⁻¹ ∈ d.UA₁ := by
  have hgW := (Subgroup.mem_inf.1 hg).2
  refine mem_UA₁_iff.2 ⟨mul_mem (mul_mem hg (mem_UA₁_iff.1 hx).1) (inv_mem hg),
    fun a ha => ?_⟩
  have hk : g⁻¹ * a * g⁻¹⁻¹ ∈ d.AW := h.conj_mem_AW_of_mem_XW_of_elem (inv_mem hg) (mem_sup_left ha)
  rw [inv_inv] at hk
  obtain ⟨k1, k2⟩ := h.mem_W_of_mem_UA₁_of_mem_AW hx hk
  refine ⟨?_, ?_⟩
  · rw [show a⁻¹ * (g * x * g⁻¹) * a * (g * x * g⁻¹)⁻¹ =
      g * ((g⁻¹ * a * g)⁻¹ * x * (g⁻¹ * a * g) * x⁻¹) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgW _).1 k1
  · rw [show a⁻¹ * (g * x * g⁻¹)⁻¹ * a * (g * x * g⁻¹) =
      g * ((g⁻¹ * a * g)⁻¹ * x⁻¹ * (g⁻¹ * a * g) * x) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgW _).1 k2

theorem conj_mem_D₁
    (h : d.Hyp) {g u : G}
    (hg : g ∈ d.XW) (hu : u ∈ d.D₁) : g * u * g⁻¹ ∈ d.D₁ := by
  obtain ⟨huU, huC⟩ := Subgroup.mem_inf.1 hu
  have hgW := (Subgroup.mem_inf.1 hg).2
  refine Subgroup.mem_inf.2 ⟨h.conj_mem_UA₁ hg huU, mem_centralizer_iff.2 fun w hw => ?_⟩
  have hw' : g⁻¹ * w * g ∈ d.W := by
    have := (mem_normalizer_iff.1 (inv_mem hgW) w).1 hw
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 huC _ hw'
  calc w * (g * u * g⁻¹) = g * ((g⁻¹ * w * g) * u) * g⁻¹ := by group
    _ = g * (u * (g⁻¹ * w * g)) * g⁻¹ := by rw [e]
    _ = g * u * g⁻¹ * w := by group

theorem W_le_D₁
    (h : d.Hyp) :
    d.W ≤ d.D₁ := fun w hw => Subgroup.mem_inf.2
  ⟨mem_UA₁_iff.2 ⟨W_le_XW hw, fun a ha => ⟨by
      rw [mul_assoc a⁻¹ w a, ← h.A₁_comm_W ha hw, ← mul_assoc, inv_mul_cancel, one_mul,
        mul_inv_cancel]
      exact one_mem _, by
      rw [mul_assoc a⁻¹ w⁻¹ a, ← h.A₁_comm_W ha (inv_mem hw), ← mul_assoc, inv_mul_cancel,
        one_mul, inv_mul_cancel]
      exact one_mem _⟩⟩,
    mem_centralizer_iff.2 fun w' hw' => h.sec4_9_W.2.2.2.2.1 w' hw' w hw⟩

theorem A₁_le_D₁
    (h : d.Hyp) :
    d.A₁ ≤ d.D₁ := fun b hb => by
  refine Subgroup.mem_inf.2 ⟨mem_UA₁_iff.2 ⟨h.A₁_le_XW hb, fun a ha => ?_⟩,
    mem_centralizer_iff.2 fun w hw => (h.A₁_comm_W hb hw).symm⟩
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  refine ⟨h.ZX₄_le_W ⟨_, commutator_mem_ZX₄sub_of_A₁ hβ hα, ?_⟩,
    h.ZX₄_le_W ⟨_, commutator_mem_ZX₄sub_of_A₁ (inv_mem hβ) hα, ?_⟩⟩
  · simp only [map_mul, map_inv]
  · simp only [map_mul, map_inv, inv_inv]

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem mem_XW_of_comm_z_of_mem_H
    (h : d.Hyp) {k : G} (hkH : k ∈ d.H)
    (hkz : k * d.z = d.z * k) : k ∈ d.XW := by
  have hkW : k ∈ normalizer (d.W : Set G) := h.normalizer_withT_W_le_normalizer_W
    (h.normalizer_ZR_le_normalizer_withT_W (h.mem_normalizer_ZR_of_comm_z hkH hkz))
  refine Subgroup.mem_inf.2 ⟨mem_normalizer_fintype fun y hy => ?_, hkW⟩
  have hle : d.AWT ≤ d.AWT.comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro a ha
      exact mem_sup_left (mem_sup_left (h.conj_mem_A₁_of_comm_z hkH hkz ha))
    · intro w hw
      exact mem_sup_left (mem_sup_right ((mem_normalizer_iff.1 hkW w).1 hw))
    · rw [zpowers_le]
      change k * d.t * k⁻¹ ∈ d.AWT
      rw [mem_centralizer_singleton_iff.1 hkH, mul_inv_cancel_right]
      exact mem_sup_right (mem_zpowers _)
  exact hle hy

theorem NHA₁_le_XW
    (h : d.Hyp) :
    normalizer (d.A₁ : Set G) ⊓ d.H ≤ d.XW := fun _ hg =>
  h.mem_XW_of_comm_z_of_mem_H (Subgroup.mem_inf.1 hg).2
    (comm_z_of_mem_NHA₁ (Subgroup.mem_inf.1 hg).1)

theorem V₂_le_D₁
    (h : d.Hyp) :
    d.V₂ ≤ d.D₁ := fun v hv => by
  obtain ⟨hvY, hvW⟩ := (h.mem_V₂_iff).1 hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq hvY)
  have hcW : ∀ a ∈ d.A₁, v * a * v⁻¹ * a⁻¹ ∈ d.W := fun a ha => by
    have := inv_mem (hvW a (d.A₁_le_S ha))
    rwa [show (a * v * a⁻¹ * v⁻¹)⁻¹ = v * a * v⁻¹ * a⁻¹ by group] at this
  have hvC : v ∈ centralizer (d.W : Set G) :=
    mem_centralizer_iff.2 fun w hw => h.Y_comm (d.W_le_Y hw) hvY
  have hvN : v ∈ normalizer (d.W : Set G) := mem_normalizer_fintype fun w hw => by
    rw [← mem_centralizer_iff.1 hvC w hw, mul_inv_cancel_right]
    exact hw
  have hvA : v ∈ normalizer (d.AWT : Set G) := mem_normalizer_fintype fun y hy => by
    have hle : d.AWT ≤ d.AWT.comap (MulAut.conj v).toMonoidHom := by
      refine sup_le (sup_le (fun a ha => ?_) (fun w hw => ?_)) ?_
      · change v * a * v⁻¹ ∈ d.AWT
        rw [show v * a * v⁻¹ = (v * a * v⁻¹ * a⁻¹) * a by group]
        exact mem_sup_left (mul_mem (mem_sup_right (hcW a ha)) (mem_sup_left ha))
      · change v * w * v⁻¹ ∈ d.AWT
        rw [← mem_centralizer_iff.1 hvC w hw, mul_inv_cancel_right]
        exact mem_sup_left (mem_sup_right hw)
      · rw [zpowers_le]
        change v * d.t * v⁻¹ ∈ d.AWT
        have hz := Z₂_le_A₁ (h.crossed_mem_Z₂_of_mem_V₂ hv)
        rw [show v * d.t * v⁻¹ = (v⁻¹ * d.t * v * d.t) * d.t by
          rw [hvi, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
        exact mul_mem (mem_sup_left (mem_sup_left hz)) (mem_sup_right (mem_zpowers _))
    exact hle hy
  refine Subgroup.mem_inf.2 ⟨mem_UA₁_iff.2 ⟨Subgroup.mem_inf.2 ⟨hvA, hvN⟩, fun a ha => ?_⟩, hvC⟩
  have e : a⁻¹ * v * a * v⁻¹ = a⁻¹ * (v * a * v⁻¹ * a⁻¹) * a := by group
  have hk : a⁻¹ * (v * a * v⁻¹ * a⁻¹) * a = v * a * v⁻¹ * a⁻¹ := by
    rw [mul_assoc, ← h.A₁_comm_W ha (hcW a ha)]
    group
  refine ⟨by rw [e, hk]; exact hcW a ha, ?_⟩
  rw [hvi, show a⁻¹ * v * a * v = a⁻¹ * v * a * v⁻¹ by rw [hvi], e, hk]
  exact hcW a ha

theorem exists_D₁_conj_t
    (h : d.Hyp) {a : G}
    (ha : a ∈ d.A₁) : ∃ u ∈ d.D₁, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = a * w := by
  let T : Set SU52 :=
    {α | α ∈ A₁sub ∧ ∃ u ∈ d.D₁, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = d.ι α * w}
  have h1 : (1 : SU52) ∈ T := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by simp [h.t_mul_t]⟩
  have hmul : ∀ α ∈ T, ∀ β ∈ T, α * β ∈ T := by
    rintro α ⟨hα, u₁, hu₁, w₁, hw₁, e₁⟩ β ⟨hβ, u₂, hu₂, w₂, hw₂, e₂⟩
    have hu₂U := (Subgroup.mem_inf.1 hu₂).1
    have hu₂N := (Subgroup.mem_inf.1 (mem_UA₁_iff.1 hu₂U).1).2
    obtain ⟨c, hc, hce⟩ : ∃ c ∈ d.W, u₂ * d.ι α * u₂⁻¹ = d.ι α * c :=
      ⟨_, (h.mem_W_of_mem_UA₁_of_mem_AW hu₂U
        (mem_sup_left (⟨α, hα, rfl⟩ : d.ι α ∈ d.A₁))).1, by group⟩
    obtain ⟨w₃, hw₃, hw₃e⟩ : ∃ w₃ ∈ d.W, u₂ * w₁ * u₂⁻¹ = w₃ :=
      ⟨_, (mem_normalizer_iff.1 hu₂N w₁).1 hw₁, rfl⟩
    have e₁' : u₁ * d.t * u₁⁻¹ = d.ι α * w₁ * d.t := by
      rw [← e₁, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
    have hcomm : d.ι β * (c * w₃) = (c * w₃) * d.ι β :=
      h.A₁_comm_W ⟨β, hβ, rfl⟩ (mul_mem hc hw₃)
    refine ⟨mul_mem hα hβ, u₂ * u₁, mul_mem hu₂ hu₁, c * w₃ * w₂,
      mul_mem (mul_mem hc hw₃) hw₂, ?_⟩
    calc u₂ * u₁ * d.t * (u₂ * u₁)⁻¹ * d.t = u₂ * (u₁ * d.t * u₁⁻¹) * u₂⁻¹ * d.t := by group
      _ = u₂ * (d.ι α * w₁ * d.t) * u₂⁻¹ * d.t := by rw [e₁']
      _ = (u₂ * d.ι α * u₂⁻¹) * (u₂ * w₁ * u₂⁻¹) * (u₂ * d.t * u₂⁻¹ * d.t) := by group
      _ = d.ι α * (c * w₃ * d.ι β) * w₂ := by rw [hce, hw₃e, e₂]; group
      _ = d.ι α * (d.ι β * (c * w₃)) * w₂ := by rw [← hcomm]
      _ = d.ι (α * β) * (c * w₃ * w₂) := by rw [map_mul]; group
  have horb : ∀ k, orbSU k * b₀SU * (orbSU k)⁻¹ ∈ T := fun k => by
    refine ⟨orb_mem_A₁sub k, ?_⟩
    obtain ⟨v, hv, hvt⟩ := h.exists_V₂_crossed_eq
      (⟨b₀SU, Fsub_inf_A₁sub ▸ Subgroup.mem_inf.2 ⟨b₀SU_mem_Fsub, b₀SU_mem_A₁sub⟩, rfl⟩ :
        d.ι b₀SU ∈ d.Z₂)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq (h.V₂_le_Y hv))
    have hgH : d.ι (orbSU k) ∈ d.H := h.L_le_H (d.ι_mem _)
    have hgX : d.ι (orbSU k) ∈ d.XW := h.mem_XW_of_comm_z_of_mem_H hgH (by
      rw [Data.z, ← map_mul, ← map_mul, comm_of_mem_CzSub (orbSU_mem_CzSub k)])
    refine ⟨d.ι (orbSU k) * v * (d.ι (orbSU k))⁻¹, h.conj_mem_D₁ hgX (h.V₂_le_D₁ hv), 1,
      one_mem _, ?_⟩
    rw [map_mul, map_mul, map_inv, mul_one]
    generalize d.ι (orbSU k) = g at hgH ⊢
    have hgt : g * d.t = d.t * g := mem_centralizer_singleton_iff.1 hgH
    have hgt' : g⁻¹ * d.t = d.t * g⁻¹ := by
      calc g⁻¹ * d.t = g⁻¹ * (d.t * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * d.t) * g⁻¹ := by rw [hgt]
        _ = d.t * g⁻¹ := by group
    calc g * v * g⁻¹ * d.t * (g * v * g⁻¹)⁻¹ * d.t =
        g * v * (g⁻¹ * d.t) * g * v⁻¹ * g⁻¹ * d.t := by group
      _ = g * v * (d.t * g⁻¹) * g * v⁻¹ * g⁻¹ * d.t := by rw [hgt']
      _ = g * (v * d.t * v⁻¹) * (g⁻¹ * d.t) := by group
      _ = g * (v * d.t * v⁻¹) * (d.t * g⁻¹) := by rw [hgt']
      _ = g * (v⁻¹ * d.t * v * d.t) * g⁻¹ := by rw [hvi]; group
      _ = g * d.ι b₀SU * g⁻¹ := by rw [hvt]
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨α', ⟨hα'A, u, hu, w, hw, e⟩, hcv⟩ :=
    exists_cvec_eq_of_orb (fun _ hβ => hβ.1) h1 hmul horb (cvec (mat α))
  have hz := (inv_mul_mem_ZX₄sub_iff hα'A hα).2 hcv
  refine ⟨u, hu, (d.ι (α'⁻¹ * α))⁻¹ * w, mul_mem (inv_mem (h.ZX₄_le_W ⟨_, hz, rfl⟩)) hw, ?_⟩
  rw [e, map_mul, map_inv]
  group

theorem mem_NHA₁W_of_conj_t
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.XW) (hxt : x * d.t * x⁻¹ * d.t ∈ d.W) :
    x ∈ (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.W := by
  obtain ⟨w, hw, hwe⟩ : ∃ w ∈ d.W, x * d.t * x⁻¹ * d.t = w := ⟨_, hxt, rfl⟩
  have hxtx : x * d.t * x⁻¹ = w * d.t := by rw [← hwe, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  have hsq : w * d.t * (w * d.t) = 1 := by
    rw [← hxtx, show x * d.t * x⁻¹ * (x * d.t * x⁻¹) = x * (d.t * d.t) * x⁻¹ by group,
      h.t_mul_t, mul_one, mul_inv_cancel]
  have hwZ : w ∈ d.ZX₄ := by
    refine (h.mem_ZX₄_iff_W w).2 ⟨hw, ?_⟩
    calc w * d.t = (w * d.t * (w * d.t)) * (d.t⁻¹ * w⁻¹) := by group
      _ = d.t⁻¹ * w⁻¹ := by rw [hsq, one_mul]
      _ = d.t * w := by rw [h.t_inv, inv_eq_of_mul_eq_one_right (h.W_sq hw)]
  obtain ⟨w', hw', hw't⟩ := (h.sec4_9_W).2.2.1 w hwZ
  have hH : w' * x ∈ d.H := mem_centralizer_singleton_iff.2 (by
    calc w' * x * d.t = w' * (x * d.t * x⁻¹) * x := by group
      _ = w' * (w'⁻¹ * d.t * w') * x := by rw [hxtx, ← hw't]
      _ = d.t * (w' * x) := by group)
  have hX : w' * x ∈ d.XW := mul_mem (W_le_XW hw') hx
  have := mul_mem (mem_sup_right (inv_mem hw') : w'⁻¹ ∈ (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.W)
    (mem_sup_left (Subgroup.mem_inf.2 ⟨h.mem_normalizer_A₁_of_mem_XW_of_mem_H hX hH, hH⟩))
  rwa [inv_mul_cancel_left] at this

theorem XW_eq_sup
    (h : d.Hyp) :
    d.XW = (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.D₁ := by
  refine le_antisymm (fun x hx => ?_) (sup_le h.NHA₁_le_XW D₁_le_XW)
  obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW (h.conj_t_mul_t_mem_AW hx)
  obtain ⟨u, hu, w', hw', e'⟩ := h.exists_D₁_conj_t ha
  have huN : u⁻¹ ∈ normalizer (d.W : Set G) := inv_mem (Subgroup.mem_inf.1 (D₁_le_XW hu)).2
  have hw₁ : u⁻¹ * (d.t * (w'⁻¹ * w) * d.t) * u⁻¹⁻¹ ∈ d.W :=
    (mem_normalizer_iff.1 huN _).1 (h.t_conj_mem_W (mul_mem (inv_mem hw') hw))
  have ex : x * d.t * x⁻¹ = a * w * d.t := by rw [e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  have eu : u * d.t * u⁻¹ = a * w' * d.t := by
    rw [← e', mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  have hyt : u⁻¹ * x * d.t * (u⁻¹ * x)⁻¹ * d.t ∈ d.W := by
    have key : u⁻¹ * x * d.t * (u⁻¹ * x)⁻¹ * d.t =
        d.t * (u⁻¹ * (d.t * (w'⁻¹ * w) * d.t) * u⁻¹⁻¹) * d.t := by
      calc u⁻¹ * x * d.t * (u⁻¹ * x)⁻¹ * d.t = u⁻¹ * (x * d.t * x⁻¹) * u * d.t := by group
        _ = u⁻¹ * ((a * w' * d.t) * (d.t * (w'⁻¹ * w) * d.t)) * u * d.t := by
            rw [ex, show (a * w' * d.t) * (d.t * (w'⁻¹ * w) * d.t) =
              a * w' * (d.t * d.t) * (w'⁻¹ * w) * d.t by group, h.t_mul_t]
            group
        _ = u⁻¹ * ((u * d.t * u⁻¹) * (d.t * (w'⁻¹ * w) * d.t)) * u * d.t := by rw [eu]
        _ = d.t * (u⁻¹ * (d.t * (w'⁻¹ * w) * d.t) * u⁻¹⁻¹) * d.t := by group
    rw [key]
    exact h.t_conj_mem_W hw₁
  have hy := h.mem_NHA₁W_of_conj_t (mul_mem (inv_mem (D₁_le_XW hu)) hx) hyt
  have := mul_mem (mem_sup_right hu : u ∈ (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.D₁)
    ((sup_le_sup_left h.W_le_D₁ _) hy)
  rwa [mul_inv_cancel_left] at this

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
