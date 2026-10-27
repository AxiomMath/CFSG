module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4WNorm
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckZ2

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD

@[expose] def centModSub {G : Type*} [Group G] (Z : Subgroup G) (g : G) : Subgroup G where
  carrier := {s | s ∈ normalizer (Z : Set G) ∧ s * g * s⁻¹ * g⁻¹ ∈ Z}
  one_mem' := ⟨one_mem _, by rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show a * b * g * (a * b)⁻¹ * g⁻¹ =
      a * (b * g * b⁻¹ * g⁻¹) * a⁻¹ * (a * g * a⁻¹ * g⁻¹) by group]
    exact mul_mem ((mem_normalizer_iff.1 ha _).1 hb') ha'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [show a⁻¹ * g * a⁻¹⁻¹ * g⁻¹ = a⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * a⁻¹⁻¹ by group]
    exact (mem_normalizer_iff.1 (inv_mem ha) _).1 (inv_mem ha')

theorem mem_centModSub {G : Type*} [Group G] {Z : Subgroup G} {g s : G} :
    s ∈ centModSub Z g ↔ s ∈ normalizer (Z : Set G) ∧ s * g * s⁻¹ * g⁻¹ ∈ Z :=
  Iff.rfl

@[expose] def Data.Z₂ {G : Type} [Group G] (d : Data G) : Subgroup G := d.pull Z₂sub

@[expose] def Data.V₂ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  closure {y | y ∈ d.Y ∧ ∀ s ∈ d.S, s * y * s⁻¹ * y⁻¹ ∈ d.W}

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem Z₂_eq : d.Z₂ = d.F ⊓ d.A₁ := by
  rw [Data.Z₂, ← Fsub_inf_A₁sub, d.pull_inf]
  rfl

omit [Finite G] in
theorem Z₂_le_F : d.Z₂ ≤ d.F := d.pull_mono Z₂sub_le_Fsub

omit [Finite G] in
theorem Z₂_le_A₁ : d.Z₂ ≤ d.A₁ := d.pull_mono Z₂sub_le_A₁sub

omit [Finite G] in
theorem card_Z₂ : Nat.card d.Z₂ = 8 := by rw [Data.Z₂, d.card_pull, card_Z₂sub]

omit [Finite G] in
theorem Z₂_eq_sup : d.Z₂ = d.X₃ ⊔ d.ZX₄ := by
  rw [Data.Z₂, Z₂sub, d.pull_sup]
  rfl

omit [Finite G] in
theorem ZX₄_comm_S {z s : G} (hz : z ∈ d.ZX₄) (hs : s ∈ d.S) : s * z = z * s := by
  obtain ⟨ζ, hζ, rfl⟩ := hz
  obtain ⟨σ, hσ, rfl⟩ := hs
  rw [← map_mul, ← map_mul, ZX₄sub_comm hζ hσ]

theorem S_le_normalizer_ZX₄ : d.S ≤ normalizer (d.ZX₄ : Set G) := fun s hs =>
  mem_normalizer_fintype fun z hz => by
    rw [ZX₄_comm_S hz hs, mul_inv_cancel_right]
    exact hz

theorem Z₂_comm_S {g s : G} (hg : g ∈ d.Z₂) (hs : s ∈ d.S) : s * g * s⁻¹ * g⁻¹ ∈ d.ZX₄ := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  have hle : d.S ≤ centModSub d.ZX₄ (d.ι γ) := by
    rw [d.S_eq_sup]
    refine sup_le (fun a ha => mem_centModSub.2 ⟨S_le_normalizer_ZX₄ (d.A₂_le_S ha), ?_⟩) ?_
    · obtain ⟨α, hα, rfl⟩ := ha
      rw [← map_mul, Fsub_comm_A₂ hα (Z₂sub_le_Fsub hγ), map_mul, mul_inv_cancel_right,
        mul_inv_cancel]
      exact one_mem _
    · rintro _ ⟨ξ, hξ, rfl⟩
      obtain ⟨c, hc⟩ := mem_X₂sub.1 hξ
      obtain rfl : ξ = x₂SU c := ext_mat (by rw [hc, mat_x₂SU])
      refine mem_centModSub.2 ⟨S_le_normalizer_ZX₄ (d.ι_x₂SU_mem_S c), ?_⟩
      have := inv_mem (Z₂sub_comm_x₂ hγ c)
      rw [show (γ * x₂SU c * γ⁻¹ * (x₂SU c)⁻¹)⁻¹ = x₂SU c * γ * (x₂SU c)⁻¹ * γ⁻¹ by group]
        at this
      exact ⟨_, this, by simp only [map_mul, map_inv]⟩
  exact (mem_centModSub.1 (hle hs)).2

theorem S_le_normalizer_Y
    (h : d.Hyp) :
    d.S ≤ normalizer (d.Y : Set G) := by
  rw [d.S_eq_sup]
  refine sup_le (fun a ha => mem_normalizer_fintype fun y hy => ?_) fun x hx => ?_
  · rw [h.Y_comm_A₂ hy ha, mul_inv_cancel_right]
    exact hy
  · have := (h.le_normalizer_E₂).1 (X₂_le_Lev hx)
    rwa [← h.Y_eq_E₂] at this

theorem S_le_normalizer_W
    (h : d.Hyp) :
    d.S ≤ normalizer (d.W : Set G) := fun s hs => mem_normalizer_fintype fun w hw => by
  obtain ⟨hwY, hwC⟩ := Subgroup.mem_inf.1 hw
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (h.S_le_normalizer_Y hs) w).1 hwY,
    mem_centralizer_iff.2 fun s' hs' => ?_⟩
  have e := mem_centralizer_iff.1 hwC (s⁻¹ * s' * s) (mul_mem (mul_mem (inv_mem hs) hs') hs)
  calc s' * (s * w * s⁻¹) = s * ((s⁻¹ * s' * s) * w) * s⁻¹ := by group
    _ = s * (w * (s⁻¹ * s' * s)) * s⁻¹ := by rw [e]
    _ = s * w * s⁻¹ * s' := by group

theorem mem_V₂_iff
    (h : d.Hyp) {y : G} :
    y ∈ d.V₂ ↔ y ∈ d.Y ∧ ∀ s ∈ d.S, s * y * s⁻¹ * y⁻¹ ∈ d.W := by
  refine ⟨fun hy => ?_, fun hy => subset_closure hy⟩
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one =>
    exact ⟨one_mem _, fun s _ => by
      rw [mul_one, mul_inv_cancel, inv_one, mul_one]
      exact one_mem _⟩
  | mul y₁ y₂ _ _ h₁ h₂ =>
    obtain ⟨hY₁, hW₁⟩ := h₁
    obtain ⟨hY₂, hW₂⟩ := h₂
    refine ⟨mul_mem hY₁ hY₂, fun s hs => ?_⟩
    have e1 : (s * y₂ * s⁻¹ * y₂⁻¹) * y₁⁻¹ = y₁⁻¹ * (s * y₂ * s⁻¹ * y₂⁻¹) :=
      h.Y_comm (d.W_le_Y (hW₂ s hs)) (inv_mem hY₁)
    rw [show s * (y₁ * y₂) * s⁻¹ * (y₁ * y₂)⁻¹ =
        (s * y₁ * s⁻¹) * ((s * y₂ * s⁻¹ * y₂⁻¹) * y₁⁻¹) by group, e1,
      show s * y₁ * s⁻¹ * (y₁⁻¹ * (s * y₂ * s⁻¹ * y₂⁻¹)) =
        (s * y₁ * s⁻¹ * y₁⁻¹) * (s * y₂ * s⁻¹ * y₂⁻¹) by group]
    exact mul_mem (hW₁ s hs) (hW₂ s hs)
  | inv y _ h₁ =>
    obtain ⟨hY, hW⟩ := h₁
    refine ⟨inv_mem hY, fun s hs => ?_⟩
    have e1 : y * (s * y * s⁻¹ * y⁻¹)⁻¹ = (s * y * s⁻¹ * y⁻¹)⁻¹ * y :=
      h.Y_comm hY (inv_mem (d.W_le_Y (hW s hs)))
    rw [show s * y⁻¹ * s⁻¹ * y⁻¹⁻¹ = y⁻¹ * ((s * y * s⁻¹ * y⁻¹)⁻¹ * y) by group, ← e1,
      show y⁻¹ * (y * (s * y * s⁻¹ * y⁻¹)⁻¹) = (s * y * s⁻¹ * y⁻¹)⁻¹ by group]
    exact inv_mem (hW s hs)

theorem V₂_le_Y
    (h : d.Hyp) :
    d.V₂ ≤ d.Y := fun _ hv => ((h.mem_V₂_iff).1 hv).1

theorem mem_V₂_of_x₂
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.Y) (h1 : d.ι (x₂SU 1) * y * (d.ι (x₂SU 1))⁻¹ * y⁻¹ ∈ d.W)
    (hω : d.ι (x₂SU F4.ω) * y * (d.ι (x₂SU F4.ω))⁻¹ * y⁻¹ ∈ d.W) : y ∈ d.V₂ := by
  refine (h.mem_V₂_iff).2 ⟨hy, fun s hs => ?_⟩
  have hle : d.S ≤ centModSub d.W y := by
    rw [d.S_eq_sup]
    refine sup_le (fun a ha => mem_centModSub.2 ⟨h.S_le_normalizer_W (d.A₂_le_S ha), ?_⟩) ?_
    · rw [h.Y_comm_A₂ hy ha, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    · rw [Data.X₂, Data.pull]
      refine (map_mono X₂sub_le_closure).trans ?_
      rw [MonoidHom.map_closure, Set.image_pair, closure_le]
      rintro _ (rfl | rfl)
      · exact mem_centModSub.2 ⟨h.S_le_normalizer_W (d.ι_x₂SU_mem_S 1), h1⟩
      · exact mem_centModSub.2 ⟨h.S_le_normalizer_W (d.ι_x₂SU_mem_S F4.ω), hω⟩
  exact (mem_centModSub.1 (hle hs)).2

theorem W_le_V₂
    (h : d.Hyp) :
    d.W ≤ d.V₂ := fun w hw => (h.mem_V₂_iff).2 ⟨d.W_le_Y hw, fun s hs => by
  rw [mem_centralizer_iff.1 (d.W_le_centralizer hw) s hs, mul_inv_cancel_right,
    mul_inv_cancel]
  exact one_mem _⟩

theorem Z₂_le_V₂
    (h : d.Hyp) :
    d.Z₂ ≤ d.V₂ := fun _ hg => (h.mem_V₂_iff).2 ⟨h.F_le_Y (Z₂_le_F hg), fun _ hs =>
  (h.ZX₄_le_W) (Z₂_comm_S hg hs)⟩

theorem Lev_conj_mem_Y
    (h : d.Hyp) {l y : G}
    (hl : l ∈ d.Lev) (hy : y ∈ d.Y) : l * y * l⁻¹ ∈ d.Y := by
  rw [h.Y_eq_E₂] at hy ⊢
  exact (mem_normalizer_iff.1 ((h.le_normalizer_E₂).1 hl) y).1 hy

theorem crossed_mul_conj
    (h : d.Hyp) {y l : G}
    (hy : y ∈ d.Y) (hl : l ∈ d.Lev) :
    (y * (l * y * l⁻¹))⁻¹ * d.t * (y * (l * y * l⁻¹)) * d.t =
      (y⁻¹ * d.t * y * d.t) * (l * (y⁻¹ * d.t * y * d.t) * l⁻¹) := by
  have hU : ∀ {x}, x ∈ d.Y → x ∈ d.U := fun hx => h.E₂_le_U (h.Y_eq_E₂ ▸ hx)
  rw [crossed_mul h.t_mul_t (h.U_comm_F (hU (h.Lev_conj_mem_Y hl hy))
    (h.U_crossed_mem_F (hU hy))).symm, crossed_conj (h.Lev_comm_t hl)]

omit [Finite G] in
theorem ι_x₂SU_mem_Lev (c : F4) : d.ι (x₂SU c) ∈ d.Lev :=
  X₂_le_Lev ⟨x₂SU c, x₂SU_mem c, rfl⟩

omit [Finite G] in
theorem ι_x₂SU_mul_self (c : F4) : d.ι (x₂SU c) * d.ι (x₂SU c) = 1 := by
  rw [← map_mul, x₂SU_mul, CharTwo.add_self_eq_zero,
    show x₂SU 0 = 1 from ext_mat (by rw [mat_x₂SU, x₂Mat_zero, mat_one]), map_one]

theorem mem_Z₂sub_of_comm {ξ : SU52} (hξ : ξ ∈ Fsub)
    (key : ∀ c : F4, x₂SU c * ξ * (x₂SU c)⁻¹ * ξ⁻¹ ∈ ZX₄sub) : ξ ∈ Z₂sub := by
  have conv : ∀ c, ξ * x₂SU c * ξ⁻¹ * (x₂SU c)⁻¹ ∈ ZX₄sub := fun c => by
    rw [show ξ * x₂SU c * ξ⁻¹ * (x₂SU c)⁻¹ = (x₂SU c * ξ * (x₂SU c)⁻¹ * ξ⁻¹)⁻¹ by group]
    exact inv_mem (key c)
  rw [← Fsub_inf_A₁sub]
  exact Subgroup.mem_inf.2 ⟨hξ, mem_A₁sub_of_comm_x₂ hξ (conv 1) (conv F4.ω)⟩

theorem V₂_inf_H
    (h : d.Hyp) :
    d.V₂ ⊓ d.H = d.Z₂ := by
  refine le_antisymm (fun v hv => ?_)
    (le_inf h.Z₂_le_V₂ fun g hg => h.withT_F_le_H (mem_sup_left (Z₂_le_F hg)))
  obtain ⟨hvV, hvH⟩ := Subgroup.mem_inf.1 hv
  obtain ⟨hvY, hvW⟩ := (h.mem_V₂_iff).1 hvV
  obtain ⟨ξ, hξ, rfl⟩ := (h.mem_F_iff_Y v).2 ⟨hvY, mem_centralizer_singleton_iff.1 hvH⟩
  refine ⟨ξ, mem_Z₂sub_of_comm hξ fun c => ?_, rfl⟩
  have hxH : d.ι (x₂SU c) ∈ d.H := h.L_le_H (d.ι_mem _)
  have hz : d.ι (x₂SU c) * d.ι ξ * (d.ι (x₂SU c))⁻¹ * (d.ι ξ)⁻¹ ∈ d.ZX₄ := by
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨hvW _ (d.ι_x₂SU_mem_S c),
      mul_mem (mul_mem (mul_mem hxH hvH) (inv_mem hxH)) (inv_mem hvH)⟩
  exact (d.ι_mem_pull_iff (M := ZX₄sub)).1 (by simp only [map_mul, map_inv]; exact hz)

theorem crossed_mem_ZX₄_iff
    (h : d.Hyp) {v : G}
    (hv : v ∈ d.V₂) : v⁻¹ * d.t * v * d.t ∈ d.ZX₄ ↔ v ∈ d.Z₂ ⊔ d.W := by
  constructor
  · intro hz
    obtain ⟨w, hw, hwt⟩ := (h.sec4_9_W).2.2.1 _ hz
    have e1 : w⁻¹ * d.t * w = v⁻¹ * d.t * v := by
      rw [hwt, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
    have hH : v * w⁻¹ ∈ d.H := mem_centralizer_singleton_iff.2 (by
      calc v * w⁻¹ * d.t = v * (w⁻¹ * d.t * w) * w⁻¹ := by group
        _ = v * (v⁻¹ * d.t * v) * w⁻¹ := by rw [e1]
        _ = d.t * (v * w⁻¹) := by group)
    have hZ : v * w⁻¹ ∈ d.Z₂ := by
      rw [← h.V₂_inf_H]
      exact Subgroup.mem_inf.2 ⟨mul_mem hv (inv_mem (h.W_le_V₂ hw)), hH⟩
    have := mul_mem (mem_sup_left hZ : v * w⁻¹ ∈ d.Z₂ ⊔ d.W) (mem_sup_right hw)
    rwa [inv_mul_cancel_right] at this
  · intro hvZW
    obtain ⟨g, hg, w, hw, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun g hg w hw => h.Y_comm (h.F_le_Y (Z₂_le_F hg)) (d.W_le_Y hw)) hvZW
    have hgt : g * d.t = d.t * g := h.t_comm_F (Z₂_le_F hg)
    rw [show (g * w)⁻¹ * d.t * (g * w) * d.t = w⁻¹ * (g⁻¹ * (d.t * g)) * w * d.t by group,
      ← hgt, show w⁻¹ * (g⁻¹ * (g * d.t)) * w * d.t = w⁻¹ * d.t * w * d.t by group]
    exact h.W_crossed_mem_ZX₄ hw

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem conj_mul_inv_mem_W_aux
    (h : d.Hyp)
    {A B C y : G} (hy : y ∈ d.Y) (hA : ∀ y ∈ d.Y, A * y * A⁻¹ ∈ d.Y)
    (hB : ∀ y ∈ d.Y, B * y * B⁻¹ ∈ d.Y) (hAA : A * A = 1) (hBB : B * B = 1)
    (hAB : A * B = C) (hBA : B * A = C)
    (hW : ∀ n ∈ d.Y, A * n = n * A → B * n = n * B → n ∈ d.W) :
    A * (y * (A * y * A⁻¹)) * A⁻¹ * (y * (A * y * A⁻¹))⁻¹ ∈ d.W ∧
      B * (y * (A * y * A⁻¹)) * B⁻¹ * (y * (A * y * A⁻¹))⁻¹ ∈ d.W := by
  have hYc : ∀ a ∈ d.Y, ∀ b ∈ d.Y, a * b = b * a := fun a ha b hb => h.Y_comm ha hb
  obtain ⟨hNY, hNA, hNB⟩ := klein_norm_comm hYc hy hA hB hAA hBB hAB hBA
  obtain ⟨hvA, hvB, -, -⟩ := klein_v_facts hYc hy hA hB hAA hBA
  have hvY : y * (A * y * A⁻¹) ∈ d.Y := mul_mem hy (hA y hy)
  have hNW := hW _ hNY hNA hNB
  generalize y * (A * y * A⁻¹) * (B * y * B⁻¹) * (C * y * C⁻¹) = N at hNW hvB
  generalize y * (A * y * A⁻¹) = v at hvA hvB hvY ⊢
  have hv2 : v * v = 1 := h.Y_sq hvY
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  refine ⟨?_, ?_⟩
  · rw [hvA, mul_inv_cancel]
    exact one_mem _
  · have hNv : N * v = v * N := hYc _ (d.W_le_Y hNW) _ hvY
    rw [hvB, hvi, ← hNv, mul_assoc, hv2, mul_one]
    exact hNW

theorem mul_conj_x₂_one_mem_V₂
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.Y) : y * (d.ι (x₂SU 1) * y * (d.ι (x₂SU 1))⁻¹) ∈ d.V₂ := by
  obtain ⟨h1, hω⟩ := h.conj_mul_inv_mem_W_aux (C := d.ι (x₂SU (F4.ω + 1))) hy
    (fun y hy => h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev 1) hy)
    (fun y hy => h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev F4.ω) hy) (ι_x₂SU_mul_self 1)
    (ι_x₂SU_mul_self F4.ω) (by rw [← map_mul, x₂SU_mul, add_comm])
    (by rw [← map_mul, x₂SU_mul]) fun n hn hnA hnB => h.mem_W_of_comm hn hnA.symm hnB.symm
  exact h.mem_V₂_of_x₂ (mul_mem hy (h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev 1) hy)) h1 hω

theorem mul_conj_x₂_ω_mem_V₂
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.Y) : y * (d.ι (x₂SU F4.ω) * y * (d.ι (x₂SU F4.ω))⁻¹) ∈ d.V₂ := by
  obtain ⟨hω, h1⟩ := h.conj_mul_inv_mem_W_aux (C := d.ι (x₂SU (F4.ω + 1))) hy
    (fun y hy => h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev F4.ω) hy)
    (fun y hy => h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev 1) hy) (ι_x₂SU_mul_self F4.ω)
    (ι_x₂SU_mul_self 1) (by rw [← map_mul, x₂SU_mul])
    (by rw [← map_mul, x₂SU_mul, add_comm]) fun n hn hnA hnB =>
      h.mem_W_of_comm hn hnB.symm hnA.symm
  exact h.mem_V₂_of_x₂ (mul_mem hy (h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev F4.ω) hy)) h1 hω

theorem crossed_mem_Z₂_of_mem_V₂
    (h : d.Hyp) {v : G} (hv : v ∈ d.V₂) :
    v⁻¹ * d.t * v * d.t ∈ d.Z₂ := by
  obtain ⟨hvY, hvW⟩ := (h.mem_V₂_iff).1 hv
  have hU : ∀ {x}, x ∈ d.Y → x ∈ d.U := fun hx => h.E₂_le_U (h.Y_eq_E₂ ▸ hx)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq hvY)
  obtain ⟨ξ, hξ, hξe⟩ := h.U_crossed_mem_F (hU hvY)
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right (Fsub_sq hξ)
  refine ⟨ξ, mem_Z₂sub_of_comm hξ fun c => ?_, hξe⟩
  have hxY : d.ι (x₂SU c) * v * (d.ι (x₂SU c))⁻¹ ∈ d.Y :=
    h.Lev_conj_mem_Y (ι_x₂SU_mem_Lev c) hvY
  have hz := h.W_crossed_mem_ZX₄ (hvW _ (d.ι_x₂SU_mem_S c))
  rw [hvi, crossed_mul h.t_mul_t (h.U_comm_F (hU hvY) (h.U_crossed_mem_F (hU hxY))).symm,
    crossed_conj (h.Lev_comm_t (ι_x₂SU_mem_Lev c)), ← hξe] at hz
  rw [hξi]
  exact (d.ι_mem_pull_iff (M := ZX₄sub)).1 (by simp only [map_mul, map_inv]; exact hz)

theorem exists_V₂_crossed_eq
    (h : d.Hyp) {g : G}
    (hg : g ∈ d.Z₂) : ∃ v ∈ d.V₂, v⁻¹ * d.t * v * d.t = g := by
  obtain ⟨γ, hγ, rfl⟩ := hg
  obtain ⟨f₁, hf₁, f₂, hf₂, e⟩ := exists_Fsub_of_mem_Z₂sub hγ
  obtain ⟨y₁, hy₁, e₁⟩ := h.exists_E₂_crossed_eq (⟨f₁, hf₁, rfl⟩ : d.ι f₁ ∈ d.F)
  obtain ⟨y₂, hy₂, e₂⟩ := h.exists_E₂_crossed_eq (⟨f₂, hf₂, rfl⟩ : d.ι f₂ ∈ d.F)
  rw [← h.Y_eq_E₂] at hy₁ hy₂
  have hU : ∀ {x}, x ∈ d.Y → x ∈ d.U := fun hx => h.E₂_le_U (h.Y_eq_E₂ ▸ hx)
  have hv₁ := h.mul_conj_x₂_one_mem_V₂ hy₁
  have hv₂ := h.mul_conj_x₂_ω_mem_V₂ hy₂
  refine ⟨_, mul_mem hv₁ hv₂, ?_⟩
  rw [crossed_mul h.t_mul_t (h.U_comm_F (hU (h.V₂_le_Y hv₂))
      (h.U_crossed_mem_F (hU (h.V₂_le_Y hv₁)))).symm,
    h.crossed_mul_conj hy₁ (ι_x₂SU_mem_Lev 1), h.crossed_mul_conj hy₂ (ι_x₂SU_mem_Lev F4.ω),
    e₁, e₂, e]
  simp only [map_mul, map_inv]

theorem card_V₂
    (h : d.Hyp) :
    Nat.card d.V₂ = 2 ^ 6 := by
  have hYB : d.V₂ ≤ centralizer (d.Z₂ : Set G) := fun v hv => mem_centralizer_iff.2 fun g hg =>
    h.Y_comm (h.F_le_Y (Z₂_le_F hg)) (h.V₂_le_Y hv)
  rw [card_eq_of_crossed_onto h.t_mul_t hYB (fun v hv => h.crossed_mem_Z₂_of_mem_V₂ hv)
    fun g hg => h.exists_V₂_crossed_eq hg]
  have e : d.V₂ ⊓ centralizer ({d.t} : Set G) = d.Z₂ := h.V₂_inf_H
  rw [e, card_Z₂]
  norm_num

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
