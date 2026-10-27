module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3A
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem eq_AW_or_eq_D₁ (h : d.Hyp) {Z : Subgroup G} (hZD : Z ≤ d.D₁) (hAW : d.AW ≤ Z)
    (hinv : ∀ g ∈ normalizer (d.A₁ : Set G) ⊓ d.H, ∀ x ∈ Z, g * x * g⁻¹ ∈ Z) :
    Z = d.AW ∨ Z = d.D₁ := by
  let B₀ : Set SU52 :=
    {α | α ∈ A₁sub ∧ ∃ x ∈ Z, ∃ w ∈ d.W, x * d.t * x⁻¹ * d.t = d.ι α * w}
  have h1 : (1 : SU52) ∈ B₀ := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by simp [h.t_mul_t]⟩
  have hmul : ∀ α ∈ B₀, ∀ β ∈ B₀, α * β ∈ B₀ := fun α hα β hβ =>
    ⟨mul_mem hα.1 hβ.1, h.crossed_set_mul_mem hZD hα.1 hβ.1 hα.2 hβ.2⟩
  have hinvB : ∀ α ∈ B₀, α⁻¹ ∈ B₀ := fun α hα => by
    have hpow : ∀ n : ℕ, α ^ n ∈ B₀ := fun n => by
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hmul _ ih _ hα
    have e : α⁻¹ = α ^ (orderOf α - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos α),
        pow_orderOf_eq_one]
    rw [e]
    exact hpow _
  let B : Subgroup SU52 :=
    { carrier := B₀
      one_mem' := h1
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      inv_mem' := fun {a} ha => hinvB a ha }
  have hZB : ZX₄sub ≤ B := fun α hα => by
    have hα1 : α ∈ A₁sub := (ZX₄sub_le_X₄sub.trans X₄sub_le_A₁sub') hα
    have hW : d.ι α ∈ d.W := h.ZX₄_le_W ⟨α, hα, rfl⟩
    exact ⟨hα1, 1, one_mem _, (d.ι α)⁻¹, inv_mem hW, by simp [h.t_mul_t]⟩
  have hBA : B ≤ A₁sub := fun α hα => hα.1
  have hN : ∀ g ∈ normalizer (A₁sub : Set SU52), ∀ r ∈ B, g * r * g⁻¹ ∈ B := by
    intro g hg r hr
    obtain ⟨hr1, x, hx, w, hw, e⟩ := hr
    have hgN : d.ι g ∈ normalizer (d.A₁ : Set G) ⊓ d.H :=
      Subgroup.mem_inf.2 ⟨ι_mem_normalizer_pull hg, h.L_le_H (d.ι_mem g)⟩
    have hgX : d.ι g ∈ d.XW := h.NHA₁_le_XW hgN
    have hgW : d.ι g * w * (d.ι g)⁻¹ ∈ d.W :=
      (mem_normalizer_iff.1 (Subgroup.mem_inf.1 hgX).2 w).1 hw
    refine ⟨(mem_normalizer_iff.1 hg r).1 hr1, d.ι g * x * (d.ι g)⁻¹, hinv _ hgN x hx, _, hgW, ?_⟩
    rw [crossed_conj_of_mem_H (Subgroup.mem_inf.1 hgN).2, e]
    simp only [map_mul, map_inv]
    group
  rcases eq_ZX₄sub_or_eq_A₁sub_of_normalizer hZB hBA hN with hB | hB
  · left
    refine le_antisymm (fun x hx => ?_) hAW
    have hxD := hZD hx
    obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW (h.theta_mem_AW hxD)
    obtain ⟨α, hα, rfl⟩ := ha
    have hαB : α ∈ B := ⟨hα, x, hx, w, hw, e.symm⟩
    rw [hB] at hαB
    have hW : d.ι α ∈ d.W := h.ZX₄_le_W ⟨α, hαB, rfl⟩
    exact (h.crossed_mem_W_iff_of_mem_D₁ hxD).1 (by rw [← e]; exact mul_mem hW hw)
  · right
    refine le_antisymm hZD (fun u hu => ?_)
    obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW (h.theta_mem_AW hu)
    obtain ⟨α, hα, rfl⟩ := ha
    have hαinv : α⁻¹ ∈ B := by
      rw [hB]
      exact inv_mem hα
    obtain ⟨-, x', hx', w'', hw'', e'⟩ := hαinv
    rw [map_inv] at e'
    obtain ⟨w₀, hw₀, e₀⟩ := h.crossed_mul_mem (Subgroup.mem_inf.1 hu).1 (D₁_le_XW (hZD hx'))
    have hcomm : d.ι α * w'' = w'' * d.ι α := h.A₁_comm_W ⟨α, hα, rfl⟩ hw''
    have hux : u * x' * d.t * (u * x')⁻¹ * d.t ∈ d.W := by
      rw [e₀, e', ← e]
      have : (d.ι α)⁻¹ * w'' * (d.ι α * w) * w₀ = w'' * w * w₀ := by
        calc (d.ι α)⁻¹ * w'' * (d.ι α * w) * w₀ = (d.ι α)⁻¹ * (w'' * d.ι α) * w * w₀ := by group
          _ = (d.ι α)⁻¹ * (d.ι α * w'') * w * w₀ := by rw [hcomm]
          _ = w'' * w * w₀ := by group
      rw [this]
      exact mul_mem (mul_mem hw'' hw) hw₀
    have hux' : u * x' ∈ Z := hAW ((h.crossed_mem_W_iff_of_mem_D₁
      (mul_mem hu (hZD hx'))).1 hux)
    have := mul_mem hux' (inv_mem hx')
    rwa [mul_inv_cancel_right] at this

theorem exists_mem_V₂_not_mem_AW (h : d.Hyp) : ∃ v ∈ d.V₂, v ∉ d.AW := by
  have hZ : Nat.card d.ZX₄ = 2 := by rw [Data.ZX₄, d.card_pull, card_ZX₄sub]
  obtain ⟨g, hg, hgZ⟩ : ∃ g ∈ d.Z₂, g ∉ d.ZX₄ := by
    by_contra hcon
    have hle : d.Z₂ ≤ d.ZX₄ := fun g hg => by
      by_contra hn
      exact hcon ⟨g, hg, hn⟩
    have := Subgroup.card_le_of_le hle
    rw [card_Z₂ (d := d), hZ] at this
    omega
  obtain ⟨v, hv, hvg⟩ := h.exists_V₂_crossed_eq hg
  refine ⟨v, hv, fun hvAW => hgZ ?_⟩
  have hvD : v ∈ d.D₁ := h.V₂_le_D₁ hv
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq (h.V₂_le_Y hv))
  have hθ : v * d.t * v⁻¹ * d.t ∈ d.W := (h.crossed_mem_W_iff_of_mem_D₁ hvD).2 hvAW
  rw [hvi] at hθ hvg
  rw [hvg] at hθ
  have : g ∈ d.A₁ ⊓ d.W := Subgroup.mem_inf.2 ⟨Z₂_le_A₁ hg, hθ⟩
  rwa [h.A₁_inf_W] at this

theorem mem_normalizer_of_forall_comm {N : Subgroup G} {x : G} (hc : ∀ n ∈ N, n * x = x * n) :
    x ∈ normalizer (N : Set G) :=
  mem_normalizer_fintype fun n hn => by
    rw [← hc n hn, mul_inv_cancel_right]
    exact hn

theorem D₂_comm_Y' {x y : G} (hx : x ∈ d.D₂) (hy : y ∈ d.Y) : x * y = y * x :=
  ((mem_D₂_iff.1 hx).2 y hy).symm

theorem D₁_le_cenMod_W_V₂ (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) : d.D₁ ≤ cenMod d.W d.V₂ := by
  rw [h.D₁_eq_D₃e₂_sup_M]
  refine sup_le (fun x hx => ?_) (fun m hm => ?_)
  · have hxD₂ := h.D₃e₂_le_D₂ hx
    refine ⟨mem_normalizer_of_forall_comm fun w hw => (D₂_comm_Y' hxD₂ (d.W_le_Y hw)).symm,
      fun v hv => ?_⟩
    rw [D₂_comm_Y' hxD₂ (h.V₂_le_Y hv), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  · have hmC := (Subgroup.mem_inf.1 hm).2
    exact ⟨mem_normalizer_of_forall_comm fun w hw => (mem_centralizer_iff.1
      (Subgroup.mem_inf.1 (M_le_D₁ hm)).2 w hw), fun v hv => hK v hv m hm⟩

theorem commutator_D₁_cenMod (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.D₁ ⊓ cenMod d.W d.D₁ = d.D₁ := by
  set Z : Subgroup G := d.D₁ ⊓ cenMod d.W d.D₁ with hZdef
  have hZD : Z ≤ d.D₁ := inf_le_left
  have hAW : d.AW ≤ Z := by
    refine sup_le (fun a ha => ?_) (fun w hw => ?_)
    · refine Subgroup.mem_inf.2 ⟨h.A₁_le_D₁ ha, mem_normalizer_of_forall_comm
        fun w hw => (h.A₁_comm_W ha hw).symm, fun y hy => ?_⟩
      have := ((mem_UA₁_iff.1 (Subgroup.mem_inf.1 hy).1).2 a⁻¹ (inv_mem ha)).1
      rwa [inv_inv] at this
    · refine Subgroup.mem_inf.2 ⟨h.W_le_D₁ hw, mem_normalizer_of_forall_comm
        fun w' hw' => (h.sec4_9_W.2.2.2.2.1 w' hw' w hw), fun y hy => ?_⟩
      have hyC := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hy).2 w hw
      rw [hyC, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hV : d.V₂ ≤ Z := fun v hv => by
    refine Subgroup.mem_inf.2 ⟨h.V₂_le_D₁ hv, ?_, fun y hy => ?_⟩
    · exact mem_normalizer_of_forall_comm fun w hw =>
        mem_centralizer_iff.1 (Subgroup.mem_inf.1 (h.V₂_le_D₁ hv)).2 w hw
    · have := inv_mem ((h.D₁_le_cenMod_W_V₂ hK hy).2 v hv)
      rwa [show (y * v * y⁻¹ * v⁻¹)⁻¹ = v * y * v⁻¹ * y⁻¹ by group] at this
  have hinv : ∀ g ∈ normalizer (d.A₁ : Set G) ⊓ d.H, ∀ x ∈ Z, g * x * g⁻¹ ∈ Z := by
    intro g hg x hx
    obtain ⟨hxD, hxcm⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxN, hxc⟩ := hxcm
    have hgX := h.NHA₁_le_XW hg
    have hgW := (Subgroup.mem_inf.1 hgX).2
    refine Subgroup.mem_inf.2 ⟨h.conj_mem_D₁ hgX hxD, ?_, fun y hy => ?_⟩
    · exact mul_mem (mul_mem hgW hxN) (inv_mem hgW)
    · have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ d.D₁ := h.conj_mem_D₁ (inv_mem hgX) hy
      rw [inv_inv] at hy'
      have := (mem_normalizer_iff.1 hgW _).1 (hxc _ hy')
      rwa [show g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ =
        g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ by group] at this
  rcases h.eq_AW_or_eq_D₁ hZD hAW hinv with hZ | hZ
  · exfalso
    obtain ⟨v, hv, hvAW⟩ := h.exists_mem_V₂_not_mem_AW
    exact hvAW (hZ ▸ hV hv)
  · exact hZ

theorem D₁_commutator_mem_W (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x y : G} (hx : x ∈ d.D₁)
    (hy : y ∈ d.D₁) : x * y * x⁻¹ * y⁻¹ ∈ d.W := by
  have hZ := h.commutator_D₁_cenMod hK
  have hx' : x ∈ d.D₁ ⊓ cenMod d.W d.D₁ := by
    rw [hZ]
    exact hx
  exact (Subgroup.mem_inf.1 hx').2.2 y hy


end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
