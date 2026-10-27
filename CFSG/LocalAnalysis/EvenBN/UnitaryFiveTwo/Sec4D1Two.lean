module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4D1
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA1C

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped Pointwise

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem D₁_inf_H
    (h : d.Hyp) :
    d.D₁ ⊓ d.H = d.A₁ := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf h.A₁_le_D₁ fun a ha => h.L_le_H (d.pull_le_L _ ha))
  obtain ⟨hxD, hxH⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.1 hxD
  obtain ⟨hxX, hxa⟩ := mem_UA₁_iff.1 hxU
  have hxN := h.mem_normalizer_A₁_of_mem_XW_of_mem_H hxX hxH
  have key : ∀ α ∈ A₁sub, α⁻¹ * h.act ⟨x, hxH⟩ α ∈ ZX₄sub := fun α hα => by
    have hαA : d.ι α ∈ d.A₁ := ⟨α, hα, rfl⟩
    have hm : (d.ι α)⁻¹ * (x * d.ι α * x⁻¹) ∈ d.ZX₄ := by
      rw [← h.W_inf_H]
      refine Subgroup.mem_inf.2 ⟨?_, h.L_le_H (d.pull_le_L _
        (mul_mem (inv_mem hαA) ((mem_normalizer_iff.1 hxN _).1 hαA)))⟩
      rw [show (d.ι α)⁻¹ * (x * d.ι α * x⁻¹) = (d.ι α)⁻¹ * x * d.ι α * x⁻¹ by group]
      exact (hxa _ hαA).1
    have e : d.ι (h.act ⟨x, hxH⟩ α) = x * d.ι α * x⁻¹ := h.ι_act_apply _ _
    rw [← e, ← map_inv, ← map_mul] at hm
    exact d.ι_mem_pull_iff.1 hm
  obtain ⟨s, hs | hs⟩ := exists_eq_conj_or_eq_conj_mul_fld (h.act ⟨x, hxH⟩)
  · have hsA : s ∈ A₁sub := mem_A₁sub_of_conj_mem fun α hα => by
      have := key α hα
      rwa [hs, MulAut.conj_apply] at this
    obtain ⟨c, hc, e⟩ := exists_eq_mul_of_act_eq_conj d.L d.η ⟨x, h.H_le_normalizer hxH⟩ s hs
    change x = d.ι s * c at e
    have hcH : c ∈ d.H := by
      have := mul_mem (inv_mem (h.L_le_H (d.ι_mem s))) hxH
      rwa [e, inv_mul_cancel_left] at this
    have hct : c ∈ zpowers d.t := by
      rw [← h.centralizer_inf_H_eq]
      exact Subgroup.mem_inf.2 ⟨hc, hcH⟩
    rcases h.eq_one_or_eq_t hct with rfl | rfl
    · rw [e, mul_one]
      exact ⟨s, hsA, rfl⟩
    · exfalso
      apply h.not_comm_t_W
      intro w hw
      have e1 := mem_centralizer_iff.1 hxC w hw
      have e2 : d.ι s * w = w * d.ι s := h.A₁_comm_W ⟨s, hsA, rfl⟩ hw
      rw [e] at e1
      refine mul_left_cancel (a := d.ι s) ?_
      calc d.ι s * (w * d.t) = (d.ι s * w) * d.t := by group
        _ = (w * d.ι s) * d.t := by rw [e2]
        _ = w * (d.ι s * d.t) := by group
        _ = d.ι s * d.t * w := e1
        _ = d.ι s * (d.t * w) := by group
  · exfalso
    refine not_conj_fld_mem s fun α hα => ?_
    have := key α hα
    rwa [hs, MulAut.mul_apply, MulAut.conj_apply] at this

theorem AW_le_D₁
    (h : d.Hyp) :
    d.AW ≤ d.D₁ := sup_le h.A₁_le_D₁ h.W_le_D₁

theorem A₁_inf_W
    (h : d.Hyp) :
    d.A₁ ⊓ d.W = d.ZX₄ := by
  refine le_antisymm (fun x hx => ?_) (le_inf ZX₄_le_A₁ h.ZX₄_le_W)
  rw [← h.W_inf_H]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
    h.L_le_H (d.pull_le_L _ (Subgroup.mem_inf.1 hx).1)⟩

theorem card_AW
    (h : d.Hyp) :
    Nat.card d.AW = 2 ^ 8 := by
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.A₁ d.W
    fun _ ha _ hw => h.A₁_comm_W ha hw).1
  rw [h.A₁_inf_W, d.card_A₁, h.sec4_9_W.1, Data.ZX₄, d.card_pull, card_ZX₄sub] at hc
  rw [Data.AW]
  omega

omit [Finite G] in
theorem crossed_conj_of_mem_H {g u : G} (hg : g ∈ d.H) :
    g * u * g⁻¹ * d.t * (g * u * g⁻¹)⁻¹ * d.t = g * (u * d.t * u⁻¹ * d.t) * g⁻¹ := by
  have hgt : g * d.t = d.t * g := mem_centralizer_singleton_iff.1 hg
  have hgt' : g⁻¹ * d.t = d.t * g⁻¹ := by
    calc g⁻¹ * d.t = g⁻¹ * (d.t * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * d.t) * g⁻¹ := by rw [hgt]
      _ = d.t * g⁻¹ := by group
  calc g * u * g⁻¹ * d.t * (g * u * g⁻¹)⁻¹ * d.t =
      g * u * (g⁻¹ * d.t) * g * u⁻¹ * g⁻¹ * d.t := by group
    _ = g * u * (d.t * g⁻¹) * g * u⁻¹ * g⁻¹ * d.t := by rw [hgt']
    _ = g * (u * d.t * u⁻¹) * (g⁻¹ * d.t) := by group
    _ = g * (u * d.t * u⁻¹) * (d.t * g⁻¹) := by rw [hgt']
    _ = g * (u * d.t * u⁻¹ * d.t) * g⁻¹ := by group

theorem crossed_mul_mem
    (h : d.Hyp) {u₁ u₂ : G}
    (hu₁ : u₁ ∈ d.UA₁) (hu₂ : u₂ ∈ d.XW) :
    ∃ w ∈ d.W, u₁ * u₂ * d.t * (u₁ * u₂)⁻¹ * d.t =
      (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) * w := by
  have hk₂ := h.conj_t_mul_t_mem_AW hu₂
  have hk₁ := h.conj_t_mul_t_mem_AW (mem_UA₁_iff.1 hu₁).1
  obtain ⟨c, hc, hce⟩ : ∃ c ∈ d.W, u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹ =
      (u₂ * d.t * u₂⁻¹ * d.t) * c :=
    ⟨_, (h.mem_W_of_mem_UA₁_of_mem_AW hu₁ hk₂).1, by group⟩
  refine ⟨c, hc, ?_⟩
  have hcomm := h.AW_comm_W hk₁ hc
  calc u₁ * u₂ * d.t * (u₁ * u₂)⁻¹ * d.t =
      (u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹) * (u₁ * d.t * u₁⁻¹ * d.t) := by
        rw [show (u₁ * (u₂ * d.t * u₂⁻¹ * d.t) * u₁⁻¹) * (u₁ * d.t * u₁⁻¹ * d.t) =
          u₁ * u₂ * d.t * u₂⁻¹ * (d.t * d.t) * u₁⁻¹ * d.t by group, h.t_mul_t]
        group
    _ = (u₂ * d.t * u₂⁻¹ * d.t) * c * (u₁ * d.t * u₁⁻¹ * d.t) := by rw [hce]
    _ = (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) * c := by
        rw [mul_assoc _ c, ← hcomm, ← mul_assoc]

theorem smul_coset_mul_t
    (h : d.Hyp) {a w : G}
    (hw : w ∈ d.W) : (a * w * d.t) • (d.W : Set G) = (a * d.t) • (d.W : Set G) := by
  rw [leftCoset_eq_iff, show (a * w * d.t)⁻¹ * (a * d.t) = d.t⁻¹ * w⁻¹ * d.t by group, h.t_inv]
  exact h.t_conj_mem_W (inv_mem hw)

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem crossed_mem_W_iff_of_mem_D₁
    (h : d.Hyp) {u : G} (hu : u ∈ d.D₁) :
    u * d.t * u⁻¹ * d.t ∈ d.W ↔ u ∈ d.AW := by
  constructor
  · intro hut
    have hy := h.mem_NHA₁W_of_conj_t (D₁_le_XW hu) hut
    have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₁ : Set G) ⊓ d.H) d.W
      fun g hg => (Subgroup.mem_inf.1 (h.NHA₁_le_XW hg)).2
    obtain ⟨n, hn, w, hw, rfl⟩ : u ∈ ((normalizer (d.A₁ : Set G) ⊓ d.H : Subgroup G) : Set G) *
        (d.W : Set G) := by
      rw [← hset]
      exact hy
    have hnD : n ∈ d.D₁ := by
      have := mul_mem hu (inv_mem (h.W_le_D₁ hw))
      rwa [mul_inv_cancel_right] at this
    have hnA : n ∈ d.A₁ := by
      rw [← h.D₁_inf_H]
      exact Subgroup.mem_inf.2 ⟨hnD, (Subgroup.mem_inf.1 hn).2⟩
    exact mul_mem (mem_sup_left hnA) (mem_sup_right hw)
  · intro huAW
    obtain ⟨a, ha, w, hw, rfl⟩ := h.exists_eq_mul_of_mem_AW huAW
    have hat : a⁻¹ * d.t = d.t * a⁻¹ := h.t_comm_of_mem_L (d.pull_le_L _ (inv_mem ha))
    have hc : w * d.t * w⁻¹ * d.t ∈ d.W := by
      have := h.W_crossed_mem_ZX₄ (inv_mem hw)
      rw [inv_inv] at this
      exact h.ZX₄_le_W this
    have e : a * w * d.t * (a * w)⁻¹ * d.t = a * (w * d.t * w⁻¹ * d.t) * a⁻¹ := by
      calc a * w * d.t * (a * w)⁻¹ * d.t = a * w * d.t * w⁻¹ * (a⁻¹ * d.t) := by group
        _ = a * w * d.t * w⁻¹ * (d.t * a⁻¹) := by rw [hat]
        _ = a * (w * d.t * w⁻¹ * d.t) * a⁻¹ := by group
    rw [e, h.A₁_comm_W ha hc, mul_inv_cancel_right]
    exact hc

theorem mem_OmW_iff_of_elem
    (h : d.Hyp) {S : Set G} :
    S ∈ d.OmW ↔ ∃ a ∈ d.A₁, S = (a * d.t) • (d.W : Set G) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW (h.conj_t_mul_t_mem_AW hx)
    refine ⟨a, ha, ?_⟩
    rw [show x * d.t * x⁻¹ = a * w * d.t by rw [e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
    exact h.smul_coset_mul_t hw
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨u, hu, w, hw, e⟩ := h.exists_D₁_conj_t ha
    refine ⟨u, D₁_le_XW hu, ?_⟩
    rw [show u * d.t * u⁻¹ = a * w * d.t by rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one],
      h.smul_coset_mul_t hw]

theorem card_OmW_of_elem
    (h : d.Hyp) :
    Nat.card d.OmW = 64 := by
  have hmem : ∀ c : Fin 3 → F4, (d.ι (nfA₁ c) * d.t) • (d.W : Set G) ∈ d.OmW := fun c =>
    (h.mem_OmW_iff_of_elem).2 ⟨_, ⟨_, nfA₁_mem c, rfl⟩, rfl⟩
  let f : (Fin 3 → F4) → d.OmW := fun c => ⟨_, hmem c⟩
  have hf : Function.Bijective f := by
    refine ⟨fun c c' e => ?_, fun S => ?_⟩
    · have := (h.coset_ι_eq_iff (nfA₁_mem c) (nfA₁_mem c')).1 (congrArg Subtype.val e)
      rwa [cvec_nfA₁, cvec_nfA₁] at this
    · obtain ⟨a, ⟨α, hα, rfl⟩, hS⟩ := (h.mem_OmW_iff_of_elem).1 S.2
      refine ⟨cvec (mat α), Subtype.ext ?_⟩
      change (d.ι (nfA₁ (cvec (mat α))) * d.t) • (d.W : Set G) = (S : Set G)
      rw [hS]
      exact (h.coset_ι_eq_iff (nfA₁_mem _) hα).2 (cvec_nfA₁ _)
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_fin, F4.card]
  norm_num

theorem card_D₁
    (h : d.Hyp) :
    Nat.card d.D₁ = 2 ^ 14 := by
  let φ : d.D₁ →* Equiv.Perm d.OmW := d.omegaPermW.comp (Subgroup.inclusion D₁_le_XW)
  let : MulAction d.D₁ d.OmW := MulAction.compHom _ φ
  have hstab : MulAction.stabilizer d.D₁ (⟨_, tW_mem_OmW⟩ : d.OmW) = d.AW.subgroupOf d.D₁ := by
    ext u
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, ← h.crossed_mem_W_iff_of_mem_D₁ u.2,
      Subtype.ext_iff]
    change (fun g => (u : G) * g * (u : G)⁻¹) '' (d.t • (d.W : Set G)) =
      d.t • (d.W : Set G) ↔ _
    rw [conj_image_smul_coset (Subgroup.mem_inf.1 (D₁_le_XW u.2)).2, leftCoset_eq_iff,
      show ((u : G) * d.t * (u : G)⁻¹)⁻¹ * d.t = (u : G) * d.t * (u : G)⁻¹ * d.t by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, h.t_inv]
        group]
  have horb : MulAction.orbit d.D₁ (⟨_, tW_mem_OmW⟩ : d.OmW) = Set.univ := by
    refine Set.eq_univ_of_forall fun S => ?_
    obtain ⟨a, ha, hS⟩ := (h.mem_OmW_iff_of_elem).1 S.2
    obtain ⟨u, hu, w, hw, e⟩ := h.exists_D₁_conj_t ha
    refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    change (fun g => u * g * u⁻¹) '' (d.t • (d.W : Set G)) = (S : Set G)
    rw [conj_image_smul_coset (Subgroup.mem_inf.1 (D₁_le_XW hu)).2, hS,
      show u * d.t * u⁻¹ = a * w * d.t by rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one],
      h.smul_coset_mul_t hw]
  have hidx := MulAction.index_stabilizer (G := d.D₁) (⟨_, tW_mem_OmW⟩ : d.OmW)
  rw [horb, Set.ncard_univ, hstab, h.card_OmW_of_elem] at hidx
  rw [← (d.AW.subgroupOf d.D₁).card_mul_index, hidx,
    Nat.card_congr (subgroupOfEquivOfLe h.AW_le_D₁).toEquiv, h.card_AW]
  norm_num

theorem sec4_11_1
    (h : d.Hyp) :
    d.XW = (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.D₁ ∧ d.D₁ ⊓ d.H = d.A₁ ∧
      ∀ a ∈ d.A₁, ∃ u ∈ d.D₁,
        (u * d.t * u⁻¹) • (d.W : Set G) = (a * d.t) • (d.W : Set G) := by
  refine ⟨h.XW_eq_sup, h.D₁_inf_H, fun a ha => ?_⟩
  obtain ⟨u, hu, w, hw, e⟩ := h.exists_D₁_conj_t ha
  refine ⟨u, hu, ?_⟩
  rw [show u * d.t * u⁻¹ = a * w * d.t by rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one],
    h.smul_coset_mul_t hw]

theorem sec4_11_2
    (h : d.Hyp) :
    (∀ u ∈ d.D₁, u * d.t * u⁻¹ * d.t ∈ d.AW) ∧
      (∀ a ∈ d.A₁, ∃ u ∈ d.D₁, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = a * w) ∧
      (∀ u ∈ d.D₁, (u * d.t * u⁻¹ * d.t ∈ d.W ↔ u ∈ d.AW)) ∧
      (∀ u₁ ∈ d.D₁, ∀ u₂ ∈ d.D₁, ∃ w ∈ d.W, u₁ * u₂ * d.t * (u₁ * u₂)⁻¹ * d.t =
        (u₂ * d.t * u₂⁻¹ * d.t) * (u₁ * d.t * u₁⁻¹ * d.t) * w) ∧
      (∀ g ∈ normalizer (d.A₁ : Set G) ⊓ d.H, ∀ u : G,
        g * u * g⁻¹ * d.t * (g * u * g⁻¹)⁻¹ * d.t = g * (u * d.t * u⁻¹ * d.t) * g⁻¹) ∧
      Nat.card d.D₁ = 2 ^ 14 :=
  ⟨fun _ hu => h.conj_t_mul_t_mem_AW (D₁_le_XW hu), fun _ ha => h.exists_D₁_conj_t ha,
    fun _ hu => h.crossed_mem_W_iff_of_mem_D₁ hu,
    fun _ hu₁ _ hu₂ => h.crossed_mul_mem (Subgroup.mem_inf.1 hu₁).1 (D₁_le_XW hu₂),
    fun _ hg _ => crossed_conj_of_mem_H (Subgroup.mem_inf.1 hg).2, h.card_D₁⟩

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
