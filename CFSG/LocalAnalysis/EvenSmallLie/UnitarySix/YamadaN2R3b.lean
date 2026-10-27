module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Set

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

section R3b

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}
variable [Fact (ElemSec D₂ (⊥ : Subgroup G))] [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal]
variable (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)
include h

omit h [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.mk2_eq_iff (n n' : nTwo D₂ K₂ D₁) :
    mk2 D₂ K₂ D₁ n = mk2 D₂ K₂ D₁ n' ↔ (n : G)⁻¹ * n' ∈ D₂ := by
  rw [mk2, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simp

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.theta2_apply (g : SL3) : theta2 h g = mk2 D₂ K₂ D₁ ⟨θ₂ g, h.θ_mem g⟩ := rfl

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.dmap2_apply (x : D₁) : dmap2 h x = mk2 D₂ K₂ D₁ ⟨x, D₁_le_nTwo x.2⟩ := rfl

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.pi_inj : Function.Injective (iota2 h) := by
  intro u v huv
  rw [iota2_apply, iota2_apply, secMk_eq_bot_iff] at huv
  have huv' : ιG u = ιG v := huv
  have h1 : ιG (u + v) = 1 := by
    rw [h.ι_add, ← huv']
    exact h.D₂_sq _ (h.A₂_le (h.ι_mem u))
  have h2 := h.ι_inj _ h1
  rw [eq_neg_of_add_eq_zero_left h2]
  ext i
  exact ZMod.neg_eq_self_mod_two (v i)

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.pi_fix (u : Fin 9 → ZMod 2) : tauW2 h (iota2 h u) = iota2 h u := by
  rw [iota2_apply, tauW2, secAct_mk]
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h.A₂_t _ (h.ι_mem u), mul_inv_cancel_right]

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.pi_range (u : Fin 9 → ZMod 2) : ∃ x, tauW2 h x + x = iota2 h u := by
  obtain ⟨x, hx, hxu⟩ := h.ι_range u
  refine ⟨secMk ⟨x, hx⟩, ?_⟩
  rw [tauW2, secAct_mk, ← secMk_mul, iota2_apply, secMk_eq_bot_iff]
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul]
  rw [← hxu, h.D₂_comm _ ((mem_normalizer_iff.mp h.t_D₂ x).mp hx) x hx]

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.card_W : Nat.card (secW D₂ (⊥ : Subgroup G)) = 2 ^ (9 + 9) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((⊥ : Subgroup G).subgroupOf D₂)
  rw [card_subgroupOf_of_le bot_le, h.card_D₂, Subgroup.card_bot, mul_one] at h1
  change Nat.card (↥D₂ ⧸ (⊥ : Subgroup G).subgroupOf D₂) = 2 ^ (9 + 9)
  rw [← h1]

theorem Y14Hyp.pi_comm (g : SL3) (x : secW D₂ (⊥ : Subgroup G)) :
    tauW2 h (pi2 h (theta2 h g) x) = pi2 h (theta2 h g) (tauW2 h x) := by
  obtain ⟨y, rfl⟩ := secMk_surjective x
  rw [h.theta2_apply, pi2_mk, tauW2, secAct_mk, secAct_mk, pi2_mk]
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  have hk := h.θ_t g
  calc t * (θ₂ g * y * (θ₂ g)⁻¹) * t⁻¹ = (t * θ₂ g) * y * (t * θ₂ g)⁻¹ := by group
    _ = (θ₂ g * t) * y * (θ₂ g * t)⁻¹ := by rw [hk]
    _ = θ₂ g * (t * y * t⁻¹) * (θ₂ g)⁻¹ := by group

theorem Y14Hyp.pi_ι_eq (g : SL3) (u : Fin 9 → ZMod 2) :
    pi2 h (theta2 h g) (iota2 h u) = iota2 h (rhoA g *ᵥ u) := by
  rw [h.theta2_apply, iota2_apply, pi2_mk, iota2_apply, secMk_eq_bot_iff]
  exact h.K₂_ι g u

omit h [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.mem_D₂_of_mk2 {y : G} (hy : y ∈ nTwo D₂ K₂ D₁)
    (h1 : mk2 D₂ K₂ D₁ ⟨y, hy⟩ = 1) : y ∈ D₂ := by
  rw [← map_one (mk2 D₂ K₂ D₁), Y14Hyp.mk2_eq_iff] at h1
  simpa using h1

omit h [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.mk2_eq_one {y : G} (hy : y ∈ nTwo D₂ K₂ D₁) (hyD : y ∈ D₂) :
    mk2 D₂ K₂ D₁ ⟨y, hy⟩ = 1 := by
  rw [← map_one (mk2 D₂ K₂ D₁), Y14Hyp.mk2_eq_iff]
  simpa using hyD

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_D_comm {a b} (ha : a ∈ DG2 h) (hb : b ∈ DG2 h) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, h.dmap2_apply, h.dmap2_apply, Y14Hyp.mk2_eq_iff]
  have hc := h.V₁_le₂ (h.D₁_comm_mod (y⁻¹ : D₁) (y⁻¹ : D₁).2 (x⁻¹ : D₁) (x⁻¹ : D₁).2)
  convert hc using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_D_sq {a} (ha : a ∈ DG2 h) : a * a = 1 := by
  obtain ⟨x, rfl⟩ := ha
  rw [← map_mul, h.dmap2_apply]
  exact Y14Hyp.mk2_eq_one _ (h.V₁_le₂ (h.D₁_sq_mod x x.2))

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_E_le {m : ℕ} (hm : m < 4) : theta2 h (gen3 (Fin.ofNat 12 m)) ∈ DG2 h :=
  ⟨⟨_, h.E_mem m hm⟩, rfl⟩

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_ν_norm {j : ℕ} (hj : j < 4) {d} (hd : d ∈ DG2 h) :
    theta2 h (gen3 (nuS j)) * d * (theta2 h (gen3 (nuS j)))⁻¹ ∈ DG2 h := by
  obtain ⟨x, rfl⟩ := hd
  have hν := h.ν_norm j hj
  refine ⟨⟨θ₂ (gen3 (nuS j)) * x * (θ₂ (gen3 (nuS j)))⁻¹, (mem_normalizer_iff.mp hν x).mp x.2⟩, ?_⟩
  rw [h.dmap2_apply, h.theta2_apply, h.dmap2_apply]
  have e : (⟨θ₂ (gen3 (nuS j)) * x * (θ₂ (gen3 (nuS j)))⁻¹,
      D₁_le_nTwo ((mem_normalizer_iff.mp hν x).mp x.2)⟩ : nTwo D₂ K₂ D₁) =
      ⟨θ₂ (gen3 (nuS j)), h.θ_mem _⟩ * ⟨x, D₁_le_nTwo x.2⟩ * ⟨θ₂ (gen3 (nuS j)), h.θ_mem _⟩⁻¹ :=
    Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_inv]

theorem Y14Hyp.pi_dmap (x : D₁) (y : D₂) :
    pi2 h (dmap2 h x) (secMk y) =
      secMk (V := (⊥ : Subgroup G)) (conjD (D := D₂) x (h.D₁_norm x.2) y) := rfl

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.comm_mem_inter (x : D₁) (y : D₂) :
    (x : G) * y * (x : G)⁻¹ * (y : G) ∈ D₁ ⊓ D₂ := by
  have hy1 : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right (h.D₂_sq y y.2)
  refine ⟨?_, ?_⟩
  · have h1 := (mem_normalizer_iff.mp (h.D₂_norm y.2) _).mp (inv_mem x.2)
    have e : (x : G) * y * (x : G)⁻¹ * y = x * ((y : G) * (x : G)⁻¹ * (y : G)⁻¹) := by
      rw [hy1]; group
    rw [e]
    exact mul_mem x.2 h1
  · have h1 := (mem_normalizer_iff.mp (h.D₁_norm x.2) _).mp y.2
    exact mul_mem h1 y.2

theorem Y14Hyp.pi_W0 {d} (hd : d ∈ DG2 h) (w : secW D₂ (⊥ : Subgroup G)) :
    pi2 h d w + w ∈ W02 h := by
  obtain ⟨x, rfl⟩ := hd
  obtain ⟨y, rfl⟩ := secMk_surjective w
  rw [h.pi_dmap, ← secMk_mul]
  exact ⟨_, (h.comm_mem_inter x y).1, rfl⟩

theorem Y14Hyp.pi_W1 {d} (hd : d ∈ DG2 h) {w : secW D₂ (⊥ : Subgroup G)} (hw : w ∈ W02 h) :
    pi2 h d w + w ∈ V2 h := by
  obtain ⟨x, rfl⟩ := hd
  obtain ⟨y, hy1, rfl⟩ := hw
  rw [h.pi_dmap, ← secMk_mul]
  refine ⟨_, ?_, rfl⟩
  have hy : (y : G)⁻¹ = y := inv_eq_of_mul_eq_one_right (h.D₂_sq y y.2)
  have := h.D₁_comm_mod x x.2 y hy1
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul]
  rw [← hy] at this ⊢
  convert this using 1
  rw [hy, hy]

theorem Y14Hyp.pi_W2 {d} (hd : d ∈ DG2 h) {w : secW D₂ (⊥ : Subgroup G)} (hw : w ∈ V2 h) :
    pi2 h d w = w := by
  obtain ⟨x, rfl⟩ := hd
  obtain ⟨y, hy, rfl⟩ := hw
  rw [h.pi_dmap, secMk_eq_bot_iff]
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← h.V₁_central y hy x x.2, mul_inv_cancel_right]

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.card_W02 [Finite G] : Nat.card (W02 h) ≤ 2 ^ 10 := by
  have hs : Function.Surjective (fun y : (D₁ ⊓ D₂ : Subgroup G) =>
      (⟨secMk (V := (⊥ : Subgroup G)) ⟨y, y.2.2⟩, ⟨_, y.2.1, rfl⟩⟩ : W02 h)) := by
    rintro ⟨_, ⟨y, hy1, rfl⟩⟩
    exact ⟨⟨y, hy1, y.2⟩, rfl⟩
  exact (Nat.card_le_card_of_surjective _ hs).trans h.card_D₁D₂

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem Y14Hyp.card_V2 [Finite G] : Nat.card (V2 h) ≤ 4 := by
  have hs : Function.Surjective (fun y : V₁ =>
      (⟨secMk (V := (⊥ : Subgroup G)) ⟨y, h.V₁_le₂ y.2⟩, ⟨_, y.2, rfl⟩⟩ : V2 h)) := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  exact (Nat.card_le_card_of_surjective _ hs).trans h.card_V₁

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.eProdG_theta2 (μ : ℕ) :
    eProdG (theta2 h) μ = mk2 D₂ K₂ D₁ ⟨eProdG θ₂ μ, Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx; exact h.θ_mem _⟩ := by
  unfold eProdG
  have : (List.map (fun m => theta2 h (gen3 (Fin.ofNat 12 m))) (bitList μ)) =
      List.map (mk2 D₂ K₂ D₁) (List.map (fun m => (⟨θ₂ (gen3 (Fin.ofNat 12 m)), h.θ_mem _⟩ :
        nTwo D₂ K₂ D₁)) (bitList μ)) := by
    rw [List.map_map]; rfl
  rw [this, ← map_list_prod]
  congr 1
  apply Subtype.ext
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  rfl

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_τfix {d} (hd : d ∈ DG2 h) (hτ : tauG2 h d = d) :
    ∃ μ < 16, d = eProdG (theta2 h) μ := by
  obtain ⟨x, rfl⟩ := hd
  rw [h.dmap2_apply, tauG2_mk, Y14Hyp.mk2_eq_iff] at hτ
  have hx : (x : G)⁻¹ * (t * x * t⁻¹) ∈ D₂ := by
    have := D₂.inv_mem hτ
    simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk] at this
    convert this using 1
    group
  obtain ⟨μ, hμ, hxμ⟩ := h.D₁_fix x x.2 hx
  refine ⟨μ, hμ, ?_⟩
  rw [h.eProdG_theta2, h.dmap2_apply, Y14Hyp.mk2_eq_iff]
  exact hxμ

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_τsurj {m : ℕ} (hm : m < 4) :
    ∃ d ∈ DG2 h, d * tauG2 h d = theta2 h (gen3 (Fin.ofNat 12 m)) := by
  obtain ⟨x, hx, hxm⟩ := h.D₁_surj m hm
  refine ⟨dmap2 h ⟨x, hx⟩, ⟨_, rfl⟩, ?_⟩
  rw [h.dmap2_apply, tauG2_mk, ← map_mul, h.theta2_apply, Y14Hyp.mk2_eq_iff]
  exact hxm

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_ττ (g : ↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :
    tauG2 h (tauG2 h g) = g := by
  induction g using QuotientGroup.induction_on with | H n => ?_
  change mk2 D₂ K₂ D₁ _ = mk2 D₂ K₂ D₁ n
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  have ht := h.t_sq
  calc t * (t * (n : G) * t⁻¹) * t⁻¹ = (t * t) * n * (t * t)⁻¹ := by group
    _ = n := by rw [ht]; group

theorem Y14Hyp.pi_πτ (g : ↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :
    pi2 h (tauG2 h g) = tauW2 h ∘ₗ pi2 h g ∘ₗ tauW2 h := by
  induction g using QuotientGroup.induction_on with | H n => ?_
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := secMk_surjective w
  change secMk _ = secMk _
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, _root_.mul_inv_rev, h.t_inv]
  group

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_τK (g : SL3) : tauG2 h (theta2 h g) = theta2 h g := by
  rw [h.theta2_apply, tauG2_mk]
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h.θ_t g, mul_inv_cancel_right]

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_τD {d} (hd : d ∈ DG2 h) : tauG2 h d ∈ DG2 h := by
  obtain ⟨x, rfl⟩ := hd
  refine ⟨⟨t * x * t⁻¹, (mem_normalizer_iff.mp h.t_D₁ x).mp x.2⟩, ?_⟩
  rw [h.dmap2_apply, h.dmap2_apply, tauG2_mk]
  rfl

theorem Y14Hyp.pi_Kr (g : ↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))
    (hπ : pi2 h g = 1) (hτ : tauG2 h g = g) : g = 1 := by
  induction g using QuotientGroup.induction_on with | H n => ?_
  have hn : (n : G) ∈ D₂ := by
    refine h.Kr n n.2 (fun y hy => ?_) ?_
    · have := LinearMap.congr_fun hπ (secMk ⟨y, hy⟩)
      rw [show ((n : ↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁))) = mk2 D₂ K₂ D₁ n from rfl,
        pi2_mk, Module.End.one_apply, secMk_eq_bot_iff] at this
      exact this
    · have h1 : mk2 D₂ K₂ D₁ (conjD t h.t_mem_normalizer n) = mk2 D₂ K₂ D₁ n := hτ
      rw [Y14Hyp.mk2_eq_iff] at h1
      have h2 := D₂.inv_mem h1
      simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk] at h2
      convert h2 using 1
      group
  change mk2 D₂ K₂ D₁ n = mk2 D₂ K₂ D₁ 1
  rw [Y14Hyp.mk2_eq_iff]
  simpa using hn

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem Y14Hyp.pi_gen : (theta2 h).range ⊔ DG2 h = ⊤ := by
  set S : Subgroup (nTwo D₂ K₂ D₁) := ((theta2 h).range ⊔ DG2 h).comap (mk2 D₂ K₂ D₁)
  have hD₂ : D₂.subgroupOf (nTwo D₂ K₂ D₁) ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    have : mk2 D₂ K₂ D₁ x = 1 := by
      rw [← map_one (mk2 D₂ K₂ D₁), Y14Hyp.mk2_eq_iff]
      simpa using Subgroup.mem_subgroupOf.mp hx
    rw [this]; exact one_mem _
  have hK₂ : K₂.subgroupOf (nTwo D₂ K₂ D₁) ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx' : (x : G) ∈ θ₂.range := by rw [h.K₂_eq]; exact Subgroup.mem_subgroupOf.mp hx
    obtain ⟨g, hg⟩ := hx'
    refine Subgroup.mem_sup_left ⟨g, ?_⟩
    rw [h.theta2_apply]
    congr 1
    exact Subtype.ext hg
  have hD₁ : D₁.subgroupOf (nTwo D₂ K₂ D₁) ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_right ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hcl : nTwo D₂ K₂ D₁ = Subgroup.closure ((D₂ : Set G) ∪ K₂ ∪ D₁) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
    rfl
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' := hx
    rw [hcl] at hx'
    refine Subgroup.closure_induction (p := fun y _ => ∀ hy : y ∈ nTwo D₂ K₂ D₁, ⟨y, hy⟩ ∈ S)
      ?_ ?_ ?_ ?_ hx' hx
    · rintro y ((hy | hy) | hy) hy'
      · exact hD₂ (Subgroup.mem_subgroupOf.mpr hy)
      · exact hK₂ (Subgroup.mem_subgroupOf.mpr hy)
      · exact hD₁ (Subgroup.mem_subgroupOf.mpr hy)
    · intro _; exact S.one_mem
    · intro a b ha hb iha ihb hab
      exact S.mul_mem (iha (by rw [hcl]; exact ha)) (ihb (by rw [hcl]; exact hb))
    · intro a ha iha hai
      exact S.inv_mem (iha (by rw [hcl]; exact ha))
  rw [eq_top_iff]
  intro γ _
  induction γ using QuotientGroup.induction_on with | H n => ?_
  have : n ∈ S := htop ▸ Subgroup.mem_top n
  exact this

theorem Y14Hyp.r3bHyp [Finite G] :
    R3bHyp (pi2 h) (theta2 h) (tauW2 h) (iota2 h) (DG2 h) (W02 h) (V2 h) (tauG2 h) where
  inj := h.pi_inj
  fix := h.pi_fix
  range := h.pi_range
  card := h.card_W
  comm := h.pi_comm
  ι_eq := h.pi_ι_eq
  D_comm := fun _ ha _ hb => h.pi_D_comm ha hb
  D_sq := fun _ ha => h.pi_D_sq ha
  E_le := fun _ hm => h.pi_E_le hm
  ν_norm := fun _ hj _ hd => h.pi_ν_norm hj hd
  W0 := fun _ hd w => h.pi_W0 hd w
  W0_card := h.card_W02
  W1 := fun _ hd _ hw => h.pi_W1 hd hw
  V_card := h.card_V2
  W2 := fun _ hd _ hw => h.pi_W2 hd hw
  τfix := fun _ hd hτ => h.pi_τfix hd hτ
  τsurj := fun _ hm => h.pi_τsurj hm
  gen := h.pi_gen
  ττ := h.pi_ττ
  πτ := h.pi_πτ
  τK := h.pi_τK
  τD := fun _ hd => h.pi_τD hd
  Kr := h.pi_Kr

end R3b

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
