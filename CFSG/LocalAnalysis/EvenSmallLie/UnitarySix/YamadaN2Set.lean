module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParN1
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Hyp

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def nTwo {G : Type*} [Group G] (D₂ K₂ D₁ : Subgroup G) : Subgroup G := D₂ ⊔ K₂ ⊔ D₁

section Hyp

variable {G : Type} [Group G]

structure Y14Hyp (t : G) (D₁ V₁ D₂ A₂ K₂ : Subgroup G) (θ₂ : SL3 →* G)
    (ιG : (Fin 9 → ZMod 2) → G) : Prop where
  t_sq : t * t = 1
  D₂_comm : ∀ x ∈ D₂, ∀ y ∈ D₂, x * y = y * x
  D₂_sq : ∀ x ∈ D₂, x * x = 1
  card_D₂ : Nat.card D₂ = 2 ^ 18
  A₂_le : A₂ ≤ D₂
  A₂_t : ∀ a ∈ A₂, t * a = a * t
  D₂_H : ∀ x ∈ D₂, t * x = x * t → x ∈ A₂
  t_D₂ : t ∈ normalizer (D₂ : Set G)
  K₂_eq : θ₂.range = K₂
  K₂_t : ∀ k ∈ K₂, t * k = k * t
  K₂_norm : K₂ ≤ normalizer (D₂ : Set G)
  ι_mem : ∀ u, ιG u ∈ A₂
  ι_add : ∀ u v, ιG (u + v) = ιG u * ιG v
  ι_inj : ∀ u, ιG u = 1 → u = 0
  K₂_ι : ∀ g u, θ₂ g * ιG u * (θ₂ g)⁻¹ = ιG (rhoA g *ᵥ u)
  ι_range : ∀ u, ∃ x ∈ D₂, x * (t * x * t⁻¹) = ιG u
  D₁_norm : D₁ ≤ normalizer (D₂ : Set G)
  D₂_norm : D₂ ≤ normalizer (D₁ : Set G)
  t_D₁ : t ∈ normalizer (D₁ : Set G)
  V₁_le₁ : V₁ ≤ D₁
  V₁_le₂ : V₁ ≤ D₂
  card_V₁ : Nat.card V₁ ≤ 4
  V₁_central : ∀ v ∈ V₁, ∀ x ∈ D₁, v * x = x * v
  D₁_comm_mod : ∀ x ∈ D₁, ∀ y ∈ D₁, x * y * x⁻¹ * y⁻¹ ∈ V₁
  D₁_sq_mod : ∀ x ∈ D₁, x * x ∈ V₁
  card_D₁D₂ : Nat.card (D₁ ⊓ D₂ : Subgroup G) ≤ 2 ^ 10
  E_mem : ∀ m < 4, θ₂ (gen3 (Fin.ofNat 12 m)) ∈ D₁
  ν_norm : ∀ j < 4, θ₂ (gen3 (nuS j)) ∈ normalizer (D₁ : Set G)
  D₁_fix : ∀ x ∈ D₁, x⁻¹ * (t * x * t⁻¹) ∈ D₂ → ∃ μ < 16, x⁻¹ * eProdG θ₂ μ ∈ D₂
  D₁_surj : ∀ m < 4, ∃ x ∈ D₁, (x * (t * x * t⁻¹))⁻¹ * θ₂ (gen3 (Fin.ofNat 12 m)) ∈ D₂
  Kr : ∀ x ∈ nTwo D₂ K₂ D₁, (∀ y ∈ D₂, x * y * x⁻¹ = y) → x⁻¹ * (t * x * t⁻¹) ∈ D₂ → x ∈ D₂

end Hyp

section Derived

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}
variable (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG)
include h

theorem Y14Hyp.elemSec : ElemSec D₂ (⊥ : Subgroup G) where
  le := bot_le
  central := fun v hv x _ => by rw [Subgroup.mem_bot.mp hv, one_mul, mul_one]
  comm := fun x hx y hy => by
    rw [Subgroup.mem_bot, h.D₂_comm x hx y hy]; group
  sq := fun x hx => by rw [Subgroup.mem_bot]; exact h.D₂_sq x hx

omit h in
theorem D₂_le_nTwo : D₂ ≤ nTwo D₂ K₂ D₁ := le_sup_left.trans le_sup_left

omit h in
theorem K₂_le_nTwo : K₂ ≤ nTwo D₂ K₂ D₁ := le_sup_right.trans le_sup_left

omit h in
theorem D₁_le_nTwo : D₁ ≤ nTwo D₂ K₂ D₁ := le_sup_right

theorem Y14Hyp.nTwo_le_normalizer : nTwo D₂ K₂ D₁ ≤ normalizer (D₂ : Set G) :=
  sup_le (sup_le le_normalizer h.K₂_norm) h.D₁_norm

omit h in
theorem le_normalizer_bot (N : Subgroup G) : N ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
  intro x _
  rw [mem_normalizer_iff]
  intro y
  simp only [Subgroup.mem_bot]
  constructor
  · rintro rfl; group
  · intro hy
    have : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [this, hy]; group

theorem Y14Hyp.t_mem_normalizer : t ∈ normalizer ((nTwo D₂ K₂ D₁ : Subgroup G) : Set G) :=
  mem_normalizer_sup' (mem_normalizer_sup' h.t_D₂ (mem_normalizer_of_conj_eq fun k hk => by
    rw [h.K₂_t k hk, mul_inv_cancel_right])) h.t_D₁

theorem Y14Hyp.t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq

theorem Y14Hyp.θ_mem (g : SL3) : θ₂ g ∈ nTwo D₂ K₂ D₁ :=
  K₂_le_nTwo (h.K₂_eq ▸ ⟨g, rfl⟩)

theorem Y14Hyp.θ_t (g : SL3) : t * θ₂ g = θ₂ g * t := h.K₂_t _ (h.K₂_eq ▸ ⟨g, rfl⟩)

end Derived

section Module

variable {G : Type} [Group G] {t : G} {D₁ V₁ D₂ A₂ K₂ : Subgroup G} {θ₂ : SL3 →* G}
  {ιG : (Fin 9 → ZMod 2) → G}
variable [Fact (ElemSec D₂ (⊥ : Subgroup G))] [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal]

@[expose] noncomputable def mk2 (D₂ K₂ D₁ : Subgroup G) [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] :
    nTwo D₂ K₂ D₁ →* (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
  QuotientGroup.mk' _

@[expose] noncomputable def pi2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) →*
      (secW D₂ (⊥ : Subgroup G) →ₗ[ZMod 2] secW D₂ (⊥ : Subgroup G)) :=
  gamRep (nTwo D₂ K₂ D₁) h.nTwo_le_normalizer (le_normalizer_bot _)

theorem pi2_mk (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) (n : nTwo D₂ K₂ D₁) (x : D₂) :
    pi2 h (mk2 D₂ K₂ D₁ n) (secMk x) =
      secMk (V := (⊥ : Subgroup G)) (conjD (D := D₂) n (h.nTwo_le_normalizer n.2) x) := rfl

@[expose] noncomputable def tauW2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    secW D₂ (⊥ : Subgroup G) →ₗ[ZMod 2] secW D₂ (⊥ : Subgroup G) :=
  secAct t h.t_D₂ (le_normalizer_bot ⊤ (Subgroup.mem_top t))

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem secMk_eq_bot_iff (x y : D₂) :
    secMk (V := (⊥ : Subgroup G)) x = secMk y ↔ (x : G) = y := by
  rw [secMk_eq_iff, Subgroup.mem_bot, inv_mul_eq_one]

@[expose] noncomputable def iota2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    (Fin 9 → ZMod 2) →ₗ[ZMod 2] secW D₂ (⊥ : Subgroup G) where
  toFun u := secMk ⟨ιG u, h.A₂_le (h.ι_mem u)⟩
  map_add' u v := by
    rw [← secMk_mul, secMk_eq_bot_iff]
    simp only [Subgroup.coe_mul]
    exact h.ι_add u v
  map_smul' c u := by
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul]
      change secMk ⟨ιG 0, _⟩ = secMk (1 : D₂)
      rw [secMk_eq_bot_iff]
      have := h.ι_add 0 0
      rw [add_zero] at this
      simpa using (mul_eq_left.mp this.symm)
    · rw [one_smul, RingHom.id_apply, one_smul]

omit [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem iota2_apply (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) (u : Fin 9 → ZMod 2) :
    iota2 h u = secMk ⟨ιG u, h.A₂_le (h.ι_mem u)⟩ := rfl

@[expose] noncomputable def theta2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    SL3 →* (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
  (mk2 D₂ K₂ D₁).comp (θ₂.codRestrict (nTwo D₂ K₂ D₁) h.θ_mem)

@[expose] noncomputable def dmap2 (_h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    D₁ →* (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
  (mk2 D₂ K₂ D₁).comp (Subgroup.inclusion D₁_le_nTwo)

@[expose] noncomputable def DG2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    Subgroup (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
  (dmap2 h).range

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] [(D₂.subgroupOf (nTwo D₂ K₂ D₁)).Normal] in
theorem conjD_t_le2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    D₂.subgroupOf (nTwo D₂ K₂ D₁) ≤
      (D₂.subgroupOf (nTwo D₂ K₂ D₁)).comap (conjD (D := nTwo D₂ K₂ D₁) t h.t_mem_normalizer) := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
  exact (mem_normalizer_iff.mp h.t_D₂ x).mp hx

@[expose] noncomputable def tauG2 (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) →*
      (↥(nTwo D₂ K₂ D₁) ⧸ D₂.subgroupOf (nTwo D₂ K₂ D₁)) :=
  QuotientGroup.map _ _ (conjD (D := nTwo D₂ K₂ D₁) t h.t_mem_normalizer) (conjD_t_le2 h)

omit [Fact (ElemSec D₂ (⊥ : Subgroup G))] in
theorem tauG2_mk (h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) (n : nTwo D₂ K₂ D₁) :
    tauG2 h (mk2 D₂ K₂ D₁ n) = mk2 D₂ K₂ D₁ (conjD t h.t_mem_normalizer n) := rfl

@[expose] noncomputable def W02 (_h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    Submodule (ZMod 2) (secW D₂ (⊥ : Subgroup G)) where
  carrier := {w | ∃ y : D₂, (y : G) ∈ D₁ ∧ secMk y = w}
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y * y', mul_mem hy hy', secMk_mul y y'⟩
  zero_mem' := ⟨1, one_mem _, rfl⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨1, one_mem _, by rw [zero_smul]; rfl⟩
    · exact ⟨y, hy, by rw [one_smul]⟩

@[expose] noncomputable def V2 (_h : Y14Hyp t D₁ V₁ D₂ A₂ K₂ θ₂ ιG) :
    Submodule (ZMod 2) (secW D₂ (⊥ : Subgroup G)) where
  carrier := {w | ∃ y : D₂, (y : G) ∈ V₁ ∧ secMk y = w}
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y * y', mul_mem hy hy', secMk_mul y y'⟩
  zero_mem' := ⟨1, one_mem _, rfl⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨1, one_mem _, by rw [zero_smul]; rfl⟩
    · exact ⟨y, hy, by rw [one_smul]⟩

end Module

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
