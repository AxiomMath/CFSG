module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParMain
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParQuot
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndConj

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Subgroup Matrix
open scoped commutatorElement

@[expose] def nOne {G : Type*} [Group G] (D₁ K₁ D₂ : Subgroup G) : Subgroup G := D₁ ⊔ K₁ ⊔ D₂

theorem conj_mem_sup_of_normalizer {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) {x : G} (hx : x ∈ H ⊔ K) :
    g * x * g⁻¹ ∈ H ⊔ K := by
  rw [Subgroup.sup_eq_closure] at hx ⊢
  refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ closure ((H : Set G) ∪ K))
    ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact Subgroup.subset_closure (Or.inl ((mem_normalizer_iff.mp hH y).mp hy))
    · exact Subgroup.subset_closure (Or.inr ((mem_normalizer_iff.mp hK y).mp hy))
  · simp
  · intro a b _ _ ha hb
    have := mul_mem ha hb
    simpa [mul_assoc] using this
  · intro a _ ha
    have := inv_mem ha
    simpa [mul_assoc] using this

theorem mem_normalizer_sup' {G : Type*} [Group G] {H K : Subgroup G} {g : G}
    (hH : g ∈ normalizer (H : Set G)) (hK : g ∈ normalizer (K : Set G)) :
    g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_sup_of_normalizer hH hK hx, fun hx => ?_⟩
  have := conj_mem_sup_of_normalizer (inv_mem hH) (inv_mem hK) hx
  simpa [mul_assoc] using this

theorem card_subgroupOf_of_le {G : Type*} [Group G] {H K : Subgroup G} (hle : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

section Hyp

variable {G : Type} [Group G]

structure Y13Hyp (t : G) (D₁ V₁ A₁ K₁ D₂ : Subgroup G) (θ : K₁ ≃* SU42b)
    (ιG : (Fin 8 → ZMod 2) → G) : Prop where
  t_sq : t * t = 1
  sec : ElemSec D₁ V₁
  card_D₁ : Nat.card D₁ = 2 ^ 18
  card_V₁ : Nat.card V₁ = 4
  V₁_sq : ∀ v ∈ V₁, v * v = 1
  D₁_nonab : ∃ x ∈ D₁, ∃ y ∈ D₁, x * y ≠ y * x
  K₁_norm : K₁ ≤ normalizer (D₁ : Set G)
  K₁_cent : ∀ k ∈ K₁, ∀ v ∈ V₁, k * v * k⁻¹ = v
  K₁_t : ∀ k ∈ K₁, t * k = k * t
  D₂_comm : ∀ x ∈ D₂, ∀ y ∈ D₂, x * y = y * x
  V₁_le_D₂ : V₁ ≤ D₂
  D₂_norm : D₂ ≤ normalizer (D₁ : Set G)
  t_D₁ : t ∈ normalizer (D₁ : Set G)
  t_D₂ : t ∈ normalizer (D₂ : Set G)
  t_V₁ : t ∈ normalizer (V₁ : Set G)
  card_D₁D₂ : 2 ^ 10 ≤ Nat.card (D₁ ⊓ D₂ : Subgroup G)
  card_D₂ : Nat.card D₂ = 2 ^ 18
  A₁_le : A₁ ≤ D₁
  A₁_t : ∀ a ∈ A₁, t * a = a * t
  D₁_H : ∀ x ∈ D₁, t * x = x * t → x ∈ A₁
  ι_mem : ∀ u, ιG u ∈ A₁
  ι_add : ∀ u v, (ιG u * ιG v)⁻¹ * ιG (u + v) ∈ V₁
  ι_inj : ∀ u, ιG u ∈ V₁ → u = 0
  ι_range : ∀ u, ∃ x ∈ D₁, (t * x * t⁻¹ * x)⁻¹ * ιG u ∈ V₁
  K₁_ι : ∀ k : K₁, ∀ u,
    ((k : G) * ιG u * (k : G)⁻¹)⁻¹ * ιG (((θ k : GL (Fin 8) (ZMod 2)) : Mat8) *ᵥ u) ∈ V₁
  E_mem : ∀ m < 4, ∃ d ∈ D₂, d⁻¹ * ((θ.symm (eSU m) : K₁) : G) ∈ D₁
  ν_norm : ∀ j < 2, ((θ.symm (nuSU j) : K₁) : G) ∈ normalizer (D₂ : Set G)
  W0 : ∀ d ∈ D₂, ∀ x ∈ D₁,
    (∀ m < 4, (((θ.symm (eSU m) : K₁) : G) * x * ((θ.symm (eSU m) : K₁) : G)⁻¹)⁻¹ * x ∈ V₁) →
      (d * x * d⁻¹)⁻¹ * x ∈ V₁
  W1 : ∀ d ∈ D₂, ∀ x ∈ D₁, ∀ m < 4,
    (((θ.symm (eSU m) : K₁) : G) * (d * x * d⁻¹ * x) * ((θ.symm (eSU m) : K₁) : G)⁻¹)⁻¹ *
      (d * x * d⁻¹ * x) ∈ V₁
  D₂_fix : ∀ d ∈ D₂, t * d * t⁻¹ * d⁻¹ ∈ D₁ → ∃ g ∈ E16, d⁻¹ * ((θ.symm g : K₁) : G) ∈ D₁
  D₂_surj : ∀ m < 4, ∃ d ∈ D₂, (d * (t * d * t⁻¹))⁻¹ * ((θ.symm (eSU m) : K₁) : G) ∈ D₁
  Dinj : ∀ d ∈ D₂, (∀ x ∈ D₁, (d * x * d⁻¹)⁻¹ * x ∈ V₁) → d ∈ D₁
  Kr : ∀ x ∈ nOne D₁ K₁ D₂, (∀ y ∈ D₁, (x * y * x⁻¹)⁻¹ * y ∈ V₁) →
    t * x * t⁻¹ * x⁻¹ ∈ D₁ → x ∈ D₁

end Hyp

theorem mem_normalizer_of_conj_eq {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ = x) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx; rwa [hg x hx]
  · intro hx
    have h3 := hg (g * x * g⁻¹) hx
    have h2 : g * x * g⁻¹ = x := by
      have : g * (g * x * g⁻¹) = g * x := by
        calc g * (g * x * g⁻¹) = (g * (g * x * g⁻¹) * g⁻¹) * g := by group
          _ = (g * x * g⁻¹) * g := by rw [h3]
          _ = g * x := by group
      exact mul_left_cancel this
    rwa [h2] at hx

section Derived

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}
variable (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG)
include h

theorem Y13Hyp.D₁_le_nOne : D₁ ≤ nOne D₁ K₁ D₂ := le_sup_left.trans le_sup_left

theorem Y13Hyp.K₁_le_nOne : K₁ ≤ nOne D₁ K₁ D₂ := le_sup_right.trans le_sup_left

theorem Y13Hyp.D₂_le_nOne : D₂ ≤ nOne D₁ K₁ D₂ := le_sup_right

theorem Y13Hyp.nOne_le_normalizer : nOne D₁ K₁ D₂ ≤ normalizer (D₁ : Set G) :=
  sup_le (sup_le le_normalizer h.K₁_norm) h.D₂_norm

theorem Y13Hyp.nOne_le_normalizer_V₁ : nOne D₁ K₁ D₂ ≤ normalizer (V₁ : Set G) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · intro x hx
    exact mem_normalizer_of_conj_eq fun v hv => by
      rw [← h.sec.central v hv x hx, mul_inv_cancel_right]
  · intro k hk
    exact mem_normalizer_of_conj_eq fun v hv => h.K₁_cent k hk v hv
  · intro d hd
    exact mem_normalizer_of_conj_eq fun v hv => by
      rw [h.D₂_comm d hd v (h.V₁_le_D₂ hv), mul_inv_cancel_right]

theorem Y13Hyp.t_mem_normalizer : t ∈ normalizer ((nOne D₁ K₁ D₂ : Subgroup G) : Set G) :=
  mem_normalizer_sup' (mem_normalizer_sup' h.t_D₁ (mem_normalizer_of_conj_eq fun k hk => by
    rw [h.K₁_t k hk, mul_inv_cancel_right])) h.t_D₂

end Derived

section Module

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}
variable [Fact (ElemSec D₁ V₁)] [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal]

@[expose] noncomputable def mkG (D₁ K₁ D₂ : Subgroup G) [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal] :
    nOne D₁ K₁ D₂ →* (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  QuotientGroup.mk' _

@[expose] noncomputable def piG (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) →* (secW D₁ V₁ →ₗ[ZMod 2] secW D₁ V₁) :=
  gamRep (nOne D₁ K₁ D₂) h.nOne_le_normalizer h.nOne_le_normalizer_V₁

theorem piG_mk (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (n : nOne D₁ K₁ D₂) (x : D₁) :
    piG h (mkG D₁ K₁ D₂ n) (secMk x) = secMk (V := V₁) (conjD (D := D₁) n
      (h.nOne_le_normalizer n.2) x) := rfl

@[expose] noncomputable def tauW (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    secW D₁ V₁ →ₗ[ZMod 2] secW D₁ V₁ :=
  secAct t h.t_D₁ h.t_V₁

theorem Y13Hyp.ι_zero (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) : ιG 0 ∈ V₁ := by
  have h1 := h.ι_add 0 0
  rw [add_zero, show (ιG 0 * ιG 0)⁻¹ * ιG 0 = (ιG 0)⁻¹ by group] at h1
  exact inv_mem_iff.mp h1

@[expose] noncomputable def iotaL (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    (Fin 8 → ZMod 2) →ₗ[ZMod 2] secW D₁ V₁ where
  toFun u := secMk ⟨ιG u, h.A₁_le (h.ι_mem u)⟩
  map_add' u v := by
    rw [← secMk_mul, secMk_eq_iff]
    have := V₁.inv_mem (h.ι_add u v)
    simp only [Subgroup.coe_mul]
    convert this using 1
    group
  map_smul' c u := by
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul]
      change secMk ⟨ιG 0, _⟩ = secMk (1 : D₁)
      rw [secMk_eq_iff]
      simpa using V₁.inv_mem h.ι_zero
    · rw [one_smul, RingHom.id_apply, one_smul]

theorem iotaL_apply (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (u : Fin 8 → ZMod 2) :
    iotaL h u = secMk ⟨ιG u, h.A₁_le (h.ι_mem u)⟩ := rfl

theorem iotaL_injective (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) : Function.Injective (iotaL h) := by
  intro u v huv
  have h0 : iotaL h (u + v) = 0 := by rw [map_add, huv, ← two_nsmul, secW_two_nsmul]
  rw [iotaL_apply] at h0
  change secMk ⟨ιG (u + v), _⟩ = secMk (1 : D₁) at h0
  rw [secMk_eq_iff] at h0
  have h1 : u + v = 0 := h.ι_inj (u + v) (by simpa using V₁.inv_mem h0)
  rw [eq_neg_of_add_eq_zero_left h1]
  ext i
  exact ZMod.neg_eq_self_mod_two (v i)

@[expose] noncomputable def kmap (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    K₁ →* (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  (mkG D₁ K₁ D₂).comp (Subgroup.inclusion h.K₁_le_nOne)

theorem piG_kmap_iota (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (k : K₁) (u : Fin 8 → ZMod 2) :
    piG h (kmap h k) (iotaL h u) =
      iotaL h (((θ k : GL (Fin 8) (ZMod 2)) : Mat8) *ᵥ u) := by
  rw [kmap, MonoidHom.comp_apply, iotaL_apply, piG_mk, iotaL_apply, secMk_eq_iff]
  exact h.K₁_ι k u

theorem mat_eq_one_of_mulVec {A : Mat8} (hA : ∀ u, A *ᵥ u = u) : A = 1 := by
  ext i j
  have := congrFun (hA (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at this
  rw [this, Matrix.one_apply]

theorem kmap_injective (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) : Function.Injective (kmap h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker] at hk
  have hkD : ((k : G)) ∈ D₁ := by
    have := (QuotientGroup.eq_one_iff _).mp hk
    rwa [Subgroup.mem_subgroupOf] at this
  have hθ : ∀ u, ((θ k : GL (Fin 8) (ZMod 2)) : Mat8) *ᵥ u = u := by
    intro u
    apply iotaL_injective h
    rw [← piG_kmap_iota, hk, map_one, Module.End.one_apply]
  have h1 : θ k = 1 := Subtype.ext (Units.ext (mat_eq_one_of_mulVec hθ))
  rw [Subgroup.mem_bot, ← θ.map_eq_one_iff, h1]

@[expose] noncomputable def KG (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  (kmap h).range

@[expose] noncomputable def thetaG (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) : KG h ≃* SU42b :=
  (MonoidHom.ofInjective (kmap_injective h)).symm.trans θ

theorem thetaG_symm (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (g : SU42b) :
    (((thetaG h).symm g : KG h) : (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) =
      kmap h (θ.symm g) := rfl

theorem thetaG_apply (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (k : K₁) :
    thetaG h ⟨kmap h k, ⟨k, rfl⟩⟩ = θ k := by
  have : (⟨kmap h k, ⟨k, rfl⟩⟩ : KG h) = (thetaG h).symm (θ k) := by
    apply Subtype.ext
    rw [thetaG_symm, MulEquiv.symm_apply_apply]
  rw [this, MulEquiv.apply_symm_apply]

@[expose] noncomputable def dmap (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    D₂ →* (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  (mkG D₁ K₁ D₂).comp (Subgroup.inclusion h.D₂_le_nOne)

@[expose] noncomputable def DG (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  (dmap h).range

theorem Y13Hyp.t_inv (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right h.t_sq

theorem conjD_t_le (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    D₁.subgroupOf (nOne D₁ K₁ D₂) ≤
      (D₁.subgroupOf (nOne D₁ K₁ D₂)).comap (conjD (D := nOne D₁ K₁ D₂) t h.t_mem_normalizer) := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
  exact (mem_normalizer_iff.mp h.t_D₁ x).mp hx

@[expose] noncomputable def tauG (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) →*
      (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :=
  QuotientGroup.map _ _ (conjD (D := nOne D₁ K₁ D₂) t h.t_mem_normalizer) (conjD_t_le h)

theorem tauG_mk (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (n : nOne D₁ K₁ D₂) :
    tauG h (mkG D₁ K₁ D₂ n) = mkG D₁ K₁ D₂ (conjD t h.t_mem_normalizer n) := rfl

end Module

section R3

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}
variable [Fact (ElemSec D₁ V₁)] [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal]
variable (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG)
include h

theorem Y13Hyp.mkG_eq_iff (n n' : nOne D₁ K₁ D₂) :
    mkG D₁ K₁ D₂ n = mkG D₁ K₁ D₂ n' ↔ (n : G)⁻¹ * n' ∈ D₁ := by
  rw [mkG, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simp

theorem Y13Hyp.card_W : Nat.card (secW D₁ V₁) = 2 ^ 16 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V₁.subgroupOf D₁)
  rw [card_subgroupOf_of_le h.sec.le, h.card_D₁, h.card_V₁] at h1
  change Nat.card (↥D₁ ⧸ V₁.subgroupOf D₁) = 2 ^ 16
  omega

theorem Y13Hyp.r3_fix (u : Fin 8 → ZMod 2) : tauW h (iotaL h u) = iotaL h u := by
  rw [iotaL_apply, tauW, secAct_mk]
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h.A₁_t _ (h.ι_mem u), mul_inv_cancel_right]

theorem Y13Hyp.r3_range (u : Fin 8 → ZMod 2) : ∃ x, tauW h x + x = iotaL h u := by
  obtain ⟨x, hx, hxu⟩ := h.ι_range u
  refine ⟨secMk ⟨x, hx⟩, ?_⟩
  rw [tauW, secAct_mk, ← secMk_mul, iotaL_apply, secMk_eq_iff]
  exact hxu

theorem Y13Hyp.r3_comm (k : KG h) (w : secW D₁ V₁) :
    tauW h (piG h k w) = piG h k (tauW h w) := by
  obtain ⟨_, k₀, rfl⟩ := k
  obtain ⟨x, rfl⟩ := secMk_surjective w
  change secMk _ = secMk _
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_inclusion]
  have hk := h.K₁_t k₀ k₀.2
  calc t * ((k₀ : G) * x * (k₀ : G)⁻¹) * t⁻¹ = (t * k₀) * x * (t * k₀)⁻¹ := by group
    _ = (k₀ * t) * x * (k₀ * t)⁻¹ := by rw [hk]
    _ = (k₀ : G) * (t * x * t⁻¹) * (k₀ : G)⁻¹ := by group

theorem Y13Hyp.r3_ι_eq (k : KG h) (u : Fin 8 → ZMod 2) :
    piG h k (iotaL h u) = iotaL h ((((thetaG h k) : GL (Fin 8) (ZMod 2)) : Mat8) *ᵥ u) := by
  obtain ⟨_, k₀, rfl⟩ := k
  rw [thetaG_apply]
  exact piG_kmap_iota h k₀ u

theorem Y13Hyp.thetaG_symm_mem_DG {g : SU42b} {d : G} (hd : d ∈ D₂)
    (hdg : d⁻¹ * ((θ.symm g : K₁) : G) ∈ D₁) :
    (((thetaG h).symm g : KG h) : (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) =
      dmap h ⟨d, hd⟩ := by
  rw [thetaG_symm, kmap, dmap, MonoidHom.comp_apply, MonoidHom.comp_apply, eq_comm,
    h.mkG_eq_iff]
  exact hdg

theorem Y13Hyp.r3_E_le {m : ℕ} (hm : m < 4) :
    (((thetaG h).symm (eSU m) : KG h) :
      (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) ∈ DG h := by
  obtain ⟨d, hd, hdm⟩ := h.E_mem m hm
  rw [h.thetaG_symm_mem_DG hd hdm]
  exact ⟨_, rfl⟩

theorem Y13Hyp.r3_ν_norm {j : ℕ} (hj : j < 2) {γ} (hγ : γ ∈ DG h) :
    (((thetaG h).symm (nuSU j) : KG h) :
        (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) * γ *
      (((thetaG h).symm (nuSU j) : KG h) :
        (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)))⁻¹ ∈ DG h := by
  obtain ⟨d, rfl⟩ := hγ
  rw [thetaG_symm]
  set ν := θ.symm (nuSU j)
  have hν := h.ν_norm j hj
  refine ⟨⟨(ν : G) * d * (ν : G)⁻¹, (mem_normalizer_iff.mp hν d).mp d.2⟩, ?_⟩
  rw [dmap, kmap, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv,
    ← map_mul, ← map_mul]
  rfl

theorem Y13Hyp.r3_πτ (g : ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :
    piG h (tauG h g) = tauW h ∘ₗ piG h g ∘ₗ tauW h := by
  induction g using QuotientGroup.induction_on with | H n => ?_
  apply LinearMap.ext
  intro w
  obtain ⟨x, rfl⟩ := secMk_surjective w
  change secMk _ = secMk _
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, _root_.mul_inv_rev, h.t_inv]
  group

theorem Y13Hyp.r3_ττ (g : ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)) :
    tauG h (tauG h g) = g := by
  induction g using QuotientGroup.induction_on with | H n => ?_
  change mkG D₁ K₁ D₂ _ = mkG D₁ K₁ D₂ n
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  have ht := h.t_sq
  calc t * (t * (n : G) * t⁻¹) * t⁻¹ = (t * t) * n * (t * t)⁻¹ := by group
    _ = n := by rw [ht]; group

theorem Y13Hyp.r3_τK {γ} (hγ : γ ∈ KG h) : tauG h γ = γ := by
  obtain ⟨k, rfl⟩ := hγ
  rw [kmap, MonoidHom.comp_apply, tauG_mk]
  congr 1
  apply Subtype.ext
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_inclusion]
  rw [h.K₁_t k k.2, mul_inv_cancel_right]

theorem Y13Hyp.r3_τD {γ} (hγ : γ ∈ DG h) : tauG h γ ∈ DG h := by
  obtain ⟨d, rfl⟩ := hγ
  refine ⟨⟨t * d * t⁻¹, (mem_normalizer_iff.mp h.t_D₂ d).mp d.2⟩, ?_⟩
  rw [dmap, MonoidHom.comp_apply, MonoidHom.comp_apply, tauG_mk]
  rfl

theorem Y13Hyp.piG_dmap (d : D₂) (x : D₁) :
    piG h (dmap h d) (secMk x) = secMk (V := V₁) (conjD (D := D₁) d (h.D₂_norm d.2) x) := rfl

theorem Y13Hyp.piG_kmap (k : K₁) (x : D₁) :
    piG h (kmap h k) (secMk x) = secMk (V := V₁) (conjD (D := D₁) k (h.K₁_norm k.2) x) := rfl

theorem Y13Hyp.r3_W0 {γ} (hγ : γ ∈ DG h) (w : secW D₁ V₁)
    (hw : ∀ m < 4, piG h (((thetaG h).symm (eSU m) : KG h) :
      (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) w = w) : piG h γ w = w := by
  obtain ⟨d, rfl⟩ := hγ
  obtain ⟨x, rfl⟩ := secMk_surjective w
  rw [h.piG_dmap, secMk_eq_iff]
  refine h.W0 d d.2 x x.2 fun m hm => ?_
  have := hw m hm
  rw [thetaG_symm, h.piG_kmap, secMk_eq_iff] at this
  exact this

theorem Y13Hyp.r3_W1 {γ} (hγ : γ ∈ DG h) (w : secW D₁ V₁) {m : ℕ} (hm : m < 4) :
    piG h (((thetaG h).symm (eSU m) : KG h) :
      (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) (piG h γ w + w) = piG h γ w + w := by
  obtain ⟨d, rfl⟩ := hγ
  obtain ⟨x, rfl⟩ := secMk_surjective w
  rw [h.piG_dmap, ← secMk_mul, thetaG_symm, h.piG_kmap, secMk_eq_iff]
  exact h.W1 d d.2 x x.2 m hm

theorem Y13Hyp.r3_Dinj {γ} (hγ : γ ∈ DG h) (hπ : piG h γ = 1) : γ = 1 := by
  obtain ⟨d, rfl⟩ := hγ
  have hd : (d : G) ∈ D₁ := by
    refine h.Dinj d d.2 fun x hx => ?_
    have := LinearMap.congr_fun hπ (secMk ⟨x, hx⟩)
    rw [h.piG_dmap, Module.End.one_apply, secMk_eq_iff] at this
    exact this
  rw [dmap, MonoidHom.comp_apply, ← map_one (mkG D₁ K₁ D₂), h.mkG_eq_iff]
  simpa using hd

theorem Y13Hyp.r3_Kr (g : ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))
    (hπ : piG h g = 1) (hτ : tauG h g = g) : g = 1 := by
  induction g using QuotientGroup.induction_on with | H n => ?_
  have hn : (n : G) ∈ D₁ := by
    refine h.Kr n n.2 (fun y hy => ?_) ?_
    · have := LinearMap.congr_fun hπ (secMk ⟨y, hy⟩)
      rw [show ((n : ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) = mkG D₁ K₁ D₂ n from rfl,
        piG_mk, Module.End.one_apply, secMk_eq_iff] at this
      exact this
    · have h1 : mkG D₁ K₁ D₂ (conjD t h.t_mem_normalizer n) = mkG D₁ K₁ D₂ n := hτ
      rw [h.mkG_eq_iff] at h1
      have h2 := (mem_normalizer_iff.mp (h.nOne_le_normalizer n.2) _).mp (D₁.inv_mem h1)
      simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk] at h2
      convert h2 using 1
      group
  change mkG D₁ K₁ D₂ n = mkG D₁ K₁ D₂ 1
  rw [h.mkG_eq_iff]
  simpa using hn

theorem Y13Hyp.tauG_dmap (d : D₂) :
    tauG h (dmap h d) = dmap h ⟨t * d * t⁻¹, (mem_normalizer_iff.mp h.t_D₂ d).mp d.2⟩ := rfl

theorem Y13Hyp.r3_τfix {γ} (hγ : γ ∈ DG h) (hfix : tauW h ∘ₗ piG h γ ∘ₗ tauW h = piG h γ) :
    ∃ g ∈ E16, piG h γ = piG h (((thetaG h).symm g : KG h) :
      (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) := by
  rw [← h.r3_πτ] at hfix
  have hτ : tauG h γ = γ := by
    have h1 : piG h (tauG h γ * γ⁻¹) = 1 := by
      rw [map_mul, hfix, ← map_mul, mul_inv_cancel, map_one]
    have h2 := h.r3_Dinj (mul_mem (h.r3_τD hγ) (inv_mem hγ)) h1
    exact mul_inv_eq_one.mp h2
  obtain ⟨d, rfl⟩ := hγ
  rw [h.tauG_dmap, dmap, MonoidHom.comp_apply, MonoidHom.comp_apply, h.mkG_eq_iff] at hτ
  have hd : t * d * t⁻¹ * (d : G)⁻¹ ∈ D₁ := by
    have h2 := (mem_normalizer_iff.mp (h.D₂_norm d.2) _).mp (D₁.inv_mem hτ)
    convert h2 using 1
    simp only [Subgroup.coe_inclusion]
    group
  obtain ⟨g, hg, hdg⟩ := h.D₂_fix d d.2 hd
  exact ⟨g, hg, by rw [h.thetaG_symm_mem_DG d.2 hdg]⟩

theorem Y13Hyp.r3_τsurj {m : ℕ} (hm : m < 4) :
    ∃ γ ∈ DG h, piG h γ ∘ₗ tauW h ∘ₗ piG h γ ∘ₗ tauW h = piG h (((thetaG h).symm (eSU m) : KG h) :
      (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) := by
  obtain ⟨d, hd, hdm⟩ := h.D₂_surj m hm
  refine ⟨dmap h ⟨d, hd⟩, ⟨_, rfl⟩, ?_⟩
  rw [← h.r3_πτ, ← Module.End.mul_eq_comp, ← map_mul, h.tauG_dmap, ← map_mul,
    h.thetaG_symm_mem_DG (d := d * (t * d * t⁻¹))
      (mul_mem hd ((mem_normalizer_iff.mp h.t_D₂ d).mp hd)) hdm]
  rfl

theorem Y13Hyp.r3_D_card [Finite G] : Nat.card (DG h) ≤ 2 ^ 8 := by
  have hker : (dmap h).ker = D₁.subgroupOf D₂ := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, dmap, MonoidHom.comp_apply,
      ← map_one (mkG D₁ K₁ D₂), h.mkG_eq_iff]
    simp
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (dmap h).ker
  have hk : Nat.card (D₁.subgroupOf D₂) = Nat.card (D₁ ⊓ D₂ : Subgroup G) := by
    have := card_subgroupOf_of_le (G := G) (H := D₁ ⊓ D₂) (K := D₂) inf_le_right
    rwa [Subgroup.inf_subgroupOf_right] at this
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (dmap h)).toEquiv, hker, h.card_D₂,
    hk] at hcard
  have h10 := h.card_D₁D₂
  change Nat.card (dmap h).range ≤ 2 ^ 8
  have hpos : 0 < Nat.card (D₁ ⊓ D₂ : Subgroup G) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : 2 ^ 8 * 2 ^ 10 < Nat.card (dmap h).range * Nat.card (D₁ ⊓ D₂ : Subgroup G) :=
    Nat.mul_lt_mul_of_lt_of_le hlt h10 (by positivity)
  omega

theorem Y13Hyp.r3_gen : KG h ⊔ DG h = ⊤ := by
  set S : Subgroup (nOne D₁ K₁ D₂) := (KG h ⊔ DG h).comap (mkG D₁ K₁ D₂)
  have hD₁ : D₁.subgroupOf (nOne D₁ K₁ D₂) ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    have : mkG D₁ K₁ D₂ x = 1 := by
      rw [← map_one (mkG D₁ K₁ D₂), h.mkG_eq_iff]
      simpa using Subgroup.mem_subgroupOf.mp hx
    rw [this]; exact one_mem _
  have hK₁ : K₁.subgroupOf (nOne D₁ K₁ D₂) ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_left ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hD₂ : D₂.subgroupOf (nOne D₁ K₁ D₂) ≤ S := by
    intro x hx
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_sup_right ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have hcl : nOne D₁ K₁ D₂ = Subgroup.closure ((D₁ : Set G) ∪ K₁ ∪ D₂) := by
    rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      Subgroup.closure_eq]
    rfl
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' := hx
    rw [hcl] at hx'
    refine Subgroup.closure_induction (p := fun y _ => ∀ hy : y ∈ nOne D₁ K₁ D₂, ⟨y, hy⟩ ∈ S)
      ?_ ?_ ?_ ?_ hx' hx
    · rintro y ((hy | hy) | hy) hy'
      · exact hD₁ (Subgroup.mem_subgroupOf.mpr hy)
      · exact hK₁ (Subgroup.mem_subgroupOf.mpr hy)
      · exact hD₂ (Subgroup.mem_subgroupOf.mpr hy)
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

theorem Y13Hyp.piG_kmap_eq (k : K₁) :
    piG h (kmap h k) = secAct (D := D₁) (V := V₁) k (h.K₁_norm k.2)
      (h.nOne_le_normalizer_V₁ (h.K₁_le_nOne k.2)) := rfl

theorem Y13Hyp.piG_dmap_eq (d : D₂) :
    piG h (dmap h d) = secAct (D := D₁) (V := V₁) d (h.D₂_norm d.2)
      (h.nOne_le_normalizer_V₁ (h.D₂_le_nOne d.2)) := rfl

theorem Y13Hyp.r3Hyp [Finite G] (fV : V₁ →* Multiplicative (ZMod 2))
    (hfV : ∃ x y : D₁, fV (secComm x y) ≠ 1) :
    R3Hyp (piG h) (KG h) (thetaG h) (tauW h) (iotaL h) (DG h) (secForm fV) (tauG h) where
  inj := iotaL_injective h
  fix := h.r3_fix
  range := h.r3_range
  card := h.card_W
  comm := h.r3_comm
  ι_eq := h.r3_ι_eq
  D_card := h.r3_D_card
  E_le := fun _ hm => h.r3_E_le hm
  ν_norm := fun _ hj _ hd => h.r3_ν_norm hj hd
  W0 := fun _ hd x hx => h.r3_W0 hd x hx
  W1 := fun _ hd x _ hm => h.r3_W1 hd x hm
  τfix := fun _ hd hfix => h.r3_τfix hd hfix
  τsurj := fun _ hm => h.r3_τsurj hm
  B0 := by
    intro h0
    obtain ⟨x, y, hxy⟩ := hfV
    have := LinearMap.congr_fun (LinearMap.congr_fun h0 (secMk x)) (secMk y)
    rw [secForm_mk, LinearMap.zero_apply, LinearMap.zero_apply] at this
    exact hxy (by rw [← ofAdd_toAdd (fV (secComm x y)), this]; rfl)
  Balt := secForm_self fV
  BK := by
    rintro ⟨_, k, rfl⟩ x y
    change secForm fV (piG h (kmap h k) x) (piG h (kmap h k) y) = _
    rw [h.piG_kmap_eq]
    exact secForm_secAct fV _ _ _ (fun v hv => h.K₁_cent k k.2 v hv) x y
  BD := by
    rintro _ ⟨d, rfl⟩ x y
    rw [h.piG_dmap_eq]
    exact secForm_secAct fV _ _ _ (fun v hv => by
      rw [h.D₂_comm d d.2 v (h.V₁_le_D₂ hv), mul_inv_cancel_right]) x y
  gen := h.r3_gen
  ττ := h.r3_ττ
  πτ := h.r3_πτ
  τK := fun _ hk => h.r3_τK hk
  τD := fun _ hd => h.r3_τD hd
  Dinj := fun _ hd hπ => h.r3_Dinj hd hπ
  Kr := fun g hπ hτ => h.r3_Kr g hπ hτ

end R3

section Back

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}
variable [Fact (ElemSec D₁ V₁)] [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal]
variable (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG)
include h

theorem Y13Hyp.tauG_mk_eq (n : nOne D₁ K₁ D₂) (hn : (n : G)⁻¹ * (t * n * t⁻¹) ∈ D₁) :
    tauG h (mkG D₁ K₁ D₂ n) = mkG D₁ K₁ D₂ n := by
  rw [tauG_mk, h.mkG_eq_iff]
  have := D₁.inv_mem hn
  simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
  convert this using 1
  group

theorem Y13Hyp.centralizer₁
    (hfix : ∀ γ : ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂), tauG h γ = γ → γ ∈ KG h)
    {x : G} (hx : x ∈ nOne D₁ K₁ D₂) (hxt : x⁻¹ * (t * x * t⁻¹) ∈ D₁) :
    ∃ k ∈ K₁, k⁻¹ * x ∈ D₁ := by
  obtain ⟨k, hk⟩ := hfix _ (h.tauG_mk_eq ⟨x, hx⟩ hxt)
  rw [kmap, MonoidHom.comp_apply, h.mkG_eq_iff] at hk
  exact ⟨k, k.2, hk⟩

@[expose] noncomputable def preG (D₁ K₁ D₂ : Subgroup G) [(D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal]
    (X : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) : Subgroup G :=
  (X.comap (mkG D₁ K₁ D₂)).map (nOne D₁ K₁ D₂).subtype

omit [Fact (ElemSec D₁ V₁)] in
omit h in
theorem mem_preG {X : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))} {y : G} :
    y ∈ preG D₁ K₁ D₂ X ↔ ∃ hy : y ∈ nOne D₁ K₁ D₂, mkG D₁ K₁ D₂ ⟨y, hy⟩ ∈ X := by
  constructor
  · rintro ⟨⟨y, hy⟩, hX, rfl⟩
    exact ⟨hy, hX⟩
  · rintro ⟨hy, hX⟩
    exact ⟨⟨y, hy⟩, hX, rfl⟩

theorem Y13Hyp.D₁_le_preG (X : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) :
    D₁ ≤ preG D₁ K₁ D₂ X := by
  intro x hx
  rw [mem_preG]
  refine ⟨h.D₁_le_nOne hx, ?_⟩
  have : mkG D₁ K₁ D₂ ⟨x, h.D₁_le_nOne hx⟩ = 1 := by
    rw [← map_one (mkG D₁ K₁ D₂), h.mkG_eq_iff]
    simpa using hx
  rw [this]; exact one_mem _

omit [Fact (ElemSec D₁ V₁)] in
omit h in
theorem preG_le (X : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) :
    preG D₁ K₁ D₂ X ≤ nOne D₁ K₁ D₂ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem Y13Hyp.conjR_preG (X : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) :
    CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR (preG D₁ K₁ D₂ X) t =
      preG D₁ K₁ D₂ (X.map (tauG h)) := by
  ext y
  rw [CFSG.EvenSmallLie.UnitarySix.YamadaEnd.mem_conjR, mem_preG, mem_preG]
  constructor
  · rintro ⟨hy, hX⟩
    have hy' : y ∈ nOne D₁ K₁ D₂ := by
      have := (mem_normalizer_iff.mp h.t_mem_normalizer y).mpr hy
      exact this
    refine ⟨hy', ⟨_, hX, ?_⟩⟩
    rw [tauG_mk]
    congr 1
    apply Subtype.ext
    simp only [conjD, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [h.t_inv]
    have ht := h.t_sq
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht]; group
  · rintro ⟨hy, ⟨m, hm, hmy⟩⟩
    have hty : t * y * t⁻¹ ∈ nOne D₁ K₁ D₂ := (mem_normalizer_iff.mp h.t_mem_normalizer y).mp hy
    refine ⟨hty, ?_⟩
    have h1 : tauG h (mkG D₁ K₁ D₂ ⟨y, hy⟩) = m := by rw [← hmy, h.r3_ττ]
    rw [tauG_mk] at h1
    rw [← h1] at hm
    exact hm

omit [Fact (ElemSec D₁ V₁)] in
omit h in
theorem preG_sup (X Y : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂))) :
    preG D₁ K₁ D₂ (X ⊔ Y) = preG D₁ K₁ D₂ X ⊔ preG D₁ K₁ D₂ Y := by
  have hs : Function.Surjective (mkG D₁ K₁ D₂) := QuotientGroup.mk'_surjective _
  rw [preG, preG, preG, ← Subgroup.comap_sup_eq (mkG D₁ K₁ D₂) X Y hs, Subgroup.map_sup]

omit [Fact (ElemSec D₁ V₁)] in
omit h in
theorem preG_top : preG D₁ K₁ D₂ ⊤ = nOne D₁ K₁ D₂ := by
  rw [preG, Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem Y13Hyp.mem_D₁_of_mkG_eq_one {y : G} (hy : y ∈ nOne D₁ K₁ D₂)
    (h1 : mkG D₁ K₁ D₂ ⟨y, hy⟩ = 1) : y ∈ D₁ := by
  rw [← map_one (mkG D₁ K₁ D₂), h.mkG_eq_iff] at h1
  simpa using h1

theorem Y13Hyp.unitary_back (X : Subgroup (↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂)))
    (h1 : X ⊔ X.map (tauG h) = ⊤) (h2 : ⁅X, X.map (tauG h)⁆ = ⊥) (h3 : X ⊓ X.map (tauG h) = ⊥)
    (h4 : CFSG.Blueprint.LieModel X .PSU 4 2 1) :
    ∃ M : Subgroup G, D₁ ≤ M ∧ M ≤ nOne D₁ K₁ D₂ ∧
      nOne D₁ K₁ D₂ = M ⊔ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t ∧
      ⁅M, CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t⁆ ≤ D₁ ∧
      M ⊓ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t = D₁ ∧
      ∃ _ : (D₁.subgroupOf M).Normal, CFSG.Blueprint.LieModel (M ⧸ D₁.subgroupOf M) .PSU 4 2 1 := by
  set M := preG D₁ K₁ D₂ X
  have hMt := h.conjR_preG X
  refine ⟨M, h.D₁_le_preG X, preG_le X, ?_, ?_, ?_, ?_⟩
  · rw [hMt, ← preG_sup, h1, preG_top]
  · rw [hMt, Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_preG] at ha hb
    obtain ⟨ha, haX⟩ := ha
    obtain ⟨hb, hbX⟩ := hb
    have hc : ⁅a, b⁆ ∈ nOne D₁ K₁ D₂ := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    refine h.mem_D₁_of_mkG_eq_one hc ?_
    have hmk : mkG D₁ K₁ D₂ ⟨⁅a, b⁆, hc⟩ =
        ⁅mkG D₁ K₁ D₂ ⟨a, ha⟩, mkG D₁ K₁ D₂ ⟨b, hb⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [hmk, ← Subgroup.mem_bot, ← h2]
    exact Subgroup.commutator_mem_commutator haX hbX
  · rw [hMt]
    apply le_antisymm
    · intro y hy
      obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp hy
      rw [mem_preG] at hy₁ hy₂
      obtain ⟨hy, hyX⟩ := hy₁
      obtain ⟨hy', hyX'⟩ := hy₂
      refine h.mem_D₁_of_mkG_eq_one hy ?_
      rw [← Subgroup.mem_bot, ← h3]
      exact ⟨hyX, hyX'⟩
    · exact le_inf (h.D₁_le_preG X) (h.D₁_le_preG _)
  · have hN : (D₁.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (h.D₁_le_preG X)).mpr
        ((preG_le X).trans h.nOne_le_normalizer)
    refine ⟨hN, ?_⟩
    have hmemX : ∀ m : M, mkG D₁ K₁ D₂ ⟨m, preG_le X m.2⟩ ∈ X := fun m => by
      obtain ⟨hm, hmX⟩ := mem_preG.mp m.2
      exact hmX
    let φ : M →* X :=
      { toFun := fun m => ⟨mkG D₁ K₁ D₂ ⟨m, preG_le X m.2⟩, hmemX m⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul (mkG D₁ K₁ D₂) ⟨a, _⟩ ⟨b, _⟩) }
    have hsurj : Function.Surjective φ := by
      rintro ⟨x, hx⟩
      obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨⟨n, mem_preG.mpr ⟨n.2, hx⟩⟩, rfl⟩
    have hker : φ.ker = D₁.subgroupOf M := by
      ext m
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hm
        exact h.mem_D₁_of_mkG_eq_one _ (congrArg Subtype.val hm)
      · intro hm
        apply Subtype.ext
        change mkG D₁ K₁ D₂ ⟨m, _⟩ = 1
        rw [← map_one (mkG D₁ K₁ D₂), h.mkG_eq_iff]
        simpa using hm
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)).symm h4

end Back

section Main

variable {G : Type} [Group G] {t : G} {D₁ V₁ A₁ K₁ D₂ : Subgroup G} {θ : K₁ ≃* SU42b}
  {ιG : (Fin 8 → ZMod 2) → G}

open scoped MatrixGroups

theorem Y13Hyp.exists_fV [Fact (ElemSec D₁ V₁)] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) :
    ∃ fV : V₁ →* Multiplicative (ZMod 2), ∃ x y : D₁, fV (secComm x y) ≠ 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h.D₁_nonab
  have hc : x * y * x⁻¹ * y⁻¹ ∈ V₁ := h.sec.comm x hx y hy
  have hc1 : x * y * x⁻¹ * y⁻¹ ≠ 1 := fun h1 => hxy (by
    have := congrArg (· * y * x) h1
    simpa [mul_assoc] using this)
  obtain ⟨fV, hfV⟩ := exists_hom_ne_one (E := V₁)
    (fun a ha b hb => h.D₂_comm a (h.V₁_le_D₂ ha) b (h.V₁_le_D₂ hb)) h.V₁_sq hc hc1
  exact ⟨fV, ⟨x, hx⟩, ⟨y, hy⟩, hfV⟩

theorem Y13Hyp.main [Finite G] (h : Y13Hyp t D₁ V₁ A₁ K₁ D₂ θ ιG) (F : Type) [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    D₁ ≤ nOne D₁ K₁ D₂ ∧ nOne D₁ K₁ D₂ ≤ normalizer (D₁ : Set G) ∧
      t ∈ normalizer ((nOne D₁ K₁ D₂ : Subgroup G) : Set G) ∧
      (∀ x ∈ nOne D₁ K₁ D₂, x⁻¹ * (t * x * t⁻¹) ∈ D₁ → x ∈ K₁ ⊔ D₁) ∧
      nOne D₁ K₁ D₂ ⊓ centralizer ({t} : Set G) = K₁ ⊔ A₁ ∧
      ((∃ _ : (D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal,
          ∃ ψ : SL(4, F) →* ↥(nOne D₁ K₁ D₂) ⧸ D₁.subgroupOf (nOne D₁ K₁ D₂),
            Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) ∨
        ∃ M : Subgroup G, D₁ ≤ M ∧ M ≤ nOne D₁ K₁ D₂ ∧
          nOne D₁ K₁ D₂ = M ⊔ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t ∧
          ⁅M, CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t⁆ ≤ D₁ ∧
          M ⊓ CFSG.EvenSmallLie.UnitarySix.YamadaEnd.conjR M t = D₁ ∧
          ∃ _ : (D₁.subgroupOf M).Normal,
            CFSG.Blueprint.LieModel (M ⧸ D₁.subgroupOf M) .PSU 4 2 1) := by
  have : Fact (ElemSec D₁ V₁) := ⟨h.sec⟩
  have hN : (D₁.subgroupOf (nOne D₁ K₁ D₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.D₁_le_nOne).mpr h.nOne_le_normalizer
  obtain ⟨fV, hfV⟩ := h.exists_fV
  have hR := h.r3Hyp fV hfV
  obtain ⟨hfix, hcase⟩ := hR.main_factor F hF
  have hcent : ∀ x ∈ nOne D₁ K₁ D₂, x⁻¹ * (t * x * t⁻¹) ∈ D₁ → ∃ k ∈ K₁, k⁻¹ * x ∈ D₁ :=
    fun x hx hxt => h.centralizer₁ hfix hx hxt
  refine ⟨h.D₁_le_nOne, h.nOne_le_normalizer, h.t_mem_normalizer, fun x hx hxt => ?_, ?_, ?_⟩
  · obtain ⟨k, hk, hkx⟩ := hcent x hx hxt
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hkx)
  · apply le_antisymm
    · rintro x ⟨hx, hxt⟩
      have hxt' : t * x = x * t := (Subgroup.mem_centralizer_singleton_iff.mp hxt).symm
      obtain ⟨k, hk, hkx⟩ := hcent x hx (by
        rw [show t * x * t⁻¹ = x by rw [hxt', mul_inv_cancel_right], inv_mul_cancel]
        exact one_mem _)
      have hkt : t * k⁻¹ = k⁻¹ * t := by
        have := h.K₁_t k hk
        calc t * k⁻¹ = k⁻¹ * (k * t) * k⁻¹ := by group
          _ = k⁻¹ * (t * k) * k⁻¹ := by rw [this]
          _ = k⁻¹ * t := by group
      have hd : k⁻¹ * x ∈ A₁ := h.D₁_H _ hkx (by
        rw [← mul_assoc, hkt, mul_assoc, hxt', mul_assoc])
      have : x = k * (k⁻¹ * x) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hd)
    · refine sup_le (fun k hk => Subgroup.mem_inf.mpr ⟨h.K₁_le_nOne hk,
        Subgroup.mem_centralizer_singleton_iff.mpr (h.K₁_t k hk).symm⟩) (fun a ha =>
        Subgroup.mem_inf.mpr ⟨h.D₁_le_nOne (h.A₁_le ha),
          Subgroup.mem_centralizer_singleton_iff.mpr (h.A₁_t a ha).symm⟩)
  · rcases hcase with hL | ⟨X, h1, h2, h3, h4⟩
    · exact Or.inl ⟨hN, hL⟩
    · exact Or.inr (h.unitary_back X h1 h2 h3 h4)

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
