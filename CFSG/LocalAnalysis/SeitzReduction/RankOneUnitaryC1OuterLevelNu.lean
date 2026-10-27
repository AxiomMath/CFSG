module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelNuBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterStepLevel

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

theorem U3Start.outerNu_mem_T {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
    {T : Subgroup G} (h : U3Start G L f t T) {S : Subgroup G} (hTS : T ≤ S) (hS2 : IsPGroup 2 S)
    {s : G} (hs : s ∈ S) (hst : s * t = t * s) : s ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := h.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  have hH : T ⊔ zpowers s ≤ centralizer ({t} : Set G) :=
    sup_le h.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hst))
  have hHS : T ⊔ zpowers s ≤ S := sup_le hTS (zpowers_le.mpr hs)
  have heq := hTsyl.eq_of_le le_sup_left hH (hS2.to_le hHS)
  rw [← heq]
  exact mem_sup_right (mem_zpowers s)

namespace U3C1OuterStage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Nu

variable (h : U3C1OuterStage G L f t T d V U U₁ k)
include h

theorem outerNu_exists_mul_V₁ (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    {z : G} (hz : z ∈ U₁) :
    ∃ y ∈ szT₁ L T, ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), z = y * w := by
  have hTN : szT₁ L T ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => by
      rw [mem_centralizer_iff.mp (mem_inf.mp hw).2 _ (inv_mem hy), inv_mul_cancel_right]
      exact hw
  have hz' : z ∈ ((szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G) := by
    rw [← hlam]
    exact hz
  rw [coe_mul_of_left_le_normalizer_right _ _ hTN] at hz'
  obtain ⟨y, hy, w, hw, rfl⟩ := hz'
  exact ⟨y, hy, w, hw, rfl⟩

theorem outerNu_commute_of_sq (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {c w : G}
    (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) {y r : G}
    (hy : y ∈ szT₁ L T) (hr : r ∈ V) (hr2 : r ^ 2 = y⁻¹ * c * y * c⁻¹) :
    c * w * t * (y * r) = y * r * (c * w * t) := by
  have e1 : t * y = y * t := (h.t_comm hy).symm
  have e2 : w * y = y * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 y hy).symm
  have e3 : w * r⁻¹ = r⁻¹ * w := h.V₁_comm hμV hlam w hw _ (h.V_le_V₁ (inv_mem hr))
  have e4 : c * r⁻¹ = r⁻¹ * c := h.V_comm (inv_mem hr) hc
  have e5 : t * r = r⁻¹ * t := h.t_mul_of_mem hr
  have hcy : c * y * c⁻¹ = y * r ^ 2 := by rw [hr2]; group
  calc c * w * t * (y * r) = c * w * (t * y) * r := by group
    _ = c * w * (y * t) * r := by rw [e1]
    _ = c * (w * y) * (t * r) := by group
    _ = c * (y * w) * (r⁻¹ * t) := by rw [e2, e5]
    _ = c * y * (w * r⁻¹) * t := by group
    _ = c * y * (r⁻¹ * w) * t := by rw [e3]
    _ = c * y * c⁻¹ * (c * r⁻¹) * w * t := by group
    _ = c * y * c⁻¹ * (r⁻¹ * c) * w * t := by rw [e4]
    _ = c * y * c⁻¹ * r⁻¹ * (c * w * t) := by group
    _ = y * r ^ 2 * r⁻¹ * (c * w * t) := by rw [hcy]
    _ = y * r * (c * w * t) := by group

theorem outerNu_exists_sq {c y : G} (hc : c ∈ szT₁ L T) (hy : y ∈ szT₁ L T) :
    ∃ r ∈ V, r ^ 2 = y⁻¹ * c * y * c⁻¹ := by
  have hA : y⁻¹ * c * y * c⁻¹ ∈ szA₁ (szT₁ L T) := by
    have := h.comm_T₁_mem (inv_mem hy) hc
    rwa [inv_inv] at this
  have h2 : (y⁻¹ * c * y * c⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.one_le; omega⟩
    rw [hj, pow_succ', pow_mul,
      (h.start.facts_of_card_sylow h.card_sylow).2.2.2.2.2.1 _ hA, one_pow]
  obtain ⟨r, hr, hre⟩ := SzC1.exists_sq_eq_of_pow_eq_one h.comm h.omega h.pow
    (by rw [h.card_szA₁, h.card]) (h.le hA) h2
  exact ⟨r, hr, hre.symm⟩

theorem outerNu_mem_szA₁_of_comm_t (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {r : G}
    (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hrt : r * t = t * r) :
    r ∈ szA₁ (szT₁ L T) :=
  h.start.outerStep_mem_szA₁_of_conj_eq h.card_sylow h.one_le (h.V₁_comm hμV hlam) h.pow
    (h.card_V₁ hlam) (fun u hu => h.sq_mem_V (mem_inf.mp hu).1)
    (fun u hu hu2 => h.omega_V₁ hμV hu hu2) h.inv hr (by rw [← hrt, mul_inv_cancel_right])

theorem outerNu_mem_szA₁_of_central (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {c w : G}
    (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) {z : G} (hz : z ∈ U₁)
    (hzx : c * w * t * z = z * (c * w * t))
    (hcen : ∀ y ∈ szT₁ L T, ∀ r ∈ V, r ^ 2 = y⁻¹ * c * y * c⁻¹ → z * (y * r) = y * r * z) :
    z ∈ szA₁ (szT₁ L T) := by
  have hV₁c := h.V₁_comm hμV hlam
  obtain ⟨y', hy', r', hr', rfl⟩ := h.outerNu_exists_mul_V₁ hlam hz
  have hy'A : y' ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy', mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨r, hr, hr2⟩ := h.outerNu_exists_sq hc hy
    have e := hcen y hy r hr hr2
    have e1 : r' * y = y * r' := (mem_centralizer_iff.mp (mem_inf.mp hr').2 y hy).symm
    have e2 : r * y' = y' * r := h.V_comm hr hy' |>.symm
    have e3 : r' * r = r * r' := hV₁c r' hr' r (h.V_le_V₁ hr)
    have e4 : y' * y * (r' * r) = y * y' * (r' * r) := by
      calc y' * y * (r' * r) = y' * (r' * y) * r := by rw [e1]; group
        _ = y' * r' * (y * r) := by group
        _ = y * r * (y' * r') := e
        _ = y * (r * y') * r' := by group
        _ = y * (y' * r) * r' := by rw [e2]
        _ = y * y' * (r * r') := by group
        _ = y * y' * (r' * r) := by rw [e3]
    exact (mul_right_cancel e4).symm
  have hy'x : c * w * t * y' = y' * (c * w * t) := by
    have e1 : c * y' = y' * c := (mem_centralizer_iff.mp (mem_szA₁.mp hy'A).2 c hc)
    have e2 : w * y' = y' * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 y' hy').symm
    have e3 : t * y' = y' * t := (h.t_comm hy').symm
    calc c * w * t * y' = c * w * (t * y') := by group
      _ = c * (w * y') * t := by rw [e3]; group
      _ = (c * y') * w * t := by rw [e2]; group
      _ = y' * (c * w * t) := by rw [e1]; group
  have hr'x : c * w * t * r' = r' * (c * w * t) := by
    have e : y' * (c * w * t * r') = y' * (r' * (c * w * t)) := by
      calc y' * (c * w * t * r') = (y' * (c * w * t)) * r' := by group
        _ = (c * w * t * y') * r' := by rw [hy'x]
        _ = c * w * t * (y' * r') := by group
        _ = y' * r' * (c * w * t) := hzx
        _ = y' * (r' * (c * w * t)) := by group
    exact mul_left_cancel e
  have hr't : r' * t = t * r' := by
    have e1 : r' * c = c * r' := (mem_centralizer_iff.mp (mem_inf.mp hr').2 c hc).symm
    have e2 : r' * w = w * r' := hV₁c r' hr' w hw
    have e : c * w * (t * r') = c * w * (r' * t) := by
      calc c * w * (t * r') = c * w * t * r' := by group
        _ = r' * (c * w * t) := hr'x
        _ = (r' * c) * w * t := by group
        _ = c * (r' * w) * t := by rw [e1]; group
        _ = c * w * (r' * t) := by rw [e2]; group
    exact (mul_left_cancel e).symm
  exact mul_mem hy'A (h.outerNu_mem_szA₁_of_comm_t hμV hlam hr' hr't)

theorem outerNu_commute_szA₁ {c w : G} (hc : c ∈ szT₁ L T)
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) {a : G} (ha : a ∈ szA₁ (szT₁ L T)) :
    c * w * t * a = a * (c * w * t) := by
  have haT := szA₁_le _ ha
  have e1 : c * a = a * c := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 c hc
  have e2 : w * a = a * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 a haT).symm
  have e3 : t * a = a * t := (h.t_comm haT).symm
  calc c * w * t * a = c * w * (t * a) := by group
    _ = c * w * (a * t) := by rw [e3]
    _ = c * (w * a) * t := by group
    _ = c * (a * w) * t := by rw [e2]
    _ = (c * a) * w * t := by group
    _ = (a * c) * w * t := by rw [e1]
    _ = a * (c * w * t) := by group

theorem outerNu_card_le_centralizer (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {c w : G}
    (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    (2 ^ f) ^ 3 ≤ Nat.card (U₁ ⊓ centralizer ({c * w * t} : Set G) : Subgroup G) := by
  set C : Subgroup G := U₁ ⊓ centralizer ({c * w * t} : Set G) with hC
  have hmem : ∀ y ∈ szT₁ L T, ∀ r ∈ V, r ^ 2 = y⁻¹ * c * y * c⁻¹ → y * r ∈ C := by
    intro y hy r hr hr2
    refine mem_inf.mpr ⟨h.sup_le_U₁ (mul_mem (mem_sup_left hy) (mem_sup_right hr)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact (h.outerNu_commute_of_sq hμV hlam hc hw hy hr hr2).symm
  have hA₁C : szA₁ (szT₁ L T) ≤ C ⊓ V := by
    intro a ha
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨h.T₁_le_U₁ (szA₁_le _ ha), ?_⟩, h.le ha⟩
    rw [mem_centralizer_singleton_iff]
    exact (h.outerNu_commute_szA₁ hc hw ha).symm
  have hTCV : szT₁ L T ⊔ V ≤ C ⊔ V := by
    refine sup_le (fun y hy => ?_) le_sup_right
    obtain ⟨r, hr, hr2⟩ := h.outerNu_exists_sq hc hy
    have := mul_mem (mem_sup_left (hmem y hy r hr hr2) : y * r ∈ C ⊔ V)
      (mem_sup_right (inv_mem hr) : r⁻¹ ∈ C ⊔ V)
    rwa [mul_inv_cancel_right] at this
  have hCN : C ≤ normalizer (V : Set G) := fun x hx =>
    h.U_le_normalizer_V (h.U₁_le (mem_inf.mp hx).1)
  have hrel := SzC1.relIndex_sup_eq_relIndex_inf hCN
  have h1 := relIndex_mul_card (H := V) (K := C ⊔ V)
  rw [inf_of_le_left le_sup_right, hrel] at h1
  have h2 := relIndex_mul_card (H := C ⊓ V) (K := C)
  rw [inf_of_le_left inf_le_left] at h2
  have h3 : Nat.card (szT₁ L T ⊔ V : Subgroup G) ≤ Nat.card (C ⊔ V : Subgroup G) :=
    Subgroup.card_le_of_le hTCV
  rw [h.card_sup, ← h1, h.card] at h3
  have h4 : 2 ^ f ≤ Nat.card (C ⊓ V : Subgroup G) := by
    rw [← h.card_szA₁]
    exact Subgroup.card_le_of_le hA₁C
  have hq0 : 0 < (2 ^ f) ^ (k + 1) := by positivity
  have h5 : (2 ^ f) ^ 2 ≤ (C ⊓ V).relIndex C := by
    have e : (2 ^ f) ^ 2 * (2 ^ f) ^ (k + 1) = (2 ^ f) ^ (k + 3) := by ring
    refine Nat.le_of_mul_le_mul_right ?_ hq0
    rw [e]
    exact h3
  rw [← h2]
  calc (2 ^ f) ^ 3 = (2 ^ f) ^ 2 * 2 ^ f := by ring
    _ ≤ (C ⊓ V).relIndex C * Nat.card (C ⊓ V : Subgroup G) := Nat.mul_le_mul h5 h4

theorem outerNu_sq_mem (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {c w : G}
    (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) {z : G} (hz : z ∈ U₁)
    (hzx : c * w * t * z = z * (c * w * t)) : z ^ 2 ∈ szA₁ (szT₁ L T) := by
  obtain ⟨y, hy, r, hr, rfl⟩ := h.outerNu_exists_mul_V₁ hlam hz
  have hσ := h.comm_t_eq_of_commute hμV hlam hc hw hy hr hzx
  have hA : y⁻¹ * c * y * c⁻¹ ∈ szA₁ (szT₁ L T) := by
    have := h.comm_T₁_mem (inv_mem hy) hc
    rwa [inv_inv] at this
  have hrV : r ∈ V := h.mem_V_of_comm_t_mem_szA₁ hr (by rw [hσ]; exact hA)
  have hr2 : r ^ 2 = y⁻¹ * c * y * c⁻¹ := by rw [← h.comm_t_of_mem_V hrV, hσ]
  have e : r * y = y * r := (h.V_comm hrV hy).symm
  have hz2 : (y * r) ^ 2 = y ^ 2 * r ^ 2 := by
    calc (y * r) ^ 2 = y * (r * y) * r := by rw [sq]; group
      _ = y * (y * r) * r := by rw [e]
      _ = y ^ 2 * r ^ 2 := by rw [sq, sq]; group
  rw [hz2, hr2]
  exact mul_mem (h.sq_mem_szA₁ hy) hA

end Nu

end U3C1OuterStage

end CFSG.SeitzReduction.RankOne
