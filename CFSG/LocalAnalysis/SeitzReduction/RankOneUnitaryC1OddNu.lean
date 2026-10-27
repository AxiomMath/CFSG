module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageNextBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageInd

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Odd

theorem le_sup_of_card_mul_le {G : Type*} [Group G] [Finite G] {H T N M : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) (hTN : T ≤ normalizer (N : Set G)) (hH : H ≤ M)
    (hN : N ≤ M) (hM : M ≤ T ⊔ N)
    (hcard : Nat.card T * Nat.card (H ⊓ N : Subgroup G) ≤
      Nat.card H * Nat.card (T ⊓ N : Subgroup G)) :
    M ≤ H ⊔ N := by
  have hH1 := SzC1.relIndex_sup_eq_relIndex_inf hHN
  have hT1 := SzC1.relIndex_sup_eq_relIndex_inf hTN
  have hcH : Nat.card (H ⊔ N : Subgroup G) = (H ⊓ N).relIndex H * Nat.card N := by
    have e := relIndex_mul_card (H := N) (K := H ⊔ N)
    rw [inf_of_le_left le_sup_right, hH1] at e
    exact e.symm
  have hcT : Nat.card (T ⊔ N : Subgroup G) = (T ⊓ N).relIndex T * Nat.card N := by
    have e := relIndex_mul_card (H := N) (K := T ⊔ N)
    rw [inf_of_le_left le_sup_right, hT1] at e
    exact e.symm
  have hiH : (H ⊓ N).relIndex H * Nat.card (H ⊓ N : Subgroup G) = Nat.card H := by
    have e := relIndex_mul_card (H := H ⊓ N) (K := H)
    rwa [inf_of_le_left inf_le_left] at e
  have hiT : (T ⊓ N).relIndex T * Nat.card (T ⊓ N : Subgroup G) = Nat.card T := by
    have e := relIndex_mul_card (H := T ⊓ N) (K := T)
    rwa [inf_of_le_left inf_le_left] at e
  have hpos1 : 0 < Nat.card (H ⊓ N : Subgroup G) := Nat.card_pos
  have hpos2 : 0 < Nat.card (T ⊓ N : Subgroup G) := Nat.card_pos
  have hle : (T ⊓ N).relIndex T ≤ (H ⊓ N).relIndex H := by
    by_contra hlt
    push Not at hlt
    have h1 : (H ⊓ N).relIndex H * Nat.card (H ⊓ N : Subgroup G) * Nat.card (T ⊓ N : Subgroup G) <
        (T ⊓ N).relIndex T * Nat.card (T ⊓ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) := by
      calc (H ⊓ N).relIndex H * Nat.card (H ⊓ N : Subgroup G) * Nat.card (T ⊓ N : Subgroup G) =
            (H ⊓ N).relIndex H *
              (Nat.card (T ⊓ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G)) := by ring
        _ < (T ⊓ N).relIndex T *
              (Nat.card (T ⊓ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G)) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos hpos2 hpos1)
        _ = (T ⊓ N).relIndex T * Nat.card (T ⊓ N : Subgroup G) *
              Nat.card (H ⊓ N : Subgroup G) := by ring
    rw [hiH, hiT] at h1
    exact (not_le.mpr h1) hcard
  have hsup : H ⊔ N ≤ T ⊔ N := (sup_le hH hN).trans hM
  have hcle : Nat.card (T ⊔ N : Subgroup G) ≤ Nat.card (H ⊔ N : Subgroup G) := by
    rw [hcH, hcT]
    exact Nat.mul_le_mul_right _ hle
  rw [Subgroup.eq_of_le_of_card_ge hsup hcle]
  exact hM

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem rootCoords_v_one (hc : U3RootCoords T₁ σ u v) : v 1 = 0 := by
  have e := hc.mul_v 1 (one_mem _) 1 (one_mem _)
  rw [mul_one, hc.u_one, zero_mul, sub_zero] at e
  linear_combination -e

theorem rootCoords_comm [CharP E 2] (hc : U3RootCoords T₁ σ u v) {y y' : G} (hy : y ∈ T₁)
    (hy' : y' ∈ T₁) :
    u (y * y' * y⁻¹ * y'⁻¹) = 0 ∧
      v (y * y' * y⁻¹ * y'⁻¹) = u y * σ (u y') + σ (u y) * u y' := by
  have hcT : y * y' * y⁻¹ * y'⁻¹ ∈ T₁ :=
    mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  have hu : u (y * y' * y⁻¹ * y'⁻¹) = 0 := by
    rw [hc.mul_u _ (mul_mem (mul_mem hy hy') (inv_mem hy)) _ (inv_mem hy'),
      hc.mul_u _ (mul_mem hy hy') _ (inv_mem hy), hc.mul_u _ hy _ hy', hc.u_inv hy,
      hc.u_inv hy']
    ring
  refine ⟨hu, ?_⟩
  have e : y * y' = (y * y' * y⁻¹ * y'⁻¹) * (y' * y) := by group
  have h1 := congrArg v e
  rw [hc.mul_v _ hy _ hy', hc.mul_v _ hcT _ (mul_mem hy' hy), hc.mul_v _ hy' _ hy, hu,
    zero_mul, sub_zero] at h1
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination -h1 - (u y * σ (u y')) * h2

theorem sigma_sigma [Finite E] {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (x : E) : σ (σ x) = x := by
  have : Fintype E := Fintype.ofFinite E
  rw [hσ, hσ, ← pow_mul, ← sq]
  have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hE] at h1

theorem exists_ne_zero_norm [Finite E] {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hq : 2 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {c : E} (hc : c ≠ 0) :
    ∃ b : E, b ≠ 0 ∧ b * σ b + (b * σ c + σ b * c) = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra hall
    push Not at hall
    have e : Nat.card {x : E // σ x = x} = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hF, hE] at e
    have : q < q ^ 2 := by nlinarith
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (map_zero σ)
  have hσa0 : σ a ≠ 0 := (map_ne_zero σ).mpr ha0
  have hs0 : σ a * a⁻¹ ≠ 0 := mul_ne_zero hσa0 (inv_ne_zero ha0)
  have hσs : σ (σ a * a⁻¹) = (σ a * a⁻¹)⁻¹ := by
    rw [map_mul, map_inv₀, sigma_sigma hσ hE, mul_inv, inv_inv, mul_comm]
  have hs1 : σ a * a⁻¹ - 1 ≠ 0 := by
    intro h0
    exact ha ((mul_inv_eq_one₀ ha0).mp (by linear_combination h0))
  refine ⟨c * (σ a * a⁻¹ - 1), mul_ne_zero hc hs1, ?_⟩
  rw [map_mul, map_sub, map_one, hσs]
  have key : (σ a * a⁻¹ - 1) * ((σ a * a⁻¹)⁻¹ - 1) + (σ a * a⁻¹ - 1) +
      ((σ a * a⁻¹)⁻¹ - 1) = 0 := by
    have e := mul_inv_cancel₀ hs0
    linear_combination e
  linear_combination (c * σ c) * key

end U3C1Odd

namespace U3C1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

section Nu

variable (h : U3C1Stage G L f t T d V U U₁ k)
include h

theorem U_le_normalizer_V₁ :
    U ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G) := by
  intro x hx
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => ?_
  obtain ⟨hwU₁, hwC⟩ := mem_inf.mp hw
  refine mem_inf.mpr ⟨?_, mem_centralizer_iff.mpr fun y hy => ?_⟩
  · simpa using h.conj_mem_U₁ (inv_mem hx) hwU₁
  · have hy' : x * y * x⁻¹ ∈ szT₁ L T := h.conj_T₁_mem hx hy
    have e := mem_centralizer_iff.mp hwC _ hy'
    calc y * (x⁻¹ * w * x) = x⁻¹ * ((x * y * x⁻¹) * w) * x := by group
      _ = x⁻¹ * (w * (x * y * x⁻¹)) * x := by rw [e]
      _ = x⁻¹ * w * x * y := by group

theorem conj_mem_szA₁_of_normalizer (hμV : U₁ ≤ centralizer (V : Set G)) {g : G}
    (hg : g ∈ normalizer (U : Set G)) {a : G} (ha : a ∈ szA₁ (szT₁ L T)) :
    g * a * g⁻¹ ∈ szA₁ (szT₁ L T) := by
  have hcen : ∀ x ∈ U, x * (g * a * g⁻¹) = (g * a * g⁻¹) * x := by
    intro x hx
    have hx' : g⁻¹ * x * g ∈ U := by
      simpa using (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    have e := h.conj_szA₁ _ hx' a ha
    calc x * (g * a * g⁻¹) = g * (g⁻¹ * x * g * a * (g⁻¹ * x * g)⁻¹) * g⁻¹ * x := by group
      _ = g * a * g⁻¹ * x := by rw [e]
  have hzU₁ : g * a * g⁻¹ ∈ U₁ :=
    h.conj_mem_U₁_of_normalizer hμV hg (h.T₁_le_U₁ (szA₁_le _ ha))
  have hzT : g * a * g⁻¹ ∈ szT₁ L T := h.mem_T₁_of_comm hzU₁ (hcen t h.t_mem_U).symm
  exact mem_szA₁.mpr ⟨hzT, mem_centralizer_iff.mpr fun y hy =>
    hcen y (h.U₁_le (h.T₁_le_U₁ hy))⟩

theorem comm_t_eq_of_commute (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {c w y r : G}
    (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) (hy : y ∈ szT₁ L T)
    (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hcomm : c * w * t * (y * r) = y * r * (c * w * t)) :
    r * t * r⁻¹ * t⁻¹ = y⁻¹ * c * y * c⁻¹ := by
  have hs := h.t_conj_mem_V₁ hr
  have e1 : t * y = y * t := (h.t_comm hy).symm
  have e2 : w * y = y * w := (mem_centralizer_iff.mp (mem_inf.mp hw).2 y hy).symm
  have e3 : w * (t * r * t⁻¹) = (t * r * t⁻¹) * w := h.V₁_comm hμV hlam w hw _ hs
  have e4 : t * r * t⁻¹ * c⁻¹ = c⁻¹ * (t * r * t⁻¹) :=
    (mem_centralizer_iff.mp (mem_inf.mp hs).2 c⁻¹ (inv_mem hc)).symm
  have key : c * w * t * (y * r) * (c * w * t)⁻¹ = c * y * c⁻¹ * (t * r * t⁻¹) := by
    calc c * w * t * (y * r) * (c * w * t)⁻¹ = c * w * (t * y) * r * t⁻¹ * w⁻¹ * c⁻¹ := by
          group
      _ = c * (w * y) * (t * r * t⁻¹) * w⁻¹ * c⁻¹ := by rw [e1]; group
      _ = c * y * (w * (t * r * t⁻¹)) * w⁻¹ * c⁻¹ := by rw [e2]; group
      _ = c * y * (t * r * t⁻¹ * c⁻¹) := by rw [e3]; group
      _ = c * y * c⁻¹ * (t * r * t⁻¹) := by rw [e4]; group
  have E : c * y * c⁻¹ * (t * r * t⁻¹) = y * r := by
    rw [← key, hcomm, mul_inv_cancel_right]
  calc r * t * r⁻¹ * t⁻¹ = y⁻¹ * (y * r) * (t * r * t⁻¹)⁻¹ := by group
    _ = y⁻¹ * (c * y * c⁻¹ * (t * r * t⁻¹)) * (t * r * t⁻¹)⁻¹ := by rw [E]
    _ = y⁻¹ * c * y * c⁻¹ := by group

theorem mem_V_of_comm_t_mem_szA₁ {r : G} (hr : r ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hσ : r * t * r⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T)) : r ∈ V := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, -⟩ := h.coords
  have h1 : (r * t * r⁻¹ * t⁻¹) ^ 2 ^ k = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.one_le; omega⟩
    rw [hj, pow_succ', pow_mul, hc.sq_eq_one hσ, one_pow]
  refine h.mem_V_of_mem_V₁_of_mem_sup hr (h.mem_sup_of_S_eq_zero hK hc (mem_inf.mp hr).1 ?_)
  rw [h1, hc.v_one]

theorem false_of_nu (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)))
    (hν : ∃ w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w * t) ^ 2 ≠ 1)
    (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) : False := by
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  obtain ⟨E, _, _, _, σ, hE, hσ, hfix, u, v', hco, hA⟩ :=
    h.start.exists_rootCoords_of_card_sylow h.card_sylow
  obtain ⟨g, hgN, -, hxt, hxR⟩ := h.exists_conj_escape hU
  obtain ⟨c, hcT, w, hw, hcw⟩ := h.exists_mul_V₁ hlam hxt
  have hx : g * t * g⁻¹ = c * w * t := by
    rw [← hcw, mul_assoc (g * t * g⁻¹) t t, h.t_mul_self, mul_one]
  have hc0 : u c ≠ 0 := by
    intro h0
    have hcA : c ∈ szA₁ (szT₁ L T) := (hA c hcT).mpr h0
    have hw' : c * w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
      mul_mem (h.V_le_V₁ (h.le hcA)) hw
    have hsq : (c * w * t) ^ 2 = 1 := by
      rw [← hx, sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group,
        h.t_mul_self, mul_one, mul_inv_cancel]
    have hV := h.mem_V_of_sq_eq_one hK hc hμ hμV hlam hν hw' hsq
    exact hxR (by rw [hx]; exact mul_mem (le_szR_mid _ _ _ hV) (mem_szR_right _ _ _))
  have hV₁comm := h.V₁_comm hμV hlam
  have hNV₁ := h.U_le_normalizer_V₁
  set H : Subgroup G := (szT₁ L T).map (MulAut.conj g).toMonoidHom with hH
  have hmemH : ∀ z ∈ H, ∃ y ∈ szT₁ L T, z = g * y * g⁻¹ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  have hHcard : Nat.card H = (2 ^ f) ^ 3 := by
    rw [hH, card_map_of_injective (MulAut.conj g).injective, h.card_T₁]
  have hHU₁ : H ≤ U₁ := fun z hz => by
    obtain ⟨y, hy, rfl⟩ := hmemH z hz
    exact h.conj_mem_U₁_of_normalizer hμV hgN (h.T₁_le_U₁ hy)
  have hcommH : ∀ z ∈ H, c * w * t * z = z * (c * w * t) := fun z hz => by
    obtain ⟨y, hy, rfl⟩ := hmemH z hz
    rw [← hx]
    calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
      _ = g * (y * t) * g⁻¹ := by rw [h.t_comm hy]
      _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
  have hHV : H ⊓ (U₁ ⊓ centralizer (szT₁ L T : Set G)) ≤ szA₁ (szT₁ L T) := by
    intro z hz
    obtain ⟨hzH, hzV⟩ := mem_inf.mp hz
    have e := hcommH z hzH
    have hzc : c * z = z * c := mem_centralizer_iff.mp (mem_inf.mp hzV).2 c hcT
    have hzw : w * z = z * w := hV₁comm w hw z hzV
    have hzt : z * t = t * z := by
      have e' : c * w * (t * z) = c * w * (z * t) := by
        calc c * w * (t * z) = c * w * t * z := by group
          _ = z * (c * w * t) := e
          _ = (z * c) * w * t := by group
          _ = (c * z) * w * t := by rw [hzc]
          _ = c * (z * w) * t := by group
          _ = c * (w * z) * t := by rw [hzw]
          _ = c * w * (z * t) := by group
      exact (mul_left_cancel e').symm
    exact mem_szA₁.mpr ⟨h.mem_T₁_of_comm (mem_inf.mp hzV).1 hzt, (mem_inf.mp hzV).2⟩
  have hT₁V₁ : szT₁ L T ⊓ (U₁ ⊓ centralizer (szT₁ L T : Set G)) = szA₁ (szT₁ L T) :=
    le_antisymm
      (fun z hz => mem_szA₁.mpr ⟨(mem_inf.mp hz).1, (mem_inf.mp (mem_inf.mp hz).2).2⟩)
      (le_inf (szA₁_le _) (h.le.trans h.V_le_V₁))
  have hle : U₁ ≤ H ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) :=
    U3C1Odd.le_sup_of_card_mul_le ((hHU₁.trans h.U₁_le).trans hNV₁)
      ((h.T₁_le_U₁.trans h.U₁_le).trans hNV₁) hHU₁ inf_le_left (le_of_eq hlam) (by
        rw [hHcard, h.card_T₁, hT₁V₁, h.card_szA₁]
        exact Nat.mul_le_mul_left _ ((Subgroup.card_le_of_le hHV).trans h.card_szA₁.le))
  obtain ⟨b, hb0, hbN⟩ :=
    U3C1Odd.exists_ne_zero_norm hσ (by have := h.four_le_q; omega) hE hfix hc0
  obtain ⟨y₀, hy₀, hy₀b⟩ := hco.u_surj b
  have hy₀U' : y₀ ∈ ((H ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G) :=
    hle (h.T₁_le_U₁ hy₀)
  rw [coe_mul_of_left_le_normalizer_right _ _ ((hHU₁.trans h.U₁_le).trans hNV₁)] at hy₀U'
  obtain ⟨z, hzH, r₀, hr₀, hzr⟩ := hy₀U'
  have hzy : z = y₀ * r₀⁻¹ := by rw [← hzr, mul_inv_cancel_right]
  have hr : r₀⁻¹ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) := inv_mem hr₀
  have hσr := h.comm_t_eq_of_commute hμV hlam hcT hw hy₀ hr (by
    rw [← hzy]
    exact hcommH z hzH)
  have hcomA : y₀⁻¹ * c * y₀ * c⁻¹ ∈ szA₁ (szT₁ L T) := by
    have e := h.comm_T₁_mem (inv_mem hy₀) hcT
    rwa [inv_inv] at e
  have hrV : r₀⁻¹ ∈ V := h.mem_V_of_comm_t_mem_szA₁ hr (by rw [hσr]; exact hcomA)
  have hr2 : r₀⁻¹ ^ 2 = y₀⁻¹ * c * y₀ * c⁻¹ := by
    rw [← h.comm_t_of_mem_V hrV, hσr]
  have hz2 : z ^ 2 = y₀ ^ 2 * (y₀⁻¹ * c * y₀ * c⁻¹) := by
    rw [hzy, ← hr2]
    have e : r₀⁻¹ * y₀ = y₀ * r₀⁻¹ := (h.V_comm hrV hy₀).symm
    calc (y₀ * r₀⁻¹) ^ 2 = y₀ * (r₀⁻¹ * y₀) * r₀⁻¹ := by rw [sq]; group
      _ = y₀ * (y₀ * r₀⁻¹) * r₀⁻¹ := by rw [e]
      _ = y₀ ^ 2 * r₀⁻¹ ^ 2 := by rw [sq y₀, sq r₀⁻¹]; group
  have hy₀2 := hco.sq hy₀
  have hcm := U3C1Odd.rootCoords_comm hco (inv_mem hy₀) hcT
  rw [inv_inv] at hcm
  have hcmT : y₀⁻¹ * c * y₀ * c⁻¹ ∈ szT₁ L T := szA₁_le _ hcomA
  have hy₀2T : y₀ ^ 2 ∈ szT₁ L T := pow_mem hy₀ 2
  have hz2T : z ^ 2 ∈ szT₁ L T := by
    rw [hz2]
    exact mul_mem hy₀2T hcmT
  have hu2 : u (z ^ 2) = 0 := by
    rw [hz2, hco.mul_u _ hy₀2T _ hcmT, hy₀2.1, hcm.1, add_zero]
  have hv2 : v' (z ^ 2) = 0 := by
    rw [hz2, hco.v_mul_of_u_eq_zero hy₀2T hcmT hy₀2.1, hy₀2.2, hcm.2, hco.u_inv hy₀, map_neg,
      hy₀b]
    simp only [CharTwo.neg_eq]
    exact hbN
  have hz21 : z ^ 2 = 1 := hco.inj _ hz2T _ (one_mem _) (by rw [hu2, hco.u_one])
    (by rw [hv2, U3C1Odd.rootCoords_v_one hco])
  obtain ⟨y', hy', hzy'⟩ := hmemH z hzH
  have hy'2 : y' ^ 2 = 1 := by
    have e : z ^ 2 = g * y' ^ 2 * g⁻¹ := by rw [hzy', conj_pow]
    rw [hz21] at e
    calc y' ^ 2 = g⁻¹ * (g * y' ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [← e]; group
  have hzA : z ∈ szA₁ (szT₁ L T) := by
    rw [hzy']
    exact h.conj_mem_szA₁_of_normalizer hμV hgN (h.mem_szA₁_of_sq_eq_one hy' hy'2)
  have hy₀V : y₀ ∈ V := by
    rw [← hzr]
    exact mul_mem (h.le hzA) (by simpa using inv_mem hrV)
  have hy₀A : y₀ ∈ szA₁ (szT₁ L T) := by
    rw [← h.inf_eq_szA₁]
    exact mem_inf.mpr ⟨hy₀, hy₀V⟩
  exact hb0 (by rw [← hy₀b]; exact (hA y₀ hy₀).mp hy₀A)

end Nu

end U3C1Stage

theorem u3C1NuInput_holds : U3C1NuInput := by
  intro G _ _ L f t T d V U U₁ k h _ _ hμV hlam hν hU
  exact h.false_of_nu hμV hlam hν hU

end CFSG.SeitzReduction.RankOne
