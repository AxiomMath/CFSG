module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Level
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1TwoToOne
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmega

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem comm_mem_V (h : SzC1Stage G L f a t T d V U U₁ k) :
    ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V := by
  refine SzC1.comm_mem_of_generators_normal (P := fun g => g ∈ U₁ ∨ g = t)
    (fun S hS => by
      rw [← h.sup_eq]
      exact sup_le (fun x hx => hS x (Or.inl hx)) (zpowers_le.mpr (hS t (Or.inr rfl))))
    (fun g hg => hg.elim (fun hg => h.U₁_le hg) (fun hg => hg ▸ h.t_mem_U))
    (fun y hy b hb => h.conj_V_of_mem_U hy hb) ?_
  rintro g (hg | hg) g' (hg' | hg')
  · exact h.le (h.comm_mem_szA₁ g hg g' hg')
  · rw [hg']
    exact h.comm_t_mem (h.U₁_le hg)
  · rw [hg, show t * g' * t⁻¹ * g'⁻¹ = (g' * t * g'⁻¹ * t⁻¹)⁻¹ by group]
    exact inv_mem (h.comm_t_mem (h.U₁_le hg'))
  · rw [hg, hg', show t * t * t⁻¹ * t⁻¹ = (1 : G) by group]
    exact one_mem _

theorem conj_V_of_mem_normalizer (h : SzC1Stage G L f a t T d V U U₁ k) {g : G}
    (hg : g ∈ normalizer (U : Set G)) {r : G} (hr : r ∈ V) : g * r * g⁻¹ ∈ V := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  obtain ⟨y, hy, rfl⟩ := h.exists_comm_t_eq hK hc hκ hr
  have hgU : ∀ x ∈ U, g * x * g⁻¹ ∈ U := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  rw [show g * (y * t * y⁻¹ * t⁻¹) * g⁻¹ =
    (g * y * g⁻¹) * (g * t * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * t * g⁻¹)⁻¹ by group]
  exact h.comm_mem_V _ (hgU y (h.U₁_le hy)) _ (hgU t h.t_mem_U)

theorem normalizer_U_le_normalizer_V (h : SzC1Stage G L f a t T d V U U₁ k) :
    normalizer (U : Set G) ≤ normalizer (V : Set G) := fun _ hg =>
  mem_normalizer_of_forall_inv_mul_mul_mem fun _ hr => by
    simpa using h.conj_V_of_mem_normalizer (inv_mem hg) hr

theorem conj_t_inv_of_normalizer (h : SzC1Stage G L f a t T d V U U₁ k) {g : G}
    (hg : g ∈ normalizer (U : Set G)) {r : G} (hr : r ∈ V) :
    g * t * g⁻¹ * r * (g * t * g⁻¹)⁻¹ = r⁻¹ := by
  have hr' : g⁻¹ * r * g ∈ V := by simpa using h.conj_V_of_mem_normalizer (inv_mem hg) hr
  calc g * t * g⁻¹ * r * (g * t * g⁻¹)⁻¹ = g * (t * (g⁻¹ * r * g) * t⁻¹) * g⁻¹ := by group
    _ = r⁻¹ := by rw [h.inv _ hr']; group

theorem exists_conj_escape
    (h : SzC1Stage G L f a t T d V U U₁ k) (hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    ∃ g ∈ normalizer (U : Set G), g ∉ U ∧ g * t * g⁻¹ * t ∈ U₁ ∧
      g * t * g⁻¹ ∉ szR (szT₁ L T) V t := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  have hK' := h.card_K hK hc
  obtain ⟨g, hgN, hgU, P, hP2, hUP, hgP⟩ :=
    exists_normalizer_not_mem_of_not_isSylow h.isPGroup_U hU
  have hxU : g * t * g⁻¹ ∈ U := (mem_normalizer_iff.mp hgN t).mp h.t_mem_U
  have hxU₁ := h.conj_not_mem_U₁ g
  refine ⟨g, hgN, hgU, (h.mem_or_mul_t_mem hxU).resolve_left hxU₁, fun hxR => ?_⟩
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers h.t_mul_self
    h.t_mem_normalizer_sup hxR with h1 | h1
  · exact hxU₁ (h.sup_le_U₁ h1)
  obtain ⟨y, hy, r, hr, hyr⟩ := h.exists_mul_of_mem_sup h1
  have hx2 : (g * t * g⁻¹) ^ 2 = 1 := by
    rw [sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_self,
      mul_one, mul_inv_cancel]
  have hxe : g * t * g⁻¹ = y * r * t := by
    rw [← hyr, mul_assoc (g * t * g⁻¹) t t, h.t_mul_self, mul_one]
  rw [hxe, h.sq_mul_mul_t hy hr] at hx2
  have hyA := SzC1.mem_szA₁_of_sq_eq_one hc h.ha hK' hy hx2
  obtain ⟨w, hw, hwσ⟩ := h.exists_comm_t_eq hK hc hκ (mul_mem (h.le hyA) hr)
  have hcent : w⁻¹ * g ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e : w * t * w⁻¹ = g * t * g⁻¹ := by
      rw [hxe, ← hwσ]
      group
    calc w⁻¹ * g * t = w⁻¹ * (g * t * g⁻¹) * g := by group
      _ = w⁻¹ * (w * t * w⁻¹) * g := by rw [e]
      _ = t * (w⁻¹ * g) := by group
  have hT : T = szT₁ L T ⊔ zpowers t := h.start.facts.1
  have hTU : T ≤ U := by
    rw [hT]
    exact sup_le (h.T₁_le_U₁.trans h.U₁_le) (zpowers_le.mpr h.t_mem_U)
  obtain ⟨P₀, hP₀⟩ := h.start.sylow
  have hmax := P₀.is_maximal' (Q := P.subgroupOf (centralizer ({t} : Set G)))
    hP2.comap_subtype (by
      rw [hP₀]
      intro z hz
      exact mem_subgroupOf.mpr (hUP (hTU (mem_subgroupOf.mp hz))))
  have hwg : (⟨w⁻¹ * g, hcent⟩ : centralizer ({t} : Set G)) ∈ (P₀ : Subgroup _) := by
    rw [← hmax]
    exact mem_subgroupOf.mpr (mul_mem (inv_mem (hUP (h.U₁_le hw))) hgP)
  rw [hP₀, mem_subgroupOf] at hwg
  exact hgU (by simpa using mul_mem (h.U₁_le hw) (hTU hwg))

theorem false_of_mu_one
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : ¬ U₁ ≤ centralizer (V : Set G)) : False := by
  by_cases hU : ∃ S : Sylow 2 G, (S : Subgroup G) = U
  · exact h.false_of_isSylow hU
  obtain ⟨g, hgN, -, hxt, hxR⟩ := h.exists_conj_escape hU
  have hxtV : g * t * g⁻¹ * t ∈ centralizer (V : Set G) := by
    refine mem_centralizer_iff.mpr fun r hr => ?_
    have e : (g * t * g⁻¹ * t) * r * (g * t * g⁻¹ * t)⁻¹ = r := by
      calc (g * t * g⁻¹ * t) * r * (g * t * g⁻¹ * t)⁻¹ =
            (g * t * g⁻¹) * (t * r * t⁻¹) * (g * t * g⁻¹)⁻¹ := by group
        _ = ((g * t * g⁻¹) * r * (g * t * g⁻¹)⁻¹)⁻¹ := by rw [h.inv r hr]; group
        _ = r := by rw [h.conj_t_inv_of_normalizer hgN hr, inv_inv]
    calc r * (g * t * g⁻¹ * t) =
          ((g * t * g⁻¹ * t) * r * (g * t * g⁻¹ * t)⁻¹) * (g * t * g⁻¹ * t) := by rw [e]
      _ = (g * t * g⁻¹ * t) * r := by group
  have hmem := h.mem_sup_of_mem_centralizer_V hμ hxt hxtV
  refine hxR ?_
  rw [show g * t * g⁻¹ = (g * t * g⁻¹ * t) * t by
    rw [mul_assoc (g * t * g⁻¹) t t, h.t_mul_self, mul_one]]
  exact mul_mem (sup_le_szR _ _ _ hmem) (mem_szR_right _ _ _)


theorem exists_sq_ne_one (h : SzC1Stage G L f a t T d V U U₁ k) : ∃ r ∈ V, r ^ 2 ≠ 1 := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  by_contra hne
  push Not at hne
  have hle : V ≤ szA₁ (szT₁ L T) := fun r hr => h.omega r hr (hne r hr)
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card, h.card_szA₁ hK hc] at h1
  have h2 : 2 ^ f < (2 ^ f) ^ (k + 1) := by
    calc 2 ^ f = (2 ^ f) ^ 1 := (pow_one _).symm
      _ < (2 ^ f) ^ (k + 1) :=
        Nat.pow_lt_pow_right (h.one_lt_q hK hc) (by have := h.one_le_k hK hc; omega)
  omega

theorem conj_mem_U₁_of_normalizer (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : U₁ ≤ centralizer (V : Set G)) {g : G} (hg : g ∈ normalizer (U : Set G)) {w : G}
    (hw : w ∈ U₁) : g * w * g⁻¹ ∈ U₁ := by
  have hzU : g * w * g⁻¹ ∈ U := (mem_normalizer_iff.mp hg w).mp (h.U₁_le hw)
  refine (h.mem_or_mul_t_mem hzU).resolve_right fun hzt => ?_
  obtain ⟨r, hr, hr2⟩ := h.exists_sq_ne_one
  have hzV : (g * w * g⁻¹) * r = r * (g * w * g⁻¹) := by
    have hr' : g⁻¹ * r * g ∈ V := by simpa using h.conj_V_of_mem_normalizer (inv_mem hg) hr
    have e := mem_centralizer_iff.mp (hμ hw) _ hr'
    calc g * w * g⁻¹ * r = g * (w * (g⁻¹ * r * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * r * g) * w) * g⁻¹ := by rw [e]
      _ = r * (g * w * g⁻¹) := by group
  have hztV := (mem_centralizer_iff.mp (hμ hzt) r hr).symm
  have htr : t * r = r * t := by
    have e1 : (g * w * g⁻¹) * (t * r) = (g * w * g⁻¹) * (r * t) := by
      calc (g * w * g⁻¹) * (t * r) = (g * w * g⁻¹ * t) * r := by group
        _ = r * (g * w * g⁻¹ * t) := hztV
        _ = (r * (g * w * g⁻¹)) * t := by group
        _ = (g * w * g⁻¹ * r) * t := by rw [hzV]
        _ = (g * w * g⁻¹) * (r * t) := by group
    exact mul_left_cancel e1
  apply hr2
  have e1 : t * r * t⁻¹ = r := by rw [htr, mul_inv_cancel_right]
  rw [h.inv r hr] at e1
  rw [sq]
  nth_rewrite 1 [← e1]
  exact inv_mul_cancel r

section Lambda

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}
  (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem delta_eq_of_u_eq {m : G} (hm : m ∈ U) {y y' : G} (hy : y ∈ szT₁ L T)
    (hy' : y' ∈ szT₁ L T) (huy : u y = u y') :
    y⁻¹ * (m * y * m⁻¹) = y'⁻¹ * (m * y' * m⁻¹) := by
  have ha := hc.inv_mul_mem_szA₁_of_u_eq h.ha (h.card_K hK hc) hy hy' huy
  have e : y' = y * (y⁻¹ * y') := by group
  rw [e, h.delta_mul_right hm hy (szA₁_le _ ha), h.conj_szA₁ m hm _ ha, inv_mul_cancel, mul_one]

theorem v_delta_of_mem_T₁ {y y' : G} (hy : y ∈ szT₁ L T) (hy' : y' ∈ szT₁ L T) :
    v (y⁻¹ * (y' * y * y'⁻¹)) = u y' * u y ^ 2 ^ (a + 1) + u y' ^ 2 ^ (a + 1) * u y := by
  have e := (hc.comm (inv_mem hy) hy').2
  rw [show y⁻¹ * y' * y⁻¹⁻¹ * y'⁻¹ = y⁻¹ * (y' * y * y'⁻¹) by group, (hc.inv hy).1] at e
  rw [e]
  ring

theorem exists_lambda (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) :
    ∃ l : K, ∀ m ∈ U₁, ∃ c : K, ∀ y ∈ szT₁ L T,
      v (y⁻¹ * (m * y * m⁻¹)) = l * (v ((m * t * m⁻¹ * t⁻¹) ^ 2 ^ k) * u y) ^ 2 ^ a +
        (c * u y ^ 2 ^ (a + 1) + c ^ 2 ^ (a + 1) * u y) := by
  have hK' := h.card_K hK hc
  choose sec hsecT hsecu _hsecv using fun b : K => hc.surj b 0
  have hdU₁ : ∀ x ∈ U₁, d⁻¹ * x * d ∈ U₁ := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem h.d_mem_U₁) x).mp hx
  obtain ⟨l, hl⟩ := exists_szDelta_const h.ha hK' hκ (M := U₁)
    (S := fun m => v ((m * t * m⁻¹ * t⁻¹) ^ 2 ^ k))
    (Δ := fun m b => v ((sec b)⁻¹ * (m * sec b * m⁻¹)))
    (fun m hm m' hm' => h.S_mul hK hc hm hm') (h.S_surj hK hc hκ)
    (fun m hm m' hm' b => by
      show v ((sec b)⁻¹ * (m * m' * sec b * (m * m')⁻¹)) = _
      rw [h.delta_mul_left (h.U₁_le hm) (h.U₁_le hm') (hsecT b),
        hc.v_mul_szA₁ h.ha hK' (h.conj_T₁ m (h.U₁_le hm) _ (hsecT b))
          (h.conj_T₁ m' (h.U₁_le hm') _ (hsecT b))])
    (fun m hm b b' => by
      show v ((sec (b + b'))⁻¹ * (m * sec (b + b') * m⁻¹)) = _
      have hmul := mul_mem (hsecT b) (hsecT b')
      rw [h.delta_eq_of_u_eq hK hc (h.U₁_le hm) (hsecT (b + b')) hmul
        (by rw [(hc.mul _ (hsecT b) _ (hsecT b')).1, hsecu, hsecu, hsecu]),
        h.delta_mul_right (h.U₁_le hm) (hsecT b) (hsecT b'),
        hc.v_mul_szA₁ h.ha hK' (h.conj_T₁ m (h.U₁_le hm) _ (hsecT b))
          (h.conj_T₁ m (h.U₁_le hm) _ (hsecT b'))])
    (fun m hm h0 => by
      obtain ⟨y', hy', r, hr, rfl⟩ := h.exists_mul_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc hm h0)
      refine ⟨u y', fun b => ?_⟩
      show v ((sec b)⁻¹ * (y' * r * sec b * (y' * r)⁻¹)) = _
      have e : y' * r * sec b * (y' * r)⁻¹ = y' * sec b * y'⁻¹ := by
        rw [show y' * r * sec b * (y' * r)⁻¹ = y' * (r * sec b * r⁻¹) * y'⁻¹ by group,
          ← h.V_comm hr (hsecT b), mul_inv_cancel_right]
      rw [e, h.v_delta_of_mem_T₁ hK hc (hsecT b) hy', hsecu])
    (fun m hm => ⟨d⁻¹ * m * d, hdU₁ m hm, h.S_conj_d hK hc hm, fun b => by
      show v ((sec (κ * b))⁻¹ * (d⁻¹ * m * d * sec (κ * b) * (d⁻¹ * m * d)⁻¹)) = _
      have hdy : d⁻¹ * sec b * d ∈ szT₁ L T := hc.conj_mem _ (hsecT b)
      rw [h.delta_eq_of_u_eq hK hc (h.U₁_le (hdU₁ m hm)) (hsecT (κ * b)) hdy
        (by rw [hc.conj_u _ (hsecT b), hsecu, hsecu]),
        show (d⁻¹ * sec b * d)⁻¹ * (d⁻¹ * m * d * (d⁻¹ * sec b * d) * (d⁻¹ * m * d)⁻¹) =
          d⁻¹ * ((sec b)⁻¹ * (m * sec b * m⁻¹)) * d by group,
        hc.v_conj_szA₁ h.ha hK' (h.conj_T₁ m (h.U₁_le hm) _ (hsecT b))]⟩)
  refine ⟨l, fun m hm => ?_⟩
  obtain ⟨c, hc'⟩ := hl m hm
  refine ⟨c, fun y hy => ?_⟩
  rw [h.delta_eq_of_u_eq hK hc (h.U₁_le hm) hy (hsecT (u y)) (hsecu _).symm]
  exact hc' (u y)


theorem false_of_lambda_ne_zero'
    (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : ¬ U₁ ≤ szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) : False := by
  have hK' := h.card_K hK hc
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have hk := h.one_le_k hK hc
  obtain ⟨l, hl⟩ := h.exists_lambda hK hc hκ
  have hl0 : l ≠ 0 := by
    rintro rfl
    refine hlam fun m hm => ?_
    obtain ⟨c, hcm⟩ := hl m hm
    obtain ⟨y₁, hy₁, hu₁, -⟩ := hc.surj c 0
    have hy₁U : y₁⁻¹ ∈ U := h.U₁_le (h.T₁_le_U₁ (inv_mem hy₁))
    have hz : y₁⁻¹ * m ∈ centralizer (szT₁ L T : Set G) := by
      refine mem_centralizer_iff.mpr fun y hy => ?_
      have e1 := h.delta_mul_left hy₁U (h.U₁_le hm) hy
      have e2 : v (y⁻¹ * (y₁⁻¹ * y * y₁⁻¹⁻¹)) = c * u y ^ 2 ^ (a + 1) + c ^ 2 ^ (a + 1) * u y := by
        rw [h.v_delta_of_mem_T₁ hK hc hy (inv_mem hy₁), (hc.inv hy₁).1, hu₁]
      have e3 := hcm y hy
      rw [zero_mul, zero_add] at e3
      have e4 : v (y⁻¹ * (y₁⁻¹ * m * y * (y₁⁻¹ * m)⁻¹)) = 0 := by
        rw [e1, hc.v_mul_szA₁ h.ha hK' (h.conj_T₁ _ hy₁U y hy) (h.conj_T₁ m (h.U₁_le hm) y hy),
          e2, e3]
        linear_combination (c * u y ^ 2 ^ (a + 1) + c ^ 2 ^ (a + 1) * u y) * h2K
      have e5 := hc.eq_one_of_v_eq_zero h.ha hK'
        (h.conj_T₁ _ (mul_mem hy₁U (h.U₁_le hm)) y hy) e4
      have e6 : y₁⁻¹ * m * y * (y₁⁻¹ * m)⁻¹ = y := by
        calc y₁⁻¹ * m * y * (y₁⁻¹ * m)⁻¹ = y * (y⁻¹ * (y₁⁻¹ * m * y * (y₁⁻¹ * m)⁻¹)) := by group
          _ = y := by rw [e5, mul_one]
      calc y * (y₁⁻¹ * m) = (y₁⁻¹ * m * y * (y₁⁻¹ * m)⁻¹) * (y₁⁻¹ * m) := by rw [e6]
        _ = y₁⁻¹ * m * y := by group
    have hmem : y₁ * (y₁⁻¹ * m) ∈ szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) :=
      mul_mem (mem_sup_left hy₁)
        (mem_sup_right (mem_inf.mpr ⟨mul_mem (inv_mem (h.T₁_le_U₁ hy₁)) hm, hz⟩))
    simpa using hmem
  have hU : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U := fun hU => h.false_of_isSylow hU
  obtain ⟨g, hgN, -, hxt, hxR⟩ := h.exists_conj_escape hU
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ = g * t * g⁻¹ * t := ⟨_, rfl⟩
  rw [← hv₀] at hxt
  have hx : g * t * g⁻¹ = v₀ * t := by
    rw [hv₀, mul_assoc (g * t * g⁻¹) t t, h.t_mul_self, mul_one]
  have hv₀U := h.U₁_le hxt
  have hs : v ((v₀ * t * v₀⁻¹ * t⁻¹) ^ 2 ^ k) ≠ 0 := fun h0 => hxR (by
    rw [hx]
    exact mul_mem (sup_le_szR _ _ _ (h.mem_sup_of_S_eq_zero hK hc hxt h0)) (mem_szR_right _ _ _))
  set C : Subgroup G := U₁ ⊓ centralizer ({g * t * g⁻¹} : Set G) with hC
  have hCsup : C ≤ szT₁ L T ⊔ V := by
    intro w hw
    obtain ⟨hwU₁, hwx⟩ := mem_inf.mp hw
    rw [mem_centralizer_singleton_iff, hx] at hwx
    have e0 : (v₀ * t) * w * (v₀ * t)⁻¹ = w := by rw [← hwx]; group
    have e : w * t * w⁻¹ * t⁻¹ = w * v₀⁻¹ * w⁻¹ * v₀⁻¹⁻¹ := by
      calc w * t * w⁻¹ * t⁻¹ = w * (v₀⁻¹ * ((v₀ * t) * w * (v₀ * t)⁻¹) * v₀)⁻¹ := by group
        _ = w * v₀⁻¹ * w⁻¹ * v₀⁻¹⁻¹ := by rw [e0]; group
    have hσA : w * t * w⁻¹ * t⁻¹ ∈ szA₁ (szT₁ L T) := by
      rw [e]
      exact h.comm_mem_szA₁ w hwU₁ v₀⁻¹ (inv_mem hxt)
    have hσk : (w * t * w⁻¹ * t⁻¹) ^ 2 ^ k = 1 := by
      obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [hj, pow_succ', pow_mul, hc.sq_eq_one_of_mem_szA₁ h.ha hK' hσA, one_pow]
    exact h.mem_sup_of_S_eq_zero hK hc hwU₁ (by rw [hσk, hc.v_one])
  have hCV : ∀ r ∈ V, r ∈ C → r ∈ szA₁ (szT₁ L T) := by
    intro r hr hrC
    refine h.omega r hr ?_
    have e1 := h.conj_t_inv_of_normalizer hgN hr
    rw [← mem_centralizer_singleton_iff.mp (mem_inf.mp hrC).2, mul_inv_cancel_right] at e1
    rw [sq]
    nth_rewrite 2 [e1]
    exact mul_inv_cancel r
  have hcardC : Nat.card C ≤ 2 ^ f * 2 ^ f := by
    have h1 := relIndex_mul_card (H := V) (K := C)
    have h2 : V.relIndex C ≤ 2 ^ f :=
      (relIndex_le_of_le_right hCsup (by rw [h.relIndex_V_sup hK hc]; positivity)).trans_eq
        (h.relIndex_V_sup hK hc)
    have h3 : Nat.card (V ⊓ C : Subgroup G) ≤ 2 ^ f :=
      (Subgroup.card_le_of_le fun r hr => hCV r (mem_inf.mp hr).1 (mem_inf.mp hr).2).trans_eq
        (h.card_szA₁ hK hc)
    rw [← h1]
    exact Nat.mul_le_mul h2 h3
  set M : Subgroup G := (szT₁ L T).map (MulAut.conj g).toMonoidHom with hM
  have hMC : M ≤ C := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.mpr ⟨h.conj_mem_U₁_of_normalizer hμ hgN (h.T₁_le_U₁ hy),
      mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [h.t_comm hy]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
  have hMeq : M = C := Subgroup.eq_of_le_of_card_ge hMC (by
    rw [hM, Subgroup.card_map_of_injective (MulAut.conj g).injective, h.card_T₁ hK hc, sq]
    exact hcardC)
  obtain ⟨c, hcv₀⟩ := hl v₀ hxt
  have hβ : l * v ((v₀ * t * v₀⁻¹ * t⁻¹) ^ 2 ^ k) ^ 2 ^ a ≠ 0 :=
    mul_ne_zero hl0 (pow_ne_zero _ hs)
  obtain ⟨e, he0, he⟩ := sz_two_to_one h.ha hK' hβ c
  obtain ⟨ye, hye, hue, -⟩ := hc.surj e 0
  have hδA := h.conj_T₁ v₀ hv₀U ye hye
  obtain ⟨x₀, hx₀, hx₀k⟩ := SzC1.exists_pow_eq_of_mem h.comm h.omega h.pow
    (by rw [h.card_szA₁ hK hc, h.card]) hδA
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, r = x₀ ^ 2 ^ j := ⟨_, rfl⟩
  have hrV : r ∈ V := hr ▸ pow_mem hx₀ _
  have hr2 : r ^ 2 = ye⁻¹ * (v₀ * ye * v₀⁻¹) := by
    rw [hr, ← pow_mul, ← pow_succ, ← hj, hx₀k]
  have hzC : ye * r ∈ C := by
    refine mem_inf.mpr ⟨mul_mem (h.T₁_le_U₁ hye) (h.V_le_U₁ hrV),
      mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hx]
    have hv₀r : v₀ * r⁻¹ * v₀⁻¹ = r⁻¹ := by
      rw [← mem_centralizer_iff.mp (hμ hxt) _ (inv_mem hrV), mul_inv_cancel_right]
    have hv₀ye : v₀ * ye * v₀⁻¹ = ye * r ^ 2 := by rw [hr2]; group
    have hconj : (v₀ * t) * (ye * r) * (v₀ * t)⁻¹ = ye * r := by
      calc (v₀ * t) * (ye * r) * (v₀ * t)⁻¹ = v₀ * (t * ye) * r * t⁻¹ * v₀⁻¹ := by group
        _ = v₀ * (ye * t) * r * t⁻¹ * v₀⁻¹ := by rw [← h.t_comm hye]
        _ = (v₀ * ye * v₀⁻¹) * (v₀ * (t * r * t⁻¹) * v₀⁻¹) := by group
        _ = (ye * r ^ 2) * (v₀ * r⁻¹ * v₀⁻¹) := by rw [hv₀ye, h.inv r hrV]
        _ = (ye * r ^ 2) * r⁻¹ := by rw [hv₀r]
        _ = ye * r := by group
    calc ye * r * (v₀ * t) = ((v₀ * t) * (ye * r) * (v₀ * t)⁻¹) * (v₀ * t) := by rw [hconj]
      _ = v₀ * t * (ye * r) := by group
  have hz2 : (ye * r) ^ 2 = 1 := by
    have hcomm : r * ye = ye * r := (h.V_comm hrV hye).symm
    have hA2 : ye ^ 2 ∈ szA₁ (szT₁ L T) := hc.sq_mem_szA₁ h.ha hK' hye
    have e1 : (ye * r) ^ 2 = ye ^ 2 * (ye⁻¹ * (v₀ * ye * v₀⁻¹)) := by
      rw [← hr2, sq, sq, sq]
      calc ye * r * (ye * r) = ye * (r * ye) * r := by group
        _ = ye * (ye * r) * r := by rw [hcomm]
        _ = ye * ye * (r * r) := by group
    refine hc.eq_one_of_v_eq_zero h.ha hK' (e1 ▸ mul_mem hA2 hδA) ?_
    rw [e1, hc.v_mul_szA₁ h.ha hK' hA2 hδA, (hc.sq hye).2, hcv₀ ye hye, hue]
    rw [pow_succ (c + e), pow_succ c, SzC1.frob_add, SzC1.frob_add] at he
    rw [mul_pow, pow_succ e]
    linear_combination he
  rw [← hMeq] at hzC
  obtain ⟨y₁, hy₁, hy₁z⟩ := hzC
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy₁z
  have hy₁2 : y₁ ^ 2 = 1 := by
    have e1 : g * y₁ ^ 2 * g⁻¹ = 1 := by rw [← conj_pow, hy₁z, hz2]
    calc y₁ ^ 2 = g⁻¹ * (g * y₁ ^ 2 * g⁻¹) * g := by group
      _ = 1 := by rw [e1]; group
  have hy₁A := SzC1.mem_szA₁_of_sq_eq_one hc h.ha hK' hy₁ hy₁2
  have hzV : ye * r ∈ V := by
    rw [← hy₁z]
    exact h.conj_V_of_mem_normalizer hgN (h.le hy₁A)
  have hyeV : ye ∈ V := by simpa using mul_mem hzV (inv_mem hrV)
  have hyeA : ye ∈ szA₁ (szT₁ L T) := h.inf_eq_szA₁ ▸ mem_inf.mpr ⟨hye, hyeV⟩
  have := hc.u_eq_zero_of_mem_szA₁ h.ha hK' hyeA
  rw [hue] at this
  exact he0 this

end Lambda

theorem false_of_lambda_ne_zero
    (h : SzC1Stage G L f a t T d V U U₁ k) (hμ : U₁ ≤ centralizer (V : Set G))
    (hlam : ¬ U₁ ≤ szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) : False := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  exact h.false_of_lambda_ne_zero' hK hc hκ hμ hlam

end SzC1Stage

end CFSG.SeitzReduction.RankOne
