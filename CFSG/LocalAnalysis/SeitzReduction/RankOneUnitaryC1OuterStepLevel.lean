module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1StageBranch
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpConf
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1PushUpMove

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools CFSG.GH74.Uniqueness.Bender

structure U3C1OuterStepHyp (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T R₂ D : Subgroup G) (d : G) (V : Subgroup G) (k : ℕ) : Prop where
  start : U3Start G L f t T
  card_sylow : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2
  r2 : U3R2 G L (szT₁ L T) R₂ t f
  inv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹
  ne : ∃ r ∈ R₂, r ^ 2 ≠ 1
  outer : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t
  cartan : U3C1Cartan L T D d
  conf : U3C1OuterConf G L f t T R₂ D V k
  not_sylow : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V
  move : ∃ y ∈ normalizer (szR (szT₁ L T) V t : Set G), ∃ r ∈ V, (∀ x ∈ V, x ^ 2 ≠ r) ∧
    y * t * y⁻¹ = r * t

structure U3C1OuterLevelData (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G)
    (T D V U U₁ : Subgroup G) (k : ℕ) : Prop where
  U_le : U ≤ normalizer (szR (szT₁ L T) V t : Set G)
  U_normal : normalizer (szR (szT₁ L T) V t : Set G) ≤ normalizer (U : Set G)
  isSylowOf : IsSylowOf 2 (U ⊔ T) (normalizer (szR (szT₁ L T) V t : Set G))
  card_U : Nat.card U = 2 * (2 ^ f) ^ (k + 4)
  szR_le : szR (szT₁ L T) V t ≤ U
  conj_t_not_mem : ∀ u ∈ U, u ∉ szR (szT₁ L T) V t → u * t * u⁻¹ ∉ szA L T t
  conj_szA₁ : ∀ u ∈ U, ∀ b ∈ szA₁ (szT₁ L T), u * b * u⁻¹ = b
  conj_T₁ : ∀ u ∈ U, ∀ y ∈ szT₁ L T, y⁻¹ * (u * y * u⁻¹) ∈ szA₁ (szT₁ L T)
  conj_V₁ : ∀ u ∈ U₁, ∀ r ∈ V, r⁻¹ * (u * r * u⁻¹) ∈ szA₁ (szT₁ L T)
  inf_centralizer : U ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t
  U₁_le : U₁ ≤ U
  U₁_normal : U ≤ normalizer (U₁ : Set G)
  sup_eq : U₁ ⊔ zpowers t = U
  t_not_mem : t ∉ U₁
  inf_eq : U₁ ⊓ szR (szT₁ L T) V t = szT₁ L T ⊔ V
  D_le : D ≤ normalizer (U₁ : Set G)
  T_le : T ≤ normalizer (U₁ : Set G)
  torus : ∃ e ∈ normalizer (U₁ : Set G), e ∈ normalizer (szT₁ L T : Set G) ∧ e * t = t * e ∧
    (∀ b ∈ szA₁ (szT₁ L T), e * b * e⁻¹ = b) ∧
    (∀ y ∈ szT₁ L T, y⁻¹ * (e * y * e⁻¹) ∈ szA₁ (szT₁ L T) → y ∈ szA₁ (szT₁ L T)) ∧
    ∀ r ∈ V, e * r * e⁻¹ = r

@[expose] def outerV₁ {G : Type} [Group G] (L T U₁ : Subgroup G) : Subgroup G :=
  U₁ ⊓ centralizer (szT₁ L T : Set G)

theorem mem_outerV₁ {G : Type} [Group G] {L T U₁ : Subgroup G} {x : G} :
    x ∈ outerV₁ L T U₁ ↔ x ∈ U₁ ∧ x ∈ centralizer (szT₁ L T : Set G) :=
  mem_inf

structure U3C1OuterV₁Facts {G : Type} [Group G] (L T V U₁ : Subgroup G) (f k : ℕ) : Prop where
  comm : ∀ x ∈ outerV₁ L T U₁, ∀ y ∈ outerV₁ L T U₁, x * y = y * x
  card : Nat.card (outerV₁ L T U₁) = (2 ^ f) ^ (k + 2)
  sq_mem : ∀ x ∈ outerV₁ L T U₁, x ^ 2 ∈ V
  omega : ∀ x ∈ outerV₁ L T U₁, x ^ 2 = 1 → x ∈ szA₁ (szT₁ L T)

@[expose] def U3C1OuterMuHighInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (k : ℕ), U3C1OuterStepHyp G L f t T R₂ D d V k →
    U3C1OuterLevelData G L f t T D V U U₁ k → 2 ≤ k → U₁ ≤ centralizer (V : Set G)

@[expose] def U3C1OuterMuOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G), U3C1OuterStepHyp G L f t T R₂ D d V 1 →
    U3C1OuterLevelData G L f t T D V U U₁ 1 → (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) →
    U₁ ≤ centralizer (V : Set G)

@[expose] def U3C1OuterMuOneSylowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G), U3C1OuterStepHyp G L f t T R₂ D d V 1 →
    U3C1OuterLevelData G L f t T D V U U₁ 1 → (∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) →
    U₁ ≤ centralizer (V : Set G)

@[expose] def U3C1OuterStructureInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (k : ℕ), U3C1OuterStepHyp G L f t T R₂ D d V k →
    U3C1OuterLevelData G L f t T D V U U₁ k → U₁ ≤ centralizer (V : Set G) →
    U₁ = szT₁ L T ⊔ outerV₁ L T U₁ → U3C1OuterV₁Facts L T V U₁ f k

@[expose] def U3C1OuterNuInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G) (k : ℕ), U3C1OuterStepHyp G L f t T R₂ D d V k →
    U3C1OuterLevelData G L f t T D V U U₁ k → U₁ ≤ centralizer (V : Set G) →
    U₁ = szT₁ L T ⊔ outerV₁ L T U₁ → U3C1OuterV₁Facts L T V U₁ f k →
    (∃ g ∈ normalizer ((T ⊔ outerV₁ L T U₁ : Subgroup G) : Set G), g ∉ T ⊔ outerV₁ L T U₁ ∧
      ∃ y ∈ szT₁ L T, ∃ u ∈ outerV₁ L T U₁, g * t * g⁻¹ = y * u * t ∧ y * u ∉ szT₁ L T ⊔ V) →
    ∀ x ∈ outerV₁ L T U₁, t * x * t⁻¹ = x⁻¹

theorem outerStep_mem_or_mul_mem {G : Type} [Group G] {Y : Subgroup G} {t : G} (ht : t * t = 1)
    (htN : t ∈ normalizer (Y : Set G)) {x : G} (hx : x ∈ Y ⊔ zpowers t) : x ∈ Y ∨ x * t ∈ Y := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [sup_comm] at hx
  obtain ⟨b, hb, a, ha, rfl⟩ := ncyc_exists_mul_of_mem_sup (zpowers_le.mpr htN) hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
  rcases Int.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    have htt : t ^ (j + j) = 1 := by
      rw [← two_mul, zpow_mul, zpow_two, ht, one_zpow]
    rw [htt, one_mul]
    exact ha
  · right
    have htt : t ^ (2 * j + 1) = t := by
      rw [zpow_add, zpow_mul, zpow_two, ht, one_zpow, one_mul, zpow_one]
    rw [htt]
    have := (mem_normalizer_iff.mp htN a).mp ha
    rwa [htinv] at this

theorem mem_normalizer_outerV₁ {G : Type} [Group G] [Finite G] {L T U₁ : Subgroup G} {g : G}
    (hgU : g ∈ normalizer (U₁ : Set G)) (hgT : g ∈ normalizer (szT₁ L T : Set G)) :
    g ∈ normalizer (outerV₁ L T U₁ : Set G) := by
  refine mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => ?_
  obtain ⟨hxU, hxC⟩ := mem_outerV₁.mp hx
  refine mem_outerV₁.mpr ⟨(mem_normalizer_iff''.mp hgU x).mp hxU,
    mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hy' : g * y * g⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hgT y).mp hy
  have e := mem_centralizer_iff.mp hxC _ hy'
  calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
    _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [e]
    _ = g⁻¹ * x * g * y := by group

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem outerStep_mem_szA₁_of_conj_eq (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {V V₁ : Subgroup G} {k : ℕ}
    (hk : 1 ≤ k) (hV₁ab : ∀ u ∈ V₁, ∀ u' ∈ V₁, u * u' = u' * u)
    (hVpow : ∀ r ∈ V, r ^ 2 ^ (k + 1) = 1) (hV₁card : Nat.card V₁ = (2 ^ f) ^ (k + 2))
    (hsq : ∀ u ∈ V₁, u ^ 2 ∈ V) (hΩ : ∀ u ∈ V₁, u ^ 2 = 1 → u ∈ szA₁ (szT₁ L T))
    (hVinv : ∀ r ∈ V, t * r * t⁻¹ = r⁻¹) {u : G} (hu : u ∈ V₁) (htu : t * u * t⁻¹ = u) :
    u ∈ szA₁ (szT₁ L T) := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hV₁pow : ∀ x ∈ V₁, x ^ 2 ^ (k + 2) = 1 := fun x hx => by
    rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by ring, pow_mul]
    exact hVpow _ (hsq x hx)
  have hu2 := hsq u hu
  have ht2 : t * u ^ 2 * t⁻¹ = u ^ 2 := by rw [← conj_pow, htu]
  rw [hVinv _ hu2] at ht2
  have hu4 : u ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add]
    nth_rewrite 1 [← ht2]
    exact inv_mul_cancel _
  obtain ⟨z, hz, hzu⟩ := pushUp_exists_pow_eq hV₁ab (pow_pos (by norm_num) f) hV₁card hV₁pow hΩ
    (le_of_eq hA₁card) (show 2 ≤ k + 2 by omega) hu hu4
  have huV : u ∈ V := by
    rw [← hzu, show k + 2 - 2 = (k - 1) + 1 by omega, pow_succ, pow_mul]
    exact hsq _ (pow_mem hz _)
  refine hΩ u hu ?_
  have h1 : u⁻¹ = u := by rw [← hVinv u huV, htu]
  rw [sq]
  nth_rewrite 2 [← h1]
  exact mul_inv_cancel u

theorem outerStep_exists_escape (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {D : Subgroup G} {d : G}
    (hC : U3C1Cartan L T D d) {V V₁ : Subgroup G} {k : ℕ} (hk : 1 ≤ k)
    (hV₁c : ∀ y ∈ szT₁ L T, ∀ u ∈ V₁, y * u = u * y)
    (hV₁ab : ∀ u ∈ V₁, ∀ u' ∈ V₁, u * u' = u' * u) (hAV : szA₁ (szT₁ L T) ≤ V) (hVV₁ : V ≤ V₁)
    (hVcard : Nat.card V = (2 ^ f) ^ (k + 1)) (hVpow : ∀ r ∈ V, r ^ 2 ^ (k + 1) = 1)
    (hV₁card : Nat.card V₁ = (2 ^ f) ^ (k + 2)) (hsq : ∀ u ∈ V₁, u ^ 2 ∈ V)
    (hΩ : ∀ u ∈ V₁, u ^ 2 = 1 → u ∈ szA₁ (szT₁ L T)) (hVinv : ∀ r ∈ V, t * r * t⁻¹ = r⁻¹)
    (hσ : ∀ u ∈ V₁, u * t * u⁻¹ * t⁻¹ ∈ V) (hTV₁ : T ≤ normalizer (V₁ : Set G))
    (hDV₁ : D ≤ normalizer (V₁ : Set G)) (hnS : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V₁) :
    ∃ g ∈ normalizer ((T ⊔ V₁ : Subgroup G) : Set G), g ∉ T ⊔ V₁ ∧
      ∃ y ∈ szT₁ L T, ∃ u ∈ V₁, g * t * g⁻¹ = y * u * t ∧ y * u ∉ szT₁ L T ⊔ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hA₁card, -, -, hinvT₁, -, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hV₁pow : ∀ x ∈ V₁, x ^ 2 ^ (k + 2) = 1 := fun x hx => by
    rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by ring, pow_mul]
    exact hVpow _ (hsq x hx)
  have hV₁t : ∀ u ∈ V₁, t * u * t⁻¹ = u → u ∈ szA₁ (szT₁ L T) := fun u hu htu =>
    h.outerStep_mem_szA₁_of_conj_eq hS2 hk hV₁ab hVpow hV₁card hsq hΩ hVinv hu htu
  have hV₁T₁ : V₁ ≤ centralizer (szT₁ L T : Set G) := fun u hu =>
    mem_centralizer_iff.mpr fun y hy => hV₁c y hy u hu
  have hV₁2 : IsPGroup 2 V₁ := IsPGroup.of_card (n := f * (k + 2)) (by rw [hV₁card, ← pow_mul])
  have hP2 : IsPGroup 2 (T ⊔ V₁ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.isPGroup hV₁2 hTV₁
  obtain ⟨z, hzN, hzP, P', hP'2, hPP', hzP'⟩ := exists_normalizer_not_mem_of_not_isSylow hP2 hnS
  have hq3 : 3 ≤ 2 ^ f :=
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  have hU8 := pushUp_exists_pow_four_ne hV₁ab hq3 (show 3 ≤ k + 2 by omega) hV₁card hV₁pow hΩ
    (le_of_eq hA₁card)
  have hsign := fun w hwT hw2 hwS => h.sign_of_cartan hS2 hC.mem hC.le_normalizer hC.odd hC.trans
    hC.conj hV₁ab hV₁T₁ (show 2 ≤ k + 2 by omega) hV₁card hV₁pow hΩ hDV₁ hTV₁ (w := w) hwT hw2
    hwS
  obtain ⟨y, hy, u, hu, hzt⟩ := (h.pushUp_exists_mul_t_of_conj_normalizer hS2 hV₁c hV₁ab
    (hAV.trans hVV₁) hV₁t hTV₁ hU8 hsign hv hP2 (inv_mem hzN)).1
  rw [inv_inv] at hzt
  refine ⟨z, hzN, hzP, y, hy, u, hu, hzt, fun hyu => hzP ?_⟩
  have hT₁NV : szT₁ L T ≤ normalizer (V : Set G) := fun y' hy' =>
    mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
      have e := hV₁c y' hy' r (hVV₁ hr)
      rw [show y'⁻¹ * r * y' = r by rw [mul_assoc, ← e, inv_mul_cancel_left]]
      exact hr
  obtain ⟨y', hy', r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup hT₁NV hyu
  have huV : u ∈ V := by
    have e : u * r⁻¹ = y⁻¹ * y' := by
      calc u * r⁻¹ = y⁻¹ * (y * u) * r⁻¹ := by group
        _ = y⁻¹ * (y' * r) * r⁻¹ := by rw [hyr]
        _ = y⁻¹ * y' := by group
    have hm : u * r⁻¹ ∈ szA₁ (szT₁ L T) := by
      refine hV₁t _ (mul_mem hu (inv_mem (hVV₁ hr))) ?_
      rw [e]
      have hyy : y⁻¹ * y' ∈ szT₁ L T := mul_mem (inv_mem hy) hy'
      rw [← mem_centralizer_iff.mp htC _ hyy, mul_inv_cancel_right]
    rw [show u = (u * r⁻¹) * r by group]
    exact mul_mem (hAV hm) hr
  have hyt : y * t = t * y := mem_centralizer_iff.mp htC y hy
  have hyu' : y * u = u * y := hV₁c y hy u hu
  have htu : t * u = u⁻¹ * t := by
    have := hVinv u huV
    calc t * u = t * u * t⁻¹ * t := by group
      _ = u⁻¹ * t := by rw [this]
  have hsq1 : (y * u * t) ^ 2 = y ^ 2 := by
    calc (y * u * t) ^ 2 = y * u * (t * y) * u * t := by rw [sq]; group
      _ = y * u * (y * t) * u * t := by rw [hyt]
      _ = y * (u * y) * (t * u) * t := by group
      _ = y * (y * u) * (u⁻¹ * t) * t := by rw [← hyu', htu]
      _ = y * y * (t * t) := by group
      _ = y ^ 2 := by rw [ht2, mul_one, sq]
  have hx2 : (z * t * z⁻¹) ^ 2 = 1 := by
    rw [sq, show z * t * z⁻¹ * (z * t * z⁻¹) = z * (t * t) * z⁻¹ by group, ht2, mul_one,
      mul_inv_cancel]
  rw [hzt, hsq1] at hx2
  have hyA := hinvT₁ y hy hx2
  set r₀ := y * u with hr₀
  have hr₀V : r₀ ∈ V := mul_mem (hAV hyA) huV
  obtain ⟨w, hw, hwr⟩ : ∃ w ∈ V₁, w * t * w⁻¹ * t⁻¹ = r₀ := by
    have hψmul : ∀ a ∈ V₁, ∀ b ∈ V₁, (a * b) * t * (a * b)⁻¹ * t⁻¹ =
        (a * t * a⁻¹ * t⁻¹) * (b * t * b⁻¹ * t⁻¹) := by
      intro a ha b hb
      have hc := hV₁ab a ha _ (hVV₁ (hσ b hb))
      calc (a * b) * t * (a * b)⁻¹ * t⁻¹ =
            (a * (b * t * b⁻¹ * t⁻¹)) * (t * a⁻¹ * t⁻¹) := by group
        _ = ((b * t * b⁻¹ * t⁻¹) * a) * (t * a⁻¹ * t⁻¹) := by rw [hc]
        _ = (b * t * b⁻¹ * t⁻¹) * (a * t * a⁻¹ * t⁻¹) := by group
        _ = (a * t * a⁻¹ * t⁻¹) * (b * t * b⁻¹ * t⁻¹) :=
          hV₁ab _ (hVV₁ (hσ b hb)) _ (hVV₁ (hσ a ha))
    let ψ : V₁ →* V₁ :=
      { toFun := fun a => ⟨(a : G) * t * (a : G)⁻¹ * t⁻¹, hVV₁ (hσ a a.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (hψmul a a.2 b b.2) }
    have hker : Nat.card ψ.ker ≤ 2 ^ f := by
      rw [← hA₁card]
      refine Nat.card_le_card_of_injective (fun a : ψ.ker => (⟨((a : V₁) : G), ?_⟩ :
        szA₁ (szT₁ L T))) ?_
      · have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
        change ((a : V₁) : G) * t * ((a : V₁) : G)⁻¹ * t⁻¹ = 1 at h1
        refine hV₁t _ (a : V₁).2 ?_
        rw [mul_inv_eq_one] at h1
        have hat : ((a : V₁) : G) * t = t * ((a : V₁) : G) := by
          calc ((a : V₁) : G) * t =
                ((a : V₁) : G) * t * ((a : V₁) : G)⁻¹ * ((a : V₁) : G) := by group
            _ = t * ((a : V₁) : G) := by rw [h1]
        rw [← hat, mul_inv_cancel_right]
      · intro a b hab
        exact Subtype.ext (Subtype.ext (congrArg (fun x : szA₁ (szT₁ L T) => (x : G)) hab))
    have hrange : ψ.range = V.subgroupOf V₁ := by
      refine eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact mem_subgroupOf.mpr (hσ a a.2)
      · have h1 := card_mul_index ψ.ker
        rw [Subgroup.index_ker] at h1
        have h2 : Nat.card (V.subgroupOf V₁) = Nat.card V :=
          Nat.card_congr (subgroupOfEquivOfLe hVV₁).toEquiv
        rw [h2, hVcard]
        rw [hV₁card] at h1
        have hq0 : 0 < 2 ^ f := pow_pos (by norm_num) f
        by_contra hlt
        push Not at hlt
        have h3 : Nat.card ψ.ker * Nat.card ψ.range < 2 ^ f * (2 ^ f) ^ (k + 1) :=
          lt_of_le_of_lt (Nat.mul_le_mul_right _ hker) (Nat.mul_lt_mul_of_pos_left hlt hq0)
        rw [h1, show (2 ^ f) ^ (k + 2) = 2 ^ f * (2 ^ f) ^ (k + 1) by ring] at h3
        exact lt_irrefl _ h3
    have hr₀' : (⟨r₀, hVV₁ hr₀V⟩ : V₁) ∈ ψ.range := by
      rw [hrange]
      exact mem_subgroupOf.mpr hr₀V
    obtain ⟨a, ha⟩ := hr₀'
    exact ⟨a, a.2, congrArg Subtype.val ha⟩
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := h.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr h.le]⟩
  have hc' : (w⁻¹ * z) * t = t * (w⁻¹ * z) := by
    have e : z * t * z⁻¹ = w * t * w⁻¹ := by
      rw [hzt, ← hwr]
      group
    calc (w⁻¹ * z) * t = w⁻¹ * (z * t * z⁻¹) * z := by group
      _ = w⁻¹ * (w * t * w⁻¹) * z := by rw [e]
      _ = t * (w⁻¹ * z) := by group
  have hwP' : w ∈ P' := hPP' (mem_sup_right hw)
  have hH : T ⊔ zpowers (w⁻¹ * z) ≤ centralizer ({t} : Set G) :=
    sup_le h.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hc'))
  have hHP : T ⊔ zpowers (w⁻¹ * z) ≤ P' :=
    sup_le (le_sup_left.trans hPP') (zpowers_le.mpr (mul_mem (inv_mem hwP') hzP'))
  have heq := hTsyl.eq_of_le le_sup_left hH (hP'2.to_le hHP)
  have hwzT : w⁻¹ * z ∈ T := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  rw [show z = w * (w⁻¹ * z) by group]
  exact mul_mem (mem_sup_right hw) (mem_sup_left hwzT)

theorem outerStep_false_of_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t) {D : Subgroup G} {d : G}
    (hC : U3C1Cartan L T D d) {V V₁ : Subgroup G} {k : ℕ} (hk : 1 ≤ k)
    (hV₁c : ∀ y ∈ szT₁ L T, ∀ u ∈ V₁, y * u = u * y)
    (hV₁ab : ∀ u ∈ V₁, ∀ u' ∈ V₁, u * u' = u' * u) (hAV : szA₁ (szT₁ L T) ≤ V) (hVV₁ : V ≤ V₁)
    (hVpow : ∀ r ∈ V, r ^ 2 ^ (k + 1) = 1) (hV₁card : Nat.card V₁ = (2 ^ f) ^ (k + 2))
    (hsq : ∀ u ∈ V₁, u ^ 2 ∈ V) (hΩ : ∀ u ∈ V₁, u ^ 2 = 1 → u ∈ szA₁ (szT₁ L T))
    (hVinv : ∀ r ∈ V, t * r * t⁻¹ = r⁻¹) (hTV₁ : T ≤ normalizer (V₁ : Set G))
    (hDV₁ : D ≤ normalizer (V₁ : Set G)) (hsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ V₁) :
    False := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hV₁pow : ∀ x ∈ V₁, x ^ 2 ^ (k + 2) = 1 := fun x hx => by
    rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by ring, pow_mul]
    exact hVpow _ (hsq x hx)
  have hV₁T₁ : V₁ ≤ centralizer (szT₁ L T : Set G) := fun u hu =>
    mem_centralizer_iff.mpr fun y hy => hV₁c y hy u hu
  have hq3 : 3 ≤ 2 ^ f :=
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
  exact h.false_of_ncyc_sylow_stage hS2 hV₁c hV₁ab (hAV.trans hVV₁)
    (fun u hu htu => h.outerStep_mem_szA₁_of_conj_eq hS2 hk hV₁ab hVpow hV₁card hsq hΩ hVinv hu
      htu) hTV₁
    (pushUp_exists_pow_four_ne hV₁ab hq3 (by omega) hV₁card hV₁pow hΩ (le_of_eq hA₁card))
    (fun w hwT hw2 hwS => h.sign_of_cartan hS2 hC.mem hC.le_normalizer hC.odd hC.trans hC.conj
      hV₁ab hV₁T₁ (by omega) hV₁card hV₁pow hΩ hDV₁ hTV₁ hwT hw2 hwS) hv hsyl

end U3Start

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T D V U U₁ : Subgroup G} {k : ℕ}

theorem sup_le_U₁ (hL : U3C1OuterLevelData G L f t T D V U U₁ k) : szT₁ L T ⊔ V ≤ U₁ :=
  hL.inf_eq ▸ inf_le_left

theorem t_mem_U (hL : U3C1OuterLevelData G L f t T D V U U₁ k) : t ∈ U :=
  hL.szR_le (mem_szR_right _ _ _)

theorem V_le_V₁ (hL : U3C1OuterLevelData G L f t T D V U U₁ k) {R₂ : Subgroup G}
    (hc : U3C1OuterConf G L f t T R₂ D V k) : V ≤ outerV₁ L T U₁ := fun _ hr =>
  mem_outerV₁.mpr ⟨hL.sup_le_U₁ (mem_sup_right hr), hc.le_centralizer hr⟩

theorem comm_t_mem (hL : U3C1OuterLevelData G L f t T D V U U₁ k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} (hc : U3C1OuterConf G L f t T R₂ D V k) {x : G} (hx : x ∈ U) :
    x * t * x⁻¹ * t⁻¹ ∈ V := by
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, -, hinvT₁, -, -⟩ := h.facts_of_card_sylow hS2
  have htC := h.mem_centralizer_szT₁
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hVc : ∀ y ∈ szT₁ L T, ∀ u ∈ V, y * u = u * y := fun y hy u hu =>
    mem_centralizer_iff.mp (hc.le_centralizer hu) y hy
  have hxR : x * t * x⁻¹ ∈ szR (szT₁ L T) V t :=
    (mem_normalizer_iff.mp (hL.U_le hx) t).mp (mem_szR_right _ _ _)
  have htN : t ∈ normalizer ((szT₁ L T ⊔ V : Subgroup G) : Set G) :=
    h.sup_le_normalizer_sup_szT₁ hS2 hVc hc.T_le (mem_sup_left htT)
  rcases outerStep_mem_or_mul_mem ht2 htN hxR with h1 | h1
  · exfalso
    apply hL.t_not_mem
    have hx' : x⁻¹ ∈ U := inv_mem hx
    have hU₁ : x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ ∈ U₁ :=
      (mem_normalizer_iff.mp (hL.U₁_normal hx') _).mp (hL.sup_le_U₁ h1)
    rwa [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at hU₁
  · have hT₁NV : szT₁ L T ≤ normalizer (V : Set G) := fun y' hy' =>
      mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => by
        have e := hVc y' hy' r hr
        rw [show y'⁻¹ * r * y' = r by rw [mul_assoc, ← e, inv_mul_cancel_left]]
        exact hr
    obtain ⟨y, hy, r, hr, hyr⟩ := ncyc_exists_mul_of_mem_sup hT₁NV h1
    have hxe : x * t * x⁻¹ = y * r * t := by
      rw [hyr, mul_assoc (x * t * x⁻¹) t t, ht2, mul_one]
    have hyt : y * t = t * y := mem_centralizer_iff.mp htC y hy
    have htr : t * r = r⁻¹ * t := by
      have := hc.inv r hr
      calc t * r = t * r * t⁻¹ * t := by group
        _ = r⁻¹ * t := by rw [this]
    have hsq1 : (y * r * t) ^ 2 = y ^ 2 := by
      calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
        _ = y * r * (y * t) * r * t := by rw [hyt]
        _ = y * (r * y) * (t * r) * t := by group
        _ = y * (y * r) * (r⁻¹ * t) * t := by rw [← hVc y hy r hr, htr]
        _ = y * y * (t * t) := by group
        _ = y ^ 2 := by rw [ht2, mul_one, sq]
    have hx2 : (x * t * x⁻¹) ^ 2 = 1 := by
      rw [sq, show x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ by group, ht2, mul_one,
        mul_inv_cancel]
    rw [hxe, hsq1] at hx2
    have hyA := hinvT₁ y hy hx2
    rw [hxe, show y * r * t * t⁻¹ = y * r by group]
    exact mul_mem (hc.le hyA) hr

theorem lambda (hL : U3C1OuterLevelData G L f t T D V U U₁ k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} (hc : U3C1OuterConf G L f t T R₂ D V k) :
    U₁ = szT₁ L T ⊔ outerV₁ L T U₁ := by
  obtain ⟨-, -, hA₁comm, -, -, -, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨e, heU, heT, het, heA, hfpf, heV⟩ := hL.torus
  have htC := h.mem_centralizer_szT₁
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hcomm : ∀ y ∈ szT₁ L T, ∀ y' ∈ szT₁ L T, y * y' * y⁻¹ * y'⁻¹ ∈ szA₁ (szT₁ L T) := by
    intro y hy y' hy'
    rw [hA₁comm]
    have := commutator_mem_commutator hy hy'
    rwa [commutatorElement_def] at this
  have hcen : ∀ a ∈ szA₁ (szT₁ L T), ∀ y ∈ szT₁ L T, a * y = y * a := fun a ha y hy =>
    (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm
  refine le_antisymm (fun x hx => ?_) (sup_le hT₁U₁ inf_le_left)
  have hxU := hL.U₁_le hx
  have hex : e * x * e⁻¹ ∈ U₁ := (mem_normalizer_iff.mp heU x).mp hx
  have hσx := hL.comm_t_mem h hS2 hc hxU
  have hz : x⁻¹ * (e * x * e⁻¹) ∈ szT₁ L T := by
    have hzU₁ : x⁻¹ * (e * x * e⁻¹) ∈ U₁ := mul_mem (inv_mem hx) hex
    have h1 : e * (x * t * x⁻¹ * t⁻¹) * e⁻¹ = x * t * x⁻¹ * t⁻¹ := heV _ hσx
    have het' : e⁻¹ * t * e = t := by
      calc e⁻¹ * t * e = e⁻¹ * (t * e) := by group
        _ = e⁻¹ * (e * t) := by rw [het]
        _ = t := by group
    have h2 : (e * x * e⁻¹) * t * (e * x * e⁻¹)⁻¹ = x * t * x⁻¹ := by
      calc (e * x * e⁻¹) * t * (e * x * e⁻¹)⁻¹ = e * x * (e⁻¹ * t * e) * x⁻¹ * e⁻¹ := by group
        _ = e * x * t * x⁻¹ * e⁻¹ := by rw [het']
        _ = e * (x * t * x⁻¹ * t⁻¹) * e⁻¹ * (e * t * e⁻¹) := by group
        _ = (x * t * x⁻¹ * t⁻¹) * (e * t * e⁻¹) := by rw [h1]
        _ = (x * t * x⁻¹ * t⁻¹) * t := by rw [het, mul_inv_cancel_right]
        _ = x * t * x⁻¹ := by group
    have hzt : x⁻¹ * (e * x * e⁻¹) ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc x⁻¹ * (e * x * e⁻¹) * t =
            x⁻¹ * ((e * x * e⁻¹) * t * (e * x * e⁻¹)⁻¹) * (e * x * e⁻¹) := by group
        _ = x⁻¹ * (x * t * x⁻¹) * (e * x * e⁻¹) := by rw [h2]
        _ = t * (x⁻¹ * (e * x * e⁻¹)) := by group
    have hmem : x⁻¹ * (e * x * e⁻¹) ∈ U ⊓ centralizer ({t} : Set G) :=
      mem_inf.mpr ⟨hL.U₁_le hzU₁, hzt⟩
    rw [hL.inf_centralizer] at hmem
    obtain ⟨y, hy, z', hz', hyz⟩ := exists_mul_eq_of_mem_sup_zpowers htC hmem
    rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz' with hz1 | hz1
    · rw [← hyz, hz1, mul_one]
      exact hy
    · exfalso
      apply hL.t_not_mem
      rw [hz1] at hyz
      rw [show t = y⁻¹ * (x⁻¹ * (e * x * e⁻¹)) by rw [← hyz]; group]
      exact mul_mem (inv_mem (hT₁U₁ hy)) hzU₁
  set z := x⁻¹ * (e * x * e⁻¹) with hzdef
  obtain ⟨y, hy, hyz⟩ := U3C1.exists_inv_mul_conj_of_fixedPointFree hcomm heT heA hfpf
    (inv_mem hz)
  set p := y⁻¹ * (e * y * e⁻¹) with hpdef
  have hpT : p ∈ szT₁ L T := mul_mem (inv_mem hy) ((mem_normalizer_iff.mp heT y).mp hy)
  set w := y * x with hwdef
  have hwU₁ : w ∈ U₁ := mul_mem (hT₁U₁ hy) hx
  have hwU := hL.U₁_le hwU₁
  have hwe : w⁻¹ * (e * w * e⁻¹) ∈ szA₁ (szT₁ L T) := by
    have e1 : w⁻¹ * (e * w * e⁻¹) = (x⁻¹ * p * x) * z := by
      rw [hwdef, hpdef, hzdef]
      group
    have ha : p⁻¹ * (x⁻¹ * p * x) ∈ szA₁ (szT₁ L T) := by
      have := hL.conj_T₁ x⁻¹ (inv_mem hxU) p hpT
      rwa [inv_inv] at this
    have hzp : z * p ∈ szA₁ (szT₁ L T) := by
      have := inv_mem hyz
      rwa [mul_inv_rev, inv_inv, inv_inv] at this
    have hpz : p * z ∈ szA₁ (szT₁ L T) := by
      have e2 : p * z = z⁻¹ * ((z * p) * z) := by group
      rw [e2, hcen _ hzp z hz, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hzp
    have e3 : (x⁻¹ * p * x) * z = (p * z) * (p⁻¹ * (x⁻¹ * p * x)) := by
      have hac := hcen _ ha z hz
      calc (x⁻¹ * p * x) * z = p * ((p⁻¹ * (x⁻¹ * p * x)) * z) := by group
        _ = p * (z * (p⁻¹ * (x⁻¹ * p * x))) := by rw [hac]
        _ = (p * z) * (p⁻¹ * (x⁻¹ * p * x)) := by group
    rw [e1, e3]
    exact mul_mem hpz ha
  have hinv : ∀ y' ∈ szT₁ L T, (e * y' * e⁻¹)⁻¹ * (w * (e * y' * e⁻¹) * w⁻¹) =
      y'⁻¹ * (w * y' * w⁻¹) := by
    intro y' hy'
    set c := w⁻¹ * (e * w * e⁻¹) with hcdef
    have hy'' : e * y' * e⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp heT y').mp hy'
    have hδ := hL.conj_T₁ w hwU y' hy'
    have h1 := heA _ hδ
    have hcy : c * (e * y' * e⁻¹) = (e * y' * e⁻¹) * c := hcen c hwe _ hy''
    have hew : e * w * e⁻¹ = w * c := by
      rw [hcdef]
      group
    rw [← h1]
    calc (e * y' * e⁻¹)⁻¹ * (w * (e * y' * e⁻¹) * w⁻¹)
        = (e * y' * e⁻¹)⁻¹ * (w * (c * (e * y' * e⁻¹) * c⁻¹) * w⁻¹) := by
          rw [hcy, mul_inv_cancel_right]
      _ = (e * y' * e⁻¹)⁻¹ * ((w * c) * (e * y' * e⁻¹) * (w * c)⁻¹) := by group
      _ = (e * y' * e⁻¹)⁻¹ * ((e * w * e⁻¹) * (e * y' * e⁻¹) * (e * w * e⁻¹)⁻¹) := by
          rw [hew]
      _ = e * (y'⁻¹ * (w * y' * w⁻¹)) * e⁻¹ := by group
  have hwC := U3C1.commute_of_fixedPointFree hcomm heT heA hfpf (hL.conj_szA₁ w hwU)
    (hL.conj_T₁ w hwU) hinv
  have hwV₁ : w ∈ outerV₁ L T U₁ := mem_outerV₁.mpr ⟨hwU₁, mem_centralizer_iff.mpr fun y' hy' => by
    calc y' * w = (w * y' * w⁻¹) * w := by rw [hwC y' hy']
      _ = w * y' := by group⟩
  rw [show x = y⁻¹ * w by rw [hwdef]; group]
  exact mul_mem (mem_sup_left (inv_mem hy)) (mem_sup_right hwV₁)

theorem conf_succ (hL : U3C1OuterLevelData G L f t T D V U U₁ k)
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} {d : G} (hC : U3C1Cartan L T D d) (hc : U3C1OuterConf G L f t T R₂ D V k)
    (hF : U3C1OuterV₁Facts L T V U₁ f k) (hν : ∀ x ∈ outerV₁ L T U₁, t * x * t⁻¹ = x⁻¹) :
    U3C1OuterConf G L f t T R₂ D (outerV₁ L T U₁) (k + 1) := by
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := h.start_of_card_sylow hS2
  have hVV₁ := hL.V_le_V₁ hc
  exact
    { one_le := by omega
      R₂_le := hc.R₂_le.trans hVV₁
      le_centralizer := inf_le_right
      comm := hF.comm
      card := by rw [hF.card]
      omega := hF.omega
      pow := fun x hx => by
        rw [show 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) by ring, pow_mul]
        exact hc.pow _ (hF.sq_mem x hx)
      le := hc.le.trans hVV₁
      inv := hν
      T_le := fun s hs => mem_normalizer_outerV₁ (hL.T_le hs) (hTN₁ hs)
      D_le := fun x hx => mem_normalizer_outerV₁ (hL.D_le hx) (hC.le_normalizer hx) }

end U3C1OuterLevelData

end CFSG.SeitzReduction.RankOne
