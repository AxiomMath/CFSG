module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E}

theorem comm_iff (hc : U3RootCoords T₁ σ u v) {y y' : G} (hy : y ∈ T₁) (hy' : y' ∈ T₁) :
    y * y' = y' * y ↔ u y * σ (u y') = u y' * σ (u y) := by
  constructor
  · intro h
    have h1 := congrArg v h
    rw [hc.mul_v _ hy _ hy', hc.mul_v _ hy' _ hy] at h1
    linear_combination -h1
  · intro h
    refine hc.inj _ (mul_mem hy hy') _ (mul_mem hy' hy) ?_ ?_
    · rw [hc.mul_u _ hy _ hy', hc.mul_u _ hy' _ hy, add_comm]
    · rw [hc.mul_v _ hy _ hy', hc.mul_v _ hy' _ hy, h, add_comm (v y)]

theorem exists_hom (hc : U3RootCoords T₁ σ u v) {B : Subgroup G} (hB : B ≤ T₁) :
    ∃ ψ : B →* Multiplicative E, ∀ b : B, ψ b = Multiplicative.ofAdd (u b) :=
  ⟨{ toFun := fun b => Multiplicative.ofAdd (u b)
     map_one' := by
       show Multiplicative.ofAdd (u 1) = Multiplicative.ofAdd 0
       rw [hc.u_one]
     map_mul' := fun x y => by
       show Multiplicative.ofAdd (u ((x : G) * y)) = Multiplicative.ofAdd (u x + u y)
       rw [hc.mul_u _ (hB x.2) _ (hB y.2)] }, fun _ => rfl⟩

theorem card_eq_mul_card_range [Finite G] {A₁ B : Subgroup G}
    (hA : ∀ y ∈ T₁, y ∈ A₁ ↔ u y = 0) (hB : B ≤ T₁) {ψ : B →* Multiplicative E}
    (hψ : ∀ b : B, ψ b = Multiplicative.ofAdd (u b)) :
    Nat.card B = Nat.card (B ⊓ A₁ : Subgroup G) * Nat.card ψ.range := by
  have hker : ψ.ker = (B ⊓ A₁).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hψ, mem_subgroupOf, mem_inf, hA _ (hB b.2)]
    simp only [SetLike.coe_mem, true_and]
    exact ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
      fun h => by rw [h]; rfl⟩
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hker,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : B ⊓ A₁ ≤ B)).toEquiv] at h1
  exact h1.symm

variable [Finite G] [Finite E]

theorem card_le_of_comm (hc : U3RootCoords T₁ σ u v) {A₁ B : Subgroup G}
    (hA : ∀ y ∈ T₁, y ∈ A₁ ↔ u y = 0) (hB : B ≤ T₁) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ Nat.card A₁ * Nat.card {x : E // σ x = x} := by
  classical
  obtain ⟨ψ, hψ⟩ := hc.exists_hom hB
  rw [card_eq_mul_card_range hA hB hψ]
  refine Nat.mul_le_mul (card_le_of_le inf_le_right) ?_
  by_cases h0 : ∀ b ∈ B, u b = 0
  · have hrange : ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨b, rfl⟩
      rw [mem_bot, hψ, h0 b b.2]
      rfl
    rw [hrange, card_bot]
    have : Nonempty {x : E // σ x = x} := ⟨⟨0, map_zero σ⟩⟩
    exact Nat.card_pos
  push Not at h0
  obtain ⟨y₀, hy₀, hα⟩ := h0
  have hσα : σ (u y₀) ≠ 0 := by
    rw [map_ne_zero]
    exact hα
  have key : ∀ b ∈ B, σ (u b / u y₀) = u b / u y₀ := by
    intro b hb
    have h1 := (hc.comm_iff (hB hb) (hB hy₀)).mp (hBc b hb y₀ hy₀)
    rw [map_div₀, div_eq_div_iff hσα hα]
    linear_combination -h1
  let f : ψ.range → {x : E // σ x = x} := fun z =>
    ⟨Multiplicative.toAdd (z : Multiplicative E) / u y₀, by
      obtain ⟨b, hb⟩ := z.2
      rw [← hb, hψ]
      exact key b b.2⟩
  refine Nat.card_le_card_of_injective f fun z z' hzz' => ?_
  have h1 : Multiplicative.toAdd (z : Multiplicative E) / u y₀ =
      Multiplicative.toAdd (z' : Multiplicative E) / u y₀ := congrArg Subtype.val hzz'
  rw [div_left_inj' hα] at h1
  exact Subtype.ext (by simpa using congrArg Multiplicative.ofAdd h1)

omit [Finite E] in
theorem exists_comm_of_mem (hc : U3RootCoords T₁ σ u v) {A₁ : Subgroup G} (hA₁ : A₁ ≤ T₁)
    (hA : ∀ y ∈ T₁, y ∈ A₁ ↔ u y = 0) {y : G} (hy : y ∈ T₁) :
    ∃ B : Subgroup G, B ≤ T₁ ∧ (∀ x ∈ B, ∀ z ∈ B, x * z = z * x) ∧ y ∈ B ∧ A₁ ≤ B ∧
      Nat.card B = Nat.card A₁ * Nat.card {x : E // σ x = x} := by
  classical
  set c : E := if u y = 0 then 1 else u y with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    split_ifs with h
    · exact one_ne_zero
    · exact h
  let B : Subgroup G :=
    { carrier := {z | z ∈ T₁ ∧ σ (u z / c) = u z / c}
      mul_mem' := by
        rintro z z' ⟨hz, hzc⟩ ⟨hz', hz'c⟩
        refine ⟨mul_mem hz hz', ?_⟩
        rw [hc.mul_u _ hz _ hz', add_div, map_add, hzc, hz'c]
      one_mem' := ⟨one_mem _, by rw [hc.u_one, zero_div, map_zero]⟩
      inv_mem' := by
        rintro z ⟨hz, hzc⟩
        refine ⟨inv_mem hz, ?_⟩
        rw [hc.u_inv hz, neg_div, map_neg, hzc] }
  have hBT : B ≤ T₁ := fun z hz => hz.1
  have hσc : σ c ≠ 0 := by rw [map_ne_zero]; exact hc0
  refine ⟨B, hBT, fun x hx z hz => ?_, ⟨hy, ?_⟩, fun z hz => ⟨hA₁ hz, ?_⟩, ?_⟩
  · rw [hc.comm_iff hx.1 hz.1]
    have hx' := hx.2
    have hz' := hz.2
    rw [map_div₀, div_eq_iff hσc] at hx' hz'
    rw [hx', hz']
    ring
  · rw [hcdef]
    split_ifs with h
    · rw [h, zero_div, map_zero]
    · rw [div_self h, map_one]
  · rw [(hA z (hA₁ hz)).mp hz, zero_div, map_zero]
  · obtain ⟨ψ, hψ⟩ := hc.exists_hom hBT
    rw [card_eq_mul_card_range hA hBT hψ, inf_eq_right.mpr (fun z hz => ⟨hA₁ hz,
      by rw [(hA z (hA₁ hz)).mp hz, zero_div, map_zero]⟩)]
    congr 1
    have hsurj : ∀ a : {x : E // σ x = x}, ∃ b : B, u b = c * a := by
      intro a
      obtain ⟨z, hz, hza⟩ := hc.u_surj (c * a)
      refine ⟨⟨z, hz, ?_⟩, hza⟩
      rw [hza, mul_div_cancel_left₀ _ hc0]
      exact a.2
    let f : ψ.range → {x : E // σ x = x} := fun z =>
      ⟨Multiplicative.toAdd (z : Multiplicative E) / c, by
        obtain ⟨b, hb⟩ := z.2
        rw [← hb, hψ]
        exact b.2.2⟩
    have hf : Function.Bijective f := by
      refine ⟨fun z z' hzz' => ?_, fun a => ?_⟩
      · have h1 : Multiplicative.toAdd (z : Multiplicative E) / c =
            Multiplicative.toAdd (z' : Multiplicative E) / c := congrArg Subtype.val hzz'
        rw [div_left_inj' hc0] at h1
        exact Subtype.ext (by simpa using congrArg Multiplicative.ofAdd h1)
      · obtain ⟨b, hb⟩ := hsurj a
        refine ⟨⟨ψ b, b, rfl⟩, Subtype.ext ?_⟩
        show Multiplicative.toAdd (ψ b) / c = a
        rw [hψ, toAdd_ofAdd, hb, mul_div_cancel_left₀ _ hc0]
    exact Nat.card_eq_of_bijective f hf

end U3RootCoords

theorem comm_sup_of_comm {G : Type*} [Group G] {B R : Subgroup G}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hBR : ∀ b ∈ B, ∀ r ∈ R, b * r = r * b) : ∀ x ∈ B ⊔ R, ∀ y ∈ B ⊔ R, x * y = y * x := by
  have hle : B ≤ normalizer (R : Set G) :=
    le_trans (fun b hb => mem_centralizer_iff.mpr fun r hr => (hBR b hb r hr).symm)
      (centralizer_le_normalizer _)
  intro x hx y hy
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right B R hle] at hx hy
  obtain ⟨b, hb, r, hr, rfl⟩ := hx
  obtain ⟨b', hb', r', hr', rfl⟩ := hy
  calc b * r * (b' * r') = b * (r * b') * r' := by group
    _ = b * (b' * r) * r' := by rw [hBR b' hb' r hr]
    _ = (b * b') * (r * r') := by group
    _ = (b' * b) * (r' * r) := by rw [hB b hb b' hb', hR r hr r' hr']
    _ = b' * (b * r') * r := by group
    _ = b' * (r' * b) * r := by rw [hBR b hb r' hr']
    _ = b' * r' * (b * r) := by group

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem le_centralizer_T₁ (hR : U3R2 G L T₁ R₂ t f) : R₂ ≤ centralizer (T₁ : Set G) :=
  fun r hr => mem_centralizer_iff.mpr fun y hy => hR.commT₁ y hy r hr

theorem le_normalizer_T₁ (hR : U3R2 G L T₁ R₂ t f) : R₂ ≤ normalizer (T₁ : Set G) :=
  hR.le_centralizer_T₁.trans (centralizer_le_normalizer _)

theorem T₁_le_normalizer (hR : U3R2 G L T₁ R₂ t f) : T₁ ≤ normalizer (R₂ : Set G) :=
  le_trans (fun y hy => mem_centralizer_iff.mpr fun r hr => (hR.commT₁ y hy r hr).symm)
    (centralizer_le_normalizer _)

theorem mem_sup_iff (hR : U3R2 G L T₁ R₂ t f) {x : G} :
    x ∈ T₁ ⊔ R₂ ↔ ∃ y ∈ T₁, ∃ r ∈ R₂, y * r = x := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left T₁ R₂ hR.le_normalizer_T₁]
  exact Set.mem_mul

theorem comm_of_mem_sup (hR : U3R2 G L T₁ R₂ t f) {r x : G} (hr : r ∈ R₂) (hx : x ∈ T₁ ⊔ R₂) :
    r * x = x * r := by
  obtain ⟨y, hy, r', hr', rfl⟩ := hR.mem_sup_iff.mp hx
  calc r * (y * r') = (r * y) * r' := by group
    _ = (y * r) * r' := by rw [hR.commT₁ y hy r hr]
    _ = y * (r * r') := by group
    _ = y * (r' * r) := by rw [hR.comm r hr r' hr']
    _ = y * r' * r := by group

theorem center_sup_eq (hR : U3R2 G L T₁ R₂ t f) :
    (T₁ ⊔ R₂) ⊓ centralizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) = R₂ := by
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hx
    have hyA : y ∈ szA₁ T₁ := by
      refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun z hz => ?_⟩
      have h1 := mem_centralizer_iff.mp hxc z (mem_sup_left hz)
      have h2 : z * r = r * z := hR.commT₁ z hz r hr
      calc z * y = z * (y * r) * r⁻¹ := by group
        _ = y * r * z * r⁻¹ := by rw [h1]
        _ = y * (r * z) * r⁻¹ := by group
        _ = y * (z * r) * r⁻¹ := by rw [h2]
        _ = y * z := by group
    exact mul_mem (hR.le hyA) hr
  · exact le_inf le_sup_right fun r hr =>
      mem_centralizer_iff.mpr fun x hx => (hR.comm_of_mem_sup hr hx).symm

theorem t_mem_normalizer (hR : U3R2 G L T₁ R₂ t f) : t ∈ normalizer (R₂ : Set G) := by
  refine mem_normalizer_iff.mpr fun r => ⟨fun hr => hR.tN r hr, fun hr => ?_⟩
  have h1 := hR.tN _ hr
  rwa [hR.t_inv, show t * (t * r * t) * t = (t * t) * r * (t * t) by group, ← sq, hR.t_sq,
    one_mul, mul_one] at h1

theorem t_mem_normalizer_sup (hR : U3R2 G L T₁ R₂ t f) :
    t ∈ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) := by
  have key : ∀ x ∈ T₁ ⊔ R₂, t * x * t⁻¹ ∈ T₁ ⊔ R₂ := by
    intro x hx
    obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hx
    have hyt := hR.t_comm y hy
    have e : t * (y * r) * t⁻¹ = y * (t * r * t⁻¹) := by
      calc t * (y * r) * t⁻¹ = (t * y) * r * t⁻¹ := by group
        _ = (y * t) * r * t⁻¹ := by rw [hyt]
        _ = y * (t * r * t⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left hy) (mem_sup_right (hR.tN r hr))
  refine mem_normalizer_iff.mpr fun x => ⟨key x, fun hx => ?_⟩
  have h1 := key _ hx
  rwa [hR.t_inv, show t * (t * x * t) * t = (t * t) * x * (t * t) by group, ← sq, hR.t_sq,
    one_mul, mul_one] at h1

theorem szR_le_normalizer_sup (hR : U3R2 G L T₁ R₂ t f) :
    szR T₁ R₂ t ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
  sup_le le_normalizer (zpowers_le.mpr hR.t_mem_normalizer_sup)

theorem card_szR_le (hR : U3R2 G L T₁ R₂ t f) :
    Nat.card (szR T₁ R₂ t) ≤ 2 * Nat.card (T₁ ⊔ R₂ : Subgroup G) := by
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (zpowers_le.mpr hR.t_mem_normalizer_sup)
  rw [sup_comm] at hprod
  have hzt : Nat.card (zpowers t) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hR.t_sq
  have h1 : 0 < Nat.card (zpowers t ⊓ (T₁ ⊔ R₂) : Subgroup G) := Nat.card_pos
  calc Nat.card (szR T₁ R₂ t) ≤
      Nat.card (szR T₁ R₂ t) * Nat.card (zpowers t ⊓ (T₁ ⊔ R₂) : Subgroup G) :=
        Nat.le_mul_of_pos_right _ h1
    _ = Nat.card (zpowers t) * Nat.card (T₁ ⊔ R₂ : Subgroup G) := hprod
    _ ≤ 2 * Nat.card (T₁ ⊔ R₂ : Subgroup G) := Nat.mul_le_mul_right _ hzt

theorem card_sup_mul (hR : U3R2 G L T₁ R₂ t f) :
    Nat.card (T₁ ⊔ R₂ : Subgroup G) * Nat.card (szA₁ T₁) = Nat.card T₁ * Nat.card R₂ := by
  have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hR.T₁_le_normalizer
  rwa [hR.inf] at h

theorem card_sup_le_of_comm (hR : U3R2 G L T₁ R₂ t f)
    (hab : ∀ B : Subgroup G, B ≤ T₁ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B ≤ (2 ^ f) ^ 2)
    (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f) {B : Subgroup G} (hB : B ≤ T₁ ⊔ R₂)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Nat.card (B ⊔ R₂ : Subgroup G) ≤ (2 ^ f) ^ 3 := by
  have hB'c : ∀ x ∈ B ⊔ R₂, ∀ y ∈ B ⊔ R₂, x * y = y * x :=
    comm_sup_of_comm hBc hR.comm fun b hb r hr => (hR.comm_of_mem_sup hr (hB hb)).symm
  set B'' := (B ⊔ R₂) ⊓ T₁ with hB''
  have hB''c : ∀ x ∈ B'', ∀ y ∈ B'', x * y = y * x := fun x hx y hy =>
    hB'c x (mem_inf.mp hx).1 y (mem_inf.mp hy).1
  have hB''card := hab B'' inf_le_right hB''c
  have hle : B ⊔ R₂ ≤ B'' ⊔ R₂ := by
    intro x hx
    have hx' : x ∈ T₁ ⊔ R₂ := (sup_le hB le_sup_right) hx
    obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hx'
    have hyB : y ∈ B ⊔ R₂ := by
      have := mul_mem hx (inv_mem (mem_sup_right hr : r ∈ B ⊔ R₂))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hyB, hy⟩)) (mem_sup_right hr)
  have hA : szA₁ T₁ ≤ B'' ⊓ R₂ := le_inf (le_inf (hR.le.trans le_sup_right) (szA₁_le T₁)) hR.le
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    ((inf_le_right : B'' ≤ T₁).trans hR.T₁_le_normalizer)
  have h1 : 2 ^ f ≤ Nat.card (B'' ⊓ R₂ : Subgroup G) := hA₁ ▸ card_le_of_le hA
  have h2 : Nat.card (B ⊔ R₂ : Subgroup G) ≤ Nat.card (B'' ⊔ R₂ : Subgroup G) := card_le_of_le hle
  rw [hR.card] at hprod
  have hq : 0 < 2 ^ f := by positivity
  have h3 : Nat.card (B'' ⊔ R₂ : Subgroup G) * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
    calc Nat.card (B'' ⊔ R₂ : Subgroup G) * 2 ^ f ≤
        Nat.card (B'' ⊔ R₂ : Subgroup G) * Nat.card (B'' ⊓ R₂ : Subgroup G) :=
          Nat.mul_le_mul_left _ h1
      _ = Nat.card B'' * (2 ^ f) ^ 2 := hprod
      _ ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ hB''card
      _ = (2 ^ f) ^ 3 * 2 ^ f := by ring
  exact h2.trans (Nat.le_of_mul_le_mul_right h3 hq)

theorem card_le_of_comm (hR : U3R2 G L T₁ R₂ t f)
    (hab : ∀ B : Subgroup G, B ≤ T₁ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B ≤ (2 ^ f) ^ 2)
    (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f) (hf : 2 ≤ f) {B : Subgroup G} (hB : B ≤ szR T₁ R₂ t)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) :
    Nat.card B ≤ (2 ^ f) ^ 3 ∧ ((2 ^ f) ^ 3 ≤ Nat.card B → B ≤ T₁ ⊔ R₂) := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  by_cases hBH : B ≤ T₁ ⊔ R₂
  · exact ⟨(card_le_of_le le_sup_left).trans (hR.card_sup_le_of_comm hab hA₁ hBH hBc),
      fun _ => hBH⟩
  have hsmall : Nat.card B < (2 ^ f) ^ 3 := by
    obtain ⟨b, hbB, hbH⟩ := Set.not_subset.mp hBH
    have hzN : zpowers t ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) :=
      zpowers_le.mpr hR.t_mem_normalizer_sup
    have hb' : b ∈ (((T₁ ⊔ R₂) ⊔ zpowers t : Subgroup G) : Set G) := hB hbB
    rw [coe_mul_of_right_le_normalizer_left (T₁ ⊔ R₂) (zpowers t) hzN] at hb'
    obtain ⟨h, hh, z, hz, hhz'⟩ := hb'
    have hhz : h * z = b := hhz'
    have hzt : z = t := by
      rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with rfl | rfl
      · exact absurd (by rw [← hhz, mul_one]; exact hh) hbH
      · rfl
    rw [hzt] at hhz
    set H := (T₁ ⊔ R₂ : Subgroup G) with hHdef
    set B₀ := B ⊓ H with hB₀
    have hB₀R : B₀ ⊓ R₂ ≤ szA₁ T₁ := by
      intro s hs
      obtain ⟨⟨hsB, -⟩, hsR⟩ := hs
      refine hR.rho_ker s hsR ?_
      have h1 : s * (h * t) = h * t * s := by rw [hhz]; exact hBc s hsB b hbB
      have h2 : s * h = h * s := hR.comm_of_mem_sup hsR hh
      have h3 : h * (s * t) = h * (t * s) := by
        calc h * (s * t) = (h * s) * t := by group
          _ = (s * h) * t := by rw [h2]
          _ = s * (h * t) := by group
          _ = h * t * s := h1
          _ = h * (t * s) := by group
      exact mul_left_cancel h3
    have hB₀c : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
      hBc x (mem_inf.mp hx).1 y (mem_inf.mp hy).1
    have hB₀card := hR.card_sup_le_of_comm hab hA₁ (inf_le_right : B₀ ≤ H) hB₀c
    have hHC : H ≤ normalizer (R₂ : Set G) :=
      le_trans (fun x hx => mem_centralizer_iff.mpr fun r hr => hR.comm_of_mem_sup hr hx)
        (centralizer_le_normalizer _)
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      ((inf_le_right : B₀ ≤ H).trans hHC)
    rw [hR.card] at hprod
    have h4 : Nat.card (B₀ ⊓ R₂ : Subgroup G) ≤ 2 ^ f := hA₁ ▸ card_le_of_le hB₀R
    have hq : 0 < 2 ^ f := by positivity
    have h5 : Nat.card B₀ ≤ (2 ^ f) ^ 2 := by
      have h6 : Nat.card B₀ * (2 ^ f) ^ 2 ≤ (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by
        rw [← hprod]
        calc Nat.card (B₀ ⊔ R₂ : Subgroup G) * Nat.card (B₀ ⊓ R₂ : Subgroup G) ≤
            (2 ^ f) ^ 3 * 2 ^ f := Nat.mul_le_mul hB₀card h4
          _ = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
      exact Nat.le_of_mul_le_mul_right h6 (by positivity)
    have hprod2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (hB.trans hR.szR_le_normalizer_sup)
    have h7 : Nat.card (B ⊔ H : Subgroup G) ≤ 2 * Nat.card H :=
      (card_le_of_le (sup_le hB (sup_le_szR T₁ R₂ t))).trans hR.card_szR_le
    have hHpos : 0 < Nat.card H := Nat.card_pos
    have h8 : Nat.card B ≤ 2 * Nat.card B₀ := by
      have h9 : Nat.card B * Nat.card H ≤ 2 * Nat.card B₀ * Nat.card H := by
        rw [← hprod2]
        calc Nat.card (B ⊔ H : Subgroup G) * Nat.card B₀ ≤ 2 * Nat.card H * Nat.card B₀ :=
            Nat.mul_le_mul_right _ h7
          _ = 2 * Nat.card B₀ * Nat.card H := by ring
      exact Nat.le_of_mul_le_mul_right h9 hHpos
    calc Nat.card B ≤ 2 * (2 ^ f) ^ 2 := h8.trans (Nat.mul_le_mul_left _ h5)
      _ < 2 ^ f * (2 ^ f) ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ = (2 ^ f) ^ 3 := by ring
  exact ⟨hsmall.le, fun h => absurd h (not_le.mpr hsmall)⟩

theorem exists_comm_of_mem_sup (hR : U3R2 G L T₁ R₂ t f)
    (hex : ∀ y ∈ T₁, ∃ B : Subgroup G, B ≤ T₁ ∧ (∀ x ∈ B, ∀ z ∈ B, x * z = z * x) ∧ y ∈ B ∧
      szA₁ T₁ ≤ B ∧ Nat.card B = (2 ^ f) ^ 2)
    (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f) {x : G} (hx : x ∈ T₁ ⊔ R₂) :
    ∃ B : Subgroup G, B ≤ T₁ ⊔ R₂ ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ x ∈ B ∧
      Nat.card B = (2 ^ f) ^ 3 := by
  obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hx
  obtain ⟨By, hByT, hByc, hyB, hAB, hBcard⟩ := hex y hy
  refine ⟨By ⊔ R₂, sup_le_sup_right hByT _,
    comm_sup_of_comm hByc hR.comm fun b hb r' hr' => hR.commT₁ b (hByT hb) r' hr',
    mul_mem (mem_sup_left hyB) (mem_sup_right hr), ?_⟩
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (hByT.trans hR.T₁_le_normalizer)
  have hinf : By ⊓ R₂ = szA₁ T₁ := by
    apply le_antisymm
    · rw [← hR.inf]
      exact inf_le_inf_right _ hByT
    · exact le_inf hAB hR.le
  rw [hinf, hA₁, hBcard, hR.card] at hprod
  have hq : 0 < 2 ^ f := by positivity
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [hprod]
  ring

theorem normalizer_le (hR : U3R2 G L T₁ R₂ t f)
    (hab : ∀ B : Subgroup G, B ≤ T₁ → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      Nat.card B ≤ (2 ^ f) ^ 2)
    (hex : ∀ y ∈ T₁, ∃ B : Subgroup G, B ≤ T₁ ∧ (∀ x ∈ B, ∀ z ∈ B, x * z = z * x) ∧ y ∈ B ∧
      szA₁ T₁ ≤ B ∧ Nat.card B = (2 ^ f) ^ 2)
    (hA₁ : Nat.card (szA₁ T₁) = 2 ^ f) (hf : 2 ≤ f) :
    normalizer (szR T₁ R₂ t : Set G) ≤ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) ⊓
      normalizer (R₂ : Set G) := by
  have key : ∀ n ∈ normalizer (szR T₁ R₂ t : Set G), ∀ x ∈ T₁ ⊔ R₂, n * x * n⁻¹ ∈ T₁ ⊔ R₂ := by
    intro n hn x hx
    obtain ⟨B, hBH, hBc, hxB, hBcard⟩ := hR.exists_comm_of_mem_sup hex hA₁ hx
    set B' := B.map (MulAut.conj n).toMonoidHom with hB'
    have hB'le : B' ≤ szR T₁ R₂ t := by
      rintro _ ⟨b, hb, rfl⟩
      exact (mem_normalizer_iff.mp hn b).mp ((sup_le_szR T₁ R₂ t) (hBH hb))
    have hB'c : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc n * a * n⁻¹ * (n * b * n⁻¹) = n * (a * b) * n⁻¹ := by group
        _ = n * (b * a) * n⁻¹ := by rw [hBc a ha b hb]
        _ = n * b * n⁻¹ * (n * a * n⁻¹) := by group
    have hB'card : Nat.card B' = (2 ^ f) ^ 3 := by
      rw [hB', card_map_of_injective (MulAut.conj n).injective, hBcard]
    have hB'H := (hR.card_le_of_comm hab hA₁ hf hB'le hB'c).2 hB'card.ge
    exact hB'H ⟨x, hxB, rfl⟩
  have hTR : ∀ n ∈ normalizer (szR T₁ R₂ t : Set G),
      n ∈ normalizer ((T₁ ⊔ R₂ : Subgroup G) : Set G) := by
    intro n hn
    refine mem_normalizer_iff.mpr fun x => ⟨key n hn x, fun hx => ?_⟩
    have h1 := key n⁻¹ (inv_mem hn) _ hx
    rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at h1
  have keyR : ∀ n ∈ normalizer (szR T₁ R₂ t : Set G), ∀ r ∈ R₂, n * r * n⁻¹ ∈ R₂ := by
    intro n hn r hr
    rw [← hR.center_sup_eq]
    refine ⟨(mem_normalizer_iff.mp (hTR n hn) r).mp (mem_sup_right hr),
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n ∈ T₁ ⊔ R₂ := by
      have := (mem_normalizer_iff.mp (hTR n⁻¹ (inv_mem hn)) y).mp hy
      rwa [inv_inv] at this
    have e := hR.comm_of_mem_sup hr hy'
    calc y * (n * r * n⁻¹) = n * ((n⁻¹ * y * n) * r) * n⁻¹ := by group
      _ = n * (r * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
      _ = n * r * n⁻¹ * y := by group
  intro n hn
  refine ⟨hTR n hn, mem_normalizer_iff.mpr fun r => ⟨keyR n hn r, fun hr => ?_⟩⟩
  have h1 := keyR n⁻¹ (inv_mem hn) _ hr
  rwa [show n⁻¹ * (n * r * n⁻¹) * n⁻¹⁻¹ = r by group] at h1

end U3R2

end CFSG.SeitzReduction.RankOne
