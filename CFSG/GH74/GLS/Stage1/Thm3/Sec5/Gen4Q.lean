module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Gen4A
public import CFSG.GH74.Generic.QuaternionCentral
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5.Rank5

open Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.GH74.Generic
open scoped commutatorElement

theorem exists_frattini_hom {G : Type} [Group G] {Y : Subgroup G} {n : ℕ}
    (hY : CFSG.GH74.GLS.IVK.IsQuaternionTwoGroup ↥Y n) :
    ∃ β : ↥Y →* V4, Function.Surjective β ∧ (∀ g : ↥Y, β g = 1 → ∃ h : ↥Y, h * h = g) ∧
      (∀ g : ↥Y, (∀ h : ↥Y, g * h = h * g) → β g = 1) := by
  obtain ⟨hn, ⟨e⟩⟩ := hY
  have hj : 1 ≤ n - 2 := by omega
  refine ⟨(qgenFrattini (n - 2) hj).comp e.toMonoidHom, ?_, ?_, ?_⟩
  · exact (qgenFrattini_surjective hj).comp e.surjective
  · intro g hg
    obtain ⟨i, hi, hpar⟩ := (qgenFrattini_eq_one_iff hj (e g)).1 hg
    have hk : ∃ k : ZMod (2 * 2 ^ (n - 2)), k + k = i := by
      have h1 : qgenParity (n - 2) ((i.val : ℕ) : ZMod (2 * 2 ^ (n - 2))) = 0 := by
        rwa [ZMod.natCast_zmod_val]
      rw [qgenParity, map_natCast, ZMod.natCast_eq_zero_iff] at h1
      obtain ⟨m, hm⟩ := h1
      refine ⟨(m : ZMod (2 * 2 ^ (n - 2))), ?_⟩
      rw [← Nat.cast_add, ← ZMod.natCast_zmod_val i, hm]
      congr 1
      ring
    obtain ⟨k, hk⟩ := hk
    refine ⟨e.symm (QuaternionGroup.a k), e.injective ?_⟩
    rw [map_mul, MulEquiv.apply_symm_apply, hi, QuaternionGroup.a_mul_a, hk]
  · intro g hg
    have hmem : e g ∈ Subgroup.center (Qgen (n - 2)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have := hg (e.symm w)
      have h2 := congrArg e this
      simpa using h2.symm
    rcases (Qgen.center_iff hj _).1 hmem with h | h
    · simp [h]
    · simp only [MonoidHom.comp_apply]
      show qgenFrattini (n - 2) hj (e g) = 1
      rw [h]
      exact qgenFrattini_z hj

theorem mem_sup_of_commute' {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : G} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  have hnorm : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have : a * b * a⁻¹ = b := by rw [hc a ha b hb]; group
      rwa [this]
    · intro hb
      have h1 := hc a ha _ hb
      have : a * b * a⁻¹ = b := by
        calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹)) := by group
          _ = a⁻¹ * ((a * b * a⁻¹) * a) := by rw [h1]
          _ = b := by group
      rwa [this] at hb
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hnorm
  have hy' : y ∈ (↑(A ⊔ B) : Set G) := hy
  rw [hset] at hy'
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hy'
  exact ⟨a, ha, b, hb, rfl⟩

theorem mem_normalizer_of_comm {G : Type} [Group G] {Y : Subgroup G} {g : G}
    (h : ∀ y ∈ Y, g * y = y * g) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ = y := by rw [h y hy]; group
    rwa [this]
  · intro hy
    have h1 := h _ hy
    have : g * y * g⁻¹ = y := by
      calc g * y * g⁻¹ = g⁻¹ * (g * (g * y * g⁻¹)) := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * g) := by rw [h1]
        _ = y := by group
    rwa [this] at hy

theorem exists_combined_hom {G : Type} [Group G] {Y₁ Y₂ : Subgroup G}
    (hc : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y = y * x)
    {β₁ : ↥Y₁ →* V4} {β₂ : ↥Y₂ →* V4}
    (hz₁ : ∀ g : ↥Y₁, (∀ h : ↥Y₁, g * h = h * g) → β₁ g = 1)
    (hz₂ : ∀ g : ↥Y₂, (∀ h : ↥Y₂, g * h = h * g) → β₂ g = 1) :
    ∃ β : ↥(Y₁ ⊔ Y₂) →* V4 × V4, ∀ (x : G) (hx : x ∈ Y₁) (y : G) (hy : y ∈ Y₂),
      β ⟨x * y, mul_mem (mem_sup_left hx) (mem_sup_right hy)⟩ = (β₁ ⟨x, hx⟩, β₂ ⟨y, hy⟩) := by
  let i₁ : ↥Y₁ →* ↥(Y₁ ⊔ Y₂) := Subgroup.inclusion le_sup_left
  let i₂ : ↥Y₂ →* ↥(Y₁ ⊔ Y₂) := Subgroup.inclusion le_sup_right
  have hcomm : ∀ (m : ↥Y₁) (n : ↥Y₂), Commute (i₁ m) (i₂ n) := fun m n =>
    Subtype.ext (hc m m.2 n n.2)
  let μ : ↥Y₁ × ↥Y₂ →* ↥(Y₁ ⊔ Y₂) := MonoidHom.noncommCoprod i₁ i₂ hcomm
  have hμ : ∀ m n, μ (m, n) = ⟨(m : G) * (n : G), mul_mem (mem_sup_left m.2) (mem_sup_right n.2)⟩ :=
    fun m n => rfl
  have hsurj : Function.Surjective μ := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute' hc hg
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  let β₀ : ↥Y₁ × ↥Y₂ →* V4 × V4 := β₁.prodMap β₂
  have hker : μ.ker ≤ β₀.ker := by
    rintro ⟨m, n⟩ hmn
    have h1 : (m : G) * (n : G) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hmn)
      simpa [hμ] using this
    have hmn' : (m : G) = (n : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hnm' : (n : G) = (m : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hm₂ : (m : G) ∈ Y₂ := by rw [hmn']; exact inv_mem n.2
    have hn₁ : (n : G) ∈ Y₁ := by rw [hnm']; exact inv_mem m.2
    have hm1 : β₁ m = 1 := by
      refine hz₁ m (fun h => Subtype.ext ?_)
      exact (hc h h.2 m hm₂).symm
    have hn1 : β₂ n = 1 := by
      refine hz₂ n (fun h => Subtype.ext ?_)
      exact hc n hn₁ h h.2
    show β₀ (m, n) = 1
    simp [β₀, hm1, hn1]
  refine ⟨(MonoidHom.liftOfSurjective μ hsurj) ⟨β₀, hker⟩, fun x hx y hy => ?_⟩
  have : (⟨x * y, mul_mem (mem_sup_left hx) (mem_sup_right hy)⟩ : ↥(Y₁ ⊔ Y₂)) =
      μ (⟨x, hx⟩, ⟨y, hy⟩) := rfl
  rw [this]
  simp [β₀]

theorem v4_sq : ∀ w : V4, w * w = 1 := by decide

theorem v4_conj : ∀ x y : V4, x * y * x⁻¹ = y := by decide

theorem v4v4_sq : ∀ w : V4 × V4, w * w = 1 := by decide

@[expose] def v4Basis : Fin 4 → V4 × V4 :=
  ![(Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2)), 1),
    (Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2)), 1),
    (1, Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2))),
    (1, Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2)))]

theorem v4Basis_indep : ∀ c : Fin 4 → Fin 2, c ≠ 0 →
    (List.ofFn fun i => v4Basis i ^ (c i : ℕ)).prod ≠ 1 := by
  unfold v4Basis
  decide

theorem hact_of_sq {G : Type} [Group G] {Y : Subgroup G} {β : ↥Y →* V4}
    (hβ : Function.Surjective β) (hsqk : ∀ g : ↥Y, β g = 1 → ∃ h : ↥Y, h * h = g)
    {d p : G} (hd : d ∈ Subgroup.normalizer (Y : Set G)) (hp : p ∈ Subgroup.normalizer (Y : Set G))
    {k : ℕ} (hdk : d ^ (2 ^ k) = 1)
    (hpact : ∀ g : ↥Y, β ((Y.normalizerMonoidHom ⟨p, hp⟩) g) = β g) (g : ↥Y) :
    β ((Y.normalizerMonoidHom ⟨d * d * p, mul_mem (mul_mem hd hd) hp⟩) g) = β g := by
  have hker : ∀ (γ : ↥(Subgroup.normalizer (Y : Set G))) (g : ↥Y), β g = 1 →
      β (Y.normalizerMonoidHom γ g) = 1 := by
    intro γ g hg
    obtain ⟨h, rfl⟩ := hsqk g hg
    rw [map_mul, map_mul]
    exact v4_sq _
  have hγ : (⟨d, hd⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ (2 ^ k) = 1 :=
    Subtype.ext (by simpa using hdk)
  have h2 := sq_acts_trivially (P := ↥Y) (V := V4) card_V4 Y.normalizerMonoidHom β hβ hker hγ
    ((Y.normalizerMonoidHom ⟨p, hp⟩) g)
  have hmul : (⟨d * d * p, mul_mem (mul_mem hd hd) hp⟩ : ↥(Subgroup.normalizer (Y : Set G))) =
      (⟨d, hd⟩ ^ 2) * ⟨p, hp⟩ := Subtype.ext (by simp [pow_two])
  rw [hmul, map_mul, MulAut.mul_apply, h2, hpact]

theorem hpact_of_comm {G : Type} [Group G] {Y Z : Subgroup G} {β : ↥Y →* V4}
    (hc : ∀ y ∈ Y, ∀ z ∈ Z, y * z = z * y) {u v p : G} (hu : u ∈ Y) (hv : v ∈ Z) (hp : p = u * v)
    (hpn : p ∈ Subgroup.normalizer (Y : Set G)) (g : ↥Y) :
    β ((Y.normalizerMonoidHom ⟨p, hpn⟩) g) = β g := by
  have h1 : (((Y.normalizerMonoidHom ⟨p, hpn⟩) g : ↥Y) : G) = u * g * u⁻¹ := by
    show p * (g : G) * p⁻¹ = _
    rw [hp]
    have hcg : (g : G) * v = v * g := hc g g.2 v hv
    calc u * v * g * (u * v)⁻¹ = u * (v * g) * v⁻¹ * u⁻¹ := by group
      _ = u * (g * v) * v⁻¹ * u⁻¹ := by rw [hcg]
      _ = u * g * u⁻¹ := by group
  have h2 : (Y.normalizerMonoidHom ⟨p, hpn⟩) g = (⟨u, hu⟩ : ↥Y) * g * (⟨u, hu⟩ : ↥Y)⁻¹ :=
    Subtype.ext h1
  rw [h2, map_mul, map_mul, map_inv]
  exact v4_conj _ _

theorem false_of_quat_pair {G : Type} [Group G] [Finite G] (hgen4 : CFSG.GH74.Gen4 G)
    {Y₁ Y₂ : Subgroup G} {n₁ n₂ : ℕ} (hq₁ : CFSG.GH74.GLS.IVK.IsQuaternionTwoGroup ↥Y₁ n₁)
    (hq₂ : CFSG.GH74.GLS.IVK.IsQuaternionTwoGroup ↥Y₂ n₂)
    (hc : ∀ x ∈ Y₁, ∀ y ∈ Y₂, x * y = y * x) {d p : G} {k : ℕ}
    (hd₁ : d ∈ Subgroup.normalizer (Y₁ : Set G)) (hd₂ : d ∈ Subgroup.normalizer (Y₂ : Set G))
    (hdk : d ^ (2 ^ k) = 1) (hp : p ∈ Y₁ ⊔ Y₂)
    (ha2 : (d * d * p) * (d * d * p) = 1) (haP : d * d * p ∉ Y₁ ⊔ Y₂) : False := by
  obtain ⟨β₁, hβ₁s, hβ₁k, hβ₁z⟩ := exists_frattini_hom hq₁
  obtain ⟨β₂, hβ₂s, hβ₂k, hβ₂z⟩ := exists_frattini_hom hq₂
  obtain ⟨β, hβ⟩ := exists_combined_hom hc hβ₁z hβ₂z
  obtain ⟨p₁, hp₁, p₂, hp₂, hpp⟩ := mem_sup_of_commute' hc hp
  have hpn₁ : p ∈ Subgroup.normalizer (Y₁ : Set G) := by
    rw [hpp]
    exact mul_mem (Subgroup.le_normalizer hp₁)
      (mem_normalizer_of_comm fun y hy => (hc y hy p₂ hp₂).symm)
  have hpn₂ : p ∈ Subgroup.normalizer (Y₂ : Set G) := by
    rw [hpp]
    exact mul_mem (mem_normalizer_of_comm fun y hy => hc p₁ hp₁ y hy)
      (Subgroup.le_normalizer hp₂)
  have ha₁ : d * d * p ∈ Subgroup.normalizer (Y₁ : Set G) := mul_mem (mul_mem hd₁ hd₁) hpn₁
  have ha₂ : d * d * p ∈ Subgroup.normalizer (Y₂ : Set G) := mul_mem (mul_mem hd₂ hd₂) hpn₂
  have haN : d * d * p ∈ Subgroup.normalizer ((Y₁ ⊔ Y₂ : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup Y₁ Y₂ ⟨ha₁, ha₂⟩
  have hact₁ : ∀ g : ↥Y₁, β₁ ((Y₁.normalizerMonoidHom ⟨d * d * p, ha₁⟩) g) = β₁ g := fun g =>
    hact_of_sq hβ₁s hβ₁k hd₁ hpn₁ hdk (fun g => hpact_of_comm hc hp₁ hp₂ hpp hpn₁ g) g
  have hc' : ∀ y ∈ Y₂, ∀ x ∈ Y₁, y * x = x * y := fun y hy x hx => (hc x hx y hy).symm
  have hpp' : p = p₂ * p₁ := by rw [hpp, (hc p₁ hp₁ p₂ hp₂)]
  have hact₂ : ∀ g : ↥Y₂, β₂ ((Y₂.normalizerMonoidHom ⟨d * d * p, ha₂⟩) g) = β₂ g := fun g =>
    hact_of_sq hβ₂s hβ₂k hd₂ hpn₂ hdk (fun g => hpact_of_comm hc' hp₂ hp₁ hpp' hpn₂ g) g
  have hactP : ∀ g : ↥(Y₁ ⊔ Y₂),
      β ((Subgroup.normalizerMonoidHom (Y₁ ⊔ Y₂) ⟨d * d * p, haN⟩) g) = β g := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute' hc hg
    have hax : d * d * p * x * (d * d * p)⁻¹ ∈ Y₁ := (Subgroup.mem_normalizer_iff.1 ha₁ x).1 hx
    have hay : d * d * p * y * (d * d * p)⁻¹ ∈ Y₂ := (Subgroup.mem_normalizer_iff.1 ha₂ y).1 hy
    have e1 : ((Subgroup.normalizerMonoidHom (Y₁ ⊔ Y₂) ⟨d * d * p, haN⟩) ⟨x * y, hg⟩ :
        ↥(Y₁ ⊔ Y₂)) = ⟨(d * d * p * x * (d * d * p)⁻¹) * (d * d * p * y * (d * d * p)⁻¹),
          mul_mem (mem_sup_left hax) (mem_sup_right hay)⟩ :=
      Subtype.ext (by show d * d * p * (x * y) * (d * d * p)⁻¹ = _; group)
    rw [e1, hβ _ hax _ hay]
    have h1 : β₁ ⟨d * d * p * x * (d * d * p)⁻¹, hax⟩ = β₁ ⟨x, hx⟩ := hact₁ ⟨x, hx⟩
    have h2 : β₂ ⟨d * d * p * y * (d * d * p)⁻¹, hay⟩ = β₂ ⟨y, hy⟩ := hact₂ ⟨y, hy⟩
    have h3 : β ⟨x * y, mul_mem (mem_sup_left hx) (mem_sup_right hy)⟩ = (β₁ ⟨x, hx⟩, β₂ ⟨y, hy⟩) :=
      hβ x hx y hy
    rw [h1, h2]
    exact h3.symm
  have hβs : Function.Surjective β := by
    rintro ⟨u, v⟩
    obtain ⟨x, hx⟩ := hβ₁s u
    obtain ⟨y, hy⟩ := hβ₂s v
    refine ⟨⟨(x : G) * (y : G), mul_mem (mem_sup_left x.2) (mem_sup_right y.2)⟩, ?_⟩
    rw [hβ _ x.2 _ y.2]
    simp [hx, hy]
  have he : ∀ i, β (Classical.choose (hβs (v4Basis i))) = v4Basis i := fun i =>
    Classical.choose_spec (hβs (v4Basis i))
  have hind : ∀ c : Fin 4 → Fin 2, c ≠ 0 →
      (List.ofFn fun i => β (Classical.choose (hβs (v4Basis i))) ^ (c i : ℕ)).prod ≠ 1 := by
    intro c hc0
    have := v4Basis_indep c hc0
    simpa only [he] using this
  have hcert := rankCertified_four_of_frattini_section (Y₁ ⊔ Y₂) (d * d * p) haN ha2 haP v4v4_sq β
    (fun i => Classical.choose (hβs (v4Basis i))) hind hactP
  exact hcert.not_gen4 le_rfl hgen4

end CFSG.GH74.GLS.Stage1.Thm3.Sec5.Rank5
