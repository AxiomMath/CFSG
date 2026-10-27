module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LieType.HighestRoot

variable {G : Type*} [Group G]

@[expose] def actLike (A L : Subgroup G) : Subgroup G where
  carrier := {a | a ∈ A ∧ ∃ l ∈ L, ∀ y ∈ A, a * y * a⁻¹ = l * y * l⁻¹}
  mul_mem' := by
    rintro a b ⟨ha, l, hl, hal⟩ ⟨hb, m, hm, hbm⟩
    refine ⟨mul_mem ha hb, l * m, mul_mem hl hm, fun y hy => ?_⟩
    have hmy : m * y * m⁻¹ ∈ A := by
      rw [← hbm y hy]
      exact mul_mem (mul_mem hb hy) (inv_mem hb)
    calc a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      _ = a * (m * y * m⁻¹) * a⁻¹ := by rw [hbm y hy]
      _ = l * (m * y * m⁻¹) * l⁻¹ := hal _ hmy
      _ = l * m * y * (l * m)⁻¹ := by group
  one_mem' := ⟨one_mem _, 1, one_mem _, fun y _ => by group⟩
  inv_mem' := by
    rintro a ⟨ha, l, hl, hal⟩
    refine ⟨inv_mem ha, l⁻¹, inv_mem hl, fun y hy => ?_⟩
    have hw : a⁻¹ * y * a ∈ A := by
      have := mul_mem (mul_mem (inv_mem ha) hy) ha
      exact this
    have h := hal _ hw
    have e : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
    rw [e] at h
    calc a⁻¹ * y * a⁻¹⁻¹ = a⁻¹ * y * a := by rw [inv_inv]
      _ = l⁻¹ * (l * (a⁻¹ * y * a) * l⁻¹) * l := by group
      _ = l⁻¹ * y * l⁻¹⁻¹ := by rw [← h, inv_inv]

theorem actLike_le (A L : Subgroup G) : actLike A L ≤ A := fun _ h => h.1

theorem le_centralizer_of_isQuasisimple {A L : Subgroup G} [Finite L]
    (hAq : CFSG.IsQuasisimple A)
    (hinner : ∀ l ∈ L, ∃ a ∈ A, ∀ y ∈ A, l * y * l⁻¹ = a * y * a⁻¹)
    (hproj : ∀ g ∈ A, ∃ v ∈ Subgroup.normalizer (L : Set G), ∀ y ∈ A,
      g * y * g⁻¹ = v * y * v⁻¹)
    {X : Subgroup G} (hXA : X ≤ A) (hXZ : ∀ x ∈ X, (∀ y ∈ A, x * y = y * x) → x = 1)
    (hXL : Nat.card L < Nat.card X) :
    L ≤ Subgroup.centralizer (A : Set G) := by
  set N := actLike A L with hN
  have hNn : (N.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnA, l, hl, hnl⟩ := hn
    obtain ⟨v, hv, hgv⟩ := hproj g g.2
    refine ⟨mul_mem (mul_mem g.2 hnA) (inv_mem g.2), v * l * v⁻¹,
      (Subgroup.mem_normalizer_iff.1 hv l).1 hl, fun y hy => ?_⟩
    have hgy : (g : G)⁻¹ * y * g ∈ A := mul_mem (mul_mem (inv_mem g.2) hy) g.2
    have hly : l * ((g : G)⁻¹ * y * g) * l⁻¹ ∈ A := by
      rw [← hnl _ hgy]
      exact mul_mem (mul_mem hnA hgy) (inv_mem hnA)
    have hginv : (g : G)⁻¹ * y * g = v⁻¹ * y * v := by
      have h := hgv _ hgy
      have e : (g : G) * ((g : G)⁻¹ * y * g) * (g : G)⁻¹ = y := by group
      rw [e] at h
      calc (g : G)⁻¹ * y * g = v⁻¹ * (v * ((g : G)⁻¹ * y * g) * v⁻¹) * v := by group
        _ = v⁻¹ * y * v := by rw [← h]
    have e : ((g : G) * n * (g : G)⁻¹) * y * ((g : G) * n * (g : G)⁻¹)⁻¹ =
        (g : G) * ((n : G) * ((g : G)⁻¹ * y * g) * (n : G)⁻¹) * (g : G)⁻¹ := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, hnl _ hgy, hgv _ hly, hginv]
    group
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hAq hNn with htop | hcen
  ·
    exfalso
    have hXN : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ A, x * y * x⁻¹ = l * y * l⁻¹ := by
      intro x hx
      have h : (⟨x, hXA hx⟩ : A) ∈ N.subgroupOf A := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 h).2
    choose f hfL hf using hXN
    have hinj : Function.Injective (fun x : X => (⟨f x.1 x.2, hfL x.1 x.2⟩ : L)) := by
      intro x x' h
      have hfx : f x.1 x.2 = f x'.1 x'.2 := congrArg Subtype.val h
      have hc : (x'.1)⁻¹ * x.1 = 1 := by
        refine hXZ _ (mul_mem (inv_mem x'.2) x.2) fun y hy => ?_
        have h1 := hf x.1 x.2 y hy
        have h2 := hf x'.1 x'.2 (x.1 * y * x.1⁻¹)
          (mul_mem (mul_mem (hXA x.2) hy) (inv_mem (hXA x.2)))
        have h3 : x'.1 * ((x'.1)⁻¹ * x.1 * y * (x.1)⁻¹ * x'.1) * (x'.1)⁻¹ =
            x'.1 * y * (x'.1)⁻¹ := by
          have h4 := hf x'.1 x'.2 y hy
          rw [← hfx] at h2
          calc x'.1 * ((x'.1)⁻¹ * x.1 * y * (x.1)⁻¹ * x'.1) * (x'.1)⁻¹ =
              x.1 * y * (x.1)⁻¹ := by group
            _ = f x.1 x.2 * y * (f x.1 x.2)⁻¹ := h1
            _ = x'.1 * y * (x'.1)⁻¹ := by rw [h4, hfx]
        have h5 : (x'.1)⁻¹ * x.1 * y * (x.1)⁻¹ * x'.1 = y := by
          have := congrArg (fun w => (x'.1)⁻¹ * w * x'.1) h3
          simpa [mul_assoc] using this
        calc (x'.1)⁻¹ * x.1 * y = ((x'.1)⁻¹ * x.1 * y * (x.1)⁻¹ * x'.1) * ((x'.1)⁻¹ * x.1) := by
              group
          _ = y * ((x'.1)⁻¹ * x.1) := by rw [h5]
      exact Subtype.ext (by
        have := congrArg (fun w => x'.1 * w) hc
        simpa using this)
    have := Nat.card_le_card_of_injective _ hinj
    omega
  ·
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, ha, hla⟩ := hinner l hl
    have haN : (⟨a, ha⟩ : A) ∈ N.subgroupOf A :=
      Subgroup.mem_subgroupOf.2 ⟨ha, l, hl, fun y hy => (hla y hy).symm⟩
    have hz := Subgroup.mem_center_iff.1 (hcen haN) ⟨y, hy⟩
    have hay : a * y = y * a := (congrArg Subtype.val hz).symm
    have h := hla y hy
    have e : a * y * a⁻¹ = y := by rw [hay]; group
    rw [e] at h
    calc y * l = (l * y * l⁻¹) * l := by rw [h]
      _ = l * y := by group
