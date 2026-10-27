module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2

open Subgroup

variable {G : Type*} [Group G]

theorem conj_eq_or_inv {σ u : G} {p : ℕ} (hp : p.Prime) (hσ : orderOf σ = p) (hu : u * u = 1)
    (h : u * σ * u⁻¹ ∈ zpowers σ) : u * σ * u⁻¹ = σ ∨ u * σ * u⁻¹ = σ⁻¹ := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hk2 : σ ^ (k * k) = σ ^ (1 : ℤ) := by
    have e1 : u * σ ^ k * u⁻¹ = (u * σ * u⁻¹) ^ k := by
      rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
    rw [zpow_one, zpow_mul, hk, ← e1, hk, huinv]
    calc u * (u * σ * u) * u = (u * u) * σ * (u * u) := by group
      _ = σ := by rw [hu, one_mul, mul_one]
  rw [zpow_eq_zpow_iff_modEq, hσ] at hk2
  have hdvd : (p : ℤ) ∣ (k - 1) * (k + 1) := by
    have := (Int.ModEq.dvd hk2.symm)
    have he : k * k - 1 = (k - 1) * (k + 1) := by ring
    rw [he] at this
    exact this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  rcases hpZ.dvd_or_dvd hdvd with h1 | h1
  · left
    rw [← hk]
    have : σ ^ k = σ ^ (1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hσ]
      exact (Int.modEq_iff_dvd.mpr h1).symm
    rw [this, zpow_one]
  · right
    rw [← hk]
    have : σ ^ k = σ ^ (-1 : ℤ) := by
      rw [zpow_eq_zpow_iff_modEq, hσ]
      exact (Int.modEq_iff_dvd.mpr (by rw [sub_neg_eq_add]; exact h1)).symm
    rw [this, zpow_neg_one]

theorem card_le_two_mul [Finite G] {E : Subgroup G} {x : G} (hx : x ≠ x⁻¹)
    (h : ∀ e ∈ E, e * x * e⁻¹ = x ∨ e * x * e⁻¹ = x⁻¹) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ centralizer ({x} : Set G)) := by
  classical
  have hnot : ∀ e ∈ E, e * x * e⁻¹ ≠ x → e * x * e⁻¹ = x⁻¹ := fun e he hne =>
    (h e he).resolve_left hne
  let φ : ↥E →* ℤˣ :=
    { toFun := fun e => if (e : G) * x * (e : G)⁻¹ = x then 1 else -1
      map_one' := by simp
      map_mul' := fun e f => by
        have hconj : ∀ g : G, g * x * g⁻¹ = x ↔ g * x = x * g := fun g => by
          constructor
          · intro hg
            calc g * x = (g * x * g⁻¹) * g := by group
              _ = x * g := by rw [hg]
          · intro hg
            rw [hg]
            group
        have hmul : ((e : G) * f) * x * ((e : G) * f)⁻¹ =
            (e : G) * ((f : G) * x * (f : G)⁻¹) * (e : G)⁻¹ := by group
        have hinv : ∀ g : G, g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := fun g => by group
        show (if ((e : G) * f) * x * ((e : G) * f)⁻¹ = x then (1 : ℤˣ) else -1) =
          (if (e : G) * x * (e : G)⁻¹ = x then (1 : ℤˣ) else -1) *
            (if (f : G) * x * (f : G)⁻¹ = x then (1 : ℤˣ) else -1)
        by_cases he : (e : G) * x * (e : G)⁻¹ = x <;> by_cases hf : (f : G) * x * (f : G)⁻¹ = x
        · have : ((e : G) * f) * x * ((e : G) * f)⁻¹ = x := by rw [hmul, hf, he]
          simp only [this, he, hf, ↓reduceIte, mul_one]
        · have hf' := hnot f f.2 hf
          have : ((e : G) * f) * x * ((e : G) * f)⁻¹ ≠ x := by
            rw [hmul, hf', hinv, he]
            exact hx.symm
          simp only [this, he, hf, ↓reduceIte, one_mul]
        · have he' := hnot e e.2 he
          have : ((e : G) * f) * x * ((e : G) * f)⁻¹ ≠ x := by
            rw [hmul, hf, he']
            exact hx.symm
          simp only [this, he, hf, ↓reduceIte, mul_one]
        · have he' := hnot e e.2 he
          have hf' := hnot f f.2 hf
          have : ((e : G) * f) * x * ((e : G) * f)⁻¹ = x := by
            rw [hmul, hf', hinv, he', inv_inv]
          simp only [this, he, hf, ↓reduceIte]
          decide }
  have hker : Nat.card φ.ker = Nat.card ↥(E ⊓ centralizer ({x} : Set G)) := by
    have hmap : φ.ker.map E.subtype = E ⊓ centralizer ({x} : Set G) := by
      ext g
      simp only [mem_map, MonoidHom.mem_ker, coe_subtype, mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨e, he, rfl⟩
        refine ⟨e.2, ?_⟩
        by_contra hc
        have hc' : (e : G) * x * (e : G)⁻¹ ≠ x := fun h1 => hc (by
          calc (e : G) * x = ((e : G) * x * (e : G)⁻¹) * e := by group
            _ = x * e := by rw [h1])
        have : φ e = -1 := by
          show (if (e : G) * x * (e : G)⁻¹ = x then (1 : ℤˣ) else -1) = -1
          simp only [hc', ↓reduceIte]
        rw [this] at he
        exact absurd he (by decide)
      · rintro ⟨hg, hgx⟩
        refine ⟨⟨g, hg⟩, ?_, rfl⟩
        show (if g * x * g⁻¹ = x then (1 : ℤˣ) else -1) = 1
        have : g * x * g⁻¹ = x := by rw [hgx]; group
        simp only [this, ↓reduceIte]
    rw [← hmap, card_map_of_injective E.subtype_injective]
  have hrange : Nat.card φ.range ≤ 2 := by
    calc Nat.card φ.range ≤ Nat.card ℤˣ := Subgroup.card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hker] at h1
  calc Nat.card E = Nat.card ↥(E ⊓ centralizer ({x} : Set G)) * Nat.card φ.range := h1.symm
    _ ≤ Nat.card ↥(E ⊓ centralizer ({x} : Set G)) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(E ⊓ centralizer ({x} : Set G)) := mul_comm _ _

theorem ne_inv_of_orderOf {x : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : orderOf x = p) :
    x ≠ x⁻¹ := by
  intro h
  have h2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel x
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hx] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)

theorem exists_large_centralizer [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X E : Subgroup G} (hXc : Nat.card X = p ∨ Nat.card X = p ^ 2)
    (hEe : ∀ e ∈ E, e * e = 1) (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e)
    (hEX : E ≤ normalizer (X : Set G)) :
    ∃ x ∈ X, orderOf x = p ∧ Nat.card E ≤ 2 * Nat.card ↥(E ⊓ centralizer ({x} : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hconjX : ∀ e ∈ E, ∀ y ∈ X, e * y * e⁻¹ ∈ X := fun e he y hy =>
    (mem_normalizer_iff.mp (hEX he) y).mp hy
  have hpX : p ∣ Nat.card X := by
    rcases hXc with h | h <;> rw [h]
    exact dvd_pow_self p (by norm_num)
  obtain ⟨⟨x₀, hx₀X⟩, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpX
  have hx₀p : orderOf x₀ = p := by rw [← hx₀]; exact Subgroup.orderOf_coe (⟨x₀, hx₀X⟩ : ↥X)
  rcases hXc with h1 | h2
  ·
    refine ⟨x₀, hx₀X, hx₀p, card_le_two_mul (ne_inv_of_orderOf hp hp2 hx₀p) fun e he => ?_⟩
    have hzX : zpowers x₀ = X := Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hx₀X)
      (by rw [h1, Nat.card_zpowers, hx₀p])
    exact conj_eq_or_inv hp hx₀p (hEe e he) (hzX ▸ hconjX e he x₀ hx₀X)
  have hXab : ∀ y ∈ X, ∀ z ∈ X, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val
      ((IsPGroup.isMulCommutative_of_card_eq_prime_sq h2).is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  by_cases hA : ∃ e ∈ E, Nat.card ↥(X ⊓ centralizer ({e} : Set G)) = p
  · obtain ⟨e, he, hcard⟩ := hA
    have hpos : 1 < Nat.card ↥(X ⊓ centralizer ({e} : Set G)) := by
      rw [hcard]; exact hp.one_lt
    obtain ⟨⟨x, hxC⟩, hx1⟩ := (Subgroup.one_lt_card_iff_ne_bot _).mp hpos |>
      fun h => (Subgroup.ne_bot_iff_exists_ne_one).mp h
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxo : orderOf x = p := by
      have h1 : orderOf x ∣ p := by
        rw [← hcard]
        exact Subgroup.orderOf_dvd_natCard _ hxC
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1'
      · exact h
    have hzC : zpowers x = X ⊓ centralizer ({e} : Set G) :=
      Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hxC) (by rw [hcard, Nat.card_zpowers, hxo])
    refine ⟨x, hxC.1, hxo, card_le_two_mul (ne_inv_of_orderOf hp hp2 hxo) fun f hf => ?_⟩
    refine conj_eq_or_inv hp hxo (hEe f hf) ?_
    rw [hzC]
    refine Subgroup.mem_inf.mpr ⟨hconjX f hf x hxC.1, mem_centralizer_singleton_iff.mpr ?_⟩
    have hxe : x * e = e * x := mem_centralizer_singleton_iff.mp hxC.2
    have hfe : e * f = f * e := hEc e he f hf
    have hfi : f⁻¹ * e = e * f⁻¹ := by
      calc f⁻¹ * e = f⁻¹ * (e * f) * f⁻¹ := by group
        _ = f⁻¹ * (f * e) * f⁻¹ := by rw [hfe]
        _ = e * f⁻¹ := by group
    calc f * x * f⁻¹ * e = f * x * (f⁻¹ * e) := by group
      _ = f * (x * e) * f⁻¹ := by rw [hfi]; group
      _ = f * (e * x) * f⁻¹ := by rw [hxe]
      _ = (f * e) * x * f⁻¹ := by group
      _ = (e * f) * x * f⁻¹ := by rw [hfe]
      _ = e * (f * x * f⁻¹) := by group
  · push Not at hA
    refine ⟨x₀, hx₀X, hx₀p, card_le_two_mul (ne_inv_of_orderOf hp hp2 hx₀p) fun e he => ?_⟩
    have hdvd : Nat.card ↥(X ⊓ centralizer ({e} : Set G)) ∣ p ^ 2 := by
      rw [← h2]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    interval_cases k
    ·
      right
      have hbot : X ⊓ centralizer ({e} : Set G) = ⊥ :=
        (Subgroup.card_eq_one).mp (by simpa using hk')
      set y := e * x₀ * e⁻¹ with hy
      have hyX : y ∈ X := hconjX e he x₀ hx₀X
      have hee : e * e = 1 := hEe e he
      have hey : e * y * e⁻¹ = x₀ := by
        rw [hy]
        calc e * (e * x₀ * e⁻¹) * e⁻¹ = (e * e) * x₀ * (e * e)⁻¹ := by group
          _ = x₀ := by rw [hee]; group
      have hz : x₀ * y ∈ X ⊓ centralizer ({e} : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨X.mul_mem hx₀X hyX, mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 : e * (x₀ * y) * e⁻¹ = x₀ * y := by
          calc e * (x₀ * y) * e⁻¹ = (e * x₀ * e⁻¹) * (e * y * e⁻¹) := by group
            _ = y * x₀ := by rw [← hy, hey]
            _ = x₀ * y := (hXab x₀ hx₀X y hyX).symm
        calc x₀ * y * e = (e * (x₀ * y) * e⁻¹) * e := by rw [h1]
          _ = e * (x₀ * y) := by group
      rw [hbot, mem_bot] at hz
      exact eq_inv_of_mul_eq_one_right hz
    · exact absurd (by simpa using hk') (hA e he)
    ·
      left
      have hle : X ⊓ centralizer ({e} : Set G) = X :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hk'])
      have hx : x₀ ∈ X ⊓ centralizer ({e} : Set G) := by
        rw [hle]
        exact hx₀X
      have hxe : x₀ * e = e * x₀ := mem_centralizer_singleton_iff.mp hx.2
      calc e * x₀ * e⁻¹ = x₀ * e * e⁻¹ := by rw [hxe]
        _ = x₀ := by group

@[expose] def KleinWit (x u₁ u₂ : G) : Prop :=
  u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧ x * u₁ * x⁻¹ = u₂ ∧
    x * u₂ * x⁻¹ = u₁ * u₂ ∧ u₂ ≠ u₁

theorem kleinWit_map_iff {H : Type*} [Group H] {f : G →* H} (hf : Function.Injective f)
    {x u₁ u₂ : G} : KleinWit (f x) (f u₁) (f u₂) ↔ KleinWit x u₁ u₂ := by
  have e1 : ∀ a b : G, f a * f b = f (a * b) := fun a b => (map_mul f a b).symm
  have e2 : ∀ a b : G, f a * f b * (f a)⁻¹ = f (a * b * a⁻¹) := fun a b => by
    rw [map_mul, map_mul, map_inv]
  unfold KleinWit
  rw [e2, e2, e1, e1, e1, e1, ← map_one f]
  simp only [hf.eq_iff, hf.ne_iff]

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinJ2
