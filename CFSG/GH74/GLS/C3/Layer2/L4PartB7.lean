module

public import CFSG.GH74.GLS.C3.Layer2.L4PartB6
public import CFSG.GH74.GLS.C3.Layer2.L4TI
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.GH74.GLS.C3.Layer2.L4.PartB7

open Equiv Perm Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.L4 CFSG.GH74.GLS.C3.Layer2.L4.Wreath
open scoped Pointwise

section Aux

variable {C : Type*} [Group C]

theorem orderOf_eq_three {w : C} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) : orderOf w = 3 :=
  orderOf_eq_prime hw3 hw1

theorem zpow_eq_one_of_two_mul {w : C} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) {k : ℤ}
    (h1 : w ^ (2 * k) = 1) : w ^ k = 1 := by
  have h2 : orderOf w ∣ (2 * k).natAbs := by
    rw [← orderOf_dvd_iff_zpow_eq_one] at h1
    exact Int.natCast_dvd.1 h1
  rw [orderOf_eq_three hw3 hw1] at h2
  have h3 : (3 : ℕ) ∣ k.natAbs := by
    rw [Int.natAbs_mul] at h2
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h2)
  have h4 : (3 : ℤ) ∣ k := Int.natCast_dvd.2 h3 |> fun h => by simpa using h
  obtain ⟨m, hm⟩ := h4
  rw [hm, zpow_mul]
  simpa using (by rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hw3, one_zpow] :
    (w ^ (3 : ℤ)) ^ m = 1)

theorem eq_one_of_mem_zpowers {w t : C} (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (ht2 : t * t = 1)
    (ht : t ∈ zpowers w) : t = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
  exact zpow_eq_one_of_two_mul hw3 hw1 (by rw [two_mul, zpow_add]; exact ht2)

theorem conj_mem_zpowers (E A : Subgroup C) (hEn : E.Normal) (w : C) (hw3 : w ^ 3 = 1)
    (hAsq : ∀ a ∈ A, a * a = 1) (hwE : ∀ e ∈ E, w * e = e * w)
    (hC0 : ∀ g : C, (∀ e ∈ E, g * e = e * g) → ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * t)
    (hinv : ∀ t ∈ A, t ∉ E → t * w * t⁻¹ = w⁻¹) (c : C) : c * w * c⁻¹ ∈ zpowers w := by
  have hcomm : ∀ e ∈ E, (c * w * c⁻¹) * e = e * (c * w * c⁻¹) := by
    intro e he
    have he' : c⁻¹ * e * c ∈ E := by
      have := hEn.conj_mem e he c⁻¹
      simpa using this
    have h1 := hwE _ he'
    calc c * w * c⁻¹ * e = c * (w * (c⁻¹ * e * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * e * c) * w) * c⁻¹ := by rw [h1]
      _ = e * (c * w * c⁻¹) := by group
  obtain ⟨k, t, ht, hwt⟩ := hC0 _ hcomm
  have hw'3 : (c * w * c⁻¹) ^ 3 = 1 := by rw [conj_pow, hw3]; group
  have ht2 := hAsq t ht
  by_cases htE : t ∈ E
  · have hcom : Commute (w ^ k) t := by
      have h1 : Commute w t := (hwE t htE)
      exact h1.pow_left k
    have h3 : (c * w * c⁻¹) ^ 3 = t := by
      rw [hwt, hcom.mul_pow, ← pow_mul, mul_comm k 3, pow_mul, hw3, one_pow, one_mul, pow_three,
        ht2, mul_one]
    rw [h3] at hw'3
    rw [hwt, hw'3, mul_one]
    exact pow_mem (mem_zpowers w) k
  · have hti := hinv t ht htE
    have h1 : t * w ^ k * t⁻¹ = (w⁻¹) ^ k := by
      rw [← conj_pow, hti]
    have h2 : (c * w * c⁻¹) ^ 2 = 1 := by
      rw [hwt, sq]
      calc w ^ k * t * (w ^ k * t) = w ^ k * (t * w ^ k * t⁻¹) * (t * t) := by group
        _ = 1 := by rw [h1, ht2, inv_pow]; group
    have h4 : c * w * c⁻¹ = 1 := by
      calc c * w * c⁻¹ = (c * w * c⁻¹) ^ 3 * ((c * w * c⁻¹) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hw'3, h2]; group
    rw [h4]
    exact one_mem _

theorem eq_one_of_mem_normalizer (A E : Subgroup C) (w : C) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hAsq : ∀ a ∈ A, a * a = 1) (a₀ : C) (ha₀ : a₀ ∈ A) (ha₀E : a₀ ∉ E)
    (hinv : ∀ t ∈ A, t ∉ E → t * w * t⁻¹ = w⁻¹) {z : C} (hz : z ∈ zpowers w)
    (hzN : z ∈ normalizer (A : Set C)) : z = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have h1 : a₀ * w ^ k * a₀⁻¹ = (w⁻¹) ^ k := by
    rw [← conj_zpow, hinv a₀ ha₀ ha₀E]
  have h2 : w ^ k * a₀ * (w ^ k)⁻¹ = w ^ (2 * k) * a₀ := by
    have h3 : a₀ * (w ^ k)⁻¹ * a₀⁻¹ = w ^ k := by
      have : a₀ * w ^ k * a₀⁻¹ = (w ^ k)⁻¹ := by rw [h1, inv_zpow]
      calc a₀ * (w ^ k)⁻¹ * a₀⁻¹ = (a₀ * w ^ k * a₀⁻¹)⁻¹ := by group
        _ = w ^ k := by rw [this, inv_inv]
    calc w ^ k * a₀ * (w ^ k)⁻¹ = w ^ k * (a₀ * (w ^ k)⁻¹ * a₀⁻¹) * a₀ := by group
      _ = w ^ k * w ^ k * a₀ := by rw [h3]
      _ = w ^ (2 * k) * a₀ := by rw [two_mul, zpow_add]
  have h4 : w ^ k * a₀ * (w ^ k)⁻¹ ∈ A := ((mem_normalizer_iff.1 hzN) a₀).1 ha₀
  rw [h2] at h4
  have h5 : w ^ (2 * k) ∈ A := by
    have := A.mul_mem h4 (A.inv_mem ha₀)
    simpa using this
  have h6 : w ^ (2 * k) = 1 :=
    eq_one_of_mem_zpowers hw3 hw1 (hAsq _ h5) (mem_zpowers_iff.2 ⟨2 * k, rfl⟩)
  exact zpow_eq_one_of_two_mul hw3 hw1 h6

theorem exists_psi (w : C) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hW : ∀ c : C, c * w * c⁻¹ ∈ zpowers w) :
    ∃ ψ : C →* ℤˣ, ∀ c, c * w * c⁻¹ = (if ψ c = 1 then w else w⁻¹) := by
  classical
  have hw2 : w ≠ w⁻¹ := by
    intro h
    apply hw1
    have : w * w = 1 := by rw [mul_eq_one_iff_eq_inv]; exact h
    have h3 : w = w ^ 3 * (w * w)⁻¹ := by group
    rw [h3, hw3, this]; group
  have hc : ∀ c : C, c * w * c⁻¹ = w ∨ c * w * c⁻¹ = w⁻¹ := by
    intro c
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hW c)
    have hne : c * w * c⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      have : w = c⁻¹ * (c * w * c⁻¹) * c := by group
      rw [this, h1]; group
    have hk3 : w ^ k = w ^ (k % 3) := by
      have := zpow_mod_orderOf w k
      rw [orderOf_eq_three hw3 hw1] at this
      simpa using this.symm
    have : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases this with h0 | h1 | h2
    · exfalso; apply hne; rw [← hk, hk3, h0]; simp
    · left; rw [← hk, hk3, h1]; simp
    · right
      rw [← hk, hk3, h2]
      have : (w ^ (2 : ℤ)) = w⁻¹ := by
        have : w ^ 3 = 1 := hw3
        calc w ^ (2 : ℤ) = w ^ 3 * (w)⁻¹ := by group
          _ = w⁻¹ := by rw [this]; group
      exact this
  let f : C → ℤˣ := fun c => if c * w * c⁻¹ = w then 1 else -1
  have hf : ∀ c, (c * w * c⁻¹ = w ∧ f c = 1) ∨ (c * w * c⁻¹ = w⁻¹ ∧ f c = -1) := by
    intro c
    rcases hc c with h1 | h1
    · left; exact ⟨h1, by simp [f, h1]⟩
    · right
      have : ¬ (c * w * c⁻¹ = w) := by rw [h1]; exact fun h => hw2 h.symm
      exact ⟨h1, by simp [f, this]⟩
  have hfw : ∀ c, c * w * c⁻¹ = w → f c = 1 := by
    intro c h1
    rcases hf c with ⟨-, h2⟩ | ⟨h2, -⟩
    · exact h2
    · rw [h1] at h2; exact absurd h2 hw2
  have hfw' : ∀ c, c * w * c⁻¹ = w⁻¹ → f c = -1 := by
    intro c h1
    rcases hf c with ⟨h2, -⟩ | ⟨-, h2⟩
    · rw [h1] at h2; exact absurd h2.symm hw2
    · exact h2
  refine ⟨MonoidHom.mk' f ?_, ?_⟩
  · intro c d
    rcases hc c with h1 | h1 <;> rcases hc d with h2 | h2
    · have : c * d * w * (c * d)⁻¹ = w := by
        calc c * d * w * (c * d)⁻¹ = c * (d * w * d⁻¹) * c⁻¹ := by group
          _ = w := by rw [h2, h1]
      rw [hfw _ this, hfw _ h1, hfw _ h2]; rfl
    · have : c * d * w * (c * d)⁻¹ = w⁻¹ := by
        calc c * d * w * (c * d)⁻¹ = c * (d * w * d⁻¹) * c⁻¹ := by group
          _ = (c * w * c⁻¹)⁻¹ := by rw [h2]; group
          _ = w⁻¹ := by rw [h1]
      rw [hfw' _ this, hfw _ h1, hfw' _ h2]; rfl
    · have : c * d * w * (c * d)⁻¹ = w⁻¹ := by
        calc c * d * w * (c * d)⁻¹ = c * (d * w * d⁻¹) * c⁻¹ := by group
          _ = w⁻¹ := by rw [h2, h1]
      rw [hfw' _ this, hfw' _ h1, hfw _ h2]; rfl
    · have : c * d * w * (c * d)⁻¹ = w := by
        calc c * d * w * (c * d)⁻¹ = c * (d * w * d⁻¹) * c⁻¹ := by group
          _ = (c * w * c⁻¹)⁻¹ := by rw [h2]; group
          _ = w := by rw [h1, inv_inv]
      rw [hfw _ this, hfw' _ h1, hfw' _ h2]; decide
  · intro c
    rcases hf c with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · show c * w * c⁻¹ = if f c = 1 then w else w⁻¹
      rw [h1, h2]; simp
    · show c * w * c⁻¹ = if f c = 1 then w else w⁻¹
      have : ¬ (f c = 1) := by rw [h2]; decide
      rw [h1]; simp [this]

theorem eq_one_of_swap {ψ' : Perm (Fin 4) →* ℤˣ} {i j : Fin 4} (hij : i ≠ j)
    (h : ψ' (swap i j) = 1) (π : Perm (Fin 4)) : ψ' π = 1 := by
  by_contra hne
  have hsurj : Function.Surjective ψ' := by
    intro z
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, map_one _⟩
    · rcases Int.units_eq_one_or (ψ' π) with h1 | h1
      · exact absurd h1 hne
      · exact ⟨π, h1⟩
  have := Equiv.Perm.eq_sign_of_surjective_hom hsurj
  have h2 := congrArg (fun f => f (swap i j)) this
  simp only [h, sign_swap hij] at h2
  exact absurd h2 (by decide)

end Aux

section Group

variable {C : Type} [Group C] [Finite C]

theorem frattini_arg (N A : Subgroup C) (hNn : N.Normal) (hA : IsSylowOf 2 A N) (c : C) :
    ∃ k ∈ N, k⁻¹ * c ∈ normalizer (A : Set C) := by
  let X : Subgroup C := A.map (MulAut.conj c).toMonoidHom
  have hAN : A ≤ N := by
    obtain ⟨Q, rfl⟩ := hA
    exact Subgroup.map_subtype_le _
  have hXN : X ≤ N := by
    rintro _ ⟨a, ha, rfl⟩
    exact hNn.conj_mem a (hAN ha) c
  have hX : IsPGroup 2 X := hA.isPGroup.map _
  obtain ⟨k, hk, hkX⟩ := exists_mem_conj_le_of_isSylowOf hA hXN hX
  refine ⟨k, hk, TIData.mem_normalizer_of_forall A fun a ha => ?_⟩
  have := hkX (c * a * c⁻¹) ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have e : k⁻¹ * c * a * (k⁻¹ * c)⁻¹ = k⁻¹ * (c * a * c⁻¹) * k := by group
  rw [e]
  exact this

theorem card_C0 (E A : Subgroup C) (w : C) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hAcard : Nat.card A = 16) (hAE : ∀ t ∈ A, ∀ e ∈ E, t * e = e * t)
    (hwE : ∀ e ∈ E, w * e = e * w)
    (hC0 : ∀ g : C, (∀ e ∈ E, g * e = e * g) → ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * t) :
    Nat.card (centralizer (E : Set C)) = 48 := by
  have hmemC0 : ∀ g : C, g ∈ centralizer (E : Set C) ↔ ∀ e ∈ E, g * e = e * g := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h e he
      exact (h e he).symm
    · intro h e he
      exact (h e he).symm
  have hle : Nat.card (centralizer (E : Set C)) ≤ 48 := by
    let f : Fin 3 × A → centralizer (E : Set C) := fun p =>
      ⟨w ^ (p.1 : ℕ) * (p.2 : C), by
        rw [hmemC0]
        intro e he
        have h1 : w ^ (p.1 : ℕ) * e = e * w ^ (p.1 : ℕ) := by
          have : Commute w e := hwE e he
          exact (this.pow_left _).eq
        calc w ^ (p.1 : ℕ) * (p.2 : C) * e = w ^ (p.1 : ℕ) * ((p.2 : C) * e) := by rw [mul_assoc]
          _ = w ^ (p.1 : ℕ) * (e * (p.2 : C)) := by rw [hAE _ p.2.2 e he]
          _ = (w ^ (p.1 : ℕ) * e) * (p.2 : C) := by rw [mul_assoc]
          _ = e * w ^ (p.1 : ℕ) * (p.2 : C) := by rw [h1]
          _ = e * (w ^ (p.1 : ℕ) * (p.2 : C)) := by rw [mul_assoc]⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨k, t, ht, rfl⟩ := hC0 g ((hmemC0 g).1 hg)
      refine ⟨(⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨t, ht⟩), Subtype.ext ?_⟩
      show w ^ (k % 3) * t = w ^ k * t
      have : w ^ (k % 3) = w ^ k := by
        conv_rhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, hw3, one_pow, mul_one]
      rw [this]
    have := Nat.card_le_card_of_surjective f hsurj
    simpa [Nat.card_prod, hAcard] using this
  have h16 : 16 ∣ Nat.card (centralizer (E : Set C)) := by
    rw [← hAcard]
    apply Subgroup.card_dvd_of_le
    intro t ht
    exact (hmemC0 t).2 (hAE t ht)
  have h3 : 3 ∣ Nat.card (centralizer (E : Set C)) := by
    have := Subgroup.card_dvd_of_le (show zpowers w ≤ centralizer (E : Set C) from by
      rw [zpowers_le]
      exact (hmemC0 w).2 hwE)
    rwa [Nat.card_zpowers, orderOf_eq_prime hw3 hw1] at this
  have h48 : 48 ∣ Nat.card (centralizer (E : Set C)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 16 3) h16 h3
  have hpos : 0 < Nat.card (centralizer (E : Set C)) := Nat.card_pos
  exact le_antisymm hle (Nat.le_of_dvd hpos h48)

theorem theta_mem_E_iff {A E : Subgroup C} (hEA : E ≤ A) (hcard : Nat.card A = 2 * Nat.card E)
    (θ : N4 →* C) (hθA : ∀ ε, θ ε ∈ A) (hb : ∀ i, θ (Pi.mulSingle i (-1)) ∉ E) (ε : N4) :
    θ ε ∈ E ↔ prodHom ε = 1 := by
  classical
  have hmul : ∀ x y : C, x ∈ A → y ∈ A → (x * y ∈ E ↔ (x ∈ E ↔ y ∈ E)) := by
    intro x y hx hy
    have h1 := Subgroup.relIndex_mul_card E A
    rw [inf_eq_left.2 hEA, hcard] at h1
    have h2 : E.relIndex A = 2 := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    have h3 : (E.subgroupOf A).index = 2 := h2
    exact Subgroup.mul_mem_iff_of_index_two h3 (a := (⟨x, hx⟩ : A)) (b := ⟨y, hy⟩)
  let ν : N4 →* ℤˣ := MonoidHom.mk' (fun ε => if θ ε ∈ E then 1 else -1) (by
    intro ε ε'
    have h := hmul (θ ε) (θ ε') (hθA ε) (hθA ε')
    rw [map_mul]
    by_cases h1 : θ ε ∈ E <;> by_cases h2 : θ ε' ∈ E
    · have : θ ε * θ ε' ∈ E := h.2 (iff_of_true h1 h2)
      simp [this, h1, h2]
    · have : θ ε * θ ε' ∉ E := fun hh => h2 ((h.1 hh).1 h1)
      simp [this, h1, h2]
    · have : θ ε * θ ε' ∉ E := fun hh => h1 ((h.1 hh).2 h2)
      simp [this, h1, h2]
    · have : θ ε * θ ε' ∈ E := h.2 (iff_of_false h1 h2)
      simp [this, h1, h2])
  have hν : ν = prodHom := by
    apply MonoidHom.pi_ext
    intro i u
    rcases Int.units_eq_one_or u with rfl | rfl
    · simp [ν]
    · have : ν (Pi.mulSingle i (-1)) = -1 := by simp [ν, MonoidHom.mk', hb i]
      rw [this]
      simp [prodHom, Pi.mulSingle_apply]
  have h1 : θ ε ∈ E ↔ ν ε = 1 := by
    by_cases h : θ ε ∈ E
    · simp [ν, h]
    · simp [ν, h]
  rw [h1, hν]

theorem card_normalizer (E A : Subgroup C) (hCcard : Nat.card C = 1152) (hEn : E.Normal)
    (hAcard : Nat.card A = 16) (hAE : ∀ t ∈ A, ∀ e ∈ E, t * e = e * t)
    (w : C) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hwE : ∀ e ∈ E, w * e = e * w)
    (hC0 : ∀ g : C, (∀ e ∈ E, g * e = e * g) → ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * t)
    (hNW : ∀ z ∈ zpowers w, z ∈ normalizer (A : Set C) → z = 1) :
    (∀ c : C, ∃ w' ∈ zpowers w, ∃ r ∈ normalizer (A : Set C), c = w' * r) ∧
      Nat.card (normalizer (A : Set C)) = 384 := by
  classical
  set N : Subgroup C := normalizer (A : Set C) with hN
  have hAN : A ≤ N := Subgroup.le_normalizer
  set C0 : Subgroup C := centralizer (E : Set C) with hC0def
  have hmemC0 : ∀ g : C, g ∈ C0 ↔ ∀ e ∈ E, g * e = e * g := by
    intro g
    rw [hC0def, Subgroup.mem_centralizer_iff]
    exact ⟨fun h e he => (h e he).symm, fun h e he => (h e he).symm⟩
  have hC0card : Nat.card C0 = 48 := card_C0 E A w hw3 hw1 hAcard hAE hwE hC0
  have hC0n : C0.Normal := ⟨fun g hg c => by
    rw [hmemC0] at hg ⊢
    intro e he
    have he' : c⁻¹ * e * c ∈ E := by
      have := hEn.conj_mem e he c⁻¹
      simpa using this
    have h1 := hg _ he'
    calc c * g * c⁻¹ * e = c * (g * (c⁻¹ * e * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * e * c) * g) * c⁻¹ := by rw [h1]
      _ = e * (c * g * c⁻¹) := by group⟩
  have hAC0 : A ≤ C0 := fun t ht => (hmemC0 t).2 (hAE t ht)
  have hSylA : IsSylowOf 2 A C0 := by
    refine isSylowOf_of_card hAC0 ?_
    have h48 : (48 : ℕ).factorization 2 = 4 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      have : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3)]
    rw [hAcard, hC0card, h48]
    norm_num
  have hfratt : ∀ c : C, ∃ w' ∈ zpowers w, ∃ r ∈ N, c = w' * r := by
    intro c
    obtain ⟨k, hk, hkN⟩ := frattini_arg C0 A hC0n hSylA c
    obtain ⟨j, t, ht, hkj⟩ := hC0 k ((hmemC0 k).1 hk)
    refine ⟨w ^ j, pow_mem (mem_zpowers w) j, t * (k⁻¹ * c), N.mul_mem (hAN ht) hkN, ?_⟩
    calc c = k * (k⁻¹ * c) := by group
      _ = w ^ j * (t * (k⁻¹ * c)) := by rw [hkj]; group
  refine ⟨hfratt, ?_⟩
  have hdisj : Disjoint (zpowers w) N := by
    rw [Subgroup.disjoint_def]
    exact fun {z} hz hzN => hNW z hz hzN
  have hmul : ((zpowers w : Subgroup C) : Set C) * (N : Set C) = Set.univ := by
    ext c
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨w', hw', r, hr, rfl⟩ := hfratt c
      exact ⟨w', hw', r, hr, rfl⟩
  have hcompl := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have h := hcompl.card_mul_card
  rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1, hCcard] at h
  omega

theorem exists_mulEquiv_W7_of_data
    (hCcard : Nat.card C = 1152) (E A : Subgroup C) (hEn : E.Normal)
    (hEcard : Nat.card E = 8) (hEcomm : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a)
    (hAcard : Nat.card A = 16) (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a)
    (hAsq : ∀ a ∈ A, a * a = 1) (hEA : E ≤ A) (hAE : ∀ t ∈ A, ∀ e ∈ E, t * e = e * t)
    (w : C) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hwE : ∀ e ∈ E, w * e = e * w)
    (hC0 : ∀ g : C, (∀ e ∈ E, g * e = e * g) → ∃ k : ℕ, ∃ t ∈ A, g = w ^ k * t)
    (hinv : ∀ t ∈ A, t ∉ E → t * w * t⁻¹ = w⁻¹)
    (b : Fin 4 → C) (hbA : ∀ i, b i ∈ A) (hbE : ∀ i, b i ∉ E) (hbsq : ∀ i, b i * b i = 1)
    (hbinj : Function.Injective b) (hbgen : ∀ t ∈ A, t ∈ Subgroup.closure (Set.range b))
    (hbperm : ∀ r ∈ normalizer (A : Set C), ∀ i, ∃ j, r * b i * r⁻¹ = b j)
    (S R : Subgroup C) (hS : IsSylowOf 2 S ⊤) (hSN : S ≤ normalizer (A : Set C)) (hAS : A ≤ S)
    (hAR : A ⊓ R = ⊥) (hARS : A ⊔ R = S)
    (Tm : Subgroup C) (hATm : A ≤ Tm) (hTmS : Tm ≤ S)
    (hM9all : ∀ (t y : C) (π₁ π₂ : Perm (Fin 4)), t ∈ Tm → y ∈ Tm → t ∉ A → y ∉ A →
      t * t = 1 → y * y = 1 → t * y = y * t → π₁.IsSwap → π₂.IsSwap → Disjoint π₁ π₂ →
      (∀ i, t * b i * t⁻¹ = b (π₁ i)) → (∀ i, y * b i * y⁻¹ = b (π₂ i)) → t * w = w * t)
    (hM9ex : ∃ (t y : C) (π₁ π₂ : Perm (Fin 4)), t ∈ Tm ∧ y ∈ Tm ∧ t ∉ A ∧ y ∉ A ∧
      t * t = 1 ∧ y * y = 1 ∧ t * y = y * t ∧ π₁.IsSwap ∧ π₂.IsSwap ∧ Disjoint π₁ π₂ ∧
      (∀ i, t * b i * t⁻¹ = b (π₁ i)) ∧ (∀ i, y * b i * y⁻¹ = b (π₂ i))) :
    Nonempty (W7 ≃* C) := by
  classical
  have hW : ∀ c : C, c * w * c⁻¹ ∈ zpowers w := conj_mem_zpowers E A hEn w hw3 hAsq hwE hC0 hinv
  set N : Subgroup C := normalizer (A : Set C) with hN
  have hAN : A ≤ N := Subgroup.le_normalizer
  have hNW : ∀ z ∈ zpowers w, z ∈ N → z = 1 := fun z hz hzN =>
    eq_one_of_mem_normalizer A E w hw3 hw1 hAsq (b 0) (hbA 0) (hbE 0) hinv hz hzN
  obtain ⟨hfratt, hNcard⟩ := card_normalizer E A hCcard hEn hAcard hAE w hw3 hw1 hwE hC0 hNW
  have hEN : E ≤ N := hEA.trans hAN
  have hRS : R ≤ S := by rw [← hARS]; exact le_sup_right
  have hRN : R ≤ N := hRS.trans hSN
  have hcentN : ∀ c ∈ N, (∀ e ∈ E, c * e = e * c) → c ∈ A := by
    intro c hc hcomm
    obtain ⟨k, t, ht, hct⟩ := hC0 c hcomm
    have h1 : w ^ k ∈ N := by
      have : w ^ k = c * t⁻¹ := by rw [hct]; group
      rw [this]; exact N.mul_mem hc (N.inv_mem (hAN ht))
    have h2 := hNW _ (pow_mem (mem_zpowers w) k) h1
    rw [hct, h2, one_mul]; exact ht
  have hSylN : IsSylowOf 2 (S.subgroupOf N) ⊤ := by
    rw [← isSylowOf_map_subtype_iff N, Subgroup.subgroupOf_map_subtype, Subgroup.map_top,
      Subgroup.range_subtype, inf_eq_left.2 hSN]
    exact hS.of_le hSN le_top
  obtain ⟨P, hP⟩ := PartB6.exists_sylow_eq_of_isSylowOf_top hSylN
  let b' : Fin 4 → ↥N := fun i => ⟨b i, hAN (hbA i)⟩
  have hEn' : (E.subgroupOf N).Normal := ⟨fun e he g => hEn.conj_mem (e : C) he (g : C)⟩
  have hEcomm' : ∀ a ∈ E.subgroupOf N, ∀ a' ∈ E.subgroupOf N, a * a' = a' * a :=
    fun a ha a' ha' => Subtype.ext (hEcomm a ha a' ha')
  have hA' : ∀ c : ↥N, c ∈ A.subgroupOf N ↔ ∀ e ∈ E.subgroupOf N, c * e = e * c := by
    intro c
    constructor
    · intro hc e he
      exact Subtype.ext (hAE c hc e he)
    · intro hc
      exact hcentN c c.2 fun e he => congrArg Subtype.val (hc ⟨e, hEN he⟩ he)
  have hAcard' : Nat.card (A.subgroupOf N) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv).trans hAcard
  have hAcomm' : ∀ a ∈ A.subgroupOf N, ∀ a' ∈ A.subgroupOf N, a * a' = a' * a :=
    fun a ha a' ha' => Subtype.ext (hAcomm a ha a' ha')
  have hbA' : ∀ i, b' i ∈ A.subgroupOf N := hbA
  have hbsq' : ∀ i, b' i * b' i = 1 := fun i => Subtype.ext (hbsq i)
  have hbinj' : Function.Injective b' := fun i j hij => hbinj (congrArg Subtype.val hij)
  have hbgen' : ∀ t ∈ A.subgroupOf N, t ∈ Subgroup.closure (Set.range b') := by
    intro t ht
    have h1 : (t : C) ∈ Subgroup.closure (Set.range b) := hbgen t ht
    have h2 : Subgroup.closure (Set.range b) = (Subgroup.closure (Set.range b')).map N.subtype := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      rfl
    rw [h2] at h1
    obtain ⟨u, hu, hut⟩ := h1
    have : u = t := Subtype.ext hut
    rwa [← this]
  have hbperm' : ∀ r : ↥N, ∀ i, ∃ j, r * b' i * r⁻¹ = b' j := by
    intro r i
    obtain ⟨j, hj⟩ := hbperm r r.2 i
    exact ⟨j, Subtype.ext hj⟩
  have hAP' : A.subgroupOf N ≤ (P : Subgroup ↥N) := by
    rw [hP]
    exact fun e he => hAS he
  have hAR' : A.subgroupOf N ⊓ R.subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨he1, he2⟩
    have h1 : (e : C) ∈ A ⊓ R := ⟨he1, he2⟩
    rw [hAR, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  have hARP' : A.subgroupOf N ⊔ R.subgroupOf N = (P : Subgroup ↥N) := by
    rw [hP, ← hARS]
    exact (Subgroup.subgroupOf_sup hAN hRN).symm
  obtain ⟨θ', s', hθ'inj, hθ'b, hθ'A, hcomp', hs'⟩ := PartB6.exists_theta_s_of_data hNcard
    (E.subgroupOf N) (A.subgroupOf N) b' P (R.subgroupOf N) hEn' hEcomm' hA' hAcard' hAcomm' hbA'
    hbsq' hbinj' hbgen' hbperm' hAP' hAR' hARP'
  let θ : N4 →* C := N.subtype.comp θ'
  let s : Perm (Fin 4) →* C := N.subtype.comp s'
  have hθinj : Function.Injective θ := N.subtype_injective.comp hθ'inj
  have hθb : ∀ i, θ (Pi.mulSingle i (-1)) = b i := fun i => congrArg Subtype.val (hθ'b i)
  have hθA : ∀ ε, θ ε ∈ A := fun ε => hθ'A ε
  have hsb : ∀ π i, s π * b i * (s π)⁻¹ = b (π i) := fun π i => congrArg Subtype.val (hs' π i)
  have hcompat : ∀ π, θ.comp (MulEquiv.toMonoidHom (actHom π)) =
      (MulEquiv.toMonoidHom (MulAut.conj (s π))).comp θ := by
    intro π
    refine MonoidHom.ext fun ε => ?_
    have h1 := congrArg (fun f => (f ε : ↥N)) (hcomp' π)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    show ((θ' ((actHom π) ε) : ↥N) : C) =
      ((s' π : ↥N) : C) * ((θ' ε : ↥N) : C) * ((s' π : ↥N) : C)⁻¹
    rw [h1]
    rfl
  have hdisj : ∀ ε π, θ ε * s π ∈ zpowers w → θ ε * s π = 1 := by
    intro ε π h1
    have hN1 : θ ε * s π ∈ N := (θ' ε * s' π).2
    exact hNW _ h1 hN1
  have hθw : ∀ ε, θ ε * w * (θ ε)⁻¹ = if prodHom ε = 1 then w else w⁻¹ := by
    intro ε
    have hiff := theta_mem_E_iff hEA (by rw [hAcard, hEcard]) θ hθA
      (fun i => by rw [hθb i]; exact hbE i) ε
    by_cases h : prodHom ε = 1
    · have hE' : θ ε ∈ E := hiff.2 h
      have hc := hwE _ hE'
      simp only [h, ↓reduceIte]
      calc θ ε * w * (θ ε)⁻¹ = (w * θ ε) * (θ ε)⁻¹ := by rw [hc]
        _ = w := by group
    · have hE' : θ ε ∉ E := fun hm => h (hiff.1 hm)
      simp only [h, ↓reduceIte]
      exact hinv _ (hθA ε) hE'
  have hw2 : w ≠ w⁻¹ := by
    intro h
    apply hw1
    have : w * w = 1 := by rw [mul_eq_one_iff_eq_inv]; exact h
    have h3 : w = w ^ 3 * (w * w)⁻¹ := by group
    rw [h3, hw3, this]; group
  have hsw : ∀ π, s π * w * (s π)⁻¹ = w := by
    obtain ⟨ψ, hψ⟩ := exists_psi w hw3 hw1 hW
    obtain ⟨t, y, π₁, π₂, htT, hyT, htA, hyA, ht2, hy2, hty, hπ₁, hπ₂, hdis, htb, hyb⟩ := hM9ex
    have hsTm : ∀ (π : Perm (Fin 4)) (t : C), t ∈ Tm → (∀ i, t * b i * t⁻¹ = b (π i)) →
        s π ∈ Tm := by
      intro π t ht htπ
      have htN : t ∈ N := hSN (hTmS ht)
      have hsN : s π ∈ N := (s' π).2
      set u : C := (s π)⁻¹ * t with hu
      have huN : u ∈ N := N.mul_mem (N.inv_mem hsN) htN
      have hub : ∀ i, u * b i = b i * u := by
        intro i
        have h1 := hsb π i
        have h2 := htπ i
        have h3 : (s π)⁻¹ * (t * b i * t⁻¹) * s π = b i := by
          rw [h2]
          calc (s π)⁻¹ * b (π i) * s π = (s π)⁻¹ * (s π * b i * (s π)⁻¹) * s π := by rw [h1]
            _ = b i := by group
        calc u * b i = ((s π)⁻¹ * (t * b i * t⁻¹) * s π) * u := by rw [hu]; group
          _ = b i * u := by rw [h3]
      have hcommE : ∀ e ∈ E, u * e = e * u := by
        intro e he
        have he' : e ∈ Subgroup.closure (Set.range b) := hbgen e (hEA he)
        have hle : Subgroup.closure (Set.range b) ≤ Subgroup.centralizer {u} := by
          rw [Subgroup.closure_le]
          rintro _ ⟨i, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
          exact (hub i).symm
        have h4 := hle he'
        rw [Subgroup.mem_centralizer_singleton_iff] at h4
        exact h4.symm
      have huA : u ∈ A := hcentN u huN hcommE
      have h5 : s π = t * u⁻¹ := by rw [hu]; group
      rw [h5]
      exact Tm.mul_mem ht (Tm.inv_mem (hATm huA))
    have hsnA : ∀ π : Perm (Fin 4), π.IsSwap → s π ∉ A := by
      intro π hπ hsA
      obtain ⟨i, j, hij, rfl⟩ := hπ
      have hcomm := hAcomm _ hsA (b i) (hbA i)
      have h1 := hsb (swap i j) i
      have h2 : b (swap i j i) = b i := by rw [← h1, hcomm]; group
      have h3 := hbinj h2
      rw [swap_apply_left] at h3
      exact hij h3.symm
    have hs2 : ∀ π : Perm (Fin 4), π.IsSwap → s π * s π = 1 := by
      intro π hπ
      obtain ⟨i, j, hij, rfl⟩ := hπ
      rw [← map_mul, swap_mul_self, map_one]
    have hcomm12 : s π₁ * s π₂ = s π₂ * s π₁ := by
      rw [← map_mul, ← map_mul, hdis.commute.eq]
    have hsπ₁ : s π₁ * w = w * s π₁ :=
      hM9all (s π₁) (s π₂) π₁ π₂ (hsTm π₁ t htT htb) (hsTm π₂ y hyT hyb) (hsnA π₁ hπ₁)
        (hsnA π₂ hπ₂) (hs2 π₁ hπ₁) (hs2 π₂ hπ₂) hcomm12 hπ₁ hπ₂ hdis (hsb π₁) (hsb π₂)
    have hψ1 : ψ (s π₁) = 1 := by
      by_contra hne
      have h1 := hψ (s π₁)
      simp only [hne, ↓reduceIte] at h1
      have h2 : s π₁ * w * (s π₁)⁻¹ = w := by rw [hsπ₁]; group
      exact hw2 (h2.symm.trans h1)
    have hπ₁' := hπ₁
    obtain ⟨i, j, hij, hπ₁eq⟩ := hπ₁'
    have hψs : ∀ π, ψ (s π) = 1 := by
      intro π
      have h1 : (ψ.comp s) (swap i j) = 1 := by rw [MonoidHom.comp_apply, ← hπ₁eq]; exact hψ1
      exact eq_one_of_swap hij h1 π
    intro π
    have h1 := hψ (s π)
    simp only [hψs π, ↓reduceIte] at h1
    exact h1
  exact exists_mulEquiv_W7 θ hθinj s hcompat w hw3 hw1 hθw hsw hdisj hCcard


end Group

end CFSG.GH74.GLS.C3.Layer2.L4.PartB7
