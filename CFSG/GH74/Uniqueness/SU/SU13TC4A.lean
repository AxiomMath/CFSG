module

public import CFSG.GH74.Uniqueness.SU.SU13TC4Z

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

section AProps

variable {e : Elts G z} {e9 : Elts9 z e} (f : FPart9 z e) (E9 : EPart9 z e e9 f.toFPart) (hWc : WAbel e)

theorem E_comm_Z : ∀ a ∈ E9.E, ∀ ζ ∈ Zsub (Vsub z e.s₁ hWc) E9.D, a * ζ = ζ * a := by
  intro a ha ζ hζ
  obtain ⟨i, d, hd, rfl⟩ := E9.E_eq a ha
  have h1 : e.s₁ ^ i * ζ = ζ * e.s₁ ^ i :=
    zpowers_comm_of_mem_centralizer (oc_le _ hζ.1.1) (zpow_mem_zpowers _ _)
  have h2 : d * ζ = ζ * d := by
    have := hζ.2 d hd
    calc d * ζ = d * ζ * d⁻¹ * d := by group
      _ = ζ * d := by rw [this]
  calc e.s₁ ^ i * d * ζ = e.s₁ ^ i * (d * ζ) := by group
    _ = e.s₁ ^ i * (ζ * d) := by rw [h2]
    _ = (e.s₁ ^ i * ζ) * d := by group
    _ = (ζ * e.s₁ ^ i) * d := by rw [h1]
    _ = ζ * (e.s₁ ^ i * d) := by group

theorem E_inf_V : E9.E ⊓ Vsub z e.s₁ hWc = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxE, hxV⟩ := mem_inf.mp hx
  have hxz : x * z = z * x := E9.Es_comm x (E9.Es_ge hxE)
  have h1 : x = x⁻¹ := by
    calc x = z * x * z⁻¹ := by rw [← hxz]; group
      _ = x⁻¹ := hxV.2
  have h2 : x * x = 1 := by
    calc x * x = x * x⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel x
  have h3 := E9.E_exp x hxE
  have : x = 1 := by
    calc x = x ^ 3 * (x * x)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  exact mem_bot.mpr this

theorem A_card (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    Nat.card (E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D : Subgroup G) = 3 ^ 5 := by
  have hEZ : E9.E ⊓ Zsub (Vsub z e.s₁ hWc) E9.D = ⊥ := by
    rw [eq_bot_iff, ← E_inf_V f E9 hWc]
    exact inf_le_inf_left _ (Z_le_V f E9 hWc)
  have := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute E9.E (Zsub (Vsub z e.s₁ hWc) E9.D)
    (E_comm_Z f E9 hWc)).1
  rw [hEZ, Subgroup.card_bot, E9.E_card, Z_card f E9 hWc hz hW5] at this
  norm_num at this
  omega

theorem A_mem {x : G} (hx : x ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D) :
    ∃ a ∈ E9.E, ∃ ζ ∈ Zsub (Vsub z e.s₁ hWc) E9.D, x = a * ζ := by
  obtain ⟨a, ha, ζ, hζ, h⟩ := SU1.mem_sup_of_commute (A := E9.E) (B := Zsub (Vsub z e.s₁ hWc) E9.D)
    (E_comm_Z f E9 hWc) hx
  exact ⟨a, ha, ζ, hζ, h.symm⟩

theorem A_comm : ∀ a ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D, ∀ b ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D,
    a * b = b * a := by
  intro a ha b hb
  obtain ⟨a₁, ha₁, ζ₁, hζ₁, rfl⟩ := A_mem f E9 hWc ha
  obtain ⟨b₁, hb₁, ζ₂, hζ₂, rfl⟩ := A_mem f E9 hWc hb
  have hZab : ζ₁ * ζ₂ = ζ₂ * ζ₁ := hWc ζ₁ hζ₁.1.1 ζ₂ hζ₂.1.1
  calc a₁ * ζ₁ * (b₁ * ζ₂) = a₁ * (ζ₁ * b₁) * ζ₂ := by group
    _ = a₁ * (b₁ * ζ₁) * ζ₂ := by rw [← E_comm_Z f E9 hWc b₁ hb₁ ζ₁ hζ₁]
    _ = (a₁ * b₁) * (ζ₁ * ζ₂) := by group
    _ = (b₁ * a₁) * (ζ₂ * ζ₁) := by rw [E9.E_abel a₁ ha₁ b₁ hb₁, hZab]
    _ = b₁ * (a₁ * ζ₂) * ζ₁ := by group
    _ = b₁ * (ζ₂ * a₁) * ζ₁ := by rw [E_comm_Z f E9 hWc a₁ ha₁ ζ₂ hζ₂]
    _ = b₁ * ζ₂ * (a₁ * ζ₁) := by group

theorem A_exp (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) (hz : orderOf z = 2) :
    ∀ a ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D, a ^ 3 = 1 := by
  intro a ha
  obtain ⟨a₁, ha₁, ζ, hζ, rfl⟩ := A_mem f E9 hWc ha
  have hc : Commute a₁ ζ := E_comm_Z f E9 hWc a₁ ha₁ ζ hζ
  rw [hc.mul_pow, E9.E_exp a₁ ha₁, V_exp hz f hWc hW5 ζ hζ.1, one_mul]

theorem A_inf_V : (E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D) ⊓ Vsub z e.s₁ hWc = Zsub (Vsub z e.s₁ hWc) E9.D := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxV⟩ := mem_inf.mp hx
    obtain ⟨a, ha, ζ, hζ, rfl⟩ := A_mem f E9 hWc hxA
    have : a ∈ Vsub z e.s₁ hWc := by
      have h1 : a = (a * ζ) * ζ⁻¹ := by group
      rw [h1]
      exact (Vsub z e.s₁ hWc).mul_mem hxV ((Vsub z e.s₁ hWc).inv_mem hζ.1)
    have h2 : a ∈ E9.E ⊓ Vsub z e.s₁ hWc := mem_inf.mpr ⟨ha, this⟩
    rw [E_inf_V f E9 hWc, mem_bot] at h2
    rw [h2, one_mul]; exact hζ
  · intro x hx
    exact mem_inf.mpr ⟨mem_sup_right hx, hx.1⟩

theorem zpowers_le_E : zpowers e.s₁ ≤ E9.E := (zpowers_le).mpr E9.s₁_mem

theorem z_conj_A : ∀ a ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D,
    z * a * z⁻¹ ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D := by
  intro a ha
  obtain ⟨a₁, ha₁, ζ, hζ, rfl⟩ := A_mem f E9 hWc ha
  have hza : z * a₁ * z⁻¹ = a₁ := by
    have := E9.Es_comm a₁ (E9.Es_ge ha₁)
    rw [← this]; group
  have hzζ : z * ζ * z⁻¹ = ζ⁻¹ := hζ.1.2
  have : z * (a₁ * ζ) * z⁻¹ = a₁ * ζ⁻¹ := by
    calc z * (a₁ * ζ) * z⁻¹ = (z * a₁ * z⁻¹) * (z * ζ * z⁻¹) := by group
      _ = a₁ * ζ⁻¹ := by rw [hza, hzζ]
  rw [this]
  exact mul_mem (mem_sup_left ha₁) (mem_sup_right ((Zsub (Vsub z e.s₁ hWc) E9.D).inv_mem hζ))

theorem V_le_normalizer_A (hz : orderOf z = 2)
    (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) :
    Vsub z e.s₁ hWc ≤ normalizer ((E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D : Subgroup G) : Set G) := by
  have key : ∀ v ∈ Vsub z e.s₁ hWc, ∀ a ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D,
      v * a * v⁻¹ ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D := by
    intro v hv a ha
    obtain ⟨a₁, ha₁, ζ, hζ, rfl⟩ := A_mem f E9 hWc ha
    obtain ⟨i, d, hd, rfl⟩ := E9.E_eq a₁ ha₁
    have hu : v * d * v⁻¹ * d⁻¹ ∈ Zsub (Vsub z e.s₁ hWc) E9.D := by
      have := (Zsub (Vsub z e.s₁ hWc) E9.D).inv_mem (V_comm_D f E9 hWc hz hW5 v hv d hd)
      have h2 : (d * v * d⁻¹ * v⁻¹)⁻¹ = v * d * v⁻¹ * d⁻¹ := by group
      rwa [h2] at this
    set u := v * d * v⁻¹ * d⁻¹ with hu_def
    have hs1v : e.s₁ ^ i * v = v * e.s₁ ^ i :=
      zpowers_comm_of_mem_centralizer (oc_le _ hv.1) (zpow_mem_zpowers _ _)
    have hs1u : e.s₁ ^ i * u = u * e.s₁ ^ i :=
      zpowers_comm_of_mem_centralizer (oc_le _ hu.1.1) (zpow_mem_zpowers _ _)
    have hvζ : v * ζ = ζ * v := hWc v hv.1 ζ hζ.1.1
    have h1 : v * (e.s₁ ^ i * d * ζ) * v⁻¹ = u * (e.s₁ ^ i * d) * ζ := by
      calc v * (e.s₁ ^ i * d * ζ) * v⁻¹ = (v * e.s₁ ^ i) * d * (ζ * v⁻¹) := by group
        _ = (e.s₁ ^ i * v) * d * (ζ * v⁻¹) := by rw [← hs1v]
        _ = e.s₁ ^ i * (v * d * v⁻¹) * ζ := by
          have : ζ * v⁻¹ = v⁻¹ * ζ := (Commute.inv_right (show Commute ζ v from hvζ.symm)).eq
          rw [this]; group
        _ = e.s₁ ^ i * (u * d) * ζ := by rw [hu_def]; group
        _ = (e.s₁ ^ i * u) * d * ζ := by group
        _ = (u * e.s₁ ^ i) * d * ζ := by rw [hs1u]
        _ = u * (e.s₁ ^ i * d) * ζ := by group
    rw [h1]
    have hE : e.s₁ ^ i * d ∈ E9.E :=
      E9.E.mul_mem (zpow_mem (E9.s₁_mem) i) (E9.D_le_E hd)
    exact mul_mem (mul_mem (mem_sup_right hu) (mem_sup_left hE)) (mem_sup_right hζ)
  intro v hv
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key v hv x, fun hx => ?_⟩
  have := key v⁻¹ ((Vsub z e.s₁ hWc).inv_mem hv) _ hx
  simpa [mul_assoc] using this

theorem cent_E_le (hz : orderOf z = 2) (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5)
    (l : Lem232 z e) {g : G} (hg : ∀ a ∈ E9.E, g * a = a * g) :
    ∃ a ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D, g = a ∨ g = a * z := by
  have hgs : g * e.s₁ = e.s₁ * g := hg _ E9.s₁_mem
  obtain ⟨c, k, hc, hcz, hk, hgck⟩ := l.a g hgs
  have hcH : c ∈ centralizer ({e.s₁} : Set G) ⊓ centralizer ({z} : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc, mem_centralizer_singleton_iff.mpr hcz⟩
  rw [f.cent] at hcH
  obtain ⟨p, hp, f', hf', hpf⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := f.F)
    (fun p hp a ha => zpowers_comm_of_mem_centralizer
      (mem_centralizer_singleton_iff.mpr (f.F_s₁ a ha)) hp) hcH
  obtain ⟨c', hc', v, hv, hkv⟩ := W_eq_sup_V hz f hWc hk
  have hc'f : c' * f' = f' * c' :=
    zpowers_comm_of_mem_centralizer (F_le_centralizerF e f.toFPart hf') hc'
  set q := p * c' with hq
  have hqE : q ∈ E9.E := E9.E.mul_mem (zpowers_le_E f E9 hp) (zpowers_le_E f E9 hc')
  have hg' : g = q * f' * v := by
    rw [hgck, ← hpf, hkv, hq]
    calc p * f' * (c' * v) = p * (f' * c') * v := by group
      _ = p * (c' * f') * v := by rw [hc'f]
      _ = p * c' * f' * v := by group
  have hD : ∀ d ∈ E9.D, f' * d * f'⁻¹ = d ∧ v * d = d * v := by
    intro d hd
    have hdE : d ∈ E9.E := E9.D_le_E hd
    have hgd := hg d hdE
    have hqd : q * d = d * q := E9.E_abel q hqE d hdE
    have h1 : f' * v * d = d * f' * v := by
      have h2 : q * (f' * v * d) = q * (d * f' * v) := by
        calc q * (f' * v * d) = (q * f' * v) * d := by group
          _ = d * (q * f' * v) := by rw [← hg', hgd]
          _ = (d * q) * f' * v := by group
          _ = (q * d) * f' * v := by rw [hqd]
          _ = q * (d * f' * v) := by group
      exact mul_left_cancel h2
    have hu : v * d * v⁻¹ * d⁻¹ ∈ Zsub (Vsub z e.s₁ hWc) E9.D := by
      have := (Zsub (Vsub z e.s₁ hWc) E9.D).inv_mem (V_comm_D f E9 hWc hz hW5 v hv d hd)
      have h2 : (d * v * d⁻¹ * v⁻¹)⁻¹ = v * d * v⁻¹ * d⁻¹ := by group
      rwa [h2] at this
    set u := v * d * v⁻¹ * d⁻¹ with hu_def
    have hu' : f' * u * f'⁻¹ ∈ Vsub z e.s₁ hWc := V_invariant f hWc f' hf' u hu.1
    have hd' : f' * d * f'⁻¹ ∈ f.F :=
      f.F.mul_mem (f.F.mul_mem hf' (E9.D_le_F hd)) (f.F.inv_mem hf')
    have h3 : (f' * u * f'⁻¹) * (f' * d * f'⁻¹) = d := by
      have : f' * (u * d) * f'⁻¹ = d := by
        have h4 : u * d = v * d * v⁻¹ := by rw [hu_def]; group
        rw [h4]
        calc f' * (v * d * v⁻¹) * f'⁻¹ = (f' * v * d) * v⁻¹ * f'⁻¹ := by group
          _ = (d * f' * v) * v⁻¹ * f'⁻¹ := by rw [h1]
          _ = d := by group
      calc (f' * u * f'⁻¹) * (f' * d * f'⁻¹) = f' * (u * d) * f'⁻¹ := by group
        _ = d := this
    have h5 : f' * u * f'⁻¹ ∈ oc (centralizer ({e.s₁} : Set G)) ⊓ f.F := by
      refine mem_inf.mpr ⟨hu'.1, ?_⟩
      have : f' * u * f'⁻¹ = d * (f' * d * f'⁻¹)⁻¹ := by
        calc f' * u * f'⁻¹ = ((f' * u * f'⁻¹) * (f' * d * f'⁻¹)) * (f' * d * f'⁻¹)⁻¹ := by group
          _ = d * (f' * d * f'⁻¹)⁻¹ := by rw [h3]
      rw [this]
      exact f.F.mul_mem (E9.D_le_F hd) (f.F.inv_mem hd')
    rw [W_inf_F e f.toFPart, mem_bot] at h5
    have hu1 : u = 1 := by
      have : u = f'⁻¹ * (f' * u * f'⁻¹) * f' := by group
      rw [this, h5]; group
    refine ⟨?_, ?_⟩
    · rw [hu1] at h3
      have : f' * d * f'⁻¹ = d := by simpa using h3
      exact this
    · have : v * d * v⁻¹ * d⁻¹ = 1 := hu1
      calc v * d = (v * d * v⁻¹ * d⁻¹) * (d * v) := by group
        _ = d * v := by rw [this, one_mul]
  have hvZ : v ∈ Zsub (Vsub z e.s₁ hWc) E9.D := ⟨hv, fun d hd => by
    have := (hD d hd).2
    calc d * v * d⁻¹ = v * d * d⁻¹ := by rw [← this]
      _ = v := by group⟩
  have hf'c : f' ∈ centralizer (E9.E : Set G) ⊓ centralizer ({z} : Set G) := by
    refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun a ha => ?_,
      mem_centralizer_singleton_iff.mpr (f.F_comm f' hf')⟩
    obtain ⟨i, d, hd, rfl⟩ := E9.E_eq a ha
    have h1 : e.s₁ ^ i * f' = f' * e.s₁ ^ i :=
      zpowers_comm_of_mem_centralizer (F_le_centralizerF e f.toFPart hf') (zpow_mem_zpowers _ _)
    have h2 : f' * d = d * f' := by
      have := (hD d hd).1
      calc f' * d = f' * d * f'⁻¹ * f' := by group
        _ = d * f' := by rw [this]
    calc e.s₁ ^ i * d * f' = e.s₁ ^ i * (d * f') := by group
      _ = e.s₁ ^ i * (f' * d) := by rw [h2]
      _ = (e.s₁ ^ i * f') * d := by group
      _ = (f' * e.s₁ ^ i) * d := by rw [h1]
      _ = f' * (e.s₁ ^ i * d) := by group
  rw [E9.cent] at hf'c
  have hcomm : ∀ a ∈ E9.E, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := hb
    exact ((Commute.zpow_right (show Commute a z from (E9.Es_comm a (E9.Es_ge ha)))) n).eq
  obtain ⟨e', he', w, hw, hew⟩ := SU1.mem_sup_of_commute (A := E9.E) (B := zpowers z) hcomm hf'c
  have hw' : w = 1 ∨ w = z := by
    obtain ⟨n, rfl⟩ := hw
    beta_reduce
    have h1 : z ^ n = z ^ (n % (orderOf z : ℤ)) := (zpow_mod_orderOf z n).symm
    rw [hz] at h1
    have h2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h2 | h2
    · left; rw [h1, h2, zpow_zero]
    · right; rw [h1, h2, zpow_one]
  have hzv : z * v * z⁻¹ = v⁻¹ := hv.2
  rcases hw' with hw1 | hwz
  · refine ⟨q * e' * v, mul_mem (mem_sup_left (E9.E.mul_mem hqE he')) (mem_sup_right hvZ), Or.inl ?_⟩
    rw [hw1, mul_one] at hew
    rw [hg', ← hew]
  · rw [hwz] at hew
    refine ⟨q * e' * v⁻¹, mul_mem (mem_sup_left (E9.E.mul_mem hqE he'))
      (mem_sup_right ((Zsub (Vsub z e.s₁ hWc) E9.D).inv_mem hvZ)), Or.inr ?_⟩
    rw [hg', ← hew]
    calc q * (e' * z) * v = q * e' * (z * v * z⁻¹) * z := by group
      _ = q * e' * v⁻¹ * z := by rw [hzv]

theorem NHE_le_normalizer_A (hz : orderOf z = 2)
    (hW5 : Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5) (l : Lem232 z e) :
    NHE E9.E z ≤ normalizer ((E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D : Subgroup G) : Set G) := by
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have key : ∀ g ∈ NHE E9.E z, ∀ a ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D,
      g * a * g⁻¹ ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D := by
    intro g hg a ha
    have hgN : g ∈ normalizer (E9.E : Set G) := (mem_inf.mp hg).1
    have hgz : g * z = z * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hg).2
    have hcent : ∀ b ∈ E9.E, (g * a * g⁻¹) * b = b * (g * a * g⁻¹) := by
      intro b hb
      have hb' : g⁻¹ * b * g ∈ E9.E := by
        have := (mem_normalizer_iff.mp (inv_mem hgN) b).mp hb
        simpa [mul_assoc] using this
      have h1 := A_comm f E9 hWc a ha _ (mem_sup_left hb')
      calc g * a * g⁻¹ * b = g * (a * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * a) * g⁻¹ := by rw [h1]
        _ = b * (g * a * g⁻¹) := by group
    obtain ⟨a', ha', h⟩ := cent_E_le f E9 hWc hz hW5 l hcent
    rcases h with h | h
    · rw [h]; exact ha'
    · exfalso
      have ha3 : (g * a * g⁻¹) ^ 3 = 1 := by
        rw [conj_pow, A_exp f E9 hWc hW5 hz a ha]; group
      rw [h] at ha3
      have ha'' : z * a' * z⁻¹ ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D := z_conj_A f E9 hWc a' ha'
      have h3 : (a' * z) ^ 3 = (a' * (z * a' * z⁻¹) * a') * z := by
        calc (a' * z) ^ 3 = a' * z * a' * z * a' * z := by rw [pow_succ, pow_two]; group
          _ = a' * (z * a' * z⁻¹) * (z * z) * a' * z := by group
          _ = a' * (z * a' * z⁻¹) * a' * z := by rw [hz2]; group
      rw [h3] at ha3
      have hzA : z ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D := by
        have hinv : (a' * (z * a' * z⁻¹) * a')⁻¹ ∈ E9.E ⊔ Zsub (Vsub z e.s₁ hWc) E9.D :=
          inv_mem (mul_mem (mul_mem ha' ha'') ha')
        have hzeq : z = (a' * (z * a' * z⁻¹) * a')⁻¹ := eq_inv_of_mul_eq_one_right ha3
        rwa [← hzeq] at hinv
      have h4 := A_exp f E9 hWc hW5 hz z hzA
      apply hz1
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [h4, hz2, inv_one, mul_one]
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ ((NHE E9.E z).inv_mem hg) _ hx
  simpa [mul_assoc] using this

end AProps

end CFSG.GH74.Uniqueness.SU.SU13
