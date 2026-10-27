module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory.TIFusion

open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem delta_mul {E : Subgroup G} {y : G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    (a * b)⁻¹ * (y * (a * b) * y⁻¹) = (a⁻¹ * (y * a * y⁻¹)) * (b⁻¹ * (y * b * y⁻¹)) := by
  have hc : b⁻¹ * (a⁻¹ * (y * a * y⁻¹)) = (a⁻¹ * (y * a * y⁻¹)) * b⁻¹ :=
    hEc _ (E.inv_mem hb) _ (E.mul_mem (E.inv_mem ha) (hyE a ha))
  calc (a * b)⁻¹ * (y * (a * b) * y⁻¹)
      = b⁻¹ * (a⁻¹ * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
    _ = (a⁻¹ * (y * a * y⁻¹)) * b⁻¹ * (y * b * y⁻¹) := by rw [hc]
    _ = _ := by group

omit [Finite G] in
theorem delta_inv {E : Subgroup G} {y : G} (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) {a : G} (ha : a ∈ E) :
    (a⁻¹)⁻¹ * (y * a⁻¹ * y⁻¹) = (a⁻¹ * (y * a * y⁻¹))⁻¹ := by
  have hc : a * (y * a * y⁻¹)⁻¹ = (y * a * y⁻¹)⁻¹ * a := hEc _ ha _ (E.inv_mem (hyE a ha))
  calc (a⁻¹)⁻¹ * (y * a⁻¹ * y⁻¹) = a * (y * a * y⁻¹)⁻¹ := by group
    _ = (y * a * y⁻¹)⁻¹ * a := hc
    _ = (a⁻¹ * (y * a * y⁻¹))⁻¹ := by group

omit [Finite G] in
@[expose] def cstar (E N : Subgroup G) (y : G)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) : Subgroup G where
  carrier := {e | e ∈ E ∧ e⁻¹ * (y * e * y⁻¹) ∈ N}
  one_mem' := ⟨E.one_mem, by simpa using N.one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, haN⟩ ⟨hb, hbN⟩
    exact ⟨E.mul_mem ha hb, by rw [delta_mul hEc hyE ha hb]; exact N.mul_mem haN hbN⟩
  inv_mem' := by
    rintro a ⟨ha, haN⟩
    exact ⟨E.inv_mem ha, by rw [delta_inv hEc hyE ha]; exact N.inv_mem haN⟩

omit [Finite G] in
theorem cstar_le {E N : Subgroup G} {y : G} {hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a}
    {hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E} : cstar E N y hEc hyE ≤ E :=
  fun _ h => h.1

theorem card_mul_card_le_sq_aux {A : Type*} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) (δ : A →* A) (hδ : ∀ a, δ (δ a) = 1)
    (M : Subgroup A) (hM : ∀ m ∈ M, δ m ∈ M) :
    Nat.card A * Nat.card M ≤ Nat.card ↥(M.comap δ) ^ 2 := by
  haveI : M.Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  have hD : δ.range ≤ M.comap δ := by
    rintro _ ⟨a, rfl⟩
    show δ (δ a) ∈ M
    rw [hδ]
    exact M.one_mem
  have hsup : M ⊔ δ.range ≤ M.comap δ := sup_le (fun m hm => hM m hm) hD
  have h1 : Nat.card ↥(M.comap δ) * (M.comap δ).index = Nat.card A := Subgroup.card_mul_index _
  have h2 : (M.comap δ).index = M.relIndex δ.range := Subgroup.index_comap M δ
  have h3 : M.relIndex (M ⊔ δ.range) = M.relIndex δ.range := Subgroup.relIndex_sup_left δ.range M
  have h4 : M.relIndex (M ⊔ δ.range) * Nat.card ↥(M ⊓ (M ⊔ δ.range)) =
      Nat.card ↥(M ⊔ δ.range) := Subgroup.relIndex_mul_card M (M ⊔ δ.range)
  rw [inf_eq_left.mpr le_sup_left] at h4
  have h5 : Nat.card ↥(M ⊔ δ.range) ≤ Nat.card ↥(M.comap δ) := Subgroup.card_le_of_le hsup
  calc Nat.card A * Nat.card M
      = Nat.card ↥(M.comap δ) * ((M.comap δ).index * Nat.card M) := by rw [← h1]; ring
    _ = Nat.card ↥(M.comap δ) * Nat.card ↥(M ⊔ δ.range) := by rw [h2, ← h3, h4]
    _ ≤ Nat.card ↥(M.comap δ) * Nat.card ↥(M.comap δ) := Nat.mul_le_mul_left _ h5
    _ = Nat.card ↥(M.comap δ) ^ 2 := (sq _).symm

theorem card_mul_card_le_sq (E N : Subgroup G) (hNE : N ≤ E)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    {y : G} (hy : y * y = 1) (hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E) (hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N) :
    Nat.card E * Nat.card N ≤ Nat.card ↥(cstar E N y hEc hyE) ^ 2 := by
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hEc a a.2 b b.2)
  let δ : E →* E := MonoidHom.mk'
    (fun e => ⟨(e : G)⁻¹ * (y * e * y⁻¹), E.mul_mem (E.inv_mem e.2) (hyE e e.2)⟩)
    (fun a b => Subtype.ext (delta_mul hEc hyE a.2 b.2))
  have hδ : ∀ e : E, ((δ e : E) : G) = (e : G)⁻¹ * (y * e * y⁻¹) := fun _ => rfl
  have hyy : ∀ g : G, y * (y * g * y⁻¹) * y⁻¹ = g := by
    intro g
    calc y * (y * g * y⁻¹) * y⁻¹ = (y * y) * g * (y * y)⁻¹ := by group
      _ = g := by rw [hy]; group
  have hδδ : ∀ e : E, δ (δ e) = 1 := by
    intro e
    apply Subtype.ext
    have hα : y * (e : G) * y⁻¹ ∈ E := hyE e e.2
    have h2 := hE2 ((y * (e : G) * y⁻¹)⁻¹ * (e : G)) (E.mul_mem (E.inv_mem hα) e.2)
    have hexp : y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹ = (y * (e : G) * y⁻¹)⁻¹ * (e : G) := by
      calc y * ((e : G)⁻¹ * (y * e * y⁻¹)) * y⁻¹
          = (y * (e : G) * y⁻¹)⁻¹ * (y * (y * e * y⁻¹) * y⁻¹) := by group
        _ = _ := by rw [hyy]
    have h3 : ((δ (δ e) : E) : G) = 1 := by
      rw [hδ (δ e), hδ e, hexp]
      calc ((e : G)⁻¹ * (y * e * y⁻¹))⁻¹ * ((y * (e : G) * y⁻¹)⁻¹ * (e : G))
          = ((y * (e : G) * y⁻¹)⁻¹ * (e : G)) * ((y * (e : G) * y⁻¹)⁻¹ * (e : G)) := by group
        _ = 1 := h2
    exact h3
  let M : Subgroup E := N.subgroupOf E
  have hM : ∀ m ∈ M, δ m ∈ M := by
    intro m hm
    have hm' : (m : G) ∈ N := hm
    show ((δ m : E) : G) ∈ N
    rw [hδ m]
    exact N.mul_mem (N.inv_mem hm') (hyN _ hm')
  have key := card_mul_card_le_sq_aux hcomm δ hδδ M hM
  have hcardM : Nat.card M = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNE).toEquiv
  have hcomap : M.comap δ = (cstar E N y hEc hyE).subgroupOf E := by
    ext x
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcardC : Nat.card ↥(M.comap δ) = Nat.card ↥(cstar E N y hEc hyE) := by
    rw [hcomap]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe cstar_le).toEquiv
  rw [← hcardM, ← hcardC]
  exact key

theorem fusion_of_rank (X E N : Subgroup G) (hEX : E ≤ X) (hNE : N ≤ E)
    (hNX : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hTI : ∀ g ∈ X, ∀ e ∈ E, e ∉ N → g * e * g⁻¹ ∈ E → g ∈ normalizer (E : Set G))
    {e : G} (he : e ∈ E) (heN : e ∉ N) (k : ℕ)
    (hrank : ∀ B : Subgroup G, B ≤ X ⊓ normalizer (E : Set G) →
      (∀ b ∈ B, e⁻¹ * (b * e * b⁻¹) ∈ N) → (∀ b ∈ B, b * b = 1) →
      Nat.card B ≤ Nat.card ↥(B ⊓ E) * 2 ^ k)
    (hk : (Nat.card N * 2 ^ k) ^ 2 < Nat.card E * Nat.card N) :
    ∀ g ∈ X, g * e * g⁻¹ ∈ normalizer (E : Set G) → g * e * g⁻¹ ∈ E := by
  intro g hgX hgn
  by_contra hgE
  obtain ⟨y, hy⟩ : ∃ y : G, y = g * e * g⁻¹ := ⟨_, rfl⟩
  rw [← hy] at hgn hgE
  have hy2 : y * y = 1 := by
    rw [hy]
    calc g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ := by group
      _ = 1 := by rw [hE2 e he]; group
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hyX : y ∈ X := by
    rw [hy]
    exact X.mul_mem (X.mul_mem hgX (hEX he)) (X.inv_mem hgX)
  have hyE : ∀ e' ∈ E, y * e' * y⁻¹ ∈ E := fun e' he' => (mem_normalizer_iff.mp hgn e').mp he'
  have hyN : ∀ n ∈ N, y * n * y⁻¹ ∈ N := hNX y hyX
  have hgn' : g ∉ normalizer (E : Set G) := fun hg =>
    hgE (by rw [hy]; exact (mem_normalizer_iff.mp hg e).mp he)
  have hcount := card_mul_card_le_sq E N hNE hE2 hEc hy2 hyE hyN
  let C : Subgroup G := cstar E N y hEc hyE
  let B : Subgroup G := C.map (MulAut.conj g⁻¹).toMonoidHom
  have hBmem : ∀ b ∈ B, ∃ c ∈ C, b = g⁻¹ * c * g := by
    intro b hb
    obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
    refine ⟨c, hc, ?_⟩
    rw [← hcb]
    simp [MulAut.conj_apply]
  have hfacts : ∀ b ∈ B, ∃ c ∈ E, ∃ n ∈ N, b = g⁻¹ * c * g ∧ c * c = 1 ∧
      b * e * b⁻¹ = e * (g⁻¹ * n * g) := by
    intro b hb
    obtain ⟨c, hcC, rfl⟩ := hBmem b hb
    obtain ⟨hcE, hcn⟩ := hcC
    refine ⟨c, hcE, _, hcn, rfl, hE2 c hcE, ?_⟩
    have hcomm' : c⁻¹ * (y * c * y⁻¹) = (y * c * y⁻¹) * c⁻¹ :=
      hEc _ (E.inv_mem hcE) _ (hyE c hcE)
    have hcy : c * y * c⁻¹ = y * (c⁻¹ * (y * c * y⁻¹)) := by
      rw [hcomm']
      calc c * y * c⁻¹ = c * y⁻¹ * c⁻¹ := by rw [hyinv]
        _ = (y * y) * c * y⁻¹ * c⁻¹ := by rw [hy2, one_mul]
        _ = y * (y * c * y⁻¹ * c⁻¹) := by group
    calc g⁻¹ * c * g * e * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * y * c⁻¹) * g := by rw [hy]; group
      _ = g⁻¹ * (y * (c⁻¹ * (y * c * y⁻¹))) * g := by rw [hcy]
      _ = (g⁻¹ * y * g) * (g⁻¹ * (c⁻¹ * (y * c * y⁻¹)) * g) := by group
      _ = e * (g⁻¹ * (c⁻¹ * (y * c * y⁻¹)) * g) := by rw [hy]; group
  have hconjN : ∀ n ∈ N, g⁻¹ * n * g ∈ N := by
    intro n hn
    have := hNX g⁻¹ (X.inv_mem hgX) n hn
    rwa [inv_inv] at this
  have hB1 : B ≤ X ⊓ normalizer (E : Set G) := by
    intro b hb
    obtain ⟨c, hcE, n, hn, hbc, -, hbe⟩ := hfacts b hb
    have hbX : b ∈ X := by
      rw [hbc]
      exact X.mul_mem (X.mul_mem (X.inv_mem hgX) (hEX hcE)) hgX
    refine ⟨hbX, hTI b hbX e he heN ?_⟩
    rw [hbe]
    exact E.mul_mem he (hNE (hconjN n hn))
  have hB2 : ∀ b ∈ B, e⁻¹ * (b * e * b⁻¹) ∈ N := by
    intro b hb
    obtain ⟨-, -, n, hn, -, -, hbe⟩ := hfacts b hb
    rw [hbe, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hconjN n hn
  have hB3 : ∀ b ∈ B, b * b = 1 := by
    intro b hb
    obtain ⟨c, -, -, -, hbc, hc2, -⟩ := hfacts b hb
    rw [hbc]
    calc g⁻¹ * c * g * (g⁻¹ * c * g) = g⁻¹ * (c * c) * g := by group
      _ = 1 := by rw [hc2]; group
  have hBE : B ⊓ E ≤ N := by
    rintro b ⟨hb, hbE⟩
    by_contra hbN
    obtain ⟨c, hcE, -, -, hbc, -, -⟩ := hfacts b hb
    apply hgn'
    refine hTI g hgX b hbE hbN ?_
    have : g * b * g⁻¹ = c := by rw [hbc]; group
    rw [this]
    exact hcE
  have hcardB : Nat.card B = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have h1 := hrank B hB1 hB2 hB3
  have h2 : Nat.card ↥(B ⊓ E) ≤ Nat.card N := Subgroup.card_le_of_le hBE
  have h3 : Nat.card C ≤ Nat.card N * 2 ^ k :=
    calc Nat.card C = Nat.card B := hcardB.symm
      _ ≤ Nat.card ↥(B ⊓ E) * 2 ^ k := h1
      _ ≤ Nat.card N * 2 ^ k := Nat.mul_le_mul_right _ h2
  have h4 : Nat.card C ^ 2 ≤ (Nat.card N * 2 ^ k) ^ 2 := Nat.pow_le_pow_left h3 2
  exact lt_irrefl _ (lt_of_le_of_lt (hcount.trans h4) hk)

omit [Finite G] in
theorem mul_pow_eq_inv_pow_mul {a r : G} (h : a * r * a⁻¹ = r⁻¹) (j : ℕ) :
    a * r ^ j = (r ^ j)⁻¹ * a := by
  have h1 : (a * r * a⁻¹) ^ j = a * r ^ j * a⁻¹ := conj_pow
  rw [h, inv_pow] at h1
  rw [h1, inv_mul_cancel_right]

omit [Finite G] in
theorem mul_pow_two_mul {x r : G} (h : x * r * x⁻¹ = r⁻¹) (j : ℕ) :
    x * r ^ (2 * j) = (r ^ j)⁻¹ * x * r ^ j := by
  rw [two_mul, pow_add, ← mul_assoc, mul_pow_eq_inv_pow_mul h j]

omit [Finite G] in
theorem dihedral_aux {x u a : G} (hx : x * x = 1) (hxa : x * a = a⁻¹ * x)
    (hua : u * a = a⁻¹ * u) : x * (a * a * (x * u)) = a⁻¹ * u * a := by
  calc x * (a * a * (x * u)) = (x * a) * (a * (x * u)) := by group
    _ = (a⁻¹ * x) * (a * (x * u)) := by rw [hxa]
    _ = a⁻¹ * ((x * a) * (x * u)) := by group
    _ = a⁻¹ * ((a⁻¹ * x) * (x * u)) := by rw [hxa]
    _ = a⁻¹ * (a⁻¹ * ((x * x) * u)) := by group
    _ = a⁻¹ * (a⁻¹ * u) := by rw [hx, one_mul]
    _ = a⁻¹ * (u * a) := by rw [hua]
    _ = a⁻¹ * u * a := by group

omit [Finite G] in
theorem mul_pow_two_mul_add_one {x u r : G} (hr : r = x * u) (hx : x * x = 1)
    (hxr : x * r * x⁻¹ = r⁻¹) (hur : u * r * u⁻¹ = r⁻¹) (j : ℕ) :
    x * r ^ (2 * j + 1) = (r ^ j)⁻¹ * u * r ^ j := by
  have h2 : r ^ (2 * j + 1) = r ^ j * r ^ j * (x * u) := by
    rw [pow_succ, two_mul, pow_add, ← hr]
  rw [h2]
  exact dihedral_aux hx (mul_pow_eq_inv_pow_mul hxr j) (mul_pow_eq_inv_pow_mul hur j)

theorem le_normalizer_of_ti (X E N : Subgroup G) (hEX : E ≤ X) (hNE : N ≤ E)
    (hNX : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hTI : ∀ g ∈ X, ∀ e ∈ E, e ∉ N → g * e * g⁻¹ ∈ E → g ∈ normalizer (E : Set G))
    {x f : G} (hxE : x ∈ E) (hxN : x ∉ N) (hfE : f ∈ E) (hfN : f ∉ N)
    (hfusx : ∀ g ∈ X, g * x * g⁻¹ ∈ normalizer (E : Set G) → g * x * g⁻¹ ∈ E)
    (hfusf : ∀ g ∈ X, g * f * g⁻¹ ∈ normalizer (E : Set G) → g * f * g⁻¹ ∈ E)
    (hsat : ∀ n ∈ N, ∃ y ∈ X ⊓ normalizer (E : Set G), y * x * y⁻¹ = x * n)
    (hdist : ∀ y ∈ X ⊓ normalizer (E : Set G), y * x * y⁻¹ ≠ f) :
    X ≤ normalizer (E : Set G) := by
  clear hEc
  by_contra hXN
  have hx2 : x * x = 1 := hE2 x hxE
  have hf2 : f * f = 1 := hE2 f hfE
  have hxX : x ∈ X := hEX hxE
  obtain ⟨g, hgX, hug⟩ : ∃ g ∈ X, g * f * g⁻¹ ∉ normalizer (E : Set G) := by
    by_contra hall
    refine hXN fun g hg => hTI g hg f hfE hfN (hfusf g hg ?_)
    by_contra h
    exact hall ⟨g, hg, h⟩
  obtain ⟨u, hu⟩ : ∃ u : G, u = g * f * g⁻¹ := ⟨_, rfl⟩
  rw [← hu] at hug
  have hu2 : u * u = 1 := by
    rw [hu]
    calc g * f * g⁻¹ * (g * f * g⁻¹) = g * (f * f) * g⁻¹ := by group
      _ = 1 := by rw [hf2]; group
  have huX : u ∈ X := by
    rw [hu]
    exact X.mul_mem (X.mul_mem hgX (hEX hfE)) (X.inv_mem hgX)
  have hfu : f = g⁻¹ * u * g := by rw [hu]; group
  obtain ⟨r, hr⟩ : ∃ r : G, r = x * u := ⟨_, rfl⟩
  have hrX : r ∈ X := by
    rw [hr]
    exact X.mul_mem hxX huX
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hxr1 : x * r = u := by rw [hr, ← mul_assoc, hx2, one_mul]
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    rw [hxr1, hr, mul_inv_rev, hu', hx']
  have hur : u * r * u⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hu', hx']
    calc u * (x * u) * u = u * x * (u * u) := by group
      _ = u * x := by rw [hu2, mul_one]
  have hxp := mul_pow_eq_inv_pow_mul hxr
  have hup := mul_pow_eq_inv_pow_mul hur
  have hxe := mul_pow_two_mul hxr
  have hxo := mul_pow_two_mul_add_one hr hx2 hxr hur
  have hex : ∃ m : ℕ, 0 < m ∧ r ^ m ∈ N :=
    ⟨orderOf r, orderOf_pos r, by rw [pow_orderOf_eq_one]; exact N.one_mem⟩
  classical
  obtain ⟨m, ⟨hm0, hmN⟩, hmin⟩ : ∃ m : ℕ, (0 < m ∧ r ^ m ∈ N) ∧ ∀ i < m, ¬ (0 < i ∧ r ^ i ∈ N) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  rcases Nat.even_or_odd' m with ⟨s, hs | hs⟩
  ·
    have hs0 : 0 < s := by omega
    have hws : r ^ s ∉ N := fun h => hmin s (by omega) ⟨hs0, h⟩
    have hww : r ^ s * r ^ s ∈ N := by
      rw [← pow_add, ← two_mul, ← hs]
      exact hmN
    have hwX : r ^ s ∈ X := pow_mem hrX s
    have hb2 : (x * r ^ s) * (x * r ^ s) = 1 := by
      calc (x * r ^ s) * (x * r ^ s) = ((r ^ s)⁻¹ * x) * (x * r ^ s) := by rw [hxp s]
        _ = (r ^ s)⁻¹ * (x * x) * r ^ s := by group
        _ = 1 := by rw [hx2]; group
    have hbX : x * r ^ s ∈ X := X.mul_mem hxX hwX
    have hbxb : (x * r ^ s) * x * (x * r ^ s)⁻¹ = x * (r ^ s * r ^ s) := by
      rw [inv_eq_of_mul_eq_one_right hb2]
      calc (x * r ^ s) * x * (x * r ^ s) = x * r ^ s * (x * x) * r ^ s := by group
        _ = x * (r ^ s * r ^ s) := by rw [hx2]; group
    have hbn : x * r ^ s ∈ normalizer (E : Set G) :=
      hTI _ hbX x hxE hxN (by rw [hbxb]; exact E.mul_mem hxE (hNE hww))
    have hbE : x * r ^ s ∈ E := by
      rcases Nat.even_or_odd' s with ⟨j, hj | hj⟩
      · have hjX : (r ^ j)⁻¹ ∈ X := X.inv_mem (pow_mem hrX j)
        have hbeq : x * r ^ s = (r ^ j)⁻¹ * x * ((r ^ j)⁻¹)⁻¹ := by
          rw [hj, hxe j, inv_inv]
        have := hfusx _ hjX (by rw [← hbeq]; exact hbn)
        rwa [← hbeq] at this
      · have hjX : (r ^ j)⁻¹ * g ∈ X := X.mul_mem (X.inv_mem (pow_mem hrX j)) hgX
        have hbeq : x * r ^ s = (r ^ j)⁻¹ * g * f * ((r ^ j)⁻¹ * g)⁻¹ := by
          rw [hj, hxo j, hu]
          group
        have := hfusf _ hjX (by rw [← hbeq]; exact hbn)
        rwa [← hbeq] at this
    have hwE : r ^ s ∈ E := by
      have : r ^ s = x * (x * r ^ s) := by rw [← mul_assoc, hx2, one_mul]
      rw [this]
      exact E.mul_mem hxE hbE
    have huw : u * r ^ s * u⁻¹ = (r ^ s)⁻¹ := by
      rw [hup s, mul_inv_cancel_right]
    exact hug (hTI u huX _ hwE hws (by rw [huw]; exact E.inv_mem hwE))
  ·
    obtain ⟨a, ha⟩ : ∃ a : G, a = r ^ (s + 1) := ⟨_, rfl⟩
    have haX : a ∈ X := by
      rw [ha]
      exact pow_mem hrX _
    have h1 : u * r ^ m = x * r ^ (2 * (s + 1)) := by
      have : 2 * (s + 1) = m + 1 := by omega
      rw [this, pow_succ', ← mul_assoc, hxr1]
    have hdih : a⁻¹ * x * a = u * r ^ m := by
      rw [h1, hxe (s + 1), ha]
    have hn'' : a * (r ^ m)⁻¹ * a⁻¹ ∈ N := hNX a haX _ (N.inv_mem hmN)
    have hu_eq : u = a⁻¹ * (x * (a * (r ^ m)⁻¹ * a⁻¹)) * a := by
      calc u = u * r ^ m * (r ^ m)⁻¹ := by group
        _ = a⁻¹ * x * a * (r ^ m)⁻¹ := by rw [← hdih]
        _ = a⁻¹ * (x * (a * (r ^ m)⁻¹ * a⁻¹)) * a := by group
    obtain ⟨y, ⟨hyX, -⟩, hyx⟩ := hsat _ hn''
    have hhX : g⁻¹ * a⁻¹ * y ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hgX) (X.inv_mem haX)) hyX
    have hh : g⁻¹ * a⁻¹ * y * x * (g⁻¹ * a⁻¹ * y)⁻¹ = f := by
      calc g⁻¹ * a⁻¹ * y * x * (g⁻¹ * a⁻¹ * y)⁻¹ = g⁻¹ * a⁻¹ * (y * x * y⁻¹) * a * g := by group
        _ = g⁻¹ * (a⁻¹ * (x * (a * (r ^ m)⁻¹ * a⁻¹)) * a) * g := by rw [hyx]; group
        _ = g⁻¹ * u * g := by rw [← hu_eq]
        _ = f := hfu.symm
    have hhn : g⁻¹ * a⁻¹ * y ∈ normalizer (E : Set G) :=
      hTI _ hhX x hxE hxN (by rw [hh]; exact hfE)
    exact hdist _ ⟨hhX, hhn⟩ hh

end CFSG.GroupTheory.TIFusion

end
