module

public import CFSG.FeitThompson.OddOrder.ShortWordRigidity

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {F : Type*} [Field F]

theorem injective_of_act (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    (Ue : normOneUnits F →* G)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w)⁻¹ * Pe (ofAdd z) * Ue w = Pe (ofAdd (z * ((w : Fˣ) : F)))) :
    Function.Injective Ue := by
  intro w w' h
  have h1 := hact 1 w
  have h2 := hact 1 w'
  rw [h, h2] at h1
  have hv : ((w' : Fˣ) : F) = ((w : Fˣ) : F) := by simpa using hPe h1
  exact (Subtype.ext (Units.ext hv)).symm

theorem eq_and_eq_of_mul_eq_mul (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    (Ue : normOneUnits F →* G) (hdisj : Disjoint Pe.range Ue.range)
    {x y : F} {w w' : normOneUnits F}
    (h : Pe (ofAdd x) * Ue w = Pe (ofAdd y) * Ue w') : x = y ∧ Ue w = Ue w' := by
  have hxy : Pe (ofAdd (x - y)) = Ue (w' * w⁻¹) := by
    have e : Pe (ofAdd (x - y)) = (Pe (ofAdd y))⁻¹ * Pe (ofAdd x) := by
      rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub]
    rw [map_mul Ue, map_inv]
    calc Pe (ofAdd (x - y))
        = (Pe (ofAdd y))⁻¹ * (Pe (ofAdd x) * Ue w) * (Ue w)⁻¹ := by rw [e]; group
      _ = (Pe (ofAdd y))⁻¹ * (Pe (ofAdd y) * Ue w') * (Ue w)⁻¹ := by rw [h]
      _ = Ue w' * (Ue w)⁻¹ := by group
  have h0 : Pe (ofAdd (x - y)) = 1 :=
    Subgroup.disjoint_def.mp hdisj ⟨ofAdd (x - y), rfl⟩ ⟨w' * w⁻¹, hxy.symm⟩
  have hx : x = y := by
    have h1 : Pe (ofAdd (x - y)) = Pe (ofAdd (0 : F)) := by rw [h0, ofAdd_zero, map_one]
    exact sub_eq_zero.mp (ofAdd.injective (hPe h1))
  refine ⟨hx, ?_⟩
  rw [hx] at h
  exact mul_left_cancel h

theorem apply_ofAdd_one_zpow (Pe : Multiplicative F →* G) (i : ℤ) :
    Pe (ofAdd (1 : F)) ^ i = Pe (ofAdd ((i : F))) := by
  rw [← map_zpow, ← ofAdd_zsmul]; simp

theorem apply_ofAdd_one_zpow_mem_primeLine (Pe : Multiplicative F →* G) (i : ℤ) :
    Pe (ofAdd (1 : F)) ^ i ∈ primeLine Pe := by
  rw [apply_ofAdd_one_zpow]
  exact apply_ofAdd_mem_primeLine Pe (Subfield.intCast_mem _ i)

theorem eq_mul_and_coord_eq_of_mul_mul_eq_range
    (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    (Ue : normOneUnits F →* G) (hdisj : Disjoint Pe.range Ue.range)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w)⁻¹ * Pe (ofAdd z) * Ue w = Pe (ofAdd (z * ((w : Fˣ) : F))))
    {i k : ℤ} {b u v : normOneUnits F} {c : F}
    (heq : Pe (ofAdd (1 : F)) ^ i * Ue b * Pe (ofAdd (1 : F)) ^ (-k) =
      Ue u * Pe (ofAdd c) * Ue v) :
    b = u * v ∧ c = (i : F) * ((u : Fˣ) : F) - (k : F) / ((v : Fˣ) : F) := by
  have hα : ((u : Fˣ) : F) ≠ 0 := (u : Fˣ).ne_zero
  have hγ : ((v : Fˣ) : F) ≠ 0 := (v : Fˣ).ne_zero
  rw [apply_ofAdd_one_zpow, apply_ofAdd_one_zpow,
    apply_ofAdd_mul_mul_apply_ofAdd Pe (fun z => hact z b)] at heq
  have hrhs : Ue u * Pe (ofAdd c) * Ue v
      = Pe (ofAdd (c * ((u : Fˣ) : F)⁻¹)) * Ue (u * v) := by
    have h := conj_apply_ofAdd_of_act Pe (fun z => hact z u) c
    rw [map_mul Ue]
    calc Ue u * Pe (ofAdd c) * Ue v
        = (Ue u * Pe (ofAdd c) * (Ue u)⁻¹) * (Ue u * Ue v) := by group
      _ = Pe (ofAdd (c * ((u : Fˣ) : F)⁻¹)) * (Ue u * Ue v) := by rw [h]
  rw [hrhs] at heq
  obtain ⟨hcoord, hU⟩ := eq_and_eq_of_mul_eq_mul Pe hPe Ue hdisj heq
  have hb : b = u * v := injective_of_act Pe hPe Ue hact hU
  refine ⟨hb, ?_⟩
  rw [hb] at hcoord
  have hβ : (((u * v : normOneUnits F) : Fˣ) : F) = ((u : Fˣ) : F) * ((v : Fˣ) : F) := by simp
  rw [hβ] at hcoord
  push_cast at hcoord
  field_simp at hcoord ⊢
  linear_combination -hcoord

theorem apply_ofAdd_ne_one_of_mul_mul_eq_range (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1))
    (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    (Ue : normOneUnits F →* G) (hdisj : Disjoint Pe.range Ue.range)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w)⁻¹ * Pe (ofAdd z) * Ue w = Pe (ofAdd (z * ((w : Fˣ) : F))))
    {i k : ℤ} {b u v : normOneUnits F} {c : F}
    (heq : Pe (ofAdd (1 : F)) ^ i * Ue b * Pe (ofAdd (1 : F)) ^ (-k) =
      Ue u * Pe (ofAdd c) * Ue v)
    (hik : ¬ (i ≡ k [ZMOD (p : ℤ)])) : Pe (ofAdd c) ≠ 1 := by
  intro hr
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  rw [hr, mul_one, apply_ofAdd_one_zpow, apply_ofAdd_one_zpow] at heq
  have hmem : Pe (ofAdd ((i : F))) * Ue b * Pe (ofAdd (((-k : ℤ) : F))) ∈ Ue.range := by
    rw [heq, ← map_mul]; exact ⟨u * v, rfl⟩
  have key := eq_one_of_mul_mul_mem_range hp hcard hcop Pe hPe Ue hdisj hact
    (c₁ := ((i : ℤ) : F)) (c₂ := ((-k : ℤ) : F))
    (Subfield.intCast_mem _ i) (Subfield.intCast_mem _ (-k)) hmem
  have hprod : Pe (ofAdd (((i - k : ℤ) : F))) = 1 := by
    have e : Pe (ofAdd (((i - k : ℤ) : F)))
        = Pe (ofAdd ((i : ℤ) : F)) * Pe (ofAdd ((-k : ℤ) : F)) := by
      rw [← map_mul, ← ofAdd_add]; push_cast; ring_nf
    rw [e]
    rcases key with ⟨h1, h2⟩ | ⟨-, h2⟩
    · rw [h1, h2, one_mul]
    · exact h2
  have hzero : ((i - k : ℤ) : F) = 0 := by
    have h1 : Pe (ofAdd (((i - k : ℤ) : F))) = Pe (ofAdd (0 : F)) := by
      rw [hprod, ofAdd_zero, map_one]
    exact ofAdd.injective (hPe h1)
  exact hik (Int.ModEq.symm (Int.modEq_iff_dvd.2 ((CharP.intCast_eq_zero_iff F p _).1 hzero)))

theorem coord_eq_and_apply_ofAdd_ne_one_of_mul_mul_eq (hp : p.Prime) (_hq : q.Prime) (_hqp : q < p)
    (hcard : Nat.card F = p ^ q)
    (hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) {P U : Subgroup G}
    (Pe : Multiplicative F ≃* P) (Ue : normOneUnits F ≃* U) (hPU : P ⊓ U = ⊥)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w : G)⁻¹ * (Pe (ofAdd z) : G) * (Ue w : G) = (Pe (ofAdd (z * ((w : Fˣ) : F))) : G))
    {H P₀ P₁ Q : Subgroup G} (_hH : H = P ⊔ U)
    (hP₀ : P₀ = primeLine (P.subtype.comp Pe.toMonoidHom))
    {s t y : G} (hs : s = (Pe (ofAdd (1 : F)) : G))
    (_hQab : ∀ x ∈ Q, ∀ z ∈ Q, x * z = z * x) (_hQp : Nat.Coprime (Nat.card Q) p)
    (_hQnorm : P₀ ≤ normalizer (Q : Set G)) (_hy : y ∈ Q)
    (hP₁ : P₁ = P₀.map (MulAut.conj y⁻¹).toMonoidHom) (hP₁U : P₁ ≤ normalizer (U : Set G))
    (ht : t = y⁻¹ * s * y)
    {i j k : ℤ} {a u v : normOneUnits F} {c : F} (_hc : c ∈ (⊥ : Subfield F))
    (heq : s ^ i * ((t ^ j)⁻¹ * (Ue a : G) * t ^ j) * s ^ (-k)
      = (Ue u : G) * (Pe (ofAdd c) : G) * (Ue v : G)) :
    (t ^ j)⁻¹ * (Ue a : G) * t ^ j = (Ue u : G) * (Ue v : G) ∧
      c = (i : F) * ((u : Fˣ) : F) - (k : F) / ((v : Fˣ) : F) ∧
      (¬ (i ≡ k [ZMOD (p : ℤ)]) → (Pe (ofAdd c) : G) ≠ 1) := by
  obtain ⟨Pe', hPev⟩ : ∃ f : Multiplicative F →* G, ∀ z, f z = (Pe z : G) :=
    ⟨P.subtype.comp Pe.toMonoidHom, fun _ => rfl⟩
  obtain ⟨Ue', hUev⟩ : ∃ f : normOneUnits F →* G, ∀ w, f w = (Ue w : G) :=
    ⟨U.subtype.comp Ue.toMonoidHom, fun _ => rfl⟩
  have hPrange : Pe'.range = P := by
    ext x
    refine ⟨fun ⟨w, hw⟩ => hw ▸ (hPev w ▸ (Pe w).2), fun hx => ⟨Pe.symm ⟨x, hx⟩, ?_⟩⟩
    rw [hPev]; simp
  have hUrange : Ue'.range = U := by
    ext x
    refine ⟨fun ⟨w, hw⟩ => hw ▸ (hUev w ▸ (Ue w).2), fun hx => ⟨Ue.symm ⟨x, hx⟩, ?_⟩⟩
    rw [hUev]; simp
  have hPeinj : Function.Injective Pe' := by
    intro z z' h
    rw [hPev, hPev] at h
    exact Pe.injective (Subtype.ext h)
  have hdisj : Disjoint Pe'.range Ue'.range := by
    rw [hPrange, hUrange, disjoint_iff]; exact hPU
  have hact' : ∀ (z : F) (w : normOneUnits F),
      (Ue' w)⁻¹ * Pe' (ofAdd z) * Ue' w = Pe' (ofAdd (z * ((w : Fˣ) : F))) := by
    intro z w; rw [hUev, hPev, hPev]; exact hact z w
  have hsP₀ : s ∈ P₀ := by
    rw [hP₀, hs]; exact apply_ofAdd_mem_primeLine _ (one_mem _)
  have htP₁ : t ∈ P₁ := by
    rw [hP₁, ht]; exact ⟨s, hsP₀, by simp [MulAut.conj]⟩
  have htjn : t ^ j ∈ normalizer (U : Set G) := zpow_mem (hP₁U htP₁) j
  have hmemU : (t ^ j)⁻¹ * (Ue a : G) * t ^ j ∈ Ue'.range := by
    rw [hUrange]
    exact ((Subgroup.mem_normalizer_iff'' (H := U) (g := t ^ j)).1 htjn _).1 (Ue a).2
  obtain ⟨b, hb⟩ := hmemU
  have heq' : Pe' (ofAdd (1 : F)) ^ i * Ue' b * Pe' (ofAdd (1 : F)) ^ (-k)
      = Ue' u * Pe' (ofAdd c) * Ue' v := by
    rw [hb, hPev, hUev, hUev, hPev, ← hs]; exact heq
  obtain ⟨hbuv, hcoord⟩ :=
    eq_mul_and_coord_eq_of_mul_mul_eq_range Pe' hPeinj Ue' hdisj hact' heq'
  refine ⟨?_, hcoord, fun hik => ?_⟩
  · rw [← hb, hbuv, map_mul, hUev, hUev]
  · have h := apply_ofAdd_ne_one_of_mul_mul_eq_range hp hcard hcop Pe' hPeinj Ue' hdisj hact'
      heq' hik
    rwa [hPev] at h

end

end CFSG.FeitThompson
