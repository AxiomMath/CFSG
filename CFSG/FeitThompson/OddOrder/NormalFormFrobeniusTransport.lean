module

public import CFSG.FeitThompson.OddOrder.ShortWordRigidity
import CFSG.FeitThompson.OddOrder.NormalFormWordCoordinates

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Multiplicative Subgroup

variable {G : Type*} [Group G] {p q : ℕ} {F : Type*} [Field F]

theorem mul_mul_eq_of_eq_mul_of_coord_eq (Pe : Multiplicative F →* G)
    (Ue : normOneUnits F →* G)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w)⁻¹ * Pe (ofAdd z) * Ue w = Pe (ofAdd (z * ((w : Fˣ) : F))))
    {i k : ℤ} {b u v : normOneUnits F} {c : F} (hb : b = u * v)
    (hc : c = (i : F) * ((u : Fˣ) : F) - (k : F) / ((v : Fˣ) : F)) :
    Pe (ofAdd (1 : F)) ^ i * Ue b * Pe (ofAdd (1 : F)) ^ (-k) =
      Ue u * Pe (ofAdd c) * Ue v := by
  have hα : ((u : Fˣ) : F) ≠ 0 := (u : Fˣ).ne_zero
  have hγ : ((v : Fˣ) : F) ≠ 0 := (v : Fˣ).ne_zero
  subst hb
  have hrhs : Ue u * Pe (ofAdd c) * Ue v
      = Pe (ofAdd (c * ((u : Fˣ) : F)⁻¹)) * Ue (u * v) := by
    have h := conj_apply_ofAdd_of_act Pe (fun z => hact z u) c
    rw [map_mul Ue]
    calc Ue u * Pe (ofAdd c) * Ue v
        = (Ue u * Pe (ofAdd c) * (Ue u)⁻¹) * (Ue u * Ue v) := by group
      _ = Pe (ofAdd (c * ((u : Fˣ) : F)⁻¹)) * (Ue u * Ue v) := by rw [h]
  have hβ : (((u * v : normOneUnits F) : Fˣ) : F) = ((u : Fˣ) : F) * ((v : Fˣ) : F) := by simp
  have hcoord : ((i : ℤ) : F) + ((-k : ℤ) : F) * (((u * v : normOneUnits F) : Fˣ) : F)⁻¹
      = c * ((u : Fˣ) : F)⁻¹ := by
    rw [hβ, hc]; push_cast; field_simp; ring
  rw [apply_ofAdd_one_zpow, apply_ofAdd_one_zpow,
    apply_ofAdd_mul_mul_apply_ofAdd Pe (fun z => hact z (u * v)), hrhs, hcoord]

theorem coord_eq_pow_of_coord_eq (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    {i k : ℤ} {c α γ : F} (hc : c ∈ (⊥ : Subfield F))
    (hcoord : c = (i : F) * α - (k : F) / γ) :
    c = (i : F) * α ^ p - (k : F) / γ ^ p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite F := finite_of_natCard_eq_prime_pow hp hcard
  have : CharP F p := charP_of_natCard_eq_prime_pow hp hcard
  have hcp : c ^ p = c := (Subfield.mem_bot_iff_pow_eq_self F p).1 hc
  have hi : ((i : F)) ^ p = (i : F) :=
    (Subfield.mem_bot_iff_pow_eq_self F p).1 (Subfield.intCast_mem _ i)
  have hk : ((k : F)) ^ p = (k : F) :=
    (Subfield.mem_bot_iff_pow_eq_self F p).1 (Subfield.intCast_mem _ k)
  calc c = c ^ p := hcp.symm
    _ = ((i : F) * α - (k : F) / γ) ^ p := by rw [hcoord]
    _ = ((i : F) * α) ^ p - ((k : F) / γ) ^ p := sub_pow_char _ _
    _ = (i : F) * α ^ p - (k : F) / γ ^ p := by rw [mul_pow, div_pow, hi, hk]

theorem mul_pow_mul_eq_of_mul_mul_eq_range (hp : p.Prime) (hcard : Nat.card F = p ^ q)
    (Pe : Multiplicative F →* G) (hPe : Function.Injective Pe)
    (Ue : normOneUnits F →* G) (hdisj : Disjoint Pe.range Ue.range)
    (hact : ∀ (z : F) (w : normOneUnits F),
      (Ue w)⁻¹ * Pe (ofAdd z) * Ue w = Pe (ofAdd (z * ((w : Fˣ) : F))))
    {i k : ℤ} {b u v : normOneUnits F} {c : F} (hc : c ∈ (⊥ : Subfield F))
    (heq : Pe (ofAdd (1 : F)) ^ i * Ue b * Pe (ofAdd (1 : F)) ^ (-k) =
      Ue u * Pe (ofAdd c) * Ue v) :
    Pe (ofAdd (1 : F)) ^ i * Ue b ^ p * Pe (ofAdd (1 : F)) ^ (-k) =
      Ue u ^ p * Pe (ofAdd c) * Ue v ^ p := by
  obtain ⟨hb, hcoord⟩ := eq_mul_and_coord_eq_of_mul_mul_eq_range Pe hPe Ue hdisj hact heq
  have key : Pe (ofAdd (1 : F)) ^ i * Ue (b ^ p) * Pe (ofAdd (1 : F)) ^ (-k) =
      Ue (u ^ p) * Pe (ofAdd c) * Ue (v ^ p) := by
    refine mul_mul_eq_of_eq_mul_of_coord_eq Pe Ue hact (by rw [hb, mul_pow]) ?_
    simpa using coord_eq_pow_of_coord_eq hp hcard hc hcoord
  simpa only [map_pow] using key

theorem mul_pow_mul_eq_of_mul_mul_eq (hp : p.Prime) (_hq : q.Prime) (_hqp : q < p)
    (hcard : Nat.card F = p ^ q)
    (_hcop : Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1)) {P U : Subgroup G}
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
    {i j k : ℤ} {a u v : normOneUnits F} {c : F} (hc : c ∈ (⊥ : Subfield F))
    (heq : s ^ i * ((t ^ j)⁻¹ * (Ue a : G) * t ^ j) * s ^ (-k)
      = (Ue u : G) * (Pe (ofAdd c) : G) * (Ue v : G)) :
    s ^ i * ((t ^ j)⁻¹ * (Ue a : G) ^ p * t ^ j) * s ^ (-k)
      = (Ue u : G) ^ p * (Pe (ofAdd c) : G) * (Ue v : G) ^ p := by
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
  have key := mul_pow_mul_eq_of_mul_mul_eq_range hp hcard Pe' hPeinj Ue' hdisj hact' hc heq'
  have hbp : (t ^ j)⁻¹ * (Ue a : G) ^ p * t ^ j = Ue' b ^ p := by
    rw [hb]
    simpa using (conj_pow (a := (t ^ j)⁻¹) (b := (Ue a : G)) (i := p)).symm
  rw [hs, hbp]
  simp only [hPev, hUev] at key ⊢
  exact key

end

end CFSG.FeitThompson
