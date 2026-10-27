module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRNorm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartNormalizer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E} (hc : U3RootCoords T₁ σ u v)
include hc

theorem exists_norm_one [Finite E] [CharP E 2] {μ : E} (hμ : σ μ ≠ μ) {x : G}
    (hxT : x ∈ normalizer (T₁ : Set G)) (hxA : ∀ y ∈ T₁, u y = 0 → x * y * x⁻¹ = y) :
    ∃ l : E, l * σ l = 1 ∧ ((∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) ∨
      (∀ y ∈ T₁, u (x * y * x⁻¹) = l * σ (u y))) := by
  have hconjT : ∀ y ∈ T₁, x * y * x⁻¹ ∈ T₁ := fun y hy => (mem_normalizer_iff.mp hxT y).mp hy
  obtain ⟨φ, hφ⟩ := hc.exists_addEquiv_conj hxT (fun y hy hu => by rw [hxA y hy hu, hu])
    (fun y hy hu => by
      have h1 := hxA _ (hconjT y hy) hu
      have h2 : y = x * y * x⁻¹ := by
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = x⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * x := by rw [h1]
          _ = x * y * x⁻¹ := by group
      rw [h2]
      exact hu)
  have hN : ∀ a, φ a * σ (φ a) = a * σ a := by
    intro a
    obtain ⟨y, hyT, rfl⟩ := hc.u_surj a
    obtain ⟨hy2u, hy2v⟩ := hc.sq hyT
    obtain ⟨-, hz2v⟩ := hc.sq (hconjT y hyT)
    rw [← hφ y hyT, ← hz2v, ← hy2v]
    congr 1
    calc (x * y * x⁻¹) ^ 2 = x * y ^ 2 * x⁻¹ := by rw [pow_two, pow_two]; group
      _ = y ^ 2 := hxA _ (pow_mem hyT 2) hy2u
  obtain ⟨l, hl, hlφ | hlφ⟩ := eq_mul_or_eq_mul_sigma_of_norm σ hμ φ.toAddMonoidHom
    φ.surjective hN
  · exact ⟨l, hl, Or.inl fun y hy => by rw [hφ y hy]; exact hlφ _⟩
  · exact ⟨l, hl, Or.inr fun y hy => by rw [hφ y hy]; exact hlφ _⟩

omit hc in
theorem u_conj_pow {x : G} (hxT : x ∈ normalizer (T₁ : Set G)) {l : E}
    (hx : ∀ y ∈ T₁, u (x * y * x⁻¹) = l * u y) (k : ℕ) :
    ∀ y ∈ T₁, u (x ^ k * y * (x ^ k)⁻¹) = l ^ k * u y := by
  induction k with
  | zero => intro y hy; simp
  | succ k ih =>
    intro y hy
    have hxk : x ^ k * y * (x ^ k)⁻¹ ∈ T₁ := (mem_normalizer_iff.mp (pow_mem hxT k) y).mp hy
    have e : x ^ (k + 1) * y * (x ^ (k + 1))⁻¹ = x * (x ^ k * y * (x ^ k)⁻¹) * x⁻¹ := by
      rw [pow_succ']
      group
    rw [e, hx _ hxk, ih y hy, pow_succ']
    ring

end U3RootCoords

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_rootCoords_scalar_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
      Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
      Nat.card {x : E // σ x = x} = 2 ^ f ∧
      ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
        (∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) ∧
        (∀ x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
          ∃ l : E, l * σ l = 1 ∧ ((∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) ∨
            (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * σ (u y)))) ∧
        ∀ x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
          Odd (orderOf x) → ∃ l : E, l * σ l = 1 ∧ ∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y := by
  obtain ⟨E, hE, hF, hch, σ, hEcard, hσ, hfix, u, v, hc, hA₁u⟩ :=
    h.exists_rootCoords_of_card_sylow hS2
  have hNT₁ := h.normalizer_szA_le_of_card_sylow hS2
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨μ, hμ⟩ : ∃ μ : E, σ μ ≠ μ := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card {x : E // σ x = x} = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hfix, hEcard] at h1
    have h2 : 2 ^ f < (2 ^ f) ^ 2 := by
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := h.two_le; omega)
      nlinarith
    omega
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul, ← sq]
    have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hEcard] at h1
  have key : ∀ x ∈ normalizer (szA L T t : Set G) ⊓ centralizer (szA₁ (szT₁ L T) : Set G),
      ∃ l : E, l * σ l = 1 ∧ ((∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * u y) ∨
        (∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = l * σ (u y))) := by
    intro x hx
    obtain ⟨hxN, hxC⟩ := mem_inf.mp hx
    refine hc.exists_norm_one hμ (hNT₁ hxN) fun y hy hu => ?_
    have hyA : y ∈ szA₁ (szT₁ L T) := (hA₁u y hy).mpr hu
    rw [(mem_centralizer_iff.mp hxC y hyA).symm, mul_inv_cancel_right]
  refine ⟨E, hE, hF, hch, σ, hEcard, hσ, hfix, u, v, hc, hA₁u, key, fun x hx hodd => ?_⟩
  obtain ⟨l, hl, hlx | hlx⟩ := key x hx
  · exact ⟨l, hl, hlx⟩
  refine ⟨1, by rw [map_one, mul_one], fun y hy => ?_⟩
  have hxT := hNT₁ (mem_inf.mp hx).1
  have hconjT : ∀ z ∈ szT₁ L T, x * z * x⁻¹ ∈ szT₁ L T := fun z hz =>
    (mem_normalizer_iff.mp hxT z).mp hz
  have hsq : ∀ z ∈ szT₁ L T, u (x ^ 2 * z * (x ^ 2)⁻¹) = u z := by
    intro z hz
    have e : x ^ 2 * z * (x ^ 2)⁻¹ = x * (x * z * x⁻¹) * x⁻¹ := by rw [sq]; group
    rw [e, hlx _ (hconjT z hz), hlx z hz, map_mul, hσσ, ← mul_assoc, hl, one_mul]
  have hx2 : ∀ z ∈ szT₁ L T, u (x ^ 2 * z * (x ^ 2)⁻¹) = 1 * u z := fun z hz => by
    rw [one_mul, hsq z hz]
  obtain ⟨m, hm⟩ := hodd
  have hxm : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hxm, U3RootCoords.u_conj_pow (pow_mem hxT 2) hx2 (m + 1) y hy, one_pow]

end U3Start

end CFSG.SeitzReduction.RankOne
