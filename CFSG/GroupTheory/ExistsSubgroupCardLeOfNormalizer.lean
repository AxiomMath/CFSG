module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank

public section

namespace CFSG.GroupTheory

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem exists_subgroup_card_le_of_normalizer {K : Type} [Group K] [Finite K]
    (X : Subgroup K) [X.Normal] (hZ : Subgroup.center ↥X = ⊥) {s : ℕ}
    (hOut : ∀ E : Subgroup (Outer ↥X), (∀ e ∈ E, e * e = 1) → Nat.card ↥E ≤ 2 ^ s)
    (L : Subgroup K) (hL : ∀ e ∈ L, ∀ f ∈ L, e * f = f * e) (hL2 : ∀ e ∈ L, e * e = 1)
    {r : K} (hrX : r ∈ X) (hrL : r ∈ L) (T : Subgroup K) (hTX : T ≤ X)
    (hTL : ∀ t ∈ T, ∀ l ∈ L, t * l * t⁻¹ ∈ L) :
    ∃ A : Subgroup ↥X, (∀ e ∈ A, e * e = 1) ∧ (∀ e ∈ A, ∀ f ∈ A, e * f = f * e) ∧
      (⟨r, hrX⟩ : ↥X) ∈ A ∧ (∀ x ∈ A, (x : K) * r = r * x) ∧
      (∀ t : ↥X, (t : K) ∈ T → ∀ x ∈ A, t * x * t⁻¹ ∈ A) ∧
      Nat.card ↥L ≤ Nat.card ↥A * 2 ^ s * Nat.card ↥(L ⊓ Subgroup.centralizer (X : Set K)) := by
  classical
  have hinn := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥X
  have hc : Function.Injective (MulAut.conj : ↥X →* MulAut ↥X) :=
    CFSG.GH74.GLS.IVK.GHInv.conj_injective_of_center_eq_bot hZ
  let Φ : K →* MulAut ↥X := MulAut.conjNormal
  let π : MulAut ↥X →* Outer ↥X := QuotientGroup.mk' (inner ↥X)
  let ρ : ↥L →* Outer ↥X := (π.comp Φ).comp L.subtype
  let ψ : ↥ρ.ker →* MulAut ↥X := (Φ.comp L.subtype).comp ρ.ker.subtype
  have hΦX : ∀ x : ↥X, Φ (x : K) = MulAut.conj x := fun x => MulAut.conjNormal_val
  have himg : Nat.card ↥ρ.range ≤ 2 ^ s := by
    refine hOut ρ.range ?_
    rintro _ ⟨x, rfl⟩
    show ρ x * ρ x = 1
    rw [← map_mul]
    have h2 : x * x = 1 := Subtype.ext (hL2 x x.2)
    rw [h2, map_one]
  have hLcard : Nat.card ↥L = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker]
    exact congrArg (· * Nat.card ↥ρ.ker)
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv)
  have hker : Nat.card ↥ρ.ker = Nat.card ↥ψ.range * Nat.card ↥ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker]
    exact congrArg (· * Nat.card ↥ψ.ker)
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv)
  have hkerψ : Nat.card ↥ψ.ker ≤ Nat.card ↥(L ⊓ Subgroup.centralizer (X : Set K)) := by
    have hmem : ∀ l : ↥ψ.ker, ((l.1.1 : ↥L) : K) ∈ L ⊓ Subgroup.centralizer (X : Set K) := by
      intro l
      refine Subgroup.mem_inf.mpr ⟨l.1.1.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      have h1 := congrArg (fun φ : MulAut ↥X => (φ ⟨h, hh⟩ : K)) l.2
      simp only [ψ, MonoidHom.comp_apply, Subgroup.subtype_apply, Φ, MulAut.conjNormal_apply,
        MulAut.one_apply] at h1
      calc h * ((l.1.1 : ↥L) : K) = (((l.1.1 : ↥L) : K) * h * ((l.1.1 : ↥L) : K)⁻¹) *
            ((l.1.1 : ↥L) : K) := by rw [h1]
        _ = ((l.1.1 : ↥L) : K) * h := by group
    refine Nat.card_le_card_of_injective (fun l => ⟨((l.1.1 : ↥L) : K), hmem l⟩) ?_
    intro l l' h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Subtype.ext this))
  let A : Subgroup ↥X := ψ.range.comap (MulAut.conj : ↥X →* MulAut ↥X)
  have hAmem : ∀ x : ↥X, x ∈ A ↔ ∃ l : ↥ρ.ker, Φ (((l : ↥L) : K)) = MulAut.conj x := by
    intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨fun ⟨l, hl⟩ => ⟨l, hl⟩, fun ⟨l, hl⟩ => ⟨l, hl⟩⟩
  have hψinner : ψ.range ≤ (MulAut.conj : ↥X →* MulAut ↥X).range := by
    rintro _ ⟨l, rfl⟩
    have h1 : π (Φ (((l : ↥L) : K))) = 1 := l.2
    exact (QuotientGroup.eq_one_iff (N := inner ↥X) _).1 h1
  have hAcard : Nat.card ↥A = Nat.card ↥ψ.range := by
    have h1 : A.map (MulAut.conj : ↥X →* MulAut ↥X) = ψ.range := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hψinner
    rw [← h1]
    exact (Subgroup.card_map_of_injective hc).symm
  have hA2 : ∀ e ∈ A, e * e = 1 := by
    intro e he
    obtain ⟨l, hl⟩ := (hAmem e).1 he
    apply hc
    rw [map_mul, ← hl, ← map_mul, hL2 _ (l : ↥L).2, map_one, map_one]
  have hAc : ∀ e ∈ A, ∀ f ∈ A, e * f = f * e := by
    intro e he f hf
    obtain ⟨l, hl⟩ := (hAmem e).1 he
    obtain ⟨l', hl'⟩ := (hAmem f).1 hf
    apply hc
    rw [map_mul, map_mul, ← hl, ← hl', ← map_mul, ← map_mul,
      hL _ (l : ↥L).2 _ (l' : ↥L).2]
  have hrA : (⟨r, hrX⟩ : ↥X) ∈ A := by
    have hρ : ρ ⟨r, hrL⟩ = 1 := by
      show π (Φ r) = 1
      have : Φ r = MulAut.conj (⟨r, hrX⟩ : ↥X) := hΦX ⟨r, hrX⟩
      rw [this]
      exact (QuotientGroup.eq_one_iff (N := inner ↥X) _).2 ⟨_, rfl⟩
    exact (hAmem _).2 ⟨⟨⟨r, hrL⟩, hρ⟩, hΦX ⟨r, hrX⟩⟩
  have hAr : ∀ x ∈ A, (x : K) * r = r * x := by
    intro x hx
    obtain ⟨l, hl⟩ := (hAmem x).1 hx
    have h1 := congrArg (fun φ : MulAut ↥X => (φ ⟨r, hrX⟩ : K)) hl
    simp only [Φ, MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    have h2 : ((l : ↥L) : K) * r * ((l : ↥L) : K)⁻¹ = r := by
      rw [hL _ (l : ↥L).2 _ hrL]
      group
    rw [h2] at h1
    calc (x : K) * r = ((x : K) * r * (x : K)⁻¹) * (x : K) := by group
      _ = r * x := by rw [← h1]
  have hAT : ∀ t : ↥X, (t : K) ∈ T → ∀ x ∈ A, t * x * t⁻¹ ∈ A := by
    intro t ht x hx
    obtain ⟨l, hl⟩ := (hAmem x).1 hx
    have hlt : (t : K) * ((l : ↥L) : K) * (t : K)⁻¹ ∈ L := hTL _ ht _ (l : ↥L).2
    have hρ : ρ ⟨(t : K) * ((l : ↥L) : K) * (t : K)⁻¹, hlt⟩ = 1 := by
      show π (Φ ((t : K) * ((l : ↥L) : K) * (t : K)⁻¹)) = 1
      have h1 : Φ ((t : K) * ((l : ↥L) : K) * (t : K)⁻¹) = MulAut.conj t * Φ (((l : ↥L) : K)) *
          (MulAut.conj t)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hΦX]
      rw [h1, hl, ← map_inv, ← map_mul, ← map_mul]
      exact (QuotientGroup.eq_one_iff (N := inner ↥X) _).2 ⟨_, rfl⟩
    refine (hAmem _).2 ⟨⟨⟨(t : K) * ((l : ↥L) : K) * (t : K)⁻¹, hlt⟩, hρ⟩, ?_⟩
    show Φ ((t : K) * ((l : ↥L) : K) * (t : K)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hΦX, hl, map_mul, map_mul, map_inv]
  refine ⟨A, hA2, hAc, hrA, hAr, hAT, ?_⟩
  calc Nat.card ↥L = Nat.card ↥ρ.range * Nat.card ↥ρ.ker := hLcard
    _ = Nat.card ↥ρ.range * (Nat.card ↥A * Nat.card ↥ψ.ker) := by rw [hker, hAcard]
    _ ≤ 2 ^ s * (Nat.card ↥A * Nat.card ↥(L ⊓ Subgroup.centralizer (X : Set K))) :=
        Nat.mul_le_mul himg (Nat.mul_le_mul_left _ hkerψ)
    _ = Nat.card ↥A * 2 ^ s * Nat.card ↥(L ⊓ Subgroup.centralizer (X : Set K)) := by ring

end CFSG.GroupTheory
