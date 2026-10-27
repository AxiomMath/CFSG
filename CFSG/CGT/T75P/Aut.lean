module

import CFSG.HardMathSupport.RichardWeiss.Proving.WCLocalBridge
public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T : Subgroup G} {n : ℕ}

theorem galoisField_two_one_eq (c : GaloisField 2 1) : c = 0 ∨ c = 1 :=
  CFSG.HardMathSupport.RichardWeiss.Proving.galoisField_two_one_eq_zero_or_one c

theorem exists_mem_conj_eq_of_natural {H : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (T : Set G)) (hnat : NaturalSL T H n 1) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ h ∈ H, ∀ t ∈ T, h * t * h⁻¹ = g * t * g⁻¹ := by
  classical
  obtain ⟨hN, e, φ, hcompat⟩ := hnat
  let A : MulAut ↥T := T.normalizerMonoidHom ⟨g, hg⟩
  have hA : ∀ t : ↥T, ((A t : ↥T) : G) = g * t * g⁻¹ := fun t => rfl
  let Ψ : Multiplicative (Fin n → GaloisField 2 1) ≃* Multiplicative (Fin n → GaloisField 2 1) :=
    φ.symm.trans (A.trans φ)
  have hΨ : ∀ t : ↥T, Ψ (φ t) = φ (A t) := fun t => by
    simp [Ψ]
  let ψ : (Fin n → GaloisField 2 1) →ₗ[GaloisField 2 1] (Fin n → GaloisField 2 1) :=
    { toFun := fun v => Multiplicative.toAdd (Ψ (Multiplicative.ofAdd v))
      map_add' := fun v w => by
        simp only [ofAdd_add, map_mul, toAdd_mul]
      map_smul' := fun c v => by
        rcases galoisField_two_one_eq c with rfl | rfl
        · simp
        · simp }
  set M : Matrix (Fin n) (Fin n) (GaloisField 2 1) := LinearMap.toMatrix' ψ with hMdef
  have hM : ∀ v, M *ᵥ v = Multiplicative.toAdd (Ψ (Multiplicative.ofAdd v)) := fun v => by
    rw [hMdef, LinearMap.toMatrix'_mulVec]
    rfl
  have hMinj : Function.Injective M.mulVec := by
    intro v w hvw
    have h1 : Multiplicative.toAdd (Ψ (Multiplicative.ofAdd v)) =
        Multiplicative.toAdd (Ψ (Multiplicative.ofAdd w)) := by
      rw [← hM v, ← hM w]
      exact hvw
    exact Multiplicative.ofAdd.injective (Ψ.injective (Multiplicative.toAdd.injective h1))
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.1 hMinj
  have hdet : M.det = 1 := by
    have h := (Matrix.isUnit_iff_isUnit_det M).1 hunit
    rcases galoisField_two_one_eq M.det with h0 | h1
    · rw [h0] at h
      exact absurd h not_isUnit_zero
    · exact h1
  let Msl : SL(n, GaloisField 2 1) := ⟨M, hdet⟩
  obtain ⟨q, hq⟩ := e.surjective Msl
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨(h : G), h.2, fun t ht => ?_⟩
  have hmem : (h : G) * t * (h : G)⁻¹ ∈ T := conj_mem_of_mem_normalizer (hHN h.2) ht
  have h1 := hcompat h ⟨t, ht⟩ hmem
  rw [hq] at h1
  have h2 : φ (A ⟨t, ht⟩) = Multiplicative.ofAdd (M *ᵥ Multiplicative.toAdd (φ ⟨t, ht⟩)) := by
    rw [hM, ofAdd_toAdd, ofAdd_toAdd, ← hΨ]
  have h3 : φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ = φ (A ⟨t, ht⟩) := h1.trans h2.symm
  have h4 := φ.injective h3
  exact congrArg Subtype.val h4

theorem inf_centralizer_eq_of_natural {H : Subgroup G} (hTH : T ≤ H)
    (hHN : H ≤ Subgroup.normalizer (T : Set G)) (hnat : NaturalSL T H n 1) :
    H ⊓ Subgroup.centralizer (T : Set G) = T := by
  classical
  have hnat' := hnat
  obtain ⟨hN, e, φ, hcompat⟩ := hnat'
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => by
    have h1 : φ ⟨a * b, T.mul_mem ha hb⟩ = φ ⟨b * a, T.mul_mem hb ha⟩ := by
      have : φ (⟨a, ha⟩ * ⟨b, hb⟩) = φ (⟨b, hb⟩ * ⟨a, ha⟩) := by
        rw [map_mul, map_mul]
        exact mul_comm _ _
      exact this
    exact congrArg Subtype.val (φ.injective h1)
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH, hxC⟩ := hx
    rw [Subgroup.mem_centralizer_iff] at hxC
    have hxT : (⟨x, hxH⟩ : ↥H) ∈ T.subgroupOf H := by
      rw [← QuotientGroup.eq_one_iff (N := T.subgroupOf H)]
      apply e.injective
      rw [map_one]
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      have hj : (Multiplicative.toAdd (φ.symm (Multiplicative.ofAdd (Pi.single j 1)))) = _ := rfl
      set t : ↥T := φ.symm (Multiplicative.ofAdd (Pi.single j (1 : GaloisField 2 1))) with ht
      have hmem : x * (t : G) * x⁻¹ ∈ T := conj_mem_of_mem_normalizer (hHN hxH) t.2
      have h1 := hcompat ⟨x, hxH⟩ t hmem
      have h2 : x * (t : G) * x⁻¹ = (t : G) := by
        have := hxC (t : G) t.2
        calc x * (t : G) * x⁻¹ = (t : G) * x * x⁻¹ := by rw [this]
          _ = t := by group
      have h3 : (⟨x * (t : G) * x⁻¹, hmem⟩ : ↥T) = t := Subtype.ext h2
      rw [h3] at h1
      have h4 : Multiplicative.toAdd (φ t) = Pi.single j 1 := by
        rw [ht]
        simp
      have h5 : ((e (QuotientGroup.mk ⟨x, hxH⟩) : SL(n, GaloisField 2 1)) :
          Matrix (Fin n) (Fin n) (GaloisField 2 1)) *ᵥ Pi.single j 1 = Pi.single j 1 := by
        have h6 := congrArg Multiplicative.toAdd h1
        rw [toAdd_ofAdd, h4] at h6
        exact h6.symm
      have h7 := congrFun h5 i
      rw [Matrix.mulVec_single_one] at h7
      simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h7
    exact (Subgroup.mem_subgroupOf.1 hxT)
  · intro t ht
    refine ⟨hTH ht, Subgroup.mem_centralizer_iff.2 fun b hb => hTcomm b hb t ht⟩

theorem exists_mul_of_natural {H : Subgroup G} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hnat : NaturalSL T H n 1) {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (T : Set G), g = h * c := by
  obtain ⟨h, hh, hact⟩ := exists_mem_conj_eq_of_natural hHN hnat hg
  refine ⟨h, hh, h⁻¹ * g, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 := hact t ht
  calc t * (h⁻¹ * g) = h⁻¹ * (h * t * h⁻¹) * g := by group
    _ = h⁻¹ * (g * t * g⁻¹) * g := by rw [h1]
    _ = h⁻¹ * g * t := by group

end CFSG.CGT.T75P
