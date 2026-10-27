module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Aff
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKG2024Cycle

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Equiv Equiv.Perm Subgroup Module

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem hol_exists (T : Subgroup (Perm Ω)) (z : Perm Ω) (o : Ω)
    (hcomm : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) (hsq : ∀ t ∈ T, t * t = 1)
    (hinv : ∀ t, t ∈ T ↔ z * t * z⁻¹ ∈ T) (hzo : z o = o)
    (hfree : ∀ t ∈ T, t o = o → t = 1)
    (hout : ∀ x, (¬ ∃ s ∈ T, s o = x) → z x = x ∧ ∀ t ∈ T, t x = x)
    (hcard : 5 ≤ Nat.card ↥T) :
    ∃ Y : Subgroup (Perm Ω), T ≤ Y ∧ Y ≤ normalizer (T : Set (Perm Ω)) ∧ z ∈ Y ∧
      S622IsSimpleSection Y T ∧ 3 ∣ T.relIndex Y := by
  classical
  letI : CommGroup ↥T :=
    { (inferInstance : Group ↥T) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have h2 : ∀ x : Additive ↥T, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [two_nsmul, toMul_add, toMul_zero]
    exact Subtype.ext (hsq _ (Additive.toMul x).2)
  letI : Module (ZMod 2) (Additive ↥T) := AddCommGroup.zmodModule h2
  haveI : Finite (Additive ↥T) := inferInstance
  have hrank : 3 ≤ finrank (ZMod 2) (Additive ↥T) := by
    haveI : FiniteDimensional (ZMod 2) (Additive ↥T) := Module.finite_iff_finite.mpr inferInstance
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive ↥T)
    rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive ↥T ≃ ↥T)] at h
    by_contra hlt
    have h1 : finrank (ZMod 2) (Additive ↥T) ≤ 2 := by omega
    have h3 : 2 ^ finrank (ZMod 2) (Additive ↥T) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  let ι : Additive ↥T → Ω := fun v => ((Additive.toMul v : ↥T) : Perm Ω) o
  have hι : Function.Injective ι := by
    intro v w hvw
    apply Additive.toMul.injective
    have hab : ((Additive.toMul v : ↥T) : Perm Ω) o = ((Additive.toMul w : ↥T) : Perm Ω) o := hvw
    have h1 : (((Additive.toMul w : ↥T)⁻¹ * Additive.toMul v : ↥T) : Perm Ω) o = o := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, hab, perm_inv_apply_self]
    have h3 : ((Additive.toMul w : ↥T)⁻¹ * Additive.toMul v : ↥T) = 1 :=
      Subtype.ext (hfree _ (((Additive.toMul w : ↥T)⁻¹ * Additive.toMul v : ↥T)).2 h1)
    exact (inv_mul_eq_one.1 h3).symm
  let ρ := affToPerm (Additive ↥T) ι hι
  have hnot : ∀ x : Ω, (∀ u, ι u ≠ x) → ¬ ∃ s ∈ T, s o = x := by
    rintro x hx ⟨s, hs, hsx⟩
    exact hx (Additive.ofMul ⟨s, hs⟩) hsx
  have hρt : ∀ w : Additive ↥T,
      ρ (AffineEquiv.constVAdd (ZMod 2) (Additive ↥T) w) = ((Additive.toMul w : ↥T) : Perm Ω) := by
    intro w
    ext x
    by_cases hx : ∃ u, ι u = x
    · obtain ⟨u, rfl⟩ := hx
      rw [affToPerm_apply_ι hι]
      simp only [AffineEquiv.constVAdd_apply, vadd_eq_add]
      show ((Additive.toMul (w + u) : ↥T) : Perm Ω) o =
        ((Additive.toMul w : ↥T) : Perm Ω) (((Additive.toMul u : ↥T) : Perm Ω) o)
      rw [toMul_add, Subgroup.coe_mul, Perm.mul_apply]
    · push Not at hx
      rw [affToPerm_apply_out hι _ hx]
      exact ((hout x (hnot x hx)).2 _ (Additive.toMul w).2).symm
  have hconj : ∀ t : ↥T, z * (t : Perm Ω) * z⁻¹ ∈ T := fun t => (hinv t).1 t.2
  have hconj' : ∀ t : ↥T, z⁻¹ * (t : Perm Ω) * z ∈ T := by
    intro t
    apply (hinv _).2
    have e : z * (z⁻¹ * (t : Perm Ω) * z) * z⁻¹ = t := by group
    rw [e]
    exact t.2
  let cz0 : Additive ↥T ≃+ Additive ↥T :=
    { toFun := fun v => Additive.ofMul ⟨z * ((Additive.toMul v : ↥T) : Perm Ω) * z⁻¹,
        hconj _⟩
      invFun := fun v => Additive.ofMul ⟨z⁻¹ * ((Additive.toMul v : ↥T) : Perm Ω) * z,
        hconj' _⟩
      left_inv := fun v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show z⁻¹ * (z * ((Additive.toMul v : ↥T) : Perm Ω) * z⁻¹) * z = _
        group
      right_inv := fun v => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show z * (z⁻¹ * ((Additive.toMul v : ↥T) : Perm Ω) * z) * z⁻¹ = _
        group
      map_add' := fun v w => by
        apply Additive.toMul.injective
        apply Subtype.ext
        show z * (((Additive.toMul v : ↥T) : Perm Ω) * ((Additive.toMul w : ↥T) : Perm Ω)) * z⁻¹ =
          (z * ((Additive.toMul v : ↥T) : Perm Ω) * z⁻¹) *
            (z * ((Additive.toMul w : ↥T) : Perm Ω) * z⁻¹)
        group }
  let cz : Additive ↥T ≃ₗ[ZMod 2] Additive ↥T :=
    AddEquiv.toLinearEquiv cz0 fun c x => ZMod.map_smul cz0 c x
  have hρz : ρ cz.toAffineEquiv = z := by
    ext x
    by_cases hx : ∃ u, ι u = x
    · obtain ⟨u, rfl⟩ := hx
      rw [affToPerm_apply_ι hι]
      show (z * ((Additive.toMul u : ↥T) : Perm Ω) * z⁻¹) o =
        z (((Additive.toMul u : ↥T) : Perm Ω) o)
      have : z⁻¹ o = o := by rw [Perm.inv_eq_iff_eq]; exact hzo.symm
      rw [Perm.mul_apply, Perm.mul_apply, this]
    · push Not at hx
      rw [affToPerm_apply_out hι _ hx]
      exact ((hout x (hnot x hx)).1).symm
  have hker : (AffineEquiv.linearHom (k := ZMod 2) (P₁ := Additive ↥T)).ker.map ρ = T := by
    ext t
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨w, rfl⟩ := (mem_ker_linearHom_iff _ f).1 hf
      rw [hρt]
      exact (Additive.toMul w).2
    · intro ht
      refine ⟨AffineEquiv.constVAdd (ZMod 2) (Additive ↥T) (Additive.ofMul ⟨t, ht⟩),
        (mem_ker_linearHom_iff _ _).2 ⟨_, rfl⟩, ?_⟩
      rw [hρt]
      rfl
  have hρinj := affToPerm_injective (V := Additive ↥T) hι
  have hnorm : ∀ f : Additive ↥T ≃ᵃ[ZMod 2] Additive ↥T, ∀ t ∈ T, ρ f * t * (ρ f)⁻¹ ∈ T := by
    intro f t ht
    have ht' : t ∈ (AffineEquiv.linearHom (k := ZMod 2) (P₁ := Additive ↥T)).ker.map ρ := by
      rw [hker]
      exact ht
    obtain ⟨g, hg, rfl⟩ := ht'
    obtain ⟨w, rfl⟩ := (mem_ker_linearHom_iff _ g).1 hg
    rw [← map_inv, ← map_mul, ← map_mul, conj_constVAdd, hρt]
    exact (Additive.toMul (f.linear w)).2
  refine ⟨ρ.range, ?_, ?_, ⟨cz.toAffineEquiv, hρz⟩, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ (AffineEquiv.linearHom (k := ZMod 2) (P₁ := Additive ↥T)).ker.map ρ := by
      rw [hker]
      exact ht
    obtain ⟨g, -, rfl⟩ := ht'
    exact ⟨g, rfl⟩
  · rintro _ ⟨f, rfl⟩
    refine mem_normalizer_of_forward (hnorm f) fun t ht => ?_
    have := hnorm f⁻¹ t ht
    rwa [map_inv, inv_inv] at this
  · have := L6LeavesNS.s622IsSimpleSection_map ρ hρinj (aff_section (Additive ↥T) hrank)
    rwa [hker, ← MonoidHom.range_eq_map] at this
  · have h := three_dvd_relIndex (Additive ↥T) hrank
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hρinj, hker,
      ← MonoidHom.range_eq_map] at h
    exact h

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
