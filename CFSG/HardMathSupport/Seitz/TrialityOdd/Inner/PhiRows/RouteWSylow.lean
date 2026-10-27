module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWPlane
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.K128 CFSG.GH74.GLS.Stage2.Bender.Thm1

lemma exists_plane_of_sylowShape_omega {G : Type*} [Group G] {r e : ℕ} [Fact r.Prime]
    (he : 1 ≤ e) (S : Subgroup G) (φ : S ≃* (Fin 2 → Multiplicative (ZMod (r ^ e)))) :
    ∃ E : Subgroup G, E ≤ S ∧ (∀ x ∈ E, x ^ r = 1) ∧ Nat.card E = r ^ 2 ∧
      (∀ x ∈ S, x ^ r = 1 → x ∈ E) ∧ (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) := by
  let E₀ : Subgroup (Fin 2 → Multiplicative (ZMod (r ^ e))) := (powMonoidHom r).ker
  let E : Subgroup G := (E₀.map φ.symm.toMonoidHom).map S.subtype
  have hmem : ∀ x : G, x ∈ E ↔ ∃ v ∈ E₀, ((φ.symm v : S) : G) = x := by
    intro x
    simp only [E, Subgroup.mem_map, Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have hv : ∀ v ∈ E₀, v ^ r = 1 := fun v hv => by
    simpa [E₀, MonoidHom.mem_ker, powMonoidHom_apply] using hv
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x hx
    obtain ⟨v, -, rfl⟩ := (hmem x).1 hx
    exact (φ.symm v).2
  · intro x hx
    obtain ⟨v, hv', rfl⟩ := (hmem x).1 hx
    rw [← Subgroup.coe_pow, ← map_pow, hv v hv', map_one]
    rfl
  · rw [Subgroup.card_map_of_injective (Subtype.val_injective),
      Subgroup.card_map_of_injective φ.symm.injective]
    exact card_ker_pow_pi r e he
  · intro x hxS hxr
    rw [hmem]
    refine ⟨φ ⟨x, hxS⟩, ?_, by simp⟩
    have h1 : (⟨x, hxS⟩ : S) ^ r = 1 := Subtype.ext (by simpa using hxr)
    have h2 := congrArg φ h1
    rw [map_pow, map_one] at h2
    simpa [E₀, MonoidHom.mem_ker, powMonoidHom_apply] using h2
  · intro x hx y hy
    have : (⟨x, hx⟩ * ⟨y, hy⟩ : S) = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      φ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    exact congrArg Subtype.val this

lemma conj_sylow_data {G : Type*} [Group G] {r : ℕ} [Fact r.Prime] (S : Sylow r G)
    (E₁ : Subgroup G) (hE : E₁ ≤ (S : Subgroup G))
    (hΩ : ∀ x ∈ (S : Subgroup G), x ^ r = 1 → x ∈ E₁)
    (hcomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x) (c : G) :
    ∃ P : Sylow r G, E₁.map (MulAut.conj c).toMonoidHom ≤ (P : Subgroup G) ∧
      (∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) ∧
      (∀ x ∈ (P : Subgroup G), x ^ r = 1 → x ∈ E₁.map (MulAut.conj c).toMonoidHom) := by
  have hP : ((c • S : Sylow r G) : Subgroup G) =
      (S : Subgroup G).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨c • S, ?_, ?_, ?_⟩
  · rw [hP]
    exact Subgroup.map_mono hE
  · rw [hP]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    change (c * s * c⁻¹) * (c * t * c⁻¹) = (c * t * c⁻¹) * (c * s * c⁻¹)
    have := hcomm s hs t ht
    calc (c * s * c⁻¹) * (c * t * c⁻¹) = c * (s * t) * c⁻¹ := by group
      _ = c * (t * s) * c⁻¹ := by rw [this]
      _ = (c * t * c⁻¹) * (c * s * c⁻¹) := by group
  · rw [hP]
    rintro _ ⟨s, hs, rfl⟩ hxr
    refine ⟨s, hΩ s hs ?_, rfl⟩
    have h : (c * s * c⁻¹) ^ r = 1 := hxr
    rw [conj_pow] at h
    have h2 : s ^ r = 1 := by
      have := congrArg (fun z => c⁻¹ * z * c) h
      simpa [mul_assoc] using this
    exact h2

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

