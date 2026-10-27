module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HG2Inn

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

theorem exists_conj_of_induces {Ω : Type} [Group Ω] {K A : Subgroup Ω}
    (hA : A ≤ Subgroup.normalizer (K : Set Ω))
    (hZ : Subgroup.center (PQuot 3 K) = ⊥) (hO : GLAPPrimeCoreOf 3 K = ⊥)
    {R : Type} [Group R] (θ : PSimple 3 K ≃* R) {a : Ω} (ha : a ∈ A) {r : R}
    (hind : GLAInduces θ (indRel 3 K a) (MulAut.conj r)) :
    ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ = k * x * k⁻¹ := by
  have haN : a ∈ Subgroup.normalizer (K : Set Ω) := hA ha
  have hainvN : a⁻¹ ∈ Subgroup.normalizer (K : Set Ω) := Subgroup.inv_mem _ haN
  have hconjK : ∀ g ∈ Subgroup.normalizer (K : Set Ω), ∀ x ∈ K, g * x * g⁻¹ ∈ K := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.1 hg x).1 hx
  have hcore : GLAPPrimeCore 3 ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 hO
  obtain ⟨F, hF⟩ : ∃ F : ↥K →* R, ∀ x : ↥K,
      F x = θ (QuotientGroup.mk (QuotientGroup.mk x : PQuot 3 K)) :=
    ⟨(θ : PSimple 3 K →* R).comp ((QuotientGroup.mk' (Subgroup.center (PQuot 3 K))).comp
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K))), fun _ => rfl⟩
  have hFq : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) : ↥K →* PQuot 3 K) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff x).1 hx
    rw [hcore] at hx'
    exact Subgroup.mem_bot.1 hx'
  have hFz : Function.Injective (QuotientGroup.mk' (Subgroup.center (PQuot 3 K)) : PQuot 3 K →* PSimple 3 K) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hy' : y ∈ Subgroup.center (PQuot 3 K) := (QuotientGroup.eq_one_iff y).1 hy
    rw [hZ] at hy'
    exact Subgroup.mem_bot.1 hy'
  have hFinj : Function.Injective F := by
    intro x y hxy
    rw [hF, hF] at hxy
    exact hFq (hFz (θ.injective hxy))
  have hFsurj : Function.Surjective F := by
    intro s
    obtain ⟨t, rfl⟩ := θ.surjective s
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    exact ⟨x, hF x⟩
  have hrel : ∀ x y : ↥K, (y : Ω) = a⁻¹ * (x : Ω) * a → F y = r * F x * r⁻¹ := by
    intro x y hxy
    have h2 := hind (QuotientGroup.mk x) (QuotientGroup.mk y) ⟨x, y, rfl, rfl, hxy⟩
    rw [MulAut.conj_apply] at h2
    rw [hF, hF]
    exact h2.symm
  obtain ⟨k₀, hk₀⟩ := hFsurj r
  have H1 : ∀ x : ↥K, a⁻¹ * (x : Ω) * a = (k₀ : Ω) * (x : Ω) * (k₀ : Ω)⁻¹ := by
    intro x
    have hy : a⁻¹ * (x : Ω) * a ∈ K := by
      have h := hconjK a⁻¹ hainvN x x.2
      rwa [inv_inv] at h
    have hFy : F ⟨a⁻¹ * (x : Ω) * a, hy⟩ = F (k₀ * x * k₀⁻¹) := by
      rw [hrel x ⟨a⁻¹ * (x : Ω) * a, hy⟩ rfl, map_mul, map_mul, map_inv, hk₀]
    have hyeq := hFinj hFy
    have hval := congrArg Subtype.val hyeq
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hval
  refine ⟨(k₀ : Ω)⁻¹, Subgroup.inv_mem K k₀.2, ?_⟩
  intro x hx
  have hyK : a * x * a⁻¹ ∈ K := hconjK a haN x hx
  have h : a⁻¹ * (a * x * a⁻¹) * a = (k₀ : Ω) * (a * x * a⁻¹) * (k₀ : Ω)⁻¹ :=
    H1 ⟨a * x * a⁻¹, hyK⟩
  have hL : a⁻¹ * (a * x * a⁻¹) * a = x := by group
  rw [hL] at h
  calc a * x * a⁻¹ = (k₀ : Ω)⁻¹ * ((k₀ : Ω) * (a * x * a⁻¹) * (k₀ : Ω)⁻¹) * (k₀ : Ω) := by group
    _ = (k₀ : Ω)⁻¹ * x * (k₀ : Ω) := by rw [← h]
    _ = (k₀ : Ω)⁻¹ * x * ((k₀ : Ω)⁻¹)⁻¹ := by group

end CFSG.LocalAnalysis.GLTheoremA.HG2Inn

end
