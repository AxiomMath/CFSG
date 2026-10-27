module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterFixRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsRootCenter

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.RootCenter CFSG.ProperTwoGeneratedCore.UnitaryKernels

section Decomposition

variable {G : Type*} [Group G] {A N D : Subgroup G}

theorem exists_inv_mul_sq_eq_one (hNA : N ≤ A) (hDA : D ≤ A) (hnormal : (N.subgroupOf A).Normal)
    (hinf : N ⊓ D = ⊥) (hsup : N ⊔ D = A) {γ : G} (hγ : γ ∈ A) (hγ2 : γ ^ 2 ∈ N) :
    ∃ c ∈ N, (c⁻¹ * γ) ^ 2 = 1 := by
  have htop : N.subgroupOf A ⊔ D.subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNA hDA, hsup, Subgroup.subgroupOf_self]
  have hmem : (⟨γ, hγ⟩ : A) ∈ ((N.subgroupOf A ⊔ D.subgroupOf A : Subgroup A) : Set A) := by
    rw [htop]
    exact Set.mem_univ _
  rw [Subgroup.normal_mul] at hmem
  obtain ⟨c, hc, d, hd, hcd⟩ := hmem
  have hcd' : (c : G) * d = γ := congrArg Subtype.val hcd
  refine ⟨c, Subgroup.mem_subgroupOf.mp hc, ?_⟩
  have hdeq : (c : G)⁻¹ * γ = d := by rw [← hcd', inv_mul_cancel_left]
  rw [hdeq]
  have hdD : (d : G) ^ 2 ∈ D := D.pow_mem (Subgroup.mem_subgroupOf.mp hd) 2
  have hdN : (d : G) ^ 2 ∈ N := by
    have hconj : γ * (c : G)⁻¹ * γ⁻¹ ∈ N := by
      have h := hnormal.conj_mem _ (Subgroup.inv_mem _ hc) ⟨γ, hγ⟩
      simpa using Subgroup.mem_subgroupOf.mp h
    have : (d : G) ^ 2 = (c : G)⁻¹ * (γ * (c : G)⁻¹ * γ⁻¹) * γ ^ 2 := by
      rw [← hdeq, pow_two, pow_two]; group
    rw [this]
    exact N.mul_mem (N.mul_mem (N.inv_mem (Subgroup.mem_subgroupOf.mp hc)) hconj) hγ2
  have h := Subgroup.mem_inf.mpr ⟨hdN, hdD⟩
  rwa [hinf, Subgroup.mem_bot] at h

theorem mul_inv_mem_of_isPGroup [Finite G] (hNA : N ≤ A) (hDA : D ≤ A)
    (hnormal : (N.subgroupOf A).Normal) (hinf : N ⊓ D = ⊥) (hsup : N ⊔ D = A) {m : ℕ}
    (hm : Odd m) (hD : Nat.card D = 2 * m) {Y : Subgroup G} (hY : IsPGroup 2 Y) {γ₁ γ₂ : G}
    (h₁Y : γ₁ ∈ Y) (h₂Y : γ₂ ∈ Y) (h₁A : γ₁ ∈ A) (h₂A : γ₂ ∈ A) (h₁ : γ₁ ∉ N) (h₂ : γ₂ ∉ N) :
    γ₁ * γ₂⁻¹ ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.subgroupOf A
  set D' := D.subgroupOf A
  let π : A →* A ⧸ N' := QuotientGroup.mk' N'
  have htop : N' ⊔ D' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNA hDA, hsup, Subgroup.subgroupOf_self]
  have hbij : Function.Bijective (π.comp D'.subtype) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro d hd
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hd
      have h := Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hd,
        Subgroup.mem_subgroupOf.mp d.2⟩
      rw [hinf, Subgroup.mem_bot] at h
      exact (Subgroup.mem_bot).mpr (Subtype.ext (Subtype.ext h))
    · intro x
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N' x
      have hmem : a ∈ ((N' ⊔ D' : Subgroup A) : Set A) := by rw [htop]; exact Set.mem_univ _
      rw [Subgroup.normal_mul] at hmem
      obtain ⟨c, hc, d, hd, rfl⟩ := hmem
      refine ⟨⟨d, hd⟩, ?_⟩
      have hc1 : π c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
      change π d = π (c * d)
      rw [map_mul, hc1, one_mul]
  have hQ : Nat.card (A ⧸ N') = 2 * m := by
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), ← hD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  set Z := (Y.subgroupOf A).map π
  have hZp : IsPGroup 2 Z := (hY.comap_of_injective A.subtype Subtype.val_injective).map π
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hZ2 : Nat.card Z ≤ 2 := by
    rw [hk]
    exact two_pow_dvd_two_of_dvd_two_mul_odd hm (hk ▸ hQ ▸ Subgroup.card_subgroup_dvd_card Z)
  have hz₁ : π ⟨γ₁, h₁A⟩ ∈ Z := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h₁Y)
  have hz₂ : π ⟨γ₂, h₂A⟩ ∈ Z := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h₂Y)
  have hne : ∀ (γ : G) (hγ : γ ∈ A), γ ∉ N → π ⟨γ, hγ⟩ ≠ 1 := by
    intro γ hγ hγN h1
    exact hγN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1))
  have heq : (⟨π ⟨γ₁, h₁A⟩, hz₁⟩ : Z) = ⟨π ⟨γ₂, h₂A⟩, hz₂⟩ :=
    eq_of_card_le_two hZ2 (o := 1) (fun h => hne γ₁ h₁A h₁ (congrArg Subtype.val h))
      (fun h => hne γ₂ h₂A h₂ (congrArg Subtype.val h))
  have h := (QuotientGroup.eq_iff_div_mem).mp (congrArg Subtype.val heq)
  simpa [div_eq_mul_inv] using Subgroup.mem_subgroupOf.mp h

end Decomposition

section Transport

variable {F : Type*} [Group F] {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) {f : ℕ}
  (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (e : F ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  (R : Sylow 2 F)
include hf hcard hfixed hJ e

theorem mem_omega_iff (x : F) :
    x ∈ (CFSG.omega₁ (G := (R : Subgroup F)) (p := 2)).map (R : Subgroup F).subtype ↔
      x ∈ (R : Subgroup F) ∧ x ^ 2 = 1 := by
  have : CharP K 2 := charP_two_of_card f hcard
  obtain ⟨⟨ε, hεR, hεU, -⟩, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J f hf hcard hfixed hJ e R _ rfl
  rw [← hεU, ← hεR]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu1, hu2⟩ := (mem_center_iff_sq_eq_one J hJ).mp hu
    exact ⟨Subgroup.mem_map_of_mem _ hu1, by rw [← map_pow, MulEquiv.coe_toMonoidHom, hu2, map_one]⟩
  · rintro ⟨⟨u, hu, rfl⟩, h2⟩
    refine ⟨u, (mem_center_iff_sq_eq_one J hJ).mpr ⟨hu, ?_⟩, rfl⟩
    apply ε.injective
    rw [map_pow, map_one]
    exact h2

theorem card_omega :
    Nat.card ((CFSG.omega₁ (G := (R : Subgroup F)) (p := 2)).map (R : Subgroup F).subtype) =
      2 ^ f := by
  have : CharP K 2 := charP_two_of_card f hcard
  obtain ⟨⟨ε, -, hεU, -⟩, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J f hf hcard hfixed hJ e R _ rfl
  rw [← hεU, Subgroup.card_map_of_injective ε.injective,
    Subgroup.card_map_of_injective (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ)]
  exact card_ker_firstCoord J hfixed

theorem fix_omega (γ : MulAut F) (hγR : (R : Subgroup F).map γ.toMonoidHom = R)
    (hγ2 : γ ^ 2 ∈ (R : Subgroup F).map MulAut.conj) {u : F} (hu : u ∈ (R : Subgroup F))
    (hu2 : u ^ 2 = 1) : γ u = u := by
  have : CharP K 2 := charP_two_of_card f hcard
  obtain ⟨⟨ε, hεR, hεU, -⟩, -⟩ :=
    even_unitary_root_center_automorphisms_of_mulEquiv J f hf hcard hfixed hJ e R _ rfl
  set γ₀ := (MulAut.congr ε).symm γ with hγ₀
  have hγγ₀ : MulAut.congr ε γ₀ = γ := MulEquiv.apply_symm_apply _ _
  have h1 : (unitaryCoverRoot J hJ).map γ₀.toMonoidHom = unitaryCoverRoot J hJ := by
    apply Subgroup.map_injective (f := ε.toMonoidHom) ε.injective
    rw [← RootCenterAutomorphisms.map_congr, hγγ₀, hεR, hγR]
  have h2 : γ₀ ^ 2 ∈ (unitaryCoverRoot J hJ).map MulAut.conj := by
    rw [← RootCenterAutomorphisms.congr_mem_map_conj ε, map_pow, hγγ₀, hεR]
    exact hγ2
  have h3 := fix_rootCenter_of_sq_mem_conj J hf hcard hfixed hJ γ₀ h1 h2
  have h4 := (RootCenterAutomorphisms.forall_congr_apply ε γ₀ (unitaryRootCenter J hJ)).mpr h3
  rw [hεU, hγγ₀] at h4
  exact h4 u ((mem_omega_iff J hf hcard hfixed hJ e R u).mpr ⟨hu, hu2⟩)

end Transport

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
