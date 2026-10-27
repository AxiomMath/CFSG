module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.SolvableHallNodes

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

private theorem exists_invariant_sylow_of_not_dvd' {A H : Type*} [Group A] [Group H] [Finite H]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hA : IsPGroup p A)
    (hnd : ¬ p ∣ Nat.card (Sylow q H)) (φ : A →* MulAut H) :
    ∃ P : Sylow q H, ∀ a : A, (P : Subgroup H).map (φ a).toMonoidHom = P := by
  let := MulDistribMulAction.compHom H φ
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q H) hnd
  refine ⟨P, fun a => ?_⟩
  have h := congrArg (fun Q : Sylow q H => (Q : Subgroup H)) (MulAction.mem_fixedPoints.mp hP a)
  rw [Sylow.pointwise_smul_def] at h
  exact h

theorem exists_conj_normalizes_inf {p : ℕ} [Fact p.Prime]
    {R V U Y : Subgroup G} (hVp : IsPGroup p V) (hRcop : Nat.Coprime p (Nat.card R))
    (hVR : V ≤ normalizer (R : Set G)) (hUV : U ≤ V)
    (hYR : Y ≤ normalizer (R : Set G)) (hUY : U ≤ normalizer (Y : Set G))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Y ⊓ R) R) :
    ∃ c ∈ R, (∀ u ∈ U, c * u = u * c) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (Y.map (MulAut.conj c).toMonoidHom ⊓ R) R ∧
      V ≤ normalizer ((Y.map (MulAut.conj c).toMonoidHom ⊓ R : Subgroup G) : Set G) := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUp : IsPGroup p U := hVp.to_le hUV
  have hUR : U ≤ normalizer (R : Set G) := hUV.trans hVR
  have hpR : ¬ p ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd hp).1 hRcop
  let φV : ↥V →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hVR)
  let φU : ↥U →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hUR)
  have hφ : ∀ (v : ↥V) (z : ↥R), (((φV v) z : ↥R) : G) = (v : G) * (z : G) * (v : G)⁻¹ :=
    fun v z => rfl
  have hnd : ¬ p ∣ Nat.card (Sylow 2 ↥R) := by
    intro h
    obtain ⟨P₂⟩ := (inferInstance : Nonempty (Sylow 2 ↥R))
    exact hpR ((h.trans (Sylow.card_dvd_index P₂)).trans
      (Subgroup.index_dvd_card (P₂ : Subgroup ↥R)))
  obtain ⟨Q₀, hQ₀⟩ := exists_invariant_sylow_of_not_dvd' hVp hnd φV
  obtain ⟨P₁, hP₁⟩ := hsyl
  have hmemP₁ : ∀ z : ↥R, z ∈ (P₁ : Subgroup ↥R) ↔ (z : G) ∈ Y := by
    intro z
    have h1 : (z : G) ∈ (P₁ : Subgroup ↥R).map R.subtype ↔ z ∈ (P₁ : Subgroup ↥R) :=
      Subgroup.mem_map_iff_mem R.subtype_injective
    rw [← h1, hP₁]
    exact ⟨fun h => h.1, fun h => ⟨h, z.2⟩⟩
  letI : MulDistribMulAction ↥U ↥R := MulDistribMulAction.compHom ↥R φU
  have hU_smul : ∀ (u : ↥U) (z : ↥R), ((u • z : ↥R) : G) = (u : G) * (z : G) * (u : G)⁻¹ :=
    fun u z => rfl
  have hP : ∀ a : ↥U, ∀ x ∈ (P₁ : Subgroup ↥R), a • x ∈ (P₁ : Subgroup ↥R) := by
    intro a x hx
    rw [hmemP₁] at hx ⊢
    rw [hU_smul]
    exact (Subgroup.mem_normalizer_iff.1 (hUY a.2) _).1 hx
  have hQ : ∀ a : ↥U, ∀ x ∈ (Q₀ : Subgroup ↥R), a • x ∈ (Q₀ : Subgroup ↥R) := by
    intro a x hx
    have h := hQ₀ ⟨a, hUV a.2⟩
    have hmem : (φV ⟨a, hUV a.2⟩) x ∈
        (Q₀ : Subgroup ↥R).map (φV ⟨a, hUV a.2⟩).toMonoidHom := ⟨x, hx, rfl⟩
    rw [h] at hmem
    exact hmem
  obtain ⟨c', hc'fix, hc'⟩ := CFSG.SolvableHall.coprime_invariant_sylow_conjugacy
    (A := ↥U) (H := ↥R) hUp hpR P₁ Q₀ hP hQ
  have hc'inv : c'⁻¹ ∈ fixedPointSubgroup ↥U ↥R := inv_mem hc'fix
  have hmemY : ∀ x : G, x ∈ Y.map (MulAut.conj ((c'⁻¹ : ↥R) : G)).toMonoidHom ↔
      (c' : G) * x * (c' : G)⁻¹ ∈ Y := by
    intro x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hmemQ₀ : ∀ z : ↥R, z ∈ (Q₀ : Subgroup ↥R) ↔ (c' : G) * (z : G) * (c' : G)⁻¹ ∈ Y := by
    intro z
    rw [← hc', Subgroup.mem_map_equiv, hmemP₁]
    simp [MulAut.conj_symm_apply]
  have hQ₀eq : (Q₀ : Subgroup ↥R).map R.subtype =
      Y.map (MulAut.conj ((c'⁻¹ : ↥R) : G)).toMonoidHom ⊓ R := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(hmemY _).2 ((hmemQ₀ z).1 hz), z.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨x, hxR⟩, (hmemQ₀ ⟨x, hxR⟩).2 ((hmemY x).1 hx), rfl⟩
  refine ⟨((c'⁻¹ : ↥R) : G), (c'⁻¹ : ↥R).2, ?_, ⟨Q₀, hQ₀eq⟩, ?_⟩
  · intro u hu
    have h := congrArg Subtype.val (hc'inv ⟨u, hu⟩)
    rw [hU_smul] at h
    simp only [Subgroup.coe_inv] at h ⊢
    calc ((c' : G))⁻¹ * u = ((u : G) * (c' : G)⁻¹ * (u : G)⁻¹) * u := by rw [h]
      _ = u * (c' : G)⁻¹ := by group
  · rw [← hQ₀eq]
    have key : ∀ w ∈ V, ∀ x ∈ (Q₀ : Subgroup ↥R).map R.subtype,
        w * x * w⁻¹ ∈ (Q₀ : Subgroup ↥R).map R.subtype := by
      intro w hw x hx
      obtain ⟨z, hz, rfl⟩ := hx
      have h := hQ₀ ⟨w, hw⟩
      have hmem : (φV ⟨w, hw⟩) z ∈
          (Q₀ : Subgroup ↥R).map (φV ⟨w, hw⟩).toMonoidHom := ⟨z, hz, rfl⟩
      rw [h] at hmem
      exact ⟨_, hmem, hφ ⟨w, hw⟩ z⟩
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key v hv x
    · intro hx
      have := key v⁻¹ (inv_mem hv) _ hx
      simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
