module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MonoIdx

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem exists_conj_mem_of_isPGroup_three {A : Type} [Group A] [Finite A] (B : Subgroup A)
    (hB : ¬ 3 ∣ B.index) (V : Subgroup A) (hV : IsPGroup 3 V) :
    ∃ β : A, ∀ x ∈ V, β⁻¹ * x * β ∈ B := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : ¬ 3 ∣ Nat.card (A ⧸ B) := by
    rw [← Subgroup.index]
    exact hB
  obtain ⟨x, hx⟩ := hV.nonempty_fixed_point_of_prime_not_dvd_card (A ⧸ B) hcard
  obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨β, fun v hv => ?_⟩
  have h1 := hx ⟨v, hv⟩
  change (QuotientGroup.mk (v * β) : A ⧸ B) = QuotientGroup.mk β at h1
  have h2 := inv_mem (QuotientGroup.eq.1 h1)
  simpa [mul_assoc] using h2

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem d4_monomial_stable_all (K : Type) [Field K] [Finite K] (σ δ : K ≃+* K) :
    ∀ n ∈ (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      fieldActor (t := TwistTag.D4) σ δ n ∈
        (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  intro n hn
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨hnN, hnΓ⟩ := Subgroup.mem_inf.1 hn
  rw [coe_fieldActor]
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact baseChangeGL_mem_monomialSubgroup δ.toRingHom hnN
  · exact units_map_entrywiseHom_mem_twistedFixedGroup (ringEquiv_comm_of_finite σ δ) hnΓ

@[expose] def d4B0 (K : Type) [Field K] [Finite K] (σ : K ≃+* K) :
    Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) where
  carrier := {α | ∃ g ∈ (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∃ δ : K ≃+* K,
      α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ}
  mul_mem' := by
    rintro _ _ ⟨g, hg, δ, rfl⟩ ⟨g', hg', δ', rfl⟩
    refine ⟨g * fieldActor (t := TwistTag.D4) σ δ g',
      mul_mem hg (d4_monomial_stable_all K σ δ g' hg'), δ * δ', ?_⟩
    rw [fieldActor_mul, map_mul]
    calc MulAut.conj g * fieldActor σ δ * (MulAut.conj g' * fieldActor σ δ')
        = MulAut.conj g * (fieldActor σ δ * MulAut.conj g') * fieldActor σ δ' := by
          simp only [mul_assoc]
      _ = MulAut.conj g * (MulAut.conj (fieldActor σ δ g') * fieldActor σ δ) *
            fieldActor σ δ' := by rw [mulAut_mul_conj]
      _ = _ := by simp only [mul_assoc]
  one_mem' := ⟨1, one_mem _, 1, by rw [map_one, fieldActor_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨g, hg, δ, rfl⟩
    refine ⟨fieldActor (t := TwistTag.D4) σ δ⁻¹ g⁻¹,
      d4_monomial_stable_all K σ δ⁻¹ g⁻¹ (inv_mem hg), δ⁻¹, ?_⟩
    have hinv : (fieldActor (t := TwistTag.D4) σ δ)⁻¹ = fieldActor σ δ⁻¹ :=
      (map_inv (fieldActorHom (t := TwistTag.D4) σ) δ).symm
    rw [mul_inv_rev, ← map_inv MulAut.conj g, hinv]
    exact mulAut_mul_conj (fieldActor (t := TwistTag.D4) σ δ⁻¹) g⁻¹

theorem d4B0_conj_mem_iff {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (y y' : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    (MulAut.conj y)⁻¹ * MulAut.conj y' ∈ d4B0 K σ ↔
      y⁻¹ * y' ∈ (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, hNF, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  rw [← map_inv, ← map_mul]
  constructor
  · rintro ⟨g, hg, δ, h⟩
    have h1 : MulAut.conj (y⁻¹ * y') =
        MulAut.conj (y⁻¹ * y') * fieldActor (t := TwistTag.D4) σ 1 := by
      rw [fieldActor_one, mul_one]
    have h2 := (hNF (MulAut.conj (y⁻¹ * y'))).unique
      (y₁ := (y⁻¹ * y', 1)) (y₂ := (g, δ)) h1 h
    have h3 : y⁻¹ * y' = g := congrArg Prod.fst h2
    rw [h3]
    exact hg
  · intro h
    exact ⟨y⁻¹ * y', h, 1, by rw [fieldActor_one, mul_one]⟩

theorem d4B0_index {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    (d4B0 K σ).index = ((graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).index := by
  classical
  obtain ⟨-, hNF, -⟩ := odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  let Φ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⧸
      (graphFixedMonomial TwistTag.D4 K σ.toRingHom).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⧸ d4B0 K σ :=
    Quotient.lift (fun y => (QuotientGroup.mk (MulAut.conj y) : _ ⧸ d4B0 K σ))
      (fun a b hab => QuotientGroup.eq.2
        ((d4B0_conj_mem_iff hp hp2 hf K hK σ hσ a b).2 (QuotientGroup.leftRel_apply.1 hab)))
  have hinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
    exact QuotientGroup.eq.2 ((d4B0_conj_mem_iff hp hp2 hf K hK σ hσ y y').1
      (QuotientGroup.eq.1 hab))
  have hsurj : Function.Surjective Φ := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF α
    refine ⟨QuotientGroup.mk g, QuotientGroup.eq.2 ⟨1, one_mem _, δ, ?_⟩⟩
    rw [hgδ, map_one, one_mul, inv_mul_cancel_left]
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem d4_exists_conj_le_B0 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hq : (p ^ f) % 3 = 1)
    (V : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hV : IsPGroup 3 V) :
    ∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), ∀ x ∈ V,
      ∃ (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K),
        (g : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom ∧
        β⁻¹ * x * β = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hidx : ¬ 3 ∣ (d4B0 K σ).index := by
    rw [d4B0_index hp hp2 hf K hK σ hσ]
    exact d4_monomial_index_not_dvd hp hp2 hf K hK σ hσ hq
  obtain ⟨β, hβ⟩ := exists_conj_mem_of_isPGroup_three (d4B0 K σ) hidx V hV
  refine ⟨β, fun x hx => ?_⟩
  obtain ⟨g, hg, δ, h⟩ := hβ x hx
  exact ⟨g, δ, Subgroup.mem_subgroupOf.1 hg, h⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
