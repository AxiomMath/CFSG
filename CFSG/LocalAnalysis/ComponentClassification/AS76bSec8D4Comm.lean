module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Defs
public import CFSG.Timmesfeld.RankTwo.ModelD43Comm
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LieType.Chevalley.FoldedWeylIdentification
public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Chevalley.EvenTrialityOrbitParametrization
public import CFSG.LieType.Chevalley.EvenDiagramRootParameters
public import CFSG.LieType.Chevalley.GraphFixedRootMonomialQuotient
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

section Bridge

variable [CharP K 2]

theorem coe_xPar_d4
    {γ : Fin TwistTag.D4.tag.rank → ℤ} (hγ : IsRoot TwistTag.D4.tag γ)
    (c : K) : ((xPar (rootOperatorFamily d4) γ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K γ c := by
  have hs : ((rootOperatorFamily d4).pinnedFamilySign γ : K) = 1 := by
    rcases (rootOperatorFamily d4).pinnedFamilySign_eq γ with h | h <;> rw [h]
    · exact Int.cast_one
    · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]
  have h := (rootOperatorFamily d4).pinnedX_eq_eltUnit K hγ c
  rw [hs, one_mul] at h
  rw [xPar_of_isRoot hγ, h]
  rfl

theorem coe_xOrbit_d4
    (σ : K →+* K) {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : IsRoot TwistTag.D4.tag γ) (c : K) :
    ((xOrbit σ γ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K γ c *
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm γ) (σ c) *
          pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) γ) (σ (σ c)) := by
  rw [xOrbit_eq σ γ c, Subgroup.coe_mul, Subgroup.coe_mul, coe_xPar_d4 hγ,
    coe_xPar_d4 (isRoot_rho hγ), coe_xPar_d4 (isRoot_rho (isRoot_rho
        hγ)), ← permLattice_D4_perm_perm]

end Bridge

theorem trialityRoot_eq_d4Root :
    trialityRoot 0 = d4Root 0 ∧ trialityRoot 1 = d4Root 2 ∧ trialityRoot 2 = d4Root 5 ∧
      trialityRoot 3 = d4Root 15 ∧ trialityRoot 4 = d4Root 19 ∧ trialityRoot 5 = d4Root 22 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext k <;> fin_cases k <;> decide +kernel

section Elements

variable [CharP K 2] (σ : K ≃+* K)

theorem d4x₁_eq
    (c : K) :
    d4x₁ K σ c = ((xOrbit σ.toRingHom (d4Root 0) c : adjointGroup d4 K) : ModGL TwistTag.D4.tag
        K) := by
  rw [d4x₁, coe_trialityOrbitProd, coe_xOrbit_d4 _ (isRoot_d4Root (by norm_num)),
    trialityRoot_eq_d4Root.1]

theorem d4x₃_eq
    (c : K) :
    d4x₃ K σ c = ((xOrbit σ.toRingHom (d4Root 5) c : adjointGroup d4 K) : ModGL TwistTag.D4.tag
        K) := by
  rw [d4x₃, coe_trialityOrbitProd, coe_xOrbit_d4 _ (isRoot_d4Root (by norm_num)),
    trialityRoot_eq_d4Root.2.2.1]

theorem d4x₄_eq
    (c : K) :
    d4x₄ K σ c = ((xOrbit σ.toRingHom (d4Root 15) c : adjointGroup d4 K) : ModGL TwistTag.D4.tag
        K) := by
  rw [d4x₄, coe_trialityOrbitProd, coe_xOrbit_d4 _ (isRoot_d4Root (by norm_num)),
    trialityRoot_eq_d4Root.2.2.2.1]

variable (K) in
theorem d4x₂_eq
    (c : K) :
    d4x₂ K c = ((xPar (rootOperatorFamily d4) (d4Root 2) c : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) := by
  rw [d4x₂, coe_xPar_d4 (isRoot_d4Root (by norm_num)), trialityRoot_eq_d4Root.2.1]

variable (K) in
theorem d4x₅_eq
    (c : K) :
    d4x₅ K c = ((xPar (rootOperatorFamily d4) (d4Root 19) c : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) := by
  rw [d4x₅, coe_xPar_d4 (isRoot_d4Root (by norm_num)), trialityRoot_eq_d4Root.2.2.2.2.1]

variable (K) in
theorem d4x₆_eq
    (c : K) :
    d4x₆ K c = ((xPar (rootOperatorFamily d4) (d4Root 22) c : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) := by
  rw [d4x₆, coe_xPar_d4 (isRoot_d4Root (by norm_num)), trialityRoot_eq_d4Root.2.2.2.2.2]

end Elements

section Relations

theorem toRingHom_cube {σ : K ≃+* K} (hσ : ∀ c, σ (σ (σ c)) = c) :
    ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c :=
  hσ

theorem coe_commutatorElement_d4
    (x y : adjointGroup d4 K) :
    ((⁅x, y⁆ : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) =
      ⁅(x : ModGL TwistTag.D4.tag K), (y : ModGL TwistTag.D4.tag K)⁆ :=
  rfl

variable [CharP K 2] (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem comm_d4x₁_d4x₄
    (s t : K) :
    ⁅d4x₁ K σ s, d4x₄ K σ t⁆ = d4x₅ K (s * t + σ (s * t) + σ (σ (s * t))) := by
  rw [d4x₁_eq, d4x₄_eq, d4x₅_eq, ← coe_commutatorElement_d4, d43_comm02 (toRingHom_cube hσ)]
  rfl

include hσ in
theorem comm_d4x₄_d4x₃
    (s t : K) :
    ⁅d4x₄ K σ s, d4x₃ K σ t⁆ = d4x₆ K (s * t + σ (s * t) + σ (σ (s * t))) := by
  rw [d4x₃_eq, d4x₄_eq, d4x₆_eq, ← coe_commutatorElement_d4, d43_comm24 (toRingHom_cube hσ)]
  rfl

theorem comm_d4x₅_d4x₂
    (s t : K) :
    ⁅d4x₅ K s, d4x₂ K t⁆ = d4x₆ K (s * t) := by
  rw [d4x₂_eq, d4x₅_eq, d4x₆_eq, ← coe_commutatorElement_d4,
    d4_comm (a := 19) (b := 2) (g := 22) (by decide) (Or.inr rfl)]

include hσ in
theorem comm_d4x₁_d4x₂
    (s u : K) (hu : σ u = u) :
    ⁅d4x₁ K σ s, d4x₂ K u⁆ = d4x₅ K (u * (s * σ s * σ (σ s))) * d4x₄ K σ (u * (σ s * σ (σ s))) *
      d4x₆ K (u ^ 2 * (s * σ s * σ (σ s))) * d4x₃ K σ (u * s) := by
  rw [d4x₁_eq, d4x₂_eq, d4x₃_eq, d4x₄_eq, d4x₅_eq, d4x₆_eq, ← coe_commutatorElement_d4,
    d43_comm05 (toRingHom_cube hσ) s u hu]
  rfl

include hσ in
theorem comm_d4x₁_d4x₃
    (s t : K) :
    ⁅d4x₁ K σ s, d4x₃ K σ t⁆ =
      d4x₅ K (σ s * σ (σ s) * t + σ (σ s * σ (σ s) * t) + σ (σ (σ s * σ (σ s) * t))) *
        d4x₄ K σ (σ s * σ (σ t) + σ (σ s) * σ t) *
          d4x₆ K (s * (σ t * σ (σ t)) + σ (s * (σ t * σ (σ t))) +
            σ (σ (s * (σ t * σ (σ t))))) := by
  rw [d4x₁_eq, d4x₃_eq, d4x₄_eq, d4x₅_eq, d4x₆_eq, ← coe_commutatorElement_d4,
    d43_comm04 (toRingHom_cube hσ)]
  rfl

theorem commute_d4x₁_d4x₅
    (s t : K) : Commute (d4x₁ K σ s) (d4x₅ K t) := by
  rw [d4x₁_eq, d4x₅_eq]
  exact (d43_commute01 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₁_d4x₆
    (s t : K) : Commute (d4x₁ K σ s) (d4x₆ K t) := by
  rw [d4x₁_eq, d4x₆_eq]
  exact (d43_commute03 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₅_d4x₄
    (s t : K) : Commute (d4x₅ K s) (d4x₄ K σ t) := by
  rw [d4x₅_eq, d4x₄_eq]
  exact (d43_commute12 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

variable (K) in
theorem commute_d4x₅_d4x₆
    (s t : K) : Commute (d4x₅ K s) (d4x₆ K t) := by
  rw [d4x₅_eq, d4x₆_eq]
  exact (d43_commute13 (K := K) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₅_d4x₃
    (s t : K) : Commute (d4x₅ K s) (d4x₃ K σ t) := by
  rw [d4x₅_eq, d4x₃_eq]
  exact (d43_commute14 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₄_d4x₆
    (s t : K) : Commute (d4x₄ K σ s) (d4x₆ K t) := by
  rw [d4x₄_eq, d4x₆_eq]
  exact (d43_commute23 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₄_d4x₂
    (s t : K) : Commute (d4x₄ K σ s) (d4x₂ K t) := by
  rw [d4x₄_eq, d4x₂_eq]
  exact (d43_commute25 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₆_d4x₃
    (s t : K) : Commute (d4x₆ K s) (d4x₃ K σ t) := by
  rw [d4x₆_eq, d4x₃_eq]
  exact (d43_commute34 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

variable (K) in
theorem commute_d4x₆_d4x₂
    (s t : K) : Commute (d4x₆ K s) (d4x₂ K t) := by
  rw [d4x₆_eq, d4x₂_eq]
  exact (d43_commute35 (K := K) s t).map (adjointGroup d4 K).subtype

theorem commute_d4x₃_d4x₂
    (s t : K) : Commute (d4x₃ K σ s) (d4x₂ K t) := by
  rw [d4x₃_eq, d4x₂_eq]
  exact (d43_commute45 (σ := σ.toRingHom) s t).map (adjointGroup d4 K).subtype

end Relations

section Additive

variable (σ : K ≃+* K)

theorem d4x₁_add
    (a b : K) : d4x₁ K σ (a + b) = d4x₁ K σ a * d4x₁ K σ b := by
  rw [d4x₁, d4x₁, d4x₁, trialityOrbitProd_add' (Or.inl rfl), Subgroup.coe_mul]

theorem d4x₃_add
    (a b : K) : d4x₃ K σ (a + b) = d4x₃ K σ a * d4x₃ K σ b := by
  rw [d4x₃, d4x₃, d4x₃, trialityOrbitProd_add' (Or.inr (Or.inl rfl)), Subgroup.coe_mul]

theorem d4x₄_add
    (a b : K) : d4x₄ K σ (a + b) = d4x₄ K σ a * d4x₄ K σ b := by
  rw [d4x₄, d4x₄, d4x₄, trialityOrbitProd_add' (Or.inr (Or.inr rfl)), Subgroup.coe_mul]

variable (K) in
theorem d4x₂_add
    (a b : K) : d4x₂ K (a + b) = d4x₂ K a * d4x₂ K b :=
  pinnedX_add _ _ _ a b

variable (K) in
theorem d4x₅_add
    (a b : K) : d4x₅ K (a + b) = d4x₅ K a * d4x₅ K b :=
  pinnedX_add _ _ _ a b

variable (K) in
theorem d4x₆_add
    (a b : K) : d4x₆ K (a + b) = d4x₆ K a * d4x₆ K b :=
  pinnedX_add _ _ _ a b

theorem d4x₁_zero :
    d4x₁ K σ 0 = 1 := by
  rw [d4x₁, coe_trialityOrbitProd]
  simp only [map_zero, pinnedX_zero, mul_one]

theorem d4x₃_zero :
    d4x₃ K σ 0 = 1 := by
  rw [d4x₃, coe_trialityOrbitProd]
  simp only [map_zero, pinnedX_zero, mul_one]

theorem d4x₄_zero :
    d4x₄ K σ 0 = 1 := by
  rw [d4x₄, coe_trialityOrbitProd]
  simp only [map_zero, pinnedX_zero, mul_one]

end Additive

section Weyl

variable [CharP K 2] (σ : K ≃+* K)

theorem conj_mul_three {G : Type*} [Group G] (n a b c : G) :
    n * (a * b * c) * n⁻¹ = n * a * n⁻¹ * (n * b * n⁻¹) * (n * c * n⁻¹) := by
  group

theorem isRoot_neg_trialityRoot
    (j : Fin 6) (h : ℕ) :
    IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ h) (-trialityRoot j)) := by
  have hroot : ∀ j : Fin 6, ∀ h : Fin 3, ∃ k : Fin 24,
      TwistTag.D4.tag.rootCertificate.root k =
        permLattice (TwistTag.D4.perm ^ (h : ℕ)) (-trialityRoot j) := by
    decide +kernel
  have hper : TwistTag.D4.perm ^ h = TwistTag.D4.perm ^ (h % 3) := by
    have h3 : TwistTag.D4.perm ^ 3 = 1 := by decide
    conv_lhs => rw [← Nat.div_add_mod h 3, pow_add, pow_mul, h3, one_pow, one_mul]
  obtain ⟨k, hk⟩ := hroot j ⟨h % 3, Nat.mod_lt _ (by norm_num)⟩
  rw [hper]
  exact (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨k, k.2, hk⟩

theorem isRoot_neg_trialityRoot'
    (j : Fin 6) :
    IsRoot TwistTag.D4.tag (-trialityRoot j) :=
  isRoot_neg_trialityRoot j 0

theorem canonicalRep_conj_trialityOrbitProd
    (w : WeylGroup TwistTag.D4.tag)
    {α β : Fin TwistTag.D4.tag.rank → ℤ} (hα₀ : IsRoot TwistTag.D4.tag α)
    (hα₁ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α))
    (hα₂ : IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ 2) α)) (h₀ : w • α = β)
    (h₁ : w • permLattice TwistTag.D4.perm α = permLattice TwistTag.D4.perm β)
    (h₂ : w • permLattice (TwistTag.D4.perm ^ 2) α = permLattice (TwistTag.D4.perm ^ 2) β)
    (c : K) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
        (trialityOrbitProd K σ.toRingHom α c : ModGL TwistTag.D4.tag K) *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) K w)⁻¹ =
      (trialityOrbitProd K σ.toRingHom β c : ModGL TwistTag.D4.tag K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd, conj_mul_three,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα₀,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα₁,
    canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hα₂, h₀, h₁, h₂]

theorem trialityOuterRep_conj_d4x₁
    (c : K) :
    trialityOuterRep K * d4x₁ K σ c * (trialityOuterRep K)⁻¹ = d4y₁ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 0 0).1 (isRoot_trialityRoot 0 1).1
    (isRoot_trialityRoot 0 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityOuterRep_conj_d4x₂
    (c : K) :
    trialityOuterRep K * d4x₂ K c * (trialityOuterRep K)⁻¹ = d4x₅ K c := by
  rw [d4x₂, d4x₅, trialityOuterRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_trialityRoot' 1)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityOuterRep_conj_d4x₃
    (c : K) :
    trialityOuterRep K * d4x₃ K σ c * (trialityOuterRep K)⁻¹ = d4x₄ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 2 0).1 (isRoot_trialityRoot 2 1).1
    (isRoot_trialityRoot 2 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityOuterRep_conj_d4x₄
    (c : K) :
    trialityOuterRep K * d4x₄ K σ c * (trialityOuterRep K)⁻¹ = d4x₃ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 3 0).1 (isRoot_trialityRoot 3 1).1
    (isRoot_trialityRoot 3 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityOuterRep_conj_d4x₅
    (c : K) :
    trialityOuterRep K * d4x₅ K c * (trialityOuterRep K)⁻¹ = d4x₂ K c := by
  rw [d4x₅, d4x₂, trialityOuterRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_trialityRoot' 4)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityOuterRep_conj_d4x₆
    (c : K) :
    trialityOuterRep K * d4x₆ K c * (trialityOuterRep K)⁻¹ = d4x₆ K c := by
  rw [d4x₆, trialityOuterRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_trialityRoot' 5)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityOuterRep_conj_d4y₂
    (c : K) :
    trialityOuterRep K * d4y₂ K c * (trialityOuterRep K)⁻¹ = d4y₅ K c := by
  rw [d4y₂, d4y₅, trialityOuterRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_neg_trialityRoot' 1)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityOuterRep_conj_d4y₃
    (c : K) :
    trialityOuterRep K * d4y₃ K σ c * (trialityOuterRep K)⁻¹ = d4y₄ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_neg_trialityRoot 2 0) (isRoot_neg_trialityRoot 2
      1)
    (isRoot_neg_trialityRoot 2 2)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityOuterRep_conj_d4y₅
    (c : K) :
    trialityOuterRep K * d4y₅ K c * (trialityOuterRep K)⁻¹ = d4y₂ K c := by
  rw [d4y₅, d4y₂, trialityOuterRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_neg_trialityRoot' 4)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityOuterRep_conj_d4y₆
    (c : K) :
    trialityOuterRep K * d4y₆ K c * (trialityOuterRep K)⁻¹ = d4y₆ K c := by
  rw [d4y₆, trialityOuterRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_neg_trialityRoot' 5)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityMiddleRep_conj_d4x₁
    (c : K) :
    trialityMiddleRep K * d4x₁ K σ c * (trialityMiddleRep K)⁻¹ = d4x₃ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 0 0).1 (isRoot_trialityRoot 0 1).1
    (isRoot_trialityRoot 0 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityMiddleRep_conj_d4x₂
    (c : K) :
    trialityMiddleRep K * d4x₂ K c * (trialityMiddleRep K)⁻¹ = d4y₂ K c := by
  rw [d4x₂, d4y₂, trialityMiddleRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_trialityRoot' 1)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityMiddleRep_conj_d4x₃
    (c : K) :
    trialityMiddleRep K * d4x₃ K σ c * (trialityMiddleRep K)⁻¹ = d4x₁ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 2 0).1 (isRoot_trialityRoot 2 1).1
    (isRoot_trialityRoot 2 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityMiddleRep_conj_d4x₄
    (c : K) :
    trialityMiddleRep K * d4x₄ K σ c * (trialityMiddleRep K)⁻¹ = d4x₄ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_trialityRoot 3 0).1 (isRoot_trialityRoot 3 1).1
    (isRoot_trialityRoot 3 2).1
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityMiddleRep_conj_d4x₅
    (c : K) :
    trialityMiddleRep K * d4x₅ K c * (trialityMiddleRep K)⁻¹ = d4x₆ K c := by
  rw [d4x₅, d4x₆, trialityMiddleRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_trialityRoot' 4)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityMiddleRep_conj_d4x₆
    (c : K) :
    trialityMiddleRep K * d4x₆ K c * (trialityMiddleRep K)⁻¹ = d4x₅ K c := by
  rw [d4x₆, d4x₅, trialityMiddleRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_trialityRoot' 5)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityMiddleRep_conj_d4y₁
    (c : K) :
    trialityMiddleRep K * d4y₁ K σ c * (trialityMiddleRep K)⁻¹ = d4y₃ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_neg_trialityRoot 0 0) (isRoot_neg_trialityRoot 0
      1)
    (isRoot_neg_trialityRoot 0 2)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityMiddleRep_conj_d4y₂
    (c : K) :
    trialityMiddleRep K * d4y₂ K c * (trialityMiddleRep K)⁻¹ = d4x₂ K c := by
  rw [d4y₂, d4x₂, trialityMiddleRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_neg_trialityRoot' 1)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityMiddleRep_conj_d4y₄
    (c : K) :
    trialityMiddleRep K * d4y₄ K σ c * (trialityMiddleRep K)⁻¹ = d4y₄ K σ c :=
  canonicalRep_conj_trialityOrbitProd σ _ (isRoot_neg_trialityRoot 3 0) (isRoot_neg_trialityRoot 3
      1)
    (isRoot_neg_trialityRoot 3 2)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel)
    (by rw [TwistTag.orbitReflection_smul]; decide +kernel) c

theorem trialityMiddleRep_conj_d4y₅
    (c : K) :
    trialityMiddleRep K * d4y₅ K c * (trialityMiddleRep K)⁻¹ = d4y₆ K c := by
  rw [d4y₅, d4y₆, trialityMiddleRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_neg_trialityRoot' 4)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

theorem trialityMiddleRep_conj_d4y₆
    (c : K) :
    trialityMiddleRep K * d4y₆ K c * (trialityMiddleRep K)⁻¹ = d4y₅ K c := by
  rw [d4y₆, d4y₅, trialityMiddleRep, canonicalRep_mul_pinnedX_mul_inv_of_two
    CharTwo.two_eq_zero _ (isRoot_neg_trialityRoot' 5)]
  congr 1
  rw [TwistTag.orbitReflection_smul]
  decide +kernel

end Weyl

section Mem

variable [CharP K 2] (σ : K ≃+* K) (hσ : σ.toRingHom ^ 3 = 1)

theorem twistHom_orbitTriple
    {α : Fin TwistTag.D4.tag.rank → ℤ}
    (h₀ : IsRoot TwistTag.D4.tag α) (h₁ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α))
    (h₂ : IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ 2) α))
    (ho₁ : α ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ permLattice TwistTag.D4.perm α) = 0)
    (ho₂ : α ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ permLattice (TwistTag.D4.perm ^ 2) α) = 0)
    (hσ : σ.toRingHom ^ 3 = 1) (c : K) :
    twistHom TwistTag.D4 K σ.toRingHom
        (trialityOrbitProd K σ.toRingHom α c : ModGL TwistTag.D4.tag K) =
      (trialityOrbitProd K σ.toRingHom α c : ModGL TwistTag.D4.tag K) := by
  rw [coe_trialityOrbitProd, map_mul, map_mul, even_diagram_root_parameters _ _ h₀,
    even_diagram_root_parameters _ _ h₁, even_diagram_root_parameters _ _ h₂,
    permLattice_D4_perm_perm, permLattice_D4_perm_perm_sq,
    ringHom_apply_apply_apply_of_pow_three hσ]
  have c₁ := commute_pinnedX_of_rootForm_eq_zero K h₀ h₁ ho₁ c (σ.toRingHom c)
  have c₂ := commute_pinnedX_of_rootForm_eq_zero K h₀ h₂ ho₂ c (σ.toRingHom (σ.toRingHom c))
  rw [mul_assoc, ← c₂.eq, ← mul_assoc, ← c₁.eq]

include hσ in
theorem d4x_short_mem
    (c : K) :
    d4x₁ K σ c ∈ d4C K σ ∧ d4x₃ K σ c ∈ d4C K σ ∧ d4x₄ K σ c ∈ d4C K σ := by
  have h : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
      (trialityOrbitProd K σ.toRingHom (trialityRoot j) c : ModGL TwistTag.D4.tag K) ∈
        d4C K σ := fun j hj =>
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (rootSpan_trialityOrbit_le j (trialityOrbitProd_mem hj hσ c))
  exact ⟨h 0 (Or.inl rfl), h 2 (Or.inr (Or.inl rfl)), h 3 (Or.inr (Or.inr rfl))⟩

theorem d4x_long_mem
    {c : K} (hc : σ c = c) :
    d4x₂ K c ∈ d4C K σ ∧ d4x₅ K c ∈ d4C K σ ∧ d4x₆ K c ∈ d4C K σ := by
  have h : ∀ j : Fin 6, (j = 1 ∨ j = 4 ∨ j = 5) →
      pinnedX TwistTag.D4.tag K (trialityRoot j) c ∈ d4C K σ := fun j hj =>
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (rootSpan_trialityOrbit_le j (pinnedX_trialityRoot_mem (σ := σ.toRingHom) hj
        (⟨c, hc⟩ : trialityFixedField K σ.toRingHom)))
  exact ⟨h 1 (Or.inl rfl), h 4 (Or.inr (Or.inl rfl)), h 5 (Or.inr (Or.inr rfl))⟩

omit [CharP K 2] in
theorem pinnedX_mem_negUnipotent_d4
    {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (hneg : height α < 0) (c : K) :
    pinnedX TwistTag.D4.tag K α c ∈ negUnipotent TwistTag.D4.tag K :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ height α < 0}) ⟨hα, hneg⟩ c

theorem height_neg_trialityRoot
    (j : Fin 6) (h : Fin 3) :
    height (permLattice (TwistTag.D4.perm ^ (h : ℕ)) (-trialityRoot j)) < 0 := by
  revert j h
  decide +kernel

theorem neg_trialityRoot_orthogonal
    : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
    (-trialityRoot j) ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ
        permLattice TwistTag.D4.perm (-trialityRoot j)) = 0 ∧
      (-trialityRoot j) ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ
        permLattice (TwistTag.D4.perm ^ 2) (-trialityRoot j)) = 0 := by
  decide +kernel

include hσ in
theorem d4y_short_mem
    (c : K) :
    d4y₁ K σ c ∈ d4C K σ ∧ d4y₃ K σ c ∈ d4C K σ ∧ d4y₄ K σ c ∈ d4C K σ := by
  have h : ∀ j : Fin 6, (j = 0 ∨ j = 2 ∨ j = 3) →
      (trialityOrbitProd K σ.toRingHom (-trialityRoot j) c : ModGL TwistTag.D4.tag K) ∈
        d4C K σ := by
    intro j hj
    refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · rw [coe_trialityOrbitProd]
      refine mul_mem (mul_mem ?_ ?_) ?_
      · exact pinnedX_mem_negUnipotent_d4 (isRoot_neg_trialityRoot j 0)
          (height_neg_trialityRoot j 0) _
      · exact pinnedX_mem_negUnipotent_d4 (isRoot_neg_trialityRoot j 1)
          (height_neg_trialityRoot j 1) _
      · exact pinnedX_mem_negUnipotent_d4 (isRoot_neg_trialityRoot j 2)
          (height_neg_trialityRoot j 2) _
    · refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨(trialityOrbitProd K _ _ c).2, ?_⟩
      exact twistHom_orbitTriple σ (isRoot_neg_trialityRoot j 0) (isRoot_neg_trialityRoot j 1)
        (isRoot_neg_trialityRoot j 2) (neg_trialityRoot_orthogonal j hj).1
        (neg_trialityRoot_orthogonal j hj).2 hσ c
  exact ⟨h 0 (Or.inl rfl), h 2 (Or.inr (Or.inl rfl)), h 3 (Or.inr (Or.inr rfl))⟩

theorem d4y_long_mem
    {c : K} (hc : σ c = c) :
    d4y₂ K c ∈ d4C K σ ∧ d4y₅ K c ∈ d4C K σ ∧ d4y₆ K c ∈ d4C K σ := by
  have hfix : ∀ j : Fin 6, (j = 1 ∨ j = 4 ∨ j = 5) →
      permLattice TwistTag.D4.perm (-trialityRoot j) = -trialityRoot j := by
    decide +kernel
  have h : ∀ j : Fin 6, (j = 1 ∨ j = 4 ∨ j = 5) →
      pinnedX TwistTag.D4.tag K (-trialityRoot j) c ∈ d4C K σ := by
    intro j hj
    refine graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
      ⟨pinnedX_mem_negUnipotent_d4 (isRoot_neg_trialityRoot' j) (height_neg_trialityRoot j 0) c,
        ?_⟩)
    have := pinnedX_D4_mem_fixed (σ := σ.toRingHom) (isRoot_neg_trialityRoot' j) (hfix j hj)
      ⟨c, hc⟩
    exact (Subgroup.mem_inf.1 this).2
  exact ⟨h 1 (Or.inl rfl), h 4 (Or.inr (Or.inl rfl)), h 5 (Or.inr (Or.inr rfl))⟩

omit [CharP K 2] in
theorem trialityRep_mem
    : trialityOuterRep K ∈ d4C K σ ∧ trialityMiddleRep K ∈ d4C K σ :=
  ⟨canonicalRep_mem_graphFixedRootGroup (σ := σ.toRingHom) (TwistTag.D4.orbitReflection_mem _),
    canonicalRep_mem_graphFixedRootGroup (σ := σ.toRingHom) (TwistTag.D4.orbitReflection_mem _)⟩

end Mem

section Torus

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (σ : K ≃+* K)

theorem rootChar_d4Tuple (x₀ x₁ x₂ x₃ : Kˣ) {v : Fin TwistTag.D4.tag.rank → ℤ} (n₀ n₁ n₂ n₃ : ℤ)
    (hv : v = (![n₀, n₁, n₂, n₃] : Fin 4 → ℤ)) :
    rootChar (d4Tuple x₀ x₁ x₂ x₃) v = x₀ ^ n₀ * x₁ ^ n₁ * x₂ ^ n₂ * x₃ ^ n₃ := by
  subst hv
  change ∏ i : Fin 4, (d4Tuple x₀ x₁ x₂ x₃ : Fin 4 → Kˣ) i ^ (![n₀, n₁, n₂, n₃] : Fin 4 → ℤ) i = _
  rw [Fin.prod_univ_four]
  rfl

theorem rootDiagUnit_conj_trialityOrbitProd
    (d : Fin TwistTag.D4.tag.rank → Kˣ)
    {α : Fin TwistTag.D4.tag.rank → ℤ} (hα₀ : IsRoot TwistTag.D4.tag α)
    (hα₁ : IsRoot TwistTag.D4.tag (permLattice TwistTag.D4.perm α))
    (hα₂ : IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ 2) α)) {χ : K}
    (h₀ : (rootChar d α : K) = χ) (h₁ : (rootChar d (permLattice TwistTag.D4.perm α) : K) = σ χ)
    (h₂ : (rootChar d (permLattice (TwistTag.D4.perm ^ 2) α) : K) = σ (σ χ)) (c : K) :
    rootDiagUnit TwistTag.D4.tag d *
        (trialityOrbitProd K σ.toRingHom α c : ModGL TwistTag.D4.tag K) *
        (rootDiagUnit TwistTag.D4.tag d)⁻¹ =
      (trialityOrbitProd K σ.toRingHom α (χ * c) : ModGL TwistTag.D4.tag K) := by
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd, conj_mul_three,
    rootDiagUnit_conj_pinnedX _ hα₀, rootDiagUnit_conj_pinnedX _ hα₁,
    rootDiagUnit_conj_pinnedX _ hα₂, h₀, h₁, h₂]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_mul]

section Outer

variable (hσ : ∀ c, σ (σ (σ c)) = c)

theorem ho_conj_d4x₁
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4x₁ K σ c * (trialityOuterTorus K σ a)⁻¹ =
      d4x₁ K σ ((a : K) ^ 2 * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4x₁, d4x₁]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (trialityRoot 0)) (isRoot_trialityRoot'
      0) (isRoot_trialityRoot 0 1).1
      (isRoot_trialityRoot 0 2).1
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (trialityRoot 0)) _ _ _ _ 1 0 0 0
        (by funext i; fin_cases i <;> decide)]
    simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (trialityRoot 0)) _ _ _ _ 0 1 0 0
        (by funext i; fin_cases i <;> decide)]
    simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 0)) _ _ _ _ 0 0 0 1
        (by funext i; fin_cases i <;> decide)]
    simp

theorem ho_conj_d4x₂
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4x₂ K c * (trialityOuterTorus K σ a)⁻¹ =
      d4x₂ K (((a : K) * σ a * σ (σ a))⁻¹ * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4x₂, d4x₂,
      rootDiagUnit_conj_pinnedX _ (isRoot_trialityRoot' 1),
    rootChar_d4Tuple (v := (trialityRoot 1)) _ _ _ _ 0 0 1 0
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp

include hσ in
theorem ho_conj_d4x₃
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4x₃ K σ c * (trialityOuterTorus K σ a)⁻¹ =
      d4x₃ K σ ((a : K) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4x₃, d4x₃]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (trialityRoot 2)) (isRoot_trialityRoot'
      2) (isRoot_trialityRoot 2 1).1
      (isRoot_trialityRoot 2 2).1
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (trialityRoot 2)) _ _ _ _ 1 0 1 0
        (by funext i; fin_cases i <;> decide)]
    simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (trialityRoot 2)) _ _ _ _ 0 1 1 0
        (by funext i; fin_cases i <;> decide)]
    simp [hσ]
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 2)) _ _ _ _ 0 0 1 1
        (by funext i; fin_cases i <;> decide)]
    simp [hσ]
    field_simp

include hσ in
theorem ho_conj_d4x₄
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4x₄ K σ c * (trialityOuterTorus K σ a)⁻¹ =
      d4x₄ K σ (σ a ^ 2 * σ (σ a) ^ 2 * ((a : K) * σ a * σ (σ a))⁻¹ * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4x₄, d4x₄]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (trialityRoot 3)) (isRoot_trialityRoot'
      3) (isRoot_trialityRoot 3 1).1
      (isRoot_trialityRoot 3 2).1
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (trialityRoot 3)) _ _ _ _ 0 1 1 1
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (trialityRoot 3)) _ _ _ _ 1 0 1 1
        (by funext i; fin_cases i <;> decide)]
    simp [hσ]
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3)) _ _ _ _ 1 1 1 0
        (by funext i; fin_cases i <;> decide)]
    simp [hσ]
    field_simp

theorem ho_conj_d4x₅
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4x₅ K c * (trialityOuterTorus K σ a)⁻¹ =
      d4x₅ K (((a : K) * σ a * σ (σ a)) * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4x₅, d4x₅,
      rootDiagUnit_conj_pinnedX _ (isRoot_trialityRoot' 4),
    rootChar_d4Tuple (v := (trialityRoot 4)) _ _ _ _ 1 1 1 1
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp
  field_simp

theorem ho_conj_d4x₆
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4x₆ K c * (trialityOuterTorus K σ a)⁻¹ =
      d4x₆ K c := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4x₆,
      rootDiagUnit_conj_pinnedX _ (isRoot_trialityRoot' 5),
    rootChar_d4Tuple (v := (trialityRoot 5)) _ _ _ _ 1 1 2 1
      (by funext i; fin_cases i <;> decide)]
  conv_rhs => rw [← one_mul c]
  congr 2
  simp
  field_simp

theorem ho_conj_d4y₂
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4y₂ K c * (trialityOuterTorus K σ a)⁻¹ =
      d4y₂ K ((((a : K) * σ a * σ (σ a))⁻¹)⁻¹ * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4y₂, d4y₂,
      rootDiagUnit_conj_pinnedX _ (isRoot_neg_trialityRoot' 1),
    rootChar_d4Tuple (v := (-trialityRoot 1)) _ _ _ _ 0 0 (-1) 0
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp

theorem ho_conj_d4y₅
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4y₅ K c * (trialityOuterTorus K σ a)⁻¹ =
      d4y₅ K ((((a : K) * σ a * σ (σ a)))⁻¹ * c) := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4y₅, d4y₅,
      rootDiagUnit_conj_pinnedX _ (isRoot_neg_trialityRoot' 4),
    rootChar_d4Tuple (v := (-trialityRoot 4)) _ _ _ _ (-1) (-1) (-1) (-1)
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp
  field_simp

theorem ho_conj_d4y₆
    (a : Kˣ) (c : K) :
    trialityOuterTorus K σ a * d4y₆ K c * (trialityOuterTorus K σ a)⁻¹ =
      d4y₆ K c := by
  rw [trialityOuterTorus_eq_rootDiagUnit, d4y₆,
      rootDiagUnit_conj_pinnedX _ (isRoot_neg_trialityRoot' 5),
    rootChar_d4Tuple (v := (-trialityRoot 5)) _ _ _ _ (-1) (-1) (-2) (-1)
      (by funext i; fin_cases i <;> decide)]
  conv_rhs => rw [← one_mul c]
  congr 2
  simp
  field_simp

end Outer

theorem hm_conj_d4x₁
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4x₁ K σ c * (trialityMiddleTorus K σ b)⁻¹ =
      d4x₁ K σ (((trialityFixedUnit K σ b : Kˣ) : K)⁻¹ * c) := by
  have hβ : σ ((trialityFixedUnit K σ b : Kˣ) : K) = ((trialityFixedUnit K σ b : Kˣ) : K) :=
    sigma_trialityFixedUnit b
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4x₁, d4x₁]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (trialityRoot 0)) (isRoot_trialityRoot'
      0) (isRoot_trialityRoot 0 1).1
      (isRoot_trialityRoot 0 2).1
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (trialityRoot 0)) _ _ _ _ 1 0 0 0
        (by funext i; fin_cases i <;> decide)]
    simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (trialityRoot 0)) _ _ _ _ 0 1 0 0
        (by funext i; fin_cases i <;> decide)]
    simp only [map_inv₀, hβ]
    simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 0)) _ _ _ _ 0 0 0 1
        (by funext i; fin_cases i <;> decide)]
    simp only [map_inv₀, hβ]
    simp

theorem hm_conj_d4x₂
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4x₂ K c * (trialityMiddleTorus K σ b)⁻¹ =
      d4x₂ K (((trialityFixedUnit K σ b : Kˣ) : K) ^ 2 * c) := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4x₂, d4x₂,
      rootDiagUnit_conj_pinnedX _ (isRoot_trialityRoot' 1),
    rootChar_d4Tuple (v := (trialityRoot 1)) _ _ _ _ 0 0 1 0
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp

theorem hm_conj_d4x₃
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4x₃ K σ c * (trialityMiddleTorus K σ b)⁻¹ =
      d4x₃ K σ (((trialityFixedUnit K σ b : Kˣ) : K) * c) := by
  have hβ : σ ((trialityFixedUnit K σ b : Kˣ) : K) = ((trialityFixedUnit K σ b : Kˣ) : K) :=
    sigma_trialityFixedUnit b
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4x₃, d4x₃]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (trialityRoot 2)) (isRoot_trialityRoot'
      2) (isRoot_trialityRoot 2 1).1
      (isRoot_trialityRoot 2 2).1
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (trialityRoot 2)) _ _ _ _ 1 0 1 0
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (trialityRoot 2)) _ _ _ _ 0 1 1 0
        (by funext i; fin_cases i <;> decide)]
    simp only [hβ]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 2)) _ _ _ _ 0 0 1 1
        (by funext i; fin_cases i <;> decide)]
    simp only [hβ]
    simp
    field_simp

theorem hm_conj_d4x₄
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4x₄ K σ c * (trialityMiddleTorus K σ b)⁻¹ =
      d4x₄ K σ c := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4x₄]
  conv_rhs => rw [← one_mul c]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (trialityRoot 3)) (isRoot_trialityRoot'
      3) (isRoot_trialityRoot 3 1).1
      (isRoot_trialityRoot 3 2).1
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (trialityRoot 3)) _ _ _ _ 0 1 1 1
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (trialityRoot 3)) _ _ _ _ 1 0 1 1
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (trialityRoot 3)) _ _ _ _ 1 1 1 0
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp

theorem hm_conj_d4x₅
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4x₅ K c * (trialityMiddleTorus K σ b)⁻¹ =
      d4x₅ K (((trialityFixedUnit K σ b : Kˣ) : K)⁻¹ * c) := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4x₅, d4x₅,
      rootDiagUnit_conj_pinnedX _ (isRoot_trialityRoot' 4),
    rootChar_d4Tuple (v := (trialityRoot 4)) _ _ _ _ 1 1 1 1
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp
  field_simp

theorem hm_conj_d4x₆
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4x₆ K c * (trialityMiddleTorus K σ b)⁻¹ =
      d4x₆ K (((trialityFixedUnit K σ b : Kˣ) : K) * c) := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4x₆, d4x₆,
      rootDiagUnit_conj_pinnedX _ (isRoot_trialityRoot' 5),
    rootChar_d4Tuple (v := (trialityRoot 5)) _ _ _ _ 1 1 2 1
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp
  field_simp

theorem hm_conj_d4y₁
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4y₁ K σ c * (trialityMiddleTorus K σ b)⁻¹ =
      d4y₁ K σ ((((trialityFixedUnit K σ b : Kˣ) : K)⁻¹)⁻¹ * c) := by
  have hβ : σ ((trialityFixedUnit K σ b : Kˣ) : K) = ((trialityFixedUnit K σ b : Kˣ) : K) :=
    sigma_trialityFixedUnit b
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4y₁, d4y₁]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (-trialityRoot 0)) (isRoot_neg_trialityRoot'
      0) (isRoot_neg_trialityRoot 0 1)
      (isRoot_neg_trialityRoot 0 2)
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (-trialityRoot 0)) _ _ _ _ (-1) 0 0 0
        (by funext i; fin_cases i <;> decide)]
    simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (-trialityRoot 0)) _ _ _ _ 0 (-1) 0 0
        (by funext i; fin_cases i <;> decide)]
    simp only [map_inv₀, hβ]
    simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (-trialityRoot 0)) _ _ _ _ 0 0 0
      (-1)
        (by funext i; fin_cases i <;> decide)]
    simp only [map_inv₀, hβ]
    simp

theorem hm_conj_d4y₂
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4y₂ K c * (trialityMiddleTorus K σ b)⁻¹ =
      d4y₂ K ((((trialityFixedUnit K σ b : Kˣ) : K) ^ 2)⁻¹ * c) := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4y₂, d4y₂,
      rootDiagUnit_conj_pinnedX _ (isRoot_neg_trialityRoot' 1),
    rootChar_d4Tuple (v := (-trialityRoot 1)) _ _ _ _ 0 0 (-1) 0
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp

theorem hm_conj_d4y₄
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4y₄ K σ c * (trialityMiddleTorus K σ b)⁻¹ =
      d4y₄ K σ c := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4y₄]
  conv_rhs => rw [← one_mul c]
  refine rootDiagUnit_conj_trialityOrbitProd σ _ (α := (-trialityRoot 3)) (isRoot_neg_trialityRoot'
      3) (isRoot_neg_trialityRoot 3 1)
      (isRoot_neg_trialityRoot 3 2)
    ?_ ?_ ?_ c
  · rw [rootChar_d4Tuple (v := (-trialityRoot 3)) _ _ _ _ 0 (-1) (-1) (-1)
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice TwistTag.D4.perm (-trialityRoot 3)) _ _ _ _ (-1) 0 (-1)
      (-1)
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp
  · rw [rootChar_d4Tuple (v := permLattice (TwistTag.D4.perm ^ 2) (-trialityRoot 3)) _ _ _ _ (-1)
      (-1) (-1) 0
        (by funext i; fin_cases i <;> decide)]
    simp
    field_simp

theorem hm_conj_d4y₅
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4y₅ K c * (trialityMiddleTorus K σ b)⁻¹ =
      d4y₅ K ((((trialityFixedUnit K σ b : Kˣ) : K)⁻¹)⁻¹ * c) := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4y₅, d4y₅,
      rootDiagUnit_conj_pinnedX _ (isRoot_neg_trialityRoot' 4),
    rootChar_d4Tuple (v := (-trialityRoot 4)) _ _ _ _ (-1) (-1) (-1) (-1)
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp
  field_simp

theorem hm_conj_d4y₆
    (b : (trialityFixedField K σ.toRingHom)ˣ) (c : K) :
    trialityMiddleTorus K σ b * d4y₆ K c * (trialityMiddleTorus K σ b)⁻¹ =
      d4y₆ K ((((trialityFixedUnit K σ b : Kˣ) : K))⁻¹ * c) := by
  rw [trialityMiddleTorus_eq_rootDiagUnit, d4y₆, d4y₆,
      rootDiagUnit_conj_pinnedX _ (isRoot_neg_trialityRoot' 5),
    rootChar_d4Tuple (v := (-trialityRoot 5)) _ _ _ _ (-1) (-1) (-2) (-1)
      (by funext i; fin_cases i <;> decide)]
  congr 2
  simp
  field_simp

end Torus

end CFSG.ComponentClassification.RankTwoExceptional.D4
