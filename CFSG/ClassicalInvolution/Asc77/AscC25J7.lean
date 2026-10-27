module

public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25I8
public import CFSG.ClassicalInvolution.Asc77.AscR10T9b

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Omega

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem crossIn_isUniqueInvolution_conjSub (hI : IsUniqueInvolution K z) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ K ⊓ Subgroup.centralizer ({a} : Set G))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (crossIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI := hI.conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI.ne_one (congrArg Subtype.val h), Subtype.ext hI.sq, fun y hy hy2 => ?_⟩
  rcases hI.unique _ (le_conjSub_of_mem_cross c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem crossIn_coe_eq_of_isUniqueInvolution (hI : IsUniqueInvolution K z) {a : G}
    (c : ↥(Subgroup.centralizer ({a} : Set G))) {u : ↥(Subgroup.centralizer ({a} : Set G))}
    (hu : IsUniqueInvolution (conjSub c (crossIn K a)) u) :
    (u : G) = (c : G) * z * (c : G)⁻¹ := by
  have hI := hI.conj (c : G)
  have hsq : (u : G) * u = 1 := congrArg Subtype.val hu.sq
  have hne : (u : G) ≠ 1 := fun h => hu.ne_one (Subtype.ext h)
  exact (hI.unique _ (le_conjSub_of_mem_cross c hu.mem) hsq).resolve_left hne

theorem crossIn_omega5_conjFamily (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω)
    (hI : IsUniqueInvolution K z) (a : G) :
    ∀ M₁ ∈ conjFamily (crossIn K a),
    ∀ M₂ ∈ conjFamily (crossIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hJne := conjSub_ne_of_ne_cross hne
  have hu' := crossIn_coe_eq_of_isUniqueInvolution hI c₁ hu
  have hvJ := le_conjSub_of_mem_cross c₂ hv
  have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
    intro h
    apply hnc
    intro w hw
    exact Subtype.ext (h _ (le_conjSub_of_mem_cross c₂ hw))
  have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    have := h2.map (Subgroup.centralizer ({a} : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
    rw [← hu']
    exact congrArg Subtype.val hvu
  have hN := hΩ.omega5 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne _
    (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of_cross c₁ v hN

theorem crossIn_omega4_conjFamily (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (a : G) :
    ∀ M₁ ∈ conjFamily (crossIn K a), ∀ M₂ ∈ conjFamily (crossIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJne := conjSub_ne_of_ne_cross hne
  obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne
  have hdvd : Nat.card ↥(conjSub c₁ (crossIn K a) ⊓ conjSub c₂ (crossIn K a)) ∣
      Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨le_conjSub_of_mem_cross c₁ hx.1, le_conjSub_of_mem_cross c₂ hx.2⟩
  have hval : padicValNat 2 (Nat.card ↥(conjSub c₁ (crossIn K a) ⊓
      conjSub c₂ (crossIn K a))) ≤
        padicValNat 2 (Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (pow_padicValNat_dvd.trans hdvd)
  refine ⟨hval.trans h4a, fun h1 => ?_⟩
  have hc := h4b (le_antisymm h4a (h1 ▸ hval))
  refine le_inf (commutator_le_oddCoreOf_conjFamily_cross c₁ c₂ (hc.trans inf_le_left)) ?_
  rw [Subgroup.commutator_comm]
  refine commutator_le_oddCoreOf_conjFamily_cross c₂ c₁ ?_
  rw [Subgroup.commutator_comm]
  exact hc.trans inf_le_right

theorem crossIn_hypOmegaModU (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (hI : IsUniqueInvolution K z)
    {b : G} (hzA : z ∈ Subgroup.centralizer ({b} : Set G))
    (hL : IsClassicalMemberU (.sl2 3 1) (crossIn K b) ⟨z, hzA⟩) :
    HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K b)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hL.conj g⟩
  omega4 := crossIn_omega4_conjFamily hΩ hK b
  omega5 := crossIn_omega5_conjFamily hΩ hK hI b

end Omega

end CFSG.ClassicalInvolution.Asc77.C25J
