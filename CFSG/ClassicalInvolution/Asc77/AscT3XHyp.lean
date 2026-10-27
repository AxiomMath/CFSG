module

public import CFSG.ClassicalInvolution.Asc77.AscT3XCore
public import CFSG.ClassicalInvolution.AschTight.S1911SecE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.x_coe_eq_of_isUniqueInvolution (d : Std20 p f K K' J S R R' W V z t) {a : G}
    (c : ↥(Subgroup.centralizer ({a} : Set G))) {u : ↥(Subgroup.centralizer ({a} : Set G))}
    (hu : IsUniqueInvolution (conjSub c (perfectCoreIn K a)) u) :
    (u : G) = (c : G) * z * (c : G)⁻¹ := by
  have hI := d.viol.hzK.conj (c : G)
  have hsq : (u : G) * u = 1 := congrArg Subtype.val hu.sq
  have hne : (u : G) ≠ 1 := fun h => hu.ne_one (Subtype.ext h)
  exact (hI.unique _ (le_conjSub_of_mem c hu.mem) hsq).resolve_left hne

theorem Std20.x_omega5_conjFamily (d : Std20 p f K K' J S R R' W V z t) (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a),
    ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hΩ := d.hyp
  have hI := d.viol.hzK
  have hJne := conjSub_ne_of_ne hne
  have hu' := d.x_coe_eq_of_isUniqueInvolution c₁ hu
  have hvJ := le_conjSub_of_mem c₂ hv
  have hnc' : ¬ ∀ w ∈ conjSub (c₂ : G) K, (v : G) * w = w * v := by
    intro h
    apply hnc
    intro w hw
    exact Subtype.ext (h _ (le_conjSub_of_mem c₂ hw))
  have h2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    have := h2.map (Subgroup.centralizer ({a} : Set G)).subtype
    rwa [MonoidHom.map_zpowers] at this
  have hvz : (v : G) * ((c₁ : G) * z * (c₁ : G)⁻¹) = ((c₁ : G) * z * (c₁ : G)⁻¹) * v := by
    rw [← hu']
    exact congrArg Subtype.val hvu
  have hN := hΩ.omega5 _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hJne _ (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of c₁ v hN

theorem Std20.x_omega4_conjFamily (d : Std20 p f K K' J S R R' W V z t) (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a), ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := d.hyp
  have hJne := conjSub_ne_of_ne hne
  obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hJne
  have hdvd : Nat.card ↥(conjSub c₁ (perfectCoreIn K a) ⊓ conjSub c₂ (perfectCoreIn K a)) ∣
      Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K) := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨le_conjSub_of_mem c₁ hx.1, le_conjSub_of_mem c₂ hx.2⟩
  have hval : padicValNat 2 (Nat.card ↥(conjSub c₁ (perfectCoreIn K a) ⊓
      conjSub c₂ (perfectCoreIn K a))) ≤
        padicValNat 2 (Nat.card ↥(conjSub (c₁ : G) K ⊓ conjSub (c₂ : G) K)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (pow_padicValNat_dvd.trans hdvd)
  refine ⟨hval.trans h4a, fun h1 => ?_⟩
  have hc := h4b (le_antisymm h4a (h1 ▸ hval))
  refine le_inf (commutator_le_oddCoreOf_conjFamily c₁ c₂ (hc.trans inf_le_left)) ?_
  rw [Subgroup.commutator_comm]
  refine commutator_le_oddCoreOf_conjFamily c₂ c₁ ?_
  rw [Subgroup.commutator_comm]
  exact hc.trans inf_le_right

theorem Std20.x_hypOmegaMod_conjFamily (d : Std20 p f K K' J S R R' W V z t) {a : G} {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hL.conj g⟩
  omega4 := d.x_omega4_conjFamily a
  omega5 := d.x_omega5_conjFamily a

theorem Std20.x_lieSystemMod [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) (h9 : p ^ f ≠ 9) {b : G}
    (hb : FieldInv20 S K K' W z t b) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧ ∃ hzA : z ∈ Subgroup.centralizer ({b} : Set G),
      IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzA⟩ ∧
      HypOmegaMod p e₀ (conjFamily (perfectCoreIn K b)) ∧
      LieSystemMod p e₀ (restrictFamily (conjFamily (perfectCoreIn K b))
        (conjGen (perfectCoreIn K b))) := by
  obtain ⟨e₀, hfe, h5, hzA, hmem, hlt, hIH⟩ := d.x_sectionData c9 h8 h9 hb
  exact ⟨e₀, hfe, h5, hzA, hmem, d.x_hypOmegaMod_conjFamily hzA hmem,
    lieSystemMod_restrict_conjugates hmem hlt hIH⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
