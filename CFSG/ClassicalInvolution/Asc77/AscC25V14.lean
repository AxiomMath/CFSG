module

public import CFSG.ClassicalInvolution.Asc77.AscC25V13
public import CFSG.ClassicalInvolution.AschTight.S1911SecE

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Hyp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


theorem fs_coe_eq_of_isUniqueInvolution (hI : IsUniqueInvolution K z) {a : G}
    (c : ↥(Subgroup.centralizer ({a} : Set G))) {u : ↥(Subgroup.centralizer ({a} : Set G))}
    (hu : IsUniqueInvolution (conjSub c (perfectCoreIn K a)) u) :
    (u : G) = (c : G) * z * (c : G)⁻¹ := by
  have hI' := hI.conj (c : G)
  have hsq : (u : G) * u = 1 := congrArg Subtype.val hu.sq
  have hne : (u : G) ≠ 1 := fun h => hu.ne_one (Subtype.ext h)
  exact (hI'.unique _ (le_conjSub_of_mem c hu.mem) hsq).resolve_left hne

theorem fs_omega5_conjFamily (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (hI : IsUniqueInvolution K z)
    (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a),
    ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
    ∀ u : ↥(Subgroup.centralizer ({a} : Set G)), IsUniqueInvolution M₁ u → ∀ v ∈ M₂,
      (¬ ∀ w ∈ M₂, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * u = u * v →
        v ∈ Subgroup.normalizer (M₁ : Set ↥(Subgroup.centralizer ({a} : Set G))) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne u hu v hv hnc h2 hvu
  have hJne := conjSub_ne_of_ne hne
  have hu' := fs_coe_eq_of_isUniqueInvolution hI c₁ hu
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
  have hN := hΩ.omega5 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne _
    (hI.conj (c₁ : G)) _ hvJ hnc' h2' hvz
  exact mem_normalizer_conjSub_of c₁ v hN

theorem fs_omega4_conjFamily (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω) (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a), ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJne := conjSub_ne_of_ne hne
  obtain ⟨h4a, h4b⟩ := hΩ.omega4 _ (hΩ.conjInvariant c₁ K hK) _ (hΩ.conjInvariant c₂ K hK) hJne
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

theorem fs_hypOmegaMod_conjFamily (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω)
    (hI : IsUniqueInvolution K z) {a : G} {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hL.conj g⟩
  omega4 := fs_omega4_conjFamily hΩ hK a
  omega5 := fs_omega5_conjFamily hΩ hK hI a

theorem fs_sectionData [IsSimpleGroup G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    {e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)} {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) (hI : IsUniqueInvolution K z)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K = K → conjSub (y * x * y⁻¹) K = K)
    (hnc : ∃ x y : G, x * y ≠ y * x) (hzb : z ∈ Subgroup.centralizer ({b} : Set G))
    (hbelow : CITBelowAll p (Nat.card G)) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzb⟩ ∧
      Nat.card ↥(Subgroup.centralizer ({b} : Set G)) < Nat.card G ∧
      CITBelowU p e₀ (Nat.card G) := by
  obtain ⟨e₀, hfe, h5, hiso⟩ := fs_exists_quotEquiv hp hq h9 e hbN hb2 hσ1
  exact ⟨e₀, hfe, h5, fs_isClassicalMember hI hKz hconj hp hzb hiso,
    fs_card_centralizer_lt hnc hb1, hbelow e₀ h5⟩

theorem fs_lieSystemMod [IsSimpleGroup G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (hΩ : HypOmegaMod p f Ω) (hK : K ∈ Ω)
    {e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)} {b : G}
    (hbN : b ∈ Subgroup.normalizer (K : Set G)) (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hσ1 : fieldChar hp hq e ⟨b, hbN⟩ ≠ 1) (hI : IsUniqueInvolution K z)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K = K → conjSub (y * x * y⁻¹) K = K)
    (hnc : ∃ x y : G, x * y ≠ y * x) (hzb : z ∈ Subgroup.centralizer ({b} : Set G))
    (hbelow : CITBelowAll p (Nat.card G)) :
    ∃ e₀ : ℕ, f = 2 * e₀ ∧ 5 ≤ p ^ e₀ ∧
      IsClassicalMember p e₀ (perfectCoreIn K b) ⟨z, hzb⟩ ∧
      HypOmegaMod p e₀ (conjFamily (perfectCoreIn K b)) ∧
      LieSystemMod p e₀ (restrictFamily (conjFamily (perfectCoreIn K b))
        (conjGen (perfectCoreIn K b))) := by
  obtain ⟨e₀, hfe, h5, hmem, hlt, hIH⟩ :=
    fs_sectionData hp hq h9 hbN hb2 hb1 hσ1 hI hKz hconj hnc hzb hbelow
  exact ⟨e₀, hfe, h5, hmem, fs_hypOmegaMod_conjFamily hΩ hK hI hzb hmem,
    lieSystemMod_restrict_conjugates hmem hlt hIH⟩

end Hyp

end CFSG.ClassicalInvolution.Asc77.C25V
