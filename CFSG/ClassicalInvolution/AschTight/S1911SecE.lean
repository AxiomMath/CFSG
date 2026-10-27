module

public import CFSG.ClassicalInvolution.AschTight.S1911SecD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem le_oddCoreOf_of_le_of_odd {Y : Type} [Group Y] {M N : Subgroup Y} (hNM : N ≤ M)
    (hn : M ≤ Subgroup.normalizer (N : Set Y)) (hodd : Odd (Nat.card N)) : N ≤ oddCoreOf M := by
  have hnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hn
  have hodd' : Odd (Nat.card ↥(N.subgroupOf M)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
  have hle : N.subgroupOf M ≤ classicalInvolutionOddCore ↥M := by
    unfold classicalInvolutionOddCore
    exact le_sSup ⟨hnorm, hodd'⟩
  intro x hx
  exact ⟨⟨x, hNM hx⟩, hle hx, rfl⟩

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

omit [IsSimpleGroup G] in
theorem commutator_le_oddCoreOf_conjFamily {a : G} (c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G)))
    (h : ⁅conjSub (c₁ : G) K, conjSub (c₂ : G) K⁆ ≤ oddCoreOf (conjSub (c₁ : G) K)) :
    ⁅conjSub c₁ (perfectCoreIn K a), conjSub c₂ (perfectCoreIn K a)⁆ ≤
      oddCoreOf (conjSub c₁ (perfectCoreIn K a)) := by
  have hOJ : oddCoreOf (conjSub (c₁ : G) K) ≤ conjSub (c₁ : G) K := Subgroup.map_subtype_le _
  have key : ∀ y ∈ conjSub (c₂ : G) K, ∀ w ∈ conjSub (c₁ : G) K,
      y * w * y⁻¹ ∈ conjSub (c₁ : G) K := by
    intro y hy w hw
    have hc : ⁅y, w⁆ ∈ conjSub (c₁ : G) K := hOJ (h (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hy hw))
    have e : y * w * y⁻¹ = ⁅y, w⁆ * w := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ hc hw
  have hJN : ∀ y ∈ conjSub (c₂ : G) K, y ∈ Subgroup.normalizer ((conjSub (c₁ : G) K : Subgroup G) :
      Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact key y hy w
    · intro hw
      have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hw
      simpa [mul_assoc] using this
  have hMN : ∀ y ∈ conjSub c₂ (perfectCoreIn K a), y ∈ Subgroup.normalizer
      ((conjSub c₁ (perfectCoreIn K a) : Subgroup ↥(Subgroup.centralizer ({a} : Set G))) :
        Set ↥(Subgroup.centralizer ({a} : Set G))) :=
    fun y hy => mem_normalizer_conjSub_of c₁ y (hJN _ (le_conjSub_of_mem c₂ hy))
  have hcomm : ⁅conjSub c₁ (perfectCoreIn K a), conjSub c₂ (perfectCoreIn K a)⁆ ≤
      conjSub c₁ (perfectCoreIn K a) ⊓
        (oddCoreOf (conjSub (c₁ : G) K)).comap (Subgroup.centralizer ({a} : Set G)).subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨?_, ?_⟩
    · have h1 : g₂ * g₁⁻¹ * g₂⁻¹ ∈ conjSub c₁ (perfectCoreIn K a) :=
        (Subgroup.mem_normalizer_iff.mp (hMN g₂ hg₂) _).mp (Subgroup.inv_mem _ hg₁)
      have e : ⁅g₁, g₂⁆ = g₁ * (g₂ * g₁⁻¹ * g₂⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.mul_mem _ hg₁ h1
    · have h2 := h (Subgroup.commutator_mem_commutator (le_conjSub_of_mem c₁ hg₁)
        (le_conjSub_of_mem c₂ hg₂))
      rw [commutatorElement_def] at h2 ⊢
      exact h2
  refine hcomm.trans (le_oddCoreOf_of_le_of_odd inf_le_left ?_ ?_)
  · intro m hm
    have hmN : (m : G) ∈ Subgroup.normalizer ((oddCoreOf (conjSub (c₁ : G) K) : Subgroup G) :
        Set G) :=
      mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer (le_conjSub_of_mem c₁ hm))
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hx1) (Subgroup.inv_mem _ hm),
        (Subgroup.mem_normalizer_iff.mp hmN _).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hmN _).mpr hx2⟩
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hx1) hm
      simpa [mul_assoc] using this
  · have hle : (conjSub c₁ (perfectCoreIn K a) ⊓
        (oddCoreOf (conjSub (c₁ : G) K)).comap (Subgroup.centralizer ({a} : Set G)).subtype).map
          (Subgroup.centralizer ({a} : Set G)).subtype ≤ oddCoreOf (conjSub (c₁ : G) K) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (Subgroup.centralizer ({a} : Set G)).subtype_injective).toEquiv]
    exact (oddCoreOf_odd_natCard _).of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem omega4_conjFamily (hd : Sec19Data p f K z S W) (a : G) :
    ∀ M₁ ∈ conjFamily (perfectCoreIn K a), ∀ M₂ ∈ conjFamily (perfectCoreIn K a), M₁ ≠ M₂ →
      padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(M₁ ⊓ M₂)) = 1 → ⁅M₁, M₂⁆ ≤ oddCoreOf M₁ ⊓ oddCoreOf M₂) := by
  rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩ hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hypOmegaMod_of_tightD hd.tight
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

theorem hypOmegaMod_conjFamily (hd : Sec19Data p f K z S W) {a : G} {e₀ : ℕ}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K a) ⟨z, hzA⟩) :
    HypOmegaMod p e₀ (conjFamily (perfectCoreIn K a)) where
  conjInvariant := by
    rintro n _ ⟨g, rfl⟩
    exact ⟨n * g, conjSub_mul _ _ _⟩
  classical := by
    rintro _ ⟨g, rfl⟩
    exact ⟨_, hL.conj g⟩
  omega4 := omega4_conjFamily hd a
  omega5 := omega5_conjFamily hd a

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
