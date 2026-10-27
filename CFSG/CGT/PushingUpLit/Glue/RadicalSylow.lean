module

public import CFSG.RankThree.Coprime.ThetaPlaneNormalizesComponent
public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs
public import CFSG.CGT.PushingUpLit.NineChoiceJ
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_centralizerModCore {Y : Subgroup G} {n g : G}
    (hn : n ∈ Subgroup.normalizer (Y : Set G)) (hg : g ∈ centralizerModCore Y) :
    n * g * n⁻¹ ∈ centralizerModCore Y := by
  obtain ⟨hgN, hg'⟩ := hg
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 := Subgroup.mem_normalizer_iff.1 hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have e : n * g * n⁻¹ * y * (n * g * n⁻¹)⁻¹ = n * (g * (n⁻¹ * y * n) * g⁻¹) * n⁻¹ := by group
    have hy' : y ∈ Y ↔ n⁻¹ * y * n ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) y)
      simpa using this
    rw [e, hy']
    constructor
    · intro hy
      have := (Subgroup.mem_normalizer_iff.1 hgN _).1 hy
      exact (h1 _).1 this
    · intro hy
      have h2 := (h1 _).2 hy
      have h3 : g * (n⁻¹ * y * n) * g⁻¹ ∈ Y := by
        simpa using h2
      exact (Subgroup.mem_normalizer_iff.1 hgN _).2 h3
  · have hx' : n⁻¹ * x * n ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) x).1 hx
      simpa using this
    have h1 := hg' _ hx'
    have e : n * g * n⁻¹ * x * (n * g * n⁻¹)⁻¹ * x⁻¹ =
        n * (g * (n⁻¹ * x * n) * g⁻¹ * (n⁻¹ * x * n)⁻¹) * n⁻¹ := by group
    rw [e]
    exact conj_mem_oTwoIn hn h1

theorem normalizer_le_normalizer_centralizerModCore (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (centralizerModCore Y : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_centralizerModCore hn hg, fun hg => ?_⟩
  have := conj_mem_centralizerModCore (inv_mem hn) hg
  simpa [mul_assoc] using this

theorem oTwoIn_le_centralizerModCore (Y : Subgroup G) : oTwoIn Y ≤ centralizerModCore Y := by
  intro c hc
  refine ⟨Subgroup.le_normalizer (oTwoIn_le Y hc), fun x hx => ?_⟩
  have : ⁅c, x⁆ ∈ ⁅oTwoIn Y, Y⁆ := Subgroup.commutator_mem_commutator hc hx
  exact blockU_le_oTwoIn Y this

theorem centralizerModCore_le_normalizer (Y : Subgroup G) :
    centralizerModCore Y ≤ Subgroup.normalizer (Y : Set G) := fun _ hg => hg.1

variable [Finite G]

theorem oTwoIn_le_of_isSylowOf_centralizerModCore {Y R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y)) : oTwoIn Y ≤ R :=
  Nine.le_of_isSylowOf_of_normal hR (isPGroup_oTwoIn Y) (oTwoIn_le_centralizerModCore Y)
    ((centralizerModCore_le_normalizer Y).trans (normalizer_le_normalizer_oTwoIn Y))

theorem le_normalizer_of_isSylowOf_centralizerModCore {Y R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizerModCore Y)) : Y ≤ Subgroup.normalizer (R : Set G) := by
  have hO := oTwoIn_le_of_isSylowOf_centralizerModCore hR
  have key : ∀ y ∈ Y, ∀ r ∈ R, y⁻¹ * r * y ∈ R := by
    intro y hy r hr
    have hrC : r⁻¹ ∈ centralizerModCore Y := inv_mem (hR.1 hr)
    have h1 := hrC.2 y⁻¹ (inv_mem hy)
    have e : y⁻¹ * r * y = r * (r⁻¹ * y⁻¹ * r * y) := by group
    rw [e]
    refine mul_mem hr (hO ?_)
    have e2 : r⁻¹ * y⁻¹ * r * y = r⁻¹ * y⁻¹ * r⁻¹⁻¹ * y⁻¹⁻¹ := by group
    rw [e2]
    exact h1
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    have := key y⁻¹ (inv_mem hy) r hr
    simpa using this
  · intro hr
    have := key y hy _ hr
    simpa [mul_assoc] using this

theorem exists_isSylowOf_normalized {C Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ Subgroup.normalizer (C : Set G)) :
    ∃ R : Subgroup G, IsSylowOf 2 R C ∧ Q ≤ Subgroup.normalizer (R : Set G) ∧
      ∀ N : Subgroup G, N ≤ C → (N.subgroupOf C).Normal → IsPGroup 2 N → N ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hRC, hR2, hRdiv, hQR, hN⟩ := CFSG.RankThree.Coprime.exists_sylow_normalized C Q hQ hQC
  refine ⟨R, ⟨hRC, hR2, ?_⟩, hQR, hN⟩
  intro hd
  obtain ⟨b, hb⟩ := hR2.exists_card_eq
  have hcard : Nat.card (R.subgroupOf C) = 2 ^ b := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hb]
  have h1 : 2 ^ (b + 1) ∣ Nat.card C := by
    rw [← Subgroup.card_mul_index (R.subgroupOf C), hcard, pow_succ]
    exact mul_dvd_mul_left _ hd
  have h2 := hRdiv (b + 1) h1
  rw [hb] at h2
  exact absurd ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 h2) (by omega)

end CFSG.CGT.PushingUpLit.Glue
