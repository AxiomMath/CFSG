module

public import CFSG.ClassicalInvolution.Q3.WeakBalance
public import CFSG.ClassicalInvolution.Balance.Quotient

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
open scoped commutatorElement

section Lift

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_zpowers_of_sq {x : X} (hx : x * x = 1) : IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  show (g : X) ^ 2 = 1
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]

theorem exists_odd_normalized_lift {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) {f : X}
    (hf : IsPGroup 2 (Subgroup.zpowers f)) {d : X ⧸ N}
    (hd : d ∈ oddCoreIn (Subgroup.centralizer ({QuotientGroup.mk' N f} : Set (X ⧸ N)))) :
    ∃ R : Subgroup X, R ≤ Subgroup.centralizer ({f} : Set X) ∧ Odd (Nat.card R) ∧
      (∀ u ∈ Subgroup.centralizer ({f} : Set X), ∀ r ∈ R, u * r * u⁻¹ ∈ R) ∧
      ∃ d₀ ∈ R, QuotientGroup.mk' N d₀ = d := by
  set π := QuotientGroup.mk' N with hπ
  set M : Subgroup (X ⧸ N) :=
    oddCoreIn (Subgroup.centralizer ({π f} : Set (X ⧸ N))) with hM
  have hmap := map_centralizer_singleton_eq hN hf
  obtain ⟨d₀, hd₀C, hd₀⟩ : d ∈ (Subgroup.centralizer ({f} : Set X)).map π := by
    rw [hmap]
    exact oddCoreIn_le _ hd
  refine ⟨Subgroup.centralizer ({f} : Set X) ⊓ M.comap π, inf_le_left, ?_, ?_, d₀,
    ⟨hd₀C, ?_⟩, hd₀⟩
  ·
    set R : Subgroup X := Subgroup.centralizer ({f} : Set X) ⊓ M.comap π with hR
    set φ : R →* X ⧸ N := π.comp R.subtype with hφ
    have hker : Odd (Nat.card φ.ker) := by
      have hle : φ.ker.map R.subtype ≤ N := by
        rintro _ ⟨x, hx, rfl⟩
        exact (QuotientGroup.eq_one_iff _).mp hx
      rw [← Subgroup.card_map_of_injective R.subtype_injective]
      exact hN.of_dvd_nat (Subgroup.card_dvd_of_le hle)
    have hrange : Odd (Nat.card φ.range) := by
      have hle : φ.range ≤ M := by
        rintro _ ⟨x, rfl⟩
        exact x.2.2
      exact (odd_card_oddCoreIn _).of_dvd_nat (Subgroup.card_dvd_of_le hle)
    rw [← Subgroup.card_ker_mul_card_range φ]
    exact hker.mul hrange
  · intro u hu r hr
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hr.1) (Subgroup.inv_mem _ hu), ?_⟩
    show π (u * r * u⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    refine conj_mem_oddCoreIn ?_ hr.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hu]
  · show π d₀ ∈ M
    rw [hd₀]
    exact hd

end Lift

section Commutator

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutator_mem_involutionOddCore_of_odd_normalized (hΩ : ConjInvariant Ω)
    (hO : LocalOddCentralizer3 Ω) {a b : G} (hb : b ∉ Subgroup.center G)
    (haY : a ∈ centralizingLayer Ω {b}) (ha2 : orderOf a = 2) {R : Subgroup G}
    (hRa : R ≤ Subgroup.centralizer ({a} : Set G)) (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (hRodd : Odd (Nat.card R))
    (hRn : ∀ u ∈ Subgroup.centralizer ({a} : Set G), u ∈ Subgroup.centralizer ({b} : Set G) →
      ∀ x ∈ R, u * x * u⁻¹ ∈ R)
    {r g : G} (hr : r ∈ R) (hg : g ∈ centralizingLayer Ω {b} ⊓ Subgroup.centralizer ({a} : Set G)) :
    ⁅r, g⁆ ∈ involutionOddCore b := by
  set Y : Subgroup G := centralizingLayer Ω {b} with hY
  have hYb : Y ≤ Subgroup.centralizer ({b} : Set G) := centralizingLayer_le_centralizer Ω {b}
  have hgY : g ∈ Y := hg.1
  have hga : g ∈ Subgroup.centralizer ({a} : Set G) := hg.2
  have hrCb : r ∈ Subgroup.centralizer ({b} : Set G) := hRb hr
  have hgCb : g ∈ Subgroup.centralizer ({b} : Set G) := hYb hgY
  have hcommR : ⁅r, g⁆ ∈ R := by
    have h1 : g * r⁻¹ * g⁻¹ ∈ R := hRn g hga hgCb r⁻¹ (R.inv_mem hr)
    have : ⁅r, g⁆ = r * (g * r⁻¹ * g⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact R.mul_mem hr h1
  have hcommY : ⁅r, g⁆ ∈ Y := by
    have : ⁅r, g⁆ = (r * g * r⁻¹) * g⁻¹ := by
      simp only [commutatorElement_def]
    rw [this]
    exact Y.mul_mem (conj_mem_centralizingLayer hΩ hrCb hgY) (Y.inv_mem hgY)
  have hRY : (R ⊓ Y) ≤ oddCoreIn (Y ⊓ Subgroup.centralizer ({a} : Set G)) := by
    refine le_oddCoreIn_of_normalizes ?_ ?_ ?_
    · intro x hx
      exact ⟨hx.2, hRa hx.1⟩
    · intro u hu
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hub : u ∈ Subgroup.centralizer ({b} : Set G) := hYb hu.1
      have hub' : u⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.inv_mem _ hub
      have hua' : u⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := Subgroup.inv_mem _ hu.2
      constructor
      · rintro ⟨hyR, hyY⟩
        exact ⟨hRn u hu.2 hub y hyR, conj_mem_centralizingLayer hΩ hub hyY⟩
      · rintro ⟨hyR, hyY⟩
        have h1 := hRn u⁻¹ hua' hub' _ hyR
        have h2 := conj_mem_centralizingLayer hΩ hub' hyY
        simp only [mul_assoc, inv_inv, inv_mul_cancel_left] at h1 h2 ⊢
        refine ⟨?_, ?_⟩
        · simpa [mul_assoc] using h1
        · simpa [mul_assoc] using h2
    · exact hRodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have h3 : ⁅r, g⁆ ∈ oddCoreIn Y := hO b hb a haY ha2 (hRY ⟨hcommR, hcommY⟩)
  exact oddCoreIn_centralizingLayer_le hΩ b h3

end Commutator

end CFSG.ClassicalInvolution.Q3.Q3KB
