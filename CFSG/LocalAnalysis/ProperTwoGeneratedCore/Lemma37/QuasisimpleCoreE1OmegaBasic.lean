module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1DegreeOmega
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Fusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1SigmaR
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUDelta

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3

section Orbit

variable {G α : Type*} [Group G] [MulAction G α]

theorem smul_mem_orbit_centralizer_iff {g s : G} {ω β : α} (hg : g • ω = ω) :
    g • β ∈ MulAction.orbit (Subgroup.centralizer {g * s * g⁻¹}) ω ↔
      β ∈ MulAction.orbit (Subgroup.centralizer {s}) ω := by
  have hg' : g⁻¹ • ω = ω := by rw [inv_smul_eq_iff, hg]
  constructor
  · rintro ⟨⟨c, hc⟩, hcβ⟩
    refine ⟨⟨g⁻¹ * c * g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · have h := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc g⁻¹ * c * g * s = g⁻¹ * (c * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * s * g⁻¹ * c) * g := by rw [h]
        _ = s * (g⁻¹ * c * g) := by group
    · change c • ω = g • β at hcβ
      change (g⁻¹ * c * g) • ω = β
      rw [mul_smul, mul_smul, hg, hcβ, inv_smul_smul]
  · rintro ⟨⟨c, hc⟩, rfl⟩
    refine ⟨⟨g * c * g⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩, ?_⟩
    · have h := Subgroup.mem_centralizer_singleton_iff.mp hc
      calc g * c * g⁻¹ * (g * s * g⁻¹) = g * (c * s) * g⁻¹ := by group
        _ = g * (s * c) * g⁻¹ := by rw [h]
        _ = g * s * g⁻¹ * (g * c * g⁻¹) := by group
    · change (g * c * g⁻¹) • ω = g • (c • ω)
      rw [mul_smul, mul_smul, hg']

theorem smul_eq_self_of_mem_orbit_centralizer {s : G} {ω β : α} (hs : s • ω = ω)
    (hβ : β ∈ MulAction.orbit (Subgroup.centralizer {s}) ω) : s • β = β := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := hβ
  change s • (c • ω) = c • ω
  rw [← mul_smul, ← Subgroup.mem_centralizer_singleton_iff.mp hc, mul_smul, hs]

end Orbit

private instance instDecEqPermFinFiveOmega : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem perm5_exists_fixed : ∀ t : Perm (Fin 5), t * t = 1 → ∃ j, t j = j := by decide +kernel

theorem perm5_exists_two_fixed : ∀ t : Perm (Fin 5), t * t = 1 → sign t = -1 → ∀ j₁ : Fin 5,
    t j₁ = j₁ → ∃ j j' : Fin 5, j ≠ j₁ ∧ j' ≠ j₁ ∧ j ≠ j' ∧ t j = j ∧ t j' = j' := by
  decide +kernel

theorem perm5_swap_mul : ∀ t : Perm (Fin 5), ∀ j₁ j : Fin 5, t * t = 1 → sign t = -1 →
    t j₁ = j₁ → t j = j → j ≠ j₁ → sign (swap j₁ j * t) = 1 ∧
      swap j₁ j * t * t = t * (swap j₁ j * t) ∧ (swap j₁ j * t) j₁ = j := by
  decide +kernel

theorem cycleType_of_existsUnique_fixed {π : Perm (Fin 9)} (hπ : π * π = 1)
    (h1 : ∃! i, π i = i) : π.cycleType = {2, 2, 2, 2} ∧ sign π = 1 := by
  obtain ⟨i₀, hi₀, huniq⟩ := h1
  have hsupp : π.support = Finset.univ.erase i₀ := by
    ext i
    rw [mem_support, Finset.mem_erase]
    exact ⟨fun h => ⟨fun h' => h (h' ▸ hi₀), Finset.mem_univ _⟩,
      fun h h' => h.1 (huniq i h')⟩
  have hcard : π.support.card = 8 := by
    rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hct : π.cycleType = {2, 2, 2, 2} := by
    rw [cycleType_eq_replicate hπ, hcard]
    rfl
  refine ⟨hct, ?_⟩
  rw [sign_of_cycleType, hct]
  decide

theorem cycleType_of_two_fixed {π : Perm (Fin 9)} (hπ : π * π = 1) (hπ1 : π ≠ 1)
    (hsign : sign π = 1) {i j : Fin 9} (hij : i ≠ j) (hi : π i = i) (hj : π j = j) :
    π.cycleType = {2, 2} := by
  have hord : orderOf π = 2 := orderOf_eq_prime (by rw [pow_two]; exact hπ) hπ1
  rcases cycleType_of_orderOf_eq_two hord hsign with h | h
  · exact h
  · exfalso
    have hsum := sum_cycleType π
    rw [h] at hsum
    have hle : π.support ⊆ (Finset.univ.erase i).erase j := fun k hk => by
      rw [mem_support] at hk
      rw [Finset.mem_erase, Finset.mem_erase]
      exact ⟨fun h' => hk (h' ▸ hj), fun h' => hk (h' ▸ hi), Finset.mem_univ _⟩
    have hcard := Finset.card_le_card hle
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      ← hsum] at hcard
    exact absurd hcard (by decide)

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem forty_ne_one : caseC3Word (Subgroup.center J) u m y x 40 ≠ 1 := by
  rw [Ne, d.caseC3BCD.caseC3Word_eq_one_iff]
  decide

@[expose] noncomputable def omegaZ :
    (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)) :=
  Classical.choose (d.setting.exists_smul_eq_self d.caseC3BCD.forty_mul_self)

theorem forty_smul_omegaZ : caseC3Word (Subgroup.center J) u m y x 40 • d.omegaZ = d.omegaZ :=
  Classical.choose_spec (d.setting.exists_smul_eq_self d.caseC3BCD.forty_mul_self)

theorem smul_omegaZ {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) :
    g • d.omegaZ = d.omegaZ :=
  d.setting.smul_eq_self_of_mem_centralizer d.caseC3BCD.genuine_forty d.forty_ne_one hg
    d.forty_smul_omegaZ

theorem word_smul_omegaZ (v : Fin 64) :
    caseC3Word (Subgroup.center J) u m y x v • d.omegaZ = d.omegaZ :=
  d.smul_omegaZ (d.map_le_centralizer_forty (d.caseC3BCD.caseC3Word_mem v))

theorem eq_omegaZ_of_genuine {s : J ⧸ Subgroup.center J}
    (hs : s ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    (hgen : CaseC3.Genuine (Subgroup.center J) s) (hs1 : s ≠ 1)
    {ω : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (hω : s • ω = ω) : ω = d.omegaZ :=
  d.setting.eq_of_smul_eq_self hgen hs1 hω (d.smul_omegaZ hs)

theorem forty_mem_centralizer_self : caseC3Word (Subgroup.center J) u m y x 40 ∈
    Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp
    (d.map_le_centralizer_forty (d.caseC3BCD.caseC3Word_mem 32))
  rw [CaseC3BCD.caseC3Word_thirtytwo] at h
  exact Subgroup.mem_centralizer_singleton_iff.mpr h.symm

theorem exists_smul_one_eq_omegaZ : ∃ c₀ : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
    c₀ • ((1 : J ⧸ Subgroup.center J) :
      (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))) = d.omegaZ := by
  obtain ⟨j₀, hj₀⟩ := d.exists_smul_eq_smul_iff
  set zC : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} :=
    ⟨_, d.forty_mem_centralizer_self⟩
  have hzz : d.rho5C zC * d.rho5C zC = 1 := by
    rw [← map_mul, show zC * zC = 1 from Subtype.ext d.caseC3BCD.forty_mul_self, map_one]
  obtain ⟨j, hj⟩ := perm5_exists_fixed _ hzz
  obtain ⟨c₀, hc₀⟩ := d.rho5C_surjective (swap j₀ j)
  refine ⟨c₀, ?_⟩
  refine d.setting.eq_of_smul_eq_self d.caseC3BCD.genuine_forty d.forty_ne_one ?_
    d.forty_smul_omegaZ
  change zC • (c₀ • ((1 : J ⧸ Subgroup.center J) :
    (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J)))) = _
  rw [← mul_smul, hj₀, map_mul, Perm.mul_apply, hc₀, swap_apply_left, hj]

theorem exists_smul_omegaZ_eq_iff : ∃ j₁ : Fin 5,
    ∀ c c' : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      c • d.omegaZ = c' • d.omegaZ ↔ d.rho5C c j₁ = d.rho5C c' j₁ := by
  obtain ⟨j₀, hj₀⟩ := d.exists_smul_eq_smul_iff
  obtain ⟨c₀, hc₀⟩ := d.exists_smul_one_eq_omegaZ
  refine ⟨d.rho5C c₀ j₀, fun c c' => ?_⟩
  rw [← hc₀, ← mul_smul, ← mul_smul, hj₀, map_mul, map_mul, Perm.mul_apply, Perm.mul_apply]

theorem ncard_orbit_omegaZ :
    (MulAction.orbit (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) d.omegaZ).ncard = 5 := by
  obtain ⟨c₀, hc₀⟩ := d.exists_smul_one_eq_omegaZ
  rw [MulAction.orbit_eq_iff.mpr ⟨c₀, hc₀⟩]
  exact d.ncard_orbit

theorem smul_eq_self_of_rho5C_eq_one {c : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}}
    (hc : d.rho5C c = 1)
    {β : (J ⧸ Subgroup.center J) ⧸ B.map (QuotientGroup.mk' (Subgroup.center J))}
    (hβ : β ∈ MulAction.orbit (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) d.omegaZ) :
    (c : J ⧸ Subgroup.center J) • β = β := by
  obtain ⟨j₁, hj₁⟩ := d.exists_smul_omegaZ_eq_iff
  obtain ⟨c', rfl⟩ := hβ
  change c • (c' • d.omegaZ) = c' • d.omegaZ
  rw [← mul_smul, hj₁, map_mul, hc, one_mul]

theorem rho5C_kappaX (i : Fin 4) : d.rho5C (d.toCentralizer (d.kappaX i)) = 1 := by
  rw [rho5C, liftC_toCentralizer, d.quasiMk_kappaX]
  exact d.rho5_of_mem_centralizer (d.kappa_mem i)

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
