module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularModel
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.TheoremC

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_rootCoords_cartan_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
      Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
      ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
        (∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) ∧
        ∃ d ∈ L, d ∈ normalizer (szT₁ L T : Set G) ∧ ∃ μ : E, μ ≠ 0 ∧
          orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1) ∧
          ∀ y ∈ szT₁ L T, u (d * y * d⁻¹) = μ * u y := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, φ, hφQ, hφD⟩ :=
    hB.exists_standard_iso_unitary Q hc.sq_eq_one hc.not_mem
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hZ : rootCenter (unitaryCoverRoot J hJ) =
      (rootCenter (Q : Subgroup L)).map φ.toMonoidHom := by
    rw [← hφQ, rootCenter_map]
  have hT₁ : ∀ y : G, y ∈ szT₁ L T ↔ ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ unitaryCoverRoot J hJ := by
    intro y
    refine ⟨fun hy => ?_, ?_⟩
    · have hyL : y ∈ L := szT₁_le_right L T hy
      refine ⟨hyL, ?_⟩
      rw [← hφQ]
      exact ⟨⟨y, hyL⟩, (hmemQ _).mpr hy, rfl⟩
    · rintro ⟨hyL, hyR⟩
      rw [← hφQ] at hyR
      obtain ⟨y', hy'Q, hy'⟩ := hyR
      have : y' = ⟨y, hyL⟩ := φ.injective hy'
      rw [this] at hy'Q
      exact (hmemQ _).mp hy'Q
  have hA₁ : ∀ y : G, y ∈ szA₁ (szT₁ L T) ↔
      ∃ hyL : y ∈ L, φ ⟨y, hyL⟩ ∈ rootCenter (unitaryCoverRoot J hJ) := by
    intro y
    refine ⟨fun hy => ?_, ?_⟩
    · have hyL : y ∈ L := szT₁_le_right L T (szA₁_le _ hy)
      refine ⟨hyL, ?_⟩
      rw [hZ]
      exact ⟨⟨y, hyL⟩, (hmemZ _).mpr hy, rfl⟩
    · rintro ⟨hyL, hyR⟩
      rw [hZ] at hyR
      obtain ⟨y', hy'Q, hy'⟩ := hyR
      have : y' = ⟨y, hyL⟩ := φ.injective hy'
      rw [this] at hy'Q
      exact (hmemZ _).mp hy'Q
  have hcyc : IsCyclic (unitaryCoverScalarImage J) :=
    isCyclic_of_injective_ringHom ((Units.coeHom E).comp (unitaryCoverScalarImage J).subtype)
      (fun a b hab => Subtype.ext (Units.ext hab))
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := unitaryCoverScalarImage J)
  obtain ⟨k₀, hk₀⟩ := s.2
  have htor : hermitianTorusPSU J hJ k₀ ∈ (cartan (Q : Subgroup L) t₀).map φ.toMonoidHom := by
    rw [hφD]
    exact ⟨k₀, rfl⟩
  obtain ⟨d₀, hd₀C, hd₀φ⟩ := htor
  have hd₀T : ((d₀ : L) : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) d₀).mp (cartan_le_borel _ _ hd₀C)
  refine ⟨E, hE, hF, inferInstance, (J.conj : E →+* E), hcard,
    huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed,
    fun y => (u3Coord J hJ φ y).1.1, fun y => (u3Coord J hJ φ y).1.2,
    u3RootCoords_of_mulEquiv J hJ φ (2 ^ f) hcard hfixed hT₁, fun y hy => ?_, d₀, d₀.2, hd₀T,
    ((s : Eˣ) : E), Units.ne_zero _, ?_, fun y hy => ?_⟩
  · obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
    have hkey := hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR
    rw [hA₁]
    constructor
    · rintro ⟨hyL', hyZ⟩
      obtain ⟨z, hz0, hz⟩ := (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mp hyZ
      have : z = u3Coord J hJ φ y := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hz, hkey])
      simp only
      rw [← this]
      exact hz0
    · intro hu
      exact ⟨hyL, (mem_rootCenter_unitaryCoverRoot_iff J hJ f hcard hfixed).mpr
        ⟨u3Coord J hJ φ y, hu, hkey⟩⟩
  · have h1 : orderOf ((s : Eˣ) : E) = orderOf (s : Eˣ) := orderOf_units
    rw [h1, Subgroup.orderOf_coe s, orderOf_eq_card_of_forall_mem_zpowers hs,
      unitaryCoverScalarImage_card J (2 ^ f) hcard hfixed hJ]
  · obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
    have hkey := hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR
    have hdy : ((d₀ : L) : G) * y * ((d₀ : L) : G)⁻¹ ∈ szT₁ L T :=
      (mem_normalizer_iff.mp hd₀T y).mp hy
    obtain ⟨hdyL, hdyR⟩ := (hT₁ _).mp hdy
    have hkey2 := hermitianUnipotentPSU_u3Coord J hJ φ hdyL hdyR
    have h3 : φ ⟨((d₀ : L) : G) * y * ((d₀ : L) : G)⁻¹, hdyL⟩ =
        hermitianUnipotentPSU J hJ (hermitianTorusAction J k₀ (u3Coord J hJ φ y)) := by
      have e : (⟨((d₀ : L) : G) * y * ((d₀ : L) : G)⁻¹, hdyL⟩ : L) = d₀ * ⟨y, hyL⟩ * d₀⁻¹ :=
        Subtype.ext (by simp)
      have hd₀φ' : φ d₀ = hermitianTorusPSU J hJ k₀ := hd₀φ
      rw [e, map_mul, map_mul, map_inv, ← unitaryCoverTorus_conj_root J hJ k₀, hkey, hd₀φ']
    have h4 : u3Coord J hJ φ (((d₀ : L) : G) * y * ((d₀ : L) : G)⁻¹) =
        hermitianTorusAction J k₀ (u3Coord J hJ φ y) :=
      CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hkey2, h3])
    show (u3Coord J hJ φ (((d₀ : L) : G) * y * ((d₀ : L) : G)⁻¹)).1.1 =
      ((s : Eˣ) : E) * (u3Coord J hJ φ y).1.1
    rw [h4, hermitianTorusAction_fst_eq_scalar, hk₀]

end U3Start

end CFSG.SeitzReduction.RankOne
