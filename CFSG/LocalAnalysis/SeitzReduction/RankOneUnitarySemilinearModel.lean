module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoForm
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularCoords
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRegularModel

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.TheoremC

namespace U3RootCoords

variable {G : Type*} [Group G] {E : Type*} [Field E] {T₁ : Subgroup G} {σ : E →+* E}
  {u v : G → E} (hc : U3RootCoords T₁ σ u v)
include hc

theorem v_one : v 1 = 0 := by
  have h := hc.mul_v 1 (one_mem _) 1 (one_mem _)
  rw [mul_one, hc.u_one, zero_mul, sub_zero] at h
  linear_combination -h

theorem conj_coords [CharP E 2] {p z : G} (hp : p ∈ T₁) (hz : z ∈ T₁) :
    u (p * z * p⁻¹) = u z ∧ v (p * z * p⁻¹) = v z + TraceForm.form σ (u p) (u z) := by
  have hpz : p * z ∈ T₁ := mul_mem hp hz
  have hpi : p⁻¹ ∈ T₁ := inv_mem hp
  have hvinv : v p⁻¹ = -v p + u p * σ (u p⁻¹) := by
    have h := hc.mul_v p hp p⁻¹ hpi
    rw [mul_inv_cancel, hc.v_one] at h
    linear_combination -h
  have e1 := hc.mul_v _ hpz _ hpi
  have e2 := hc.mul_v _ hp _ hz
  have e3 := hc.mul_u _ hp _ hz
  have e4 := hc.u_inv hp
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_⟩
  · rw [hc.mul_u _ hpz _ hpi, e3, e4]
    ring
  · rw [e1, e2, e3, hvinv, e4, map_neg, TraceForm.form]
    linear_combination (-(u p * σ (u z))) * h2

end U3RootCoords

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_rootCoords_borel_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (σ : E →+* E),
      Nat.card E = (2 ^ f) ^ 2 ∧ (∀ x, σ x = x ^ (2 ^ f)) ∧
      Nat.card {x : E // σ x = x} = 2 ^ f ∧
      ∃ u v : G → E, U3RootCoords (szT₁ L T) σ u v ∧
        (∀ y ∈ szT₁ L T, (y ∈ szA₁ (szT₁ L T) ↔ u y = 0)) ∧
        (∀ g ∈ L, g ∈ normalizer (szT₁ L T : Set G) → ∃ s c : E, s ≠ 0 ∧
          ∀ y ∈ szT₁ L T, u (g * y * g⁻¹) = s * u y ∧
            v (g * y * g⁻¹) = s * σ s * v y + TraceForm.form σ c (s * u y)) ∧
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
  have hcoord : U3RootCoords (szT₁ L T) (J.conj : E →+* E) (fun y => (u3Coord J hJ φ y).1.1)
      (fun y => (u3Coord J hJ φ y).1.2) :=
    u3RootCoords_of_mulEquiv J hJ φ (2 ^ f) hcard hfixed hT₁
  have htor : ∀ c : L, c ∈ cartan (Q : Subgroup L) t₀ → ∀ k : Eˣ,
      φ c = hermitianTorusPSU J hJ k → ∀ y ∈ szT₁ L T,
        u3Coord J hJ φ ((c : G) * y * (c : G)⁻¹) =
          hermitianTorusAction J k (u3Coord J hJ φ y) := by
    intro c hcC k hck y hy
    have hcT : (c : G) ∈ normalizer (szT₁ L T : Set G) :=
      (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) c).mp (cartan_le_borel _ _ hcC)
    obtain ⟨hyL, hyR⟩ := (hT₁ y).mp hy
    have hkey := hermitianUnipotentPSU_u3Coord J hJ φ hyL hyR
    have hcy : (c : G) * y * (c : G)⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hcT y).mp hy
    obtain ⟨hcyL, hcyR⟩ := (hT₁ _).mp hcy
    have hkey2 := hermitianUnipotentPSU_u3Coord J hJ φ hcyL hcyR
    have h3 : φ ⟨(c : G) * y * (c : G)⁻¹, hcyL⟩ =
        hermitianUnipotentPSU J hJ (hermitianTorusAction J k (u3Coord J hJ φ y)) := by
      have e : (⟨(c : G) * y * (c : G)⁻¹, hcyL⟩ : L) = c * ⟨y, hyL⟩ * c⁻¹ :=
        Subtype.ext (by simp)
      rw [e, map_mul, map_mul, map_inv, ← unitaryCoverTorus_conj_root J hJ k, hkey, hck]
    exact CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ (by rw [hkey2, h3])
  have hcart : ∀ c : L, c ∈ cartan (Q : Subgroup L) t₀ → ∃ k : Eˣ,
      φ c = hermitianTorusPSU J hJ k := by
    intro c hcC
    have hmem : φ c ∈ unitaryCoverTorus J hJ := by
      rw [← hφD]
      exact ⟨c, hcC, rfl⟩
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, hk.symm⟩
  have hcyc : IsCyclic (unitaryCoverScalarImage J) :=
    isCyclic_of_injective_ringHom ((Units.coeHom E).comp (unitaryCoverScalarImage J).subtype)
      (fun a b hab => Subtype.ext (Units.ext hab))
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := unitaryCoverScalarImage J)
  obtain ⟨k₀, hk₀⟩ := s.2
  have htor₀ : hermitianTorusPSU J hJ k₀ ∈ (cartan (Q : Subgroup L) t₀).map φ.toMonoidHom := by
    rw [hφD]
    exact ⟨k₀, rfl⟩
  obtain ⟨d₀, hd₀C, hd₀φ⟩ := htor₀
  have hd₀T : ((d₀ : L) : G) ∈ normalizer (szT₁ L T : Set G) :=
    (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) d₀).mp (cartan_le_borel _ _ hd₀C)
  refine ⟨E, hE, hF, inferInstance, (J.conj : E →+* E), hcard,
    huppert_II_10_4_conj_eq_frobenius J (2 ^ f) hcard hfixed, hfixed,
    fun y => (u3Coord J hJ φ y).1.1, fun y => (u3Coord J hJ φ y).1.2, hcoord, fun y hy => ?_,
    fun g hgL hgT => ?_, d₀, d₀.2, hd₀T, ((s : Eˣ) : E), Units.ne_zero _, ?_, fun y hy => ?_⟩
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
  ·
    have hgB : (⟨g, hgL⟩ : L) ∈ borel (Q : Subgroup L) :=
      (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) ⟨g, hgL⟩).mpr hgT
    rw [← hc.sup_eq, ← SetLike.mem_coe,
      coe_mul_of_right_le_normalizer_left (Q : Subgroup L) (cartan (Q : Subgroup L) t₀)
        (cartan_le_borel _ _)] at hgB
    obtain ⟨p, hpQ, c, hcC, hpc⟩ := hgB
    have hpc' : g = (p : G) * (c : G) := by
      have := congrArg Subtype.val hpc
      simpa using this.symm
    have hpT : (p : G) ∈ szT₁ L T := (hmemQ p).mp hpQ
    have hcT : (c : G) ∈ normalizer (szT₁ L T : Set G) :=
      (mem_borel_iff_mem_normalizer hmemQ (szT₁_le_right L T) c).mp (cartan_le_borel _ _ hcC)
    obtain ⟨k, hk⟩ := hcart c hcC
    refine ⟨((unitaryCoverScalar J k : Eˣ) : E), (u3Coord J hJ φ (p : G)).1.1, Units.ne_zero _,
      fun y hy => ?_⟩
    have hcy : (c : G) * y * (c : G)⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hcT y).mp hy
    have h4 := htor c hcC k hk y hy
    obtain ⟨hu1, hv1⟩ := hcoord.conj_coords hpT hcy
    have e : g * y * g⁻¹ = (p : G) * ((c : G) * y * (c : G)⁻¹) * (p : G)⁻¹ := by
      rw [hpc']
      group
    have hu2 : (u3Coord J hJ φ ((c : G) * y * (c : G)⁻¹)).1.1 =
        ((unitaryCoverScalar J k : Eˣ) : E) * (u3Coord J hJ φ y).1.1 := by
      rw [h4, hermitianTorusAction_fst_eq_scalar]
    have hv2 : (u3Coord J hJ φ ((c : G) * y * (c : G)⁻¹)).1.2 =
        ((unitaryCoverScalar J k : Eˣ) : E) * J.conj ((unitaryCoverScalar J k : Eˣ) : E) *
          (u3Coord J hJ φ y).1.2 := by
      rw [h4, hermitianTorusAction_snd, unitaryCoverScalar_norm]
      ring
    simp only at hu1 hv1 ⊢
    rw [e, hu1, hv1, hu2, hv2]
    exact ⟨rfl, rfl⟩
  · have h1 : orderOf ((s : Eˣ) : E) = orderOf (s : Eˣ) := orderOf_units
    rw [h1, Subgroup.orderOf_coe s, orderOf_eq_card_of_forall_mem_zpowers hs,
      unitaryCoverScalarImage_card J (2 ^ f) hcard hfixed hJ]
  · have h4 := htor d₀ hd₀C k₀ hd₀φ y hy
    show (u3Coord J hJ φ (((d₀ : L) : G) * y * ((d₀ : L) : G)⁻¹)).1.1 =
      ((s : Eˣ) : E) * (u3Coord J hJ φ y).1.1
    rw [h4, hermitianTorusAction_fst_eq_scalar, hk₀]

end U3Start

end CFSG.SeitzReduction.RankOne
