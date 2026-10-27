module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndOddTwisted
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)

section Quot

variable {G : Type*} [Group G] {X : Type*} [Group X] {G₀ : Subgroup G}

@[expose] noncomputable def normalizerQuotMulAut (e : G₀ ⧸ center G₀ ≃* X) :
    normalizer (G₀ : Set G) →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp ((centerQuotientHom G₀).comp G₀.normalizerMonoidHom)

theorem normalizerQuotMulAut_apply (e : G₀ ⧸ center G₀ ≃* X) (n : normalizer (G₀ : Set G))
    (y : G₀) :
    normalizerQuotMulAut e n (e (QuotientGroup.mk' (center G₀) y)) =
      e (QuotientGroup.mk' (center G₀) (G₀.normalizerMonoidHom n y)) := by
  show e (onCenterQuotient (G₀.normalizerMonoidHom n)
    (e.symm (e (QuotientGroup.mk' (center G₀) y)))) = _
  rw [MulEquiv.symm_apply_apply, onCenterQuotient_apply_mk]

theorem normalizerQuotMulAut_of_mem (e : G₀ ⧸ center G₀ ≃* X) {z : G} (hz : z ∈ G₀) :
    normalizerQuotMulAut e ⟨z, le_normalizer hz⟩ =
      MulAut.conj (e (QuotientGroup.mk' (center G₀) ⟨z, hz⟩)) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center G₀) (e.symm x)
  have hx : x = e (QuotientGroup.mk' (center G₀) y) := by rw [hy, e.apply_symm_apply]
  rw [hx, normalizerQuotMulAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
    ← map_inv, ← map_mul, ← map_mul]
  congr 2

theorem exists_normalizerQuotMulAut_eq_conj (e : G₀ ⧸ center G₀ ≃* X) (g : X) :
    ∃ m : normalizer (G₀ : Set G), normalizerQuotMulAut e m = MulAut.conj g := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center G₀) (e.symm g)
  refine ⟨⟨(y : G), le_normalizer y.2⟩, ?_⟩
  rw [normalizerQuotMulAut_of_mem e y.2, Subtype.coe_eta, hy, e.apply_symm_apply]

theorem not_mem_of_normalizerQuotMulAut_not_mem_range (e : G₀ ⧸ center G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerQuotMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) : t ∉ G₀ :=
  fun htG => hout ⟨_, (normalizerQuotMulAut_of_mem e htG).symm⟩

theorem ne_bot_of_normalizerQuotMulAut_not_mem_range (e : G₀ ⧸ center G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerQuotMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) :
    G₀ ≠ ⊥ := by
  intro hbot
  have hX : ∀ x : X, x = 1 := fun x => by
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center G₀) (e.symm x)
    have hy1 : y = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall G₀).1 hbot _ y.2)
    rw [← e.apply_symm_apply x, ← hy, hy1, map_one, map_one]
  exact hout ⟨1, MulEquiv.ext fun x => (hX _).trans (hX _).symm⟩

theorem two_lt_card_of_normalizerQuotMulAut_not_mem_range [Finite G] (e : G₀ ⧸ center G₀ ≃* X)
    {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (hout : normalizerQuotMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range) :
    2 < Nat.card G := by
  have h1 : 1 < Nat.card G₀ :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 (ne_bot_of_normalizerQuotMulAut_not_mem_range e htN hout)
  have h2 : 1 < G₀.index := Subgroup.one_lt_index_of_ne_top fun h =>
    not_mem_of_normalizerQuotMulAut_not_mem_range e htN hout (h ▸ mem_top t)
  rw [← G₀.card_mul_index]
  nlinarith

theorem false_of_simple_of_quotMulAut_hom [Finite G] [IsSimpleGroup G]
    (e : G₀ ⧸ center G₀ ≃* X) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G))
    {Q : Type*} [Group Q] [Finite Q] (χ : MulAut X →* Q) (hQ : ¬ 4 ∣ Nat.card Q)
    (hχInn : ∀ x : X, χ (MulAut.conj x) = 1) (hχt : χ (normalizerQuotMulAut e ⟨t, htN⟩) ≠ 1) :
    False := by
  have hout : normalizerQuotMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range := by
    rintro ⟨x, hx⟩
    exact hχt (hx ▸ hχInn x)
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (two_lt_card_of_normalizerQuotMulAut_not_mem_range e htN hout)
    (exists_normal_index_two_of_unique_of_not_four_dvd htN ht huniq
      (χ.comp (normalizerQuotMulAut e)) hQ hχt)

theorem normalizerQuotMulAut_eq_one_of_mem_centralizer (e : G₀ ⧸ center G₀ ≃* X) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (htC : t ∈ centralizer (G₀ : Set G)) :
    normalizerQuotMulAut e ⟨t, htN⟩ = 1 := by
  have h1 : G₀.normalizerMonoidHom ⟨t, htN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker, mem_subgroupOf]
    exact htC
  change (MulAut.congr e) (centerQuotientHom G₀ (G₀.normalizerMonoidHom ⟨t, htN⟩)) = 1
  rw [h1, map_one, map_one]

theorem ker_normalizerQuotMulAut [Group.IsPerfect G₀] (e : G₀ ⧸ center G₀ ≃* X) :
    (normalizerQuotMulAut e).ker =
      (centralizer (G₀ : Set G)).subgroupOf (normalizer (G₀ : Set G)) := by
  rw [← normalizerMonoidHom_ker]
  ext n
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (MulAut.congr e) (centerQuotientHom G₀ (G₀.normalizerMonoidHom n)) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    exact CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective G₀
      (h.trans (map_one _).symm)
  · intro h
    rw [h, map_one]

theorem card_ker_normalizerQuotMulAut [Group.IsPerfect G₀] (e : G₀ ⧸ center G₀ ≃* X) :
    Nat.card (normalizerQuotMulAut e).ker = Nat.card (centralizer (G₀ : Set G)) := by
  rw [ker_normalizerQuotMulAut]
  exact Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv

end Quot

variable {G : Type*} [Group G] [Finite G] {G₀ : Subgroup G}

theorem false_of_simple_of_E6_conj_graph_quot [IsSimpleGroup G] (K : Type) [Field K] [Finite K]
    (e : G₀ ⧸ center G₀ ≃* adjointGroup Tag.E6 K) {t : G} (htN : t ∈ normalizer (G₀ : Set G))
    (ht : orderOf t = 2)
    (hgraph : ∃ (φ : MulAut (adjointGroup Tag.E6 K)) (g : adjointGroup Tag.E6 K)
      (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K),
      φ * normalizerQuotMulAut e ⟨t, htN⟩ * φ⁻¹ = MulAut.conj g * exactNormalAut Tag.E6 K a σ 1)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  obtain ⟨χ, hχInn, hχ⟩ := exists_E6_graphCoordinate K
  obtain ⟨φ, g, a, σ, hN⟩ := hgraph
  refine false_of_simple_of_quotMulAut_hom e htN ht huniq χ (by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]; decide) hχInn ?_
  have h1 : χ (φ * normalizerQuotMulAut e ⟨t, htN⟩ * φ⁻¹) =
      χ (normalizerQuotMulAut e ⟨t, htN⟩) := by
    rw [map_mul, map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  rw [← h1, hN, hχ g a σ (by norm_num), Nat.cast_one, Ne, ofAdd_eq_one]
  decide

theorem false_of_simple_of_twistedE6_quot
    [IsSimpleGroup G]
    [Group.IsPerfect G₀] (hZ : Odd (Nat.card (centralizer (G₀ : Set G)))) {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (e : G₀ ⧸ center G₀ ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom) {t : G}
    (htN : t ∈ normalizer (G₀ : Set G)) (ht : orderOf t = 2)
    (hout : normalizerQuotMulAut e ⟨t, htN⟩ ∉
      (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ.toRingHom →* _).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G)) :
    False := by
  have : Finite (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := Finite.of_equiv _ e.toEquiv
  have hker : Odd (Nat.card (normalizerQuotMulAut e).ker) := by
    rw [card_ker_normalizerQuotMulAut]
    exact hZ
  exact CFSG.SeitzReduction.not_exists_normal_index_two_of_simple
    (two_lt_card_of_normalizerQuotMulAut_not_mem_range e htN hout)
    (exists_normal_index_two_of_twistedE6_action hf K hK σ hσ (normalizerQuotMulAut e) hker
      (exists_normalizerQuotMulAut_eq_conj e) htN ht hout huniq)

end CFSG.SeitzReduction.EPilot
