module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutBorel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutFieldDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutLift
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankOne
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne (centerQuotientConj)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open scoped commutatorElement

@[expose] def LieOutConcl {Y : Type} [Group Y] (L : Subgroup Y) (x : Y) : Prop :=
  (∀ J : Subgroup Y, IsParabolicTwo L J → (∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) → J = L) ∧
    ((∃ J : Subgroup Y, IsParabolicTwo L J ∧ J ≠ L ∧
        ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) →
      ∃ D : Subgroup Y, D ≤ L ∧ D ≠ ⊥ ∧ ⁅D, D⁆ = D ∧
        D ≤ Subgroup.centralizer ({x} : Set Y))

theorem ne_bot_of_nonLocalized {X : Type*} [Group X] [Nontrivial X] {N : Subgroup X}
    (h : NonLocalized N) : N ≠ ⊥ := by
  intro hN
  obtain ⟨g, hg⟩ := exists_ne (1 : X)
  refine h (Subgroup.zpowers g) ?_ ?_ ?_
  · intro hz
    exact hg (Subgroup.zpowers_eq_bot.1 hz)
  · infer_instance
  · rw [hN]
    exact bot_le

theorem lieOutConcl_of_fixesNonLocalized {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y))
    (hOL : OvergroupLocal (↥L ⧸ Subgroup.center ↥L)) [Nontrivial (↥L ⧸ Subgroup.center ↥L)]
    (hF : FixesNonLocalized (centerQuotientConj L ⟨x, hx⟩)) : LieOutConcl L x := by
  obtain ⟨N₀, hperf, hfix, hNL⟩ := hF
  refine ⟨fun J ⟨hJL, T, hT, hNT⟩ hCJ => ?_, fun _ => ?_⟩
  · by_contra hne
    exact not_le_quotImage_of_nonLocalized hOL hT hNT hJL hne hNL
      (le_quotImage_of_centralizer_le L J hx hperf hfix hCJ)
  · obtain ⟨W, hW, hWmap, hWfix⟩ := exists_perfect_centralizer_lift L hx hperf hfix
    refine ⟨W.map L.subtype, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨w, -, rfl⟩
      exact w.2
    · intro hbot
      have hW1 : W = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hbot
      apply ne_bot_of_nonLocalized hNL
      rw [← hWmap, hW1, Subgroup.map_bot]
    · rw [← Subgroup.map_commutator, hW]
    · rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hWfix w hw
      exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem not_sThree_le_normalizer {X : Type*} [Group X] [Finite X] (S : Sylow 2 X) {t c : X}
    (ht : t ^ 2 = 1) (hc : c ^ 3 = 1) (hcne : c ≠ 1) (htc : t * c * t⁻¹ = c⁻¹)
    (ht' : t ∈ Subgroup.normalizer ((S : Subgroup X) : Set X))
    (hc' : c ∈ Subgroup.normalizer ((S : Subgroup X) : Set X)) : False := by
  have hP : IsPGroup 2 (Subgroup.zpowers t) := by
    have hord : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one ht
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have htS : t ∈ (S : Subgroup X) := by
    have h1 : t ∈ Subgroup.zpowers t ⊓ Subgroup.normalizer (S : Set X) :=
      ⟨Subgroup.mem_zpowers t, ht'⟩
    rw [hP.inf_normalizer_sylow S] at h1
    exact h1.2
  have hctS : c * t * c⁻¹ ∈ (S : Subgroup X) :=
    (Subgroup.mem_normalizer_iff.1 hc' t).1 htS
  have hc2 : c ^ 2 ∈ (S : Subgroup X) := by
    have h1 : c * t * c⁻¹ * t⁻¹ ∈ (S : Subgroup X) := mul_mem hctS (inv_mem htS)
    have h2 : c * t * c⁻¹ * t⁻¹ = c ^ 2 := by
      have htt : t * t = 1 := by rw [← pow_two, ht]
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      rw [← htc, htinv]
      calc c * t * (t * c * t) * t = c * (t * t) * c * (t * t) := by group
        _ = c ^ 2 := by rw [htt, mul_one, mul_one, pow_two]
    rwa [h2] at h1
  have hcS : c ∈ (S : Subgroup X) := by
    have h1 : c ^ 2 * c ^ 2 ∈ (S : Subgroup X) := mul_mem hc2 hc2
    have h2 : c ^ 2 * c ^ 2 = c := by
      calc c ^ 2 * c ^ 2 = c ^ 3 * c := by group
        _ = c := by rw [hc, one_mul]
    rwa [h2] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨c, hcS⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : 2 ^ k ∣ 3 := hk ▸ orderOf_dvd_of_pow_eq_one hc
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact hcne hk
  · have : 2 ∣ 3 := (dvd_pow_self 2 hk0.ne').trans hdvd
    omega

theorem le_borel_of_quotImage_le {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hJL : J ≤ L)
    (h : quotImage L J ≤ Subgroup.normalizer ((barSylow hT : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
      Set (↥L ⧸ Subgroup.center ↥L))) : J ≤ L ⊓ Subgroup.normalizer (T : Set Y) := by
  intro y hy
  have hyq : (QuotientGroup.mk (⟨y, hJL hy⟩ : L) : ↥L ⧸ Subgroup.center ↥L) ∈ quotImage L J :=
    mem_quotImage.2 ⟨⟨y, hJL hy⟩, hy, rfl⟩
  have hl := CFSG.AGLEmbedding.TwoGenInner.mem_normalizer_of_mem_normalizer_map
    (CFSG.AGLEmbedding.TwoGenInner.sylowOfIsSylowTwoOf hT) (g := (⟨y, hJL hy⟩ : L)) (h hyq)
  have hl' : (⟨y, hJL hy⟩ : L) ∈ Subgroup.normalizer ((T.subgroupOf L : Subgroup L) : Set L) := hl
  rw [← Subgroup.subgroupOf_normalizer_eq hT.1] at hl'
  exact ⟨hJL hy, Subgroup.mem_subgroupOf.1 hl'⟩

theorem lieOutConcl_of_sThree {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {x : Y}
    (hx : x ∈ Subgroup.normalizer (L : Set Y)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hxp : x ^ p = 1) (hmax : BorelMaximal (↥L ⧸ Subgroup.center ↥L))
    {t c : ↥L ⧸ Subgroup.center ↥L} (htfix : centerQuotientConj L ⟨x, hx⟩ t = t)
    (hcfix : centerQuotientConj L ⟨x, hx⟩ c = c) (ht : t ^ 2 = 1) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (htc : t * c * t⁻¹ = c⁻¹) : LieOutConcl L x := by
  have hcop2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
  have hcop3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).2 (by omega)
  refine ⟨fun J ⟨hJL, T, hT, hNT⟩ hCJ => ?_, ?_⟩
  · by_contra hne
    have heq := hmax (barSylow hT) (quotImage L J) (normalizer_barSylow_le_quotImage hT hNT)
      (quotImage_ne_top hT hNT hJL hne)
    have htJ := mem_quotImage_of_coprime L J hx hp hxp hCJ htfix hcop2 ht
    have hcJ := mem_quotImage_of_coprime L J hx hp hxp hCJ hcfix hcop3 hc
    rw [heq] at htJ hcJ
    exact not_sThree_le_normalizer (barSylow hT) ht hc hcne htc htJ hcJ
  · rintro ⟨J, ⟨hJL, T, hT, hNT⟩, hne, hnB⟩
    exfalso
    apply hnB T hT
    have heq := hmax (barSylow hT) (quotImage L J) (normalizer_barSylow_le_quotImage hT hNT)
      (quotImage_ne_top hT hNT hJL hne)
    exact le_antisymm (le_borel_of_quotImage_le hT hJL (heq ▸ le_rfl)) hNT

end CFSG.AGLEmbedding.LieOut
