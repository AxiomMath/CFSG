module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingSylowAut
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEnding

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_sylow_le_of_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {N K : Subgroup G} (S : Sylow p G) (hSN : (S : Subgroup G) ≤ N) (hK : IsPGroup p K)
    (hKN : K ≤ N) : ∃ S' : Sylow p G, K ≤ S' ∧ (S' : Subgroup G) ≤ N := by
  obtain ⟨Q, hQ⟩ := (hK.comap_subtype (K := N)).exists_le_sylow
  have hcard : Nat.card ((Q : Subgroup N).map N.subtype) = p ^ (Nat.card G).factorization p := by
    rw [Subgroup.card_map_of_injective (subtype_injective N), Q.card_eq_multiplicity]
    have h1 := (S.subtype hSN).card_eq_multiplicity
    rw [Sylow.coe_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv,
      S.card_eq_multiplicity] at h1
    exact h1.symm
  refine ⟨Sylow.ofCard _ hcard, ?_, ?_⟩
  · intro k hk
    rw [Sylow.coe_ofCard]
    exact ⟨⟨k, hKN hk⟩, hQ (show (⟨k, hKN hk⟩ : N) ∈ K.comap N.subtype from hk), rfl⟩
  · rw [Sylow.coe_ofCard]
    exact map_subtype_le _

namespace U3U1Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T R₂ U₁ : Subgroup G}

theorem mem_centralizer_of_mem_normalizer
    (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) {x : G}
    (hxx : x * x = 1) (hxU : x ∈ normalizer (U₁ : Set G))
    (hxM : x ∈ normalizer ((U₁ ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G)) :
    x ∈ centralizer (R₂ : Set G) := by
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  obtain ⟨hCA₁, hCA₂, hna₁, hna₂⟩ :=
    hU.product_facts_of_card_sylow h hS2 hR hY hinf hcomm ht₁ ht₂
  obtain ⟨hne, -, hdich⟩ := map_conj_eq_or_eq hY hinf hcomm hCA₁ hCA₂ hna₁ hna₂ htt htU ht₁ ht₂
  have hxM₂ : x ∈ normalizer ((U₁ ⊓ centralizer (Y₁ : Set G) : Subgroup G) : Set G) := by
    rcases hdich x hxU with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact mem_normalizer_iff_map_conj_eq'.mpr h2
    · exact absurd ((mem_normalizer_iff_map_conj_eq'.mp hxM).symm.trans h1) hne
  obtain ⟨E, _, _, _, σ, hEcard, hσq, hFcard, u, v, hc, -⟩ :=
    h.exists_rootCoords_of_card_sylow hS2
  have hCt : ∀ y ∈ U₁, y * t = t * y → y ∈ szT₁ L T :=
    fun y hy hyt => hU.mem_szT₁_of_commute hR hy hyt
  have hT₁ : ∀ y ∈ szT₁ L T, y ∈ U₁ ∧ y * t = t * y :=
    fun y hy => ⟨hU.le (mem_sup_left hy), hR.t_comm y hy⟩
  have hY' : Y₂ ⊔ Y₁ = U₁ := by rw [sup_comm]; exact hY
  have hinf' : Y₂ ⊓ Y₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hcomm' : ∀ a ∈ Y₂, ∀ b ∈ Y₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hc₁ := hc.of_partner htt hY hinf hcomm ht₁ ht₂ hCt hT₁
  have hc₂ := hc.of_partner htt hY' hinf' hcomm' ht₂ ht₁ hCt hT₁
  have hsq₁ : ∀ a ∈ Y₁, x * a ^ 2 * x⁻¹ = a ^ 2 := fun a ha =>
    conj_sq_eq_of_mem_normalizer hσq hEcard hFcard hc₁ hc₂ hY hinf hcomm hxx hxM hxM₂ ha
  have hsq₂ : ∀ b ∈ Y₂, x * b ^ 2 * x⁻¹ = b ^ 2 := fun b hb =>
    conj_sq_eq_of_mem_normalizer hσq hEcard hFcard hc₂ hc₁ hY' hinf' hcomm' hxx hxM₂ hxM hb
  have hsqU : ∀ w ∈ U₁, x * w ^ 2 * x⁻¹ = w ^ 2 := fun w hw =>
    conj_sq_eq_of_mem_sup hcomm hsq₁ hsq₂ (hY ▸ hw)
  have hcen : ∀ w ∈ U₁, ∀ w' ∈ U₁, ∀ z ∈ U₁, ⁅w, w'⁆ * z = z * ⁅w, w'⁆ := by
    intro w hw w' hw' z hz
    have hr : ⁅w, w'⁆ ∈ R₂ := by rw [commutatorElement_def]; exact hU.comm_mem w hw w' hw'
    exact mem_centralizer_iff.mp (hU.le_centralizer hz) _ hr
  have hle := commutator_le_centralizer_of_sq hcen hsqU
  rw [hU.commutator_eq] at hle
  exact mem_centralizer_iff.mpr fun r hr => mem_centralizer_singleton_iff.mp (hle hr)

theorem conj_not_mem_normalizer_of_product
    (hU : U3U1Data G L f t T R₂ U₁) (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U₁)
    (hinf : Y₁ ⊓ Y₂ = ⊥) (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (ht₁ : ∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) (ht₂ : ∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) (g : G)
    (hgU : g * t * g⁻¹ ∈ normalizer (U₁ : Set G)) :
    g * t * g⁻¹ ∉ normalizer ((U₁ ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G) := by
  intro hgM
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have hxx : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  exact hU.conj_not_mem_centralizer h hS2 hR g
    (hU.mem_centralizer_of_mem_normalizer h hS2 hR hY hinf hcomm ht₁ ht₂ hxx hgU hgM)

end U3U1Data

@[expose] def U3EndingSylowNormalizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ U₁ : Subgroup G)
    (s v : G) (Y₁ Y₂ : Subgroup G), U3EndingData G L f t T R₂ U₁ s → v ∈ T → v ^ 2 = 1 →
    v ∉ szT₁ L T ⊔ zpowers t → s * t * s⁻¹ = t * v →
    Y₁ ⊔ Y₂ = U₁ → Y₁ ⊓ Y₂ = ⊥ → (∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) →
    (∀ a ∈ Y₁, t * a * t⁻¹ ∈ Y₂) → (∀ b ∈ Y₂, t * b * t⁻¹ ∈ Y₁) →
      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ normalizer (U₁ : Set G)

theorem u3EndingSylowInput_of_normalizer
    (hN : U3EndingSylowNormalizerInput) : U3EndingSylowInput := by
  intro G _ _ L f t T R₂ U₁ s v Y₁ Y₂ hD hvT hv2 hvS hsv hY hinf hcomm ht₁ ht₂
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hD.start
  have hS2 := hD.card_sylow
  have hR := hD.r2
  have hU := hD.u1
  obtain ⟨S, hSN⟩ := hN G L f t T R₂ U₁ s v Y₁ Y₂ hD hvT hv2 hvS hsv hY hinf hcomm ht₁ ht₂
  have htU : t ∈ normalizer (U₁ : Set G) := hU.normalizer_le (Subgroup.le_normalizer
    (show t ∈ szT₁ L T ⊔ R₂ ⊔ zpowers t from mem_sup_right (mem_zpowers t)))
  have htP : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.inv, pow_one])
  obtain ⟨S', htS', hS'N⟩ :=
    exists_sylow_le_of_le S hSN htP ((zpowers_le (G := G)).mpr htU)
  exact ⟨S', htS' (mem_zpowers t), hS'N, fun g hg =>
    hU.conj_not_mem_normalizer_of_product h hS2 hR hY hinf hcomm ht₁ ht₂ g (hS'N hg)⟩

end CFSG.SeitzReduction.RankOne
