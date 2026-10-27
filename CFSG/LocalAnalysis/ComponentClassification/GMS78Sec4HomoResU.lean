module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4HomoRes
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Homo

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

@[expose] def GMS42ResidualT0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T U₁ : Subgroup G), Sec3 G L T → Foundation →
    Nonempty (rankTwoQuot L ≃* PSL(2, GaloisField 2 4)) → Sec3.Facts L T (2 ^ 4) →
    Lemma313 L T (2 ^ 4) → Sec4Homo L T U₁ (2 ^ 4) →
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 → ¬ T ≤ gmsV L T →
    ∀ (U : Subgroup G) (g : G), U ≤ gmsV L T → IsElemAbelian 2 (rightConjugate U g) →
    rightConjugate U g ≤ U₁ ⊔ T →
    (∀ x ∈ rightConjugate U g, Nat.card (⁅gmsV L T, zpowers x⁆ : Subgroup G) ≤ 4) →
    ∀ u ∈ U₁, u ∉ gmsA L T → ∀ t₀ ∈ T ⊓ centralizer (L : Set G), t₀ ≠ 1 →
    (∀ v ∈ U₁, t₀ * v * t₀⁻¹ = v⁻¹) → u * t₀ ∈ rightConjugate U g →
    ∀ w ∈ rightConjugate U g, w ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)) →
    Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 16 →
    g * w * g⁻¹ ∉ gmsA L T → w * w = 1 → w ≠ 1 →
    Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 4 →
    ∀ c ∈ normalizer (gmsV L T : Set G), ∀ x : G, c * w * c⁻¹ = x → x ∈ T →
    x ∉ gmsV L T → Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) = 4 →
    T ⊓ centralizer (L : Set G) ≤ centralizer ({x} : Set G) →
    ∀ y : G, y * x * y⁻¹ ∈ T ⊓ centralizer (L : Set G) →
    2 ≤ Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) ⊓ rightConjugate L y : Subgroup G) →
    False

@[expose] def GMS42ResidualRoot : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T U₁ : Subgroup G), Sec3 G L T → Foundation →
    Nonempty (rankTwoQuot L ≃* PSL(2, GaloisField 2 4)) → Sec3.Facts L T (2 ^ 4) →
    Lemma313 L T (2 ^ 4) → Sec4Homo L T U₁ (2 ^ 4) →
    Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4 → ¬ T ≤ gmsV L T →
    ∀ (U : Subgroup G) (g : G), U ≤ gmsV L T → IsElemAbelian 2 (rightConjugate U g) →
    rightConjugate U g ≤ U₁ ⊔ T →
    (∀ x ∈ rightConjugate U g, Nat.card (⁅gmsV L T, zpowers x⁆ : Subgroup G) ≤ 4) →
    ∀ u ∈ U₁, u ∉ gmsA L T → ∀ t₀ ∈ T ⊓ centralizer (L : Set G), t₀ ≠ 1 →
    (∀ v ∈ U₁, t₀ * v * t₀⁻¹ = v⁻¹) → u * t₀ ∈ rightConjugate U g →
    ∀ w ∈ rightConjugate U g, w ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)) →
    Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 16 →
    g * w * g⁻¹ ∈ gmsA L T → w * w = 1 → w ≠ 1 →
    Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 4 →
    ∀ c ∈ normalizer (gmsV L T : Set G), ∀ x : G, c * w * c⁻¹ = x → x ∈ T →
    x ∉ gmsV L T → Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) = 4 →
    T ⊓ centralizer (L : Set G) ≤ centralizer ({x} : Set G) →
    g * c⁻¹ * x * (g * c⁻¹)⁻¹ ∈ gmsA L T → False

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_mul_self {x : G} (hxx : x * x = 1) : IsPGroup 2 (zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf x ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq, hxx])
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem card_inf_centralizer_conj_eq {A : Subgroup G} {c : G}
    (hc : c ∈ normalizer (A : Set G)) (w : G) :
    Nat.card (A ⊓ centralizer ({c * w * c⁻¹} : Set G) : Subgroup G) =
      Nat.card (A ⊓ centralizer ({w} : Set G) : Subgroup G) := by
  have heq : (A ⊓ centralizer ({w} : Set G)).map (MulAut.conj c).toMonoidHom =
      A ⊓ centralizer ({c * w * c⁻¹} : Set G) := by
    ext b
    rw [mem_map_equiv, MulAut.conj_symm_apply, mem_inf, mem_inf,
      mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have hA : c⁻¹ * b * c ∈ A ↔ b ∈ A := by
      rw [mem_normalizer_iff.mp hc (c⁻¹ * b * c)]
      rw [show c * (c⁻¹ * b * c) * c⁻¹ = b by group]
    rw [hA]
    refine and_congr_right fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩
    · calc b * (c * w * c⁻¹) = c * (c⁻¹ * b * c * w) * c⁻¹ := by group
        _ = c * (w * (c⁻¹ * b * c)) * c⁻¹ := by rw [h1]
        _ = c * w * c⁻¹ * b := by group
    · calc c⁻¹ * b * c * w = c⁻¹ * (b * (c * w * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * w * c⁻¹ * b) * c := by rw [h1]
        _ = w * (c⁻¹ * b * c) := by group
  rw [← heq, card_map_of_injective (MulAut.conj c).injective]

variable {L T U₁ : Subgroup G} {f : ℕ}

theorem Lemma313.normalizer_V_le {q : ℕ} (h313 : Lemma313 L T q) :
    normalizer (gmsV L T : Set G) ≤ normalizer (gmsA L T : Set G) := by
  intro z hz
  rw [mem_normalizer_iff]
  intro a
  refine ⟨fun ha => h313.stronglyClosed a ha z
    ((mem_normalizer_iff.mp hz a).mp ((le_sup_left : gmsA L T ≤ gmsV L T) ha)), fun hza => ?_⟩
  have haV : a ∈ gmsV L T :=
    (mem_normalizer_iff.mp hz a).mpr ((le_sup_left : gmsA L T ≤ gmsV L T) hza)
  have h1 := h313.stronglyClosed _ hza z⁻¹
    (by rw [show z⁻¹ * (z * a * z⁻¹) * z⁻¹⁻¹ = a by group]; exact haV)
  rwa [show z⁻¹ * (z * a * z⁻¹) * z⁻¹⁻¹ = a by group] at h1

variable [Finite G]

namespace Sec3

theorem exists_conj_mem_normalizer_of_commute
    (h : Sec3 G L T) (hF : Foundation) {q : ℕ}
    (hX : Facts L T q) (h313 : Lemma313 L T q) {w t : G} (ht : t ∈ gmsV L T)
    (htA : t ∉ gmsA L T) (hwt : w * t = t * w) :
    ∃ z ∈ normalizer (gmsV L T : Set G), z⁻¹ * w * z ∈ normalizer (L : Set G) := by
  obtain ⟨Q, ⟨⟨x₀, rfl⟩, hQV⟩, htQ, ht1⟩ := (h313.cover t ht).mp htA
  obtain ⟨z, hz, hzQ⟩ := hX.exists_mem_normalizer h hF hQV
  have hs : z⁻¹ * t * z ∈ T ⊓ centralizer (L : Set G) := by
    rw [← hzQ, mem_rightConjugate_iff]
    rwa [show z * (z⁻¹ * t * z) * z⁻¹ = t by group]
  have hs1 : z⁻¹ * t * z ≠ 1 := fun h1 => ht1 (by
    rw [show t = z * (z⁻¹ * t * z) * z⁻¹ by group, h1]
    group)
  have hss : z⁻¹ * t * z * (z⁻¹ * t * z) = 1 := by
    rw [← sq]
    exact (h.isElemAbelian_T₀ hF).2 _ hs
  refine ⟨z, hz, h.centralizer_le_normalizer_of_mem (mem_inf.mp hs).2 hs1 hss
    (mem_centralizer_singleton_iff.mpr ?_)⟩
  calc z⁻¹ * w * z * (z⁻¹ * t * z) = z⁻¹ * (w * t) * z := by group
    _ = z⁻¹ * (t * w) * z := by rw [hwt]
    _ = z⁻¹ * t * z * (z⁻¹ * w * z) := by group

theorem T_le_normalizer_V (h : Sec3 G L T) : T ≤ normalizer (gmsV L T : Set G) := by
  intro t ht
  have h1 : t ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (le_normalizer ht) (h.sylow.le ht)
  have hA : t ∈ normalizer (gmsA L T : Set G) :=
    mem_normalizer_inf h1 (AS76b.Lemma22.normalizer_le_normalizer_centralizer _ h1)
  exact mem_normalizer_sup hA (mem_normalizer_inf (le_normalizer ht)
    (h.normalizer_le_normalizer_centralizer (h.sylow.le ht)))

theorem exists_conj_mem_T_of_mem_normalizer (h : Sec3 G L T) {x : G}
    (hxL : x ∈ normalizer (L : Set G)) (hxV : x ∈ normalizer (gmsV L T : Set G))
    (hxx : x * x = 1) : ∃ m ∈ normalizer (gmsV L T : Set G), m * x * m⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ normalizer (L : Set G) ⊓ normalizer (gmsV L T : Set G) := fun t ht =>
    mem_inf.mpr ⟨h.sylow.le ht, h.T_le_normalizer_V ht⟩
  have hS : IsSylowOf 2 T (normalizer (L : Set G) ⊓ normalizer (gmsV L T : Set G)) :=
    h.sylow.of_le hTN inf_le_left
  obtain ⟨m, hm, hmx⟩ := exists_conj_le_of_isSylowOf hS
    (zpowers_le.mpr (mem_inf.mpr ⟨hxL, hxV⟩)) (isPGroup_zpowers_of_mul_self hxx)
  exact ⟨m, (mem_inf.mp hm).2, hmx x (mem_zpowers x)⟩

theorem not_mem_V_of_card_lt
    (h : Sec3 G L T) (hF : Foundation) {q : ℕ} (hX : Facts L T q) {x : G}
    (hxc : Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G) < q) :
    x ∉ gmsV L T := by
  intro hxV
  have hVel := (hX.vFacts h hF).2.1
  have hle : gmsA L T ≤ centralizer ({x} : Set G) := fun a ha => by
    have haV : a ∈ gmsV L T := (le_sup_left : gmsA L T ≤ gmsV L T) ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, haV⟩ ⟨x, hxV⟩))
  rw [inf_eq_left.mpr hle, (hX.sylow h).1] at hxc
  exact lt_irrefl _ hxc

theorem le_centralizer_of_card
    (h : Sec3 G L T) (hF : Foundation) {q : ℕ} (hX : Facts L T q) {x : G} (hxT : x ∈ T)
    (hcard : Nat.card (gmsV L T ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (gmsA L T) =
      Nat.card (gmsV L T) * Nat.card (gmsA L T ⊓ centralizer ({x} : Set G) : Subgroup G)) :
    T ⊓ centralizer (L : Set G) ≤ centralizer ({x} : Set G) := by
  have hVel := (hX.vFacts h hF).2.1
  have hcommV : ∀ a ∈ gmsV L T, ∀ b ∈ gmsV L T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set D := gmsV L T ⊓ centralizer ({x} : Set G) with hD
  have hAV : gmsA L T ≤ gmsV L T := le_sup_left
  have hDV : D ≤ gmsV L T := inf_le_left
  have hnorm : ∀ {H K : Subgroup G}, H ≤ gmsV L T → K ≤ gmsV L T →
      H ≤ normalizer (K : Set G) := fun {H K} hH hK a ha => by
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rwa [hcommV a (hH ha) b (hK hb), mul_inv_cancel_right]
    · intro hb
      have h1 : a * b * a⁻¹ ∈ gmsV L T := hK hb
      have h2 : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [h2, hcommV _ (inv_mem (hH ha)) _ h1, mul_assoc, inv_mul_cancel, mul_one]
      exact hb
  have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (hnorm hAV hDV)
  have hDA : D ⊓ gmsA L T = gmsA L T ⊓ centralizer ({x} : Set G) := by
    rw [hD, inf_comm, ← inf_assoc, inf_eq_left.mpr hAV]
  rw [hDA] at h1
  have h2 : Nat.card (D ⊔ gmsA L T : Subgroup G) = Nat.card (gmsV L T) :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans hcard)
  have hsup : D ⊔ gmsA L T = gmsV L T := eq_of_le_of_card_ge (sup_le hDV hAV) h2.ge
  intro t ht
  have htV : t ∈ D ⊔ gmsA L T := hsup ▸ (le_sup_right : T ⊓ centralizer (L : Set G) ≤ _) ht
  obtain ⟨d, hd, a, ha, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (hnorm hDV hAV) htV
  have hxA : x * a * x⁻¹ ∈ gmsA L T := by
    have hxN : x ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) :=
      mem_normalizer_inf (le_normalizer hxT) (h.sylow.le hxT)
    exact (mem_normalizer_iff.mp (mem_normalizer_inf hxN
      (AS76b.Lemma22.normalizer_le_normalizer_centralizer _ hxN)) a).mp ha
  have hxK : x * (d * a) * x⁻¹ ∈ T ⊓ centralizer (L : Set G) :=
    (mem_normalizer_iff.mp (mem_normalizer_inf (le_normalizer hxT)
      (h.normalizer_le_normalizer_centralizer (h.sylow.le hxT))) _).mp ht
  have hdx : x * d = d * x := (mem_centralizer_singleton_iff.mp (mem_inf.mp hd).2).symm
  have hu : (d * a)⁻¹ * (x * (d * a) * x⁻¹) = a⁻¹ * (x * a * x⁻¹) := by
    calc (d * a)⁻¹ * (x * (d * a) * x⁻¹) = a⁻¹ * d⁻¹ * ((x * d) * a * x⁻¹) := by group
      _ = a⁻¹ * (x * a * x⁻¹) := by rw [hdx]; group
  have hmem : (d * a)⁻¹ * (x * (d * a) * x⁻¹) ∈
      (T ⊓ L) ⊓ (T ⊓ centralizer (L : Set G)) := by
    refine mem_inf.mpr ⟨?_, mul_mem (inv_mem ht) hxK⟩
    rw [hu]
    exact (inf_le_left : gmsA L T ≤ T ⊓ L) (mul_mem (inv_mem ha) hxA)
  rw [h.inf_eq_bot_of_odd hX.oddCenter, mem_bot] at hmem
  have h3 : x * (d * a) * x⁻¹ = d * a := by
    have := congrArg (fun y => d * a * y) hmem
    simpa [mul_assoc] using this
  refine mem_centralizer_singleton_iff.mpr ?_
  calc d * a * x = x * (d * a) * x⁻¹ * x := by rw [h3]
    _ = x * (d * a) := by group

end Sec3

namespace Sec4Homo

theorem exists_conj_mem_T
    (hE : Sec4Homo L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (h313 : Lemma313 L T (2 ^ f)) {w t : G} (hw : w ∈ U₁ ⊔ T) (hww : w * w = 1)
    (ht : t ∈ gmsV L T) (htA : t ∉ gmsA L T) (hwt : w * t = t * w) :
    ∃ c ∈ normalizer (gmsV L T : Set G), c * w * c⁻¹ ∈ T := by
  obtain ⟨z, hz, hzw⟩ := h.exists_conj_mem_normalizer_of_commute hF hX h313 ht htA hwt
  have hwV := hE.S₀_le_normalizer_V h hF hf e hw
  have hw'V : z⁻¹ * w * z ∈ normalizer (gmsV L T : Set G) :=
    mul_mem (mul_mem (inv_mem hz) hwV) hz
  have hw'w' : z⁻¹ * w * z * (z⁻¹ * w * z) = 1 := by
    calc z⁻¹ * w * z * (z⁻¹ * w * z) = z⁻¹ * (w * w) * z := by group
      _ = 1 := by rw [hww]; group
  obtain ⟨m, hm, hmT⟩ := h.exists_conj_mem_T_of_mem_normalizer hzw hw'V hw'w'
  refine ⟨m * z⁻¹, mul_mem hm (inv_mem hz), ?_⟩
  rwa [show m * z⁻¹ * w * (m * z⁻¹)⁻¹ = m * (z⁻¹ * w * z) * m⁻¹ by group]

theorem card_inf_centralizer_eq_four
    (hE : Sec4Homo L T U₁ (2 ^ 4)) (h : Sec3 G L T)
    (hF : Foundation) (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 4))
    (hX : Sec3.Facts L T (2 ^ 4))
    (hq : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4) {w : G} (hw : w ∈ U₁ ⊔ T)
    (hww : w * w = 1) (hwW : w ∉ U₁ ⊔ (T ⊓ centralizer (L : Set G)))
    (hCw : Nat.card (gmsV L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 16) :
    Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) = 4 := by
  obtain ⟨h1, h2⟩ := hE.inf_A_bound h (by norm_num) e hX hw hww hwW
    (inf_le_left : gmsV L T ⊓ centralizer ({w} : Set G) ≤ gmsV L T) inf_le_right
  have heq : (gmsV L T ⊓ centralizer ({w} : Set G)) ⊓ gmsA L T =
      gmsA L T ⊓ centralizer ({w} : Set G) := by
    rw [inf_comm, ← inf_assoc, inf_eq_left.mpr (le_sup_left : gmsA L T ≤ gmsV L T)]
  obtain ⟨hVcard, -⟩ := hX.vFacts h hF
  rw [heq, hCw, hVcard, hq] at h1
  rw [heq] at h2
  obtain ⟨d, hd⟩ : ∃ d, Nat.card (gmsA L T ⊓ centralizer ({w} : Set G) : Subgroup G) = d :=
    ⟨_, rfl⟩
  rw [hd] at h1 h2 ⊢
  norm_num at h1 h2
  nlinarith

end Sec4Homo

theorem gms42ResidualU_of
    (hT0 : GMS42ResidualT0) (hRoot : GMS42ResidualRoot) : GMS42ResidualU := by
  intro G _ _ L T U₁ h hF he hX h313 hE hq hTV U g hUV hU'el hU'S hcomm u hu huA t₀ ht₀ ht₀1
    hinv hut w hwU' hwW hCw
  obtain ⟨e⟩ := he
  have hww : w * w = 1 := by rw [← sq]; exact hU'el.2 w hwU'
  have hw1 : w ≠ 1 := fun h1 => hwW (h1 ▸ one_mem _)
  have hwS : w ∈ U₁ ⊔ T := hU'S hwU'
  have hCA := hE.card_inf_centralizer_eq_four h hF e hX hq hwS hww hwW hCw
  obtain ⟨t, htVw, htA⟩ : ∃ t ∈ gmsV L T ⊓ centralizer ({w} : Set G), t ∉ gmsA L T := by
    by_contra hall
    push Not at hall
    have hle : gmsV L T ⊓ centralizer ({w} : Set G) ≤ gmsA L T ⊓ centralizer ({w} : Set G) :=
      fun x hx => mem_inf.mpr ⟨hall x hx, (mem_inf.mp hx).2⟩
    have := card_le_of_le hle
    omega
  obtain ⟨htV, htw⟩ := mem_inf.mp htVw
  obtain ⟨c, hc, hcT⟩ := hE.exists_conj_mem_T h hF (by norm_num) e hX h313 hwS hww htV htA
    (mem_centralizer_singleton_iff.mp htw).symm
  have hcA : Nat.card (gmsA L T ⊓ centralizer ({c * w * c⁻¹} : Set G) : Subgroup G) = 4 :=
    (card_inf_centralizer_conj_eq (h313.normalizer_V_le hc) w).trans hCA
  have hcV : c * w * c⁻¹ ∉ gmsV L T := h.not_mem_V_of_card_lt hF hX (by rw [hcA]; norm_num)
  have hcT₀ : T ⊓ centralizer (L : Set G) ≤ centralizer ({c * w * c⁻¹} : Set G) := by
    refine h.le_centralizer_of_card hF hX hcT ?_
    rw [card_inf_centralizer_conj_eq hc w, hCw, hcA, (hX.sylow h).1, (hX.vFacts h hF).1, hq]
    norm_num
  have hgw : g * w * g⁻¹ ∈ gmsV L T := hUV ((mem_rightConjugate_iff _ _ _).mp hwU')
  by_cases hroot : g * w * g⁻¹ ∈ gmsA L T
  · refine hRoot G L T U₁ h hF ⟨e⟩ hX h313 hE hq hTV U g hUV hU'el hU'S hcomm u hu huA t₀ ht₀
      ht₀1 hinv hut w hwU' hwW hCw hroot hww hw1 hCA c hc _ rfl hcT hcV hcA hcT₀ ?_
    rwa [show g * c⁻¹ * (c * w * c⁻¹) * (g * c⁻¹)⁻¹ = g * w * g⁻¹ by group]
  ·
    obtain ⟨Q, ⟨⟨x₀, rfl⟩, -⟩, hwQ, -⟩ := (h313.cover _ hgw).mp hroot
    rw [mem_rightConjugate_iff] at hwQ
    have hyx : x₀ * g * c⁻¹ * (c * w * c⁻¹) * (x₀ * g * c⁻¹)⁻¹ ∈
        T ⊓ centralizer (L : Set G) := by
      rwa [show x₀ * g * c⁻¹ * (c * w * c⁻¹) * (x₀ * g * c⁻¹)⁻¹ =
        x₀ * (g * w * g⁻¹) * x₀⁻¹ by group]
    have hx1 : c * w * c⁻¹ ≠ 1 := fun h1 => hw1 (conj_eq_one_iff.mp h1)
    have hxx : c * w * c⁻¹ * (c * w * c⁻¹) = 1 := by
      calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
        _ = 1 := by rw [hww]; group
    have hP3 := h.card_le_two_mul_inf_rightConjugate (by norm_num : 3 ≤ 4) e h313
      (mem_inf.mp hyx).2 hx1 hxx (E := gmsA L T ⊓ centralizer ({c * w * c⁻¹} : Set G))
      inf_le_left inf_le_right
    rw [hcA] at hP3
    exact hT0 G L T U₁ h hF ⟨e⟩ hX h313 hE hq hTV U g hUV hU'el hU'S hcomm u hu huA t₀ ht₀
      ht₀1 hinv hut w hwU' hwW hCw hroot hww hw1 hCA c hc _ rfl hcT hcV hcA hcT₀ _ hyx
      (by omega)

end CFSG.ComponentClassification.GMS78
