module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5Swap
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5SwapF5

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII

variable {G : Type} [Group G] [Finite G]

namespace Sec3.SzR

variable {L T R R₂ : Subgroup G} {a : ℕ} {y d : G}

structure SwapElt (L T R R₂ : Subgroup G) (w : G) : Prop where
  mem_normalizer : w ∈ normalizer (R : Set G)
  conj_V : rightConjugate (gmsV L T) w = R₂
  pow_two_pow : ∃ k : ℕ, w ^ 2 ^ k = 1
  sq_mem : w ^ 2 ∈ R


theorem gmsV_ne_isR₂ (hS : SzR G L T R a y d) (hR₂ : IsR₂ L T R R₂ d) : gmsV L T ≠ R₂ := by
  intro h
  obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hS.sec3.T₀_ne_bot
  have hs1' : s ≠ 1 := fun h' => hs1 (Subtype.ext h')
  have hsR₂ : s ∈ R₂ := h ▸ (mem_sup_right hs : s ∈ gmsV L T)
  have hsA : s ∈ gmsA L T := by rw [← hR₂.inf_eq]; exact mem_inf.mpr ⟨(mem_inf.mp hs).1, hsR₂⟩
  have hs' : s ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨hs, hsA⟩
  rw [hS.lemma313.inf_gmsA_eq_bot mem_delta_T₀, mem_bot] at hs'
  exact hs1' hs'

theorem rightConjugate_isR₂_eq (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) {g : G}
    (hg : g ∈ normalizer (R : Set G)) (hgV : rightConjugate (gmsV L T) g = R₂) :
    rightConjugate R₂ g = gmsV L T := by
  by_contra h
  have h2 : rightConjugate (gmsV L T) (g * g) ≠ gmsV L T := by
    rwa [← rightConjugate_mul, hgV]
  have h1 := (hS.swap_of_ne h34 hR₂ h4 hne (mul_mem hg hg) h2).2.2.2
  rw [← rightConjugate_mul, hgV] at h1
  have h3 := congrArg (fun H => rightConjugate H g⁻¹) (h1.trans hgV.symm)
  simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h3
  exact hS.gmsV_ne_isR₂ hR₂ h3.symm

theorem exists_swapElt (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) {g : G}
    (hg : g ∈ normalizer (R : Set G)) (hgV : rightConjugate (gmsV L T) g = R₂) :
    ∃ w : G, SwapElt L T R R₂ w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgR₂ := hS.rightConjugate_isR₂_eq h34 hR₂ h4 hne hg hgV
  have hg2 : rightConjugate (gmsV L T) (g * g) = gmsV L T := by
    rw [← rightConjugate_mul, hgV, hgR₂]
  have heven : ∀ n : ℕ, rightConjugate (gmsV L T) (g ^ (2 * n)) = gmsV L T := by
    intro n
    induction n with
    | zero => simp [rightConjugate_one]
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, sq, ← rightConjugate_mul, ih, hg2]
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  obtain ⟨m', hm'⟩ := hm
  have hw1 : (g ^ m) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  refine ⟨g ^ m, ⟨pow_mem hg _, ?_, ⟨k, hw1⟩, ?_⟩⟩
  · rw [hm', pow_succ, ← rightConjugate_mul, heven, hgV]
  ·
    have hzV : (g ^ m) ^ 2 ∈ normalizer (gmsV L T : Set G) := by
      rw [← rightConjugate_eq_self_iff, ← pow_mul, show m * 2 = 2 * m by ring, heven]
    have hzR : (g ^ m) ^ 2 ∈ normalizer (R : Set G) := pow_mem (pow_mem hg _) 2
    have hzp : IsPGroup 2 (zpowers ((g ^ m) ^ 2)) := by
      have hz1 : ((g ^ m) ^ 2) ^ 2 ^ k = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hw1, one_pow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz1)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hR := hS.isSylowOf_normalizer
    have heq := hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hzV))
      (IsPGroup.to_sup_of_normal_left' hR.isPGroup hzp (zpowers_le.mpr hzR))
    exact heq ▸ mem_sup_right (mem_zpowers _)

theorem mem_T₁_of_commute (hS : SzR G L T R a y d) (hR₂ : IsR₂ L T R R₂ d)
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {t : G} (ht : t ∈ R)
    (htV : ∀ v ∈ gmsV L T, t * v = v * t) (htR₂ : ∀ r ∈ R₂, t * r = r * t) : t ∈ T ⊓ L := by
  have htT : t ∈ T := by
    rw [← hS.inf_centralizer_R]
    exact mem_inf.mpr ⟨ht, mem_centralizer_iff.mpr fun v hv => (htV v hv).symm⟩
  obtain ⟨t₁, ht₁, s, hs, rfl⟩ := hS.exists_mul_of_mem_T htT
  by_cases hs1 : s = 1
  · rw [hs1, mul_one]; exact ht₁
  exfalso
  obtain ⟨r, hr, hrA⟩ := hS.exists_mem_isR₂_not_mem_gmsA hR₂
  apply hrA
  rw [← hS.commutator_eq_one_iff hR₂ hs hs1 hr]
  have h1 := htR₂ r hr
  have h2 := hcomm t₁ ht₁ r hr
  have hrs : r * s = s * r := by
    calc r * s = t₁⁻¹ * (r * t₁) * s := by rw [← h2]; group
      _ = t₁⁻¹ * (r * (t₁ * s)) := by group
      _ = t₁⁻¹ * (t₁ * s * r) := by rw [h1]
      _ = s * r := by group
  rw [hrs]
  group

theorem commute_gmsV_of_mem_T₁ (hS : SzR G L T R a y d) {t : G} (ht : t ∈ T ⊓ L) {v : G}
    (hv : v ∈ gmsV L T) : t * v = v * t := by
  obtain ⟨-, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have := mem_centralizer_iff.mp (hVC hv) t (by rw [← hS.eq_gmsW]; exact (mem_inf.mp ht).1)
  exact this

theorem SwapElt.conj_R₂ {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) :
    rightConjugate R₂ w = gmsV L T :=
  hS.rightConjugate_isR₂_eq h34 hR₂ h4 hne hw.mem_normalizer hw.conj_V

theorem SwapElt.mem_normalizer_T₁ {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) :
    w ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hR₂w := hw.conj_R₂ hS h34 hR₂ h4 hne
  refine mem_normalizer_of_conj_mem_of_finite fun t ht => ?_
  have htR : t ∈ R := hS.T_le (mem_inf.mp ht).1
  refine hS.mem_T₁_of_commute hR₂ hcomm ((mem_normalizer_iff.mp hw.mem_normalizer t).mp htR)
    (fun v hv => ?_) (fun r hr => ?_)
  ·
    have hv' : w⁻¹ * v * w ∈ R₂ := by
      rw [← hw.conj_V, mem_rightConjugate_iff]
      simpa [mul_assoc] using hv
    have h := hcomm t ht _ hv'
    calc w * t * w⁻¹ * v = w * (t * (w⁻¹ * v * w)) * w⁻¹ := by group
      _ = w * (w⁻¹ * v * w * t) * w⁻¹ := by rw [h]
      _ = v * (w * t * w⁻¹) := by group
  ·
    have hr' : w⁻¹ * r * w ∈ gmsV L T := by
      rw [← hR₂w, mem_rightConjugate_iff]
      simpa [mul_assoc] using hr
    have h := hS.commute_gmsV_of_mem_T₁ ht hr'
    calc w * t * w⁻¹ * r = w * (t * (w⁻¹ * r * w)) * w⁻¹ := by group
      _ = w * (w⁻¹ * r * w * t) * w⁻¹ := by rw [h]
      _ = r * (w * t * w⁻¹) := by group

theorem conj_eq_of_two_elt (hS : SzR G L T R a y d) {x : G}
    (hx : x ∈ normalizer ((T ⊓ L : Subgroup G) : Set G)) {k : ℕ} (hxk : x ^ 2 ^ k = 1) :
    (∀ b ∈ gmsA L T, x * b * x⁻¹ = b) ∧ ∀ t ∈ T ⊓ L, x * t * x⁻¹ * t⁻¹ ∈ gmsA L T := by
  obtain ⟨u, v, κ, hc, -⟩ := hS.exists_rootCoords
  obtain ⟨h1, h2⟩ := hc.conj_eq_of_pow_two_pow_eq_one hS.one_le hx hxk
  refine ⟨fun b hb => h2 b (mem_inf.mp hb).1 (hS.u_eq_zero_of_mem_gmsA hc hb), fun t ht => ?_⟩
  have hxt : x * t * x⁻¹ ∈ T ⊓ L := (mem_normalizer_iff.mp hx t).mp ht
  have hmem : x * t * x⁻¹ * t⁻¹ ∈ T ⊓ L := mul_mem hxt (inv_mem ht)
  refine (hc.mem_center_iff hS.one_le hmem).mpr ?_
  rw [(hc.mul _ hxt _ (inv_mem ht)).1, (hc.inv ht).1, h1 t ht]
  exact CharTwo.add_self_eq_zero _

theorem SwapElt.exists_phi_conj {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    (hC : RCoords L T R R₂ a v φ 0 0 ⊤) :
    ∃ κ₀ : BinaryGaloisField (2 * a + 1), κ₀ ≠ 0 ∧
      ∀ z ∈ R, φ (w * z * w⁻¹) = ((φ z).1, (φ z).2.2 / κ₀, κ₀ * (φ z).2.1) := by
  obtain ⟨k, hk⟩ := hw.pow_two_pow
  obtain ⟨hwA, hwT⟩ := hS.conj_eq_of_two_elt (hw.mem_normalizer_T₁ hS h34 hR₂ h4 hne hcomm) hk
  have hR₂w := hw.conj_R₂ hS h34 hR₂ h4 hne
  have hwR : ∀ z ∈ R, w * z * w⁻¹ ∈ R := fun z hz =>
    (mem_normalizer_iff.mp hw.mem_normalizer z).mp hz
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hT₀R : ∀ s ∈ T ⊓ centralizer (L : Set G), s ∈ R := fun s hs => hS.T_le (mem_inf.mp hs).1
  have hsR₂ : ∀ s ∈ T ⊓ centralizer (L : Set G), w * s * w⁻¹ ∈ R₂ := fun s hs => by
    have : s ∈ rightConjugate R₂ w := by rw [hR₂w]; exact mem_sup_right hs
    exact (mem_rightConjugate_iff _ _ _).mp this
  have hrV : ∀ r ∈ R₂, w * r * w⁻¹ ∈ gmsV L T := fun r hr => by
    have : r ∈ rightConjugate (gmsV L T) w := by rw [hw.conj_V]; exact hr
    exact (mem_rightConjugate_iff _ _ _).mp this
  have hA₁N : gmsA L T ≤ normalizer ((T ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    fun b hb => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun s hs =>
      (mem_centralizer_iff.mp (mem_inf.mp hs).2 b (mem_inf.mp (mem_inf.mp hb).1).2).symm)
  have hφV : ∀ x ∈ gmsV L T, (φ x).1 = 0 ∧ (φ x).2.1 = 0 := by
    intro x hx
    obtain ⟨b, hb, s, hs, rfl⟩ := CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hA₁N hx
    have hbR : b ∈ R := hS.T_le (Sec3.SzR.gmsA_le_T hb)
    rw [hC.mul _ hbR _ (hT₀R s hs), (hC.ker b hbR).mpr hb, zero_add]
    exact hC.of_T₀ s hs
  have hpair : ∀ s ∈ T ⊓ centralizer (L : Set G), ∀ r ∈ R₂,
      (φ (w * s * w⁻¹)).2.1 * (φ (w * r * w⁻¹)).2.2 = (φ s).2.2 * (φ r).2.1 := by
    intro s hs r hr
    have hrR := hR₂.le_R hr
    have hsR := hT₀R s hs
    have hcA := hS.commutator_mem_gmsA h34 hsR hrR
    have e1 : w * s * w⁻¹ * (w * r * w⁻¹) * (w * s * w⁻¹)⁻¹ * (w * r * w⁻¹)⁻¹ =
        w * (s * r * s⁻¹ * r⁻¹) * w⁻¹ := by group
    have h1 := hC.comm _ (hwR s hsR) _ (hwR r hrR)
    rw [e1, hwA _ hcA, hC.comm _ hsR _ hrR] at h1
    obtain ⟨hs1, hs2⟩ := hC.of_R₂ _ (hsR₂ s hs)
    obtain ⟨hr1, hr2⟩ := hφV _ (hrV r hr)
    obtain ⟨hs1', hs2'⟩ := hC.of_T₀ s hs
    obtain ⟨hr1', hr2'⟩ := hC.of_R₂ r hr
    simp only [VLike.commMap, hs1, hs2, hr1, hr2, hs1', hs2', hr1', hr2', zero_mul, mul_zero,
      add_zero, zero_add] at h1
    linear_combination -h1
  obtain ⟨s₁, hs₁, hs₁φ⟩ := hC.T₀_surj 1 (AddSubgroup.mem_top _)
  obtain ⟨r₁, hr₁, hr₁φ⟩ := hC.R₂_surj 1
  set κ₀ := (φ (w * r₁ * w⁻¹)).2.2 with hκ₀
  have h11 := hpair s₁ hs₁ r₁ hr₁
  rw [hs₁φ, hr₁φ, mul_one] at h11
  have hκ₀0 : κ₀ ≠ 0 := by
    intro h0
    rw [← hκ₀, h0, mul_zero] at h11
    exact zero_ne_one h11
  have hα : ∀ s ∈ T ⊓ centralizer (L : Set G), (φ (w * s * w⁻¹)).2.1 = (φ s).2.2 / κ₀ := by
    intro s hs
    have h := hpair s hs r₁ hr₁
    rw [hr₁φ, mul_one, ← hκ₀] at h
    rw [eq_div_iff hκ₀0, h]
  have hβ : ∀ r ∈ R₂, (φ (w * r * w⁻¹)).2.2 = κ₀ * (φ r).2.1 := by
    intro r hr
    have h := hpair s₁ hs₁ r hr
    rw [hα s₁ hs₁, hs₁φ] at h
    field_simp at h
    linear_combination h
  refine ⟨κ₀, hκ₀0, fun z hz => ?_⟩
  obtain ⟨t, ht, r, hr, s, hs, rfl⟩ := hS.exists_decomp h34 hR₂ hz
  have htR : t ∈ R := hS.T_le (mem_inf.mp ht).1
  have hrR := hR₂.le_R hr
  have hsR := hT₀R s hs
  have e1 : w * (t * r * s) * w⁻¹ = w * t * w⁻¹ * (w * r * w⁻¹) * (w * s * w⁻¹) := by group
  have hφt : φ (w * t * w⁻¹) = φ t := by
    have e2 : w * t * w⁻¹ = (w * t * w⁻¹ * t⁻¹) * t := by group
    rw [e2, hC.mul _ (mul_mem (hwR t htR) (inv_mem htR)) _ htR,
      (hC.ker _ (mul_mem (hwR t htR) (inv_mem htR))).mpr (hwT t ht), zero_add]
  rw [e1, hC.mul _ (mul_mem (hwR t htR) (hwR r hrR)) _ (hwR s hsR),
    hC.mul _ (hwR t htR) _ (hwR r hrR), hC.mul _ (mul_mem htR hrR) _ hsR, hC.mul _ htR _ hrR, hφt]
  obtain ⟨ht1, ht2⟩ := hC.of_T₁ t ht
  obtain ⟨hr1, hr2⟩ := hC.of_R₂ r hr
  obtain ⟨hs1, hs2⟩ := hC.of_T₀ s hs
  obtain ⟨hwr1, hwr2⟩ := hφV _ (hrV r hr)
  obtain ⟨hws1, hws2⟩ := hC.of_R₂ _ (hsR₂ s hs)
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_add, hwr1, hws1, hr1, hs1, add_zero]
  · simp only [Prod.snd_add, Prod.fst_add, hwr2, hα s hs, ht1, ht2, hr2, zero_add, add_zero]
  · simp only [Prod.snd_add, Prod.fst_add, hβ r hr, hws2, ht1, ht2, hs2, zero_add, add_zero]

omit [Finite G] in
theorem SwapElt.mem_sup_iff {w : G} (hw : SwapElt L T R R₂ w) {z : G} :
    z ∈ R ⊔ zpowers w ↔ z ∈ R ∨ z * w⁻¹ ∈ R := by
  constructor
  · intro hz
    rw [sup_comm] at hz
    obtain ⟨x, hx, r, hr, rfl⟩ :=
      CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer (zpowers_le.mpr hw.mem_normalizer) hz
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hx
    have hw2 : ∀ i : ℤ, w ^ (2 * i) ∈ R := fun i => by
      rw [zpow_mul, zpow_ofNat, sq]
      exact zpow_mem (by rw [← sq]; exact hw.sq_mem) i
    rcases Int.even_or_odd j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · left
      rw [← two_mul]
      exact mul_mem (hw2 i) hr
    · right
      have e : w ^ (2 * i + 1) * r * w⁻¹ = w ^ (2 * i) * (w * r * w⁻¹) := by
        rw [zpow_add_one]; group
      rw [e]
      exact mul_mem (hw2 i) ((mem_normalizer_iff.mp hw.mem_normalizer r).mp hr)
  · rintro (hz | hz)
    · exact mem_sup_left hz
    · have e : z = z * w⁻¹ * w := by group
      rw [e]
      exact mul_mem (mem_sup_left hz) (mem_sup_right (mem_zpowers w))

theorem SwapElt.isPGroup_sup {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d) :
    IsPGroup 2 (R ⊔ zpowers w : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hw.pow_two_pow
  have hwp : IsPGroup 2 (zpowers w) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  exact IsPGroup.to_sup_of_normal_left' hS.isR.isPGroup hwp (zpowers_le.mpr hw.mem_normalizer)

theorem SwapElt.commute_gmsA {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {z : G} (hz : z ∈ R ⊔ zpowers w) {b : G}
    (hb : b ∈ gmsA L T) : z * b = b * z := by
  obtain ⟨k, hk⟩ := hw.pow_two_pow
  obtain ⟨hwA, -⟩ := hS.conj_eq_of_two_elt (hw.mem_normalizer_T₁ hS h34 hR₂ h4 hne hcomm) hk
  rcases hw.mem_sup_iff.mp hz with hz | hz
  · exact hS.commute_gmsA hz hb
  · have h1 := hS.commute_gmsA hz hb
    have h2 := hwA b hb
    calc z * b = z * w⁻¹ * (w * b * w⁻¹) * w := by group
      _ = z * w⁻¹ * b * w := by rw [h2]
      _ = b * (z * w⁻¹) * w := by rw [h1]
      _ = b * z := by group

theorem SwapElt.mem_gmsA_of_forall_commute {w : G} (hw : SwapElt L T R R₂ w)
    (hS : SzR G L T R a y d) (hR₂ : IsR₂ L T R R₂ d) {z : G} (hz : z ∈ R ⊔ zpowers w)
    (hzc : ∀ x ∈ R ⊔ zpowers w, x * z = z * x) : z ∈ gmsA L T := by
  have hzR : z ∈ R := by
    rcases hw.mem_sup_iff.mp hz with hz | hz
    · exact hz
    exfalso
    have hzV : rightConjugate (gmsV L T) z = gmsV L T := by
      rw [rightConjugate_eq_self_iff]
      refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun v hv => ?_)
      exact hzc v (mem_sup_left (hS.gmsV_le_R hv))
    have e : z = z * w⁻¹ * w := by group
    rw [e, ← rightConjugate_mul, (rightConjugate_eq_self_iff _ _).mpr
      (hS.isR.le_normalizer_gmsV hz), hw.conj_V] at hzV
    exact hS.gmsV_ne_isR₂ hR₂ hzV.symm
  exact hS.mem_gmsA_of_forall_commute hR₂ hzR fun r hr => hzc r (mem_sup_left hr)

theorem SwapElt.mem_normalizer_R {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) {n : G}
    (hn : n ∈ normalizer ((R ⊔ zpowers w : Subgroup G) : Set G)) :
    n ∈ normalizer (R : Set G) := by
  classical
  set S₁ : Subgroup G := R ⊔ zpowers w with hS₁
  have hnS : ∀ z ∈ S₁, n * z * n⁻¹ ∈ S₁ := fun z hz => (mem_normalizer_iff.mp hn z).mp hz
  have hnS' : ∀ z ∈ S₁, n⁻¹ * z * n ∈ S₁ := fun z hz => by
    simpa using (mem_normalizer_iff.mp (inv_mem hn) z).mp hz
  have hnA : ∀ b ∈ gmsA L T, n * b * n⁻¹ ∈ gmsA L T := by
    intro b hb
    have hbS : b ∈ S₁ := mem_sup_left (hS.T_le (Sec3.SzR.gmsA_le_T hb))
    refine hw.mem_gmsA_of_forall_commute hS hR₂ (hnS b hbS) fun x hx => ?_
    have h1 := hw.commute_gmsA hS h34 hR₂ h4 hne hcomm (hnS' x hx) hb
    calc x * (n * b * n⁻¹) = n * (n⁻¹ * x * n * b) * n⁻¹ := by group
      _ = n * (b * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
      _ = n * b * n⁻¹ * x := by group
  refine mem_normalizer_of_conj_mem_of_finite fun r hr => ?_
  by_contra hnr
  set x := n * r * n⁻¹ with hx
  have hxS : x ∈ S₁ := hnS r (mem_sup_left hr)
  have hxw : x * w⁻¹ ∈ R := (hw.mem_sup_iff.mp hxS).resolve_left hnr
  have hRn : ∀ z ∈ R, n * z * n⁻¹ * x * (n * z * n⁻¹)⁻¹ * x⁻¹ ∈ gmsA L T := by
    intro z hz
    have e : n * z * n⁻¹ * x * (n * z * n⁻¹)⁻¹ * x⁻¹ = n * (z * r * z⁻¹ * r⁻¹) * n⁻¹ := by
      rw [hx]; group
    rw [e]
    exact hnA _ (hS.commutator_mem_gmsA h34 hz hr)
  have hVA : ∀ v ∈ gmsV L T, (∃ z ∈ R, n * z * n⁻¹ = v) → v ∈ gmsA L T := by
    rintro v hv ⟨z, hz, hzv⟩
    have hc := hRn z hz
    rw [hzv] at hc
    have hxR₂ : x⁻¹ * v * x ∈ R₂ := by
      have e : x⁻¹ * v * x = w⁻¹ * ((x * w⁻¹)⁻¹ * v * (x * w⁻¹)) * w := by group
      rw [e, ← hw.conj_V, mem_rightConjugate_iff]
      have : (x * w⁻¹)⁻¹ * v * (x * w⁻¹) ∈ gmsV L T := by
        simpa using (mem_normalizer_iff.mp (inv_mem (hS.isR.le_normalizer_gmsV hxw)) v).mp hv
      simpa [mul_assoc] using this
    have hxV : x⁻¹ * v * x ∈ gmsV L T := by
      have hxA : x⁻¹ * (v * x * v⁻¹ * x⁻¹) * x ∈ gmsA L T := by
        have hxA' := hw.commute_gmsA hS h34 hR₂ h4 hne hcomm (inv_mem hxS) hc
        have e : x⁻¹ * (v * x * v⁻¹ * x⁻¹) * x = v * x * v⁻¹ * x⁻¹ := by
          calc x⁻¹ * (v * x * v⁻¹ * x⁻¹) * x = (x⁻¹ * (v * x * v⁻¹ * x⁻¹)) * x := rfl
            _ = (v * x * v⁻¹ * x⁻¹ * x⁻¹) * x := by rw [hxA']
            _ = v * x * v⁻¹ * x⁻¹ := by group
        rw [e]
        exact hc
      have e : x⁻¹ * v * x = x⁻¹ * (v * x * v⁻¹ * x⁻¹) * x * v := by group
      rw [e]
      exact mul_mem (mem_sup_left hxA) hv
    have hA : x⁻¹ * v * x ∈ gmsA L T := by
      rw [← hR₂.inf_eq]
      exact mem_inf.mpr ⟨hS.eq_gmsW ▸ hS.gmsV_le hxV, hxR₂⟩
    have hxx := hw.commute_gmsA hS h34 hR₂ h4 hne hcomm hxS hA
    have e : v = x * (x⁻¹ * v * x) * x⁻¹ := by group
    rw [e, hxx]
    simpa using hA
  obtain ⟨hVc, -, -, -, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  obtain ⟨hAc, -, -⟩ := hS.facts.sylow hS.sec3
  have hcard : Nat.card (gmsV L T) ≤ 2 * Nat.card (gmsA L T) := by
    by_cases hall : ∀ v ∈ gmsV L T, ∃ z ∈ R, n * z * n⁻¹ = v
    · have hle : gmsV L T ≤ gmsA L T := fun v hv => hVA v hv (hall v hv)
      have := Subgroup.card_le_of_le hle
      omega
    push Not at hall
    obtain ⟨v₀, hv₀, hv₀R⟩ := hall
    have hsplit : ∀ v ∈ gmsV L T, v ∈ gmsA L T ∨ v₀⁻¹ * v ∈ gmsA L T := by
      intro v hv
      by_cases hvR : ∃ z ∈ R, n * z * n⁻¹ = v
      · exact Or.inl (hVA v hv hvR)
      right
      push Not at hvR
      refine hVA _ (mul_mem (inv_mem hv₀) hv) ⟨n⁻¹ * (v₀⁻¹ * v) * n, ?_, by group⟩
      have h1 : (n⁻¹ * v₀ * n) * w⁻¹ ∈ R := by
        refine (hw.mem_sup_iff.mp (hnS' _ (mem_sup_left (hS.gmsV_le_R hv₀)))).resolve_left ?_
        intro h
        exact hv₀R _ h (by group)
      have h2 : (n⁻¹ * v * n) * w⁻¹ ∈ R := by
        refine (hw.mem_sup_iff.mp (hnS' _ (mem_sup_left (hS.gmsV_le_R hv)))).resolve_left ?_
        intro h
        exact hvR _ h (by group)
      have h3 : w * (n⁻¹ * (v₀⁻¹ * v) * n) * w⁻¹ ∈ R := by
        have e : w * (n⁻¹ * (v₀⁻¹ * v) * n) * w⁻¹ =
            ((n⁻¹ * v₀ * n) * w⁻¹)⁻¹ * ((n⁻¹ * v * n) * w⁻¹) := by group
        rw [e]
        exact mul_mem (inv_mem h1) h2
      simpa [mul_assoc] using (mem_normalizer_iff.mp (inv_mem hw.mem_normalizer) _).mp h3
    let f : gmsV L T → gmsA L T × Fin 2 := fun v =>
      if h : (v : G) ∈ gmsA L T then (⟨v, h⟩, 0) else
        (⟨v₀⁻¹ * v, (hsplit v v.2).resolve_left h⟩, 1)
    have hf : Function.Injective f := by
      intro v v' hvv
      simp only [f] at hvv
      by_cases h : (v : G) ∈ gmsA L T <;> by_cases h' : (v' : G) ∈ gmsA L T <;>
        simp only [h, h', ↓reduceDIte, Prod.mk.injEq] at hvv
      · exact Subtype.ext (Subtype.mk.inj hvv.1)
      · exact absurd hvv.2 (by decide)
      · exact absurd hvv.2 (by decide)
      · exact Subtype.ext (mul_left_cancel (Subtype.mk.inj hvv.1))
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at this
    omega
  rw [hVc, hAc] at hcard
  have hq : 0 < 2 ^ (2 * a + 1) := by positivity
  nlinarith

theorem SwapElt.isSylowOf_top {w : G} (hw : SwapElt L T R R₂ w) (hS : SzR G L T R a y d)
    (h34 : NoStronglyClosedAbelian G) (hR₂ : IsR₂ L T R R₂ d)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4))
    (hcomm : ∀ x ∈ T ⊓ L, ∀ r ∈ R₂, x * r = r * x) :
    IsSylowOf 2 (R ⊔ zpowers w : Subgroup G) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨S, hS₁S, z, hzS, hzN, hzS₁⟩ :=
    exists_mem_normalizer_of_not_isSylowOf (hw.isPGroup_sup hS) hnot
  have hzR := hw.mem_normalizer_R hS h34 hR₂ h4 hne hcomm hzN
  have hR := hS.isSylowOf_normalizer
  have key : ∀ z' ∈ (S : Subgroup G), z' ∈ normalizer (R : Set G) →
      z' ∈ normalizer (gmsV L T : Set G) → z' ∈ R := by
    intro z' hz'S hz'R hz'V
    have hp : IsPGroup 2 (zpowers z') := S.isPGroup'.to_le (zpowers_le.mpr hz'S)
    have heq := hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hz'V))
      (IsPGroup.to_sup_of_normal_left' hR.isPGroup hp (zpowers_le.mpr hz'R))
    exact heq ▸ mem_sup_right (mem_zpowers z')
  by_cases hzV : rightConjugate (gmsV L T) z = gmsV L T
  · exact hzS₁ (mem_sup_left (key z hzS hzR ((rightConjugate_eq_self_iff _ _).mp hzV)))
  · have hzV' := (hS.swap_of_ne h34 hR₂ h4 hne hzR hzV).2.2.2
    have hw' : z * w⁻¹ ∈ normalizer (gmsV L T : Set G) := by
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hzV', ← hw.conj_V,
        rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
    have hwS : w ∈ (S : Subgroup G) := hS₁S (mem_sup_right (mem_zpowers w))
    have hmem := key (z * w⁻¹) (mul_mem hzS (inv_mem hwS))
      (mul_mem hzR (inv_mem hw.mem_normalizer)) hw'
    exact hzS₁ (hw.mem_sup_iff.mpr (Or.inr hmem))

theorem swapShape (hS : SzR G L T R a y d) (h34 : NoStronglyClosedAbelian G)
    (hR₂ : IsR₂ L T R R₂ d) {v : G → BinaryGaloisField (2 * a + 1)}
    {φ : G → BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1)}
    {c e : BinaryGaloisField (2 * a + 1)} {Λ : AddSubgroup (BinaryGaloisField (2 * a + 1))}
    (hC : RCoords L T R R₂ a v φ c e Λ)
    (h4 : 4 ≤ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G))
    (hne : ¬ (a = 1 ∧ Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) = 4)) {g : G}
    (hg : g ∈ normalizer (R : Set G)) (hgV : rightConjugate (gmsV L T) g ≠ gmsV L T) :
    c = 0 ∧ e = 0 ∧ Λ = ⊤ := by
  classical
  have : Fintype (BinaryGaloisField (2 * a + 1)) := Fintype.ofFinite _
  have hK : Fintype.card (BinaryGaloisField (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 (2 * a + 1) (by omega)]
  obtain ⟨X, hX⟩ := hS.exists_isX h34
  obtain ⟨hVc, -, -, hVC, -⟩ := hS.facts.vFacts hS.sec3 hS.foundation
  have hT₀el := hS.sec3.isElemAbelian_T₀ hS.foundation
  have hcomm : ∀ x ∈ R, ∀ z ∈ R, x * z * x⁻¹ * z⁻¹ ∈ gmsA L T := fun x hx z hz =>
    hS.commutator_mem_gmsA h34 hx hz
  have hgN := hS.normalizer_le_normalizer_gmsA hR₂ hg
  have hgA : ∀ b ∈ gmsA L T, g * b * g⁻¹ ∈ gmsA L T := fun b hb =>
    (mem_normalizer_iff.mp hgN b).mp hb
  have hgA' : ∀ b ∈ gmsA L T, g⁻¹ * b * g ∈ gmsA L T := fun b hb => by
    simpa using (mem_normalizer_iff.mp (inv_mem hgN) b).mp hb
  have hgR : ∀ x ∈ R, g⁻¹ * x * g ∈ R := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem hg) x).mp hx
  have hgR' : ∀ x ∈ R, g * x * g⁻¹ ∈ R := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  have hT₀R : ∀ s ∈ T ⊓ centralizer (L : Set G), s ∈ R := fun s hs => hS.T_le (mem_inf.mp hs).1
  have hv1 : v 1 = 0 := by
    have h := hC.v_mul 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination -h
  have hφ1 : φ 1 = 0 := (hC.ker 1 (one_mem _)).mpr (one_mem _)
  have hφeq : ∀ x ∈ R, ∀ x' ∈ R, φ x = φ x' → x * x'⁻¹ ∈ gmsA L T := by
    intro x hx x' hx' h
    rw [← hC.ker _ (mul_mem hx (inv_mem hx')), hC.mul _ hx _ (inv_mem hx'), h,
      ← hC.mul _ hx' _ (inv_mem hx'), mul_inv_cancel, hφ1]
  obtain ⟨E, hE⟩ : ∃ E : AddSubgroup (BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1)),
      ∀ z, z ∈ E ↔ ∃ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = z :=
    ⟨{ carrier := {z | ∃ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = z}
       add_mem' := by
         rintro _ _ ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
         refine ⟨s * s', mul_mem hs hs', ?_⟩
         rw [← hC.mul _ (hgR _ (hT₀R s hs)) _ (hgR _ (hT₀R s' hs'))]
         congr 1
         group
       zero_mem' := ⟨1, one_mem _, by rw [show g⁻¹ * 1 * g = 1 by group, hφ1]⟩
       neg_mem' := by
         rintro _ ⟨s, hs, rfl⟩
         exact ⟨s, hs, Prod.ext (CharTwo.neg_eq _).symm
           (Prod.ext (CharTwo.neg_eq _).symm (CharTwo.neg_eq _).symm)⟩ }, fun z => Iff.rfl⟩
  have hφs0 : ∀ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) = 0 → s = 1 := by
    intro s hs h0
    have hA := (hC.ker _ (hgR _ (hT₀R s hs))).mp h0
    have hsA : s ∈ gmsA L T := by simpa [mul_assoc] using hgA _ hA
    have hs' : s ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨hs, hsA⟩
    rw [hS.lemma313.inf_gmsA_eq_bot mem_delta_T₀, mem_bot] at hs'
    exact hs'
  have hs1 : ∀ s ∈ T ⊓ centralizer (L : Set G), φ (g⁻¹ * s * g) ≠ 0 → s ≠ 1 := by
    rintro s - h rfl
    exact h (by rw [show g⁻¹ * 1 * g = 1 by group, hφ1])
  have htwo : ∃ z ∈ E, ∃ z' ∈ E, z ≠ 0 ∧ z' ≠ 0 ∧ z ≠ z' := by
    obtain ⟨s₁, hs₁, s₂, hs₂, h1, h2, h12⟩ := exists_two_ne_one_of_four_le h4
    refine ⟨_, (hE _).mpr ⟨s₁, hs₁, rfl⟩, _, (hE _).mpr ⟨s₂, hs₂, rfl⟩,
      fun h => h1 (hφs0 _ hs₁ h), fun h => h2 (hφs0 _ hs₂ h), fun h => h12 ?_⟩
    have h3 : φ (g⁻¹ * (s₁ * s₂) * g) = 0 := by
      rw [show g⁻¹ * (s₁ * s₂) * g = g⁻¹ * s₁ * g * (g⁻¹ * s₂ * g) by group,
        hC.mul _ (hgR _ (hT₀R _ hs₁)) _ (hgR _ (hT₀R _ hs₂)), h]
      exact Prod.ext (CharTwo.add_self_eq_zero _)
        (Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _))
    have h5 := hφs0 _ (mul_mem hs₁ hs₂) h3
    rw [eq_inv_of_mul_eq_one_right h5, inv_eq_of_mul_eq_one_right
      (by rw [← sq]; exact hT₀el.2 s₁ hs₁)]
  have hVgV : rightConjugate (gmsV L T) g ⊓ gmsV L T = gmsA L T :=
    (hS.rightConjugate_eq_or_inf_eq hR₂ hg).resolve_left hgV
  have hinf : ∀ z ∈ E, z.1 = 0 → z.2.1 = 0 → z = 0 := by
    intro z hz h1 h2
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    have hsR := hgR _ (hT₀R s hs)
    obtain ⟨s', hs', hs'φ⟩ := hC.T₀_surj _ (hC.mem _ hsR)
    have hmem := hφeq _ hsR _ (hT₀R s' hs') (by rw [hs'φ]; exact Prod.ext h1 (Prod.ext h2 rfl))
    have hV : g⁻¹ * s * g ∈ gmsV L T := by
      have e : g⁻¹ * s * g = g⁻¹ * s * g * s'⁻¹ * s' := by group
      rw [e]
      exact mul_mem (mem_sup_left hmem) (mem_sup_right hs')
    have hVg : g⁻¹ * s * g ∈ rightConjugate (gmsV L T) g := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using (mem_sup_right hs : s ∈ gmsV L T)
    have hA : g⁻¹ * s * g ∈ gmsA L T := by rw [← hVgV]; exact mem_inf.mpr ⟨hVg, hV⟩
    exact (hC.ker _ hsR).mpr hA
  have hsq : ∀ z ∈ E, VLike.sqMap a c e z = 0 := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    rw [← hC.sq _ (hgR _ (hT₀R s hs))]
    have e1 : (g⁻¹ * s * g) ^ 2 = 1 := by
      have e2 : (g⁻¹ * s * g) ^ 2 = g⁻¹ * s ^ 2 * g := by simp only [sq]; group
      rw [e2, hT₀el.2 s hs]
      group
    rw [e1, hv1]
  have hsurj : ∀ z ∈ E, z ≠ 0 → ∀ w, ∃ z' : BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1),
      z'.2.2 ∈ Λ ∧ VLike.commMap a c z z' = w := by
    intro z hz hz0 w
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    obtain ⟨b, hb, hbw⟩ := hC.v_surj w
    obtain ⟨r, hr, hrb⟩ := hS.exists_commutator_eq hR₂ hs (hs1 s hs hz0) (hgA _ (inv_mem hb))
    have hrR := hR₂.le_R hr
    refine ⟨φ (g⁻¹ * r * g), hC.mem _ (hgR _ hrR), ?_⟩
    rw [← hC.comm _ (hgR _ (hT₀R s hs)) _ (hgR _ hrR)]
    have e1 : g⁻¹ * s * g * (g⁻¹ * r * g) * (g⁻¹ * s * g)⁻¹ * (g⁻¹ * r * g)⁻¹ =
        g⁻¹ * (r * s * r⁻¹ * s⁻¹)⁻¹ * g := by group
    rw [e1, hrb, show g⁻¹ * (g * b⁻¹ * g⁻¹)⁻¹ * g = b by group, hbw]
  have hker : ∀ z ∈ E, ∀ z' ∈ E, z ≠ 0 → z' ≠ 0 → ∀ x : BinaryGaloisField (2 * a + 1) ×
      BinaryGaloisField (2 * a + 1) × BinaryGaloisField (2 * a + 1), x.2.2 ∈ Λ →
      VLike.commMap a c z x = 0 → VLike.commMap a c z' x = 0 := by
    intro z hz z' hz' hz0 _ x hx h0
    obtain ⟨s, hs, rfl⟩ := (hE z).mp hz
    obtain ⟨s', hs', rfl⟩ := (hE z').mp hz'
    obtain ⟨w, hw, rfl⟩ := hC.surj x hx
    rw [← hC.comm _ (hgR _ (hT₀R s hs)) _ hw] at h0
    rw [← hC.comm _ (hgR _ (hT₀R s' hs')) _ hw]
    have h1 := hC.v_inj _ (hcomm _ (hgR _ (hT₀R s hs)) _ hw) h0
    have hc1 : g * w * g⁻¹ * s = s * (g * w * g⁻¹) := by
      have h3 : g⁻¹ * s * g * w = w * (g⁻¹ * s * g) := by
        calc g⁻¹ * s * g * w =
            g⁻¹ * s * g * w * (g⁻¹ * s * g)⁻¹ * w⁻¹ * (w * (g⁻¹ * s * g)) := by group
          _ = w * (g⁻¹ * s * g) := by rw [h1, one_mul]
      calc g * w * g⁻¹ * s = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by group
        _ = g * (g⁻¹ * s * g * w) * g⁻¹ := by rw [h3]
        _ = s * (g * w * g⁻¹) := by group
    have hT := hS.mem_T_of_commute_T₀ hR₂ hs (hs1 s hs hz0) (hgR' _ hw) hc1
    have hc2 : g * w * g⁻¹ * s' = s' * (g * w * g⁻¹) :=
      mem_centralizer_iff.mp (hVC (mem_sup_right hs')) _ (by rw [hS.eq_gmsW] at hT; exact hT)
    have e1 : g⁻¹ * s' * g * w * (g⁻¹ * s' * g)⁻¹ * w⁻¹ = 1 := by
      calc g⁻¹ * s' * g * w * (g⁻¹ * s' * g)⁻¹ * w⁻¹ =
          g⁻¹ * (s' * (g * w * g⁻¹) * s'⁻¹ * (g * w * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * w * g⁻¹ * s' * s'⁻¹ * (g * w * g⁻¹)⁻¹) * g := by rw [← hc2]
        _ = 1 := by group
    rw [e1, hv1]
  have hH : VLike.Hyp a c e Λ E := ⟨hS.one_le, hK, by rw [hC.card]; exact h4,
    fun z hz => by obtain ⟨s, hs, rfl⟩ := (hE z).mp hz; exact hC.mem _ (hgR _ (hT₀R s hs)),
    htwo, hinf, hsq, hsurj, hker⟩
  obtain ⟨hc0, he0, hΛK, -⟩ := hH.eq_zero_of_hyp (by rw [hC.card]; exact hne)
  refine ⟨hc0, he0, ?_⟩
  exact AddSubgroup.eq_top_of_card_eq Λ (by rw [hΛK, Nat.card_eq_fintype_card])

end Sec3.SzR

end CFSG.ComponentClassification.GMS78
