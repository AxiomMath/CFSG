module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBSigned
public import CFSG.LocalAnalysis.SectionRank.QTK.Witness3

public section

namespace CFSG.SectionRank.QTK.CoverB

open Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G]

theorem localRank_le_two_of_not_dvd (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥Y)) :
    localRank r (↥Y ⧸ center ↥Y) ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨H, ⟨R, hR, hR2, rfl⟩, rfl⟩
  exact pRank_normalizer_le_two_of_not_dvd he hr hr2 hrZ hR hR2

theorem false_of_three_le_localRank (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {T : Type} [Group T] [Finite T] (e : ↥Y ⧸ center ↥Y ≃* T) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥Y)) (h : 3 ≤ localRank r T) : False := by
  have h1 := localRank_le_two_of_not_dvd he hr hr2 hrZ
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr] at h1
  omega

theorem not_dvd_card_center_of_signed_equiv (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {T : Type} [Group T] (e : ↥Y ⧸ center ↥Y ≃* T) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {R : Subgroup T} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) {a b d₁ d₂ : T}
    (ha : a ∈ normalizer (R : Set T)) (hb : b ∈ normalizer (R : Set T)) (har : a ^ r = 1)
    (hbr : b ^ r = 1) (hab : a * b = b * a)
    (hind : ∀ i j : ℕ, i < r → j < r → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)
    (hd₁a : d₁ * a * d₁⁻¹ = a⁻¹) (hd₁b : d₁ * b * d₁⁻¹ = b) (hd₂b : d₂ * b * d₂⁻¹ = b⁻¹) :
    ¬ r ∣ Nat.card (center ↥Y) := by
  have hmap : ∀ x : T, x ∈ normalizer (R : Set T) →
      e.symm x ∈ normalizer ((R.map e.symm.toMonoidHom : Subgroup _) : Set _) := fun x hx => by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.mem_map_of_mem _ hx
  refine not_dvd_card_center_of_signed he hr hr2 (R := R.map e.symm.toMonoidHom)
    (fun h => hR ((Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h))
    (hR2.map _) (hmap a ha) (hmap b hb) (by rw [← map_pow, har, map_one])
    (by rw [← map_pow, hbr, map_one]) (by rw [← map_mul, hab, map_mul])
    (fun i j hi hj h => hind i j hi hj (e.symm.injective (by rw [map_mul, map_pow, map_pow, h,
      map_one]))) (d₁ := e.symm d₁) (d₂ := e.symm d₂) ?_ ?_ ?_
  · rw [← map_mul, ← map_inv, ← map_mul, hd₁a, map_inv]
  · rw [← map_mul, ← map_inv, ← map_mul, hd₁b]
  · rw [← map_mul, ← map_inv, ← map_mul, hd₂b, map_inv]

theorem not_dvd_card_center_of_signed_inv (he : CFSG.Open.evenRank G ≤ 2) {Y : Subgroup G}
    {T : Type} [Group T] (e : ↥Y ⧸ center ↥Y ≃* T) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {t a b d₁ d₂ : T} (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (hta : Commute a t) (htb : Commute b t)
    (har : a ^ r = 1) (hbr : b ^ r = 1) (hab : a * b = b * a)
    (hind : ∀ i j : ℕ, i < r → j < r → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0)
    (hd₁a : d₁ * a * d₁⁻¹ = a⁻¹) (hd₁b : d₁ * b * d₁⁻¹ = b) (hd₂b : d₂ * b * d₂⁻¹ = b⁻¹) :
    ¬ r ∣ Nat.card (center ↥Y) :=
  not_dvd_card_center_of_signed_equiv he e hr hr2 (R := zpowers t)
    (fun h => ht1 (Subgroup.zpowers_eq_bot.mp h)) (isPGroup_zpowers_of_sq ht)
    (mem_normalizer_zpowers hta) (mem_normalizer_zpowers htb) har hbr hab hind hd₁a hd₁b hd₂b

end CFSG.SectionRank.QTK.CoverB
