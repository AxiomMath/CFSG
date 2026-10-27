module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltSetup
public import CFSG.GH74.Generic.BProg.B3.S3SL2Perm

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.Blueprint Subgroup Equiv Equiv.Perm

namespace S3SL2AltOrd

variable {Y : Type} [Group Y] {H : Subgroup Y} {n : ℕ} {s : Y} {hsN : s ∈ normalizer (H : Set Y)}

theorem card_image_dvd (S : AltSetting H n hsN) [Finite Y] {Lb : Subgroup Y} (hLbH : Lb ≤ H)
    (hZ : Nat.card (center ↥H) = 2) :
    ∃ m : ℕ, m ∣ 2 ∧ Nat.card Lb = m * Nat.card ((Lb.subgroupOf H).map S.π) := by
  classical
  let P : Subgroup ↥H := Lb.subgroupOf H
  let φ : ↥P →* alternatingGroup (Fin n) := S.π.comp P.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hrange : φ.range = P.map S.π := by
    ext a
    simp only [φ, MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_map]
    constructor
    · rintro ⟨p, rfl⟩; exact ⟨p, p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
  have hker : Nat.card φ.ker ∣ 2 := by
    have hle : (φ.ker.map P.subtype) ≤ center ↥H := by
      rintro _ ⟨p, hp, rfl⟩
      rw [← S.ker_eq]
      exact hp
    have : Nat.card (φ.ker.map P.subtype) ∣ Nat.card (center ↥H) := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective P.subtype_injective] at this
    rwa [hZ] at this
  have hP : Nat.card P = Nat.card Lb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLbH).toEquiv
  refine ⟨Nat.card φ.ker, hker, ?_⟩
  rw [← hP, ← h1, hrange]

theorem card_image_dvd_centralizer (S : AltSetting H n hsN) {Lb : Subgroup Y}
    {σ₁ : Perm (Fin n)}
    (hc : ∀ l : ↥H, (l : Y) ∈ Lb →
      σ₁ * (S.π l : Perm (Fin n)) = (S.π l : Perm (Fin n)) * σ₁) :
    Nat.card ((Lb.subgroupOf H).map S.π) ∣ Nat.card (centralizer ({σ₁} : Set (Perm (Fin n)))) := by
  classical
  set R : Subgroup (alternatingGroup (Fin n)) := (Lb.subgroupOf H).map S.π with hR
  have hRle : R.map (alternatingGroup (Fin n)).subtype ≤ centralizer ({σ₁} : Set (Perm (Fin n))) := by
    rintro _ ⟨a, ⟨l, hl, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hc l hl
  have := Subgroup.card_dvd_of_le hRle
  rwa [Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective] at this

theorem constraint_of_commuting (S : AltSetting H n hsN) [Finite Y] {Lb : Subgroup Y} (hLbH : Lb ≤ H)
    (hZ : Nat.card (center ↥H) = 2) {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q)
    (hcard : Nat.card Lb = q * (q ^ 2 - 1)) {σ₁ : Perm (Fin n)} (hσ₁ : σ₁ * σ₁ = 1) (hσ₁1 : σ₁ ≠ 1)
    (hc : ∀ l : ↥H, (l : Y) ∈ Lb →
      σ₁ * (S.π l : Perm (Fin n)) = (S.π l : Perm (Fin n)) * σ₁) :
    5 ≤ n - 2 * σ₁.cycleType.card ∨ 5 ≤ σ₁.cycleType.card := by
  classical
  obtain ⟨r, hr, hr5, hrdvd⟩ := S3SL2Perm.prime_ge_five_dvd hq hq5
  obtain ⟨m, hm2, hmcard⟩ := card_image_dvd S hLbH hZ
  have hrm : ¬ r ∣ m := by
    intro h
    have := Nat.le_of_dvd (by norm_num) (h.trans hm2)
    omega
  have hrL : r ∣ Nat.card Lb := hcard ▸ hrdvd
  have hrR : r ∣ Nat.card ((Lb.subgroupOf H).map S.π) := by
    rw [hmcard] at hrL
    exact ((Nat.Prime.dvd_mul hr).1 hrL).resolve_left hrm
  have hdvd := card_image_dvd_centralizer S hc
  rw [S3SL2Perm.card_centralizer_involution hσ₁ hσ₁1] at hdvd
  have := S3SL2Perm.prime_dvd_cases hr hr5 (hrR.trans hdvd)
  omega

end S3SL2AltOrd

end CFSG.GH74.Generic.BProg.B3
