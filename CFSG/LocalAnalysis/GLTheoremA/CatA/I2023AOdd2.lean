module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ACtx

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem cube_mem_of_comm {Y : Type*} [Group Y] (Nn : Subgroup Y) [Nn.Normal] {a w : Y}
    (hc : a * w * a⁻¹ * w⁻¹ ∈ Nn) (h1 : (a * w) ^ 3 ∈ Nn) (h2 : a ^ 3 ∈ Nn) : w ^ 3 ∈ Nn := by
  have hcomm : (QuotientGroup.mk a : Y ⧸ Nn) * QuotientGroup.mk w =
      QuotientGroup.mk w * QuotientGroup.mk a := by
    have h : (QuotientGroup.mk (a * w * a⁻¹ * w⁻¹) : Y ⧸ Nn) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h)
  have e1 : (QuotientGroup.mk a : Y ⧸ Nn) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h2
  have e2 : ((QuotientGroup.mk a : Y ⧸ Nn) * QuotientGroup.mk w) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h1
  rw [(show Commute (QuotientGroup.mk a : Y ⧸ Nn) (QuotientGroup.mk w) from hcomm).mul_pow, e1,
    one_mul] at e2
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
  exact e2

theorem le_normalizer_of_commute {M : Type*} [Group M] {A K : Subgroup M}
    (h : ∀ a ∈ A, ∀ k ∈ K, a * k = k * a) : A ≤ Subgroup.normalizer (K : Set M) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have e : ∀ k ∈ K, a * k * a⁻¹ = k := fun k hk => by rw [h a ha k hk]; group
  constructor
  · intro hk
    rw [e k hk]
    exact hk
  · intro hk
    have h1 : a * (a * k * a⁻¹) = (a * k * a⁻¹) * a := h a ha _ hk
    have h2 : a * k * a⁻¹ = k := by
      have : a * (a * k * a⁻¹) = a * k := by rw [h1]; group
      exact mul_left_cancel this
    rw [h2] at hk
    exact hk

namespace Ctx

variable {B : Subgroup G} {x : G} {L : Subgroup G}

theorem lemmaW (hc : Ctx B x L) {w : G} (hwX : w ∈ cx x) (hwk : w ∈ centModSubgroup 3 L)
    (hw3 : w ^ 3 ∈ GLAPPrimeCoreOf 3 (cx x)) :
    ∃ (i : ℤ) (n : G), n ∈ GLAPPrimeCoreOf 3 (cx x) ∧ w = x ^ i * n := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set N : Subgroup G := GLAPPrimeCoreOf 3 (cx x) with hN
  have hm : Nat.Coprime (Nat.card N) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 (cx x))).symm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (Nat.card N : ℤ) * a + 3 * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab (Nat.card N) 3
    rw [Nat.Coprime.gcd_eq_one hm] at h
    exact ⟨Nat.gcdA _ _, Nat.gcdB _ _, by exact_mod_cast h.symm⟩
  set k : ℤ := (Nat.card N : ℤ) * a with hk
  have hk1 : k = 1 - 3 * b := by rw [hk]; linarith
  set w' : G := w ^ k with hw'
  have hw'X : w' ∈ cx x := Subgroup.zpow_mem _ hwX k
  have hw'k : w' ∈ centModSubgroup 3 L := Subgroup.zpow_mem _ hwk k
  have hw'3 : w' ^ 3 = 1 := by
    have h1 : (w ^ 3) ^ Nat.card N = 1 := by
      have h := pow_card_eq_one' (G := ↥N) (x := (⟨w ^ 3, hw3⟩ : ↥N))
      have h' := congrArg Subtype.val h
      rw [Subgroup.coe_pow] at h'
      exact h'
    have e : w' ^ 3 = (w ^ 3) ^ k := by
      rw [hw', ← zpow_natCast (w ^ k) 3, ← zpow_mul, ← zpow_natCast w 3, ← zpow_mul, mul_comm]
    rw [e, hk, zpow_mul, zpow_natCast, h1, one_zpow]
  have hx3 := hc.hx3
  have hcomm : w' * x = x * w' := Subgroup.mem_centralizer_singleton_iff.1 hw'X
  have hw'x : w' ∈ Subgroup.zpowers x := by
    by_contra hnot
    obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp3 hcomm hw'3 hx3 hc.hx1 hnot
    have hxL : x ∈ centModSubgroup 3 L := hc.hxker
    have hle : Subgroup.zpowers w' ⊔ Subgroup.zpowers x ≤ centModSubgroup 3 L :=
      sup_le (Subgroup.zpowers_le.2 hw'k) (Subgroup.zpowers_le.2 hxL)
    have hcyc : IsCyclic (Subgroup.zpowers w' ⊔ Subgroup.zpowers x : Subgroup G) :=
      hc.hCyc _ (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
    have hdiv := card_le_of_isCyclic_of_pow hp3 hcyc (fun d hd => hE.2 d hd)
    rw [hcard] at hdiv
    omega
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hw'x
  refine ⟨i, (w ^ 3) ^ b, Subgroup.zpow_mem _ hw3 b, ?_⟩
  have e : w ^ k * (w ^ 3) ^ b = w := by
    rw [← zpow_natCast w 3, ← zpow_mul, ← zpow_add]
    have : k + ((3 : ℕ) : ℤ) * b = 1 := by rw [hk1]; push_cast; ring
    rw [this, zpow_one]
  rw [hi, hw']
  exact e.symm

theorem coset_dec (hc : Ctx B x L) (F : TD4Rank (PQuot 3 L)) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hnon : ¬ InducesInnerMod 3 L b₀) :
    ∀ (b : G) (hb : b ∈ B), ∃ (l : ↥L) (j : ℤ), rho L ⟨b, hc.hBL hb⟩ =
      rho L ⟨(l : G), Subgroup.le_normalizer l.2⟩ * (rho L ⟨b₀, hc.hBL hb₀⟩) ^ j := by
  intro b hb
  set R : Subgroup (MulAut (PQuot 3 L)) := (rhoSub L B hc.hBL).range with hR
  set Fi : Subgroup (MulAut (PQuot 3 L)) := R ⊓ innerAutS (PQuot 3 L) with hFi
  obtain ⟨hR27, -, hF9⟩ := hc.rank_eq F
  set u : MulAut (PQuot 3 L) := rho L ⟨b₀, hc.hBL hb₀⟩ with hu
  have huR : u ∈ R := ⟨⟨b₀, hb₀⟩, rfl⟩
  have huF : u ∉ innerAutS (PQuot 3 L) := fun h =>
    hnon ((inducesInnerMod_iff_barAut_mem_inner (hc.hBL hb₀)).2 h)
  have hRcomm : ∀ a ∈ R, ∀ c ∈ R, a * c = c * a := fun a ha c hc' =>
    isElemAbelian_commute (isElemAbelian_range hc.hBel (rhoSub L B hc.hBL)) ha hc'
  have hFcomm : ∀ f ∈ Fi, ∀ z ∈ Subgroup.zpowers u, f * z = z * f := by
    intro f hf z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((Commute.zpow_right (show Commute f u from hRcomm f hf.1 u huR) j).eq)
  have hFnorm : Fi ≤ Subgroup.normalizer ((Subgroup.zpowers u : Subgroup _) : Set _) :=
    le_normalizer_of_commute hFcomm
  set H : Subgroup (MulAut (PQuot 3 L)) := Fi ⊔ Subgroup.zpowers u with hH
  have hHR : H ≤ R := sup_le inf_le_left (Subgroup.zpowers_le.2 huR)
  have h1 : 9 ∣ Nat.card H := hF9 ▸ Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card H ∣ 27 := hR27 ▸ Subgroup.card_dvd_of_le hHR
  have h3 : Nat.card H ≠ 9 := by
    intro h9
    have hFH : Fi = H := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h9, hF9])
    have hu' : u ∈ Fi := hFH ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
    exact huF hu'.2
  have h27 : Nat.card H = 27 := by
    have hle : Nat.card H ≤ 27 := Nat.le_of_dvd (by norm_num) h2
    obtain ⟨k, hk⟩ := h1
    have hpos : 0 < Nat.card H := Nat.card_pos
    have : Nat.card H = 9 ∨ Nat.card H = 18 ∨ Nat.card H = 27 := by omega
    rcases this with h | h | h
    · exact absurd h h3
    · rw [h] at h2
      norm_num at h2
    · exact h
  have hHE : H = R := Subgroup.eq_of_le_of_card_ge hHR (by rw [h27, hR27])
  have he : rhoSub L B hc.hBL ⟨b, hb⟩ ∈ (H : Set (MulAut (PQuot 3 L))) := by
    rw [hHE]
    exact ⟨⟨b, hb⟩, rfl⟩
  rw [hH, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hFnorm] at he
  obtain ⟨f, hf, z, hz, hfz⟩ := Set.mem_mul.1 he
  obtain ⟨c, hcf⟩ := hf.2
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine ⟨l, j, ?_⟩
  rw [rho_inner]
  have := hfz
  rw [← hcf, ← hj] at this
  exact this.symm

end Ctx

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
