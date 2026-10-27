module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupCenterTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open Subgroup CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding.MaxD2 CFSG.RankThree.Native
open scoped commutatorElement

private theorem zin_eq_inf_centralizer_mcl {K : Type} [Group K] (S : Subgroup K) :
    Zin S = S ⊓ centralizer (S : Set K) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hy, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    have := Subgroup.mem_center_iff.mp hyc ⟨h, hh⟩
    exact congrArg Subtype.val this
  · intro hx
    obtain ⟨hxS, hxc⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)

private theorem commutator_mul_mem_inf_centralizer_mcl {Q : Type*} [Group Q] {R : Subgroup Q}
    {a b w₁ w₂ : Q} (ha : a ∈ R) (hb : b ∈ R) (hw₁ : w₁ ∈ R ⊓ centralizer (R : Set Q))
    (hw₂ : w₂ ∈ R ⊓ centralizer (R : Set Q)) : ⁅a * w₁, b * w₂⁆ = ⁅a, b⁆ := by
  have hcen : ∀ w (hw : w ∈ R ⊓ centralizer (R : Set Q)),
      (⟨w, (Subgroup.mem_inf.1 hw).1⟩ : R) ∈ Subgroup.center R := by
    intro w hw
    refine Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hw).2 g g.2
  have h1 := commutator_mul_mem_center (⟨a, ha⟩ : R) ⟨b, hb⟩ (hcen w₁ hw₁) (hcen w₂ hw₂)
  have h2 := map_commutatorElement R.subtype ((⟨a, ha⟩ : R) * ⟨w₁, (Subgroup.mem_inf.1 hw₁).1⟩)
    ((⟨b, hb⟩ : R) * ⟨w₂, (Subgroup.mem_inf.1 hw₂).1⟩)
  rw [h1] at h2
  simpa using h2.symm

private theorem intCast_eq_of_zpow_eq_mcl {G : Type*} [Group G] {p : ℕ} {z : G}
    (hz : orderOf z = p) {i j : ℤ} (h : z ^ i = z ^ j) : (i : ZMod p) = (j : ZMod p) := by
  rw [zpow_eq_zpow_iff_modEq, hz] at h
  exact (ZMod.intCast_eq_intCast_iff i j p).2 h

theorem centerTransAt_of_heisData_two {Q : Type} [Group Q] {p lam e : ℕ} [Fact p.Prime]
    {G R : Subgroup Q} (h : HeisData p 2 lam e G R)
    (hgen : ∀ d : ZMod p, d ^ 2 = (lam : ZMod p) ^ 2 →
      ∀ t : ZMod p, t ≠ 0 → ∃ m : ℕ, d ^ m = t) :
    CenterTransAt (R.subgroupOf G) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hRG, -, -, -, hZ, hcomm, -, -, t, htN, hpow, -, -⟩ := h
  have hnab : ∃ x ∈ R, ∃ y ∈ R, ⁅x, y⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : ⁅R, R⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha b hb
      exact commutatorElement_eq_one_iff_mul_comm.1 (hall b hb a ha)
    rw [h1] at hcomm
    have : Nat.card (R ⊓ centralizer (R : Set Q) : Subgroup Q) = 1 := by
      rw [← hcomm]; simp
    rw [hZ] at this
    exact hp.one_lt.ne' this
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  set c : Q := ⁅x, y⁆ with hc
  have hcZ : c ∈ R ⊓ centralizer (R : Set Q) := hcomm ▸ Subgroup.commutator_mem_commutator hx hy
  have hord : orderOf c = p := by
    have hdvd : orderOf c ∣ p := by
      have := Subgroup.orderOf_dvd_natCard _ hcZ
      rwa [hZ] at this
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hxy
    · exact h1
  haveI : Finite (R ⊓ centralizer (R : Set Q) : Subgroup Q) :=
    Nat.finite_of_card_ne_zero (by rw [hZ]; exact hp.ne_zero)
  have hZz : R ⊓ centralizer (R : Set Q) = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hcZ) ?_).symm
    rw [hZ, Nat.card_zpowers, hord]
  have hcR : c ∈ R := (Subgroup.mem_inf.1 hcZ).1
  have hcG : c ∈ G := hRG hcR
  have hzx : Commute c x := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcZ).2 x hx).symm
  have hzy : Commute c y := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcZ).2 y hy).symm
  have htR : ∀ r ∈ R, t * r * t⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.1 htN.1 r).1 hr
  have hconjc : t * c * t⁻¹ = ⁅t * x * t⁻¹, t * y * t⁻¹⁆ := conjugate_commutatorElement x y t
  have htc : t * c * t⁻¹ ∈ R ⊓ centralizer (R : Set Q) := by
    rw [hconjc, ← hcomm]
    exact Subgroup.commutator_mem_commutator (htR x hx) (htR y hy)
  obtain ⟨δ, hδ⟩ := Subgroup.mem_zpowers_iff.1 (hZz ▸ htc)
  have h2 : t ^ 2 * c * (t ^ 2)⁻¹ = c ^ (δ * δ) := by
    calc t ^ 2 * c * (t ^ 2)⁻¹ = t * (t * c * t⁻¹) * t⁻¹ := by rw [pow_two]; group
      _ = t * c ^ δ * t⁻¹ := by rw [← hδ]
      _ = (t * c * t⁻¹) ^ δ := by rw [conj_zpow]
      _ = (c ^ δ) ^ δ := by rw [← hδ]
      _ = c ^ (δ * δ) := by rw [← zpow_mul]
  obtain ⟨z₁, hz₁, hx'⟩ := hpow x hx
  obtain ⟨z₂, hz₂, hy'⟩ := hpow y hy
  have h3 : t ^ 2 * c * (t ^ 2)⁻¹ = c ^ ((lam : ℤ) * lam) := by
    calc t ^ 2 * c * (t ^ 2)⁻¹ = ⁅t ^ 2 * x * (t ^ 2)⁻¹, t ^ 2 * y * (t ^ 2)⁻¹⁆ :=
          conjugate_commutatorElement x y (t ^ 2)
      _ = ⁅x ^ lam * z₁, y ^ lam * z₂⁆ := by rw [hx', hy']
      _ = ⁅x ^ lam, y ^ lam⁆ :=
          commutator_mul_mem_inf_centralizer_mcl (R.pow_mem hx lam) (R.pow_mem hy lam) hz₁ hz₂
      _ = c ^ ((lam : ℤ) * lam) := by
          have := commutator_zpow_mul_zpow x y hzx hzy (lam : ℤ) 0 0 (lam : ℤ)
          simpa using this
  have h4 : ((δ * δ : ℤ) : ZMod p) = (((lam : ℤ) * lam : ℤ) : ZMod p) :=
    intCast_eq_of_zpow_eq_mcl hord (h2.symm.trans h3)
  have hδ2 : (δ : ZMod p) ^ 2 = (lam : ZMod p) ^ 2 := by
    push_cast at h4
    rw [sq, sq]
    exact h4
  have hZin : Zin (R.subgroupOf G) = Subgroup.zpowers (⟨c, hcG⟩ : G) := by
    ext g
    rw [zin_eq_inf_centralizer_mcl, subgroupOf_centralizer_eq hRG, Subgroup.mem_inf,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← Subgroup.mem_inf, hZz,
      Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp⟩
  have hnorm : (⟨t, htN.2⟩ : G) ∈ normalizer ((R.subgroupOf G : Subgroup G) : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hRG]
    exact Subgroup.mem_subgroupOf.2 htN.1
  refine centerTransAt_of_generator (R.subgroupOf G) (z := (⟨c, hcG⟩ : G))
    (n := (⟨t, htN.2⟩ : G)) (δ := δ) hZin ?_ hnorm ?_ (hgen _ hδ2)
  · rw [Subgroup.orderOf_mk]
    exact hord
  · apply Subtype.ext
    simpa using hδ.symm

private theorem zmod5_gen : ∀ d : ZMod 5, d ^ 2 = ((3 : ℕ) : ZMod 5) ^ 2 →
    ∀ t : ZMod 5, t ≠ 0 → ∃ m : ℕ, d ^ m = t := by
  have h : ∀ d : ZMod 5, d ^ 2 = ((3 : ℕ) : ZMod 5) ^ 2 →
      ∀ t : ZMod 5, t ≠ 0 → ∃ m : Fin 4, d ^ (m : ℕ) = t := by
    decide +kernel
  intro d hd t ht
  obtain ⟨m, hm⟩ := h d hd t ht
  exact ⟨m, hm⟩


theorem mcl_transCenter :
    ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerTransitiveCenter 5 K := by
  intro K _ _ hK
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let θ : K ≃* mcl275P := (e.trans eC.symm).trans mcl275Equiv
  obtain ⟨R₀, hR₀⟩ := mcl_heisData_P
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hC : CenterTransAt (R₀.subgroupOf mcl275P) := centerTransAt_of_heisData_two hR₀ zmod5_gen
  have hcard : Nat.card (R₀.subgroupOf mcl275P) = 5 ^ (Nat.card mcl275P).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀.1).toEquiv, hR₀.2.1,
      factorization_card_mcl275P_five]
  exact normalizerTransitiveCenter_of_equiv Nat.prime_five θ (Sylow.ofCard _ hcard) hC

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
