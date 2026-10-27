module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.Open.MonsterDefs
import CFSG.Sporadic.ON
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Fi24.Simple
import CFSG.RankThree.PartOne.CTP.SporadicOrders
import CFSG.Monster.Existence.BabyOrder
import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Open.MonsterY443Defs
public import CFSG.Sporadic.Co1
public import CFSG.Sporadic.Fi23.Simple

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Blueprint CFSG.Sporadic
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem JStarElimDataOf.card_dvd_card_mul_outer {L₀ T : Type} [Group L₀] [Finite L₀] [Group T]
    {p B : ℕ} (h : JStarElimDataOf L₀ p B T) :
    Nat.card T ∣ Nat.card L₀ * Nat.card (Outer L₀) := by
  obtain ⟨-, J, -, -, -, φ, hφ, -⟩ := h
  have h1 : Nat.card T ∣ Nat.card (MulAut L₀) :=
    (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card J)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner L₀), mul_comm] at h1
  exact h1.trans (mul_dvd_mul_right (Subgroup.card_range_dvd _) _)

theorem JStarElimDataOf.pow_dvd_card_of_dvd {L₀ T : Type} [Group L₀] [Finite L₀] [Group T]
    {p B : ℕ} (hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L₀))
    (h : JStarElimDataOf L₀ p B T) {ℓ k : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hd : ℓ ^ k ∣ Nat.card T) : ℓ ^ k ∣ Nat.card L₀ :=
  (Nat.Coprime.pow_left k
    ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr (hOut ℓ hℓ hℓ2))).dvd_of_dvd_mul_right
    (hd.trans h.card_dvd_card_mul_outer)

@[expose] def sporListOrd : TauCeti.SporadicName → ℕ
  | .J3 => 50232960
  | .McL => 898128000
  | .Suz => 448345497600
  | .ONan => 460815505920
  | .Co1 => 4157776806543360000
  | .Co2 => 42305421312000
  | .Co3 => 495766656000
  | .Fi22 => 64561751654400
  | .Fi23 => 4089470473293004800
  | .Fi24Prime => 1255205709190661721292800
  | .HN => 273030912000000
  | .Ly => 51765179004000000
  | .Th => 90745943887872000
  | .B => 4154781481226426191177580544000000
  | .M => 808017424794512875886459904961710757005754368000000000
  | .M22 => 443520
  | _ => 0

theorem card_eq_sporListOrd
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    {L₀ : Type} [Group L₀] {p : ℕ} {s : TauCeti.SporadicName} (hs : P1ThreeSporList p s)
    (e : L₀ ≃* (TauCeti.CFSGIndex.sporadic s).Group) : Nat.card L₀ = sporListOrd s := by
  obtain ⟨f⟩ := hbr s
  have hc : ∀ {N : ℕ}, Nat.card (NativeSporadic.Carrier s) = N → Nat.card L₀ = N :=
    fun hN => (Nat.card_congr (e.trans f.symm).toEquiv).trans hN
  have hMc : Nat.card (NativeSporadic.Carrier .M) = Open.monsterOrder :=
    (Nat.card_congr Bridge.Y443.commutatorMulEquiv.toEquiv).trans hMcard
  rcases hs with ⟨-, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl⟩ | ⟨-, rfl | rfl | rfl | rfl | rfl⟩ | ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩
  · exact (hc J3.card_J3).trans (by decide)
  · exact (hc McL.card_McL).trans (by decide)
  · exact (hc Suz.card_Suz).trans (by decide)
  · exact (hc ON.card_ON).trans (by decide)
  · exact (hc Co1.card_Co1).trans (by decide)
  · exact (hc Co2.card_Co2).trans (by decide)
  · exact (hc Co3.card_Co3).trans (by decide)
  · exact (hc Fi22.card_Fi22).trans (by decide)
  · exact (hc Fi23.card_Fi23).trans (by decide)
  · exact (hc Fi24.card_Fi24prime).trans (by decide)
  · exact (hc HN.card_HN).trans (by decide)
  · exact (hc Ly.card_Ly).trans (by decide)
  · exact (hc RankThree.PartOne.CTP.card_Th).trans (by decide)
  · exact (hc Monster.Existence.card_nativeB).trans (by decide)
  · exact (hc hMc).trans (by decide)
  · exact (hc Mathieu.card_M22).trans (by decide)
  · exact (hc Co1.card_Co1).trans (by decide)
  · exact (hc Ly.card_Ly).trans (by decide)
  · exact (hc HN.card_HN).trans (by decide)
  · exact (hc Monster.Existence.card_nativeB).trans (by decide)
  · exact (hc hMc).trans (by decide)
  · exact (hc Fi24.card_Fi24prime).trans (by decide)
  · exact (hc hMc).trans (by decide)
  · exact (hc hMc).trans (by decide)

theorem card_catGroup_unitary {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) :
    Nat.card (CatGroup d) = ordTwistedA 2 (p ^ d.1.fieldExponent) := by
  obtain ⟨q, rfl, hdq⟩ := hd
  have hfe : d.1.fieldExponent = q.exponent := by rw [hdq]; simp
  rw [hfe]
  exact card_catGroup_twistedA hdq

theorem unitary_spor_arith {p n : ℕ} {s : TauCeti.SporadicName} (hs : P1ThreeSporList p s)
    (hn : 2 ≤ n) (hpow : p ^ (3 * n) ∣ sporListOrd s)
    (hdvd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ℓ ∣ ordTwistedA 2 (p ^ n) → ℓ ∣ sporListOrd s) :
    False := by
  rcases hs with ⟨rfl, hs3⟩ | ⟨rfl, hs5⟩ | ⟨rfl, hs7⟩ | ⟨rfl, rfl⟩
  · have hn6 : n ≤ 6 := by
      by_contra h
      have h21 : 3 ^ 21 ∣ sporListOrd s := (pow_dvd_pow 3 (by omega)).trans hpow
      rcases hs3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;> exact absurd h21 (by decide)
    rcases hs3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> interval_cases n <;>
      first
      | exact absurd hpow (by decide)
      | exact absurd (hdvd 73 (by norm_num) (by norm_num) (by decide)) (by decide)
      | exact absurd (hdvd 37 (by norm_num) (by norm_num) (by decide)) (by decide)
      | exact absurd (hdvd 6481 (by norm_num) (by norm_num) (by decide)) (by decide)
      | exact absurd (hdvd 61 (by norm_num) (by norm_num) (by decide)) (by decide)
  · have hn3 : n ≤ 3 := by
      by_contra h
      have h12 : 5 ^ 12 ∣ sporListOrd s := (pow_dvd_pow 5 (by omega)).trans hpow
      rcases hs5 with rfl | rfl | rfl | rfl | rfl <;> exact absurd h12 (by decide)
    rcases hs5 with rfl | rfl | rfl | rfl | rfl <;> interval_cases n <;>
      first
      | exact absurd hpow (by decide)
      | exact absurd (hdvd 601 (by norm_num) (by norm_num) (by decide)) (by decide)
      | exact absurd (hdvd 5167 (by norm_num) (by norm_num) (by decide)) (by decide)
  · rcases hs7 with rfl | rfl
    · exact absurd ((pow_dvd_pow 7 (by omega : 6 ≤ 3 * n)).trans hpow) (by decide)
    · have hn2 : n ≤ 2 := by
        by_contra h
        have h9 : 7 ^ 9 ∣ sporListOrd .M := (pow_dvd_pow 7 (by omega)).trans hpow
        exact absurd h9 (by decide)
      obtain rfl : n = 2 := le_antisymm hn2 hn
      exact absurd (hdvd 181 (by norm_num) (by norm_num) (by decide)) (by decide)
  · exact absurd ((pow_dvd_pow 13 (by omega : 6 ≤ 3 * n)).trans hpow) (by decide)

theorem ree_spor_arith {n : ℕ} {s : TauCeti.SporadicName} (hs : P1ThreeSporList 3 s)
    (hn : 3 ≤ n) (hodd : n % 2 = 1) (hpow : 3 ^ (3 * n) ∣ sporListOrd s)
    (hdvd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
      ℓ ∣ (3 ^ n) ^ 3 * ((3 ^ n) ^ 3 + 1) * (3 ^ n - 1) → ℓ ∣ sporListOrd s) : False := by
  rcases hs with ⟨-, hs3⟩ | ⟨h5, -⟩ | ⟨h7, -⟩ | ⟨h13, -⟩
  · have hn6 : n ≤ 6 := by
      by_contra h
      have h21 : 3 ^ 21 ∣ sporListOrd s := (pow_dvd_pow 3 (by omega)).trans hpow
      rcases hs3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl <;> exact absurd h21 (by decide)
    rcases hs3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> interval_cases n <;>
      first
      | omega
      | exact absurd hpow (by decide)
      | exact absurd (hdvd 37 (by norm_num) (by norm_num) (by decide)) (by decide)
      | exact absurd (hdvd 61 (by norm_num) (by norm_num) (by decide)) (by decide)
  · omega
  · omega
  · omega

theorem kFactJStarElimUnitarySpor_of
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    : KFactJStarElimUnitarySpor := by
  rintro p _ d₀ hp2 hd₀ hn L _ _ s hs ⟨e⟩ hdata
  have hp : p.Prime := Fact.out
  have hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L) := fun q hq hq2 => by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hOutS s q hq hq2
  have hN := card_eq_sporListOrd hbr hMcard hs e
  have hT := card_catGroup_unitary hd₀
  refine unitary_spor_arith hs hn ?_ ?_
  · rw [← hN]
    exact hdata.pow_dvd_card_of_dvd hOut hp hp2 (pow_dvd_card_catGroup_unitary hd₀)
  · intro ℓ hℓ hℓ2 hd
    rw [← hN]
    have := hdata.pow_dvd_card_of_dvd (k := 1) hOut hℓ hℓ2 (by rwa [pow_one, hT])
    rwa [pow_one] at this

theorem kFactJStarElimReeSpor_of (hRee : KFactReeOrder)
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (Outer (TauCeti.CFSGIndex.sporadic s).Group))
    (hMcard : Nat.card Open.MonsterY443Derived = Open.monsterOrder)
    : KFactJStarElimReeSpor := by
  rintro d₀ hd₀ L _ _ s hs ⟨e⟩ hdata
  have hfin : Finite (CatGroup d₀) := by
    obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := hdata
    exact Finite.of_surjective φ hφ
  have hOut : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card (Outer L) := fun q hq hq2 => by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact hOutS s q hq hq2
  have hN := card_eq_sporListOrd hbr hMcard hs e
  have hT := hRee (CatGroup d₀) d₀ hd₀ ⟨MulEquiv.refl _⟩
  have hn3 := hd₀.three_le_fieldExponent
  have hodd : d₀.1.fieldExponent % 2 = 1 := Nat.odd_iff.mp hd₀.odd_fieldExponent
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ree_spor_arith hs hn3 hodd ?_ ?_
  · rw [← hN]
    refine hdata.pow_dvd_card_of_dvd hOut Nat.prime_three (by norm_num) ?_
    rw [hT]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _
    rw [← pow_mul]
    exact pow_dvd_pow 3 (by omega)
  · intro ℓ hℓ hℓ2 hd
    rw [← hN]
    have := hdata.pow_dvd_card_of_dvd (k := 1) hOut hℓ hℓ2 (by rwa [pow_one, hT])
    rwa [pow_one] at this

end CFSG.AGLEmbedding
