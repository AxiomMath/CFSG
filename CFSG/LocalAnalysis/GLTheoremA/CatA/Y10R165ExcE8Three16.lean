module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE8Three17
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Rk2Six
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Three
public import CFSG.RankThree.PartOne.KE6.E8T3Frame

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE6 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
  CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
open scoped Matrix MatrixGroups

section Certs


private theorem concl165_e8Model (F : Type) [Field F] [Finite F] [CharP F 2]
    (n p q : ℕ) (hcard : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + ε * (Nat.card F : ℤ) + 1)
    (hq2ε : ε = -1 → 2 < 2 ^ n) (hp3 : 3 < p)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hqdiv : q ∣ 2 ^ n - 1 ∨ n = 1 ∧ q = 3)
    (Ã : Subgroup (adjointGroup Tag.E8 F)) (hAe : IsElemAbelian p Ã)
    (hΩ : ∀ g ∈ Subgroup.centralizer (Ã : Set (adjointGroup Tag.E8 F)),
      orderOf g = p → g ∈ Ã) :
    Concl165 (adjointGroup Tag.E8 F) p q Ã := by
  classical
  let L := AlgebraicClosure F
  haveI : CharP L 2 :=
    charP_of_injective_algebraMap (algebraMap F L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpL : (p : L) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff L 2]
    exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  obtain ⟨ζ, hζord⟩ := CFSG.exists_unit_orderOf_eq_of_isAlgClosed (k := L) (n := p) hpL
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.iff_orderOf.2 hζord
  have hE6 : E6Layer Tag.E8 := e6Layer_E8
  set n₀ : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L (e8T3We ε) with hn₀
  have hnm : n₀ ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L _
  have hnW : weylQuotientHom Tag.E8 L ⟨n₀, hnm⟩ = e8T3We ε :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep (R := L) _)
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ :=
    e8T3_frame (ε := ε) hε F hn hcard hp hp3 hpf L n₀ hnm hnW
  have hJQ : ∀ (x z c : adjointGroup Tag.E8 F), Commute x z → orderOf x = p →
      adjEmb Tag.E8 F L (c * x * c⁻¹) = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card F : ZMod p) i).val) *
        g0⁻¹ →
      adjEmb Tag.E8 F L (c * z * c⁻¹) = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card F : ZMod p) i).val) *
        g0⁻¹ →
      ∃ J Q : Subgroup (adjointGroup Tag.E8 F),
        J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 F)) ∧
        (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 F)))).Normal ∧
        CFSG.IsQuasisimple J ∧ p ∣ Nat.card J ∧
        Q ≤ J ∧ Q ≤ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E8 F)) ∧
        (Q.subgroupOf (J ⊓ Subgroup.centralizer ({z} : Set (adjointGroup Tag.E8 F)))).Normal ∧
        CFSG.IsQuasisimple Q ∧ p ∣ Nat.card Q := by
    intro x z c hxz hx hxframe hzframe
    exact exists_e8T3_JQ_layers (hE6 := hE6) (hε := hε) (hf := hn) (hK := hcard)
      (hp := hp) (hp3 := hp3) (hpf := hpf) (hq2 := hq2ε) (n := n₀) (hnm := hnm)
      (hnW := hnW) (g0 := g0) (hg0C := hg0C) (hg0 := hg0) (hperf := hperf)
      (hζ := hζ) (c := c) (hxz := hxz) (hx := hx) (hxframe := hxframe) (hzframe := hzframe)
  have hF : ∀ (x z c x₀ z₀ : adjointGroup Tag.E8 F) (J : Subgroup (adjointGroup Tag.E8 F)),
      x ∈ Ã → z ∈ Ã → orderOf x = p → orderOf z = p → z ∉ Subgroup.zpowers x →
      c * x * c⁻¹ = x₀ → c * z * c⁻¹ = z₀ →
      adjEmb Tag.E8 F L x₀ = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card F : ZMod p) i).val) *
        g0⁻¹ →
      adjEmb Tag.E8 F L z₀ = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3ZColumn ε (Nat.card F : ZMod p) i).val) *
        g0⁻¹ →
      J ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 F)) →
      (J.subgroupOf (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 F)))).Normal →
      CFSG.IsQuasisimple J → p ∣ Nat.card J →
      ∃ G : Subgroup (adjointGroup Tag.E8 F),
        G ≤ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E8 F)) ∧
        G ≤ Subgroup.normalizer (J : Set (adjointGroup Tag.E8 F)) ∧
        IsElemAbelian q G ∧ 3 ≤ CFSG.Open.pRank q G := by
    intro x z c x₀ z₀ J hx hz hxord hzord hzx hcx hcz hxfr hzfr hJx hJn hJq hpJ
    have hxfr' : adjEmb Tag.E8 F L (c * x * c⁻¹) = g0 *
        rootDiagUnit Tag.E8 (fun i => ζ ^ (e8T3XColumn ε (Nat.card F : ZMod p) i).val) *
        g0⁻¹ := by rw [hcx]; exact hxfr
    by_cases hqK : q ∣ Nat.card F - 1
    · exact exists_rank_three_qTorus_centralizer_normalizer (hE6 := hE6) (hε := hε)
        (K := F) (hf := hn) (hK := hcard) (hp := hp) (hp3 := hp3) (hpf := hpf)
        (n := n₀) (hnm := hnm) (hnW := hnW) (g0 := g0) (hg0C := hg0C) (hg0 := hg0)
        (hperf := hperf) (hζ := hζ) (hx := hxord) (c := c) (hxframe := hxfr')
        (hJx := hJx) (hJn := hJn) (hq := hq) (hq2 := hq2) (hqp := hqp) (hqK := hqK)
    · have hn1q3 : n = 1 ∧ q = 3 := by
        rcases hqdiv with hd | h
        · rw [hcard] at hqK
          exact absurd hd hqK
        · exact h
      have hK2 : Nat.card F = 2 := by rw [hcard, hn1q3.1]; norm_num
      exact exists_rank_three_qTorus_centralizer_normalizer_of_charTwo (hE6 := hE6)
        (hε := hε) (K := F) (ℓ := 2) (f := n) (L := L) (hf := hn) (hK := hcard)
        (hℓ := rfl) (hf1 := hn1q3.1) (hp := hp) (hp3 := hp3) (hpf := hpf)
        (n := n₀) (hnm := hnm) (hnW := hnW) (g0 := g0) (hg0C := hg0C) (hg0 := hg0)
        (hperf := hperf) (hζ := hζ) (hx := hxord) (c := c) (hxframe := hxfr')
        (hJx := hJx) (hJn := hJn) (hq := hq) (hq2 := hq2) (hqp := hqp) (hq3 := hn1q3.2)
  exact concl165_of_e8T3_model (hE6 := hE6) (hε := hε) (hf := hn) (hK := hcard)
    (hp := hp) (hp3 := hp3) (hpf := hpf) (hq2 := hq2ε) (n := n₀) (hnm := hnm)
    (hnW := hnW) (g0 := g0) (hg0C := hg0C) (hg0 := hg0) (hperf := hperf)
    (hconj := hconj) (hAe := hAe) (hΩ := hΩ) (hζ := hζ) (hq := hq) (hq2' := hq2)
    (hqp := hqp) (hJQ := hJQ) (hF := hF)

theorem e8Model165At_three : E8Model165At 3 := by
  intro F hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv Ã hAe hΩ hmax hA3
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hp3 : 3 < p := three_lt_of_card hcard hp hp2 hrk
  have hpf : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + 1 * (Nat.card F : ℤ) + 1 := by
    simpa using three_dvd_card_sq_add_int hcard hp hp2 hrk
  exact concl165_e8Model F n p q hcard hn hp hp2 1 (Or.inl rfl) hpf
    (fun h => absurd h (by norm_num)) hp3 hq hq2 hqp hqdiv Ã hAe hΩ

theorem e8Model165At_six : E8Model165At 6 := by
  intro F hField hFinite hChar n p q hcard hn hp hp2 hrk hq hq2 hqp hqdiv Ã hAe hΩ hmax hA3
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  have hp3 : 3 < p := by have := seven_le_of_rk2Ord_six hp hp2 hrk; omega
  have hpf : (p : ℤ) ∣ (Nat.card F : ℤ) ^ 2 + (-1) * (Nat.card F : ℤ) + 1 := by
    have h : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := dvd_two_pow_sq_sub_of_rk2Ord_six hp hp2 hrk
    have hle : 2 ^ n ≤ (2 ^ n) ^ 2 := by
      have h2 : 2 ≤ 2 ^ n := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      nlinarith
    have hcast : ((2 ^ n : ℤ) ^ 2 - (2 ^ n : ℤ) + 1) =
        ((2 ^ n) ^ 2 - 2 ^ n + 1 : ℕ) := by
      rw [Nat.cast_add, Nat.cast_sub hle]
      push_cast
      ring
    have h' : (p : ℤ) ∣ (2 ^ n : ℤ) ^ 2 - (2 ^ n : ℤ) + 1 := by
      rw [hcast]
      exact_mod_cast h
    rw [hcard]
    rwa [show (((2 ^ n : ℕ) : ℤ) ^ 2 + (-1) * (((2 ^ n : ℕ) : ℤ)) + 1) =
      (2 ^ n : ℤ) ^ 2 - (2 ^ n : ℤ) + 1 by push_cast; ring]
  exact concl165_e8Model F n p q hcard hn hp hp2 (-1) (Or.inr rfl) hpf
    (fun _ => two_lt_two_pow_of_rk2Ord_six hp hp2 hrk) hp3 hq hq2 hqp hqdiv Ã hAe hΩ

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
