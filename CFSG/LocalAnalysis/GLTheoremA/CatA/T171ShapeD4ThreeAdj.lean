module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeNeThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171D4

open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false


private lemma two_pow_mod_three_eq_one_or_two (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h1 | h1 <;> rw [h1] <;> norm_num

private lemma two_pow_mod_three_of_not_dvd (n : ℕ) (h : ¬ 3 ∣ 2 ^ n - 1) : 2 ^ n % 3 = 2 := by
  rcases two_pow_mod_three_eq_one_or_two n with h1 | h2
  · exact absurd (Nat.ModEq.dvd' (by change 1 % 3 = 2 ^ n % 3; rw [h1])) h
  · exact h2

private lemma card_mod_three_of_not_dvd {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : ¬ 3 ∣ Nat.card K - 1) : Nat.card K % 3 = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hqK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rw [hqK]
  exact two_pow_mod_three_of_not_dvd (n : ℕ) (by simpa only [hqK] using h)

private lemma catalogIs_isD4any_of_exists {S : Type} [Group S]
    (h : catalogIs S (onLie fun i : TauCeti.LieTypeIndex =>
      ∃ q : TauCeti.PrimePower, i = .D 4 q ∧ q.p = 2)) : catalogIs S isD4any := by
  obtain ⟨j, hj, hne⟩ := h
  refine ⟨j, ?_, hne⟩
  cases j with
  | cyclic _ _ => exact hj.elim
  | alternating _ _ => exact hj.elim
  | lie i =>
      obtain ⟨q, hi, hqp⟩ := hj
      simpa only [isD4any, onLie, hi] using hqp
  | sporadic _ => exact hj.elim

private lemma exists_frobenius_q_of_card {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    {S : LangSetup τ L p₀} {K : Type} [Field K] (hq : S.D.q = Nat.card K)
    (h : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ Nat.card K) ∧
      S.D.Φ = Units.map (entrywiseHom Fr)) :
    ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) := by
  obtain ⟨Fr, hFrc, hΦ⟩ := h
  refine ⟨Fr, ?_, hΦ⟩
  intro c
  rw [hq]
  exact hFrc c

theorem d4ExitAt_adjoint_three {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hG2 : τ = .G2 → 4 ≤ Nat.card K)
    (hE6 : τ = .E6 → ¬ 3 ∣ Nat.card K - 1) :
    F151.D4ExitAt ↥(adjointGroup τ K) 3 := by
  intro x w hx1 hxp hwp hxw Kc hKc hCat hw hmem
  exfalso
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hqK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hpK : ¬ 3 ∣ Nat.card K := by
    rw [hqK]; intro h; exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hqK]; intro h; exact absurd (Nat.prime_five.dvd_of_dvd_pow h) (by norm_num)
  have hτD4 : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h | h <;> simp [h]
  have hmon := LieSemisimple.monomialToralAt_exc LieSemisimple.monomialToralAt_E6_five
    LieSemisimple.monomialToralAt_E7_five hτD4 Nat.prime_three (by norm_num)
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ :=
    (LieComp.ExcCopy.isPerfect_adjointGroup τ K
      (fun h => le_trans (by norm_num) (hG2 h))).commutator_eq_top
  let β : MulAut ↥(adjointGroup τ K) := MulAut.conj x
  have hβ : ∀ c, (β c : ModGL τ K) = (x : ModGL τ K) * c * (x : ModGL τ K)⁻¹ := by
    intro c; change (MulAut.conj x c : ModGL τ K) = _; rw [MulAut.conj_apply]; rfl
  have hhL : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) ∈
      adjointGroup τ (AlgebraicClosure K) := baseChangeGL_mem_adjointGroup _ x.2
  have hxp' : (x : ModGL τ K) ^ 3 = 1 := by
    simpa using congrArg (fun z : ↥(adjointGroup τ K) => (z : ModGL τ K)) hxp
  have hxne : (x : ModGL τ K) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨S, a, ι, hq, huntw, hT, hap, h1, hinj, hrange, hconjι⟩ :=
    LieSemisimple.exists_langSetup_of_inner_untw_of_prime hτ Nat.prime_three hpK
      Nat.prime_five h5K (Or.inl le_rfl) hmon hperf β (x : ModGL τ K) hhL hβ hxp' hxne
  have hKc' : CFSG.Open.IsComponentOf Kc
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hKc
  have hTame := LieSemisimple.langSetup_hTame_of_prime S Nat.prime_three
    (LieSemisimple.natCast_ne_zero_algebraicClosure Nat.prime_three hpK)
    (fun h => Or.inr (by rw [hq]; exact hG2 h)) hT hap h1
  obtain ⟨i, hqs, hKR⟩ := LieComp.components_of_langSetup S Nat.prime_three ι hinj hrange
    (MulAut.conj x) hconjι hT hap h1 hTame hKc'
  let R := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let eJ : ↥Kc ≃* ↥R := (Kc.equivMapOfInjective ι hinj).trans (MulEquiv.subgroupCongr hKR)
  have hD4 : catalogIs (↥R ⧸ Subgroup.center ↥R) isD4any :=
    catalogIs_isD4any_of_exists ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr
      (QuotientGroup.congr (Subgroup.center ↥Kc) (Subgroup.center ↥R) eJ
        (Subgroup.map_center_eq eJ))).1 hCat)
  exact false_of_d4Rational_three_untw hτ S (exists_frobenius_q_of_card hq huntw)
    (fun hτE6 => by rw [hq]; exact card_mod_three_of_not_dvd (hE6 hτE6)) hT hap h1 i hqs hD4

theorem excAdjD4Inner_of_G2Two
    (h2 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 →
      F151.D4ExitAt ↥(adjointGroup .G2 K) 3) :
    F151.ExcAdjD4Inner := by
  intro τ hτ K _ _ _ p hp hp2 hE6
  by_cases hp3 : p = 3
  · subst hp3
    by_cases hcase : τ = .G2 ∧ Nat.card K = 2
    · obtain ⟨hτG2, hcard⟩ := hcase
      subst hτG2
      exact h2 K hcard
    · have hG2le : τ = .G2 → 4 ≤ Nat.card K := by
        intro hτG2
        have hcard2 : Nat.card K ≠ 2 := fun hc => hcase ⟨hτG2, hc⟩
        haveI : Fintype K := Fintype.ofFinite K
        obtain ⟨n, -, hn⟩ := FiniteField.card K 2
        have hqK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
        have hn1 : (n : ℕ) ≠ 1 := by
          intro h1; apply hcard2; rw [hqK, h1]; norm_num
        have hn2 : 2 ≤ (n : ℕ) := by have := n.pos; omega
        have h4 : 4 ≤ 2 ^ (n : ℕ) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n : ℕ) := pow_le_pow_right' (by norm_num) hn2
        rw [hqK]; exact h4
      exact d4ExitAt_adjoint_three hτ K hG2le (fun h => hE6 h rfl)
  · exact d4ExitAt_of_ne_three _ hp hp2 hp3

end CFSG.LocalAnalysis.GLTheoremA.T171D4

end
