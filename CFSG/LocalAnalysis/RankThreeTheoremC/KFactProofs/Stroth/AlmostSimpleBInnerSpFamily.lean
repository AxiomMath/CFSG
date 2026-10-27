module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGUMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open Polynomial

section Centralizer

variable {K : Type} [Field K]

theorem oddPCoreInClosure_spSupported_factor [Finite K] [CharP K 2] {p ℓ f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hℓ : ℓ = 2) {r : ℕ} {x : StatedSp r K} {a : StatedProj (StatedSp r K)}
    (blocks : SpPrimaryBlocks ℓ f p x a) (h : primaryFactors (spEnd x)) :
    OddPCoreInClosure p ↥(spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  by_cases hself : reciprocalPolynomial (h : K[X]) = h
  · have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
      rw [hself, Set.pair_eq_singleton]
    suffices H : OddPCoreInClosure p ↥(spSupported x {(h : K[X])}) from
      OddPCoreInClosure.of_mulEquiv (MulEquiv.subgroupCongr (congrArg (spSupported x) hO.symm)) H
    by_cases h1 : (h : K[X]) = X - 1
    · obtain ⟨h0, hm⟩ := h
      change h0 = X - 1 at h1
      subst h1
      obtain ⟨φ, -⟩ := blocks.fixedFactor hm
      exact OddPCoreInClosure.of_mulEquiv φ.symm
        (oddPCoreInClosure_sesqUnitaryGroup_alt hp hp2
          (fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)) blocks.fixed_nondegenerate)
    · obtain ⟨d, -, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
        (blocks.selfDual h h1 hself).exists_half
      haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
      haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
      haveI : CharP (AdjoinRoot (h : K[X])) 2 :=
        charP_of_injective_ringHom (AdjoinRoot.of (h : K[X])).injective 2
      exact OddPCoreInClosure.of_mulEquiv φ.symm
        (oddPCoreInClosure_sesqUnitaryGroup hp hp2 hℓ hHf hHfl)
  · have hP := blocks.paired h (fun e => hself e.symm)
    obtain ⟨φ, -, -⟩ := hP.factor
    haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
    haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
    haveI : CharP (AdjoinRoot (h : K[X])) 2 :=
      charP_of_injective_ringHom (AdjoinRoot.of (h : K[X])).injective 2
    exact OddPCoreInClosure.of_mulEquiv φ.symm (oddPCoreInClosure_generalLinearGroup hp hp2)

theorem oddPCoreInClosure_centralizer_statedSp {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hℓ : ℓ = 2) (hℓp : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {r : ℕ} (hr : 1 ≤ r)
    (x : ↥(StatedSp r K)) (hx : x ^ p = 1) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set ↥(StatedSp r K))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓp.ne_zero
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  haveI := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  haveI hcharK : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
  haveI : CharP K 2 := hℓ ▸ hcharK
  by_cases hx1 : x = 1
  · subst hx1
    have htop : Subgroup.centralizer ({1} : Set ↥(StatedSp r K)) = ⊤ := by
      ext g
      simp [Subgroup.mem_centralizer_iff]
    exact OddPCoreInClosure.of_mulEquiv
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm))
      (oddPCoreInClosure_statedSp hp hp2 r)
  · have hpℓ : p ≠ ℓ := by rw [hℓ]; exact hp2
    have hZc : (SymplecticFlag.proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
      rw [SymplecticHigher.ker_proj]
      exact SymplecticHigher.spScalars_le_center
    have hZp : Nat.Coprime (Nat.card (SymplecticFlag.proj r K).ker) p := by
      rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
        ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    have ha1 : SymplecticFlag.proj r K x ≠ 1 := fun h =>
      hx1 (eq_of_map_eq_of_pow_eq_one_of_coprime (a := 1) (b := 0)
        (SymplecticFlag.proj r K) hZc hZp (by rwa [pow_one]) (by simp)
        (by rw [h, map_one]))
    have ha : orderOf (SymplecticFlag.proj r K x) = p :=
      orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
    have hxp : orderOf x = p := orderOf_eq_prime hx hx1
    have blocks := (symplectic_cross_prime_primary_centralizer_blocks hℓp hf hK hp hp2 hpℓ hr _
      ha).2 x rfl hxp
    haveI : Finite ↥(reciprocalOrbits (spEnd x)) :=
      (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
    obtain ⟨hcomm, hind, hjoin⟩ := blocks.directProduct
    have hprod := OddPCoreInClosure.of_noncommPiCoprod hp
      (fun O : ↥(reciprocalOrbits (spEnd x)) => spSupported x (O : Set K[X]))
      (fun i j hij a b ha hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
      hind ?_
    · exact OddPCoreInClosure.of_mulEquiv (MulEquiv.subgroupCongr hjoin) hprod
    · rintro ⟨O, h, hh, rfl⟩
      exact oddPCoreInClosure_spSupported_factor hp hp2 hℓ blocks ⟨h, hh⟩

theorem pClosureOdd_statedProj_sp {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hℓ : ℓ = 2)
    (hℓp : ℓ.Prime) (hf : 1 ≤ f) [Finite K] (hK : Nat.card K = ℓ ^ f) {r : ℕ} (hr : 1 ≤ r) :
    PClosureOdd p (StatedProj (StatedSp r K)) := by
  haveI : CharP K 2 := by
    classical
    haveI := Fintype.ofFinite K
    have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
    haveI : Fact ℓ.Prime := ⟨hℓp⟩
    haveI hcharK : CharP K ℓ := charP_of_card_eq_prime_pow (f := f) hcardK
    exact hℓ ▸ hcharK
  have hZ : (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot
  exact pClosureOdd_quotient_of_central hp _
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
    (fun z hz _ => by rw [hZ] at hz; exact Subgroup.mem_bot.1 hz)
    fun x hx => oddPCoreInClosure_centralizer_statedSp hp hp2 hℓ hℓp hf hK hr x hx

end Centralizer

section Family

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)

theorem chevTwoPClosureOddFamily_symplectic : ChevTwoPClosureOddFamily LieFamilySymplectic := by
  intro p hp hp2 L _ _ hs hnab hrk hSE ⟨dd, hv⟩ hF hdi he
  cases dd with
  | B r q =>
    obtain ⟨e⟩ := he
    have hdi' : q.p = 2 := hdi
    rcases CFSG.Models.lieModel_B r q hv e with hm | hm
    · obtain ⟨⟨-, -, hr2, -⟩, hmod⟩ := hm
      rcases hmod with hmod | ⟨h0, -⟩
      · obtain ⟨-, K, _, _, hcard, ⟨e1⟩⟩ := hmod
        exact PClosureOdd.of_mulEquiv e1.symm
          (pClosureOdd_statedProj_sp hp hp2 hdi' q.prime_p q.exponent_pos hcard (by omega))
      · omega
    · exact absurd hdi' hm.1.2.2.2
  | _ => exact absurd hF (by simp [LieFamilySymplectic])

end Family

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
