module

public import CFSG.LieType.OutStructureA2

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open
open CFSG.Semidihedral.SemilinearOuterQuotient
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

theorem exists_fieldPart_primeFormP {p₀ f N : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p₀ f K) (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ p₀ ^ f = 2)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hSylow : ∀ S : Sylow p (Outer (primeFormP h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))),
      (S : Subgroup (Outer (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)))).Normal)
    (hpRank : CFSG.Open.pRank p (⊤ : Subgroup (primeFormP h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))) ≤ 1) :
    ∃ F : Subgroup (MulAut (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ⊔ F).Normal ∧
      IsCyclic ↥F ∧
      F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) = ⊥ ∧
      ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ⊔ F).index ∧
      ∀ x : MulAut (primeFormP h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)),
        (∃ k : ℕ, x ^ (p ^ k) = 1) →
          x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (primeFormP h
            ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) ⊔ F := by
  classical
  haveI : Fact p₀.Prime := ⟨h.prime⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := h.finite
  let C : GL (Fin N) K := 1
  have hC : IsPrimeFormGram C := isPrimeFormGram_one
  let T := primeFormP h (C : Matrix (Fin N) (Fin N) K)
  obtain ⟨-, -, -, -, -, hfac, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hN hq
  obtain ⟨-, -, -, hOut, -, -⟩ :=
    unitary_full_diagonal_outer_order h hN hq
  have hcardAut : Nat.card (K ≃+* K) = 2 * f := fieldAut_card K h.prime h.card
  have h2f : 0 < 2 * f := Nat.mul_pos (by norm_num) (Nat.lt_of_lt_of_le zero_lt_one h.one_le)
  haveI : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; exact h2f.ne')
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let F : Subgroup (MulAut T) :=
    (S : Subgroup (K ≃+* K)).map (primeFormFieldHom h hC)
  have hfacφ : ∀ φ : K ≃+* K,
      primeFormFieldFactor h hC hN hq (primeFormFieldHom h hC φ) = φ := by
    intro φ
    have := hfac (1 : primeFormUnitary h (C : Matrix (Fin N) (Fin N) K)) φ
    simpa using this
  have hfinj : Function.Injective (primeFormFieldHom h hC) := by
    rw [injective_iff_map_eq_one]
    intro φ hφ
    have h1 := hfacφ φ
    rw [hφ, map_one] at h1
    exact h1.symm
  have hinner_le_D : CFSG.ComponentClassification.OuterAutomorphisms.inner T ≤
      primeFormD h (C : Matrix (Fin N) (Fin N) K) := by
    intro α hα
    obtain ⟨s, hs⟩ := (hinn α).1 hα
    exact ⟨⟨s, s.2.1⟩, hs.symm⟩
  have hFbot : F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨φ, -, rfl⟩ := hxF
    have hmem : primeFormFieldHom h hC φ ∈
        (primeFormFieldFactor h hC hN hq).ker := by
      rw [hFker]
      exact hinner_le_D hxI
    have hφ1 : φ = 1 := by
      have h1 := (MonoidHom.mem_ker).mp hmem
      rw [hfacφ φ] at h1
      exact h1
    rw [hφ1, map_one]
    exact one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K))
      (primeFormFieldHom h hC) hfinj).isCyclic.mp hScyc
  have hFp : IsPGroup p F := (S.isPGroup').map (primeFormFieldHom h hC)
  have hgcd : ¬ p ∣ Nat.gcd N (p₀ ^ f + 1) := by
    intro hdvd
    obtain ⟨hpN, hpq⟩ := Nat.dvd_gcd_iff.1 hdvd
    have hKsq : Nat.card K = (p₀ ^ f) ^ 2 := by
      rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have h2 := GL83.I713.two_le_pRank_statedPSU_of_dvd (K := K) (q := p₀ ^ f)
      (n := N) (ℓ := p) hKsq hp hp2 hN hpN hpq
    let ePU : primeFormP h (C : Matrix (Fin N) (Fin N) K) ≃* unitaryPSU h N :=
      Classical.choice (nonempty_primeFormP_mulEquiv h hC)
    let ePS : unitaryPSU h N ≃* StatedProj (StatedSU N (p₀ ^ f) K) :=
      unitaryPSUEquiv h (by omega)
    have hEq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (ePU.trans ePS)
    have hpRank' : CFSG.Open.pRank p
        (⊤ : Subgroup (StatedProj (StatedSU N (p₀ ^ f) K))) ≤ 1 := by
      rwa [hEq] at hpRank
    exact Nat.not_le_of_lt (Nat.lt_of_le_of_lt hpRank' (by norm_num)) h2
  let φ : (K ≃+* K) →* Outer T :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)).comp
      (primeFormFieldHom h hC)
  let C' : Subgroup (Outer T) := (S : Subgroup (K ≃+* K)).map φ
  have hFC : F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) =
      C' := by
    dsimp [F, C', φ]
    rw [Subgroup.map_map]
  have hmap : (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).map
      (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) =
      F.map (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T)) := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hCindex : C'.index =
      (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).index := by
    rw [← hFC, ← hmap]
    exact Subgroup.index_map_eq
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F)
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hinj : Function.Injective (φ.comp (S : Subgroup (K ≃+* K)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxI : primeFormFieldHom h hC (x : K ≃+* K) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner T := by
      have hx' : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner T))
          (primeFormFieldHom h hC (x : K ≃+* K)) = 1 := hx
      exact (QuotientGroup.eq_one_iff
        (N := CFSG.ComponentClassification.OuterAutomorphisms.inner T) _).mp hx'
    have hxbot : primeFormFieldHom h hC (x : K ≃+* K) ∈
        F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner T :=
      ⟨Subgroup.mem_map_of_mem (primeFormFieldHom h hC) x.2, hxI⟩
    rw [hFbot] at hxbot
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (hfinj (by simpa using Subgroup.mem_bot.mp hxbot)))
  have hCcard : Nat.card ↥C' = Nat.card ↥(S : Subgroup (K ≃+* K)) := by
    have hrange : C' = (φ.comp (S : Subgroup (K ≃+* K)).subtype).range := by
      dsimp [C', φ]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hScard : Nat.card ↥(S : Subgroup (K ≃+* K)) =
      p ^ Nat.factorization (2 * f) p := by
    rw [Sylow.card_eq_multiplicity, hcardAut]
  have hOutEq : Nat.card (Outer T) = C'.index * p ^ Nat.factorization (2 * f) p := by
    have h1 := Subgroup.index_mul_card C'
    rw [hCcard, hScard] at h1
    exact h1.symm
  have hOut' : Nat.card (Outer T) = 2 * f * Nat.gcd N (p₀ ^ f + 1) := by
    simpa [T, C] using hOut
  set v := Nat.factorization (2 * f) p with hv
  set m := ordCompl[p] (2 * f) with hm
  have hpm : ¬ p ∣ m := by
    have hcop : Nat.Coprime p m := Nat.coprime_ordCompl hp (by positivity)
    exact (hp.coprime_iff_not_dvd).mp hcop
  have heq : 2 * f = p ^ v * m := by
    rw [hv, hm, Nat.ordProj_mul_ordCompl_eq_self (2 * f) p]
  have hout' : C'.index * p ^ v ∣ p ^ v * (m * Nat.gcd N (p₀ ^ f + 1)) := by
    have h := hOut'
    rw [hOutEq] at h
    rw [show 2 * f * Nat.gcd N (p₀ ^ f + 1) =
      p ^ v * (m * Nat.gcd N (p₀ ^ f + 1)) by rw [heq]; ring] at h
    rw [h]
  have hidxC : C'.index ∣ m * Nat.gcd N (p₀ ^ f + 1) := by
    have hpv0 : 0 < p ^ v := pow_pos hp.pos v
    rw [mul_comm C'.index (p ^ v)] at hout'
    exact (Nat.mul_dvd_mul_iff_left hpv0).mp hout'
  have hidxC' : ¬ p ∣ C'.index := by
    intro h
    rcases hp.dvd_mul.mp (h.trans hidxC) with h1 | h1
    · exact hpm h1
    · exact hgcd h1
  have hidx : ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner T ⊔ F).index := by
    rw [← hCindex]
    exact hidxC'
  exact exists_fieldPart_of_isPGroup hp F hFp hFcyc hFbot hSylow hidx

end CFSG.LieType.OutStructure
