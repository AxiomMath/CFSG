module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalUniOuter

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Matrix CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

section Uni

variable {f n : ℕ} {K : Type} [Field K]

theorem isLocallyBalancedAbs_three_one_primeFormP_uni {ℓ : ℕ} (h : UnitaryFieldData ℓ f K)
    (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3) (hn : 4 ≤ n) (h3 : ¬ 3 ∣ n) :
    IsLocallyBalancedAbs 3 1 (primeFormP h (idGram K n)) := by
  subst hℓ
  classical
  haveI : Finite K := h.finite
  haveI : Finite (primeFormP h (idGram K n)) := finite_primeFormP
  have hn3 : 3 ≤ n := by omega
  have hq : 2 ^ f = 2 ∨ 2 ^ f = 8 := by rcases hf with rfl | rfl <;> simp
  have hne : ¬(n = 3 ∧ 2 ^ f = 2) := fun h' => by omega
  have hpq : 3 ∣ 2 ^ f + 1 := by rcases hq with hq | hq <;> rw [hq] <;> norm_num
  have hg : Nat.gcd n (2 ^ f + 1) = 1 := by
    have h3' : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rcases hq with hq | hq <;> rw [hq]
    · exact h3'.symm
    · exact (Nat.Coprime.pow_left 2 h3').symm
  have hpg : ¬ 3 ∣ Nat.gcd n (2 ^ f + 1) := by rw [hg]; norm_num
  have hZ : normOneScalars h (gramSU h (idGram K n)) n = ⊥ := normOneScalars_eq_bot (by omega) hg
  have hinj := mk_injective_of_eq_bot hZ
  have hcen : Subgroup.center (primeFormP h (idGram K n)) = ⊥ :=
    KCUnitaryRegular.center_primeFormP_eq_bot h isPrimeFormGram_idGram hn3 hne
  refine isLocallyBalancedAbs_one_of_inner_outer_good Nat.prime_three hcen
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _))
    (fun α => QuotientGroup.eq_one_iff α) ?_ ?_ ?_
  · intro y hy
    exact outer_sq_eq_one hn3 hne hg hf hy
  · intro s hs3 hs1
    refine ⟨?_, fun σ hσ2 hσ => exists_moved_of_outer hn3 hne hpq hg hσ2 hσ hs3⟩
    obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective s
    have hX3 : X ^ 3 = 1 := by
      apply hinj
      rw [QuotientGroup.mk_pow, hs3]
      rfl
    exact core_centralizer_primeFormP_eq_bot hZ (noNormalPPrime_three_centralizer_gramSU h hq hX3)
  · intro x hx3 hx
    exact Or.inl (fieldCoreAt_three_of_outer hn hpq hpg hx3 hx)

end Uni

section Row

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

theorem bal207LocalBalRow_uni : Bal207LocalBalRow FamUni := by
  rintro p ⟨d, hd⟩ ⟨hidx, huni⟩
  cases d with
  | twistedA r q =>
    obtain ⟨rfl, -⟩ := hidx
    obtain ⟨h3, hq⟩ := huni
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hd
      (MulEquiv.refl (CatT ⟨.twistedA r q, hd⟩))
    obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := hm
    have h : UnitaryFieldData q.p q.exponent K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have h4 : 4 ≤ r + 1 := by omega
    obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := r + 1) (K := K))
    let e : CatT ⟨.twistedA r q, hd⟩ ≃* primeFormP h (idGram K (r + 1)) :=
      (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
    refine IsLocallyBalancedAbs.of_mulEquiv e
      (isLocallyBalancedAbs_three_one_primeFormP_uni h ?_ ?_ h4 h3)
    · rcases hq with hq | hq <;> exact hq.1
    · rcases hq with hq | hq
      · exact Or.inl hq.2
      · exact Or.inr hq.2
  | _ => exact huni.elim

end Row

end CFSG.HardMathSupport.Dickson.Bal207

end
