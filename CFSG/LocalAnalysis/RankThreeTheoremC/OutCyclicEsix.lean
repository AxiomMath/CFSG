module

public import CFSG.RankThree.PartOne.MB3.OddOutExceptional
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicNine

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.RankThree.PartOne.OutStructure CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree CFSG.ComponentClassification.UnbalancedCatalog

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem torusElt_pow_eq (i : Fin τ.rank) (ζ : Kˣ) (n : ℕ) :
    torusElt τ K i (ζ ^ n) = (torusElt τ K i ζ) ^ n := by
  induction n with
  | zero => simp [torusElt_one]
  | succ n ih => rw [pow_succ, torusElt_mul, ih, pow_succ]

theorem rootVec_single_ne (i : Fin τ.rank) (c : K)
    (h : c • rootVec τ K (Pi.single i 1) = rootVec τ K (Pi.single i 1)) : c = 1 := by
  have hr : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  have e : rootVec τ K (Pi.single i 1) = Finsupp.single (Sum.inr ⟨Pi.single i 1, hr⟩) 1 :=
    dite_eq_left hr
  rw [e] at h
  have := congrArg (fun v => v (Sum.inr ⟨Pi.single i 1, hr⟩)) h
  simpa using this

theorem sum_cartan_single (i j : Fin τ.rank) :
    ∑ k, τ.cartan i k * (Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) k = τ.cartan i j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

theorem torusElt_mul_apply_single (i j k : Fin τ.rank) (a b : ℕ) (ζ : Kˣ) :
    ((torusElt τ K i (ζ ^ a) * torusElt τ K j (ζ ^ b) : (Module.End K (RootModule τ K))ˣ) :
        Module.End K (RootModule τ K)) (rootVec τ K (Pi.single k 1)) =
      (((ζ ^ a) ^ τ.cartan i k * (ζ ^ b) ^ τ.cartan j k : Kˣ) : K) •
        rootVec τ K (Pi.single k 1) := by
  have hr : IsRoot τ (Pi.single k (1 : ℤ)) := isRoot_single τ k
  rw [Units.val_mul, Module.End.mul_apply, torusElt_rootVec j (ζ ^ b) hr, map_smul,
    torusElt_rootVec i (ζ ^ a) hr, smul_smul, sum_cartan_single, sum_cartan_single]
  congr 1
  rw [mul_comm]
  simp

theorem exists_nine_adjointGroup {i j : Fin τ.rank}
    (hij0 : τ.cartan j i = 0) (hji0 : τ.cartan i j = 0) {ζ : Kˣ} (hζ : orderOf ζ = 3) :
    ∃ A : Subgroup (adjointGroup τ K), CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine exists_isElemAbelian_card_nine_of_commute
    (⟨torusElt τ K i ζ, torusElt_mem_adjointGroup i ζ⟩ : adjointGroup τ K)
    ⟨torusElt τ K j ζ, torusElt_mem_adjointGroup j ζ⟩ ?_ ?_ ?_ ?_
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← torusElt_pow_eq, hζ3, torusElt_one]
  · refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← torusElt_pow_eq, hζ3, torusElt_one]
  · exact Subtype.ext (torusElt_mul_comm i j ζ ζ)
  · intro a b h
    have h' : torusElt τ K i (ζ ^ a) * torusElt τ K j (ζ ^ b) = 1 := by
      have := congrArg Subtype.val h
      simpa [torusElt_pow_eq] using this
    have hi := torusElt_mul_apply_single (K := K) i j i a b ζ
    have hj := torusElt_mul_apply_single (K := K) i j j a b ζ
    rw [h', Units.val_one, Module.End.one_apply] at hi hj
    have hi1 := rootVec_single_ne i _ hi.symm
    have hj1 := rootVec_single_ne j _ hj.symm
    rw [Tag.cartan_self, hij0] at hi1
    rw [Tag.cartan_self, hji0] at hj1
    simp only [zpow_zero, mul_one, one_mul] at hi1 hj1
    have e1 : (ζ ^ a) ^ (2 : ℤ) = 1 := Units.ext hi1
    have e2 : (ζ ^ b) ^ (2 : ℤ) = 1 := Units.ext hj1
    have h2a : ζ ^ (a * 2) = 1 := by rw [pow_mul]; simpa using e1
    have h2b : ζ ^ (b * 2) = 1 := by rw [pow_mul]; simpa using e2
    have da := orderOf_dvd_iff_pow_eq_one.mpr h2a
    have db := orderOf_dvd_iff_pow_eq_one.mpr h2b
    rw [hζ] at da db
    exact ⟨by omega, by omega⟩

end Torus

section Exceptional


theorem outPNice_ordinaryE_of_not_dvd_units {p r f : ℕ} (hp : p.Prime) {X : Type} [Group X]
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : ¬ p ∣ r ^ f - 1)
    (hexact : ¬ p ∣ exactE τ) (hr : r.Prime) (hf1 : 1 ≤ f)
    (hm : UntwistedChevalleyModel X τ (r ^ f)) : OutPNice p X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ hm
  obtain ⟨Φ, -, hkerΦ, -⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  have hring := card_ringAut_and_isCyclic hr K hK
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hring.1]; omega)
  have : IsCyclic (RingAut K) := hring.2
  have hker : Nat.card Φ.ker ∣ (r ^ f - 1) ^ τ.rank := by
    rw [hkerΦ]
    refine (Subgroup.card_range_dvd _).trans ?_
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units, hK]
  let Θ := Φ.comp (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (adjointGroup τ K)))
  refine OutPNice.of_mulEquiv e (outPNice_of_hom Θ ?_ ?_ ?_ ?_)
  · intro x y
    exact Prod.ext (ringAut_comm K _ _) (mul_comm _ _)
  · intro δ hδ
    have h1 : (QuotientGroup.mk δ : CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (adjointGroup τ K)) = 1 := (QuotientGroup.eq_one_iff _).mpr hδ
    show Φ (QuotientGroup.mk δ) = 1
    rw [h1, map_one]
  · intro δ hδ k hk
    have hx : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup τ K)) δ) ∈ Φ.ker := hδ
    set x' : Φ.ker := ⟨_, hx⟩ with hx'
    have hxk : x' ^ (p ^ k) = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk' _ δ) ^ (p ^ k) = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have hdvd1 : orderOf x' ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    have hdvd2 : orderOf x' ∣ (r ^ f - 1) ^ τ.rank := (orderOf_dvd_natCard x').trans hker
    have hcop : Nat.Coprime (p ^ k) ((r ^ f - 1) ^ τ.rank) :=
      Nat.Coprime.pow k τ.rank ((Nat.Prime.coprime_iff_not_dvd hp).mpr hq)
    have hx1 : orderOf x' = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have h1 : x' = 1 := orderOf_eq_one_iff.mp hx1
    have h2 : (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (adjointGroup τ K)) δ) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff _).mp h2
  · exact pChain_prod (pChain_of_isCyclic hp) (multiplicative_zmod_pElement hp hexact)

theorem outPNice_E6_three_of_not_dvd {r f : ℕ} {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .E6 r f) (h3 : ¬ 3 ∣ r ^ f - 1) : OutPNice 3 X := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  refine outPNice_ordinaryE_of_not_dvd_units Nat.prime_three .E6 (Or.inl rfl) h3 ?_ hrp hf1 hm
  have he : exactE Tag.E6 = 2 := rfl
  rw [he]
  decide

theorem exists_nine_of_E6 {r f : ℕ} {X : Type} [Group X]
    (h : ChevalleyExceptionalModel X .E6 r f) (h3 : 3 ∣ r ^ f - 1) :
    ∃ A : Subgroup X, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 2 := by
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  have hcardU : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hcardU
  exact exists_isElemAbelian_of_mulEquiv e.symm
    (exists_nine_adjointGroup (i := (0 : Fin 6)) (j := (1 : Fin 6)) (by decide) (by decide) hζ)

end Exceptional

end CFSG.LocalAnalysis.RankThreeTheoremC
