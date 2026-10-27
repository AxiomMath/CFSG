module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIUnitaryRadical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIUnitaryRigid

public section

namespace CFSG.ComponentClassification.RankTwoHypIIUnitary

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.RankTwoHypIIY CFSG.ComponentClassification.RankTwoHypIIClassical
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem false_of_config (hn : 4 ≤ n) (h42 : ¬ (n = 4 ∧ f = 1))
    {E M : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hc : HypIIConfig (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) E M) :
    False := by
  have := EvenCatalog.finite_mulAut_primeFormP (C := (1 : GL (Fin n) K)) h
  have hXn := inner_normal (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  obtain ⟨t, htE, htX⟩ := IsConcreteLE.not_le_iff_exists.mp hc.not_le
  have ht1 : t ≠ 1 := fun h1 => htX (h1 ▸ one_mem _)
  rcases rigid_or_bar h hn h42 htX (hc.elemAbelian.2 t htE) with hrig | ⟨hev, σ, hσ, θ, hθ⟩
  · exact hc.not_rigidInvolution htE ht1 hrig
  have hc' := hc.conj hXn θ⁻¹
  set E' := E.map (MulAut.conj θ⁻¹).toMonoidHom with hE'
  have hγ : primeFormFieldHom h isPrimeFormGram_one σ ∈ E' :=
    ⟨t, htE, by rw [hθ]; simp [mul_assoc]⟩
  have hγ2 := hc'.elemAbelian.2 _ hγ
  set φ := primeFormFieldFactor h (isPrimeFormGram_one (n := n) (K := K)) (by omega) hq with hφ
  have hφγ : φ (primeFormFieldHom h isPrimeFormGram_one σ) = σ := by
    have := primeFormFieldFactor_apply h (isPrimeFormGram_one (n := n) (K := K)) (by omega) hq 1 σ
    rwa [map_one, one_mul] at this
  have hE0 : ∃ e ∈ E', e ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧
      e ≠ 1 := by
    obtain ⟨s, hsE, hs1, hsγ⟩ :
        ∃ s ∈ E', s ≠ 1 ∧ s ≠ primeFormFieldHom h isPrimeFormGram_one σ := by
      by_contra hcon
      push Not at hcon
      have hle : E' ≤ zpowers (primeFormFieldHom h isPrimeFormGram_one σ) := fun s hs => by
        by_cases h1 : s = 1
        · rw [h1]
          exact one_mem _
        · rw [hcon s hs h1]
          exact mem_zpowers _
      have hcard := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at hcard
      have := orderOf_le_of_pow_eq_one two_pos hγ2
      have := hc'.four_le_card
      omega
    by_cases hsX : s ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    · exact ⟨s, hsE, hsX, hs1⟩
    · have hs2 := hc'.elemAbelian.2 s hsE
      have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
      obtain ⟨hF, -, -, hD⟩ := even_unitary_involution_matrix_lifts h
        (isPrimeFormGram_one (n := n) (K := K)) (by omega) hq s hso
      have hφs : φ s = σ := by
        rcases hF with hF | hF
        · have hsD : s ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by omega) hq, MonoidHom.mem_ker]
            exact hF
          exact absurd (hD s hsD hso) hsX
        · exact RingEquiv.ext fun x => by rw [hF x, hσ x]
      have hsγ1 : s * primeFormFieldHom h isPrimeFormGram_one σ ≠ 1 := by
        intro h1
        apply hsγ
        rw [mul_eq_one_iff_eq_inv] at h1
        rw [h1, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hγ2)]
      have hsγD : s * primeFormFieldHom h isPrimeFormGram_one σ ∈
          primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by omega) hq, MonoidHom.mem_ker]
        change φ (s * primeFormFieldHom h isPrimeFormGram_one σ) = 1
        have hσσ : σ * σ = 1 := by
          have := congrArg φ hγ2
          rwa [map_pow, map_one, hφγ, sq] at this
        rw [map_mul, hφs, hφγ, hσσ]
      exact ⟨_, mul_mem hsE hγ, hD _ hsγD (orderOf_eq_prime (hc'.elemAbelian.2 _ (mul_mem hsE hγ))
        hsγ1), hsγ1⟩
  exact false_of_config_bar h hev hn h42 hc' σ hσ hγ hE0


theorem isSimpleGroup_primeFormP (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    IsSimpleGroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n) (K := K))
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 f h.card_eq_sq n hn
    fun h3 => hq ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  exact (ψ.trans (unitaryPSUEquiv h (by omega))).isSimpleGroup

theorem center_eq_bot_of_perfect {A G : Type*} [Group A] [Group G] [IsSimpleGroup G]
    (hA : commutator A = ⊤) (e : A ⧸ center A ≃* G) : center G = ⊥ := by
  have hsurj : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (center A))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hG : commutator G = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ hsurj, ← Subgroup.map_commutator,
      ← commutator_def, hA]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    have h1 := (commutator_eq_bot_iff_center_eq_top G).2 h
    rw [hG] at h1
    exact top_ne_bot h1

theorem hypII_of_primeFormP (hn : 4 ≤ n) (h42 : ¬ (n = 4 ∧ f = 1)) {A : Type*} [Group A]
    (hA : commutator A = ⊤) (hodd : Even n → Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    AS76b.HypII A := by
  have := EvenCatalog.finite_mulAut_primeFormP (C := (1 : GL (Fin n) K)) h
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have := isSimpleGroup_primeFormP h (by omega) hq
  have hZ := center_eq_bot_of_perfect hA e
  rcases Nat.even_or_odd n with hev | hodd'
  · exact hypII_of_forall_not_config (autModel_mulAut hZ)
      (fun _ _ hc => false_of_config h hn h42 hc) hA (hodd hev) e
  · refine hypII_of_rigidInvolution (autModel_mulAut hZ) (fun t htX ht2 => ?_) hA e
    rcases rigid_or_bar h hn h42 (α := t) htX ht2 with hrig | ⟨hev, -⟩
    · exact hrig
    · exact absurd hev (Nat.not_even_iff_odd.mpr hodd')

theorem hypII_of_psu {A : Type} [Group A] (hA : commutator A = ⊤) {n m : ℕ}
    (hodd : Even n → Odd (Nat.card (center A))) (hn : 4 ≤ n) (h42 : (n, m) ≠ (4, 1))
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .PSU n 2 m) :
    AS76b.HypII A := by
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨ψ⟩ := nonempty_primeFormP_mulEquiv hU (isPrimeFormGram_one (n := n) (K := K))
  exact hypII_of_primeFormP hU hn (fun h4 => h42 (by rw [h4.1, h4.2])) hA hodd
    (e.trans ((unitaryPSUEquiv hU (by omega)).symm.trans ψ.symm))

end CFSG.ComponentClassification.RankTwoHypIIUnitary
