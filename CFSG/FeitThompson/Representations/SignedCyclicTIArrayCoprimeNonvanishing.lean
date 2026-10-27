module

public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs
import CFSG.FeitThompson.Representations.CyclicTILinearCharIntegralCoprime

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G} {σ : classFun ↥W →ₗ[ℂ] classFun G}

namespace IsCyclicTIPair

noncomputable def signedProdCharEtaSum (hW : IsCyclicTIPair W W1 W2)
    (σ : classFun ↥W →ₗ[ℂ] classFun G) (ε : Irr ↥W1 × Irr ↥W2 → ℂ) : G → ℂ :=
  letI := hW.finite_left
  letI := hW.finite_right
  letI : Fintype (Irr ↥W1 × Irr ↥W2) := Fintype.ofFinite _
  ∑ p : Irr ↥W1 × Irr ↥W2, ε p • hW.prodCharEta σ p.1 p.2

theorem signedProdCharEtaSum_eq_sum [Fintype (Irr ↥W1 × Irr ↥W2)]
    (hW : IsCyclicTIPair W W1 W2) (ε : Irr ↥W1 × Irr ↥W2 → ℂ) :
    hW.signedProdCharEtaSum σ ε = ∑ p : Irr ↥W1 × Irr ↥W2, ε p • hW.prodCharEta σ p.1 p.2 := by
  rw [signedProdCharEtaSum]
  congr 1
  exact congrArg (@Finset.univ (Irr ↥W1 × Irr ↥W2)) (Subsingleton.elim _ _)

theorem signedProdCharEtaSum_apply [Fintype (Irr ↥W1 × Irr ↥W2)]
    (hW : IsCyclicTIPair W W1 W2) (ε : Irr ↥W1 × Irr ↥W2 → ℂ) (g : G) :
    hW.signedProdCharEtaSum σ ε g =
      ∑ p : Irr ↥W1 × Irr ↥W2, ε p * hW.prodCharEta σ p.1 p.2 g := by
  rw [hW.signedProdCharEtaSum_eq_sum]
  simp [Finset.sum_apply]

theorem signedProdCharEtaSum_mem_classFun (hW : IsCyclicTIPair W W1 W2)
    (ε : Irr ↥W1 × Irr ↥W2 → ℂ) : hW.signedProdCharEtaSum σ ε ∈ classFun G := by
  have := hW.finite_left
  have := hW.finite_right
  have : Fintype (Irr ↥W1 × Irr ↥W2) := Fintype.ofFinite _
  rw [hW.signedProdCharEtaSum_eq_sum]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (hW.prodCharEta_mem_classFun p.1 p.2)

variable [Fintype G] [Fintype ↥W]

theorem exists_int_prodCharEta_apply (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) {g : G}
    (hg : (orderOf g).Coprime (Nat.card ↥W)) :
    ∃ n : ℤ, hW.prodCharEta σ i j g = n := by
  have := hW.isMulCommutative_coe
  obtain ⟨ψ, hψ⟩ := exists_monoidHom_coe_eq_of_mem_Irr (hW.prodChar_mem_Irr i.2 j.2)
  have hbasis : linearCharClassFun ψ = hW.basisProdIrr (i, j) := by
    refine Subtype.ext ?_
    rw [coe_linearCharClassFun, coe_basisProdIrr_apply, ← hψ]
  obtain ⟨n, hn⟩ := exists_int_apply_linearCharClassFun hW hσ ψ (m := Nat.card ↥W)
    Nat.card_pos (fun x => by rw [← map_pow, pow_card_eq_one', map_one]) hg
  refine ⟨n, ?_⟩
  rw [congrFun (hW.prodCharEta_eq_coe_apply i j) g, ← hbasis]
  exact hn

theorem prodCharEta_starIrr_apply (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) (i : Irr ↥W1) (j : Irr ↥W2) (g : G) :
    haveI := hW.finite_left
    haveI := hW.finite_right
    hW.prodCharEta σ (starIrr i) (starIrr j) g = conj (hW.prodCharEta σ i j g) := by
  have := hW.finite_left
  have := hW.finite_right
  exact (congrFun (hW.star_prodCharEta hσ (coe_starIrr i) (coe_starIrr j)) g).symm

theorem signedProdCharEtaSum_mem_virtualChars (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {ε : Irr ↥W1 × Irr ↥W2 → ℂ}
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) : hW.signedProdCharEtaSum σ ε ∈ virtualChars G := by
  have := hW.finite_left
  have := hW.finite_right
  have : Fintype (Irr ↥W1 × Irr ↥W2) := Fintype.ofFinite _
  rw [hW.signedProdCharEtaSum_eq_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hη := hW.prodCharEta_mem_virtualChars hσ p.1 p.2
  rcases hε p with h | h
  · simpa [h] using hη
  · simpa [h] using neg_mem hη

theorem exists_odd_int_signedProdCharEtaSum_apply (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {ε : Irr ↥W1 × Irr ↥W2 → ℂ}
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) {g : G} (hg : (orderOf g).Coprime (Nat.card ↥W)) :
    ∃ n : ℤ, Odd n ∧ hW.signedProdCharEtaSum σ ε g = (n : ℂ) := by
  classical
  have hfl := hW.finite_left
  have hfr := hW.finite_right
  have : Fintype (Irr ↥W1 × Irr ↥W2) := Fintype.ofFinite _
  have hex : ∀ p : Irr ↥W1 × Irr ↥W2, ∃ n : ℤ, hW.prodCharEta σ p.1 p.2 g = n :=
    fun p => hW.exists_int_prodCharEta_apply hσ p.1 p.2 hg
  choose N hN using hex
  have hsign : ∀ p, ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ ε p = (e : ℂ) := by
    intro p
    rcases hε p with h | h
    · exact ⟨1, Or.inl rfl, by simp [h]⟩
    · exact ⟨-1, Or.inr rfl, by simp [h]⟩
  choose e he hee using hsign
  set T : Irr ↥W1 × Irr ↥W2 → Irr ↥W1 × Irr ↥W2 := fun p => (starIrr p.1, starIrr p.2) with hT
  have hTN : ∀ p, N (T p) = N p := by
    intro p
    have h1 : ((N (T p) : ℂ)) = ((N p : ℂ)) := by
      rw [← hN (T p), ← hN p, hT]
      simp only
      rw [hW.prodCharEta_starIrr_apply hσ, hN p]
      simp
    exact_mod_cast h1
  set p0 : Irr ↥W1 × Irr ↥W2 := (principalIrr ↥W1, principalIrr ↥W2) with hp0
  have hNp0 : N p0 = 1 := by
    have h1 : ((N p0 : ℂ)) = 1 := by
      rw [← hN p0, hp0]
      exact congrFun (hW.prodCharEta_principal hσ) g
    exact_mod_cast h1
  refine ⟨∑ p : Irr ↥W1 × Irr ↥W2, e p * N p, ?_, ?_⟩
  ·
    have key : (((∑ p : Irr ↥W1 × Irr ↥W2, e p * N p : ℤ)) : ZMod 2) = 1 := by
      push_cast
      have hstep : ∀ p : Irr ↥W1 × Irr ↥W2,
          ((e p : ZMod 2)) * ((N p : ZMod 2)) = ((N p : ZMod 2)) := by
        intro p
        rcases he p with h | h <;> rw [h] <;> simp
      rw [Finset.sum_congr rfl fun p _ => hstep p,
        ← Finset.add_sum_erase _ _ (Finset.mem_univ p0), hNp0]
      have hzero : ∑ p ∈ Finset.univ.erase p0, ((N p : ZMod 2)) = 0 := by
        refine Finset.sum_involution (fun p _ => T p) ?_ ?_ ?_ ?_
        · intro p _
          rw [hTN p]
          exact CharTwo.add_self_eq_zero _
        ·
          intro p hp _
          simp only [Finset.mem_erase] at hp
          intro hfix
          refine hp.1 ?_
          have h1 : starIrr p.1 = p.1 := (Prod.ext_iff.1 hfix).1
          have h2 : starIrr p.2 = p.2 := (Prod.ext_iff.1 hfix).2
          by_cases hc : p.1 = principalIrr ↥W1
          · by_cases hd : p.2 = principalIrr ↥W2
            · exact Prod.ext hc hd
            · exact absurd h2 (starIrr_ne_self hW.odd_natCard_right hd)
          · exact absurd h1 (starIrr_ne_self hW.odd_natCard_left hc)
        · intro p hp
          simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hp ⊢
          intro hTp
          refine hp ?_
          have h1 : starIrr p.1 = principalIrr ↥W1 := (Prod.ext_iff.1 hTp).1
          have h2 : starIrr p.2 = principalIrr ↥W2 := (Prod.ext_iff.1 hTp).2
          exact Prod.ext (by simpa using congrArg starIrr h1) (by simpa using congrArg starIrr h2)
        · intro p _
          simp [hT]
      rw [hzero, add_zero]
      simp
    rw [← Int.not_even_iff_odd]
    intro heven
    rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast heven.two_dvd)] at key
    exact zero_ne_one key
  · rw [hW.signedProdCharEtaSum_apply]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by rw [hee p, hN p]

theorem one_le_sq_norm_signedProdCharEtaSum_apply (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {ε : Irr ↥W1 × Irr ↥W2 → ℂ}
    (hε : ∀ p, ε p = 1 ∨ ε p = -1) {g : G} (hg : (orderOf g).Coprime (Nat.card ↥W)) :
    1 ≤ ‖hW.signedProdCharEtaSum σ ε g‖ ^ 2 := by
  obtain ⟨n, hodd, hn⟩ := hW.exists_odd_int_signedProdCharEtaSum_apply hσ hε hg
  have h1 : 1 ≤ |n| := Int.one_le_abs (by obtain ⟨k, rfl⟩ := hodd; omega)
  have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h1
  have h3 : ‖hW.signedProdCharEtaSum σ ε g‖ = |(n : ℝ)| := by rw [hn]; simp
  rw [h3]
  nlinarith

end IsCyclicTIPair

end CFSG.FeitThompson

end
