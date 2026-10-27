module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.PerfectKer
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Escape
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.SiegelEigen
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.SiegelBlock
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.SiegelConj
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.SiegelSL2

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)

variable {K : Type} [Field K]

theorem false_of_siegel [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpK : p ∣ Nat.card K - 1) {v : StatedSp 2 K}
    (hv : v ∈ perfectJoin (flagStabilizer 2 K {2})) (hvp : v ^ p = 1) (hv1 : v ≠ 1)
    (hfix : ∀ V : Subgroup (StatedSp 2 K), V ≤ Subgroup.centralizer ({v} : Set (StatedSp 2 K)) →
      ⁅V, V⁆ = V → V ≤ flagStabilizer 2 K {2}) : False := by
  have hp2 : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).1 h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    omega
  obtain ⟨hvJ, hdet⟩ := exists_mem_ker_of_mem_perfectJoin _ (blockDet (K := K)) hv
  set vJ : ↥(flagStabilizer 2 K {2}) := ⟨v, hvJ⟩ with hvJdef
  set A : Matrix (Fin 2) (Fin 2) K := blockA vJ with hA
  have hdetA : A.det = 1 := by
    rw [← blockDet_apply, hdet]; rfl
  have hApow : A ^ p = 1 := by
    rw [hA, ← map_pow, hvJdef]
    have : (⟨v, hvJ⟩ : ↥(flagStabilizer 2 K {2})) ^ p = 1 := Subtype.ext hvp
    rw [this, map_one]
  have hMa : ∀ u : Fin 2 → K, spMat v *ᵥ (Sum.elim u 0 : Fin 2 ⊕ Fin 2 → K) =
      Sum.elim (A *ᵥ u) 0 := fun u => spMat_mulVec_elim_zero vJ u
  have hne : ∀ u : Fin 2 → K, u ≠ 0 → (Sum.elim u 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := by
    intro u hu h
    apply hu
    funext i
    exact congrFun h (Sum.inl i)
  have hinr : ∀ u : Fin 2 → K, ∀ j, (Sum.elim u 0 : Fin 2 ⊕ Fin 2 → K) (Sum.inr j) = 0 :=
    fun u j => rfl
  by_cases hfixed : ∃ u : Fin 2 → K, u ≠ 0 ∧ A *ᵥ u = u
  · obtain ⟨u, hu0, hu⟩ := hfixed
    obtain ⟨W, b, hWc, hWp, hab, w, hwW, hw⟩ := exists_perfect_escape hK hvp hp2
      (hne u hu0) (by rw [hMa, hu])
    have hwJ : w ∈ flagStabilizer 2 K {2} := hfix W hWc hWp hwW
    have hb : ∀ j, b (Sum.inr j) = 0 := by
      intro j
      have h1 := mulVec_inr_eq_zero_of_mem hwJ (hinr u) j
      rw [hw] at h1
      simpa using h1
    have := psf_eq_zero_of_inr_eq_zero (hinr u) hb
    rw [hab] at this
    exact one_ne_zero this
  · push Not at hfixed
    have hp0 : 0 < p := hp.pos
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by
      rw [Nat.card_units]; exact hpK)
    have hω : IsPrimitiveRoot (ωu : K) p := by
      rw [← hωu]
      exact (IsPrimitiveRoot.orderOf ωu).map_of_injective (f := Units.coeHom K) Units.val_injective
    obtain ⟨ζ, hζp, hζ2, u, u', hu0, hu0', hu, hu'⟩ :=
      exists_eigenpair hp0 hω hApow hdetA hfixed
    have hsmul : ∀ (c : K) (w : Fin 2 → K), (Sum.elim (c • w) 0 : Fin 2 ⊕ Fin 2 → K) =
        c • (Sum.elim w 0 : Fin 2 ⊕ Fin 2 → K) := by
      intro c w
      funext x
      rcases x with i | i <;> simp
    obtain ⟨g, y, hg0, hg1, hya', hconj⟩ := exists_frame_conj v hvp hp2 hζp hζ2
      (hne u hu0) (hne u' hu0') (by rw [hMa, hu, hsmul]) (by rw [hMa, hu', hsmul])
      (psf_eq_zero_of_inr_eq_zero (hinr u) (hinr u'))
    obtain ⟨W, hWc, hWp, w, hwW, hw⟩ := exists_perfect_conj_escape hK v g ζ hconj
    have hwJ : w ∈ flagStabilizer 2 K {2} := hfix W hWc hWp hwW
    rw [hg0, hg1] at hw
    have hy : ∀ j, y (Sum.inr j) = 0 := by
      intro j
      have h1 := mulVec_inr_eq_zero_of_mem hwJ (hinr u) j
      rw [hw] at h1
      simpa using h1
    have := psf_eq_zero_of_inr_eq_zero hy (hinr u')
    rw [hya'] at this
    exact one_ne_zero this

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
