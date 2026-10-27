module

public import CFSG.LocalAnalysis.AGLEmbedding.LinearThreeKitParab

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LinearThreeKit

variable {K : Type*} [Field K]

theorem card_scalars_le_three [Finite K] : Nat.card (scalars 3 K) ≤ 3 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let f : scalars 3 K → K := fun g => ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0
  have hf : Function.Injective f := by
    intro g h hgh
    obtain ⟨c, -, hc⟩ := mem_scalars.mp g.2
    obtain ⟨d, -, hd⟩ := mem_scalars.mp h.2
    apply Subtype.ext
    apply Subtype.ext
    have hcd : (c : K) = d := by
      have := hgh
      simp only [f] at this
      rw [hc, hd] at this
      simpa [Matrix.scalar_apply] using this
    rw [hc, hd, hcd]
  have hmem : ∀ g, f g ∈ Polynomial.nthRootsFinset 3 (1 : K) := by
    intro g
    obtain ⟨c, hc, hgc⟩ := mem_scalars.mp g.2
    rw [Polynomial.mem_nthRootsFinset (by norm_num)]
    have : f g = (c : K) := by simp [f, hgc, Matrix.scalar_apply]
    rw [this, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  calc Nat.card (scalars 3 K) ≤ Nat.card (Polynomial.nthRootsFinset 3 (1 : K)) :=
        Nat.card_le_card_of_injective (fun g => ⟨f g, hmem g⟩) (fun g h hgh =>
          hf (congrArg Subtype.val hgh))
    _ = (Polynomial.nthRootsFinset 3 (1 : K)).card := Nat.card_eq_finsetCard _
    _ ≤ 3 := by
      rw [Polynomial.nthRootsFinset]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)

theorem eq_one_of_mem_scalars_of_perfect {d : ℕ} (hd : d = 1 ∨ d = 2)
    {V : Subgroup (SpecialLinearGroup (Fin 3) K)} (hV : V ≤ stabilizer (flagSpace 3 K d))
    (hVp : ⁅V, V⁆ = V) {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ V) (hgs : g ∈ scalars 3 K) :
    g = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hgs
  have hcs : ∀ v : Fin 3 → K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (c : K) • v := fun v => by
    rw [hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hc1 : (c : K) = 1 := by
    rcases hd with rfl | rfl
    · have h := mulVec_single_zero_of_perfect hV hVp hg
      rw [hcs] at h
      have := congrFun h 0
      simpa using this
    · have h := mulVec_sub_mem_of_perfect hV hVp hg (Pi.single 2 1)
      rw [hcs, mem_flagSpace_two_iff] at h
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h
      exact sub_eq_zero.mp h
  apply Subtype.ext
  rw [hc, hc1, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, one_smul,
    SpecialLinearGroup.coe_one]

end CFSG.HardMathSupport.Curtis.Coordinator
