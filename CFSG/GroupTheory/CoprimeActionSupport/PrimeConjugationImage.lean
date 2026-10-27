module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Group

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.PrimeConjugationImage

theorem exists_subgroup {H : Type*} [Group H] [Finite H] {q : ℕ} (hq : q.Prime)
    (E D : Subgroup H) (hE : E ≠ ⊥) (hD : Nat.card D = q) (hcomm : ⁅E, D⁆ = E) :
    ∃ C : Subgroup (MulAut E), Nat.card C = q := by
  have hN : D ≤ Subgroup.normalizer E := by
    have := Subgroup.normalizer_commutator_ge_right E D
    rwa [hcomm] at this
  let φ : D →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  haveI : Fact q.Prime := ⟨hq⟩
  have hker : φ.ker = ⊥ := by
    have hdvd : Nat.card φ.ker ∣ q := hD ▸ Subgroup.card_subgroup_dvd_card φ.ker
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have htop : φ.ker = ⊤ := Subgroup.card_eq_iff_eq_top _ |>.mp (h.trans hD.symm)
      apply hE
      rw [← hcomm, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr]
      intro e he d hd'
      have : (⟨d, hd'⟩ : D) ∈ φ.ker := by rw [htop]; trivial
      have h2 := (MonoidHom.mem_ker.mp this)
      have h3 := congrArg (fun f : MulAut E => (f ⟨e, he⟩ : E).1) h2
      simp [φ] at h3
      calc d * e = (d * e * d⁻¹) * d := by group
        _ = e * d := by rw [h3]
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  exact ⟨φ.range, by rw [← hD]; exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm⟩

end CFSG.GroupTheory.CoprimeActionSupport.PrimeConjugationImage
