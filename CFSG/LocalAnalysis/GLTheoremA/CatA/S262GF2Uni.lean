module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262GF2Red
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusAut
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagU
import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldU

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open TauCeti CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Malle.E27Lie
open CFSG.HardMathSupport.Curtis.Coordinator (autFix mem_autFix)

theorem fixed_perfect_gf2Uni : ∀ (d : TauCeti.ValidLieTypeIndex)
    [Finite (TauCeti.CFSGIndex.lie d).Group], gf2Uni d.1 →
    ∀ a : MulAut (TauCeti.CFSGIndex.lie d).Group, a ≠ 1 → a ^ 3 = 1 →
      ∃ P : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        P ≤ fixSubgroup a ∧ ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  intro d _ hgf2 a ha1 ha3
  obtain ⟨i, hv⟩ := d
  have hi : ∃ r q, i = .twistedA r q := by
    cases i <;> simp_all [gf2Uni]
  obtain ⟨r, q, rfl⟩ := hi
  simp only [gf2Uni] at hgf2
  obtain ⟨hr, hcard⟩ := hgf2
  have hℓf : q.p ^ q.exponent = 2 := by
    simpa [TauCeti.PrimePower.card_def] using hcard
  have hq2 : q.p = 2 := by
    have hp : q.p ∣ 2 := by
      rw [← hℓf]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hp
  have hℓ3 : q.p ≠ 3 := by omega
  have hn : 3 ≤ r + 1 := by omega
  have hqn : (4 ≤ q.p ^ q.exponent ∧ 4 ≤ r + 1) ∨
      (q.p ^ q.exponent = 2 ∧ 10 ≤ r + 1) := Or.inr ⟨hℓf, by omega⟩
  let G := (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group
  have hmodel : StatedClassicalModel G .PSU (r + 1) q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl G)
  obtain ⟨⟨hℓ, hf, -, hne⟩, F, _, _, hFcard, ⟨e₁⟩⟩ := hmodel
  have hne' : ¬(r + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rintro ⟨h1, h2⟩
    exact hne (by rw [h1, h2])
  have h : UnitaryFieldData q.p q.exponent F :=
    ⟨hℓ, hf, by rw [hFcard, ← pow_mul, mul_comm]⟩
  have hC1 : IsPrimeFormGram (1 : GL (Fin (r + 1)) F) := isPrimeFormGram_one
  obtain ⟨θ⟩ : Nonempty (G ≃* primeFormP h
      ((1 : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F)) :=
    ⟨(e₁.trans (unitaryPSUEquiv h (by omega)).symm).trans
      (Classical.choice (unitary_prime_form_full_semilinear_realization h hC1 hn hne').1).symm⟩
  set β := MulAut.congr θ a with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ha3, map_one]
  by_cases hσ1 : primeFormFieldFactor h isPrimeFormGram_one hn hne' β = 1
  · have hD : β ∈ primeFormD h
        ((1 : GL (Fin (r + 1)) F) : Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
      rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn hne']
      exact hσ1
    obtain ⟨y, hy⟩ := hD
    obtain ⟨c, hc⟩ := exists_scalar_of_conjHom_pow_three hn hne' y (hy ▸ hβ3)
    obtain ⟨R, hRfix, hRperf, hR3⟩ :=
      exists_perfect_three_dvd_autFix_of_diag hℓ3 hqn y c hc
    obtain ⟨P, hPfix, hPperf, hP3⟩ := exists_fixed_perfect_of_congr θ a
      (fun x hx => by
        have := hRfix hx
        rwa [mem_autFix, hy] at this)
      hRperf hR3
    exact ⟨P, fun x hx => (mem_fixSubgroup).mpr (hPfix x hx), hPperf, hP3⟩
  · have hq0 : ¬(r + 1 = 3 ∧ q.p ^ (q.exponent / 3) = 2) := by
      rintro ⟨h1, -⟩
      omega
    obtain ⟨D, hDfix, hDperf, hD3⟩ :=
      exists_fixed_perfect_three_PSU h hn hne' hq0 β hβ3 hσ1
    obtain ⟨P, hPfix, hPperf, hP3⟩ := exists_fixed_perfect_of_congr θ a hDfix hDperf hD3
    exact ⟨P, fun x hx => (mem_fixSubgroup).mpr (hPfix x hx), hPperf, hP3⟩

end CFSG.LocalAnalysis.GLTheoremA.S262

end
