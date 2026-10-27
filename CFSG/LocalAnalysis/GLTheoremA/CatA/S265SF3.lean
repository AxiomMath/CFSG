module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF2
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LUPSL
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF3Psu

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

namespace SF

theorem le_linearAutGroup_of_nl {n p : ℕ} (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {F : Type} [Field F] [Finite F] (hpF : p ∣ Nat.card F - 1)
    {X : Subgroup (MulAut (projectiveSL n F))} (hX : IsElemAbelian p X)
    (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) :
    X ≤ linearAutGroup n F := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro x hxX
  by_contra hxL
  have hx1 : x ≠ 1 := fun h1 => hxL (by rw [h1]; exact one_mem _)
  have hxp : x ^ p = 1 := hX.2 x hxX
  have hxS := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.mem_semilinearAutGroup_of_pow_eq_one
    hn hp hp2 hxp
  haveI := Fintype.ofFinite F
  obtain ⟨ℓ, hchar, f, hℓ, hcard⟩ := FiniteField.card' F
  haveI : CharP F ℓ := hchar
  have hF : Nat.card F = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hpf, σ, -, ⟨β, -, hxβ⟩, hkcard⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ f.pos hn hF hp x hxS hxL (orderOf_eq_prime hxp hx1)
  have hk : ∀ c, c ∈ semilinearFixedSubfield σ ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hpow : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p := by
    rw [hkcard, hF, ← pow_mul, Nat.div_mul_cancel hpf]
  obtain ⟨y, hyX, hy1, L, hL⟩ := LUGood_of_conj (YS04LUPSL.psl_core hn hp _ hk
    (YS04LUPSL.dvd_sub_one_of_pow_eq hp hpow hpF)) hxX hx1 hxβ
  exact glaPLayer_ne_bot_of_luCore hp hL (hnl y hyX hy1)

theorem le_primeFormD_of_nl_of_ne {ℓ f n p : ℕ} {F : Type} [Field F]
    (hF : UnitaryFieldData ℓ f F) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hqp : ¬(n = 3 ∧ ℓ ^ f = 2 ^ p)) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))}
    (hX : IsElemAbelian p X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) :
    X ≤ primeFormD hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hF.finite
  intro x hxX
  by_contra hxD
  have hx1 : x ≠ 1 := fun h1 => hxD (by rw [h1]; exact one_mem _)
  have hxp : x ^ p = 1 := hX.2 x hxX
  have hΦx : primeFormFieldFactor hF isPrimeFormGram_one hn hq x ≠ 1 := fun h1 => hxD (by
    rw [← ker_primeFormFieldFactor hF isPrimeFormGram_one hn hq]
    exact MonoidHom.mem_ker.2 h1)
  have hσ : orderOf (primeFormFieldFactor hF isPrimeFormGram_one hn hq x) = p :=
    orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) hΦx
  obtain ⟨hpf, -⟩ := CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary hF hp hp2 hσ
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / p) = 2) := fun h' => hqp ⟨h'.1, by
    rw [← Nat.div_mul_cancel hpf, pow_mul, h'.2]⟩
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' hF hn hq hp
      hp2 x (orderOf_eq_prime hxp hx1) _ rfl hσ
  have hxeq : x = primeFormConjHom hF _ M * primeFormFieldHom hF isPrimeFormGram_one
      (primeFormFieldFactor hF isPrimeFormGram_one hn hq x) * (primeFormConjHom hF _ M)⁻¹ := by
    rw [← hM]
    group
  obtain ⟨y, hyX, hy1, L, hL⟩ :=
    LUGood_of_conj (psu_core_of_ne hF hn hp hp2 hσ hpq hq₀) hxX hx1 hxeq
  exact glaPLayer_ne_bot_of_luCore hp hL (hnl y hyX hy1)

theorem le_primeFormD_of_nl {ℓ f n p : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData ℓ f F)
    (hn : 3 ≤ n) (hn3 : n ≠ 3) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {X : Subgroup (MulAut (primeFormP hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)))}
    (hX : IsElemAbelian p X) (hnl : ∀ α ∈ X, α ≠ 1 → GLAPLayer p (fixSubgroup α) = ⊥) :
    X ≤ primeFormD hF ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  le_primeFormD_of_nl_of_ne hF hn (fun h' => hn3 h'.1) (fun h' => hn3 h'.1) hp hp2 hpq hX hnl

end SF

end CFSG.LocalAnalysis.GLTheoremA.S265

end
