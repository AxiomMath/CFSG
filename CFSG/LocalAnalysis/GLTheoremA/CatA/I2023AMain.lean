module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ATD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AEven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AOdd4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

theorem twoPart_eq_sqrt {n e N : ℕ} (hfac : n.factorization 2 = 6 * e) (hN : N = 2 ^ (12 * e)) :
    twoPart n = Nat.sqrt N := by
  unfold twoPart
  rw [hfac, hN, show (2 : ℕ) ^ (12 * e) = (2 ^ (6 * e)) ^ 2 by ring]
  exact (Nat.sqrt_eq' _).symm

@[expose] def I2023FactD4RankTwo : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower), q.p = 2 → catalogIs S (isTD4Of q) →
    ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E ≤ 9

theorem catalogIs_isTD4Any {S : Type} [Group S] {q : TauCeti.PrimePower}
    (h : catalogIs S (isTD4Of q)) : catalogIs S isTD4Any := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine ⟨i, ?_, ⟨e⟩⟩
  cases i with
  | lie j =>
    obtain ⟨d, hd⟩ := j
    cases d <;> first | exact trivial | exact hi.elim
  | _ => exact hi.elim

section Main

set_option linter.unusedSectionVars false

theorem i2023At_of_facts (G : Type) [Group G] [Finite G]
    (hA : I2023FactD4RankTwo) (hB : I2023FactOutCyclic) (hC : I2023FactC1)
    (hD : I2023FactD2LocalOdd) (hE : I2023FactD4BorelEven) : I2023At G := by
  intro B x L b₀ hstar hchev hTD4 hb₀B hnon h81 hC3
  have hS : IsSTriple 3 B x L := hstar.1.1.1
  have hBmax : GLAIsBmax 3 B := hS.1
  have hxB : x ∈ B := hS.2.1.1
  have hx1 : x ≠ 1 := hS.2.1.2.1
  have hL : GLAPComponent 3 (cx x) L := hS.2.2
  obtain ⟨q, hq2, hZ, hcat, hcard2⟩ := td4_package hL hchev hTD4
  have hEss : ∃ T : Subgroup G, T ≤ cx x ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (T ≃* QuaternionGroup 2) := by
    obtain ⟨T, hTx, hT2, hBT, hTc, hTQ⟩ := hS.2.1.2.2
    exact ⟨T, hTx, hT2, hBT, hTc, hTQ rfl⟩
  have hc : Ctx B x L :=
    ⟨hBmax, hxB, hx1, hL, hstar.1.2.2, hstar.2, cx_le_normalizer hstar, hZ, hC3, hEss, h81⟩
  have hcatAny : catalogIs (PQuot 3 L) isTD4Any := catalogIs_isTD4Any hcat
  have F : TD4Facts (PQuot 3 L) q :=
    { A := hA _ q hq2 hcat
      B := hB _ hcatAny
      C := hC _ q hq2 hcat
      D := fun hodd => hD _ q hq2 hodd hcat
      E := fun hev => hE _ q hq2 hev hcat }
  rcases Nat.even_or_odd q.exponent with hev | hod
  · obtain ⟨bs, hbs, hψout, hψfac, hout⟩ := starOut_even hc F hev hb₀B hnon.2
    exact final_of_starOut hBmax hx1 hL hψout (twoPart_eq_sqrt hψfac hcard2) hout
  · obtain ⟨bs, hbs, hψout, hψfac, hout⟩ := starOut_odd hc F hod hb₀B hnon.2
    exact final_of_starOut hBmax hx1 hL hψout (twoPart_eq_sqrt hψfac hcard2) hout

end Main

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
