module

public import CFSG.LieType.SpecialLinear.TypeLabel.Period
public import CFSG.HardMathSupport.GuralnickMalle.EndFieldDescent.Curtis
public import CFSG.LieType.SpecialLinear.CurtisDatum
public import CFSG.LieType.SpecialLinear.TypeLabel.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.SpecialLinear
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.SmithCurtis
open MonoidAlgebra
open scoped MatrixGroups MonoidAlgebra TensorProduct

noncomputable section

variable (m : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem le_mul_card_active_of_isCoverType_endField [Fintype F]
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin (m + 1)) F) W)
    [Representation.IsIrreducible ρ]
    (hF : Nat.card F = 2 ^ f) {s : ℕ}
    (hE : Nat.card (End (ZMod 2)[SpecialLinearGroup (Fin (m + 1)) F] ρ.asModule) = 2 ^ s)
    (k : Type) [Field k] [CharP k 2]
    [Algebra (End (ZMod 2)[SpecialLinearGroup (Fin (m + 1)) F] ρ.asModule) k]
    [Algebra F k]
    {y : k ⊗[End (ZMod 2)[SpecialLinearGroup (Fin (m + 1)) F] ρ.asModule] ρ.asModule}
    {χ : SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F 2)
      (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ)) y χ J)
    {ε : Fin f → Finset (Fin (m + 1))} (h0 : ∀ r, (0 : Fin (m + 1)) ∉ ε r)
    (hε : ∀ g ∈ (curtisDatum m F 2).H, χ g = slChiEps m (algebraMap F k) ε g)
    (hne : ∃ r, ε r ≠ ∅) :
    f ≤ s * (Finset.univ.filter fun r => ε r ≠ ∅).card := by
  classical
  let E := End (ZMod 2)[SpecialLinearGroup (Fin (m + 1)) F] ρ.asModule
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨r₀, hr₀⟩ := hne
  obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hr₀
  have hj₀0 : j₀ ≠ 0 := fun h => h0 r₀ (h ▸ hj₀)
  obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hj₀0
  have hj : (i.succ : Fin (m + 1)) ∈ ε r₀ := hi ▸ hj₀
  have hb : bDigit ε i.succ ≠ 0 := by
    intro h
    exact ((bDigit_eq_zero_iff ε i.succ).mp h) r₀ hj
  have hsplit : SplitOver k (curtisDatum m F 2).H := by
    have h := splitOver m F 2 k
    rwa [Subgroup.comap_id] at h
  have : Finite ((RootSystem.coxeterMatrix (isFiniteType_A m)).Group) :=
    Finite.of_equiv (Equiv.Perm (Fin (m + 1))) (CFSG.StandardType.typeAWeylEquiv m).toEquiv
  have hD4 : ∀ h ∈ (curtisDatum m F 2).H, ∃ c : E, χ h = algebraMap E k c :=
    CFSG.HardMathSupport.GuralnickMalle.isCoverType_chi_mem_endField (ρ := ρ) k hsplit ht
  have hval : ∀ u : Fˣ,
      (algebraMap F k) (u : F) ^ bDigit ε i.succ ∈ (algebraMap E k).range := by
    intro u
    obtain ⟨c, hc⟩ := hD4 (hdiag m F i u) (hdiag_mem_H m F i u)
    refine ⟨c, ?_⟩
    rw [← hc, hε (hdiag m F i u) (hdiag_mem_H m F i u), slChiEps_hdiag]
  have hE' : Fintype.card E = 2 ^ s := by
    rw [← Nat.card_eq_fintype_card]
    exact hE
  have hs1 : 1 ≤ s := by
    have h2 : 1 < Nat.card E := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [hE] at h2
    by_contra h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    rw [hs0] at h2
    exact lt_irrefl 1 h2
  have hperiod := le_mul_card_of_values_mem (m := m) (F := F) (f := f) (k := k) (E := E)
    hF hE' hs1 (algebraMap F k) ε i.succ hb hval
  have hsub : (Finset.univ.filter fun r : Fin f => i.succ ∈ ε r) ⊆
      (Finset.univ.filter fun r => ε r ≠ ∅) := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact Finset.nonempty_iff_ne_empty.mp ⟨i.succ, hr⟩
  exact le_trans hperiod (Nat.mul_le_mul_left s (Finset.card_le_card hsub))

end

end CFSG.LieType.SpecialLinear
