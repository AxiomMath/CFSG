module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbSpFour
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.Classical CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.PartOne.KCPrimary
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {r : ℕ}

@[expose] def PerfFree {X : Type*} [Group X] (v : X) : Prop :=
  ∀ V : Subgroup X, V ≤ Subgroup.centralizer ({v} : Set X) → ⁅V, V⁆ = V → V = ⊥

instance : CharP (ZMod 2) 2 := inferInstance

theorem card_fixed_le_four {v : StatedSp r (ZMod 2)} (hr : 1 ≤ r) (hv3 : v ^ 3 = 1) (hv1 : v ≠ 1)
    (hfree : PerfFree v) :
    Module.finrank (ZMod 2) (primaryComponent (spEnd v) (Polynomial.X - 1)) ≤ 2 := by
  have HB := exists_blocks_sp_three (K := ZMod 2) (f := 1) le_rfl (by simp) hr hv3 hv1
  obtain ⟨s, hs, -⟩ := HB.rank
  by_contra hlt
  obtain ⟨V, hV, hVp, Q, hQV, -, hQ⟩ := perfectNoncycThreeIn_spFixed HB (by omega)
  have hVbot : V = ⊥ := hfree V (hV.trans (spSupported_le_centralizer _)) hVp
  have hQbot : Q = ⊥ := le_bot_iff.mp (hVbot ▸ hQV)
  subst hQbot
  exact hQ inferInstance

theorem fixed_isotropic_pair {v : StatedSp r (ZMod 2)} (hr : 1 ≤ r) (hv3 : v ^ 3 = 1)
    (hv1 : v ≠ 1) (hfree : PerfFree v) {a : Fin r ⊕ Fin r → ZMod 2} (ha : spMat v *ᵥ a = a)
    (ha0 : a ≠ 0) {c : Fin r ⊕ Fin r → ZMod 2} (hc : spMat v *ᵥ c = c)
    (hac : pairedSympForm (ZMod 2) r a c = 0) : c = 0 ∨ c = a := by
  have HB := exists_blocks_sp_three (K := ZMod 2) (f := 1) le_rfl (by simp) hr hv3 hv1
  set Fx := primaryComponent (spEnd v) (Polynomial.X - 1) with hFx
  have hmem : ∀ z : Fin r ⊕ Fin r → ZMod 2, z ∈ Fx ↔ spMat v *ᵥ z = z := by
    intro z
    rw [hFx, HB.fixed_eq, LinearMap.mem_ker]
    change spEnd v z - z = 0 ↔ _
    rw [sub_eq_zero]
    rfl
  have hform : ∀ u w, spForm r (ZMod 2) u w = pairedSympForm (ZMod 2) r u w := by
    intro u w
    rw [spForm_apply]
    simp [pairedSympForm, Matrix.toBilin'_apply',
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram]
  have hcard : Nat.card Fx ≤ 4 := by
    have h1 := card_fixed_le_four hr hv3 hv1 hfree
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 2 ^ Module.finrank (ZMod 2) Fx ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h1
      _ = 4 := by norm_num
  have hnd : ∃ b ∈ Fx, pairedSympForm (ZMod 2) r a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := HB.fixed_nondegenerate.1 ⟨a, (hmem a).2 ha⟩ (fun y => by
      have := hcon y.1 y.2
      show spForm r (ZMod 2) a y.1 = 0
      rw [hform]
      exact this)
    exact ha0 (congrArg Subtype.val h0)
  obtain ⟨b, hbF, hab⟩ := hnd
  have hcF : c ∈ Fx := (hmem c).2 hc
  have haF : a ∈ Fx := (hmem a).2 ha
  have halt : ∀ u, pairedSympForm (ZMod 2) r u u = 0 := by
    intro u
    rw [← hform]
    exact spForm_isAlt u
  have hsymm : ∀ u w, pairedSympForm (ZMod 2) r w u = pairedSympForm (ZMod 2) r u w := by
    intro u w
    have h := halt (u + w)
    simp only [map_add, LinearMap.add_apply, halt u, halt w, zero_add, add_zero] at h
    have h2 : pairedSympForm (ZMod 2) r u w = - pairedSympForm (ZMod 2) r w u := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact h
    rw [h2]
    generalize pairedSympForm (ZMod 2) r w u = t
    revert t; decide
  have hca : pairedSympForm (ZMod 2) r c a = 0 := by rw [hsymm]; exact hac
  by_contra hcon
  push Not at hcon
  obtain ⟨hc0, hca'⟩ := hcon
  have hb0 : b ≠ 0 := fun h => hab (by rw [h]; simp)
  have hba : b ≠ a := fun h => hab (by rw [h]; exact halt a)
  have hab' : a + b ≠ 0 := by
    intro h
    apply hba
    have : b = -a := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [this]
    ext x
    simp
  have hcb : c ≠ b := by
    intro h
    apply hab
    rw [← hsymm, ← h]; exact hca
  have hcab : c ≠ a + b := by
    intro h
    apply hab
    have : pairedSympForm (ZMod 2) r (a + b) a = pairedSympForm (ZMod 2) r b a := by
      simp [halt a]
    rw [← hsymm, ← this, ← h]; exact hca
  have d01 : (0 : Fin r ⊕ Fin r → ZMod 2) ≠ a := ha0.symm
  have d02 : (0 : Fin r ⊕ Fin r → ZMod 2) ≠ b := hb0.symm
  have d03 : (0 : Fin r ⊕ Fin r → ZMod 2) ≠ a + b := hab'.symm
  have d04 : (0 : Fin r ⊕ Fin r → ZMod 2) ≠ c := hc0.symm
  have d12 : a ≠ b := hba.symm
  have d13 : a ≠ a + b := fun h => hb0 (by simpa using h.symm)
  have d14 : a ≠ c := hca'.symm
  have d23 : b ≠ a + b := fun h => ha0 (by simpa using h.symm)
  have d24 : b ≠ c := hcb.symm
  have d34 : a + b ≠ c := hcab.symm
  have hinj : Function.Injective (fun i : Fin 5 =>
      (⟨![0, a, b, a + b, c] i, by
        fin_cases i
        · exact Fx.zero_mem
        · exact haF
        · exact hbF
        · exact Fx.add_mem haF hbF
        · exact hcF⟩ : Fx)) := by
    intro i j hij
    have h := congrArg Subtype.val hij
    simp only at h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | (exfalso; simp at h; exact absurd h (by assumption))
  have h5 := Nat.card_le_card_of_injective _ hinj
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h5
  omega

end CFSG.HardMathSupport.Curtis.UnitaryLevi
