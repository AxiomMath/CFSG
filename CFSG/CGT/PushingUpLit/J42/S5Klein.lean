module

public import CFSG.CGT.PushingUpLit.J42.S5Setup

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.GH74 CFSG.CGT.PushingUpLit.BHS
  CFSG.Quasithin CFSG.Quasithin.G6 Equiv Equiv.Perm

@[expose] def sA : Perm (Fin 5) := swap 0 1 * swap 2 3

@[expose] def sB : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def sC : Perm (Fin 5) := swap 0 3 * swap 1 2

@[expose] def klein : Subgroup (Perm (Fin 5)) where
  carrier := {σ | σ = 1 ∨ σ = sA ∨ σ = sB ∨ σ = sC}
  one_mem' := Or.inl rfl
  mul_mem' := fun {a b} ha hb => by
    have ha' : a = 1 ∨ a = sA ∨ a = sB ∨ a = sC := ha
    have hb' : b = 1 ∨ b = sA ∨ b = sB ∨ b = sC := hb
    show a * b = 1 ∨ a * b = sA ∨ a * b = sB ∨ a * b = sC
    rcases ha' with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;>
      simp only [sA, sB, sC] <;> decide
  inv_mem' := fun {a} ha => by
    have ha' : a = 1 ∨ a = sA ∨ a = sB ∨ a = sC := ha
    show a⁻¹ = 1 ∨ a⁻¹ = sA ∨ a⁻¹ = sB ∨ a⁻¹ = sC
    rcases ha' with rfl | rfl | rfl | rfl <;> simp only [sA, sB, sC] <;> decide

theorem mem_klein {σ : Perm (Fin 5)} : σ ∈ klein ↔ σ = 1 ∨ σ = sA ∨ σ = sB ∨ σ = sC := Iff.rfl

instance : DecidablePred (· ∈ klein) := fun σ =>
  inferInstanceAs (Decidable (σ = 1 ∨ σ = sA ∨ σ = sB ∨ σ = sC))

theorem card_klein : Nat.card klein = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem sA_mul_sB : sA * sB = sC := by decide +kernel

theorem sA_fix4 : sA 4 = 4 := by decide +kernel

theorem sB_fix4 : sB 4 = 4 := by decide +kernel

theorem sC_fix4 : sC 4 = 4 := by decide +kernel

theorem five_distinct : ∀ σ : Perm (Fin 5), σ 4 = 4 → (∀ i : Fin 5, i ≠ 4 → σ i ≠ i) →
    σ * σ ≠ 1 →
    ({1, σ, σ * σ, σ * σ * σ, cyc 0 1 2 * σ * (cyc 0 1 2)⁻¹} : Finset (Perm (Fin 5))).card = 5 := by
  decide +kernel

theorem mem_klein_of_fpf : ∀ σ : Perm (Fin 5), σ 4 = 4 → (∀ i : Fin 5, i ≠ 4 → σ i ≠ i) →
    σ * σ = 1 → σ ∈ klein := by
  decide +kernel

theorem eq_klein_of_fourGroup {N : Subgroup (Perm (Fin 5))}
    (h : FourGroup ({0, 1, 2, 3} : Finset (Fin 5)) N) (hN : N ≠ ⊥) : N = klein := by
  have hI : ({0, 1, 2, 3} : Finset (Fin 5)).card = 4 := by decide
  have h4 : Nat.card N = 4 := h.card_eq_four hI hN
  have hle : N ≤ klein := by
    intro σ hσ
    by_cases hσ1 : σ = 1
    · rw [hσ1]; exact klein.one_mem
    have hfree := h.free hI hσ hσ1
    have h4fix : σ 4 = 4 := h.fix σ hσ 4 (by decide)
    have hfpf : ∀ i : Fin 5, i ≠ 4 → σ i ≠ i := fun i hi => hfree i (by
      revert i; decide)
    refine mem_klein_of_fpf σ h4fix hfpf ?_
    by_contra hsq
    have hc := five_distinct σ h4fix hfpf hsq
    have hτ : cyc 0 1 2 ∈ altOn ({0, 1, 2, 3} : Finset (Fin 5)) :=
      cyc_mem_altOn_of_mem (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hsub : (({1, σ, σ * σ, σ * σ * σ, cyc 0 1 2 * σ * (cyc 0 1 2)⁻¹} :
        Finset (Perm (Fin 5))) : Set (Perm (Fin 5))) ⊆ (N : Set (Perm (Fin 5))) := by
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact N.one_mem
      · exact hσ
      · exact N.mul_mem hσ hσ
      · exact N.mul_mem (N.mul_mem hσ hσ) hσ
      · exact h.norm _ hτ σ hσ
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hc, ← Nat.card_coe_set_eq] at hcard
    have : Nat.card (N : Set (Perm (Fin 5))) = Nat.card N := rfl
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h4, card_klein])

@[expose] def tau3 : Perm (Fin 5) := cyc 1 3 2

theorem tau3_sA : tau3 * sA * tau3⁻¹ = sB := by decide +kernel

theorem tau3_sB : tau3 * sB * tau3⁻¹ = sC := by decide +kernel

theorem tau3_sC : tau3 * sC * tau3⁻¹ = sA := by decide +kernel

theorem tau3_mem : tau3 ∈ altOn ({0, 1, 2, 3} : Finset (Fin 5)) :=
  cyc_mem_altOn_of_mem (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

@[expose] def qvec (X Y z : ZMod 2) : ↥(coreMod 5) :=
  mkEven ![X + Y + z, X + z, Y + z, z, 0] (by
    revert X Y z
    decide)

theorem vcoord_qvec (X Y z : ZMod 2) (i : Fin 5) :
    vcoord (qvec X Y z) i = ![X + Y + z, X + z, Y + z, z, 0] i := rfl

theorem qvec_mul (X Y z X' Y' z' : ZMod 2) :
    qvec X Y z * qvec X' Y' z' = qvec (X + X') (Y + Y') (z + z') := by
  refine vcoord_ext fun i => ?_
  rw [vcoord_mul]
  fin_cases i <;> simp [vcoord_qvec] <;> ring

theorem qvec_zero : qvec 0 0 0 = 1 := by
  refine vcoord_ext fun i => ?_
  fin_cases i <;> simp [vcoord_qvec, vcoord_one]

theorem qvec_inj {X Y z X' Y' z' : ZMod 2} (h : qvec X Y z = qvec X' Y' z') :
    X = X' ∧ Y = Y' ∧ z = z' := by
  revert X Y z X' Y' z'
  decide +kernel

theorem xI_eq : xI = qvec 0 0 1 := by decide +kernel

theorem exists_qvec {u : ↥(coreMod 5)} (h : vcoord u 4 = 0) : ∃ X Y z, u = qvec X Y z := by
  refine ⟨vcoord u 1 + vcoord u 3, vcoord u 2 + vcoord u 3, vcoord u 3, ?_⟩
  have hs := sum_vcoord u
  simp only [Fin.sum_univ_five] at hs
  have key : ∀ a0 a1 a2 a3 a4 : ZMod 2, a0 + a1 + a2 + a3 + a4 = 0 → a4 = 0 →
      a0 = (a1 + a3) + (a2 + a3) + a3 ∧ a1 = (a1 + a3) + a3 ∧ a2 = (a2 + a3) + a3 := by
    decide
  obtain ⟨k0, k1, k2⟩ := key _ _ _ _ _ hs h
  refine vcoord_ext fun i => ?_
  fin_cases i
  · exact k0
  · exact k1
  · exact k2
  · rfl
  · exact h

theorem coreAct_sA (X Y z : ZMod 2) : coreAct 5 sA (qvec X Y z) = qvec X Y (z + Y) := by
  revert X Y z
  decide +kernel

theorem coreAct_sB (X Y z : ZMod 2) : coreAct 5 sB (qvec X Y z) = qvec X Y (z + X) := by
  revert X Y z
  decide +kernel

theorem coreAct_sC (X Y z : ZMod 2) : coreAct 5 sC (qvec X Y z) = qvec X Y (z + X + Y) := by
  revert X Y z
  decide +kernel

end CFSG.CGT.PushingUpLit.SolK
