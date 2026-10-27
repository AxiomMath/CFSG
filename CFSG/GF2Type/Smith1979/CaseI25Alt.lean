module

public import CFSG.GH74.GLS.C3.Layer1.Th2AltInv
public import Mathlib.GroupTheory.Nilpotent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

theorem no_conj_elemAbelian_sixteen_alt {n : ℕ} (hn : n = 10 ∨ n = 11)
    (K : Subgroup (alternatingGroup (Fin n))) (hK : ∀ x ∈ K, x * x = 1)
    (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hcard : Nat.card K = 16)
    (hconj : ∀ x ∈ K, ∀ y ∈ K, x ≠ 1 → y ≠ 1 →
      (x : Equiv.Perm (Fin n)).cycleType = (y : Equiv.Perm (Fin n)).cycleType) : False := by
  classical
  clear hcomm
  have hn11 : n ≤ 11 := by omega
  obtain ⟨x0, hx0K, hx01⟩ : ∃ x ∈ K, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : K = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      exact hcon
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨s, hs⟩ : ∃ s : ℕ,
      ((x0 : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType.sum = s := ⟨_, rfl⟩
  have hs48 : s = 4 ∨ s = 8 := by
    rw [← hs]
    rcases CFSG.GH74.GLS.Th2.AltInv.cycleType_involution hn11 (hK x0 hx0K) hx01 with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  have hfix : ∀ g : K, Fintype.card (MulAction.fixedBy (Fin n) g) =
      n - ((g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).cycleType.sum := by
    intro g
    have hset : MulAction.fixedBy (Fin n) g =
        Function.fixedPoints ((g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := rfl
    rw [← Nat.card_eq_fintype_card, hset, Nat.card_eq_fintype_card]
    have h := Equiv.Perm.card_fixedPoints ((g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))
    rw [Fintype.card_fin] at h
    exact h
  have hone : Fintype.card (MulAction.fixedBy (Fin n) (1 : K)) = n := by
    rw [hfix 1]
    simp [Equiv.Perm.cycleType_one]
  have hterm : ∀ g : K, g ≠ 1 → Fintype.card (MulAction.fixedBy (Fin n) g) = n - s := by
    intro g hg
    have hg1 : (g : alternatingGroup (Fin n)) ≠ 1 := fun h => hg (Subtype.ext h)
    have hc := hconj (g : alternatingGroup (Fin n)) g.2 x0 hx0K hg1 hx01
    rw [hfix g, hc, hs]
  have hfinK : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hfintK : Fintype ↥K := Fintype.ofFinite ↥K
  have hcardK : Fintype.card ↥K = 16 := by rw [← Nat.card_eq_fintype_card, hcard]
  have hcardE : (Finset.univ.erase (1 : K)).card = 15 := by
    simp [Finset.card_erase_of_mem, hcardK]
  have hsplit : ∑ g : K, Fintype.card (MulAction.fixedBy (Fin n) g) =
      Fintype.card (MulAction.fixedBy (Fin n) (1 : K)) +
        ∑ g ∈ Finset.univ.erase (1 : K), Fintype.card (MulAction.fixedBy (Fin n) g) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : K))).symm
  have h2 : ∑ g ∈ Finset.univ.erase (1 : K), Fintype.card (MulAction.fixedBy (Fin n) g) =
      ∑ g ∈ Finset.univ.erase (1 : K), (n - s) :=
    Finset.sum_congr rfl (fun g hg => hterm g (Finset.ne_of_mem_erase hg))
  have h15 : ∑ g ∈ Finset.univ.erase (1 : K), (n - s) = 15 * (n - s) := by
    simp [hcardE, hcardK]
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := ↥K) (X := Fin n)
  rw [hsplit, hone, h2, h15, hcardK] at hB
  omega

theorem no_conj_elemAbelian_sixteen_alt_isConj {n : ℕ} (hn : n = 10 ∨ n = 11)
    (K : Subgroup (alternatingGroup (Fin n))) (hK : ∀ x ∈ K, x * x = 1)
    (hcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hcard : Nat.card K = 16)
    (hconj : ∀ x ∈ K, ∀ y ∈ K, x ≠ 1 → y ≠ 1 → IsConj x y) : False := by
  refine no_conj_elemAbelian_sixteen_alt hn K hK hcomm hcard fun x hx y hy hx1 hy1 => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj x hx y hy hx1 hy1)
  refine Equiv.Perm.isConj_iff_cycleType_eq.1 (isConj_iff.2 ⟨(c : Equiv.Perm (Fin n)), ?_⟩)
  have h := congrArg Subtype.val hc
  simpa using h

end CFSG.GF2Type.Smith1979
