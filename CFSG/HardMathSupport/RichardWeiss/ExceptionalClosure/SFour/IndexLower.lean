module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderAlt

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique Equiv Equiv.Perm
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

def vecI {d r : ℕ} (a : Fin r → Fin d) (γ : Fin d) (I : Finset (Fin r)) : Fin d → ZMod 2 :=
  fun p => ∑ i ∈ I, ((if p = a i then 1 else 0) + (if p = γ then 1 else 0))

theorem vecI_mem {d r : ℕ} (a : Fin r → Fin d) (γ : Fin d) (I : Finset (Fin r)) :
    vecI a γ I ∈ evenWeight d := by
  classical
  simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, vecI]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  decide

theorem vecI_apply_a {d r : ℕ} {a : Fin r → Fin d} {γ : Fin d} (hainj : Function.Injective a)
    (haγ : ∀ i, a i ≠ γ) (I : Finset (Fin r)) (k : Fin r) :
    vecI a γ I (a k) = if k ∈ I then 1 else 0 := by
  classical
  simp only [vecI]
  have h1 : ∀ i : Fin r, (if a k = a i then (1 : ZMod 2) else 0) = if k = i then 1 else 0 :=
    fun i => by
    simp [hainj.eq_iff]
  have h2 : (if a k = γ then (1 : ZMod 2) else 0) = 0 := by simp [haγ k]
  simp only [h1, h2, add_zero, Finset.sum_ite_eq]

theorem vecI_apply_b {d r : ℕ} {a b : Fin r → Fin d} {γ : Fin d} (hba : ∀ i j, b i ≠ a j)
    (hbγ : ∀ i, b i ≠ γ) (I : Finset (Fin r)) (k : Fin r) : vecI a γ I (b k) = 0 := by
  classical
  simp only [vecI]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [hba k i, hbγ k]

theorem two_pow_le_index_altFix {d r : ℕ} (a b : Fin r → Fin d) (γ : Fin d)
    (hainj : Function.Injective a) (hba : ∀ i j, b i ≠ a j) (haγ : ∀ i, a i ≠ γ)
    (hbγ : ∀ i, b i ≠ γ) (E : Subgroup (Perm (Fin d))) (hγ : ∀ g ∈ E, g γ = γ)
    (P : Finset (Fin r)) (ht : ∀ k ∈ P, ∃ g ∈ E, g (b k) = a k) :
    2 ^ P.card ≤ (altFix d E).index := by
  classical
  let X : Finset (Fin r) → evenWeight d := fun I => ⟨vecI a γ I, vecI_mem a γ I⟩
  let f : P.powerset → altHeart d ⧸ altFix d E := fun I =>
    QuotientAddGroup.mk (QuotientAddGroup.mk (X I.1) : altHeart d)
  have hf : Function.Injective f := by
    intro I' J' hIJ
    by_contra hne
    obtain ⟨I, hI⟩ := I'
    obtain ⟨J, hJ⟩ := J'
    have hne' : I ≠ J := fun h => hne (Subtype.ext h)
    obtain ⟨k, hk⟩ : ∃ k, ¬ (k ∈ I ↔ k ∈ J) := by
      by_contra h
      push Not at h
      exact hne' (Finset.ext h)
    have hkP : k ∈ P := by
      by_cases hkI : k ∈ I
      · exact Finset.mem_powerset.1 hI hkI
      · by_cases hkJ : k ∈ J
        · exact Finset.mem_powerset.1 hJ hkJ
        · exact absurd (iff_of_false hkI hkJ) hk
    obtain ⟨g, hg, hgk⟩ := ht k hkP
    have h1 := QuotientAddGroup.eq.1 hIJ
    have hmk : (QuotientAddGroup.mk (-X I + X J) : altHeart d) =
        -(QuotientAddGroup.mk (X I) : altHeart d) + QuotientAddGroup.mk (X J) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_neg]
    have h2 := (mem_altFix_iff d E _).1 h1 g hg (-X I + X J) hmk.symm
    rw [← hmk] at h2
    have h3 := QuotientAddGroup.eq.1 h2.symm
    obtain ⟨c, hc⟩ := (mem_evenWeightOnes_iff d _).1 h3
    set x : evenWeight d := -X I + X J with hx
    have hxp : ∀ p, (x : Fin d → ZMod 2) p = -vecI a γ I p + vecI a γ J p := fun p => rfl
    have hyp : ∀ p, ((evenWeightPerm g x : evenWeight d) : Fin d → ZMod 2) p =
        (x : Fin d → ZMod 2) (g⁻¹ p) := fun p => rfl
    have hcoord : ∀ p, c = -(x : Fin d → ZMod 2) p + (x : Fin d → ZMod 2) (g⁻¹ p) := fun p => by
      have := hc p
      rw [show ((-x + evenWeightPerm g x : evenWeight d) : Fin d → ZMod 2) p =
        -(x : Fin d → ZMod 2) p + ((evenWeightPerm g x : evenWeight d) : Fin d → ZMod 2) p from rfl,
        hyp] at this
      exact this.symm
    have hginv : g⁻¹ γ = γ := by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact (hγ g hg).symm
    have hc0 : c = 0 := by
      have h5 := hcoord γ
      rw [hginv] at h5
      rw [h5]
      exact neg_add_cancel _
    have hak := hcoord (a k)
    have hga : g⁻¹ (a k) = b k := by
      rw [← hgk]; simp
    rw [hga, hxp, hxp, vecI_apply_b hba hbγ, vecI_apply_b hba hbγ,
      vecI_apply_a hainj haγ, vecI_apply_a hainj haγ, hc0] at hak
    by_cases hkI : k ∈ I <;> by_cases hkJ : k ∈ J
    · exact hk (iff_of_true hkI hkJ)
    · simp only [hkI, hkJ, ite_true, ite_false] at hak
      exact absurd hak (by decide)
    · simp only [hkI, hkJ, ite_true, ite_false] at hak
      exact absurd hak (by decide)
    · exact hk (iff_of_false hkI hkJ)
  have hcard : Nat.card P.powerset = 2 ^ P.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powerset]
  rw [← hcard]
  exact Nat.card_le_card_of_injective f hf

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure
