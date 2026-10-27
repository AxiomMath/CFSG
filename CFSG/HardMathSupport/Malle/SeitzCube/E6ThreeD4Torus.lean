module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeD4Kernel
public import CFSG.RankThree.PartOne.KE6.EqpOpp
public import CFSG.RankThree.PartOne.S11c.G2Torus

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar)

open scoped MatrixGroups

section Coroot

variable {Ω : Type} [Field Ω]

theorem corootPair_eq_sum {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (δ : Fin τ.rank → ℤ) :
    corootPair β δ = ∑ i, δ i * corootPair β (Pi.single i 1) := by
  have hp := iform_self_pos_of_isRoot hβ
  refine mul_right_cancel₀ hp.ne' ?_
  rw [corootPair_mul hβ δ, Finset.sum_mul]
  have h1 : ∀ i, iform β (Pi.single i 1 : Fin τ.rank → ℤ) = ∑ a, β a * τ.symmetrizedCartan a i := by
    intro i
    simp [iform, Pi.single_apply]
  have hδ : iform β δ = ∑ i, δ i * iform β (Pi.single i 1) := by
    have e1 : iform β δ = ∑ j, ∑ a, β a * τ.symmetrizedCartan a j * δ j := by
      simp only [iform]; exact Finset.sum_comm
    rw [e1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [hδ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, corootPair_mul hβ (Pi.single i 1)]
  ring

theorem rootSL2_HSL_eq_coroot {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (c : Ωˣ) :
    rootSL2 Tag.E6 Ω β (HSL c) =
      rootDiagUnit Tag.E6 (fun k => c ^ corootPair β (Pi.single k 1)) :=
  CFSG.RankThree.PartOne.rootSL2_HSL_eq_rootDiagUnit hβ _
    (fun δ _ => corootPair_eq_sum hβ δ) c

theorem rootDiagUnit_prod_coroots_mem_rootSpan {S : Set (Fin Tag.E6.rank → ℤ)}
    (β : Fin 4 → Fin Tag.E6.rank → ℤ) (hβ : ∀ j, IsRoot Tag.E6 (β j))
    (hS : ∀ j, β j ∈ S ∧ -β j ∈ S) (μ : Fin 4 → Ωˣ) :
    rootDiagUnit Tag.E6 (fun k => ∏ j, μ j ^ corootPair (β j) (Pi.single k 1)) ∈
      rootSpan Tag.E6 Ω S := by
  have hj : ∀ j, rootDiagUnit Tag.E6 (fun k => μ j ^ corootPair (β j) (Pi.single k 1)) ∈
      rootSpan Tag.E6 Ω S := fun j => by
    rw [← rootSL2_HSL_eq_coroot (hβ j) (μ j)]
    exact CFSG.RankThree.PartOne.KE6.rootSL2_mem_rootSpan (hβ j) (hS j).1 (hS j).2 _
  have e : (fun k => ∏ j, μ j ^ corootPair (β j) (Pi.single k 1)) =
      (fun k => μ 0 ^ corootPair (β 0) (Pi.single k 1)) *
        (fun k => μ 1 ^ corootPair (β 1) (Pi.single k 1)) *
        (fun k => μ 2 ^ corootPair (β 2) (Pi.single k 1)) *
        (fun k => μ 3 ^ corootPair (β 3) (Pi.single k 1)) := by
    funext k
    simp only [Fin.prod_univ_four, Pi.mul_apply]
  rw [e, rootDiagUnit_mul, rootDiagUnit_mul, rootDiagUnit_mul]
  exact mul_mem (mul_mem (mul_mem (hj 0) (hj 1)) (hj 2)) (hj 3)

end Coroot

section Data

@[expose] def e6D4Beta : Fin 3 → Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![![![1, 0, 1, 1, 0, 0], ![0, 1, 1, 2, 2, 1], ![0, 0, 0, -1, -1, -1], ![0, 0, -1, -1, -1, 0]],
    ![![-1, 0, -1, -1, -1, -1], ![1, 2, 2, 3, 2, 1], ![0, 0, 0, 1, 1, 0], ![0, 0, 1, 1, 0, 0]],
    ![![1, 1, 1, 1, 1, 0], ![1, 2, 2, 3, 2, 1], ![0, 1, 0, 1, 0, 0], ![0, 1, 1, 1, 1, 1]]]

@[expose] def e6D4Alpha : Fin 3 → Fin 4 → ℤ := ![![1, 0, 1, 0], ![-1, 0, -1, 0], ![1, 0, -1, 0]]

@[expose] def e6D4Gamma : Fin 3 → Fin 4 → ℤ := ![![0, 0, 1, -1], ![0, 0, -1, 1], ![0, 0, -1, 1]]

@[expose] def e6D4F (s : Fin 3) (k : Fin Tag.E6.rank) : ℤ × ℤ × ℤ × ℤ :=
  let A := e6KerP 0 (Pi.single k 1)
  let B := e6KerQ 0 (Pi.single k 1)
  let C := e6KerP 1 (Pi.single k 1)
  let D := e6KerQ 1 (Pi.single k 1)
  let t0 := ∑ j, e6D4Alpha s j * corootPair (e6D4Beta s j) (Pi.single k 1)
  let t1 := ∑ j, e6D4Gamma s j * corootPair (e6D4Beta s j) (Pi.single k 1)
  if s = 0 then (A - C - t0, B - D - t1, 0, 0)
  else if s = 1 then (A - t0, B - C - t1, -D, 0)
  else (A - t0, B - t1, -C, -D)

theorem e6D4_check : ∀ (s : Fin 3) (k : Fin Tag.E6.rank),
    (e6D4F s k).2.1 = (e6D4F s k).2.2.1 ∧ (e6D4F s k).2.1 = (e6D4F s k).1 + (e6D4F s k).2.2.2 := by
  decide +kernel

theorem e6D4_beta_mem : ∀ (s : Fin 3) (j : Fin 4),
    e6D4Beta s j ∈ e6BlockRootsF 2 ∪ e6MixedRootsF s ∧
      -e6D4Beta s j ∈ e6BlockRootsF 2 ∪ e6MixedRootsF s := by
  decide +kernel

theorem e6D4_exp_dvd {p q : ℕ} (hp1 : 1 ≤ p) (hq : p ∣ q ^ 2 + q + 1) (s : Fin 3)
    (k : Fin Tag.E6.rank) :
    (p : ℤ) ∣ e6KerExp (q : ℤ) 1 (((p - 1) * q ^ (s : ℕ) : ℕ) : ℤ) (Pi.single k 1) -
      ∑ j, (e6D4Alpha s j + e6D4Gamma s j * (q : ℤ)) * corootPair (e6D4Beta s j) (Pi.single k 1) := by
  obtain ⟨h1, h2⟩ := e6D4_check s k
  have hΦ : (p : ℤ) ∣ (q : ℤ) ^ 2 + q + 1 := by exact_mod_cast hq
  have hcast : (((p - 1) * q ^ (s : ℕ) : ℕ) : ℤ) = ((p : ℤ) - 1) * (q : ℤ) ^ (s : ℕ) := by
    push_cast [Nat.cast_sub hp1]; ring
  rw [hcast]
  have hsum0 : ∑ j, (e6D4Alpha s j + e6D4Gamma s j * (q : ℤ)) *
        corootPair (e6D4Beta s j) (Pi.single k 1) =
      (∑ j, e6D4Alpha s j * corootPair (e6D4Beta s j) (Pi.single k 1)) +
        (q : ℤ) * ∑ j, e6D4Gamma s j * corootPair (e6D4Beta s j) (Pi.single k 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsum0]
  set A := e6KerP 0 (Pi.single k 1)
  set B := e6KerQ 0 (Pi.single k 1)
  set C := e6KerP 1 (Pi.single k 1)
  set D := e6KerQ 1 (Pi.single k 1)
  unfold e6KerExp
  have key : (1 : ℤ) * (A + (q : ℤ) * B) + ((p : ℤ) - 1) * (q : ℤ) ^ (s : ℕ) * (C + (q : ℤ) * D) -
      ((∑ j, e6D4Alpha s j * corootPair (e6D4Beta s j) (Pi.single k 1)) +
        (q : ℤ) * ∑ j, e6D4Gamma s j * corootPair (e6D4Beta s j) (Pi.single k 1)) =
      ((q : ℤ) ^ 2 + q + 1) * ((e6D4F s k).2.1 + (e6D4F s k).2.2.2 * ((q : ℤ) - 1)) +
        (p : ℤ) * ((q : ℤ) ^ (s : ℕ) * (C + (q : ℤ) * D)) := by
    fin_cases s <;> simp only [e6D4F] at h1 h2 ⊢ <;> simp at h1 h2 ⊢ <;>
      linear_combination (-1 : ℤ) * h2 + (-((q : ℤ) ^ 2)) * h1
  rw [key]
  exact dvd_add (dvd_mul_of_dvd_left hΦ _) (dvd_mul_right _ _)

theorem prod_zpow_eq_zpow_sum_e6 {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

end Data

section Final

variable {Ω : Type} [Field Ω]

theorem e6D4_torus_mem_kernel {ζ : Ωˣ} {p q : ℕ} (hp : p.Prime) (hζ : orderOf ζ = p)
    (hq : p ∣ q ^ 2 + q + 1) (s : Fin 3) :
    rootDiagUnit Tag.E6 (e6KerChar ζ q 1 ((p - 1) * q ^ (s : ℕ))) ∈
      rootSpan Tag.E6 Ω (e6BlockRoots 2 ∪ e6MixedRoots s) := by
  have hU : e6BlockRoots 2 ∪ e6MixedRoots s = ↑(e6BlockRootsF 2 ∪ e6MixedRootsF s) := by
    simp [e6BlockRoots, e6MixedRoots]
  have hroot : ∀ j, IsRoot Tag.E6 (e6D4Beta s j) := fun j => by
    have h := (e6D4_beta_mem s j).1
    rw [Finset.mem_union] at h
    rcases h with h | h
    · exact ((mem_e6BlockRoots 2 _).1 (by simpa [e6BlockRoots] using h)).1
    · exact ((mem_e6MixedRoots s _).1 (by simpa [e6MixedRoots] using h)).1
  have hS : ∀ j, e6D4Beta s j ∈ e6BlockRoots 2 ∪ e6MixedRoots s ∧
      -e6D4Beta s j ∈ e6BlockRoots 2 ∪ e6MixedRoots s := fun j => by
    rw [hU]; exact ⟨by simpa using (e6D4_beta_mem s j).1, by simpa using (e6D4_beta_mem s j).2⟩
  have h := rootDiagUnit_prod_coroots_mem_rootSpan (Ω := Ω) (e6D4Beta s) hroot hS
    (fun j => ζ ^ (e6D4Alpha s j + e6D4Gamma s j * (q : ℤ)))
  convert h using 2
  funext k
  have hp1 : 1 ≤ p := hp.pos
  have h1 : e6KerChar ζ q 1 ((p - 1) * q ^ (s : ℕ)) k =
      ζ ^ e6KerExp (q : ℤ) 1 (((p - 1) * q ^ (s : ℕ) : ℕ) : ℤ) (Pi.single k 1) := by
    have := rootChar_e6KerChar ζ q 1 ((p - 1) * q ^ (s : ℕ)) (Pi.single k 1)
    rw [show rootChar (e6KerChar ζ q 1 ((p - 1) * q ^ (s : ℕ))) (Pi.single k 1) =
        e6KerChar ζ q 1 ((p - 1) * q ^ (s : ℕ)) k by
      simp [rootChar, Pi.single_apply]] at this
    rw [this]
    simp
  rw [h1]
  simp only [← zpow_mul]
  rw [prod_zpow_eq_zpow_sum_e6, zpow_eq_zpow_iff_modEq, hζ]
  refine (Int.modEq_iff_dvd).2 ?_
  have := e6D4_exp_dvd hp1 hq s k
  rw [← dvd_neg, neg_sub]
  convert this using 3

end Final

end CFSG.HardMathSupport.Malle.SeitzCube
