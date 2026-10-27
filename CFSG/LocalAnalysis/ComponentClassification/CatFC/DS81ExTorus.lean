module

public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public section

namespace CFSG.ComponentClassification.CatFC.DS81.Ex

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagUnit_pow (a : Fin τ.rank → Kˣ) (n : ℕ) :
    rootDiagUnit τ a ^ n = rootDiagUnit τ (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, rootDiagUnit_mul]

theorem rootDiagUnit_ne_one_of_rootChar_ne_one (a : Fin τ.rank → Kˣ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (h : rootChar a β ≠ 1) : rootDiagUnit τ a ≠ 1 := by
  intro h1
  have h2 := rootDiag_single_inr (K := K) a ⟨β, hβ⟩
  have h3 : rootDiag a = (1 : Module.End K (RootModule τ K)) := congrArg Units.val h1
  rw [h3, Module.End.one_apply] at h2
  have h4 : (((∏ i, a i ^ β i : Kˣ)) : K) = 1 := by
    have := congrArg (fun v => v (Sum.inr ⟨β, hβ⟩)) h2
    simpa using this.symm
  exact h (Units.ext h4)

theorem orderOf_rootDiagUnit_eq_prime {p : ℕ} [hp : Fact p.Prime] {ε : Kˣ} (hε : orderOf ε = p)
    (c : Fin τ.rank → ℤ) (j : Fin τ.rank) (hj : ¬ (p : ℤ) ∣ c j) :
    orderOf (rootDiagUnit τ fun i => ε ^ c i) = p := by
  have hεp : ε ^ p = 1 := by rw [← hε]; exact pow_orderOf_eq_one ε
  refine orderOf_eq_prime ?_ ?_
  · rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := τ) (K := K)]
    congr 1
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hεp, one_zpow]
  · refine rootDiagUnit_ne_one_of_rootChar_ne_one _ (isRoot_single τ j) ?_
    have hchar : rootChar (fun i => ε ^ c i) (Pi.single j 1) = ε ^ c j := by
      rw [rootChar, Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_apply, hij]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hchar]
    intro h
    apply hj
    have := orderOf_dvd_iff_zpow_eq_one.2 h
    rwa [hε] at this

theorem orderOf_rootDiagUnit_eq_prime_of_pow {p : ℕ} [hp : Fact p.Prime] (a : Fin τ.rank → Kˣ)
    (ha : ∀ i, a i ^ p = 1) (j : Fin τ.rank) (hj : a j ≠ 1) :
    orderOf (rootDiagUnit τ a) = p := by
  refine orderOf_eq_prime ?_ ?_
  · rw [rootDiagUnit_pow, ← rootDiagUnit_one (τ := τ) (K := K)]
    congr 1
    funext i
    simpa using ha i
  · refine rootDiagUnit_ne_one_of_rootChar_ne_one a (isRoot_single τ j) ?_
    have hchar : rootChar a (Pi.single j 1) = a j := by
      rw [rootChar, Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_apply, hij]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hchar]
    exact hj

theorem commute_rootDiagUnit_framePt (F : List (Fin τ.rank → ℤ)) (hF : ∀ β ∈ F, IsRoot τ β)
    (c : Fin τ.rank → ℤ) (hc : ∀ β ∈ F, ∑ i, c i * β i = 0) (ε : Kˣ) :
    Commute (rootDiagUnit τ (fun i => ε ^ c i)) ((F.map fun β => pinnedX τ K β 1).prod) := by
  induction F with
  | nil => simp
  | cons β F ih =>
    simp only [List.map_cons, List.prod_cons]
    refine Commute.mul_right ?_ (ih (fun γ hγ => hF γ (List.mem_cons_of_mem _ hγ))
      (fun γ hγ => hc γ (List.mem_cons_of_mem _ hγ)))
    have key : rootChar (fun i => ε ^ c i) β = 1 := by
      have hs : ∀ s : Finset (Fin τ.rank),
          ∏ i ∈ s, ε ^ (c i * β i) = ε ^ (∑ i ∈ s, c i * β i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]
      unfold rootChar
      simp only [← zpow_mul]
      rw [hs, hc β List.mem_cons_self, zpow_zero]
    have h := rootDiagUnit_conj_pinnedX (fun i => ε ^ c i) (hF β List.mem_cons_self) (1 : K)
    rw [key, Units.val_one, one_mul] at h
    exact mul_inv_eq_iff_eq_mul.mp h

theorem sum_single_mul (j : Fin τ.rank) (β : Fin τ.rank → ℤ) :
    ∑ i, (Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) i * β i = β j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_apply, hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem commute_rootDiagUnit_single_framePt (j : Fin τ.rank) (F : List (Fin τ.rank → ℤ))
    (hF : ∀ β ∈ F, IsRoot τ β) (h0 : ∀ β ∈ F, β j = 0) (ε : Kˣ) :
    Commute (rootDiagUnit τ (fun i => ε ^ (Pi.single j (1 : ℤ) : Fin τ.rank → ℤ) i))
      ((F.map fun β => pinnedX τ K β 1).prod) :=
  commute_rootDiagUnit_framePt F hF _ (fun β hβ => by rw [sum_single_mul, h0 β hβ]) ε

theorem torusGroup_le_adjointGroup_ex : torusGroup τ K ≤ adjointGroup τ K :=
  (Subgroup.closure_le _).2 fun _ ⟨p, hp⟩ => hp ▸ torusElt_mem_adjointGroup p.1 p.2

theorem rootDiagUnit_mem_adjointGroup_of_charTwo
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E7 ∨ τ = .E8) [Finite K] (h2 : ringChar K = 2)
    (a : Fin τ.rank → Kˣ) : rootDiagUnit τ a ∈ adjointGroup τ K :=
  torusGroup_le_adjointGroup_ex ((even_power_two_Cartan_root_diagonals_inner τ hτ K h2).1 a)

end CFSG.ComponentClassification.CatFC.DS81.Ex
