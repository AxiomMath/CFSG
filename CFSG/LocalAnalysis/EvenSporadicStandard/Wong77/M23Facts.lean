module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ModFacts
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.EvenSporadicStandard.Wong77

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier

@[expose] def mkM23 (x : Equiv.Perm (Fin 23)) (hx : x ∈ NativeSporadic.M23) : Carrier .M23 :=
  (⟨x, hx⟩ : M23)

theorem permOf_mem (g : Carrier .M23) : permOf g ∈ NativeSporadic.M23 := (show M23 from g).2

theorem permOf_injective : Function.Injective permOf := fun _ _ h => Subtype.ext h

theorem orderOf_permOf (g : Carrier .M23) : orderOf (permOf g) = orderOf g :=
  Subgroup.orderOf_coe (show M23 from g)

theorem m23Rep1_eq : m23Rep1 = m23PermA := by
  simp [m23Rep1, m23InvReps, m23InvRepWords, evalCodes]

theorem m23Rep1_mem : m23Rep1 ∈ NativeSporadic.M23 := by
  rw [m23Rep1_eq, m23_eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

@[expose] def rep1 : Carrier .M23 := mkM23 m23Rep1 m23Rep1_mem

theorem permOf_rep1 : permOf rep1 = m23PermA := m23Rep1_eq

theorem orderOf_rep1 : orderOf rep1 = 2 := by
  rw [← orderOf_permOf, permOf_rep1]
  apply orderOf_eq_prime
  · decide
  · decide

theorem m23_involution_conj :
    ∀ u : Carrier .M23, orderOf u = 2 → ∃ c : Carrier .M23, u = c * rep1 * c⁻¹ := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m23_oddcore_cover
  rw [m23InvReps_eq] at hok
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hr1 : m23Rep1 ∈ m23Certificate.originalSubgroup := by
    rw [m23Certificate_originalSubgroup]; exact m23Rep1_mem
  have hro1 : orderOf m23Rep1 = 2 := (orderOf_permOf rep1).trans orderOf_rep1
  have h := (exists_conj_of_repsOK hn m23Certificate m23Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m23Rep1] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok).1
  rw [m23Certificate_originalSubgroup] at h
  intro u hu
  obtain ⟨r, hr, c, hc, hcu⟩ := h (permOf u) (by simpa using permOf_mem u)
    (by rw [orderOf_permOf]; exact hu)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨mkM23 c hc, permOf_injective hcu⟩

end CFSG.EvenSporadicStandard.Wong77
