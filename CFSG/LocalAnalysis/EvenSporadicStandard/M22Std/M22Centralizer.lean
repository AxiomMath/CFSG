module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Blueprint.NativeSporadic

theorem card_centralizer_involution_perm :
    ∀ u ∈ NativeSporadic.M22, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := CFSG.QuasithinUnique.Ch1.centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m22Rep1, m22CentQ1.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩)
    2000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      dsimp only
      rw [hsz, hKc1, m22Certificate_originalSubgroup, m22_card])
    u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact hcard.trans hKc1

theorem card_centralizer_involution
    {t : Carrier .M22}
    (ht : orderOf t = 2) : Nat.card (Subgroup.centralizer ({t} : Set (Carrier .M22))) = 384 := by
  let t' : ↥NativeSporadic.M22 := t
  have h := card_centralizer_involution_perm (t' : Equiv.Perm (Fin 22)) t'.2
    (by rw [Subgroup.orderOf_coe]; exact ht)
  rw [← map_centralizer_subtype,
    Subgroup.card_map_of_injective (NativeSporadic.M22).subtype_injective] at h
  exact h

end CFSG.EvenSporadicStandard.M22Std
