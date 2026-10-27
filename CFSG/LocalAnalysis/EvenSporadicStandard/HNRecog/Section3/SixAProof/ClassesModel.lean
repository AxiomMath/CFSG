module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.TypesOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

private lemma sixA_ne_one_of_cycleType_ne_zero {s : Sym 7} (h : s.cycleType ≠ 0) : s ≠ 1 := by
  intro h1
  exact h (by rw [h1, Equiv.Perm.cycleType_one])

private lemma sixA_ne_sigma_of_mul_ne_zero {s : Sym 7}
    (h : (sixASigma * s).cycleType ≠ 0) : s ≠ sixASigma := by
  intro h1
  exact h (by rw [h1, sixA_sigma_mul_self, Equiv.Perm.cycleType_one])

private lemma sixA_exists_lift (h : IsF5Type a z) (hx : x ∈ orb6A a a) (ψ : SixAIso a x)
    {s : Sym 7} (hs : s ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)))
    (hs2 : s ^ 2 = 1) (h1 : s.cycleType ≠ 0) (h2 : (sixASigma * s).cycleType ≠ 0) :
    ∃ t ∈ Gxy a x, orderOf t = 2 ∧ t ≠ (a * x) ^ 3 ∧ ψ.f t = s :=
  ψ.exists_invol h hx hs hs2 (sixA_ne_one_of_cycleType_ne_zero h1)
    (sixA_ne_sigma_of_mul_ne_zero h2)

theorem sixA_nonempty (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (ψ : SixAIso a x) (i : Fin 5) : (sixASet a z x i).Nonempty := by
  fin_cases i
  · exact ⟨_, rfl⟩
  · obtain ⟨s, hs, hs2, hB⟩ := sixA_model_exists_B
    obtain ⟨t, ht, ht2, htb, hft⟩ := sixA_exists_lift h hx ψ hs hs2
      (by rw [hB.1]; decide) (by rw [hB.2]; decide)
    have hB' : sixAIsB (ψ.f t) := by rw [hft]; exact hB
    exact ⟨t, sixA_mem_P1_of_isB h hx hS ψ ht ht2 htb hB'⟩
  · obtain ⟨s, hs, hs2, hD⟩ := sixA_model_exists_D
    obtain ⟨t, ht, ht2, htb, hft⟩ := sixA_exists_lift h hx ψ hs hs2
      (by rw [hD.1]; decide) (by rw [hD.2]; decide)
    have hD' : sixAIsD (ψ.f t) := by rw [hft]; exact hD
    exact ⟨t, sixA_mem_P2_of_isD h hx hS ψ ht ht2 htb hD'⟩
  · obtain ⟨s, hs, hs2, hA⟩ := sixA_model_exists_A
    obtain ⟨t, ht, ht2, htb, hft⟩ := sixA_exists_lift h hx ψ hs hs2
      (by rw [hA.1]; decide) (by rw [hA.2]; decide)
    have hA' : sixAIsA (ψ.f t) := by rw [hft]; exact hA
    exact ⟨t, sixA_mem_P3_of_isA h hx hS ψ ht ht2 htb hA'⟩
  · obtain ⟨s, hs, hs2, hC⟩ := sixA_model_exists_C
    obtain ⟨t, ht, ht2, htb, hft⟩ := sixA_exists_lift h hx ψ hs hs2
      (by rw [hC.1]; decide) (by rw [hC.2]; decide)
    have hC' : sixAIsC (ψ.f t) := by rw [hft]; exact hC
    exact ⟨t, sixA_mem_P4_of_isC h hx hS ψ ht ht2 htb hC'⟩

private lemma sixA_transitive_aux (h : IsF5Type a z) (hx : x ∈ orb6A a a) (ψ : SixAIso a x)
    {c c' : G} (hcK : c ∈ Gxy a x) (hcK' : c' ∈ Gxy a x)
    (hs : ψ.f c ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)))
    (hs' : ψ.f c' ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)))
    (h1 : (ψ.f c).cycleType = (ψ.f c').cycleType)
    (h2 : (sixASigma * ψ.f c).cycleType = (sixASigma * ψ.f c').cycleType) :
    ∃ k ∈ Gxy a x, k * c * k⁻¹ = c' := by
  obtain ⟨κ, hκ, hκeq⟩ := sixA_model_conj hs hs' h1 h2
  obtain ⟨k, hk, hfk⟩ := ψ.exists_of_mem_cent h hx hκ
  have hky : k ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hk
  have hcy : c ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hcK
  have hc'y : c' ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x hcK'
  refine ⟨k, hk, ?_⟩
  apply (ψ.f_inj (mul_mem (mul_mem hky hcy) (inv_mem hky)) hc'y).1
  rw [ψ.f_conj hky hcy, hfk, hκeq]

theorem sixA_transitive (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (hnc : ¬ IsConj a z) (ψ : SixAIso a x) (i : Fin 5) {c c' : G} (hc : c ∈ sixASet a z x i)
    (hc' : c' ∈ sixASet a z x i) : ∃ k ∈ Gxy a x, k * c * k⁻¹ = c' := by
  fin_cases i
  · change c ∈ ({(a * x) ^ 3} : Set G) at hc
    change c' ∈ ({(a * x) ^ 3} : Set G) at hc'
    rw [Set.mem_singleton_iff] at hc hc'
    exact ⟨1, one_mem _, by rw [hc, hc']; simp⟩
  · obtain ⟨hcK, _⟩ := sixA_subset h hx 1 hc
    obtain ⟨hcK', _⟩ := sixA_subset h hx 1 hc'
    have hB := sixA_isB_of_mem h hx hS hnc ψ hc
    have hB' := sixA_isB_of_mem h hx hS hnc ψ hc'
    exact sixA_transitive_aux h hx ψ hcK hcK' (ψ.f_mem_cent h hx hcK)
      (ψ.f_mem_cent h hx hcK') (hB.1.trans hB'.1.symm) (hB.2.trans hB'.2.symm)
  · obtain ⟨hcK, _⟩ := sixA_subset h hx 2 hc
    obtain ⟨hcK', _⟩ := sixA_subset h hx 2 hc'
    have hD := sixA_isD_of_mem h hx hS hnc ψ hc
    have hD' := sixA_isD_of_mem h hx hS hnc ψ hc'
    exact sixA_transitive_aux h hx ψ hcK hcK' (ψ.f_mem_cent h hx hcK)
      (ψ.f_mem_cent h hx hcK') (hD.1.trans hD'.1.symm) (hD.2.trans hD'.2.symm)
  · obtain ⟨hcK, _⟩ := sixA_subset h hx 3 hc
    obtain ⟨hcK', _⟩ := sixA_subset h hx 3 hc'
    have hA := sixA_isA_of_mem h hx hS hnc ψ hc
    have hA' := sixA_isA_of_mem h hx hS hnc ψ hc'
    exact sixA_transitive_aux h hx ψ hcK hcK' (ψ.f_mem_cent h hx hcK)
      (ψ.f_mem_cent h hx hcK') (hA.1.trans hA'.1.symm) (hA.2.trans hA'.2.symm)
  · obtain ⟨hcK, _⟩ := sixA_subset h hx 4 hc
    obtain ⟨hcK', _⟩ := sixA_subset h hx 4 hc'
    have hC := sixA_isC_of_mem h hx hS hnc ψ hc
    have hC' := sixA_isC_of_mem h hx hS hnc ψ hc'
    exact sixA_transitive_aux h hx ψ hcK hcK' (ψ.f_mem_cent h hx hcK)
      (ψ.f_mem_cent h hx hcK') (hC.1.trans hC'.1.symm) (hC.2.trans hC'.2.symm)

end CFSG.EvenSporadicStandard.HNRecog.Section3
