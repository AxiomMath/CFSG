module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermOdd
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTypesWitness

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF

open Equiv Subgroup Janko

@[expose] def sixPoints : Finset (Fin 9) :=
  {3, 4, 5, 6, 7, 8}

theorem mem_sixPoints {x : Fin 9} (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) : x ∈ sixPoints := by
  revert x
  decide

theorem Fbar_eq_range : Fbar = (alternatingGroup.ofSubtype sixPoints).range := by
  ext g
  rw [alternatingGroup.mem_range_ofSubtype_iff, mem_Fbar_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ x hx
    rw [Perm.mem_support] at hx
    exact mem_sixPoints (fun h => hx (h ▸ h0)) (fun h => hx (h ▸ h1)) (fun h => hx (h ▸ h2))
  · intro h
    refine ⟨?_, ?_, ?_⟩ <;> by_contra hne <;>
      exact absurd (h (Perm.mem_support.mpr hne)) (by decide)

@[expose] noncomputable def FbarEquiv : alternatingGroup sixPoints ≃* Fbar :=
  (MonoidHom.ofInjective alternatingGroup.ofSubtype_injective).trans
    (MulEquiv.subgroupCongr Fbar_eq_range.symm)

theorem card_sixPoints : Nat.card sixPoints = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

theorem card_Fbar : Nat.card Fbar = 360 := by
  have : Nontrivial sixPoints :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [card_sixPoints]; norm_num)
  rw [← Nat.card_congr FbarEquiv.toEquiv, nat_card_alternatingGroup, card_sixPoints]
  decide

theorem isSimpleGroup_Fbar : IsSimpleGroup Fbar :=
  have : IsSimpleGroup (alternatingGroup sixPoints) :=
    alternatingGroup.isSimpleGroup (by rw [card_sixPoints]; norm_num)
  FbarEquiv.symm.isSimpleGroup

theorem sbar₁_apply_of_ne : ∀ x : Fin 9, x ≠ 0 → x ≠ 1 → x ≠ 2 → (sbar₁ : Perm (Fin 9)) x = x := by
  decide

theorem commute_sbar₁_of_mem_Fbar {g : alternatingGroup (Fin 9)} (hg : g ∈ Fbar) :
    Commute g sbar₁ := by
  obtain ⟨h0, h1, h2⟩ := mem_Fbar_iff.mp hg
  have hdisj : Perm.Disjoint (g : Perm (Fin 9)) sbar₁ := by
    intro x
    by_cases hx0 : x = 0
    · exact Or.inl (hx0 ▸ h0)
    by_cases hx1 : x = 1
    · exact Or.inl (hx1 ▸ h1)
    by_cases hx2 : x = 2
    · exact Or.inl (hx2 ▸ h2)
    exact Or.inr (sbar₁_apply_of_ne x hx0 hx1 hx2)
  exact Subtype.ext hdisj.commute.eq

theorem sbar₁_notMem_Fbar : sbar₁ ∉ Fbar := fun h =>
  absurd (mem_Fbar_iff.mp h).1 (by decide)

theorem orderOf_dvd_sixty_of_apply_eq {σ : Perm (Fin 9)} (h0 : σ 0 = 0) (h1 : σ 1 = 1)
    (h2 : σ 2 = 2) : orderOf σ ∣ 60 := by
  have hsupp := JankoPerm.card_support_le_six h0 h1 h2
  rw [← Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun m hm => ?_
  have hle : m ≤ 6 :=
    (Multiset.le_sum_of_mem hm).trans (by rw [Perm.sum_cycleType]; exact hsupp)
  have hm2 := Perm.two_le_of_mem_cycleType hm
  interval_cases m <;> norm_num

theorem orderOf_dvd_sixty_of_mem_Fbar {g : alternatingGroup (Fin 9)} (hg : g ∈ Fbar) :
    orderOf g ∣ 60 := by
  obtain ⟨h0, h1, h2⟩ := mem_Fbar_iff.mp hg
  rw [← Subgroup.orderOf_coe]
  exact orderOf_dvd_sixty_of_apply_eq h0 h1 h2

private theorem conj_apply_eq {k f : Perm (Fin 9)} (k0 : k 0 = 0) (k1 : k 1 = 1) (k2 : k 2 = 2)
    (hf : ∀ i : Fin 9, i = 0 ∨ i = 1 ∨ i = 2 → f⁻¹ i = 0 ∨ f⁻¹ i = 1 ∨ f⁻¹ i = 2) {i : Fin 9}
    (hi : i = 0 ∨ i = 1 ∨ i = 2) : (f * k * f⁻¹) i = i := by
  rw [Perm.mul_apply, Perm.mul_apply]
  have hk : k (f⁻¹ i) = f⁻¹ i := by
    rcases hf i hi with h | h | h <;> rw [h] <;> assumption
  rw [hk]
  simp

theorem mem_normalizer_Fbar {g : alternatingGroup (Fin 9)}
    (hg : ∀ i : Fin 9, i = 0 ∨ i = 1 ∨ i = 2 →
      (g : Perm (Fin 9)) i = 0 ∨ (g : Perm (Fin 9)) i = 1 ∨ (g : Perm (Fin 9)) i = 2)
    (hg' : ∀ i : Fin 9, i = 0 ∨ i = 1 ∨ i = 2 →
      (g : Perm (Fin 9))⁻¹ i = 0 ∨ (g : Perm (Fin 9))⁻¹ i = 1 ∨ (g : Perm (Fin 9))⁻¹ i = 2) :
    g ∈ normalizer (Fbar : Set (alternatingGroup (Fin 9))) := by
  rw [mem_normalizer_iff]
  intro h
  rw [mem_Fbar_iff, mem_Fbar_iff]
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨conj_apply_eq h0 h1 h2 hg' (by simp), conj_apply_eq h0 h1 h2 hg' (by simp),
      conj_apply_eq h0 h1 h2 hg' (by simp)⟩
  · rintro ⟨h0, h1, h2⟩
    have hinv : ∀ i : Fin 9, i = 0 ∨ i = 1 ∨ i = 2 → ((g : Perm (Fin 9))⁻¹)⁻¹ i = 0 ∨
        ((g : Perm (Fin 9))⁻¹)⁻¹ i = 1 ∨ ((g : Perm (Fin 9))⁻¹)⁻¹ i = 2 := by
      simpa only [inv_inv] using hg
    have e : (h : Perm (Fin 9)) = (g : Perm (Fin 9))⁻¹ * ((g : Perm (Fin 9)) * h *
        (g : Perm (Fin 9))⁻¹) * ((g : Perm (Fin 9))⁻¹)⁻¹ := by group
    rw [e]
    exact ⟨conj_apply_eq h0 h1 h2 hinv (by simp), conj_apply_eq h0 h1 h2 hinv (by simp),
      conj_apply_eq h0 h1 h2 hinv (by simp)⟩

theorem tbar_mem_normalizer_Fbar : tbar ∈ normalizer (Fbar : Set (alternatingGroup (Fin 9))) :=
  mem_normalizer_Fbar (by decide) (by decide)

theorem ℓbar_mem_Fbar : ℓbar ∈ Fbar :=
  mem_Fbar_iff.mpr (by decide)

theorem ybar_mem_Fbar : ybar ∈ Fbar :=
  mem_Fbar_iff.mpr (by decide)

theorem sbar₂_mem_Fbar : sbar₂ ∈ Fbar :=
  mem_Fbar_iff.mpr (by decide)

theorem ebar₂_mem_Fbar : ebar₂ ∈ Fbar :=
  mem_Fbar_iff.mpr (by decide)

theorem ebar₃_mem_Fbar : ebar₃ ∈ Fbar :=
  mem_Fbar_iff.mpr (by decide)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF
