module

public import CFSG.CGT.PushingUpLit.BHS6.NestedPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped Pointwise

variable {n : ℕ}

theorem isSwapGroupOfSize_conjSub {Y : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (h : IsSwapGroupOfSize Y k) (g : Equiv.Perm (Fin n)) : IsSwapGroupOfSize (A1b.conjSub g Y) k := by
  obtain ⟨T, hT, hc, hcard, rfl⟩ := h
  have hinj : Function.Injective fun t : Equiv.Perm (Fin n) => g * t * g⁻¹ := fun a b hab => by
    simpa using hab
  refine ⟨(fun t => g * t * g⁻¹) '' T, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨a, b, hab, rfl⟩ := hT t ht
    refine ⟨g a, g b, g.injective.ne hab, ?_⟩
    exact (Equiv.swap_apply_apply g a b).symm
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    have := congrArg (fun z => g * z * g⁻¹) (hc t ht t' ht')
    simp only [mul_assoc, inv_mul_cancel_left] at this ⊢
    simpa [mul_assoc] using this
  · rw [Set.ncard_image_of_injective _ hinj]
    exact hcard
  · unfold A1b.conjSub
    rw [MonoidHom.map_closure]
    rfl

theorem exists_conjSub_eq_of_isSwapGroupOfSize {Y Y' : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (hY : IsSwapGroupOfSize Y k) (hY' : IsSwapGroupOfSize Y' k) :
    ∃ g : Equiv.Perm (Fin n), A1b.conjSub g Y = Y' := by
  obtain ⟨T, hT, hc, hcard, rfl⟩ := hY
  obtain ⟨T', hT', hc', hcard', rfl⟩ := hY'
  obtain ⟨σ, hσ, hσt⟩ := exists_prod_swaps hT hc
  obtain ⟨σ', hσ', hσt'⟩ := exists_prod_swaps hT' hc'
  obtain ⟨g, hg⟩ := isConj_iff.1 ((Equiv.Perm.isConj_iff_cycleType_eq (σ := σ) (τ := σ')).2
    (by rw [hσt, hσt', hcard, hcard']))
  refine ⟨g, ?_⟩
  have hmap := Equiv.Perm.cycleFactorsFinset_conj σ g
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, hg] at hmap
  unfold A1b.conjSub
  rw [MonoidHom.map_closure, ← hσ, ← hσ', hmap, Finset.coe_map]
  rfl

theorem isMaxSwapGroup_conjSub {Y : Subgroup (Equiv.Perm (Fin n))} (h : IsMaxSwapGroup Y)
    (g : Equiv.Perm (Fin n)) : IsMaxSwapGroup (A1b.conjSub g Y) :=
  isSwapGroupOfSize_conjSub h g

theorem exists_isMaxSwapGroup_le_of_isSylow (hn : Odd n) {P : Subgroup (Equiv.Perm (Fin n))}
    (hP : IsPGroup 2 P) (hidx : ¬ 2 ∣ P.index) : ∃ Y ≤ P, IsMaxSwapGroup Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, hs, hc, hcard⟩ := exists_isMaxSwapGroup_ge hn (T' := ∅) (by simp) (by simp)
  have hY : IsMaxSwapGroup (Subgroup.closure T) := ⟨T, hs, hc, hcard, rfl⟩
  have hY2 : IsPGroup 2 (Subgroup.closure T) := fun x => ⟨1, Subtype.ext (by
    simpa using sq_eq_one_of_mem_closure hs hc x.2)⟩
  let Q : Sylow 2 (Equiv.Perm (Fin n)) := hP.toSylow hidx
  obtain ⟨Q', hQ'⟩ := hY2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin n)) Q' Q
  refine ⟨A1b.conjSub g (Subgroup.closure T), ?_, isMaxSwapGroup_conjSub hY g⟩
  intro y hy
  rw [A1b.mem_conjSub_iff] at hy
  have h1 : g⁻¹ * y * g ∈ (Q' : Subgroup (Equiv.Perm (Fin n))) := hQ' hy
  have h2 : y ∈ MulAut.conj g • (Q' : Subgroup (Equiv.Perm (Fin n))) := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def] using h1
  rw [← Sylow.coe_subgroup_smul, hg] at h2
  exact h2

theorem isSwapGroupOfSize_closure_finset {TM : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ TM, t.IsSwap)
    (hc : ∀ t ∈ TM, ∀ t' ∈ TM, t * t' = t' * t) {S : Finset (Equiv.Perm (Fin n))}
    (hS : (S : Set (Equiv.Perm (Fin n))) ⊆ TM) :
    IsSwapGroupOfSize (Subgroup.closure (S : Set (Equiv.Perm (Fin n)))) S.card :=
  ⟨S, fun t ht => hs t (hS ht), fun t ht t' ht' => hc t (hS ht) t' (hS ht'),
    Set.ncard_coe_finset S, rfl⟩

theorem swap_rank_eq_of_unique_conj (hn : Odd n) {B P : Subgroup (Equiv.Perm (Fin n))} {k : ℕ}
    (hB : IsSwapGroupOfSize B k) (hk : 1 ≤ k) (hP : ∃ Y ≤ P, IsMaxSwapGroup Y)
    (hstar : ∀ π : Equiv.Perm (Fin n), A1b.conjSub π B ≤ P → A1b.conjSub π B = B) :
    k = (n - 1) / 2 := by
  classical
  obtain ⟨Y, hYP, TM, hsM, hcM, hcardM, rfl⟩ := hP
  have hkle : k ≤ (n - 1) / 2 := by
    obtain ⟨TB, hsB, hcB, hcardB, -⟩ := hB
    have := two_mul_ncard_le hsB hcB
    obtain ⟨j, hj⟩ := hn
    omega
  by_contra hne
  have hlt : k < (n - 1) / 2 := lt_of_le_of_ne hkle hne
  have hfinM : TM.Finite := Set.toFinite TM
  set Mf := hfinM.toFinset with hMf
  have hMcard : Mf.card = (n - 1) / 2 := by
    rw [← hcardM, Set.ncard_eq_toFinset_card TM hfinM]
  have hMsub : ∀ S : Finset (Equiv.Perm (Fin n)), S ⊆ Mf → (S : Set (Equiv.Perm (Fin n))) ⊆ TM :=
    fun S hS t ht => hfinM.mem_toFinset.1 (hS ht)
  obtain ⟨T1, hT1M, hT1c⟩ := Finset.exists_subset_card_eq (show k ≤ Mf.card by omega)
  obtain ⟨sx, hsx⟩ : T1.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨sy, hsyM, hsyT1⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := T1) (t := Mf) (by omega)
  set T2 : Finset (Equiv.Perm (Fin n)) := insert sy (T1.erase sx) with hT2
  have hT2M : T2 ⊆ Mf := by
    intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hsyM
    · exact hT1M (Finset.mem_of_mem_erase ht)
  have hT2c : T2.card = k := by
    rw [hT2, Finset.card_insert_of_notMem (fun h => hsyT1 (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hsx, hT1c]
    omega
  have hsxM : sx ∈ TM := hfinM.mem_toFinset.1 (hT1M hsx)
  have hsxT2 : sx ∉ T2 := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact hsyT1 (h ▸ hsx)
    · exact (Finset.notMem_erase sx T1) h
  have hconj : ∀ S : Finset (Equiv.Perm (Fin n)), S ⊆ Mf → S.card = k →
      Subgroup.closure (S : Set (Equiv.Perm (Fin n))) = B := by
    intro S hS hSc
    have h1 := isSwapGroupOfSize_closure_finset hsM hcM (hMsub S hS)
    rw [hSc] at h1
    obtain ⟨π, hπ⟩ := exists_conjSub_eq_of_isSwapGroupOfSize hB h1
    have hle : Subgroup.closure (S : Set (Equiv.Perm (Fin n))) ≤ P :=
      (Subgroup.closure_mono (hMsub S hS)).trans hYP
    rw [← hπ] at hle
    rw [← hπ]
    exact hstar π hle
  have h12 : Subgroup.closure (T1 : Set (Equiv.Perm (Fin n))) =
      Subgroup.closure (T2 : Set (Equiv.Perm (Fin n))) :=
    (hconj T1 hT1M hT1c).trans (hconj T2 hT2M hT2c).symm
  obtain ⟨a, b, hab, hsxeq⟩ := hsM sx hsxM
  have hmov : sx a ≠ a := by
    rw [hsxeq, Equiv.swap_apply_left]
    exact fun h => hab h.symm
  have hfix : ∀ t ∈ (T2 : Set (Equiv.Perm (Fin n))), t a = a := by
    intro t ht
    have htM : t ∈ TM := hMsub T2 hT2M ht
    have hne' : sx ≠ t := fun h => hsxT2 (h ▸ ht)
    exact apply_eq_of_commute_swap (hsM sx hsxM) (hsM t htM) (hcM sx hsxM t htM) hne' hmov
  have hsxcl : sx ∈ Subgroup.closure (T2 : Set (Equiv.Perm (Fin n))) :=
    h12 ▸ Subgroup.subset_closure (Finset.mem_coe.2 hsx)
  exact hmov (apply_eq_of_mem_closure hfix hsxcl)

end CFSG.CGT.PushingUpLit.BHS7
