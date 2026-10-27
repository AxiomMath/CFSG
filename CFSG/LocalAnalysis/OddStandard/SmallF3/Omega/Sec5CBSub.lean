module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CDVec

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv

theorem sec5cb_alt_two_trans {i j a b : Fin 6} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ ∈ alternatingGroup (Fin 6), σ i = a ∧ σ j = b := by
  have h4 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 4 := by
    have h := alternatingGroup.isMultiplyPretransitive (Fin 6)
    simpa using h
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 6)) (Fin 6) 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := alternatingGroup (Fin 6)) (α := Fin 6)
      (m := 2) (n := 4) (by norm_num) (by simp)
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp h2) hij hab
  exact ⟨g, g.2, hg1, hg2⟩

theorem sec5cb_alt_trans (j k : Fin 6) : ∃ σ ∈ alternatingGroup (Fin 6), σ j = k := by
  obtain ⟨j', hj'⟩ : ∃ j' : Fin 6, j' ≠ j := by
    by_cases h : j = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h0 => h h0.symm⟩
  obtain ⟨k', hk'⟩ : ∃ k' : Fin 6, k' ≠ k := by
    by_cases h : k = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h0 => h h0.symm⟩
  obtain ⟨σ, hσ, h1, -⟩ := sec5cb_alt_two_trans (Ne.symm hj') (Ne.symm hk')
  exact ⟨σ, hσ, h1⟩

theorem sec5cb_inv_all (W : AddSubmonoid (Fin 6 → ZMod 2))
    (hW : ∀ σ ∈ alternatingGroup (Fin 6), ∀ v ∈ W, permVec σ v ∈ W) {j : Fin 6}
    (hj : (Pi.single j 1 : Fin 6 → ZMod 2) ∈ W) (v : Fin 6 → ZMod 2) : v ∈ W := by
  have hk : ∀ k : Fin 6, (Pi.single k 1 : Fin 6 → ZMod 2) ∈ W := by
    intro k
    obtain ⟨σ, hσ, hσj⟩ := sec5cb_alt_trans j k
    have := hW σ hσ _ hj
    rwa [sec5c_permVec_single, hσj] at this
  have hv : v = ∑ k, (Pi.single k (v k) : Fin 6 → ZMod 2) := by
    simpa using (Finset.univ_sum_single v).symm
  rw [hv]
  refine AddSubmonoid.sum_mem W fun k _ => ?_
  by_cases h0 : v k = 0
  · rw [h0]
    simp only [Pi.single_zero]
    exact W.zero_mem
  · have h1 : v k = 1 := by
      generalize v k = a at h0
      revert a
      decide
    rw [h1]
    exact hk k

theorem sec5cb_pairs_sum :
    ((Pi.single 0 1 + Pi.single 1 1) + (Pi.single 2 1 + Pi.single 3 1) +
      (Pi.single 4 1 + Pi.single 5 1) : Fin 6 → ZMod 2) = fun _ => 1 := by
  funext x
  fin_cases x <;> simp [Pi.single_apply]

theorem sec5cb_inv_ones_of_pair (W : AddSubmonoid (Fin 6 → ZMod 2))
    (hW : ∀ σ ∈ alternatingGroup (Fin 6), ∀ v ∈ W, permVec σ v ∈ W) {i j : Fin 6} (hij : i ≠ j)
    (h : (Pi.single i 1 + Pi.single j 1 : Fin 6 → ZMod 2) ∈ W) :
    (fun _ => (1 : ZMod 2)) ∈ W := by
  have hp : ∀ a b : Fin 6, a ≠ b →
      (Pi.single a 1 + Pi.single b 1 : Fin 6 → ZMod 2) ∈ W := by
    intro a b hab
    obtain ⟨σ, hσ, h1, h2⟩ := sec5cb_alt_two_trans hij hab
    have := hW σ hσ _ h
    rwa [sec5c_permVec_add, sec5c_permVec_single, sec5c_permVec_single, h1, h2] at this
  rw [← sec5cb_pairs_sum]
  exact W.add_mem (W.add_mem (hp 0 1 (by decide)) (hp 2 3 (by decide))) (hp 4 5 (by decide))

theorem sec5cb_add_swap {v : Fin 6 → ZMod 2} {i j k l : Fin 6} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (hv : v i ≠ v j) (hvkl : v k = v l) :
    v + permVec (swap i j * swap k l) v = Pi.single i 1 + Pi.single j 1 := by
  have hsum : ∀ a b : ZMod 2, a ≠ b → a + b = 1 := by decide
  have hsame : ∀ a b : ZMod 2, a = b → a + b = 0 := by decide
  have hs : ∀ x, (swap i j * swap k l).symm x = swap k l (swap i j x) := by
    intro x
    simp [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  funext x
  simp only [Pi.add_apply, permVec, Function.comp_apply, hs]
  by_cases hxi : x = i
  · subst hxi
    rw [swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hkj) (Ne.symm hlj), hsum _ _ hv]
    simp [Pi.single_apply, hij]
  by_cases hxj : x = j
  · subst hxj
    rw [swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hki) (Ne.symm hli),
      add_comm, hsum _ _ hv]
    simp [Pi.single_apply, Ne.symm hij]
  rw [swap_apply_of_ne_of_ne hxi hxj]
  by_cases hxk : x = k
  · subst hxk
    rw [swap_apply_left, ← hvkl, hsame _ _ rfl]
    simp [Pi.single_apply, hxi, hxj]
  by_cases hxl : x = l
  · subst hxl
    rw [swap_apply_right, hvkl, hsame _ _ rfl]
    simp [Pi.single_apply, hxi, hxj]
  rw [swap_apply_of_ne_of_ne hxk hxl, hsame _ _ rfl]
  simp [Pi.single_apply, hxi, hxj]

theorem sec5cb_inv_ones (W : AddSubmonoid (Fin 6 → ZMod 2))
    (hW : ∀ σ ∈ alternatingGroup (Fin 6), ∀ v ∈ W, permVec σ v ∈ W) {v : Fin 6 → ZMod 2}
    (hv : v ∈ W) (hv0 : v ≠ 0) : (fun _ => (1 : ZMod 2)) ∈ W := by
  by_cases hconst : ∀ i j, v i = v j
  · have hone : v = fun _ => 1 := by
      funext x
      by_contra hx
      apply hv0
      funext y
      have h1 : v x = 0 := by
        generalize v x = a at hx ⊢
        revert a
        decide
      rw [hconst x y] at h1
      simpa using h1
    rw [← hone]
    exact hv
  · push Not at hconst
    obtain ⟨i, j, hij⟩ := hconst
    have hne : i ≠ j := fun h => hij (by rw [h])
    have hjm : j ∈ (Finset.univ : Finset (Fin 6)).erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ _⟩
    have hTcard : ((Finset.univ.erase i).erase j : Finset (Fin 6)).card = 4 := by
      rw [Finset.card_erase_of_mem hjm, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
    obtain ⟨k, hk, l, hl, hkl, hvkl⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := (Finset.univ.erase i).erase j) (t := (Finset.univ : Finset (ZMod 2))) (f := v)
        (by rw [hTcard]; decide) (fun _ _ => Finset.mem_univ _)
    obtain ⟨hkj, hk'⟩ := Finset.mem_erase.mp hk
    obtain ⟨hki, -⟩ := Finset.mem_erase.mp hk'
    obtain ⟨hlj, hl'⟩ := Finset.mem_erase.mp hl
    obtain ⟨hli, -⟩ := Finset.mem_erase.mp hl'
    have hσ : swap i j * swap k l ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne,
        Equiv.Perm.sign_swap hkl]
      decide
    have hsum := W.add_mem hv (hW _ hσ v hv)
    rw [sec5cb_add_swap hne hki hkj hli hlj hij hvkl] at hsum
    exact sec5cb_inv_ones_of_pair W hW hne hsum

variable {G : Type} [Group G]

theorem sec5cb_phi_zero {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6))) :
    φ 0 = 1 := by
  have h := hφ.1 0 0 trivial trivial
  rw [add_zero] at h
  exact mul_left_cancel (a := φ 0) (by rw [mul_one]; exact h.symm)

theorem sec5cb_exists_W {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6)))
    {B' : Subgroup G} (hinv : ∀ h ∈ H, ∀ b ∈ B', h * b * h⁻¹ ∈ B') :
    ∃ W : AddSubmonoid (Fin 6 → ZMod 2), (∀ v, v ∈ W ↔ φ v ∈ B') ∧
      ∀ σ ∈ alternatingGroup (Fin 6), ∀ v ∈ W, permVec σ v ∈ W := by
  have h0 := sec5cb_phi_zero hφ
  obtain ⟨hadd, -, -, -, hreal⟩ := hφ
  refine ⟨{ carrier := {v | φ v ∈ B'}
            zero_mem' := by
              show φ 0 ∈ B'
              rw [h0]
              exact B'.one_mem
            add_mem' := fun {v w} hv hw => by
              show φ (v + w) ∈ B'
              rw [hadd v w trivial trivial]
              exact B'.mul_mem hv hw }, fun v => Iff.rfl, ?_⟩
  intro σ hσ v hv
  obtain ⟨h, hh, hform⟩ := hreal σ hσ
  show φ (permVec σ v) ∈ B'
  rw [← hform v trivial]
  exact hinv h hh _ hv

theorem sec5cb_ones_mem {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6)))
    {B' : Subgroup G} (hinv : ∀ h ∈ H, ∀ b ∈ B', h * b * h⁻¹ ∈ B') {v : Fin 6 → ZMod 2}
    (hv0 : v ≠ 0) (hv : φ v ∈ B') : φ (fun _ => 1) ∈ B' := by
  obtain ⟨W, hW, hWinv⟩ := sec5cb_exists_W hφ hinv
  exact (hW _).mp (sec5cb_inv_ones W hWinv ((hW v).mpr hv) hv0)

theorem sec5cb_le_of_single {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6)))
    {B' : Subgroup G} (hinv : ∀ h ∈ H, ∀ b ∈ B', h * b * h⁻¹ ∈ B') {j : Fin 6}
    (hj : φ (Pi.single j 1) ∈ B') : E ≤ B' := by
  obtain ⟨W, hW, hWinv⟩ := sec5cb_exists_W hφ hinv
  intro x hx
  obtain ⟨v, -, rfl⟩ := (hφ.2.2.1 x).mp hx
  exact (hW v).mp (sec5cb_inv_all W hWinv ((hW _).mpr hj) v)

theorem sec5cb_eq_bot {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6)))
    {B' : Subgroup G} (hB'E : B' ≤ E) (hv : ∀ v, φ v ∈ B' → v = 0) : B' = ⊥ := by
  have h0 := sec5cb_phi_zero hφ
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨v, -, rfl⟩ := (hφ.2.2.1 x).mp (hB'E hx)
  rw [hv v hx, h0]

end CFSG.OddStandard.SmallF3.Omega
