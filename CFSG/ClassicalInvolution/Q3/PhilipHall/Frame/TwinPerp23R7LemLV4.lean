module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLPerm

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE

section Klein

@[expose] def v4List : List (Equiv.Perm (Fin 4)) := [1, d₁, d₂, d₃]

theorem v4_invol : ∀ δ ∈ v4List, ∀ i, δ (δ i) = i := by decide +kernel

theorem v4_fpf : ∀ δ ∈ v4List, δ ≠ 1 → ∀ i, δ i ≠ i := by decide +kernel

theorem v4_trans : ∀ i j : Fin 4, ∃ δ ∈ v4List, δ i = j := by decide +kernel

theorem v4_comm_fn : ∀ g : Fin 4 → Fin 4, (∀ δ ∈ v4List, ∀ i, g (δ i) = δ (g i)) →
    ∃ f ∈ v4List, ∀ i, g i = f i := by decide +kernel

theorem d₁_mem_v4List : d₁ ∈ v4List := by decide +kernel

end Klein

section CommV

variable {k : ℕ}

@[expose] def CommV (σ : Equiv.Perm (Fin k)) (ι : Fin 4 ↪ Fin k) : Prop :=
  ∀ δ ∈ v4List, σ * embedPerm ι δ = embedPerm ι δ * σ

theorem CommV.apply {σ : Equiv.Perm (Fin k)} {ι : Fin 4 ↪ Fin k} (h : CommV σ ι)
    {δ : Equiv.Perm (Fin 4)} (hδ : δ ∈ v4List) (x : Fin k) :
    σ (embedPerm ι δ x) = embedPerm ι δ (σ x) :=
  congrArg (fun p : Equiv.Perm (Fin k) => p x) (h δ hδ)

theorem CommV.exists_map {σ : Equiv.Perm (Fin k)} {ι : Fin 4 ↪ Fin k} (h : CommV σ ι) :
    ∃ f ∈ v4List, ∀ i, σ (ι i) = ι (f i) := by
  have h1 : ∀ i, ∃ j, σ (ι i) = ι j := by
    intro i
    by_contra hcon
    have hnot : σ (ι i) ∉ Set.range ι := fun ⟨j, hj⟩ => hcon ⟨j, hj.symm⟩
    have hD : embedPerm ι d₁ (σ (ι i)) = σ (ι i) := embedPerm_of_not_mem ι d₁ hnot
    have h2 := h.apply d₁_mem_v4List (ι i)
    rw [embedPerm_apply, hD] at h2
    have h3 : ι (d₁ i) = ι i := σ.injective h2
    exact v4_fpf d₁ d₁_mem_v4List (by decide +kernel) i (ι.injective h3)
  choose g hg using h1
  have hcomm : ∀ δ ∈ v4List, ∀ i, g (δ i) = δ (g i) := by
    intro δ hδ i
    have h2 := h.apply hδ (ι i)
    rw [embedPerm_apply, hg (δ i), hg i, embedPerm_apply] at h2
    exact ι.injective h2
  obtain ⟨f, hf, hfg⟩ := v4_comm_fn g hcomm
  exact ⟨f, hf, fun i => by rw [hg, hfg]⟩

theorem CommV.mem_iff {σ : Equiv.Perm (Fin k)} {ι : Fin 4 ↪ Fin k} (h : CommV σ ι) (x : Fin k) :
    σ x ∈ Finset.univ.map ι ↔ x ∈ Finset.univ.map ι := by
  obtain ⟨f, hf, hσ⟩ := h.exists_map
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨f j, σ.injective ?_⟩
    rw [hσ, v4_invol f hf j]
    exact hj
  · rintro ⟨i, rfl⟩
    exact ⟨f i, (hσ i).symm⟩

theorem CommV.fix_or {σ : Equiv.Perm (Fin k)} {ι : Fin 4 ↪ Fin k} (h : CommV σ ι) :
    (∀ x ∈ Finset.univ.map ι, σ x = x) ∨
      ∀ x ∈ Finset.univ.map ι, σ x ≠ x ∧ σ (σ x) = x := by
  obtain ⟨f, hf, hσ⟩ := h.exists_map
  by_cases h1 : f = 1
  · left
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    rw [hσ, h1]
    rfl
  · right
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    refine ⟨?_, ?_⟩
    · rw [hσ]
      exact fun h2 => v4_fpf f hf h1 i (ι.injective h2)
    · rw [hσ, hσ, v4_invol f hf i]

theorem even_card_of_involution (σ : Equiv.Perm (Fin k)) (U : Finset (Fin k))
    (hmem : ∀ x ∈ U, σ x ∈ U) (hfp : ∀ x ∈ U, σ x ≠ x) (hinv : ∀ x ∈ U, σ (σ x) = x) :
    Even U.card := by
  have h := Finset.sum_involution (s := U) (f := fun _ => (1 : ZMod 2)) (fun a _ => σ a)
    (fun a _ => by decide) (fun a ha _ => hfp a ha) (fun a ha => hmem a ha)
    (fun a ha => hinv a ha)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (ZMod.natCast_eq_zero_iff_even).mp h

theorem false_of_commV_pair (hk7 : k ≤ 7) {σ : Equiv.Perm (Fin k)} (hs : Equiv.Perm.sign σ = 1)
    (h1 : σ ≠ 1) {ι ι' : Fin 4 ↪ Fin k} (hι : CommV σ ι) (hι' : CommV σ ι')
    (hne : Finset.univ.map ι ≠ Finset.univ.map ι') : False := by
  set R := Finset.univ.map ι with hR
  set R' := Finset.univ.map ι' with hR'
  have hRc : R.card = 4 := by simp [hR]
  have hR'c : R'.card = 4 := by simp [hR']
  have hUk : (R ∪ R').card ≤ k := by
    calc (R ∪ R').card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
      _ = k := by simp
  have hU4 : 5 ≤ (R ∪ R').card := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have e1 : R = R ∪ R' := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
    have e2 : R' = R ∪ R' := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
    exact hne (e1.trans e2.symm)
  have hint : (R ∩ R').Nonempty := by
    have := Finset.card_union_add_card_inter R R'
    rw [← Finset.card_pos]
    omega
  rcases hι.fix_or with hfx | hfp <;> rcases hι'.fix_or with hfx' | hfp'
  · have hsupp : σ.support ⊆ (R ∪ R')ᶜ := by
      intro x hx
      rw [Equiv.Perm.mem_support] at hx
      rw [Finset.mem_compl, Finset.mem_union]
      rintro (hx1 | hx1)
      · exact hx (hfx x hx1)
      · exact hx (hfx' x hx1)
    have hc : σ.support.card ≤ 2 := by
      calc σ.support.card ≤ ((R ∪ R')ᶜ).card := Finset.card_le_card hsupp
        _ = k - (R ∪ R').card := by rw [Finset.card_compl, Fintype.card_fin]
        _ ≤ 2 := by omega
    exact h1 (eq_one_of_sign_one_of_card_support_le_two hs hc)
  · obtain ⟨x, hx⟩ := hint
    exact (hfp' x (Finset.mem_inter.mp hx).2).1 (hfx x (Finset.mem_inter.mp hx).1)
  · obtain ⟨x, hx⟩ := hint
    exact (hfp x (Finset.mem_inter.mp hx).1).1 (hfx' x (Finset.mem_inter.mp hx).2)
  · have hmemU : ∀ x ∈ R ∪ R', σ x ∈ R ∪ R' := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ ((hι.mem_iff x).mpr hx)
      · exact Finset.mem_union_right _ ((hι'.mem_iff x).mpr hx)
    have hfpU : ∀ x ∈ R ∪ R', σ x ≠ x := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (hfp x hx).1
      · exact (hfp' x hx).1
    have hinvU : ∀ x ∈ R ∪ R', σ (σ x) = x := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (hfp x hx).2
      · exact (hfp' x hx).2
    have hev := even_card_of_involution σ (R ∪ R') hmemU hfpU hinvU
    have h6 : (R ∪ R').card = 6 := by
      obtain ⟨m, hm⟩ := hev
      omega
    have hout : ∀ x, x ∉ R ∪ R' → σ x ∉ R ∪ R' := by
      intro x hx hσx
      apply hx
      have h' : σ (σ x) = x := σ.injective (hinvU _ hσx)
      rw [← h']
      exact hmemU _ hσx
    have hC : ((R ∪ R')ᶜ).card ≤ 1 := by
      rw [Finset.card_compl, Fintype.card_fin, h6]
      omega
    have hfixC : ∀ x, x ∉ R ∪ R' → σ x = x := fun x hx =>
      Finset.card_le_one.mp hC _ (Finset.mem_compl.mpr (hout x hx)) _ (Finset.mem_compl.mpr hx)
    have hσ2 : σ ^ 2 = 1 := by
      refine Equiv.ext fun x => ?_
      rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      by_cases hx : x ∈ R ∪ R'
      · exact hinvU x hx
      · rw [hfixC x hx, hfixC x hx]
    have hsupp : σ.support = R ∪ R' := by
      refine Finset.ext fun x => ?_
      rw [Equiv.Perm.mem_support]
      constructor
      · intro hx
        by_contra hxU
        exact hx (hfixC x hxU)
      · exact fun hx => hfpU x hx
    exact false_of_pow_two_support_six hσ2 (by rw [hsupp]; exact h6) hs

end CommV

section KeyLemma

open Equiv in
theorem swap_mul_swap_mem_closure_odd {n : ℕ} (Q : Subgroup (Equiv.Perm (Fin n))) {p q r s e : Fin n}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hrs : r ≠ s)
    (h1 : swap p q * swap s e ∈ Q) (h2 : swap s e * swap p r ∈ Q)
    (h3 : swap p r * swap q e ∈ Q) (h4 : swap q e * swap r s ∈ Q) :
    swap p q * swap r s ∈ Subgroup.closure {y : Equiv.Perm (Fin n) | y ∈ Q ∧ Odd (orderOf y)} := by
  have c1 : Equiv.Perm.IsThreeCycle (swap p q * swap p r) :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hpq hpr hqr
  have c2 : Equiv.Perm.IsThreeCycle (swap r p * swap r s) :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hpr.symm hrs hps
  have y1 : swap p q * swap p r ∈
      Subgroup.closure {y : Equiv.Perm (Fin n) | y ∈ Q ∧ Odd (orderOf y)} := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · have : swap p q * swap p r = (swap p q * swap s e) * (swap s e * swap p r) := by
        rw [mul_assoc, ← mul_assoc (swap s e), swap_mul_self, one_mul]
      rw [this]
      exact Q.mul_mem h1 h2
    · rw [c1.orderOf]
      decide
  have y2 : swap r p * swap r s ∈
      Subgroup.closure {y : Equiv.Perm (Fin n) | y ∈ Q ∧ Odd (orderOf y)} := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · have : swap r p * swap r s = (swap p r * swap q e) * (swap q e * swap r s) := by
        rw [swap_comm r p, mul_assoc, ← mul_assoc (swap q e), swap_mul_self, one_mul]
      rw [this]
      exact Q.mul_mem h3 h4
    · rw [c2.orderOf]
      decide
  have : swap p q * swap r s = (swap p q * swap p r) * (swap r p * swap r s) := by
    rw [swap_comm r p, mul_assoc, ← mul_assoc (swap p r), swap_mul_self, one_mul]
  rw [this]
  exact Subgroup.mul_mem _ y1 y2

end KeyLemma

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
