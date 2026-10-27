module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMThree

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup

section Distinct

variable {G : Type} [Group G]

private theorem eq_bot_of_inv_and_comm {W W' : Subgroup G} {t : G}
    (hW : Nat.card W = 3) (hinv : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹)
    (hcomm : ∀ w ∈ W', t * w = w * t) (hle : W ≤ W') : W = ⊥ := by
  refine le_bot_iff.mp ?_
  intro w hw
  have hweq : w = w⁻¹ := by
    have h1 : t * w * t⁻¹ = w := by rw [hcomm w (hle hw)]; group
    rw [hinv w hw] at h1
    exact h1.symm
  have hsq : w ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hweq]
    exact mul_inv_cancel w
  have hdvd2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hdvd3 : orderOf w ∣ 3 := by
    have := Subgroup.orderOf_dvd_natCard W hw
    rwa [hW] at this
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 2 3) hdvd2 hdvd3)

theorem IsE27InvConfig.W₁_ne_W₂ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : W₁ ≠ W₂ := by
  intro hW
  have hbot : W₁ = ⊥ :=
    eq_bot_of_inv_and_comm h.card₁ h.inv₁
      (fun w hw => h.comm₁ w (Subgroup.mem_sup_left hw)) (le_of_eq hW)
  have hcard := h.card₁
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem IsE27InvConfig.W₁_ne_W₃ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : W₁ ≠ W₃ := by
  intro hW
  have hbot : W₁ = ⊥ :=
    eq_bot_of_inv_and_comm h.card₁ h.inv₁
      (fun w hw => h.comm₁ w (Subgroup.mem_sup_right hw)) (le_of_eq hW)
  have hcard := h.card₁
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem IsE27InvConfig.W₂_ne_W₃ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (h : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) : W₂ ≠ W₃ := by
  intro hW
  have hbot : W₂ = ⊥ :=
    eq_bot_of_inv_and_comm h.card₂ h.inv₂
      (fun w hw => h.comm₂ w (Subgroup.mem_sup_right hw)) (le_of_eq hW)
  have hcard := h.card₂
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

end Distinct

section Conjugates

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem W_le_dV (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ≤ D.V ∧ D.W₂ ≤ D.V ∧ D.W₃ ≤ D.V := by
  refine ⟨?_, ?_, ?_⟩
  · rw [D.cfg.join]; exact le_sup_left.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right.trans le_sup_left
  · rw [D.cfg.join]; exact le_sup_right

private theorem W_le_blocks (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ≤ L₁ ∧ D.W₂ ≤ L₂ ∧ D.W₃ ≤ L₃ :=
  ⟨D.le₁.trans (D.le_inf₁.trans inf_le_right),
    D.le₂.trans (D.le_inf₂.trans inf_le_right),
    D.le₃.trans (D.le_inf₃.trans inf_le_right)⟩

private theorem map_conj_eq_of_le_block
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {U : Subgroup G} (hU : IsPGroup 3 U) {u : G} (hu : u ∈ U)
    {W L L' W' : Subgroup G}
    (hWU : W ≤ U) (hWL : W ≤ L) (hcardW : Nat.card W = 3)
    (hLmap : L.map (MulAut.conj u).toMonoidHom = L')
    (hL' : L' ∈ ({L₁, L₂, L₃} : Set (Subgroup G)))
    (hW'L' : W' ≤ L') (hW'U : W' ≤ U) (hcardW' : Nat.card W' = 3) :
    W.map (MulAut.conj u).toMonoidHom = W' := by
  have hL'weak : L' ∈ weakBlockSet M H := by
    rw [TwelveFiveData.weakBlockSet_eq hc.data]
    exact hL'
  refine TwelveSixKCtx.eq_of_le_block hc hL'weak hU ?_ hcardW' ?_ hW'L' ?_ hW'U
  · rw [Subgroup.card_map_of_injective (MulAut.conj u).injective, hcardW]
  · calc W.map (MulAut.conj u).toMonoidHom ≤ L.map (MulAut.conj u).toMonoidHom :=
        Subgroup.map_mono hWL
      _ = L' := hLmap
  · have hUmap : U.map (MulAut.conj u).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hu)
    exact (Subgroup.map_mono hWU).trans (le_of_eq hUmap)

private theorem W₁_map_conj_mem_other
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U) (hVU : D.V ≤ U) {u : G}
    (hu : u ∈ U) (huV : u ∉ D.V) :
    D.W₁.map (MulAut.conj u).toMonoidHom = D.W₂ ∨
      D.W₁.map (MulAut.conj u).toMonoidHom = D.W₃ := by
  obtain ⟨hW1dV, hW2dV, hW3dV⟩ := W_le_dV D
  obtain ⟨hW1L1, hW2L2, hW3L3⟩ := W_le_blocks D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hUM hu) (by simp : L₁ ∈ _)
  have hne := hc.map_conj_ne_of_not_mem D hn hUM hU hVU hu huV (by simp : L₁ ∈ _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact absurd h hne
  · left
    exact map_conj_eq_of_le_block hc hU hu (hW1dV.trans hVU) hW1L1 D.cfg.card₁ h
      (by simp) hW2L2 (hW2dV.trans hVU) D.cfg.card₂
  · right
    exact map_conj_eq_of_le_block hc hU hu (hW1dV.trans hVU) hW1L1 D.cfg.card₁ h
      (by simp) hW3L3 (hW3dV.trans hVU) D.cfg.card₃

private theorem W₂_map_conj_mem_other
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U) (hVU : D.V ≤ U) {u : G}
    (hu : u ∈ U) (huV : u ∉ D.V) :
    D.W₂.map (MulAut.conj u).toMonoidHom = D.W₁ ∨
      D.W₂.map (MulAut.conj u).toMonoidHom = D.W₃ := by
  obtain ⟨hW1dV, hW2dV, hW3dV⟩ := W_le_dV D
  obtain ⟨hW1L1, hW2L2, hW3L3⟩ := W_le_blocks D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hUM hu) (by simp : L₂ ∈ _)
  have hne := hc.map_conj_ne_of_not_mem D hn hUM hU hVU hu huV (by simp : L₂ ∈ _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · left
    exact map_conj_eq_of_le_block hc hU hu (hW2dV.trans hVU) hW2L2 D.cfg.card₂ h
      (by simp) hW1L1 (hW1dV.trans hVU) D.cfg.card₁
  · exact absurd h hne
  · right
    exact map_conj_eq_of_le_block hc hU hu (hW2dV.trans hVU) hW2L2 D.cfg.card₂ h
      (by simp) hW3L3 (hW3dV.trans hVU) D.cfg.card₃

private theorem W₃_map_conj_mem_other
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U) (hVU : D.V ≤ U) {u : G}
    (hu : u ∈ U) (huV : u ∉ D.V) :
    D.W₃.map (MulAut.conj u).toMonoidHom = D.W₁ ∨
      D.W₃.map (MulAut.conj u).toMonoidHom = D.W₂ := by
  obtain ⟨hW1dV, hW2dV, hW3dV⟩ := W_le_dV D
  obtain ⟨hW1L1, hW2L2, hW3L3⟩ := W_le_blocks D
  have hmem := TwelveFiveData.map_conj_mem hc.data (hUM hu) (by simp : L₃ ∈ _)
  have hne := hc.map_conj_ne_of_not_mem D hn hUM hU hVU hu huV (by simp : L₃ ∈ _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · left
    exact map_conj_eq_of_le_block hc hU hu (hW3dV.trans hVU) hW3L3 D.cfg.card₃ h
      (by simp) hW1L1 (hW1dV.trans hVU) D.cfg.card₁
  · right
    exact map_conj_eq_of_le_block hc hU hu (hW3dV.trans hVU) hW3L3 D.cfg.card₃ h
      (by simp) hW2L2 (hW2dV.trans hVU) D.cfg.card₂
  · exact absurd h hne

private theorem conj_mul_eq_comp (u : G) :
    (MulAut.conj (u * u)).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
  ext x
  change (u * u) * x * (u * u)⁻¹ = u * (u * x * u⁻¹) * u⁻¹
  group

theorem TwelveSixKCtx.exists_conj_eq_W₂_and_W₃
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hn : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1)
    {U : Subgroup G} (hUM : U ≤ M) (hU : IsPGroup 3 U) (hVU : D.V ≤ U) {u : G}
    (hu : u ∈ U) (huV : u ∉ D.V) :
    (∃ x ∈ U, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₂) ∧
      ∃ x ∈ U, D.W₁.map (MulAut.conj x).toMonoidHom = D.W₃ := by
  classical
  have hW1 := W₁_map_conj_mem_other hc D hn hUM hU hVU hu huV
  have hW2 := W₂_map_conj_mem_other hc D hn hUM hU hVU hu huV
  have hW3 := W₃_map_conj_mem_other hc D hn hUM hU hVU hu huV
  have hne12 := D.cfg.W₁_ne_W₂
  have hne13 := D.cfg.W₁_ne_W₃
  have hne23 := D.cfg.W₂_ne_W₃
  rcases hW1 with h12 | h13
  · refine ⟨⟨u, hu, h12⟩, ?_⟩
    rcases hW2 with h21 | h23
    · exfalso
      rcases hW3 with h31 | h32
      · exact hne23 ((Subgroup.map_injective (MulAut.conj u).injective
          (h31.trans h21.symm)).symm)
      · exact hne13 ((Subgroup.map_injective (MulAut.conj u).injective
          (h32.trans h12.symm)).symm)
    · have hsq : D.W₁.map (MulAut.conj (u * u)).toMonoidHom = D.W₃ := by
        rw [conj_mul_eq_comp u, ← Subgroup.map_map, h12, h23]
      exact ⟨u * u, U.mul_mem hu hu, hsq⟩
  · refine ⟨?_, ⟨u, hu, h13⟩⟩
    rcases hW3 with h31 | h32
    · exfalso
      rcases hW2 with h21 | h23
      · exact hne23 (Subgroup.map_injective (MulAut.conj u).injective (h21.trans h31.symm))
      · exact hne12 ((Subgroup.map_injective (MulAut.conj u).injective
          (h23.trans h13.symm)).symm)
    · have hsq : D.W₁.map (MulAut.conj (u * u)).toMonoidHom = D.W₂ := by
        rw [conj_mul_eq_comp u, ← Subgroup.map_map, h13, h32]
      exact ⟨u * u, U.mul_mem hu hu, hsq⟩

end Conjugates

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
