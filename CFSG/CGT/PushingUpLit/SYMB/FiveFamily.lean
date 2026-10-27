module

public import CFSG.CGT.PushingUpLit.SYMB.BlockJoin

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}

@[expose] def triBlocks {n : ℕ} (G T : Subgroup Γ) (φ : ↥G →* Equiv.Perm (Fin n)) :
    Set (Subgroup Γ) :=
  {F | IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T ∧
    ∃ Ω : Finset (Fin n), Ω.card = 3 ∧ imgG G φ F = altOn Ω}

section Tri

variable {n : ℕ} {T' : Set (Equiv.Perm (Fin n))}

theorem card_triple {t : Equiv.Perm (Fin n)} {x c : Fin n}
    (h : SymTriple T' t x c) : ({x, t x, c} : Finset (Fin n)).card = 3 := by
  classical
  have hxy : x ≠ t x := h.moves.symm
  have hxc : x ≠ c := fun h' => h.moves (h' ▸ h.fixed t h.mem)
  have htc : t x ≠ c := fun h' => by
    have hxc' : x = c := t.injective (h'.trans (h.fixed t h.mem).symm)
    exact h.moves (h'.trans hxc'.symm)
  exact Finset.card_eq_three.2 ⟨x, t x, c, hxy, hxc, htc, rfl⟩

theorem stab_triple (hs : ∀ t ∈ T', t.IsSwap) (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
    {t : Equiv.Perm (Fin n)} {x c : Fin n} (h : SymTriple T' t x c) :
    ∀ s ∈ T', s ∈ setStab ({x, t x, c} : Finset (Fin n)) := by
  classical
  intro s hsT
  have e1 : t = Equiv.swap x (t x) := eq_swap_of_isSwap_apply_ne (hs t h.mem) h.moves
  by_cases hst : s = t
  · subst hst
    refine mem_setStab_of_support_subset fun y hy => ?_
    rw [e1, Equiv.Perm.support_swap h.moves.symm] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · refine mem_setStab_of_disjoint ?_
    have hd := disjoint_support_of_commute (hs s hsT) (hs t h.mem) (hc s hsT t h.mem) hst
    have hcs : c ∉ s.support := fun h' => (Equiv.Perm.mem_support.1 h') (h.fixed s hsT)
    rw [Finset.disjoint_left]
    intro y hy hyΩ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyΩ
    rw [e1, Equiv.Perm.support_swap h.moves.symm] at hd
    rcases hyΩ with rfl | rfl | rfl
    · exact Finset.disjoint_left.1 hd hy (by simp)
    · exact Finset.disjoint_left.1 hd hy (by simp)
    · exact hcs hy

end Tri

section Cover

variable {m : ℕ} {φ : ↥G →* Equiv.Perm (Fin (2 * m + 1))}
  {ψ : ↥V →* ↥(G6.coreMod (2 * m + 1))} {T' : Set (Equiv.Perm (Fin (2 * m + 1)))}

theorem exists_triBlock_cyc (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 2 ≤ m)
    (hih : IHFor G) {t : Equiv.Perm (Fin (2 * m + 1))} {x c : Fin (2 * m + 1)}
    (h : SymTriple T' t x c) : ∃ F ∈ triBlocks G T φ, cyc x (t x) c ∈ imgG G φ F := by
  classical
  have hcard := card_triple h
  have hxΩ : x ∈ ({x, t x, c} : Finset (Fin (2 * m + 1))) := by simp
  have htxΩ : t x ∈ ({x, t x, c} : Finset (Fin (2 * m + 1))) := by simp
  have hcΩ : c ∈ ({x, t x, c} : Finset (Fin (2 * m + 1))) := by simp
  have hsimple : IsSimpleGroup ↥(altOn ({x, t x, c} : Finset (Fin (2 * m + 1)))) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine isSimpleGroup_of_prime_card (p := 3) ?_
    rw [card_altOn (by omega), hcard]
    decide
  obtain ⟨F, hF, hFn, hFΩ⟩ := exists_block_altOn_of_simple S hih hsimple (by omega)
    (stab_triple S.swaps S.comm h) h.mem h.moves h.fixed hxΩ htxΩ hcΩ
  refine ⟨F, ⟨hF, hFn, _, hcard, hFΩ⟩, ?_⟩
  have hxc : x ≠ c := fun h' => h.moves (h' ▸ h.fixed t h.mem)
  have htc : t x ≠ c := fun h' => by
    have hxc' : x = c := t.injective (h'.trans (h.fixed t h.mem).symm)
    exact h.moves (h'.trans hxc'.symm)
  rw [hFΩ]
  exact cyc_mem_altOn hxΩ htxΩ hcΩ h.moves.symm hxc htc

theorem triBlocks_nonempty (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 2 ≤ m)
    (hih : IHFor G) : (triBlocks G T φ).Nonempty := by
  obtain ⟨t, ht⟩ := S.nonempty
  obtain ⟨c, hc⟩ := exists_fixed_of_swaps S.odd S.swaps S.comm
  obtain ⟨a, a', haa, hta⟩ := S.swaps t ht
  have hmov : t a ≠ a := by
    rw [hta, Equiv.swap_apply_left]
    exact haa.symm
  obtain ⟨F, hF, -⟩ := exists_triBlock_cyc S hm hih (⟨ht, hmov, hc⟩ : SymTriple T' t a c)
  exact ⟨F, hF⟩

theorem symJoin_triBlocks (S : SymSetting G T V (2 * m + 1) φ ψ T') (hm : 2 ≤ m)
    (hih : IHFor G) : SymJoin G T V φ ψ (sSup (triBlocks G T φ)) :=
  symJoin_of_blocks S (fun _ hF => ⟨hF.1, hF.2.1⟩)
    (fun _ _ _ h => exists_triBlock_cyc S hm hih h) (triBlocks_nonempty S hm hih)

end Cover

end CFSG.CGT.PushingUpLit.SYMB
