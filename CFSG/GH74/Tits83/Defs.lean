module

public import CFSG.GH74.BNPair.Defs
import CFSG.GH74.BNPair.ChainProdFun

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

universe u

@[expose] def win {G : Type u} [Group G] (U : ℤ → Subgroup G) (a b : ℤ) : Subgroup G :=
  ⨆ k ∈ Set.Icc a b, U k

structure TitsSystem (G : Type u) [Group G] (n : ℕ) where
  U : ℤ → Subgroup G
  periodic : ∀ i, U (i + 2 * (n : ℤ)) = U i
  ne_bot : ∀ i, U i ≠ ⊥
  comm : ∀ i j : ℤ, i < j → j < i + n → ∀ u ∈ U i, ∀ v ∈ U j,
    u * v * u⁻¹ * v⁻¹ ∈ ⨆ k ∈ Set.Ioo i j, U k
  unique : ∀ i : ℤ, ∀ f g : ℤ → G,
    (∀ k ∈ intList (i + 1) (i + n), f k ∈ U k) →
    (∀ k ∈ intList (i + 1) (i + n), g k ∈ U k) →
    ((intList (i + 1) (i + n)).map f).prod = ((intList (i + 1) (i + n)).map g).prod →
    ∀ k ∈ intList (i + 1) (i + n), f k = g k
  moufang : ∀ i : ℤ, ∀ u ∈ U i, u ≠ 1 → ∃ v ∈ U (i + n), ∃ w ∈ U (i + n),
    ∀ j : ℤ, (U j).map (MulAut.conj (v * u * w)).toMonoidHom = U (2 * i + n - j)

namespace TitsSystem

variable {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n)

@[expose] def shift (s : ℤ) : TitsSystem G n where
  U i := T.U (i + s)
  periodic i := by
    rw [show i + 2 * (n : ℤ) + s = (i + s) + 2 * (n : ℤ) by ring]
    exact T.periodic (i + s)
  ne_bot i := T.ne_bot (i + s)
  comm i j hij hji u hu v hv := by
    refine SetLike.le_def.mp (iSup₂_le fun k hk => ?_)
      (T.comm (i + s) (j + s) (by omega) (by omega) u hu v hv)
    have hk' : i + s < k ∧ k < j + s := hk
    exact le_iSup₂_of_le (k - s) ⟨by omega, by omega⟩
      (le_of_eq (by rw [sub_add_cancel]))
  unique i f g hf hg hprod k hk := by
    have hL : intList (i + s + 1) (i + s + n) =
        (intList (i + 1) (i + n)).map (fun k => k + s) := by
      simpa [add_assoc, add_comm, add_left_comm] using intList_add (i + 1) (i + n) s
    let F : ℤ → G := fun k => f (k - s)
    let G' : ℤ → G := fun k => g (k - s)
    have hF : ∀ k ∈ intList (i + s + 1) (i + s + n), F k ∈ T.U k := by
      intro k hk
      rw [hL, List.mem_map] at hk
      obtain ⟨t, ht, rfl⟩ := hk
      simpa [F, add_comm, add_left_comm, add_assoc] using hf t ht
    have hG : ∀ k ∈ intList (i + s + 1) (i + s + n), G' k ∈ T.U k := by
      intro k hk
      rw [hL, List.mem_map] at hk
      obtain ⟨t, ht, rfl⟩ := hk
      simpa [G', add_comm, add_left_comm, add_assoc] using hg t ht
    have hprod' : ((intList (i + s + 1) (i + s + n)).map F).prod =
        ((intList (i + 1) (i + n)).map f).prod := by
      rw [hL, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      simp [F, add_comm, add_left_comm, add_assoc]
    have hprod'' : ((intList (i + s + 1) (i + s + n)).map G').prod =
        ((intList (i + 1) (i + n)).map g).prod := by
      rw [hL, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      simp [G', add_comm, add_left_comm, add_assoc]
    have huniq := T.unique (i + s) F G' hF hG (by rw [hprod', hprod'', hprod])
    have hmem : k + s ∈ intList (i + s + 1) (i + s + n) := by
      rw [hL, List.mem_map]
      exact ⟨k, hk, by ring⟩
    have := huniq (k + s) hmem
    simpa [F, G'] using this
  moufang i u hu hu1 := by
    obtain ⟨v, hv, w, hw, hconj⟩ := T.moufang (i + s) u hu hu1
    refine ⟨v, ?_, w, ?_, fun j => ?_⟩
    · simpa [add_assoc, add_comm, add_left_comm] using hv
    · simpa [add_assoc, add_comm, add_left_comm] using hw
    · have h := hconj (j + s)
      simpa [show 2 * (i + s) + (n : ℤ) - (j + s) = 2 * i + n - j + s by ring]
        using h

@[expose] def refl (c : ℤ) : TitsSystem G n where
  U i := T.U (c - i)
  periodic i := by
    have h := T.periodic (c - i - 2 * (n : ℤ))
    rw [show c - i - 2 * (n : ℤ) + 2 * (n : ℤ) = c - i by ring] at h
    rw [show c - (i + 2 * (n : ℤ)) = c - i - 2 * (n : ℤ) by ring]
    exact h.symm
  ne_bot i := T.ne_bot (c - i)
  comm i j hij hji u hu v hv := by
    have h := T.comm (c - j) (c - i) (by omega) (by omega) v hv u hu
    have hinv : u * v * u⁻¹ * v⁻¹ ∈ (⨆ k ∈ Set.Ioo (c - j) (c - i), T.U k) := by
      have := (⨆ k ∈ Set.Ioo (c - j) (c - i), T.U k).inv_mem h
      simpa [commutatorElement_def, mul_assoc] using this
    refine SetLike.le_def.mp (iSup₂_le fun k hk => ?_) hinv
    have hk' : c - j < k ∧ k < c - i := hk
    exact le_iSup₂_of_le (c - k) ⟨by omega, by omega⟩
      (le_of_eq (by rw [sub_sub_cancel]))
  unique i f g hf hg hprod k hk := by
    have hL : intList (i + 1) (i + n) =
        ((intList (c - i - n) (c - i - 1)).map (fun k => c - k)).reverse := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        intList_map_sub (i + 1) (i + n) c
    let L := intList (c - i - n) (c - i - 1)
    let F : ℤ → G := fun k => (f (c - k))⁻¹
    let G' : ℤ → G := fun k => (g (c - k))⁻¹
    have hmem : ∀ k ∈ L, c - k ∈ intList (i + 1) (i + n) := by
      intro k hk
      rw [hL, List.mem_reverse, List.mem_map]
      exact ⟨k, hk, rfl⟩
    have hlist : intList ((c - i - n - 1) + 1) ((c - i - n - 1) + n) = L := by
      rw [show (c - i - n - 1) + 1 = c - i - n by ring,
        show (c - i - n - 1) + n = c - i - 1 by ring]
    have hF : ∀ k ∈ intList ((c - i - n - 1) + 1) ((c - i - n - 1) + n), F k ∈ T.U k := by
      intro k hk
      have hk' : k ∈ L := by rw [hlist] at hk; exact hk
      have := hf (c - k) (hmem k hk')
      have e : c - (c - k) = k := by ring
      exact (T.U k).inv_mem (by rwa [e] at this)
    have hG : ∀ k ∈ intList ((c - i - n - 1) + 1) ((c - i - n - 1) + n), G' k ∈ T.U k := by
      intro k hk
      have hk' : k ∈ L := by rw [hlist] at hk; exact hk
      have := hg (c - k) (hmem k hk')
      have e : c - (c - k) = k := by ring
      exact (T.U k).inv_mem (by rwa [e] at this)
    have hprod' : ((intList ((c - i - n - 1) + 1) ((c - i - n - 1) + n)).map F).prod =
        ((intList (i + 1) (i + n)).map f).prod⁻¹ := by
      rw [hlist]
      have hmain : ((intList (i + 1) (i + n)).map f).prod⁻¹ = (L.map F).prod := by
        rw [hL, List.map_reverse, List.map_map]
        rw [List.prod_reverse_noncomm]
        simp only [inv_inv, List.map_map]
        rfl
      exact hmain.symm
    have hprod'' : ((intList ((c - i - n - 1) + 1) ((c - i - n - 1) + n)).map G').prod =
        ((intList (i + 1) (i + n)).map g).prod⁻¹ := by
      rw [hlist]
      have hmain : ((intList (i + 1) (i + n)).map g).prod⁻¹ = (L.map G').prod := by
        rw [hL, List.map_reverse, List.map_map]
        rw [List.prod_reverse_noncomm]
        simp only [inv_inv, List.map_map]
        rfl
      exact hmain.symm
    have hprod_inv : ((intList (i + 1) (i + n)).map f).prod⁻¹ =
        ((intList (i + 1) (i + n)).map g).prod⁻¹ := by rw [hprod]
    have huniq := T.unique (c - i - n - 1) F G' hF hG
      (by rw [hprod', hprod'', hprod_inv])
    have hmemL : c - k ∈ L := by
      rw [hL, List.mem_reverse, List.mem_map] at hk
      obtain ⟨t, ht, htk⟩ := hk
      have : c - k = t := by rw [← htk]; ring
      rw [this]
      exact ht
    have := huniq (c - k) (by rw [hlist]; exact hmemL)
    have e : c - (c - k) = k := by ring
    simpa [F, G', e] using this
  moufang i u hu hu1 := by
    obtain ⟨v, hv, w, hw, hconj⟩ := T.moufang (c - i) u hu hu1
    have hv' : v ∈ T.U (c - (i + n)) := by
      have h := T.periodic (c - i - (n : ℤ))
      rw [show c - i - (n : ℤ) + 2 * (n : ℤ) = (c - i) + n by ring] at h
      have := h ▸ hv
      simpa [show c - (i + (n : ℤ)) = c - i - n by ring] using this
    have hw' : w ∈ T.U (c - (i + n)) := by
      have h := T.periodic (c - i - (n : ℤ))
      rw [show c - i - (n : ℤ) + 2 * (n : ℤ) = (c - i) + n by ring] at h
      have := h ▸ hw
      simpa [show c - (i + (n : ℤ)) = c - i - n by ring] using this
    refine ⟨v, hv', w, hw', fun j => ?_⟩
    have h := hconj (c - j)
    rw [show 2 * (c - i) + (n : ℤ) - (c - j) = c - (2 * i + n - j) + 2 * (n : ℤ) by ring]
      at h
    rwa [T.periodic] at h

end TitsSystem

theorem shift_U {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n) (s i : ℤ) :
    (T.shift s).U i = T.U (i + s) := rfl

theorem refl_U {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n) (c i : ℤ) :
    (T.refl c).U i = T.U (c - i) := rfl

attribute [irreducible] TitsSystem.shift TitsSystem.refl

theorem win_shift {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n) (s a b : ℤ) :
    win (T.shift s).U a b = win T.U (a + s) (b + s) := by
  simp only [win, shift_U]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (k + s) (by simp only [Set.mem_Icc] at hk ⊢; omega) le_rfl
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (k - s) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by rw [sub_add_cancel]))

theorem win_refl {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n) (c a b : ℤ) :
    win (T.refl c).U a b = win T.U (c - b) (c - a) := by
  simp only [win, refl_U]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (c - k) (by simp only [Set.mem_Icc] at hk ⊢; omega) le_rfl
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (c - k) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by rw [sub_sub_cancel]))

theorem U_add_two_mul {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n) (i k : ℤ) :
    T.U (i + 2 * (n : ℤ) * k) = T.U i := by
  have hnat : ∀ (j : ℤ) (m : ℕ), T.U (j + 2 * (n : ℤ) * (m : ℤ)) = T.U j := by
    intro j m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show j + 2 * (n : ℤ) * ((m + 1 : ℕ) : ℤ) =
        (j + 2 * (n : ℤ) * (m : ℤ)) + 2 * (n : ℤ) by push_cast; ring]
      rw [T.periodic, ih]
  rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
  · exact hnat i m
  · convert (hnat (i - 2 * (n : ℤ) * (m : ℤ)) m).symm using 2 <;> ring

end CFSG.GH74.Tits83
