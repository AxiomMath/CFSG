module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem aePerm_ge_nine (hn : 9 ≤ n) : TwinThinPf8.AEPerm n := by
  classical
  intro α hα w ⟨a, hA⟩ hB
  right
  have hn8 : n ≠ 8 := by omega
  have hB' : ∀ c : Bool, ∀ x ∈ memBar α hα c, mkQ n w * x * (mkQ n w)⁻¹ = x :=
    fun c x hx => hB α hα c (Or.inr rfl) x hx
  obtain ⟨c, e, hw, he, hc⟩ := exists_split (by omega) hn8 α hα w hB'
  have hep : e.perm = 1 := by
    rcases he with rfl | rfl
    · rfl
    · exact zOf_perm _
  have hwp : w.perm = c.perm := by rw [hw, mul_perm, hep, mul_one]
  have hwS : ∀ x, x ∈ Set.range (emb α hα) → w.perm x = x := fun x hx => by
    rw [hwp]; exact (hc x (by simpa using hx)).2
  have hrange : ∀ x, x ∈ Set.range (emb α hα) ↔ x ∈ α := fun x => by
    rw [range_emb]; exact Finset.mem_coe
  have hTcard : (αᶜ).card = n - 4 := by rw [Finset.card_compl, Fintype.card_fin, hα]
  have hTfix : ∀ x ∈ αᶜ, w.perm x = x := by
    intro x hx
    have hxT : x ∈ αᶜ := hx
    have hσT : ∀ y, y ∈ αᶜ → w.perm y ∈ αᶜ := by
      intro y hy
      rw [Finset.mem_compl] at hy ⊢
      intro hσ
      have := hwS _ ((hrange _).mpr hσ)
      have h2 := w.perm.injective this
      rw [← h2] at hy
      exact hy hσ
    have hnot : ∀ y ∈ αᶜ, y ≠ x → w.perm x ≠ y := by
      intro y hy hyx hσ
      have hS : 3 ≤ (((αᶜ).erase y).erase x).card := by
        rw [Finset.card_erase_of_mem (by simp [hxT, Ne.symm hyx]), Finset.card_erase_of_mem hy, hTcard]
        omega
      obtain ⟨B3, hB3, hB3c⟩ := Finset.exists_subset_card_eq hS
      have hxB3 : x ∉ B3 := fun h => by simpa using hB3 h
      have hβc : (insert x B3).card = 4 := by rw [Finset.card_insert_of_notMem hxB3, hB3c]
      have hβT : ∀ z ∈ insert x B3, z ∈ αᶜ := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact hxT
        · have := hB3 hz
          simp only [Finset.mem_erase] at this
          exact this.2.2
      have hyβ : y ∉ insert x B3 := by
        intro h
        rw [Finset.mem_insert] at h
        rcases h with rfl | h
        · exact hyx rfl
        · have := hB3 h
          simp at this
      have hdisj : Disjoint α (insert x B3) := by
        rw [Finset.disjoint_left]
        intro z hzα hzβ
        exact (Finset.mem_compl.mp (hβT z hzβ)) hzα
      have hBβ : ∀ cb : Bool, ∀ t ∈ memBar (insert x B3) hβc cb,
          mkQ n w * t * (mkQ n w)⁻¹ = t := fun cb t ht => hB _ hβc cb (Or.inl hdisj) t ht
      have hz := hBβ true (zBar (insert x B3) hβc) (zBar_mem_memBar _ hβc true)
      have hz' : mkQ n (w * zOf (emb (insert x B3) hβc) * w⁻¹) =
          mkQ n (zOf (emb (insert x B3) hβc)) := by
        have hz0 : mkQ n w * mkQ n (zOf (emb (insert x B3) hβc)) * (mkQ n w)⁻¹ =
            mkQ n (zOf (emb (insert x B3) hβc)) := hz
        simpa only [map_mul, map_inv] using hz0
      have hp := perm_range_of_conj hn8 (emb (insert x B3) hβc) w hz'
      have hxr : x ∈ Set.range (emb (insert x B3) hβc) := by
        rw [range_emb]; exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
      have := (hp x).mp hxr
      rw [hσ, range_emb] at this
      exact hyβ (Finset.mem_coe.mp this)
    by_contra hne
    exact hnot (w.perm x) (hσT x hxT) hne rfl
  have hw1 : w.perm = 1 := by
    refine Equiv.ext fun x => ?_
    by_cases hx : x ∈ α
    · exact hwS x ((hrange x).mpr hx)
    · exact hTfix x (Finset.mem_compl.mpr hx)
  have hw2 : w ^ 2 = 1 := by
    rw [sq]
    refine Wr.ext (funext fun t => ?_) (by rw [mul_perm, hw1]; rfl)
    show w.vec t + w.vec (w.perm.symm t) = 0
    have : w.perm.symm t = t := by rw [hw1]; rfl
    rw [this]
    exact zmod_two_add_self _
  have hpow : w ^ 3 ^ a = w := by
    rw [pow_eq_pow_mod _ hw2]
    have : 3 ^ a % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
    rw [this, pow_one]
  intro t ht
  have := hA t ht
  rwa [hpow] at this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
