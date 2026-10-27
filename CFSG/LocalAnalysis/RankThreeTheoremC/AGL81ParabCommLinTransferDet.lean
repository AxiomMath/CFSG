module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
  CFSG.QuasithinUnique.Vol2Native.A312L

section Product

variable {K : Type*} [CommRing K] {n : ℕ} {I : Set ℕ}

theorem det_eq_prod_blkAt {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ c ∈ I, ∀ k l : Fin n, (l : ℕ) < c → c ≤ (k : ℕ) → M k l = 0) :
    M.det = ∏ a : Fin n, (blkAt a (linBlockLen n I a) (linBlockLen_le a) M).det := by
  classical
  have hle : ∀ r : Fin n, Nat.findGreatest (fun c => c = 0 ∨ c ∈ I) r < n := fun r =>
    lt_of_le_of_lt (Nat.findGreatest_le _) r.isLt
  let b : Fin n → Fin n := fun r => ⟨Nat.findGreatest (fun c => c = 0 ∨ c ∈ I) r, hle r⟩
  have hbP : ∀ r : Fin n, (b r : ℕ) = 0 ∨ (b r : ℕ) ∈ I := fun r =>
    Nat.findGreatest_spec (P := fun c => c = 0 ∨ c ∈ I) (Nat.zero_le _) (Or.inl rfl)
  have hbr : ∀ r : Fin n, (b r : ℕ) ≤ r := fun r => Nat.findGreatest_le _
  have hge : ∀ (c : ℕ) (r : Fin n), (c = 0 ∨ c ∈ I) → c ≤ (r : ℕ) → c ≤ (b r : ℕ) :=
    fun c r hc hcr => Nat.le_findGreatest hcr hc
  have hfib : ∀ c r : Fin n, b r = c ↔ (c : ℕ) ≤ r ∧ (r : ℕ) < c + linBlockLen n I c := by
    intro c r
    by_cases hc : (c : ℕ) = 0 ∨ (c : ℕ) ∈ I
    · obtain ⟨-, h2, h3, h4⟩ := linBlockLen_spec (I := I) (a := c) hc
      constructor
      · intro h
        subst h
        refine ⟨hbr r, ?_⟩
        by_contra hr
        have hmI : (b r : ℕ) + linBlockLen n I (b r) ∈ I := by
          rcases h3 with h | h
          · have := r.isLt
            omega
          · exact h
        have := hge _ r (Or.inr hmI) (not_lt.mp hr)
        omega
      · rintro ⟨hcr, hrc⟩
        apply Fin.ext
        have h5 := hge c r hc hcr
        have h6 := hbr r
        by_contra hne
        have hlt : (c : ℕ) < b r := lt_of_le_of_ne h5 (fun h => hne h.symm)
        have hbI : (b r : ℕ) ∈ I := (hbP r).resolve_left (by omega)
        exact h4 _ hbI ⟨hlt, by omega⟩
    · rw [linBlockLen_of_not_start hc]
      constructor
      · intro h
        subst h
        exact absurd (hbP r) hc
      · rintro ⟨h1, h2⟩
        omega
  have hbt : M.BlockTriangular b := by
    intro i j hij
    have hij' : (b j : ℕ) < b i := hij
    have hlt : (j : ℕ) < b i := by
      by_contra h
      have := hge (b i) j (hbP i) (not_lt.mp h)
      omega
    have hbI : (b i : ℕ) ∈ I := (hbP i).resolve_left (by omega)
    exact hM _ hbI i j hlt (hbr i)
  rw [hbt.det_fintype]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hci : ∀ i : Fin (linBlockLen n I c), (c : ℕ) + i < n := fun i => by
    have := linBlockLen_le (I := I) c
    have := i.isLt
    omega
  let e : Fin (linBlockLen n I c) ≃ {r : Fin n // b r = c} :=
    { toFun := fun i => ⟨⟨c + i, hci i⟩, (hfib c _).mpr ⟨Nat.le_add_right _ _,
        Nat.add_lt_add_left i.isLt _⟩⟩
      invFun := fun r => ⟨r - c, by have := (hfib c r).mp r.2; omega⟩
      left_inv := fun i => by
        ext
        simp
      right_inv := fun r => by
        have := ((hfib c r).mp r.2).1
        apply Subtype.ext
        apply Fin.ext
        simp
        omega }
  rw [← Matrix.det_submatrix_equiv_self e (M.toSquareBlock b c)]
  rfl

end Product

section Block

theorem det_linBlockHom_eq_one {K : Type} [Field K] {n : ℕ} {I : Set ℕ} (a : Fin n)
    (x : ↥(LinearFlag.flagStabilizer n K I))
    (hx : ∀ c : Fin n, c ≠ a → linLeviHom K n I x c = 1) :
    ((linBlockHom K n I a x : Matrix.GeneralLinearGroup (Fin (linBlockLen n I a)) K) :
      Matrix (Fin (linBlockLen n I a)) (Fin (linBlockLen n I a)) K).det = 1 := by
  have hM : ∀ c ∈ I, ∀ k l : Fin n, (l : ℕ) < c → c ≤ (k : ℕ) →
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) k l = 0 :=
    fun c hc k l hl hk => stabilizer_entries (mem_flagStabilizer.mp x.2 c hc) hl hk
  have h1 := det_eq_prod_blkAt hM
  rw [Matrix.SpecialLinearGroup.det_coe, Finset.prod_eq_single a] at h1
  · exact h1.symm
  · intro c _ hc
    rw [← coe_linLeviHom_apply, hx c hc]
    simp
  · simp

end Block

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
