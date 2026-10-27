module

public import CFSG.Certificates.Kernel.LocalQTR9ConjSound

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1 CFSG.KC.Ord

theorem iffB_iff48 {a b : Bool} : S.iffB a b = true ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp [S.iffB, notB]

open CFSG.QuasithinUnique.Unc25L33 in
theorem s4048k (L : List R9) (hL : ∀ r, r ∈ L ↔ rdet r = 1) (sa sb : R9) (P0 W : List R9)
    {SA SB : ℕ} {LP LI LW PR : List ℕ}
    (ha : codeR sa = SA) (hb : codeR sb = SB) (hp : P0.map codeR = LP) (hw : W.map codeR = LW)
    (hk : c4048 SA SB LP LI LW PR = true)
    (hs : ∀ c < 20, allSLc c (sl4048 SA SB LP LI PR) = true) :
    let I := P0.filter fun x => x != rone && rmul x x == rone
    (rdet sa = 1 ∧ rdet sb = 1 ∧ rpw sa 8 = rone ∧ rmul sb sb = rone ∧
            rmul sb sa = rmul (rpw sa 3) sb ∧ P0.Nodup ∧ P0.length = 16 ∧ rone ∈ P0 ∧ sa ∈ P0 ∧
            sb ∈ P0 ∧ (∀ x ∈ P0, ∀ y ∈ P0, rmul x y ∈ P0) ∧ (∀ x ∈ P0, rpw x 16 = rone) ∧
            (∀ w ∈ W, rdet w = 1) ∧
            (∀ t ∈ I, ∀ s ∈ I, t ≠ s → rmul t s = rmul s t →
              ∃ w ∈ W, rpw w 3 = rone ∧ w ≠ rone ∧
                (∃ u ∈ [rone, t, s, rmul t s], rmul w t = rmul u w) ∧
                (∃ u ∈ [rone, t, s, rmul t s], rmul w s = rmul u w)))
    ∧ (∀ g ∈ L,
          (∃ p ∈ P0, rmul g sa = rmul p g) → (∃ q ∈ P0, rmul g sb = rmul q g) → g ∈ P0)
    ∧ (∀ g ∈ L, ∀ t ∈ I, ∀ s ∈ I, rmul g t = rmul t g → rmul g s = rmul s g → t ≠ s →
          rmul t s = rmul s t → g = rone ∨ g = t ∨ g = s ∨ g = rmul t s)
    ∧ (∀ g ∈ L, ∀ t ∈ I, ∀ s ∈ I, rmul g (rcof t) = rmul t g →
          rmul g (rcof s) = rmul s g → t ≠ s → rmul t s = rmul s t →
          (∃ p ∈ P0, rmul g (rcof sa) = rmul p g) ∧ (∃ q ∈ P0, rmul g (rcof sb) = rmul q g))
    ∧ (∀ g ∈ L,
          ¬ (rmul g (rcof sa) = rmul sa g ∧ rmul g (rcof sb) = rmul sb g)) := by
  intro I
  subst ha hb hp hw
  have hr : ∀ g ∈ L, sl4048 (codeR sa) (codeR sb) (P0.map codeR) LI PR (codeR g) = true :=
    fun g h => allSLc_sound hs g ((hL g).1 h)
  simp only [sl4048, P.letB_eq, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hr
  simp only [c4048, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hk
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17⟩ := hk
  rw [eqL_iff, filterL_mapR] at k14
  simp only [invoK_eq] at k14
  have hLI : LI = I.map codeR := k14
  subst hLI
  simp only [P.beq_iff, detK_eq_one, pwK_codeR, oneK_eq, mulK_codeR, codeR_eq_iff,
    distinctL_mapR, S.lenL_eq, List.length_map, S.memL_iff, mem_mapR, allL_mapR,
    P.blt_iff] at k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k15
  have hmemI : ∀ x, x ∈ I ↔ x ∈ P0 ∧ x ≠ rone ∧ rmul x x = rone := by
    intro x
    simp [I]
  have hpair : ∀ t ∈ I, ∀ s ∈ I, t ≠ s → rmul t s = rmul s t → ∃ i j : ℕ,
      ∃ (hi : i < I.length) (hj : j < I.length), I[i] = t ∧ I[j] = s ∧
        Nat.add i (Nat.mul 8 j) ∈ PR ∧ Nat.mod (Nat.add i (Nat.mul 8 j)) 8 = i ∧
        Nat.div (Nat.add i (Nat.mul 8 j)) 8 = j := by
    intro t ht s hs hts hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    refine ⟨i, j, hi, hj, rfl, rfl, ?_, ?_, ?_⟩
    · have h := (P.allN_iff _ _).1 k16 i (by rw [S.lenL_eq, List.length_map]; exact hi)
      have h2 := (P.allN_iff _ _).1 h j (by rw [S.lenL_eq, List.length_map]; exact hj)
      rw [iffB_iff48, getL_mapR I hi, getL_mapR I hj, P.andB_iff, P.notB_iff, beq_codeR,
        commK_codeR, S.memL_iff] at h2
      exact h2.1 ⟨hts, hc⟩
    · change (i + 8 * j) % 8 = i
      omega
    · change (i + 8 * j) / 8 = j
      omega
  refine ⟨⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht s hs hts hc
    obtain ⟨i, j, hi, hj, rfl, rfl, hp, e1, e2⟩ := hpair t ht s hs hts hc
    have h := (P.allL_iff _ _).1 k17 _ hp
    rw [P.letB_eq, P.letB_eq, e1, e2, getL_mapR I hi, getL_mapR I hj, anyL_mapR] at h
    obtain ⟨w, hw, h⟩ := h
    simp only [P.andB_iff, and_true, P.notB_iff, P.beq_iff, pwK_codeR, oneK_eq, mulK_codeR, codeR_eq_iff, P.anyL_iff, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    exact ⟨w, hw, h⟩
  · intro g hg ⟨p, hp, ep⟩ ⟨q, hq, eq⟩
    have h := (hr g hg).1
    rw [P.impB_iff, P.impB_iff, transK_cofK, mulK_codeR, mulK_codeR, mulK_codeR, mulK_codeR,
      S.memL_iff, S.memL_iff, S.memL_iff, mem_mapR, mem_mapR, mem_mapR] at h
    have hdg := (hL g).1 hg
    exact h (by rw [(conj_iff hdg sa p).2 ep]; exact hp) (by rw [(conj_iff hdg sb q).2 eq]; exact hq)
  · intro g hg t ht s hs hgt hgs hts hc
    obtain ⟨i, j, hi, hj, rfl, rfl, hp, e1, e2⟩ := hpair t ht s hs hts hc
    have h := (P.allL_iff _ _).1 (hr g hg).2.1 _ hp
    rw [e1, e2, P.impB_iff, P.andB_iff] at h
    have h2 := h ⟨bit_maskL _ _ (by simpa using hi)
      (by rw [getL_mapR I hi, commK_codeR]; exact hgt),
      bit_maskL _ _ (by simpa using hj) (by rw [getL_mapR I hj, commK_codeR]; exact hgs)⟩
    rw [getL_mapR I hi, getL_mapR I hj, S.memL_iff, oneK_eq, mulK_codeR] at h2
    simpa [codeR_eq_iff] using h2
  · intro g hg t ht s hs hgt hgs hts hc
    obtain ⟨i, j, hi, hj, rfl, rfl, hp, e1, e2⟩ := hpair t ht s hs hts hc
    have hdg := (hL g).1 hg
    have h := (P.allL_iff _ _).1 (hr g hg).2.2.1 _ hp
    rw [e1, e2, P.impB_iff, P.andB_iff] at h
    have h2 := h ⟨bit_maskL _ _ (by simpa using hi)
      (by simp only [getL_mapR I hi, cofK_codeR, transK_codeR, tr_rcof, mulK_codeR, P.beq_iff,
        codeR_eq_iff, conj_iff hdg]; exact hgt),
      bit_maskL _ _ (by simpa using hj)
      (by simp only [getL_mapR I hj, cofK_codeR, transK_codeR, tr_rcof, mulK_codeR, P.beq_iff,
        codeR_eq_iff, conj_iff hdg]; exact hgs)⟩
    simp only [P.andB_iff, cofK_codeR, transK_codeR, tr_rcof, mulK_codeR, S.memL_iff,
      mem_mapR] at h2
    exact ⟨⟨_, h2.1, ((conj_iff hdg _ _).1 rfl)⟩, ⟨_, h2.2, ((conj_iff hdg _ _).1 rfl)⟩⟩
  · intro g hg ⟨h1, h2⟩
    have hdg := (hL g).1 hg
    have h := (hr g hg).2.2.2
    simp only [P.notB_iff, P.andB_iff, cofK_codeR, transK_codeR, tr_rcof, mulK_codeR,
      P.beq_iff, codeR_eq_iff, conj_iff hdg] at h
    exact h ⟨h1, h2⟩

end CFSG.KC.LQT.R

end
