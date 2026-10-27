module

public import CFSG.Certificates.Kernel.LocalQTR9DecSound
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadL33Inputs

public section

namespace CFSG.KC.LQT.R

open CFSG.QuasithinUnique.Unc25K1 CFSG.QuasithinUnique.Unc25L33 CFSG.KC.Ord

section Conj

variable {g : R9} (hg : rdet g = 1)
include hg

theorem F_B (y : R9) : cjw g (adj g) (cjw (adj g) g y) = y := cjw_cjw (mul_adj hg) y
theorem B_F (y : R9) : cjw (adj g) g (cjw g (adj g) y) = y := cjw_cjw (adj_mul hg) y
theorem F_mul (x y : R9) : cjw g (adj g) (rmul x y) = rmul (cjw g (adj g) x) (cjw g (adj g) y) :=
  cjw_mul (adj_mul hg) x y
theorem B_mul (x y : R9) : cjw (adj g) g (rmul x y) = rmul (cjw (adj g) g x) (cjw (adj g) g y) :=
  cjw_mul (mul_adj hg) x y
theorem F_one : cjw g (adj g) rone = rone := cjw_one (mul_adj hg)
theorem B_one : cjw (adj g) g rone = rone := cjw_one (adj_mul hg)
theorem F_det (y : R9) : rdet (cjw g (adj g) y) = rdet y := rdet_cjw (mul_adj hg) y
theorem B_det (y : R9) : rdet (cjw (adj g) g y) = rdet y := rdet_cjw (adj_mul hg) y
theorem F_inj {x y : R9} (h : cjw g (adj g) x = cjw g (adj g) y) : x = y :=
  cjw_inj (adj_mul hg) h
theorem B_inj {x y : R9} (h : cjw (adj g) g x = cjw (adj g) g y) : x = y :=
  cjw_inj (mul_adj hg) h
theorem F_rpw (x : R9) (n : ℕ) : cjw g (adj g) (rpw x n) = rpw (cjw g (adj g) x) n :=
  cjw_rpw (mul_adj hg) (adj_mul hg) x n
theorem B_rpw (x : R9) (n : ℕ) : cjw (adj g) g (rpw x n) = rpw (cjw (adj g) g x) n :=
  cjw_rpw (adj_mul hg) (mul_adj hg) x n

theorem B_comm (x y : R9) :
    rmul (cjw (adj g) g x) (cjw (adj g) g y) = rmul (cjw (adj g) g y) (cjw (adj g) g x) ↔
      rmul x y = rmul y x := by
  rw [← B_mul hg, ← B_mul hg]
  exact ⟨B_inj hg, fun h => h ▸ rfl⟩

theorem B_eq_one (x : R9) : cjw (adj g) g x = rone ↔ x = rone := by
  constructor
  · intro h
    exact B_inj hg (h.trans (B_one hg).symm)
  · rintro rfl
    exact B_one hg

theorem F_eq_one (x : R9) : cjw g (adj g) x = rone ↔ x = rone := by
  constructor
  · intro h
    exact F_inj hg (h.trans (F_one hg).symm)
  · rintro rfl
    exact F_one hg

end Conj

theorem distinctL_iff : ∀ l : List ℕ, S.distinctL l = true ↔ l.Nodup
  | [] => by simp [S.distinctL]
  | x :: l => by
    change andB (notB (S.memL x l)) (S.distinctL l) = true ↔ _
    rw [P.andB_iff, P.notB_iff, S.memL_iff, distinctL_iff l, List.nodup_cons]

theorem getL_ge {l : List ℕ} {i : ℕ} (h : l.length ≤ i) : getL l i = 0 := by
  rw [getL_eq, List.getD_eq_default _ _ h]

open CFSG.QuasithinUnique.Fin253 in
theorem s4056k (M : ListModel S3 R9) (hm : M.mul = rmul) (h1 : M.one = rone) (_hi : M.inv = rinv)
    (hL : ∀ r, r ∈ M.elems ↔ rdet r = 1) (hn : M.elems.Nodup) {G R WO WT S0 C0 : List ℕ}
    {CI : List (List ℕ)} {T0 : ℕ}
    (hk : c4056 G R WO CI T0 WT S0 C0 = true)
    (hs : ∀ c < 20, allSLc c (sl4056 G R WO CI T0 WT S0 C0) = true) :
    let I := M.elems.filter fun t => decide (t ≠ M.one ∧ M.mul t t = M.one)
    let O := M.elems.filter fun u => decide (lpow M.mul M.one u 4 = M.one ∧
      lpow M.mul M.one u 2 ≠ M.one)
    (CenterOK M.mul M.one M.elems)
    ∧ (OddOK M.mul M.one 351 M.elems I O)
    ∧ (QuatAll M.mul M.one M.elems I)
    ∧ (CoreAll M.mul M.one M.inv M.elems I) := by
  have hinv : ∀ c ∈ M.elems, M.inv c = adj c := by
    intro c hc
    obtain ⟨x, rfl⟩ := (M.mem_elems _).1 hc
    have e1 : rmul (M.inv (M.enc x)) (M.enc x) = rone := by
      rw [← M.enc_inv, ← hm, ← M.enc_mul, inv_mul_cancel, M.enc_one, h1]
    exact (inv_unique (mul_adj ((hL _).1 hc)) e1).symm
  intro I O
  have hI : ∀ t, t ∈ I ↔ t ∈ M.elems ∧ t ≠ rone ∧ rmul t t = rone := by
    intro t
    simp [I, hm, h1]
  have hO : ∀ u, u ∈ O ↔ u ∈ M.elems ∧ rpw u 4 = rone ∧ rpw u 2 ≠ rone := by
    intro u
    simp [O, hm, h1, lpow_eq]
  rw [hm, h1]
  generalize hE : M.elems = E at hL hn hinv hI hO ⊢
  simp only [c4056, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hk
  obtain ⟨k1, k2, -, -, k5, -, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ := hk
  obtain ⟨τ, rfl, hτ⟩ := exists_of_slOK k7
  have hr : ∀ z ∈ E, sl4056 G R WO CI (codeR τ) WT S0 C0 (codeR z) = true :=
    fun z h => allSLc_sound hs z ((hL z).1 h)
  simp only [sl4056, S.allBs_cons, S.allBs_nil, P.andB_iff, and_true] at hr
  simp only [P.orB_iff, P.andB_iff, P.notB_iff, P.impB_iff, P.beq_iff, P.anyL_iff, P.allN_iff,
    S.memL_iff, S.lenL_eq, mulK_dec, pwK_dec, pwB351, commK_dec, invoK_dec, dec_codeR, oneK_eq,
    codeR_eq_iff, ne_eq] at hr
  have hconjI : ∀ t ∈ E, t ≠ rone → rmul t t = rone →
      ∃ g, rdet g = 1 ∧ cjw g (adj g) τ = t := by
    intro t ht ht1 ht2
    obtain ⟨w, hw, hwt⟩ := (hr t ht).2.2.2.1 ⟨ht1, ht2⟩
    have h8 := (P.allL_iff _ _).1 k8 w hw
    rw [P.andB_iff, P.beq_iff, conjK_dec, dec_codeR, hwt, codeR_eq_iff] at h8
    obtain ⟨-, hgd⟩ := codeR_dec_of_slOK h8.1
    exact ⟨_, hgd, h8.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro z hz
    rcases (hr z hz).1 with h | ⟨g, hg, h⟩
    · exact Or.inl h
    · obtain ⟨-, hgd⟩ := codeR_dec_of_slOK ((P.allL_iff _ _).1 k1 g hg)
      exact Or.inr ⟨dec g, (hL _).2 hgd, h⟩
  ·
    intro x hx hx1 hxp
    rw [lpow_eq] at hxp
    obtain ⟨w, hw, hwx⟩ := (hr x hx).2.1 ⟨hx1, hxp⟩
    have h2 := (P.allL_iff _ _).1 k2 w hw
    rw [P.andB_iff, P.beq_iff, conjK_dec, hwx, codeR_eq_iff] at h2
    obtain ⟨hsl, hcx⟩ := h2
    obtain ⟨-, hg⟩ := codeR_dec_of_slOK hsl
    set g := dec (Nat.land (snd20 w) 1048575)
    set r := dec (getL R (Nat.shiftRight w 40))
    have hxr : cjw g (adj g) r = x := hcx
    have hil : Nat.shiftRight w 40 < R.length := by
      by_contra hc
      have h0 : r = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
        change dec (getL R (Nat.shiftRight w 40)) = _
        rw [getL_ge (by omega), dec_zero]
      have := (hL x).1 hx
      rw [← hxr, h0, rdet_cjw_zero] at this
      exact absurd this (by decide)
    have hc := fun z hz => (hr z hz).2.2.1 _ hil
    have hBr : ∀ z, rmul z x = rmul x z →
        rmul (cjw (adj g) g z) r = rmul r (cjw (adj g) g z) := by
      intro z hz
      rw [← B_F hg r, hxr, B_comm hg]
      exact hz
    have hBE : ∀ z ∈ E, cjw (adj g) g z ∈ E := fun z hz => (hL _).2 (by
      rw [B_det hg]; exact (hL z).1 hz)
    refine ⟨?_, ?_⟩
    · intro u hu hux
      obtain ⟨huE, hu4, hu2⟩ := (hO u).1 hu
      have := (hc _ (hBE u huE) (hBr u hux)).2
      rw [← B_rpw hg, ← B_rpw hg, B_eq_one hg, B_eq_one hg] at this
      exact this ⟨hu4, hu2⟩
    · intro t ht s hs hts hcm
      rw [List.mem_filter, decide_eq_true_iff, hI] at ht hs
      obtain ⟨⟨htE, ht1, ht2⟩, htx⟩ := ht
      obtain ⟨⟨hsE, hs1, hs2⟩, hsx⟩ := hs
      have hmt := (hc _ (hBE t htE) (hBr t htx)).1
        ⟨by rw [B_eq_one hg]; exact ht1, by rw [← B_mul hg, ht2, B_one hg]⟩
      have hms := (hc _ (hBE s hsE) (hBr s hsx)).1
        ⟨by rw [B_eq_one hg]; exact hs1, by rw [← B_mul hg, hs2, B_one hg]⟩
      rcases getLL_mem CI (Nat.shiftRight w 40) with hl | hl
      · have h5 := (allLL_iff _ _).1 k5 _ hl
        rw [P.allL_iff] at h5
        have h55 := (P.allL_iff _ _).1 (h5 _ hmt) _ hms
        rw [P.impB_iff, P.notB_iff, P.notB_iff, beq_codeR, commK_codeR, B_comm hg] at h55
        exact h55 (fun h => hts (B_inj hg h)) hcm
      · rw [hl] at hmt
        exact absurd hmt (List.not_mem_nil)
  ·
    intro t ht
    obtain ⟨htE, ht1, ht2⟩ := (hI t).1 ht
    obtain ⟨g, hg, hgt⟩ := hconjI t htE ht1 ht2
    have hBt : cjw (adj g) g t = τ := by rw [← hgt, B_F hg]
    have hBE : ∀ z ∈ E, cjw (adj g) g z ∈ E := fun z hz => (hL _).2 (by
      rw [B_det hg]; exact (hL z).1 hz)
    have hFE : ∀ z, rdet z = 1 → cjw g (adj g) z ∈ E := fun z hz => (hL _).2 (by
      rw [F_det hg]; exact hz)
    have hS0 : ∀ y ∈ S0, codeR (dec y) = y ∧ rdet (dec y) = 1 ∧ rmul (dec y) (dec y) = τ := by
      intro y hy
      have h9 := (P.allL_iff _ _).1 k9 y hy
      rw [P.andB_iff, P.beq_iff, mulK_dec, codeR_eq_iff] at h9
      obtain ⟨h9a, h9b⟩ := codeR_dec_of_slOK h9.1
      exact ⟨h9a, h9b, h9.2⟩
    have hFS : ∀ y ∈ S0, cjw g (adj g) (dec y) ∈ E.filter fun y => decide (rmul y y = t) := by
      intro y hy
      obtain ⟨-, hyd, hyy⟩ := hS0 y hy
      rw [List.mem_filter, decide_eq_true_iff, ← F_mul hg, hyy, hgt]
      exact ⟨hFE _ hyd, rfl⟩
    have hS0nd : S0.Nodup := by
      have := (distinctL_iff _).1 k11
      exact (List.nodup_cons.1 (List.nodup_cons.1 this).2).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [P.notB_iff, P.beq_iff, S.lenL_eq] at k10
      obtain ⟨y0, hy0⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero k10)
      exact List.ne_nil_of_mem (hFS y0 hy0)
    · intro y hy y' hy'
      rw [List.mem_filter, decide_eq_true_iff] at hy hy'
      have hz : ∀ y ∈ E, rmul y y = t → codeR (cjw (adj g) g y) ∈ S0 := fun y hyE hyt =>
        (hr _ (hBE y hyE)).2.2.2.2.1 (by rw [← B_mul hg, hyt, hBt])
      have h13 := (P.allL_iff _ _).1 ((P.allL_iff _ _).1 k13 _ (hz y hy.1 hy.2)) _
        (hz y' hy'.1 hy'.2)
      simp only [P.letB_eq, P.orB_iff, P.beq_iff, mulK_dec, dec_codeR, oneK_eq,
        codeR_eq_iff] at h13
      rw [← B_mul hg, ← B_mul hg, B_eq_one hg, ← hBt] at h13
      rcases h13 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (B_inj hg h))
      · exact Or.inr (Or.inr (B_inj hg h))
    · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hn.filter _⟩⟩
      · simp only [List.mem_cons, List.mem_filter, decide_eq_true_iff, not_or]
        refine ⟨fun h => ht1 h.symm, fun h => ht1 ?_⟩
        rw [← h.2, one_rmul]
      · simp only [List.mem_filter, decide_eq_true_iff, not_and]
        intro _ h
        exact ht1 (by rw [← h, ht2])
    · rw [S.lenL_eq] at k12
      have k12' : 3 ≤ S0.length := Nat.le_of_ble_eq_true k12
      have hnd : (S0.map fun y => cjw g (adj g) (dec y)).Nodup := by
        refine hS0nd.map_on fun a ha b hb hab => ?_
        rw [← (hS0 a ha).1, ← (hS0 b hb).1, F_inj hg hab]
      have hle := (hnd.subperm fun z hz => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
        exact hFS y hy).length_le
      rw [List.length_map] at hle
      simp only [List.length_cons]
      omega
  ·
    intro t ht
    obtain ⟨htE, ht1, ht2⟩ := (hI t).1 ht
    obtain ⟨g, hg, hgt⟩ := hconjI t htE ht1 ht2
    have hBt : cjw (adj g) g t = τ := by rw [← hgt, B_F hg]
    intro c hc
    rw [List.mem_filter, decide_eq_true_iff] at hc
    obtain ⟨hcE, hct⟩ := hc
    have hcd := (hL c).1 hcE
    set c' := cjw (adj g) g c
    have hc'd : rdet c' = 1 := by rw [B_det hg]; exact hcd
    have hc'E : c' ∈ E := (hL _).2 hc'd
    have hcc : cjw g (adj g) c' = c := F_B hg c
    have hm0 := (hr c' hc'E).2.2.2.2.2 (by rw [← hBt, B_comm hg]; exact hct)
    have h15 := (P.allL_iff _ _).1 k15 _ hm0
    simp only [P.orB_iff, P.beq_iff, P.anyL_iff, P.notB_iff, mulK_dec, transK_cofK_dec, pwB16,
      dec_codeR, oneK_eq, codeR_eq_iff] at h15
    rcases h15 with (h | h | h) | ⟨w, hw, h⟩
    · left; left
      rw [← hcc, h, F_one hg]
    · left; right; left
      rw [← hcc, h, hgt]
    · left; right; right
      rw [← hcc, ← F_mul hg, h, hgt]
    · right
      have h14 := (P.allL_iff _ _).1 k14 w hw
      rw [P.andB_iff, commK_dec, dec_codeR] at h14
      obtain ⟨-, hwd⟩ := codeR_dec_of_slOK h14.1
      set w' := dec w
      set W := cjw g (adj g) w'
      have hWE : W ∈ E := (hL _).2 (by rw [F_det hg]; exact hwd)
      have hWt : rmul W t = rmul t W := by
        rw [← hgt, ← F_mul hg, ← F_mul hg, h14.2]
      refine ⟨W, List.mem_filter.2 ⟨hWE, decide_eq_true hWt⟩, ?_⟩
      have hac : adj c = cjw g (adj g) (adj c') := by
        refine (inv_unique (c := c) ?_ (adj_mul hcd)).symm
        rw [← hcc, ← F_mul hg, mul_adj hc'd, F_one hg]
      have haW : adj W = cjw g (adj g) (adj w') := by
        refine (inv_unique (c := W) ?_ (adj_mul ((hL W).1 hWE))).symm
        rw [← F_mul hg, mul_adj hwd, F_one hg]
      rw [hinv c hcE, hinv W hWE, lpow_eq, hac, haW, ← hcc, ← F_mul hg, ← F_mul hg, ← F_mul hg,
        ← F_rpw hg, Ne, F_eq_one hg]
      exact h

end CFSG.KC.LQT.R

end
