module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtN
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf5TtPairs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK

open CFSG.Monster.B.Co2 PkG CovK CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6Cover
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic

set_option linter.unusedSectionVars false

@[expose] abbrev RR (p : ℕ) (x : ↥ySub) : Prop := ResRep p (x : Equiv.Perm (Fin 240))

theorem RR.mul {p q : ℕ} {x y : ↥ySub} (hp : RR p x) (hq : RR q y) :
    RR (PkG.comp 64 48 p q) (x * y) := ResRep.comp hp hq

theorem RR.one' : RR (PkG.one 64 48) 1 := ResRep.one

theorem RR.unique {p q : ℕ} {x : ↥ySub} (hp : RR p x) (hq : RR q x) : p = q :=
  ResRep.digits_unique hp hq

theorem res_xw {w : List ℕ} : RR (evalW 64 48 base48 w) (xw w) := resW w

theorem res_xw_inv {w : List ℕ} (hw : ∀ l ∈ w, l < 6) :
    RR (evalW 64 48 base48 (invW6 w)) (xw w)⁻¹ := by
  have h := resW (invW6 w)
  rw [permW_inv6 _ hw] at h
  exact h

theorem rowW_lt {r : List ℕ} (hr : r ∈ rowsT) : ∀ l ∈ rowW r, l < 6 := fun l hl =>
  rowOk_letters hr l (List.mem_append_right _ hl)

theorem IP_get (a : ℕ) : IP.getD a (one 64 48) = evalW 64 48 base48 (Iw.getD a []) := by
  rw [← IP_eq]
  exact getD_map' (evalW 64 48 base48) Iw a []

theorem IiP_get (a : ℕ) :
    IiP.getD a (one 64 48) = evalW 64 48 base48 (invW6 (Iw.getD a [])) := by
  rw [← IiP_eq]
  exact getD_map' (fun w => evalW 64 48 base48 (invW6 w)) Iw a []

theorem Iw_length : Iw.length = 48 := by decide +kernel

theorem sq_elt_index {x : ↥ySub} (hx : x ∈ tT) (hsq : x * x = Sp6Cover.tY) :
    ∃ a < 48, RR (IP.getD a (one 64 48)) x ∧ RR (IiP.getD a (one 64 48)) x⁻¹ := by
  obtain ⟨r, hr, rfl⟩ := exists_row hx
  have hflag := sq_flag hr hsq
  have hF : rowW r ∈ Iw := by
    rw [← Iw_eq]
    exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, by rw [hflag]; rfl⟩, rfl⟩
  obtain ⟨a, ha, hga⟩ := List.mem_iff_getElem.1 hF
  have hw : Iw.getD a [] = rowW r := by
    rw [List.getD_eq_getElem _ _ ha]
    exact hga
  refine ⟨a, Iw_length ▸ ha, ?_, ?_⟩
  · rw [IP_get, hw]
    exact res_elt r
  · rw [IiP_get, hw]
    exact res_xw_inv (rowW_lt hr)

theorem pair_rec (a b : ℕ) (ha : a < 48) (hb : b < 48) :
    ∃ r ∈ pairRecs, r.getD 0 0 = a ∧ r.getD 1 0 = b ∧ pairOk r = true := by
  have hm : (a, b) ∈ pairRecs.map (fun r => (r.getD 0 0, r.getD 1 0)) := by
    rw [pairs_exh]
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨a, ha, b, hb, rfl⟩
  obtain ⟨r, hr, hrab⟩ := List.mem_map.1 hm
  obtain ⟨h1, h2⟩ := Prod.mk.inj hrab
  exact ⟨r, hr, h1, h2, List.all_eq_true.1 pairs_true r hr⟩

theorem xw_mem_RY {w : List ℕ} (hw : w ∈ L0w) : xw w ∈ RY := by
  obtain ⟨e, he, hew⟩ := List.mem_iff_getElem.1 hw
  have := L0_mem_RY e
  rwa [List.getD_eq_getElem _ _ he, hew] at this

theorem mem_RY_of_L0 {x : ℕ} {z : ↥ySub} (hz : z ∈ tT) (hxz : RR x z)
    (h : L0P.contains x = true) : z ∈ RY := by
  have hm := List.mem_of_elem_eq_true h
  rw [← L0P_eq] at hm
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hm
  have : z = xw w := res_inj hz (xw_mem w) hxz (resW w)
  rw [this]
  exact xw_mem_RY hw

@[expose] def Rl48 (x y : ℕ) : List ℕ :=
  [one 64 48, x, comp 64 48 x x, comp 64 48 (comp 64 48 x x) x, y, comp 64 48 y x,
    comp 64 48 y (comp 64 48 x x), comp 64 48 y (comp 64 48 (comp 64 48 x x) x)]

theorem R_tables {i' j' : ↥ySub} {X Y : ℕ} (hX : RR X i') (hY : RR Y j') {R : Subgroup ↥ySub}
    (hRel : ∀ r ∈ R, ∃ k < 4, r = i' ^ k ∨ r = j' * i' ^ k) :
    ∀ r ∈ R, ∃ p ∈ Rl48 X Y, RR p r := by
  intro r hr
  obtain ⟨k, hk, hcase⟩ := hRel r hr
  have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl | rfl <;> rcases hcase with rfl | rfl
  · exact ⟨one 64 48, by simp [Rl48], by rw [pow_zero]; exact RR.one'⟩
  · exact ⟨Y, by simp [Rl48], by rw [pow_zero, mul_one]; exact hY⟩
  · exact ⟨X, by simp [Rl48], by rw [pow_one]; exact hX⟩
  · exact ⟨comp 64 48 Y X, by simp [Rl48], by rw [pow_one]; exact RR.mul hY hX⟩
  · exact ⟨comp 64 48 X X, by simp [Rl48], by rw [pow_two]; exact RR.mul hX hX⟩
  · exact ⟨comp 64 48 Y (comp 64 48 X X), by simp [Rl48],
      by rw [pow_two]; exact RR.mul hY (RR.mul hX hX)⟩
  · exact ⟨comp 64 48 (comp 64 48 X X) X, by simp [Rl48],
      by rw [pow_succ, pow_two]; exact RR.mul (RR.mul hX hX) hX⟩
  · exact ⟨comp 64 48 Y (comp 64 48 (comp 64 48 X X) X), by simp [Rl48],
      by rw [pow_succ, pow_two]; exact RR.mul hY (RR.mul (RR.mul hX hX) hX)⟩

theorem quat_data {R : Subgroup ↥ySub} {t : ↥ySub} (e : ↥R ≃* QuaternionGroup 2)
    (hu : IsUniqueInvolution R t) :
    ∃ i j : ↥ySub, i ∈ R ∧ j ∈ R ∧ i * i = t ∧ j * j = t ∧
      j * i * j⁻¹ = i⁻¹ ∧ ∀ r ∈ R, ∃ k < 4, r = i ^ k ∨ r = j * i ^ k := by
  let ι : QuaternionGroup 2 →* ↥ySub := R.subtype.comp e.symm.toMonoidHom
  have hιR : ∀ q, ι q ∈ R := fun q => (e.symm q).2
  have hιinj : Function.Injective ι := R.subtype_injective.comp e.symm.injective
  have hιsurj : ∀ r ∈ R, ∃ q, ι q = r := fun r hr => ⟨e ⟨r, hr⟩, by
    show ((e.symm (e ⟨r, hr⟩) : ↥R) : ↥ySub) = r
    rw [MulEquiv.symm_apply_apply]⟩
  have q1 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
  have q2 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide
  have q3 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
      QuaternionGroup.a 2 := by decide
  have q4 : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 *
      (QuaternionGroup.xa 0)⁻¹ = (QuaternionGroup.a 1)⁻¹ := by decide
  have q5 : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by decide
  have q6 : ∀ q : QuaternionGroup 2, ∃ k < 4,
      q = (QuaternionGroup.a 1) ^ k ∨ q = QuaternionGroup.xa 0 * (QuaternionGroup.a 1) ^ k := by
    decide
  have ht : ι (QuaternionGroup.a 2) = t := by
    have hm := hιR (QuaternionGroup.a 2)
    have hs : ι (QuaternionGroup.a 2) * ι (QuaternionGroup.a 2) = 1 := by
      rw [← map_mul, q1, map_one]
    rcases hu.unique _ hm hs with h | h
    · exact absurd (hιinj (h.trans (map_one ι).symm)) q5
    · exact h
  refine ⟨ι (QuaternionGroup.a 1), ι (QuaternionGroup.xa 0), hιR _, hιR _, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, q2, ht]
  · rw [← map_mul, q3, ht]
  · simpa only [map_mul, map_inv] using congrArg ι q4
  · intro r hr
    obtain ⟨q, rfl⟩ := hιsurj r hr
    obtain ⟨k, hk, hq⟩ := q6 q
    refine ⟨k, hk, ?_⟩
    rcases hq with rfl | rfl
    · left; rw [map_pow]
    · right; rw [map_mul, map_pow]

theorem card_of_quat (R : Subgroup ↥ySub) (e : ↥R ≃* QuaternionGroup 2) : Nat.card R = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem core_eq_RY_of_data {R : Subgroup ↥ySub}
    (hdata : ∃ i j : ↥ySub, i ∈ R ∧ j ∈ R ∧ i * i = Sp6Cover.tY ∧ j * j = Sp6Cover.tY ∧
      j * i * j⁻¹ = i⁻¹ ∧ ∀ r ∈ R, ∃ k < 4, r = i ^ k ∨ r = j * i ^ k)
    (hcard : Nat.card R = 8)
    (htw : ∀ s ∈ Sp0Core.TT Sp6Cover.tY, conjSub s R = R ∨ Commutes R (conjSub s R)) :
    R = RY := by
  obtain ⟨i', j', hiR, hjR, hii, hjj, hji, hRel⟩ := hdata
  have hiT : i' ∈ tT := mem_tT_of_comm (by rw [← hii, ← mul_assoc])
  have hjT : j' ∈ tT := mem_tT_of_comm (by rw [← hjj, ← mul_assoc])
  obtain ⟨a, ha, hXa, hXia⟩ := sq_elt_index hiT hii
  obtain ⟨b, hb, hYb, hYib⟩ := sq_elt_index hjT hjj
  obtain ⟨r, hrp, hr0, hr1, hok⟩ := pair_rec a b ha hb
  unfold pairOk at hok
  simp only [hr0, hr1] at hok
  have pick : ∀ n : ℕ, ∃ gE ∈ R, RR (if n == 0 then IP.getD a (one 64 48) else IP.getD b (one 64 48)) gE := by
    intro n
    by_cases hn : (n == 0) = true
    · exact ⟨i', hiR, by rw [if_pos hn]; exact hXa⟩
    · exact ⟨j', hjR, by rw [if_neg hn]; exact hYb⟩
  rcases (by omega : r.getD 2 0 = 0 ∨ r.getD 2 0 = 1 ∨ 2 ≤ r.getD 2 0) with hk | hk | hk
  · exfalso
    have c0 : (r.getD 2 0 == 0) = true := by rw [hk]; rfl
    rw [if_pos c0] at hok
    have hne := bne_iff_ne.1 hok
    apply hne
    have h1 := RR.mul (RR.mul hYb hXa) hYib
    rw [hji] at h1
    exact RR.unique h1 hXia
  · have c0 : ¬ (r.getD 2 0 == 0) = true := by rw [hk]; decide
    have c1 : (r.getD 2 0 == 1) = true := by rw [hk]; rfl
    rw [if_neg c0, if_pos c1] at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hx, hy⟩ := hok
    have hiRY : i' ∈ RY := mem_RY_of_L0 hiT hXa hx
    have hjRY : j' ∈ RY := mem_RY_of_L0 hjT hYb hy
    have hle : R ≤ RY := by
      intro r hr
      obtain ⟨k, hk4, hcase⟩ := hRel r hr
      rcases hcase with rfl | rfl
      · exact RY.pow_mem hiRY k
      · exact RY.mul_mem hjRY (RY.pow_mem hiRY k)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_RY, hcard])
  · exfalso
    have c0 : ¬ (r.getD 2 0 == 0) = true := by simp only [beq_iff_eq]; omega
    have c1 : ¬ (r.getD 2 0 == 1) = true := by simp only [beq_iff_eq]; omega
    rw [if_neg c0, if_neg c1] at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hA, -⟩, hC⟩, hD⟩ := hok
    have hlet : ∀ l ∈ r.drop 6, l < 6 := fun l hl => by
      simpa using List.all_eq_true.1 hA l hl
    have hs : xw (r.drop 6) ∈ Sp0Core.TT Sp6Cover.tY := mem_TT_iff.2 (xw_mem _)
    have hRc : RR (evalW 64 48 base48 (r.drop 6)) (xw (r.drop 6)) := res_xw
    have hRci : RR (evalW 64 48 base48 (invW6 (r.drop 6))) (xw (r.drop 6))⁻¹ :=
      res_xw_inv hlet
    obtain ⟨gE, hgR, hgRR⟩ := pick (r.getD 3 0)
    obtain ⟨uE, huR, huRR⟩ := pick (r.getD 4 0)
    obtain ⟨g'E, hg'R, hg'RR⟩ := pick (r.getD 5 0)
    have hcg := RR.mul hRc (RR.mul hgRR hRci)
    have hcg' := RR.mul hRc (RR.mul hg'RR hRci)
    rcases htw _ hs with hcon | hcom
    · have hmemR : xw (r.drop 6) * (gE * (xw (r.drop 6))⁻¹) ∈ R := by
        rw [← mul_assoc, ← hcon]
        exact conj_mem_conjSub hgR
      obtain ⟨p, hpmem, hpRR⟩ := R_tables hXa hYb hRel _ hmemR
      have hcgp := RR.unique hcg hpRR
      have hcont : (Rl48 (IP.getD a (one 64 48)) (IP.getD b (one 64 48))).contains
          (comp 64 48 (evalW 64 48 base48 (r.drop 6))
            (comp 64 48 (if r.getD 3 0 == 0 then IP.getD a (one 64 48) else IP.getD b (one 64 48))
              (evalW 64 48 base48 (invW6 (r.drop 6))))) = true := by
        rw [hcgp]
        exact List.elem_eq_true_of_mem hpmem
      simp only [Rl48] at hcont
      rw [hcont] at hC
      exact absurd hC (by decide)
    · have hmem : xw (r.drop 6) * (g'E * (xw (r.drop 6))⁻¹) ∈ conjSub (xw (r.drop 6)) R := by
        rw [← mul_assoc]
        exact conj_mem_conjSub hg'R
      have hcm := hcom uE huR _ hmem
      have e1 := RR.mul huRR hcg'
      have e2 := RR.mul hcg' huRR
      rw [hcm] at e1
      exact bne_iff_ne.1 hD (RR.unique e1 e2)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.TtK
