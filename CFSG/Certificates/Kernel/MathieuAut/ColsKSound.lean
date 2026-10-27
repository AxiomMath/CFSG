module

public import Certificates.Data.Kernel.MathieuAut.ColsK
public import CFSG.Certificates.Kernel.MathieuAut.InAutKSound

public section

namespace CFSG.KS.MathieuAut

open CFSG.Quasithin.H.Mathieu

theorem actM_colsOf (κ lift : List ℕ) {a : Array ℕ} (ha : a.size = 24) (m : ℕ) :
    actM κ (permM a (actM lift m)) = actM (colsOf κ lift a.toList) m := by
  rw [colsOf, permM, permCols_eq ha]
  exact (actM_map ((actM_xor κ).comp (actM_xor _)) lift m).symm

theorem act10_eq_cols {a : Array ℕ} (ha : a.size = 24) (m : ℕ) :
    act10 a m = actM (cols10 a.toList) m :=
  actM_colsOf cc10Cols lift10Cols ha m

theorem act11_eq_cols {a : Array ℕ} (ha : a.size = 24) (m : ℕ) :
    act11 a m = actM (cols11 a.toList) m :=
  actM_colsOf ccECols liftECols ha m

theorem actC10_eq_cols {a : Array ℕ} (ha : a.size = 24) (m : ℕ) :
    actC10 a m = actM (colsC10 a.toList) m :=
  actM_colsOf κC22Cols lift22Cols ha m

theorem actC11_eq_cols {a : Array ℕ} (ha : a.size = 24) (m : ℕ) :
    actC11 a m = actM (colsC11 a.toList) m :=
  actM_colsOf κCCols liftCCols ha m

theorem fixAll_spec {Ms : List (List ℕ)} {N : ℕ} {rel : ℕ → ℕ → Bool} {ok : ℕ → Bool}
    (h : fixAll Ms N rel ok = true) (m : ℕ) (hm : m < N)
    (hfix : ∀ M ∈ Ms, rel (actM M m) m = true) : ok m = true := by
  have h1 := List.all_eq_true.1 h m (List.mem_range.2 hm)
  have h2 : (Ms.all fun M => rel (actM M m) m) = true := List.all_eq_true.2 hfix
  simp only [h2, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem spanAll_spec {N : ℕ} {l : List ℕ} (h : spanAll N l = true) (m : ℕ) (hm : m < N) :
    m ∈ combos l := by
  simp only [spanAll, beq_iff_eq] at h
  have h1 := testBit_orMask m (combos l)
  rw [h, Nat.testBit_two_pow_sub_one, decide_eq_true hm] at h1
  exact of_decide_eq_true h1.symm

theorem transOK_spec {S : List ℕ} (hS : S.length = 24) (h : transOK S = true) (e : ℕ)
    (he : ∀ p < 24, ∃ q < 24, S.getD q 0 = S.getD p 0 ^^^ e) : e = 0 := by
  have hmem : ∀ p < 24, S.getD p 0 ∈ S := fun p hp => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  obtain ⟨q, hq, hq0⟩ := he 0 (by norm_num)
  have hhead : S.headD 0 = S.getD 0 0 := by cases S <;> rfl
  have hes : S.getD q 0 ^^^ S.headD 0 = e := by
    rw [hhead, hq0, Nat.xor_assoc, Nat.xor_comm e, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hall := List.all_eq_true.1 h (S.getD q 0) (hmem q hq)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.not_eq_true'] at hall
  rw [hes] at hall
  rcases hall with h0 | ⟨t, ht, hbit⟩
  · exact h0
  · obtain ⟨p, hp, hpt⟩ := List.getElem_of_mem ht
    obtain ⟨q', hq', hq'e⟩ := he p (by omega)
    rw [List.getD_eq_getElem _ _ hp, hpt] at hq'e
    rw [testBit_orMask, ← hq'e] at hbit
    exact absurd (hmem q' hq') (by simpa using hbit)

@[expose] def pairs24 : List (ℕ × ℕ) :=
  (List.range 24).flatMap fun i => ((List.range 24).filter (i < ·)).map fun j => (i, j)

theorem o2Masks24_eq : o2Masks24 = pairs24.map fun p => pairImg11 p.1 p.2 := by
  simp only [o2Masks24, pairs24, List.map_flatMap, List.map_map]
  rfl

theorem pairImg11_symm (i j : ℕ) : pairImg11 i j = pairImg11 j i := by
  rw [pairImg11, pairImg11, pairMask, pairMask, Nat.xor_comm]

theorem pairImg11_inj_of_nodup (h : o2Masks24.Nodup) (i j k l : Fin 24) (hij : i ≠ j)
    (hkl : k ≠ l) (he : pairImg11 i j = pairImg11 k l) : (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  rw [o2Masks24_eq] at h
  have hinj := List.inj_on_of_nodup_map h
  have hmem : ∀ a b : ℕ, a < b → b < 24 → (a, b) ∈ pairs24 := fun a b hab hb => by
    simp only [pairs24, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Prod.mk.injEq]
    exact ⟨a, by omega, b, ⟨hb, hab⟩, rfl, rfl⟩
  have key : ∀ a b c d : ℕ, a < b → b < 24 → c < d → d < 24 →
      pairImg11 a b = pairImg11 c d → a = c ∧ b = d := fun a b c d h1 h2 h3 h4 e =>
    Prod.mk.inj (hinj (hmem a b h1 h2) (hmem c d h3 h4) e)
  have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
  have hkl' : (k : ℕ) ≠ l := fun e => hkl (Fin.ext e)
  simp only [Fin.ext_iff]
  rcases Nat.lt_or_gt_of_ne hij' with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hkl' with h2 | h2
  · have := key _ _ _ _ h1 j.2 h2 l.2 he
    omega
  · have := key _ _ _ _ h1 j.2 h2 k.2 (he.trans (pairImg11_symm _ _))
    omega
  · have := key _ _ _ _ h1 i.2 h2 l.2 ((pairImg11_symm _ _).symm.trans he)
    omega
  · have := key _ _ _ _ h1 i.2 h2 k.2
      ((pairImg11_symm _ _).symm.trans (he.trans (pairImg11_symm _ _)))
    omega

end CFSG.KS.MathieuAut

end
