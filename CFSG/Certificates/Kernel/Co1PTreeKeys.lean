module

public import CFSG.Certificates.Kernel.Co1PPathSound

public section

namespace CFSG.KC.Co1P

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.TreeK

section

variable {GK GiK : List Nat} {ng R0 N kw d : Nat} {rs : List (Nat × Nat)} {R SK IX : Nat → Nat}
  (hh : (treePts (hsAct GK) ng oneK rs).2 = true) (hhi : (treePts (hisAct GiK) ng oneK rs).2 = true)
  (hr : recsEqK R rs 0 = true) (hN : rs.length + 1 = N)
  (hk : ∀ s < N, keyAtP N kw SK IX (ptPK GK GiK R R0 d) s = true)

include hk in
theorem keyAtP_keys : ∀ s < N, keyAt N kw SK IX (fun i => (ptPK GK GiK R R0 d i).1) s = true :=
  fun s hs => (CFSG.KC.TreeK.andB_true (hk s hs)).1

include hk in
theorem ptPK_flag {i : Nat} (hi : i < N) : (ptPK GK GiK R R0 d i).2 = true := by
  obtain ⟨s, hs, rfl⟩ := ix_surj (keyAtP_keys hk) hi
  exact (CFSG.KC.TreeK.andB_true (hk s hs)).2

include hh hhi in
theorem ptsL_len : (ptsL GK GiK ng R0 rs).length = rs.length + 1 := by
  have l1 := walk_length hh
  have l2 := walk_length hhi
  rw [ptsL, (conjL_get R0 _ _ (l1.trans l2.symm)).1, l1]

include hh hhi hr hN hk in
theorem ptsL_get {i : Nat} (hi : i < N) :
    (ptsL GK GiK ng R0 rs)[i]?.getD 0 = (ptPK GK GiK R R0 d i).1 := by
  have l1 := walk_length hh
  have l2 := walk_length hhi
  rw [ptsL, (conjL_get R0 _ _ (l1.trans l2.symm)).2 i (by omega),
    ptPK_sound hh hhi hr (by omega) (ptPK_flag hk hi)]
  rfl

include hh hhi hr hN hk in
theorem ptsL_nodup (hkw : kw ≤ 576) : (modL (ptsL GK GiK ng R0 rs)).Nodup :=
  nodup_modL_of_keys hkw (keyAtP_keys hk) (by rw [ptsL_len hh hhi, hN])
    fun _ hi => ptsL_get hh hhi hr hN hk hi

include hh hhi hr hN hk in
theorem ptsL_any {dd : Nat} (hkw : kw ≤ 576) (hd : N < 2 ^ dd) (X : Nat) :
    ((ptsL GK GiK ng R0 rs).any fun y => eqK X y) =
      memPin N kw dd SK IX (fun i => (ptPK GK GiK R R0 d i).1) X := by
  apply Bool.eq_iff_iff.2
  rw [memPin_iff (keyAtP_keys hk) hkw hd, List.any_eq_true]
  have hl := ptsL_len (GK := GK) (GiK := GiK) (R0 := R0) hh hhi
  constructor
  · rintro ⟨y, hy, e⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
    have hi' : i < N := by omega
    refine ⟨i, hi', ?_⟩
    rw [← ptsL_get hh hhi hr hN hk hi', List.getElem?_eq_getElem hi, Option.getD_some]
    exact e
  · rintro ⟨i, hi, e⟩
    have hi' : i < (ptsL GK GiK ng R0 rs).length := by omega
    refine ⟨_, List.getElem_mem hi', ?_⟩
    rw [← ptsL_get hh hhi hr hN hk hi, List.getElem?_eq_getElem hi', Option.getD_some] at e
    exact e

end

end CFSG.KC.Co1P

end
