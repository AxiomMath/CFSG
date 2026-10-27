module

public import Certificates.Data.Kernel.HMathieu.Odd
public import CFSG.Certificates.Kernel.HMathieu.TabSound
public import CFSG.Certificates.Kernel.HMathieu.FixCertSound
public import CFSG.Quasithin.Background.HMathieuChain

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu

variable {cc lift : List Nat} {n r fuel : Nat} {gens E : List Nat} {Js : List (List Nat)}

theorem oddOK_spec (h : oddOK cc lift n r fuel gens E Js = true) :
    (bfsP gens fuel [pidn 24 5] [pidn 24 5]).reverse = E ∧ (∀ p ∈ E, vpK p = true) ∧
      (∀ g ∈ gens, vpK g = true) ∧ allImg n r ((E.drop 1).map (matP cc lift n)) Js = true := by
  simp only [oddOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem packed_of_oddOK {T : PT 24} (hT : T = PT.ofGens 24 (gens.map unpk) fuel)
    (h : oddOK cc lift n r fuel gens E Js = true) : Packed T E where
  elems := by
    subst hT
    change bfsClosure 24 (gens.map unpk) fuel = _
    rw [bfsClosure_eq (oddOK_spec h).2.2.1, (oddOK_spec h).1]
  one := by subst hT; rfl
  vp := (oddOK_spec h).2.1

theorem oddFix_of {T : PT 24} [Fact (T.check = true)]
    (hT : T = PT.ofGens 24 (gens.map unpk) fuel) (h : oddOK cc lift n r fuel gens E Js = true)
    {b : Nat} (hb : n - r ≤ b) {mats : Array (List Nat)}
    (hm : mats = T.elems.map fun a => matOf n fun m => actM cc (permM a (actM lift m))) :
    ∀ p : T.Elem, p ≠ 1 → (fixMasks n (fun q m => actM (mats[q.idx]!) m) [p]).length ≤ 2 ^ b := by
  intro p hp
  have H := packed_of_oddOK hT h
  have hidx : p.idx ≠ 0 := fun e => hp (PT.Elem.ext' (by rw [e, PT.idx_one, H.one]))
  have hM : mats[p.idx]! = matP cc lift n (pk E p) := by
    rw [hm, map_elems_get H]
    unfold matP matOf
    simp only [actM_unpk]
  have hlt := idx_lt H p
  have hmem : matP cc lift n (pk E p) ∈ (E.drop 1).map (matP cc lift n) := by
    refine List.mem_map.2 ⟨pk E p, ?_, rfl⟩
    rw [pk_eq H]
    have e : E[p.idx] = (E.drop 1)[p.idx - 1]'(by simp; omega) := by
      rw [List.getElem_drop]
      congr 1
      omega
    rw [e]
    exact List.getElem_mem _
  simp only [fixMasks, List.all_cons, List.all_nil, Bool.and_true, hM]
  exact (allImg_sound (oddOK_spec h).2.2.2 _ hmem).trans (Nat.pow_le_pow_right (by norm_num) hb)

theorem n_of_oddOK {T : PT 24} (hT : T = PT.ofGens 24 (gens.map unpk) fuel)
    (h : oddOK cc lift n r fuel gens E Js = true) : T.n = E.length := by
  have e := (packed_of_oddOK hT h).elems
  subst hT
  change (PT.ofGens 24 (gens.map unpk) fuel).elems.size = _
  rw [e]
  simp

theorem arr_of_oddOK {T : PT 24} (hT : T = PT.ofGens 24 (gens.map unpk) fuel)
    (h : oddOK cc lift n r fuel gens E Js = true) (s : T.Elem) :
    s.idx < E.length ∧ T.arr s = unpk (E.getD s.idx 0) := by
  have hs : s.idx < E.length := n_of_oddOK hT h ▸ s.lt
  refine ⟨hs, ?_⟩
  have e : T.arr s = (E.map unpk).toArray[s.idx]! := by
    rw [← (packed_of_oddOK hT h).elems]
    rfl
  rw [e]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs, hs]

theorem tail_of {T : PT 24} (hT : T = PT.ofGens 24 (gens.map unpk) fuel)
    (h : oddOK cc lift n r fuel gens E Js = true) {ok : Array Nat → Bool}
    (ht : tailOK ok cc lift n E = true) {k : Nat} (hk : k < n) (s : T.Elem)
    (hs : ((List.range (2 ^ n)).filter fun m =>
      actM cc (permM (T.arr s) (actM lift m)) == m).length = 2 ^ k) :
    ok (T.arr s) = true := by
  simp only [tailOK, Bool.and_eq_true, List.all_eq_true] at ht
  obtain ⟨hlt, harr⟩ := arr_of_oddOK hT h s
  rcases Nat.eq_zero_or_pos s.idx with h0 | hpos
  · exfalso
    have hK := allKer_sound ht.1 _ (List.mem_singleton_self _)
    have e : (List.range (2 ^ n)).filter (fun m => actM (matP cc lift n (E.getD 0 0)) m == m) =
        (List.range (2 ^ n)).filter fun m => actM cc (permM (T.arr s) (actM lift m)) == m := by
      refine List.filter_congr fun m hm => ?_
      have hf : actP cc lift (E.getD 0 0) = fun m => actM cc (permM (unpk (E.getD 0 0)) (actM lift m)) :=
        funext fun m => (actM_unpk cc lift _ m).symm
      rw [harr, h0, matP, hf, actM_matOf (f := fun m => actM cc (permM (unpk (E.getD 0 0))
        (actM lift m))) (((actM_xor _).comp (actM_xor _)).comp (actM_xor _)) n m
        (List.mem_range.1 hm)]
    rw [e, hs] at hK
    exact absurd hK (Nat.not_le.2 (Nat.pow_lt_pow_right (by norm_num) hk))
  · rw [harr]
    refine ht.2 _ ?_
    have e : E.getD s.idx 0 = (E.drop 1)[s.idx - 1]'(by simp; omega) := by
      rw [List.getElem_drop, List.getD_eq_getElem _ _ hlt]
      congr 1
      omega
    rw [e]
    exact List.getElem_mem _

theorem cube_of {T : PT 24} [Fact (T.check = true)] (H : Packed T E) (h : cubeOK E = true) :
    ∀ p : T.Elem, p * p * p = 1 := by
  intro p
  rw [mul_iff H, pk_mul H, pk_one H]
  unfold cubeOK at h
  rw [List.all_eq_true] at h
  have hp := h (pk E p) (by rw [pk_eq H]; exact List.getElem_mem _)
  exact beq_iff_eq.1 hp

end CFSG.KC.HMathieu

end
