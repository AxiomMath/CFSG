
module

public import CFSG.Certificates.Kernel.HeFixKSnd.Basic
public import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KC.HeFixKSnd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.PSL3Four.Native CFSG.Monster.B.Co2.Native CFSG.KC.HeFixK
open CFSG.ComponentClassification.GrSLit.HeldFix CFSG.Sporadic.SmallOddCore
open CFSG.KLie.CT (fget)

theorem out2_E8_pre {m : Nat} {x y z : Tab} (h : hfE8OK m x y z = true) :
    (comp m x y == comp m y x && !(x == y) && !(x == idTab m) && !(y == idTab m)) = true := by
  unfold hfE8OK at h
  have hyx : (x == y) = (y == x) := Bool.beq_comm
  simp only [Bool.and_eq_true_iff, Bool.not_eq_true', hyx] at h ⊢
  tauto

theorem hfFindE8_isSome {m : Nat} {TT : Array Tab} {C : List Nat} {i j k : Nat}
    (hi : i ∈ C) (hj : j ∈ C) (hk : k ∈ C) (h : hfE8OK m TT[i]! TT[j]! TT[k]! = true) :
    (hfFindE8 m TT C).isSome = true := by
  unfold hfFindE8
  refine List.findSome?_isSome_iff.2 ⟨i, hi, List.findSome?_isSome_iff.2 ⟨j, hj, ?_⟩⟩
  rw [if_pos (out2_E8_pre h)]
  refine List.findSome?_isSome_iff.2 ⟨k, hk, ?_⟩
  simp [h]

theorem hfFindE8_spec {m : Nat} {TT : Array Tab} {C : List Nat} {i j k : Nat}
    (h : hfFindE8 m TT C = some (i, j, k)) :
    i ∈ C ∧ j ∈ C ∧ k ∈ C ∧ hfE8OK m TT[i]! TT[j]! TT[k]! = true := by
  unfold hfFindE8 at h
  obtain ⟨a, ha, h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨b, hb, h2⟩ := List.exists_of_findSome?_eq_some h1
  split at h2
  · obtain ⟨c, hc, h3⟩ := List.exists_of_findSome?_eq_some h2
    split at h3
    · simp only [Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨rfl, rfl, rfl⟩ := h3
      exact ⟨ha, hb, hc, by assumption⟩
    · cases h3
  · cases h2

theorem out2_mem_hfCands {m : Nat} {TT : Array Tab} {a b : Tab} {t : Nat}
    (ht : t < TT.size) (hs : (comp m TT[t]! TT[t]! == idTab m) = true)
    (hc : (comp m TT[t]! a == comp m a TT[t]! && comp m TT[t]! b == comp m b TT[t]!) = true) :
    t ∈ hfCands m TT a b := by
  simp only [Bool.and_eq_true_iff] at hc
  simp only [hfCands, List.mem_filter, List.mem_range, Bool.and_eq_true_iff]
  exact ⟨ht, ⟨hs, hc.1⟩, hc.2⟩

theorem out2_of_mem_hfCands {m : Nat} {TT : Array Tab} {a b : Tab} {t : Nat}
    (ht : t ∈ hfCands m TT a b) :
    t < TT.size ∧ (comp m TT[t]! a == comp m a TT[t]!) = true ∧
      (comp m TT[t]! b == comp m b TT[t]!) = true := by
  simp only [hfCands, List.mem_filter, List.mem_range, Bool.and_eq_true_iff] at ht
  exact ⟨ht.1, ht.2.1.2, ht.2.2⟩

theorem hfPairOK_of_triple {m : Nat} {TT : Array Tab} {a b : Tab} {i j k : Nat}
    (hi : i < TT.size) (hj : j < TT.size) (hk : k < TT.size)
    (he : hfE8OK m TT[i]! TT[j]! TT[k]! = true)
    (hsq : ∀ t ∈ [TT[i]!, TT[j]!, TT[k]!], (comp m t t == idTab m) = true)
    (hc : ∀ t ∈ [TT[i]!, TT[j]!, TT[k]!],
      (comp m t a == comp m a t && comp m t b == comp m b t) = true) :
    hfPairOK m TT a b = true := by
  have hmi := out2_mem_hfCands hi (hsq (TT[i]!) (by simp)) (hc (TT[i]!) (by simp))
  have hmj := out2_mem_hfCands hj (hsq (TT[j]!) (by simp)) (hc (TT[j]!) (by simp))
  have hmk := out2_mem_hfCands hk (hsq (TT[k]!) (by simp)) (hc (TT[k]!) (by simp))
  obtain ⟨⟨i', j', k'⟩, hp⟩ := Option.isSome_iff_exists.mp (hfFindE8_isSome hmi hmj hmk he)
  obtain ⟨h1, h2, h3, h4⟩ := hfFindE8_spec hp
  obtain ⟨l1, a1, b1⟩ := out2_of_mem_hfCands h1
  obtain ⟨l2, a2, b2⟩ := out2_of_mem_hfCands h2
  obtain ⟨l3, a3, b3⟩ := out2_of_mem_hfCands h3
  have hT : hfTripleOK m TT a b i' j' k' = true := by
    simp only [hfTripleOK, Bool.and_eq_true_iff, decide_eq_true_eq, List.all_cons, List.all_nil,
      Bool.and_true, l1, l2, l3, h4, a1, b1, a2, b2, a3, b3, and_self, and_true, true_and]
  unfold hfPairOK
  rw [hp]
  exact hT

theorem tab_comm {x y : Nat} (hx : PP 32 6 x) (hy : PP 32 6 y) :
    (comp 32 (unpack 32 6 x) (unpack 32 6 y) == comp 32 (unpack 32 6 y) (unpack 32 6 x)) =
      comm 32 6 x y := by
  rw [comp_unpack_PP hx hy, comp_unpack_PP hy hx, beq_unpack_PP (hx.mul hy) (hy.mul hx)]
  unfold CFSG.KC.HexaK.comm
  rw [strictB_app, strictB_app]
  rfl

theorem tab_sq {x : Nat} (hx : PP 32 6 x) :
    (comp 32 (unpack 32 6 x) (unpack 32 6 x) == idTab 32) =
      Nat.beq (mul 32 6 x x) (pidn 32 6) := by
  rw [comp_unpack_PP hx hx, idTab_unpack_PP hx.sz, beq_unpack_PP (hx.mul hx) (PP.id hx.sz)]
  rfl

theorem tab_eq_id {x : Nat} (hx : PP 32 6 x) :
    (unpack 32 6 x == idTab 32) = Nat.beq x (pidn 32 6) := by
  rw [idTab_unpack_PP hx.sz, beq_unpack_PP hx (PP.id hx.sz)]

theorem tab_eq_mul {x y z : Nat} (hx : PP 32 6 x) (hy : PP 32 6 y) (hz : PP 32 6 z) :
    (unpack 32 6 z == comp 32 (unpack 32 6 x) (unpack 32 6 y)) = Nat.beq z (mul 32 6 x y) := by
  rw [comp_unpack_PP hx hy, beq_unpack_PP hz (hx.mul hy)]
  rfl

theorem hfE8OK_unpack {x y z : Nat} (hx : PP 32 6 x) (hy : PP 32 6 y) (hz : PP 32 6 z) :
    hfE8OK 32 (unpack 32 6 x) (unpack 32 6 y) (unpack 32 6 z) = e8K x y z := by
  unfold hfE8OK e8K
  rw [strictB_app, tab_sq hx, tab_sq hy, tab_sq hz, tab_comm hx hy, tab_comm hx hz,
    tab_comm hy hz, tab_eq_id hx, tab_eq_id hy, tab_eq_id hz, beq_unpack_PP hy hx,
    beq_unpack_PP hz hx, beq_unpack_PP hz hy, tab_eq_mul hx hy hz]
  simp only [andB_eq, notB_eq, beq_nat, Bool.and_assoc]

@[expose] noncomputable def tabsOf (N : Nat) (T : Nat → Nat) : Array Tab :=
  Array.ofFn (n := N) fun i => unpack 32 6 (T i.val)

theorem tabsOf_size (N : Nat) (T : Nat → Nat) : (tabsOf N T).size = N := by
  unfold tabsOf
  exact Array.size_ofFn

theorem tabsOf_get {N l : Nat} (T : Nat → Nat) (hl : l < N) :
    (tabsOf N T)[l]! = unpack 32 6 (T l) := by
  unfold tabsOf
  exact getElem!_ofFn_lt (fun i : Fin N => unpack 32 6 (T i.val)) hl

theorem hfE8OK_sq {m : Nat} {x y z : Tab} (h : hfE8OK m x y z = true) :
    (comp m x x == idTab m) = true ∧ (comp m y y == idTab m) = true ∧
      (comp m z z == idTab m) = true := by
  simp only [hfE8OK, Bool.and_eq_true] at h
  tauto

theorem hfPairOK_of_ijk {N : Nat} {T : Nat → Nat} {a b i j k : Nat}
    (hT : ∀ i < N, PP 32 6 (T i)) (ha : PP 32 6 a) (hb : PP 32 6 b)
    (hi : i < N) (hj : j < N) (hk : k < N) (he : e8K (T i) (T j) (T k) = true)
    (hxa : comm 32 6 (T i) a = true) (hxb : comm 32 6 (T i) b = true)
    (hya : comm 32 6 (T j) a = true) (hyb : comm 32 6 (T j) b = true)
    (hza : comm 32 6 (T k) a = true) (hzb : comm 32 6 (T k) b = true) :
    hfPairOK 32 (tabsOf N T) (unpack 32 6 a) (unpack 32 6 b) = true := by
  have e8 : hfE8OK 32 (unpack 32 6 (T i)) (unpack 32 6 (T j)) (unpack 32 6 (T k)) = true := by
    rw [hfE8OK_unpack (hT i hi) (hT j hj) (hT k hk)]
    exact he
  have hsq := hfE8OK_sq e8
  refine hfPairOK_of_triple (m := 32) (i := i) (j := j) (k := k) (by rw [tabsOf_size]; exact hi)
    (by rw [tabsOf_size]; exact hj) (by rw [tabsOf_size]; exact hk) ?_ ?_ ?_
  · rw [tabsOf_get T hi, tabsOf_get T hj, tabsOf_get T hk]
    exact e8
  · intro t ht
    rw [tabsOf_get T hi, tabsOf_get T hj, tabsOf_get T hk] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact hsq.1
    · exact hsq.2.1
    · exact hsq.2.2
  · intro t ht
    rw [tabsOf_get T hi, tabsOf_get T hj, tabsOf_get T hk] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rw [Bool.and_eq_true]
    rcases ht with rfl | rfl | rfl
    · rw [tab_comm (hT i hi) ha, tab_comm (hT i hi) hb]
      exact ⟨hxa, hxb⟩
    · rw [tab_comm (hT j hj) ha, tab_comm (hT j hj) hb]
      exact ⟨hya, hyb⟩
    · rw [tab_comm (hT k hk) ha, tab_comm (hT k hk) hb]
      exact ⟨hza, hzb⟩

theorem hfPairOK_of_tripK {N : Nat} {T : Nat → Nat} {a b c : Nat}
    (hT : ∀ i < N, PP 32 6 (T i)) (ha : PP 32 6 a) (hb : PP 32 6 b)
    (h : tripK N T a b c = true) :
    hfPairOK 32 (tabsOf N T) (unpack 32 6 a) (unpack 32 6 b) = true := by
  unfold tripK at h
  simp only [strictB_app, andB_eq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hi, hj, hk, he, ⟨hxa, hxb⟩, ⟨hya, hyb⟩, hza, hzb⟩ := h
  exact hfPairOK_of_ijk hT ha hb hi hj hk he hxa hxb hya hyb hza hzb

end CFSG.KC.HeFixKSnd

end
