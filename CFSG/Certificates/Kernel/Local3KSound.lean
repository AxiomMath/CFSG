module

public import Certificates.Data.Kernel.Local3K
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Co1BMulSound
import CFSG.Sporadic.HS.SmallF2Spec
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Local3Sound

namespace CFSG.KC.Local3K

open CFSG.KC.M1F2 CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.KC.OpsF2K CFSG.Sporadic.SmallF2
open CFSG.KC.Co1F2 (unpackR bind_sound)
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.LocalWitness
open scoped Matrix

theorem seqN_eq {α : Sort _} (y : Nat) (k : Nat → α) : seqN y k = k y := by
  cases y <;> rfl

theorem getD_cases (L : List Nat) (c x : Nat) : L.getD c x ∈ L ∨ L.getD c x = x := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[c]? with
  | none => exact Or.inr rfl
  | some y => exact Or.inl (List.mem_of_getElem? h)

theorem mat_mul (d X Y : Nat) : rowsMatrix d (unpackR d (mulF d X Y)) =
    rowsMatrix d (unpackR d X) * rowsMatrix d (unpackR d Y) :=
  CFSG.KC.LocalComp.Cub.rowsMatrix_unpackR_mulF d X Y

theorem mat_id (d : Nat) : rowsMatrix d (unpackR d (idF d)) = 1 :=
  CFSG.KC.LocalComp.Cub.rowsMatrix_unpackR_idF d

theorem mat_pow {d X e : Nat} (he : e < 65536) :
    rowsMatrix d (unpackR d (powK d X e)) = rowsMatrix d (unpackR d X) ^ e :=
  CFSG.KC.LocalComp.Cub.rowsMatrix_powF (nb := 16) (by norm_num; exact he)

theorem vec_vmF (d X v : Nat) :
    toVecD d (vmF d X v) = toVecD d v ᵥ* rowsMatrix d (unpackR d X) := by
  rw [← CFSG.KC.F2W.vecMulN_unpackR]
  exact toVecD_vecMulN d _ _

theorem mod_eq_of_toVecD {d u w : Nat} (h : toVecD d u = toVecD d w) : u % 2 ^ d = w % 2 ^ d := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < d
  · have := congrFun h ⟨j, hj⟩
    simp only [toVecD_apply] at this
    simp only [hj, decide_true, Bool.true_and]
    cases hu : u.testBit j <;> cases hw : w.testBit j <;> simp_all
  · simp [hj]

variable {d : Nat} {S : Submonoid (Matrix (Fin d) (Fin d) (ZMod 2))}

theorem evalLettersK_mem {L : List Nat} (hL : ∀ X ∈ L, rowsMatrix d (unpackR d X) ∈ S) :
    ∀ w : List Nat, rowsMatrix d (unpackR d (evalLettersK d L w)) ∈ S
  | [] => by
    rw [evalLettersK, mat_id]
    exact S.one_mem
  | c :: w => by
    rw [evalLettersK, mat_mul]
    refine S.mul_mem ?_ (evalLettersK_mem hL w)
    rcases getD_cases L c (idF d) with h | h
    · exact hL _ h
    · rw [h, mat_id]
      exact S.one_mem

theorem extendLettersK_mem : ∀ (ds : List (List Nat)) {L : List Nat},
    (∀ X ∈ L, rowsMatrix d (unpackR d X) ∈ S) →
      ∀ X ∈ extendLettersK d L ds, rowsMatrix d (unpackR d X) ∈ S
  | [], _, hL => hL
  | w :: ws, L, hL => by
    rw [extendLettersK]
    refine extendLettersK_mem ws fun X hX => ?_
    rcases List.mem_append.1 hX with hX | hX
    · exact hL X hX
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact evalLettersK_mem hL w
      · exact evalLettersK_mem hL _

theorem evalGenK_mat {m : Nat} {x : Fin m → Sˣ} {G Gi : List Nat}
    (hG : ∀ i : Fin m, rowsMatrix d (unpackR d (G.getD i (idF d))) = valHom S (x i))
    (hGi : ∀ i : Fin m, rowsMatrix d (unpackR d (Gi.getD i (idF d))) = valHom S (x i)⁻¹) :
    ∀ w : List (Fin m × Bool), rowsMatrix d (unpackR d (evalGenK d G Gi w)) =
      valHom S (FreeGroup.lift x (FreeGroup.mk w))
  | [] => by
    rw [evalGenK, mat_id, ← FreeGroup.one_eq_mk, map_one, map_one]
  | (i, b) :: w => by
    have e : FreeGroup.lift x (FreeGroup.mk ((i, b) :: w)) =
        (if b then x i else (x i)⁻¹) * FreeGroup.lift x (FreeGroup.mk w) := by
      rw [FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_cons, List.prod_cons]
      cases b <;> rfl
    rw [e, map_mul, ← evalGenK_mat hG hGi w]
    cases b
    · rw [evalGenK, mat_mul, hGi]
      rfl
    · rw [evalGenK, mat_mul, hG]
      rfl

theorem childrenK_inv (P : Nat → Prop) (d k v : Nat) : ∀ (G : List Nat) (g : Nat) (acc : List Nat),
    (∀ X ∈ G, P (vmF d X v)) → (∀ y ∈ acc, P y) → ∀ y ∈ childrenK d k v g G acc, P y
  | [], _, _, _, hacc => by
    intro y hy
    rw [childrenK] at hy
    exact hacc y hy
  | X :: G, g, acc, hX, hacc => by
    intro y hy
    rw [childrenK] at hy
    have hX' : ∀ X' ∈ G, P (vmF d X' v) := fun X' h => hX X' (List.mem_cons_of_mem _ h)
    split_ifs at hy
    · rw [seqN_eq] at hy
      refine childrenK_inv P d k v G (g + 1) _ hX' (fun z hz => ?_) y hy
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hX X (List.mem_cons.2 (Or.inl rfl))
      · exact hacc z hz
    · exact childrenK_inv P d k v G (g + 1) acc hX' hacc y hy

theorem orbK_inv (P : Nat → Prop) {d n : Nat} {G : List Nat}
    (hstep : ∀ v, P v → ∀ X ∈ G, P (vmF d X v)) :
    ∀ (fuel c : Nat) (front back ds out res : List Nat), (∀ v ∈ front, P v) →
      (∀ v ∈ back, P v) → (∀ v ∈ out, P v) → orbK d n G fuel c front back ds out = some res →
        ∀ v ∈ res, P v
  | 0, _, _, _, _, out, res, _, _, ho, h => by
    change some out = some res at h
    cases h
    exact ho
  | f + 1, c, front, back, ds, out, res, hf, hb, ho, h => by
    rw [orbK.eq_def] at h
    dsimp only at h
    split_ifs at h with hc
    · cases h
      exact ho
    · rcases front with _ | ⟨v0, vs⟩
      · rcases back with _ | ⟨b, bs⟩
        · simp at h
        · exact orbK_inv P hstep f c _ [] ds out res
            (fun v hv => hb v (List.mem_reverse.1 hv)) (fun v hv => absurd hv List.not_mem_nil) ho h
      · rcases ds with _ | ⟨k, ds⟩
        · simp at h
        · have hcs : ∀ y ∈ childrenK d k v0 0 G [], P y :=
            childrenK_inv P d k v0 G 0 [] (hstep v0 (hf v0 (List.mem_cons.2 (Or.inl rfl))))
              (fun _ h => absurd h List.not_mem_nil)
          simp only [seqN_eq] at h
          refine orbK_inv P hstep f _ vs _ ds _ res
            (fun v hv => hf v (List.mem_cons_of_mem _ hv)) (fun v hv => ?_) (fun v hv => ?_) h
          · rcases List.mem_append.1 hv with hv | hv
            · exact hcs v hv
            · exact hb v hv
          · rcases List.mem_append.1 hv with hv | hv
            · exact hcs v hv
            · exact ho v hv

theorem mergeK_perm : ∀ (f : Nat) (a b : List Nat), (mergeK f a b).Perm (a ++ b)
  | 0, a, b => by
    rw [mergeK]
  | _ + 1, [], b => by
    rw [mergeK]
    exact List.Perm.refl _
  | _ + 1, x :: a, [] => by
    rw [mergeK, List.append_nil]
    exact fun h => List.cons_ne_nil _ _ h
  | f + 1, x :: a, y :: b => by
    rw [mergeK]
    split_ifs
    · exact (mergeK_perm f a (y :: b)).cons x
    · exact ((mergeK_perm f (x :: a) b).cons y).trans List.perm_middle.symm

theorem mergePairsK_perm : ∀ ls : List (List Nat), (mergePairsK ls).flatten.Perm ls.flatten
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | a :: b :: ls => by
    rw [mergePairsK, List.flatten_cons, List.flatten_cons, List.flatten_cons, ← List.append_assoc]
    exact (mergeK_perm _ a b).append (mergePairsK_perm ls)

theorem mergeRoundsK_perm : ∀ (f : Nat) (ls : List (List Nat)),
    (mergeRoundsK f ls).flatten.Perm ls.flatten
  | 0, _ => List.Perm.refl _
  | f + 1, ls => (mergeRoundsK_perm f _).trans (mergePairsK_perm ls)

theorem flatten_singletons : ∀ l : List Nat, (l.map fun x => [x]).flatten = l
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_singletons l]
    rfl

theorem sortK_perm {l s : List Nat} (h : sortK l = some s) : s.Perm l := by
  have hp := mergeRoundsK_perm 64 (l.map fun x => [x])
  rw [flatten_singletons] at hp
  unfold sortK at h
  generalize mergeRoundsK 64 (l.map fun x => [x]) = r at h hp
  rcases r with _ | ⟨s', _ | ⟨t, r⟩⟩
  · simp only [Option.some.injEq] at h
    subst h
    exact hp
  · simp only [Option.some.injEq] at h
    subst h
    simpa using hp
  · simp at h

end CFSG.KC.Local3K

public section

namespace CFSG.KC.Local3K

open CFSG.KC.M1F2 CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
open CFSG.KC.OpsF2K CFSG.Sporadic.SmallF2
open CFSG.KC.Co1F2 (unpackR bind_sound)
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.LocalWitness
open scoped Matrix

theorem exists_local3_of_K {d A B : Nat} {csA csB ms : List Char} {m : Nat} {D : Local3Data m}
    {root : Nat} (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (hms : D.masks = String.ofList ms) (h : local3K d A B ms D root = true) :
    ∃ x : Fin m → (CFSG.Blueprint.NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB)ˣ,
      (∀ r ∈ D.rels, FreeGroup.lift x (FreeGroup.mk r) = 1) ∧
      (∀ i : Fin m, x i ^ D.ords.getD i 0 = 1) ∧
      D.n ≤ Nat.card (Subgroup.closure (Set.range x)) := by
  classical
  clear hms
  set S := CFSG.Blueprint.NativeSporadic.seedMonoid 2 d 1 D.seedA D.seedB with hS
  unfold local3K at h
  generalize hGd : gensK d A B D = G at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hord, hrel⟩, horb⟩ := h
  unfold ordsK at hord
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hord
  obtain ⟨⟨⟨⟨⟨⟨-, hoA⟩, hoB⟩, hlen⟩, -⟩, -⟩, hords⟩ := hord
  have eA : rowsMatrix d (unpackR d A) = CFSG.Blueprint.NativeSporadic.decode 2 d 1 D.seedA := by
    rw [hsA, ← bind_sound hA]
    exact rowsMatrix_rowsOfPayload d _
  have eB : rowsMatrix d (unpackR d B) = CFSG.Blueprint.NativeSporadic.decode 2 d 1 D.seedB := by
    rw [hsB, ← bind_sound hB]
    exact rowsMatrix_rowsOfPayload d _
  have mA : rowsMatrix d (unpackR d A) ∈ S := by
    rw [eA]
    exact Submonoid.subset_closure (Set.mem_insert _ _)
  have mB : rowsMatrix d (unpackR d B) ∈ S := by
    rw [eB]
    exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hL0 : ∀ X ∈ [A, powK d A (D.oA - 1), B, powK d B (D.oB - 1)],
      rowsMatrix d (unpackR d X) ∈ S := by
    intro X hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl
    · exact mA
    · rw [mat_pow hoA]
      exact S.pow_mem mA _
    · exact mB
    · rw [mat_pow hoB]
      exact S.pow_mem mB _
  have hGS : ∀ X ∈ G, rowsMatrix d (unpackR d X) ∈ S := by
    intro X hX
    rw [← hGd] at hX
    unfold gensK at hX
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hX
    exact evalLettersK_mem (extendLettersK_mem D.defs hL0) w
  have hGlen : G.length = m := by
    rw [← hGd]
    unfold gensK
    rw [List.length_map, hlen]
  have hGi_mem : ∀ i : Fin m, rowsMatrix d (unpackR d (G.getD i (idF d))) ∈ S := by
    intro i
    rcases getD_cases G i (idF d) with h | h
    · exact hGS _ h
    · rw [h, mat_id]
      exact S.one_mem
  have hne : ∀ i : Fin m, D.ords.getD i 0 ≠ 0 := fun i => (hords i i.2).1.1.1
  have hlt : ∀ i : Fin m, D.ords.getD i 0 < 65536 := fun i => (hords i i.2).1.2
  have hpow : ∀ i : Fin m, rowsMatrix d (unpackR d (G.getD i (idF d))) ^ D.ords.getD i 0 = 1 := by
    intro i
    have e := congrArg (fun X => rowsMatrix d (unpackR d X))
      (Nat.eq_of_beq_eq_true (hords i i.2).2)
    rw [mat_pow (hlt i), mat_id] at e
    exact e
  let x : Fin m → Sˣ := fun i => unitOf S (hGi_mem i) (hne i) (hpow i)
  have hxval : ∀ i : Fin m, rowsMatrix d (unpackR d (G.getD i (idF d))) = valHom S (x i) :=
    fun i => (valHom_unitOf S _ _ _).symm
  have hxpow : ∀ i : Fin m, x i ^ D.ords.getD i 0 = 1 := fun i => unitOf_pow S _ _ _
  have hxinv : ∀ i : Fin m,
      rowsMatrix d (unpackR d ((invsK d D G).getD i (idF d))) = valHom S (x i)⁻¹ := by
    intro i
    have e : (invsK d D G).getD i (idF d) = powK d (G.getD i (idF d)) (D.ords.getD i 0 - 1) := by
      unfold invsK
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]
    rw [e, mat_pow (by have := hlt i; omega), hxval, valHom_inv_of_pow S (hne i) (hxpow i)]
  have : Finite Sˣ := Finite.of_injective (valHom S) (valHom_injective S)
  refine ⟨x, fun r hr => ?_, hxpow, ?_⟩
  · unfold relsK at hrel
    rw [List.all_eq_true] at hrel
    have e := congrArg (fun X => rowsMatrix d (unpackR d X)) (Nat.eq_of_beq_eq_true (hrel r hr))
    rw [evalGenK_mat hxval hxinv, mat_id, ← map_one (valHom S)] at e
    exact valHom_injective S e
  ·
    let P : Nat → Prop := fun v => ∃ g ∈ Subgroup.closure (Set.range x),
      toVecD d v = toVecD d root ᵥ* valHom S g
    have hstep : ∀ v, P v → ∀ X ∈ G, P (vmF d X v) := by
      rintro v ⟨g, hg, hv⟩ X hX
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hX
      have hj' : j < m := by rw [← hGlen]; exact hj
      have hXj : G[j] = G.getD (⟨j, hj'⟩ : Fin m) (idF d) := (List.getD_eq_getElem _ _ hj).symm
      refine ⟨g * x ⟨j, hj'⟩, Subgroup.mul_mem _ hg (Subgroup.subset_closure ⟨_, rfl⟩), ?_⟩
      rw [vec_vmF, hv, hXj, hxval, Matrix.vecMul_vecMul, map_mul]
    have hroot : P root := ⟨1, Subgroup.one_mem _, by rw [map_one, Matrix.vecMul_one]⟩
    unfold orbitK at horb
    rw [Bool.and_eq_true, decide_eq_true_eq] at horb
    obtain ⟨-, horb⟩ := horb
    generalize hres : orbK d D.n G (2 * D.n + 2) 1 [root] [] (ms.map fun c => c.toNat - 48) [root]
      = res at horb
    rcases res with _ | out
    · exact absurd horb Bool.false_ne_true
    have hout := orbK_inv P hstep _ _ _ _ _ _ out
      (fun v hv => by rw [List.mem_singleton.1 hv]; exact hroot)
      (fun v hv => absurd hv List.not_mem_nil)
      (fun v hv => by rw [List.mem_singleton.1 hv]; exact hroot) hres
    change (decide (D.n ≤ out.length) && _) = true at horb
    rw [Bool.and_eq_true, decide_eq_true_eq] at horb
    obtain ⟨hn, horb⟩ := horb
    generalize hsort : sortK ((out.reverse.take D.n).map fun v => v % 2 ^ d) = so at horb
    rcases so with _ | s
    · exact absurd horb Bool.false_ne_true
    have hnd : ((out.reverse.take D.n).map fun v => v % 2 ^ d).Nodup :=
      (sortK_perm hsort).nodup_iff.1 (strictInc_nodup horb)
    set ws := out.reverse.take D.n with hws
    have hwlen : ws.length = D.n := by
      rw [hws, List.length_take, List.length_reverse]
      omega
    have hsem : ∀ i : Fin D.n, P (ws[i.val]'(by rw [hwlen]; exact i.2)) := by
      intro i
      refine hout _ (List.mem_reverse.1 (List.mem_of_mem_take (List.getElem_mem _)))
    choose g hg hv using hsem
    let F : Fin D.n → Subgroup.closure (Set.range x) := fun i => ⟨g i, hg i⟩
    have hF : Function.Injective F := by
      intro i j hij
      have hgij : g i = g j := congrArg Subtype.val hij
      have hveq := mod_eq_of_toVecD (Eq.trans (hv i) (Eq.trans
        (congrArg (fun g' => toVecD d root ᵥ* valHom S g') hgij) (hv j).symm))
      have hlen : ∀ k : Fin D.n, k.val < (ws.map fun v => v % 2 ^ d).length := fun k => by
        rw [List.length_map, hwlen]
        exact k.2
      have := (hnd.getElem_inj_iff (hi := hlen i) (hj := hlen j)).1
        (by rw [List.getElem_map, List.getElem_map]; exact hveq)
      exact Fin.ext this
    calc D.n = Nat.card (Fin D.n) := by simp
      _ ≤ Nat.card (Subgroup.closure (Set.range x)) := Nat.card_le_card_of_injective F hF

end CFSG.KC.Local3K

end
