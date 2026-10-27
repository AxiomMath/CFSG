module

public import Certificates.Data.Kernel.HMathieu.Roots
public import CFSG.Certificates.Kernel.HMathieu.BfsSound
public import CFSG.Certificates.Kernel.TreeKSound
public import CFSG.Certificates.Kernel.MathieuAut.InAutKSound
public import CFSG.Quasithin.Background.HMathieuPT24

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.KS.MathieuAut

theorem hasArr_unpk_iff {σ : Equiv.Perm (Fin 24)} {x : Nat} :
    HasArr σ (unpk x) ↔ ∀ i : Fin 24, (σ i : Nat) = pg 5 (mask 5) x i :=
  forall_congr' fun i => by rw [unpk_get x i.2]

theorem hasArr_one : HasArr 1 (unpk (pidn 24 5)) :=
  hasArr_unpk_iff.2 fun i => by rw [pg_id i.2]; rfl

theorem hasArr_mul {σ τ : Equiv.Perm (Fin 24)} {x y : Nat} (hx : HasArr σ (unpk x))
    (hy : HasArr τ (unpk y)) : HasArr (σ * τ) (unpk (pc24 x y)) := by
  rw [hasArr_unpk_iff] at hx hy ⊢
  intro i
  rw [pg_pc24 x y i.2, Equiv.Perm.mul_apply, hx, hy]

theorem invPairOK_of_hasArr {σ : Equiv.Perm (Fin 24)} {a b : Array Nat} (ha : HasArr σ a)
    (hb : HasArr σ⁻¹ b) : InvPairOK 24 a b = true := by
  unfold InvPairOK
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have e1 : a[i]! = σ ⟨i, hi'⟩ := (ha ⟨i, hi'⟩).symm
  have e2 : b[i]! = σ⁻¹ ⟨i, hi'⟩ := (hb ⟨i, hi'⟩).symm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [e1]
    exact (σ _).2
  · rw [e2]
    exact (σ⁻¹ _).2
  · rw [e2, ← ha (σ⁻¹ ⟨i, hi'⟩)]
    simp
  · rw [e1, ← hb (σ ⟨i, hi'⟩)]
    simp

theorem size_invArr (a : Array Nat) : (invArr a).size = 24 := by
  unfold invArr
  rw [size_foldl_set (fun i => a[i]!)]
  simp

theorem invArr_eq {σ : Equiv.Perm (Fin 24)} {a b : Array Nat} (ha : HasArr σ a)
    (hb : HasArr σ⁻¹ b) (hbs : b.size = 24) : invArr a = b := by
  have hlt : ∀ i < 24, a[i]! < 24 := fun i hi => by
    rw [← ha ⟨i, hi⟩]
    exact (σ _).2
  have hinj : ∀ i < 24, ∀ j < 24, a[i]! = a[j]! → i = j := fun i hi j hj e => by
    rw [← ha ⟨i, hi⟩, ← ha ⟨j, hj⟩] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))
  have key : ∀ v < 24, (invArr a)[v]! = b[v]! := fun v hv => by
    have hav : a[((σ⁻¹ ⟨v, hv⟩ : Fin 24) : Nat)]! = v := by
      rw [← ha (σ⁻¹ ⟨v, hv⟩)]
      simp
    have hbv : b[v]! = σ⁻¹ ⟨v, hv⟩ := (hb ⟨v, hv⟩).symm
    exact (congrArg (fun k => (invArr a)[k]!) hav.symm).trans
      ((invArr_getElem hlt hinj _ (σ⁻¹ ⟨v, hv⟩).2).trans hbv.symm)
  have hsz : (invArr a).size = b.size := (size_invArr a).trans hbs.symm
  generalize invArr a = c at key hsz ⊢
  refine Array.ext hsz fun i h1 h2 => ?_
  have hi : i < 24 := hbs ▸ hsz ▸ h1
  exact ((getElem!_pos c i h1).symm.trans (key i hi)).trans (getElem!_pos b i h2)

inductive GReach (gs : List Nat) : Nat → Prop
  | id : GReach gs (pidn 24 5)
  | step {g x : Nat} : g ∈ gs → GReach gs x → GReach gs (pc24 g x)

theorem GReach.vpK {gs : List Nat} (hvG : ∀ g ∈ gs, vpK g = true) {x : Nat} (h : GReach gs x) :
    vpK x = true := by
  induction h with
  | id => exact vpK_id
  | step hg _ ih => exact vpK_pc24 (hvG _ hg) ih

theorem GReach.hasArr {gs : List Nat} (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hgΓ : ∀ g ∈ gs, ∃ σ ∈ Γ, HasArr σ (unpk g)) {x : Nat} (h : GReach gs x) :
    ∃ σ ∈ Γ, HasArr σ (unpk x) := by
  induction h with
  | id => exact ⟨1, Γ.one_mem, hasArr_one⟩
  | step hg _ ih =>
    obtain ⟨σ, hσ, hs⟩ := hgΓ _ hg
    obtain ⟨τ, hτ, ht⟩ := ih
    exact ⟨σ * τ, Γ.mul_mem hσ hτ, hasArr_mul hs ht⟩

@[expose] noncomputable def bstepG (x : Nat) (st : List Nat × List Nat) (g : Nat) :
    List Nat × List Nat :=
  if st.1.contains (pc24 g x) then st else (pc24 g x :: st.1, pc24 g x :: st.2)

theorem bfsStep_eq (gs : List Nat) (st : List Nat × List Nat) (x : Nat) :
    bfsStep gs st x = gs.foldl (bstepG x) st := rfl

theorem bstep_inv {gs : List Nat} {x : Nat} (hx : GReach gs x) : ∀ (hs : List Nat),
    (∀ g ∈ hs, g ∈ gs) → ∀ st : List Nat × List Nat, (∀ y ∈ st.1, GReach gs y) →
      (∀ y ∈ st.2, GReach gs y) →
      (∀ y ∈ (hs.foldl (bstepG x) st).1, GReach gs y) ∧
        (∀ y ∈ (hs.foldl (bstepG x) st).2, GReach gs y) ∧
          ∃ S, (hs.foldl (bstepG x) st).1 = S ++ st.1
  | [], _, _, h1, h2 => ⟨h1, h2, [], rfl⟩
  | g :: hs, hhs, st, h1, h2 => by
    rw [List.foldl_cons]
    have hy : GReach gs (pc24 g x) := GReach.step (hhs g List.mem_cons_self) hx
    have key : (∀ y ∈ (bstepG x st g).1, GReach gs y) ∧ (∀ y ∈ (bstepG x st g).2, GReach gs y) ∧
        ∃ S, (bstepG x st g).1 = S ++ st.1 := by
      unfold bstepG
      split
      · exact ⟨h1, h2, [], rfl⟩
      · refine ⟨fun y hy' => ?_, fun y hy' => ?_, [pc24 g x], rfl⟩
        · rcases List.mem_cons.1 hy' with rfl | h
          · exact hy
          · exact h1 y h
        · rcases List.mem_cons.1 hy' with rfl | h
          · exact hy
          · exact h2 y h
    obtain ⟨k1, k2, S, hS⟩ := key
    obtain ⟨r1, r2, S', hS'⟩ :=
      bstep_inv hx hs (fun g' h => hhs g' (List.mem_cons_of_mem g h)) _ k1 k2
    exact ⟨r1, r2, S' ++ S, by rw [hS', hS, List.append_assoc]⟩

theorem round_inv {gs : List Nat} : ∀ (fr : List Nat), (∀ x ∈ fr, GReach gs x) →
    ∀ st : List Nat × List Nat, (∀ y ∈ st.1, GReach gs y) → (∀ y ∈ st.2, GReach gs y) →
      (∀ y ∈ (fr.foldl (bfsStep gs) st).1, GReach gs y) ∧
        (∀ y ∈ (fr.foldl (bfsStep gs) st).2, GReach gs y) ∧
          ∃ S, (fr.foldl (bfsStep gs) st).1 = S ++ st.1
  | [], _, _, h1, h2 => ⟨h1, h2, [], rfl⟩
  | x :: fr, hfr, st, h1, h2 => by
    rw [List.foldl_cons, bfsStep_eq]
    obtain ⟨k1, k2, S, hS⟩ := bstep_inv (hfr x List.mem_cons_self) gs (fun _ h => h) st h1 h2
    obtain ⟨r1, r2, S', hS'⟩ :=
      round_inv fr (fun y h => hfr y (List.mem_cons_of_mem x h)) _ k1 k2
    exact ⟨r1, r2, S' ++ S, by rw [hS', hS, List.append_assoc]⟩

theorem bfsP_inv {gs : List Nat} : ∀ (fuel : Nat) (acc fr : List Nat),
    (∀ y ∈ acc, GReach gs y) → (∀ y ∈ fr, GReach gs y) →
      (∀ y ∈ bfsP gs fuel acc fr, GReach gs y) ∧ ∃ S, bfsP gs fuel acc fr = S ++ acc
  | 0, acc, fr, h1, _ => by
    rw [bfsP]
    exact ⟨h1, [], rfl⟩
  | f + 1, acc, [], h1, _ => by
    rw [bfsP]
    exact ⟨h1, [], rfl⟩
  | f + 1, acc, x :: xs, h1, h2 => by
    rw [bfsP]
    obtain ⟨k1, k2, S, hS⟩ := round_inv (x :: xs) h2 (acc, []) h1 (by simp)
    obtain ⟨r, S', hS'⟩ := bfsP_inv f _ _ k1 (fun y hy => k2 y (List.mem_reverse.1 hy))
    exact ⟨r, S' ++ S, by rw [hS', hS, List.append_assoc]⟩

theorem reach_of_bfs {gs E : List Nat} {fuel : Nat}
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (∀ y ∈ E, GReach gs y) ∧ E = pidn 24 5 :: E.tail := by
  have hi : ∀ y ∈ [pidn 24 5], GReach gs y := fun y hy => by
    rw [List.mem_singleton.1 hy]
    exact GReach.id
  obtain ⟨hR, S, hS⟩ := bfsP_inv fuel _ _ hi hi
  refine ⟨fun y hy => hR y (List.mem_reverse.1 (hbfs ▸ hy)), ?_⟩
  rw [← hbfs, hS, List.reverse_append]
  rfl

theorem pc24_id_left {y : Nat} (hy : vpK y = true) : pc24 (pidn 24 5) y = y :=
  eq_of_pg (vpK_pc24 vpK_id hy) hy fun i hi => by
    rw [pg_pc24 _ _ hi, pg_id ((vpK_spec hy).2 i hi)]

theorem pc24_assoc {p q r : Nat} (hp : vpK p = true) (hq : vpK q = true) (hr : vpK r = true) :
    pc24 (pc24 p q) r = pc24 p (pc24 q r) :=
  eq_of_pg (vpK_pc24 (vpK_pc24 hp hq) hr) (vpK_pc24 hp (vpK_pc24 hq hr)) fun i hi => by
    rw [pg_pc24 _ _ hi, pg_pc24 _ _ ((vpK_spec hr).2 i hi), pg_pc24 p _ hi, pg_pc24 q r hi]

theorem mem_of_closedK {gs E : List Nat} {np : Nat}
    (hcl : CFSG.KC.TreeK.closedK (fun l x => pc24 (gs.getD l 0) x) gs.length np E = true)
    {g y : Nat} (hg : g ∈ gs) (hy : y ∈ E) : pc24 g y ∈ E := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hg
  have := CFSG.KC.TreeK.closedK_sound hcl y hy l hl
  simpa [List.getD_eq_getElem?_getD, hl] using this

theorem mul_mem {gs E : List Nat} {np : Nat}
    (hcl : CFSG.KC.TreeK.closedK (fun l x => pc24 (gs.getD l 0) x) gs.length np E = true)
    (hvG : ∀ g ∈ gs, vpK g = true) (hvE : ∀ e ∈ E, vpK e = true) {x : Nat} (hx : GReach gs x) :
    ∀ y ∈ E, pc24 x y ∈ E := by
  induction hx with
  | id =>
    intro y hy
    rw [pc24_id_left (hvE y hy)]
    exact hy
  | step hg h ih =>
    intro y hy
    rw [pc24_assoc (hvG _ hg) (h.vpK hvG) (hvE y hy)]
    exact mem_of_closedK hcl hg (ih y hy)

@[expose] noncomputable def ppow (x : Nat) : Nat → Nat
  | 0 => pidn 24 5
  | k + 1 => pc24 x (ppow x k)

theorem ppow_mem {E : List Nat} {x : Nat} (hid : pidn 24 5 ∈ E) (hmul : ∀ y ∈ E, pc24 x y ∈ E) :
    ∀ k, ppow x k ∈ E
  | 0 => hid
  | k + 1 => hmul _ (ppow_mem hid hmul k)

theorem hasArr_ppow {σ : Equiv.Perm (Fin 24)} {x : Nat} (hx : HasArr σ (unpk x)) :
    ∀ k, HasArr (σ ^ k) (unpk (ppow x k))
  | 0 => by
    rw [pow_zero]
    exact hasArr_one
  | k + 1 => by
    rw [pow_succ']
    exact hasArr_mul hx (hasArr_ppow hx k)

theorem exists_inv {gs E : List Nat} {fuel np : Nat} (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hgΓ : ∀ g ∈ gs, ∃ σ ∈ Γ, HasArr σ (unpk g)) (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hcl : CFSG.KC.TreeK.closedK (fun l x => pc24 (gs.getD l 0) x) gs.length np E = true)
    {x : Nat} (hx : x ∈ E) :
    ∃ y ∈ E, ∃ σ ∈ Γ, HasArr σ (unpk x) ∧ HasArr σ⁻¹ (unpk y) := by
  obtain ⟨hR, hE⟩ := reach_of_bfs hbfs
  have hid : pidn 24 5 ∈ E := by
    rw [hE]
    exact List.mem_cons_self
  obtain ⟨σ, hσ, hs⟩ := (hR x hx).hasArr Γ hgΓ
  have hvE : ∀ e ∈ E, vpK e = true := fun e he => (hR e he).vpK hvG
  refine ⟨ppow x (orderOf σ - 1), ppow_mem hid (mul_mem hcl hvG hvE (hR x hx)) _, σ, hσ, hs, ?_⟩
  have e : σ ^ (orderOf σ - 1) = σ⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos σ),
      pow_orderOf_eq_one]
  rw [← e]
  exact hasArr_ppow hs _

theorem index_getD (els : Array (Array Nat))
    (hnd : ∀ i < els.size, ∀ j < els.size, els[i]! = els[j]! → i = j) :
    ∀ j < els.size, ((List.range els.size).foldl (fun m i => m.insert els[i]! i)
      (∅ : Std.HashMap (Array Nat) Nat)).getD els[j]! 0 = j := by
  have key : ∀ k ≤ els.size, ∀ j < k, ((List.range k).foldl (fun m i => m.insert els[i]! i)
      (∅ : Std.HashMap (Array Nat) Nat)).getD els[j]! 0 = j := by
    intro k
    induction k with
    | zero => exact fun _ j hj => absurd hj (Nat.not_lt_zero _)
    | succ k ih =>
      intro hk j hj
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getD_insert]
      by_cases hjk : j = k
      · subst hjk
        simp
      · have hne : (els[k]! == els[j]!) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun e => hjk (hnd k (by omega) j (by omega) e).symm
        rw [hne]
        exact ih (by omega) j (by omega)
  exact fun j hj => key _ le_rfl j hj

theorem getElem!_map_toArray (E : List Nat) {k : Nat} (hk : k < E.length) :
    (E.map unpk).toArray[k]! = unpk E[k] := by
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

structure Closure (gs E : List Nat) (Γ : Subgroup (Equiv.Perm (Fin 24))) : Prop where
  nodup : E.Nodup
  vp : ∀ e ∈ E, vpK e = true
  head : E = pidn 24 5 :: E.tail
  mul : ∀ x ∈ E, ∀ y ∈ E, pc24 x y ∈ E
  inv : ∀ x ∈ E, ∃ y ∈ E, ∃ σ ∈ Γ, HasArr σ (unpk x) ∧ HasArr σ⁻¹ (unpk y)

theorem closure_of {gs E : List Nat} {fuel np : Nat} (Γ : Subgroup (Equiv.Perm (Fin 24)))
    (hgΓ : ∀ g ∈ gs, ∃ σ ∈ Γ, HasArr σ (unpk g)) (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hcl : CFSG.KC.TreeK.closedK (fun l x => pc24 (gs.getD l 0) x) gs.length np E = true) :
    Closure gs E Γ := by
  obtain ⟨hR, hE⟩ := reach_of_bfs hbfs
  have hvE : ∀ e ∈ E, vpK e = true := fun e he => (hR e he).vpK hvG
  have hS : CFSG.KLie.CT.andB (CFSG.KC.TreeK.sincK (CFSG.KC.TreeK.sortP np E))
      (CFSG.KC.TreeK.subS (CFSG.KC.TreeK.sortP np (CFSG.KC.TreeK.imagesK
        (fun l x => pc24 (gs.getD l 0) x) gs.length E)) (CFSG.KC.TreeK.sortP np E)) = true := hcl
  have hnd : E.Nodup := (CFSG.KC.TreeK.sortP_perm np E).nodup_iff.1
    (CFSG.KC.TreeK.sincGo_sound _ none (CFSG.KC.TreeK.andB_true hS).1).1
  exact ⟨hnd, hvE, hE, fun x hx => mul_mem hcl hvG hvE (hR x hx),
    fun x hx => exists_inv Γ hgΓ hvG hbfs hcl hx⟩

variable {gs E : List Nat} {fuel : Nat} {Γ : Subgroup (Equiv.Perm (Fin 24))}

theorem elems_ofGens (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (PT.ofGens 24 (gs.map unpk) fuel).elems = (E.map unpk).toArray := by
  change bfsClosure 24 (gs.map unpk) fuel = _
  rw [bfsClosure_eq hvG, hbfs]

theorem n_ofGens (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (PT.ofGens 24 (gs.map unpk) fuel).n = E.length := by
  change (PT.ofGens 24 (gs.map unpk) fuel).elems.size = _
  rw [elems_ofGens hvG hbfs]
  simp

theorem lookup_ofGens (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) (H : Closure gs E Γ) {x : Nat}
    (hx : x ∈ E) :
    ((List.range (PT.ofGens 24 (gs.map unpk) fuel).elems.size).foldl
      (fun m i => m.insert (PT.ofGens 24 (gs.map unpk) fuel).elems[i]! i)
      (∅ : Std.HashMap (Array Nat) Nat)).getD (unpk x) 0 = E.idxOf x := by
  have hels := elems_ofGens hvG hbfs
  have hlen : (PT.ofGens 24 (gs.map unpk) fuel).elems.size = E.length := by rw [hels]; simp
  have hi : E.idxOf x < E.length := List.idxOf_lt_length_of_mem hx
  have hget : (PT.ofGens 24 (gs.map unpk) fuel).elems[E.idxOf x]! = unpk x := by
    rw [hels, getElem!_map_toArray E hi, List.getElem_idxOf]
  rw [← hget]
  refine index_getD _ (fun i hi' j hj' e => ?_) _ (by rw [hlen]; exact hi)
  rw [hlen] at hi' hj'
  rw [hels, getElem!_map_toArray E hi', getElem!_map_toArray E hj'] at e
  exact (H.nodup.getElem_inj_iff).1
    (unpk_inj (H.vp _ (List.getElem_mem _)) (H.vp _ (List.getElem_mem _)) e)

theorem inv_ofGens (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) (H : Closure gs E Γ) {p : Nat}
    (hp : p < E.length) :
    ∃ σ ∈ Γ, HasArr σ ((PT.ofGens 24 (gs.map unpk) fuel).elems[p]!) ∧
      HasArr σ⁻¹ ((PT.ofGens 24 (gs.map unpk) fuel).elems[
        (PT.ofGens 24 (gs.map unpk) fuel).invIdx p]!) := by
  have hels := elems_ofGens hvG hbfs
  have hn := n_ofGens hvG hbfs
  obtain ⟨y, hy, σ, hσ, hs, hsi⟩ := H.inv _ (List.getElem_mem hp)
  have hiy : E.idxOf y < E.length := List.idxOf_lt_length_of_mem hy
  have hinv : (PT.ofGens 24 (gs.map unpk) fuel).invIdx p = E.idxOf y := by
    unfold PT.invIdx
    rw [hn]
    have e : (PT.ofGens 24 (gs.map unpk) fuel).invT[p]! =
        ((List.range (PT.ofGens 24 (gs.map unpk) fuel).elems.size).foldl
          (fun m i => m.insert (PT.ofGens 24 (gs.map unpk) fuel).elems[i]! i)
          (∅ : Std.HashMap (Array Nat) Nat)).getD
          (invArr ((PT.ofGens 24 (gs.map unpk) fuel).elems[p]!)) 0 := by
      change (bfsClosure 24 (gs.map unpk) fuel |>.map fun a => _)[p]! = _
      have hs' : p < (bfsClosure 24 (gs.map unpk) fuel).size := by
        change p < (PT.ofGens 24 (gs.map unpk) fuel).elems.size
        rw [hels]
        simpa using hp
      rw [getElem!_pos _ p (by simpa using hs'), Array.getElem_map, ← getElem!_pos _ p hs']
      rfl
    rw [e, hels, getElem!_map_toArray E hp,
      invArr_eq hs hsi (size_unpk y), ← hels, lookup_ofGens hvG hbfs H hy, Nat.mod_eq_of_lt hiy]
  refine ⟨σ, hσ, ?_, ?_⟩
  · rw [hels, getElem!_map_toArray E hp]
    exact hs
  · rw [hinv, hels, getElem!_map_toArray E hiy, List.getElem_idxOf]
    exact hsi

theorem mul_ofGens (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) (H : Closure gs E Γ) {p q : Nat}
    (hp : p < E.length) (hq : q < E.length) :
    (PT.ofGens 24 (gs.map unpk) fuel).elems[(PT.ofGens 24 (gs.map unpk) fuel).mulIdx p q]! =
      unpk (pc24 E[p] E[q]) := by
  have hels := elems_ofGens hvG hbfs
  have hn := n_ofGens hvG hbfs
  have hz := H.mul _ (List.getElem_mem hp) _ (List.getElem_mem hq)
  have hiz : E.idxOf (pc24 E[p] E[q]) < E.length := List.idxOf_lt_length_of_mem hz
  have hmul : (PT.ofGens 24 (gs.map unpk) fuel).mulIdx p q = E.idxOf (pc24 E[p] E[q]) := by
    unfold PT.mulIdx
    rw [hn]
    have hs' : ∀ k < E.length, k < (bfsClosure 24 (gs.map unpk) fuel).size := fun k hk => by
      change k < (PT.ofGens 24 (gs.map unpk) fuel).elems.size
      rw [hels]
      simpa using hk
    have e : ((PT.ofGens 24 (gs.map unpk) fuel).mulT[p]!)[q]! =
        ((List.range (PT.ofGens 24 (gs.map unpk) fuel).elems.size).foldl
          (fun m i => m.insert (PT.ofGens 24 (gs.map unpk) fuel).elems[i]! i)
          (∅ : Std.HashMap (Array Nat) Nat)).getD
          (compArr ((PT.ofGens 24 (gs.map unpk) fuel).elems[p]!)
            ((PT.ofGens 24 (gs.map unpk) fuel).elems[q]!)) 0 := by
      change ((bfsClosure 24 (gs.map unpk) fuel |>.map fun a => _)[p]!)[q]! = _
      rw [getElem!_pos _ p (by simpa using hs' p hp), Array.getElem_map,
        getElem!_pos _ q (by simpa using hs' q hq), Array.getElem_map,
        ← getElem!_pos _ p (hs' p hp), ← getElem!_pos _ q (hs' q hq)]
      rfl
    rw [e, hels, getElem!_map_toArray E hp, getElem!_map_toArray E hq,
      compArr_unpk _ (H.vp _ (List.getElem_mem hq)), ← hels, lookup_ofGens hvG hbfs H hz,
      Nat.mod_eq_of_lt hiz]
  rw [hmul, hels, getElem!_map_toArray E hiz, List.getElem_idxOf]

theorem check_ofGens (hvG : ∀ g ∈ gs, vpK g = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) (H : Closure gs E Γ) :
    (PT.ofGens 24 (gs.map unpk) fuel).check = true ∧
      (PT.ofGens 24 (gs.map unpk) fuel).n = E.length := by
  have hels := elems_ofGens hvG hbfs
  have hn := n_ofGens hvG hbfs
  have hone : (PT.ofGens 24 (gs.map unpk) fuel).one = 0 := rfl
  have hpos : 0 < E.length := by
    rw [H.head]
    exact Nat.succ_pos _
  refine ⟨?_, hn⟩
  simp only [PT.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq, Bool.or_eq_true, List.any_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hone, hn]
    exact hpos
  · intro i hi
    rw [hone, hels, getElem!_map_toArray E hpos, unpk_get _ hi]
    have e : E[0] = pidn 24 5 := by
      have := congrArg (fun l : List Nat => l[0]?) H.head
      simpa [List.getElem?_eq_getElem hpos] using this
    rw [e, pg_id hi]
  · intro p hp
    rw [hn] at hp
    obtain ⟨σ, -, h1, h2⟩ := inv_ofGens (Γ := Γ) hvG hbfs H hp
    exact invPairOK_of_hasArr h1 h2
  · intro p hp q hq i hi
    rw [hn] at hp hq
    have hqi := (vpK_spec (H.vp _ (List.getElem_mem hq))).2 i hi
    rw [mul_ofGens hvG hbfs H hp hq, hels, getElem!_map_toArray E hp, getElem!_map_toArray E hq,
      unpk_get _ hi, unpk_get _ hi, unpk_get _ hqi, pg_pc24 _ _ hi]
  · intro p hp q hq
    rw [hn] at hp hq
    by_cases hpq : p = q
    · exact Or.inl hpq
    · refine Or.inr ?_
      by_contra hall
      push Not at hall
      apply hpq
      rw [hels, getElem!_map_toArray E hp, getElem!_map_toArray E hq] at hall
      have e : unpk E[p] = unpk E[q] := by
        apply Array.ext (by rw [size_unpk, size_unpk])
        intro i h1 h2
        have hi : i < 24 := by rwa [size_unpk] at h1
        rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
        exact hall i hi
      exact (H.nodup.getElem_inj_iff).1
        (unpk_inj (H.vp _ (List.getElem_mem _)) (H.vp _ (List.getElem_mem _)) e)

theorem allOK_ofGens {ok : Array Nat → Array Nat → Bool}
    (hok : ∀ σ ∈ Γ, ∀ a b, HasArr σ a → HasArr σ⁻¹ b → ok a b = true)
    (hvG : ∀ g ∈ gs, vpK g = true) (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (H : Closure gs E Γ) : (PT.ofGens 24 (gs.map unpk) fuel).allOK ok = true := by
  unfold PT.allOK
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_range, n_ofGens hvG hbfs] at hp
  obtain ⟨σ, hσ, h1, h2⟩ := inv_ofGens hvG hbfs H hp
  exact hok σ hσ _ _ h1 h2

theorem autArrOK_of_mem {σ : Equiv.Perm (Fin 24)} {a b : Array Nat} (ha : HasArr σ a)
    (hb : HasArr σ⁻¹ b) (hσ : σ ∈ AutPerm) : autArrOK a b = true := by
  have key : ∀ (τ : Equiv.Perm (Fin 24)) (c : Array Nat), HasArr τ c → τ⁻¹ ∈ AutPerm →
      ∀ i < 12, syndM (permM c (Bmask i)) = 0 := by
    intro τ c hc hτ i hi
    rw [← bvec_mem_C_iff, ← permWord_bvec hc]
    have e : bvec 24 (Bmask i) = B ⟨i, hi⟩ := (B_eq_bvec ⟨i, hi⟩).symm
    rw [e]
    have e2 : permWord τ (B ⟨i, hi⟩) = B ⟨i, hi⟩ ∘ ⇑τ⁻¹ := rfl
    rw [e2]
    exact (hτ _).1 (B_mem_C _)
  refine autArrOK_iff.2 ⟨key σ a ha (inv_mem hσ), key σ⁻¹ b hb ?_⟩
  rw [inv_inv]
  exact hσ

theorem okAut_of_mem : ∀ σ ∈ AutPerm, ∀ a b, HasArr σ a → HasArr σ⁻¹ b → okAut a b = true :=
  fun _ hσ _ _ ha hb => autArrOK_of_mem ha hb hσ

theorem okM23_of_mem : ∀ σ ∈ mog23, ∀ a b, HasArr σ a → HasArr σ⁻¹ b → okM23 a b = true := by
  intro σ hσ a b ha hb
  obtain ⟨hA, h0⟩ := hσ
  have h0' : σ 0 = 0 := (mem_stab_iff 0 σ).1 h0
  have e : a[0]! = 0 := by
    have h := (ha 0).symm
    rw [h0'] at h
    exact h
  simp [okM23, autArrOK_of_mem ha hb hA, e]

theorem okPlus_of_mem : ∀ σ ∈ mog22plus, ∀ a b, HasArr σ a → HasArr σ⁻¹ b →
    okPlus a b = true := by
  intro σ hσ a b ha hb
  obtain ⟨hA, hP⟩ := hσ
  have e0 : a[0]! = (σ 0 : Nat) := (ha 0).symm
  have e1 : a[1]! = (σ 1 : Nat) := (ha 1).symm
  simp only [okPlus, autArrOK_of_mem ha hb hA, Bool.true_and, e0, e1]
  rcases hP with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp [h0, h1]
  · simp [h0, h1]

theorem pg_lt_of_vpK {g : Nat} (hg : vpK g = true) {i : Nat} (hi : i < 24) :
    pg 5 (mask 5) g i < 24 := (vpK_spec hg).2 i hi

theorem mem_of_inAutKL {g : Nat} (h : inAutKL ((List.range 24).map (pg 5 (mask 5) g)) = true) :
    ∃ σ ∈ AutPerm, HasArr σ (unpk g) := by
  have e : (unpk g).toList = (List.range 24).map (pg 5 (mask 5) g) := by simp [unpk]
  rw [← e, inAutKL_iff (size_unpk g)] at h
  obtain ⟨hp, hf⟩ := h
  have hinv := invPairOK_invArr_iff.2 hp
  exact ⟨permOfArr 24 (unpk g) (invArr (unpk g)) hinv,
    mem_AutPerm_of_arr hinv (autArrOK_iff.2 ⟨hf, bwd_of_fwd hinv hf⟩), hasArr_permOfArr hinv⟩

theorem genK_spec {t g : Nat} (h : genK t g = true) :
    vpK g = true ∧ ∃ σ ∈ AutPerm, HasArr σ (unpk g) ∧ stabK t g = true := by
  unfold genK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hv, ha⟩, ht⟩ := h
  obtain ⟨σ, hσ, hs⟩ := mem_of_inAutKL ha
  exact ⟨hv, σ, hσ, hs, ht⟩

theorem rootK_spec {t np : Nat} {gs E : List Nat} (h : rootK t np gs E = true) :
    (∀ g ∈ gs, genK t g = true) ∧
      CFSG.KC.TreeK.closedK (fun l x => pc24 (gs.getD l 0) x) gs.length np E = true := by
  simp only [rootK, Bool.and_eq_true, List.all_eq_true] at h
  exact h

theorem rootK_vp {t np : Nat} {gs E : List Nat} (h : rootK t np gs E = true) :
    ∀ g ∈ gs, vpK g = true := fun g hg => (genK_spec ((rootK_spec h).1 g hg)).1

theorem closure_rootK {t np : Nat} (h : rootK t np gs E = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hΓ : ∀ σ ∈ AutPerm, ∀ g, HasArr σ (unpk g) → vpK g = true → stabK t g = true → σ ∈ Γ) :
    Closure gs E Γ :=
  closure_of Γ (fun g hg => by
    obtain ⟨hv, σ, hσ, hs, ht⟩ := genK_spec ((rootK_spec h).1 g hg)
    exact ⟨σ, hΓ σ hσ g hs hv ht, hs⟩) (rootK_vp h) hbfs (rootK_spec h).2

theorem rootK_check {t np : Nat} (h : rootK t np gs E = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (PT.ofGens 24 (gs.map unpk) fuel).check = true ∧
      (PT.ofGens 24 (gs.map unpk) fuel).n = E.length :=
  check_ofGens (rootK_vp h) hbfs (closure_rootK (Γ := AutPerm) h hbfs fun _ hσ _ _ _ _ => hσ)

theorem rootK_allOK_aut {t np : Nat} (h : rootK t np gs E = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (PT.ofGens 24 (gs.map unpk) fuel).allOK okAut = true :=
  allOK_ofGens okAut_of_mem (rootK_vp h) hbfs
    (closure_rootK (Γ := AutPerm) h hbfs fun _ hσ _ _ _ _ => hσ)

theorem rootK_allOK_m23 {np : Nat} (h : rootK 1 np gs E = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (PT.ofGens 24 (gs.map unpk) fuel).allOK okM23 = true :=
  allOK_ofGens okM23_of_mem (rootK_vp h) hbfs
    (closure_rootK (Γ := mog23) h hbfs fun σ hσ g hs hv ht => by
      refine ⟨hσ, (mem_stab_iff 0 σ).2 (Fin.ext ?_)⟩
      rw [stabK] at ht
      exact (hs 0).trans ((unpk_get g (i := 0) (by norm_num)).trans (Nat.eq_of_beq_eq_true ht)))

theorem rootK_allOK_plus {np : Nat} (h : rootK 2 np gs E = true)
    (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E) :
    (PT.ofGens 24 (gs.map unpk) fuel).allOK okPlus = true :=
  allOK_ofGens okPlus_of_mem (rootK_vp h) hbfs
    (closure_rootK (Γ := mog22plus) h hbfs fun σ hσ g hs hv ht => by
      rw [stabK] at ht
      have hsum := Nat.eq_of_beq_eq_true ht
      have e0 : (σ 0 : Nat) = pg 5 (mask 5) g 0 := (hs 0).trans (unpk_get g (i := 0) (by norm_num))
      have e1 : (σ 1 : Nat) = pg 5 (mask 5) g 1 := (hs 1).trans (unpk_get g (i := 1) (by norm_num))
      refine ⟨hσ, ?_⟩
      rcases Nat.eq_zero_or_pos (pg 5 (mask 5) g 0) with h0 | h0
      · exact Or.inl ⟨Fin.ext (by rw [e0, h0]; rfl), Fin.ext (by rw [e1]; omega)⟩
      · exact Or.inr ⟨Fin.ext (by rw [e0]; omega), Fin.ext (by rw [e1]; omega)⟩)

theorem ok_aut_of_rootK {T : PT 24} {t np m : Nat} (hT : T = PT.ofGens 24 (gs.map unpk) fuel)
    (h : rootK t np gs E = true) (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hm : E.length = m) : T.check = true ∧ T.n = m ∧ T.allOK okAut = true := by
  subst hT
  exact ⟨(rootK_check h hbfs).1, (rootK_check h hbfs).2.trans hm, rootK_allOK_aut h hbfs⟩

theorem ok_m23_of_rootK {T : PT 24} {np m : Nat} (hT : T = PT.ofGens 24 (gs.map unpk) fuel)
    (h : rootK 1 np gs E = true) (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hm : E.length = m) : T.check = true ∧ T.n = m ∧ T.allOK okM23 = true := by
  subst hT
  exact ⟨(rootK_check h hbfs).1, (rootK_check h hbfs).2.trans hm, rootK_allOK_m23 h hbfs⟩

theorem ok_plus_of_rootK {T : PT 24} {np m : Nat} (hT : T = PT.ofGens 24 (gs.map unpk) fuel)
    (h : rootK 2 np gs E = true) (hbfs : (bfsP gs fuel [pidn 24 5] [pidn 24 5]).reverse = E)
    (hm : E.length = m) : T.check = true ∧ T.n = m ∧ T.allOK okPlus = true := by
  subst hT
  exact ⟨(rootK_check h hbfs).1, (rootK_check h hbfs).2.trans hm, rootK_allOK_plus h hbfs⟩

end CFSG.KC.HMathieu

end
