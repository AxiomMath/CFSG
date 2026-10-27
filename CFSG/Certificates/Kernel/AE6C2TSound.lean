module

public import Certificates.Data.Kernel.AE6C2T
public import CFSG.Certificates.Kernel.AE6C2BSound
public import CFSG.Certificates.Kernel.YoshQ.TabNSound

public section

namespace CFSG.KC.AE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KS.PF
open CFSG.KC.Census (strictLA strictNA strictLA_eq strictNA_eq)
open CFSG.KC.KGC31P (pfilterProducts)

@[expose] def Rng (x : Nat) : Prop := ∀ i < 360, pg 9 (mask 9) x i < 360

@[expose] def TOK (g h h' : Nat) : Prop :=
  ∀ i < 360, pg 9 (mask 9) h i < 360 ∧ pg 9 (mask 9) h' i = pg 9 (mask 9) g (pg 9 (mask 9) h i)

theorem pg_pc {p q i : Nat} (hi : i < 360) :
    pg 9 (mask 9) (CFSG.KC.KGC31P.pc 360 9 p q) i = pg 9 (mask 9) p (pg 9 (mask 9) q i) :=
  pg_pcomp (by norm_num) hi

theorem tok_root (g : Nat) : TOK g (pidn 360 9) g := fun i hi => by
  rw [pg_pidn (n := 360) (w := 9) (by norm_num) (by norm_num) hi]
  exact ⟨hi, rfl⟩

theorem tok_step {g h h' t : Nat} (hh : TOK g h h') (ht : Rng t) :
    TOK g (CFSG.KC.KGC31P.pc 360 9 h t) (CFSG.KC.KGC31P.pc 360 9 h' t) := fun i hi => by
  rw [pg_pc hi, pg_pc hi]
  exact hh _ (ht i hi)

theorem conj_leaf {g gi h h' t : Nat} (hh : TOK g h h') (ht : Rng t) (hgi : Rng gi) :
    conjN g gi (CFSG.KC.KGC31P.pc 360 9 h t) =
      CFSG.KC.KGC31P.pc 360 9 h' (CFSG.KC.KGC31P.pc 360 9 t gi) := by
  unfold conjN pmN
  apply eq_of_fields (n := 360) (w := 9) (by norm_num) (pcomp_shr _ _ (by norm_num) (by norm_num))
    (pcomp_shr _ _ (by norm_num) (by norm_num))
  intro i hi
  have hj := hgi i hi
  have hk := ht _ hj
  have hl := (hh _ hk).1
  rw [pg_pcomp (by norm_num) hi, pg_pcomp (by norm_num) hi, pg_pc hi, pg_mod hj, pg_pcomp (by norm_num) hj,
    pg_pc hj, pg_mod hl, (hh _ hk).2]

theorem lvlT_map (φ ψ : Nat → Nat) (k k' : Nat → List Nat → List Nat) (h h' : Nat) :
    ∀ (T : List Nat), (∀ t ∈ T, ∀ acc, (k (CFSG.KC.KGC31P.pc 360 9 h t) acc).map φ =
        k' (CFSG.KC.KGC31P.pc 360 9 h' (ψ t)) (acc.map φ)) →
      ∀ acc, (lvlT T k h acc).map φ = lvlT (T.map ψ) k' h' (acc.map φ)
  | [], _, _ => rfl
  | t :: T, hk, acc => by
    change (strictNA (CFSG.KC.KGC31P.pc 360 9 h t) fun x => lvlT T k h (k x acc)).map φ =
      strictNA (CFSG.KC.KGC31P.pc 360 9 h' (ψ t)) fun x => lvlT (T.map ψ) k' h' (k' x (acc.map φ))
    rw [strictNA_eq, strictNA_eq, ← hk t List.mem_cons_self acc]
    exact lvlT_map φ ψ k k' h h' T (fun t ht => hk t (List.mem_cons_of_mem _ ht)) _

theorem lvlT_map_id (φ : Nat → Nat) (k k' : Nat → List Nat → List Nat) (h h' : Nat) (T : List Nat)
    (hk : ∀ t ∈ T, ∀ acc, (k (CFSG.KC.KGC31P.pc 360 9 h t) acc).map φ =
      k' (CFSG.KC.KGC31P.pc 360 9 h' t) (acc.map φ)) (acc : List Nat) :
    (lvlT T k h acc).map φ = lvlT T k' h' (acc.map φ) := by
  have e := lvlT_map φ id k k' h h' T hk acc
  rwa [List.map_id] at e

theorem lvlT_eq (T : List Nat) (k : Nat → List Nat → List Nat) :
    ∀ h acc, lvlT T k h acc = T.foldl (fun acc t => k (CFSG.KC.KGC31P.pc 360 9 h t) acc) acc := by
  induction T with
  | nil => intro h acc; rfl
  | cons t T ih =>
    intro h acc
    change (strictNA (CFSG.KC.KGC31P.pc 360 9 h t) fun x => lvlT T k h (k x acc)) = _
    rw [strictNA_eq, ih, List.foldl_cons]

theorem pf_cons (T : List Nat) (Ts : List (List Nat)) :
    pfilterProducts 360 9 (fun _ => true) (T :: Ts) =
      lvlT T (pfilterProducts 360 9 (fun _ => true) Ts) := by
  funext h acc
  rw [lvlT_eq]
  simp only [pfilterProducts]

theorem pf_nil : pfilterProducts 360 9 (fun _ => true) [] = List.cons := by
  funext h acc
  simp [pfilterProducts]

theorem pf4_eq (T0 T1 T2 T3 : List Nat) (h : Nat) :
    pfilterProducts 360 9 (fun _ => true) [T0, T1, T2, T3] h [] = prod4 T0 T1 T2 T3 h := by
  rw [pf_cons, pf_cons, pf_cons, pf_cons, pf_nil]
  rfl

theorem prod4_conj {g gi : Nat} {T0 T1 T2 T3 : List Nat} (hT : ∀ T ∈ [T0, T1, T2, T3], ∀ t ∈ T, Rng t)
    (hgi : Rng gi) :
    (pfilterProducts 360 9 (fun _ => true) [T0, T1, T2, T3] (pidn 360 9) []).map (conjN g gi) =
      prod4 T0 T1 T2 (T3.map fun t => CFSG.KC.KGC31P.pc 360 9 t gi) g := by
  have r0 : ∀ t ∈ T0, Rng t := hT T0 (by simp)
  have r1 : ∀ t ∈ T1, Rng t := hT T1 (by simp)
  have r2 : ∀ t ∈ T2, Rng t := hT T2 (by simp)
  have r3 : ∀ t ∈ T3, Rng t := hT T3 (by simp)
  have L3 : ∀ h h', TOK g h h' → ∀ acc, (lvlT T3 List.cons h acc).map (conjN g gi) =
      lvlT (T3.map fun t => CFSG.KC.KGC31P.pc 360 9 t gi) List.cons h' (acc.map (conjN g gi)) :=
    fun h h' hh => lvlT_map _ _ _ _ h h' T3 fun t ht acc => by
      rw [List.map_cons, conj_leaf hh (r3 t ht) hgi]
  have L2 : ∀ h h', TOK g h h' → ∀ acc,
      (lvlT T2 (lvlT T3 List.cons) h acc).map (conjN g gi) =
        lvlT T2 (lvlT (T3.map fun t => CFSG.KC.KGC31P.pc 360 9 t gi) List.cons) h'
          (acc.map (conjN g gi)) :=
    fun h h' hh => lvlT_map_id _ _ _ h h' T2 fun t ht => L3 _ _ (tok_step hh (r2 t ht))
  have L1 : ∀ h h', TOK g h h' → ∀ acc,
      (lvlT T1 (lvlT T2 (lvlT T3 List.cons)) h acc).map (conjN g gi) =
        lvlT T1 (lvlT T2 (lvlT (T3.map fun t => CFSG.KC.KGC31P.pc 360 9 t gi) List.cons)) h'
          (acc.map (conjN g gi)) :=
    fun h h' hh => lvlT_map_id _ _ _ h h' T1 fun t ht => L2 _ _ (tok_step hh (r1 t ht))
  rw [pf4_eq]
  unfold prod4
  exact lvlT_map_id _ _ _ _ _ T0 (fun t ht => L1 _ _ (tok_step (tok_root g) (r0 t ht))) []

theorem zfilt_map (mem : Nat → Bool) (f : Nat → Nat) :
    ∀ L : List Nat, zfilt mem L (L.map f) = L.filter fun x => mem (f x)
  | [] => rfl
  | x :: L => by
    have e : zfilt mem (x :: L) ((x :: L).map f) =
        Bool.rec (zfilt mem L (L.map f)) (x :: zfilt mem L (L.map f)) (mem (f x)) := rfl
    rw [e, zfilt_map mem f L, List.filter_cons]
    cases mem (f x) <;> rfl

theorem rngN_spec {x : Nat} (h : rngN x = true) : Rng x := fun i hi => by
  have e : Nat.blt (pg 9 (mask 9) x i) 360 = true := allN_spec h i hi
  rwa [Nat.blt_eq] at e

theorem qsAllT_eq {mem : Nat → Bool} {P T0 T1 T2 T3 G : List Nat}
    (hP : P = pfilterProducts 360 9 (fun _ => true) [T0, T1, T2, T3] (pidn 360 9) [])
    (hT : ∀ T ∈ [T0, T1, T2, T3], ∀ t ∈ T, Rng t) (hG : rngG G = true) :
    qsAllT mem P T0 T1 T2 T3 G = qsAllK mem P G := by
  unfold rngG at hG
  unfold qsAllT qsAllK
  refine List.map_congr_left fun i hi => ?_
  simp only [strictNA_eq, strictLA_eq]
  have hgi : Rng (invN 360 9 (G.getD i (pidn 360 9))) :=
    rngN_spec (List.all_eq_true.1 hG i hi)
  rw [← prod4_conj hT hgi, ← hP, zfilt_map]

theorem basicT_sound {G P T0 T1 T2 T3 L3I B : List Nat} {CZ : List (List Nat)}
    (h : basicT G P T0 T1 T2 T3 L3I B CZ = true)
    (hP : P = pfilterProducts 360 9 (fun _ => true) [T0, T1, T2, T3] (pidn 360 9) [])
    (hT : ∀ T ∈ [T0, T1, T2, T3], ∀ t ∈ T, Rng t) :
    (c2BasicN G P (qsAllN P G) (lsRec P L3I) &&
      lsN (qsAllN P G) (l3N ((qsAllN P G).getD 3 []) B CZ) == lsRec P L3I) = true := by
  apply basicF_sound
  unfold basicT at h
  unfold basicF
  simp only [strictLA_eq, strictLLA_eq, strictB_eqC] at h ⊢
  obtain ⟨ht, hx⟩ := rec_true h
  rw [Bool.and_eq_true] at ht
  rw [qsAllT_eq hP hT ht.2] at hx
  rw [ht.1]
  exact hx

end CFSG.KC.AE6C2

end
