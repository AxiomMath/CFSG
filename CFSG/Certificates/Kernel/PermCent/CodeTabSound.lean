module

public import CFSG.Certificates.Kernel.PermCent.KGrpCSound
public import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.Certificates.Kernel.PkCV

open CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV.KGrp

variable {n : Nat} [Small n]

@[expose] noncomputable def tstT (s : CV n) (a b : Nat) : Bool :=
  CFSG.KC.Enum.eq22 n (wC n) (CFSG.KS.mask (wC n)) s.1 a b s.1

omit [Small n] in
theorem tstT_eq (s u v : CV n) : tstT s u.1 v.1 = eq22C s u v s := rfl

@[expose] noncomputable def tieT (X : Nat → Nat) : List (CV n) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun u _ ih k => Nat.beq u.1 (X k) && CFSG.KC.Enum.strictB (Nat.add k 1) ih)

@[expose] noncomputable def clsT (s : CV n) (X : Nat → Nat) (N : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun k => Nat.beq k N)
    (fun t _ ih k => Nat.blt t N && tstT s (X k) (X t) && CFSG.KC.Enum.strictB (Nat.add k 1) ih)

@[expose] noncomputable def incT : List (CV n) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun u _ ih p => Nat.blt p u.1 && ih u.1)

@[expose] noncomputable def wordT (gens : List (CV n)) (w : List Nat) : CV n :=
  w.foldr (fun j x => gens.getD j 1 * x) 1

@[expose] noncomputable def orbT (gens : List (CV n)) (r : CV n) (ws : List (List Nat)) :
    List (CV n) :=
  ws.map fun w => wordT gens w * r * (wordT gens w)⁻¹

@[expose] noncomputable def orbTabOK (gens : List (CV n)) (r : CV n) (ws : List (List Nat))
    (X : Nat → Nat) (rows : List (List Nat)) : Bool :=
  tieT X (orbT gens r ws) 0 && incT (orbT gens r ws) 0 &&
    (orbT gens r ws).any (fun e => Nat.beq e.1 r.1) &&
    (List.range gens.length).all fun k => clsT (gens.getD k 1) X ws.length (rows.getD k []) 0

theorem strictB_add (k : Nat) (f : Nat → Bool) :
    CFSG.KC.Enum.strictB (Nat.add k 1) f = f (k + 1) := by
  cases k <;> rfl

omit [Small n] in
theorem tieT_get (X : Nat → Nat) : ∀ (L : List (CV n)) (k : Nat), tieT X L k = true →
    ∀ i (h : i < L.length), L[i].1 = X (k + i)
  | [], _, _, i, h => absurd h (Nat.not_lt_zero _)
  | u :: L, k, hT, i, h => by
    have e : tieT X (u :: L) k = (Nat.beq u.1 (X k) &&
        CFSG.KC.Enum.strictB (Nat.add k 1) (tieT X L)) := rfl
    rw [e, strictB_add, Bool.and_eq_true] at hT
    cases i with
    | zero => rw [List.getElem_cons_zero, Nat.add_zero, ← Nat.beq_eq]; exact hT.1
    | succ i =>
      rw [List.getElem_cons_succ, tieT_get X L (k + 1) hT.2 i (by simpa using h)]
      congr 1
      omega

omit [Small n] in
theorem clsT_get (s : CV n) (X : Nat → Nat) (N : Nat) : ∀ (row : List Nat) (k : Nat),
    clsT s X N row k = true → k + row.length = N ∧ ∀ i (h : i < row.length),
      row[i] < N ∧ tstT s (X (k + i)) (X row[i]) = true
  | [], k, hc => by
    have e : clsT s X N [] k = Nat.beq k N := rfl
    rw [e, Nat.beq_eq] at hc
    exact ⟨by simpa using hc, fun i h => absurd h (Nat.not_lt_zero _)⟩
  | t :: row, k, hc => by
    have e : clsT s X N (t :: row) k = (Nat.blt t N && tstT s (X k) (X t) &&
        CFSG.KC.Enum.strictB (Nat.add k 1) (clsT s X N row)) := rfl
    rw [e, strictB_add, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hc
    obtain ⟨hl, hr⟩ := clsT_get s X N row (k + 1) hc.2
    refine ⟨by rw [List.length_cons]; omega, fun i h => ?_⟩
    cases i with
    | zero => exact ⟨hc.1.1, by rw [Nat.add_zero]; exact hc.1.2⟩
    | succ i =>
      have := hr i (by simpa using h)
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact this

theorem clsT_mem (s : CV n) (L : List (CV n)) (X : Nat → Nat) (row : List Nat)
    (hT : tieT X L 0 = true) (hc : clsT s X L.length row 0 = true) :
    ∀ u ∈ L, ev s * ev u * (ev s)⁻¹ ∈ L.map ev := by
  intro u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hu
  obtain ⟨hlen, hrow⟩ := clsT_get s X L.length row 0 hc
  obtain ⟨ht, he⟩ := hrow i (by omega)
  have e1 := tieT_get X L 0 hT i hi
  have e2 := tieT_get X L 0 hT _ ht
  rw [Nat.zero_add] at e1 e2
  have he' : eq22C s L[i] L[row[i]] s = true := by
    rw [← tstT_eq, e1, e2]
    rwa [Nat.zero_add] at he
  rw [eq22C_eq, decide_eq_true_eq] at he'
  have e : ev s * ev L[i] * (ev s)⁻¹ = ev L[row[i]] := by
    rw [ev_mul', he', ← ev_mul', mul_inv_cancel_right]
  rw [e]
  exact List.mem_map_of_mem (List.getElem_mem _)

omit [Small n] in
theorem incT_lt :∀ (L : List (CV n)) (p : Nat), incT L p = true → ∀ u ∈ L, p < u.1
  | [], _, _, _, hu => absurd hu List.not_mem_nil
  | v :: L, p, h, u, hu => by
    have e : incT (v :: L) p = (Nat.blt p v.1 && incT L v.1) := rfl
    rw [e, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.1
    · exact h.1.trans (incT_lt L v.1 h.2 u hu)

omit [Small n] in
theorem incT_nodup :∀ (L : List (CV n)) (p : Nat), incT L p = true → L.Nodup
  | [], _, _ => List.nodup_nil
  | v :: L, p, h => by
    have e : incT (v :: L) p = (Nat.blt p v.1 && incT L v.1) := rfl
    rw [e, Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hv => ?_, incT_nodup L v.1 h.2⟩
    exact lt_irrefl _ (incT_lt L v.1 h.2 v hv)

omit [Small n] in
theorem conj_closure_iff (gs V : Set (Equiv.Perm (Fin n)))
    (h : ∀ s ∈ gs, ∀ x ∈ V, s * x * s⁻¹ ∈ V) :
    ∀ g ∈ Subgroup.closure gs, ∀ x, x ∈ V ↔ g * x * g⁻¹ ∈ V := by
  have hgen : ∀ s ∈ gs, ∀ x, x ∈ V ↔ s * x * s⁻¹ ∈ V := by
    intro s hs x
    refine ⟨h s hs x, fun hx => ?_⟩
    have hm : Set.MapsTo (fun y => s * y * s⁻¹) V V := fun y hy => h s hs y hy
    have hinj : Set.InjOn (fun y => s * y * s⁻¹) V := fun a _ b _ e => by simpa using e
    obtain ⟨y, hy, e⟩ :=
      ((Set.Finite.injOn_iff_bijOn_of_mapsTo (Set.toFinite V) hm).1 hinj).surjOn hx
    have hyx : y = x := by simpa using e
    exact hyx ▸ hy
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one => simp
  | mul a b _ _ ha hb =>
    intro x
    have e : a * (b * x * b⁻¹) * a⁻¹ = a * b * x * (a * b)⁻¹ := by group
    rw [hb x, ha (b * x * b⁻¹), e]
  | inv a _ ha =>
    intro x
    have e : a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ = x := by group
    rw [ha (a⁻¹ * x * a⁻¹⁻¹), e]

theorem wordT_mem (gens : List (CV n)) (w : List Nat) :
    ev (wordT gens w) ∈ Subgroup.closure {σ | σ ∈ gens.map ev} := by
  induction w with
  | nil => rw [wordT, List.foldr_nil, ev_one]; exact Subgroup.one_mem _
  | cons j w ih =>
    change ev (gens.getD j 1 * wordT gens w) ∈ _
    rw [ev_mul]
    refine Subgroup.mul_mem _ ?_ ih
    rw [List.getD_eq_getElem?_getD]
    cases h : gens[j]? with
    | none => rw [Option.getD_none, ev_one]; exact Subgroup.one_mem _
    | some a =>
      rw [Option.getD_some]
      exact Subgroup.subset_closure (List.mem_map_of_mem (List.mem_of_getElem? h))

@[expose] def ConjPerm (n : Nat) : Type := Equiv.Perm (Fin n)

@[expose] def toCP {n : Nat} (x : Equiv.Perm (Fin n)) : ConjPerm n := x

@[expose] def ofCP {n : Nat} (x : ConjPerm n) : Equiv.Perm (Fin n) := x

theorem ofCP_toCP {n : Nat} (x : Equiv.Perm (Fin n)) : ofCP (toCP x) = x := rfl

theorem conj_mul_conj {n : Nat} (a b x : Equiv.Perm (Fin n)) :
    a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
  group

@[expose] instance conjMA {n : Nat} (G : Subgroup (Equiv.Perm (Fin n))) :
    MulAction G (ConjPerm n) where
  smul g x := toCP ((g : Equiv.Perm (Fin n)) * ofCP x * (g : Equiv.Perm (Fin n))⁻¹)
  one_smul x := by
    change toCP (((1 : G) : Equiv.Perm (Fin n)) * ofCP x * ((1 : G) : Equiv.Perm (Fin n))⁻¹) = x
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one]
    rfl
  mul_smul g h x := by
    change toCP (((g * h : G) : Equiv.Perm (Fin n)) * ofCP x * ((g * h : G) : Equiv.Perm (Fin n))⁻¹) =
      toCP ((g : Equiv.Perm (Fin n)) * ofCP (toCP ((h : Equiv.Perm (Fin n)) * ofCP x *
        (h : Equiv.Perm (Fin n))⁻¹)) * (g : Equiv.Perm (Fin n))⁻¹)
    rw [Subgroup.coe_mul, ofCP_toCP, conj_mul_conj]

theorem smul_CP {n : Nat} (G : Subgroup (Equiv.Perm (Fin n))) (g : G) (x : Equiv.Perm (Fin n)) :
    g • toCP x = toCP ((g : Equiv.Perm (Fin n)) * x * (g : Equiv.Perm (Fin n))⁻¹) := rfl

theorem toCP_injective {n : Nat} : Function.Injective (toCP : Equiv.Perm (Fin n) → ConjPerm n) :=
  fun _ _ h => h

theorem count_eq_card (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (r : CV n) :
    ((elemsC Q).filter fun h => eq22C h r r h).length =
      Nat.card {g : Q.originalSubgroup // (g : Equiv.Perm (Fin n)) * ev r = ev r * g} := by
  rw [card_filter Q hQ (fun g => g * ev r = ev r * g), elemsT_eq_elemsC, List.filter_map,
    List.length_map]
  congr 1
  apply List.filter_congr
  intro h _
  rw [eq22C_eq, Function.comp_apply, ← ev_mul, ← ev_mul]
  exact decide_eq_decide.2 ev_injective.eq_iff.symm

theorem count_mul_orbit (Q : RawSchreierDatum n) (hQ : ValidSchreier Q) (gens : List (CV n))
    (hgen : Q.originalSubgroup = Subgroup.closure {σ | σ ∈ gens.map ev}) (r : CV n)
    (ws : List (List Nat)) (X : Nat → Nat) (rows : List (List Nat))
    (h : orbTabOK gens r ws X rows = true) :
    ((elemsC Q).filter fun h => eq22C h r r h).length * ws.length =
      Nat.card Q.originalSubgroup := by
  set O := orbT gens r ws with hO
  have hOl : O.length = ws.length := List.length_map _
  unfold orbTabOK at h
  rw [← hO] at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    Nat.beq_eq] at h
  obtain ⟨⟨⟨hT, hI⟩, ⟨e, heO, her⟩⟩, hc⟩ := h
  have hrO : r ∈ O := (Subtype.ext her : e = r) ▸ heO
  set G := Q.originalSubgroup
  let V : Set (Equiv.Perm (Fin n)) := {x | x ∈ O.map ev}
  have hstep : ∀ s ∈ {σ | σ ∈ gens.map ev}, ∀ x ∈ V, s * x * s⁻¹ ∈ V := by
    intro s hs x hx
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hs
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hs'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
    have hck := hc k hk
    rw [← hOl, List.getD_eq_getElem _ _ hk] at hck
    exact clsT_mem _ O X _ hT hck u hu
  have key := conj_closure_iff _ V hstep
  rw [← hgen] at key
  have hrV : ev r ∈ V := List.mem_map_of_mem hrO
  have horb : MulAction.orbit G (toCP (ev r)) = toCP '' V := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change g • toCP (ev r) ∈ toCP '' V
      rw [smul_CP]
      exact Set.mem_image_of_mem _ ((key g g.2 (ev r)).1 hrV)
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hu
      have hw : ev (wordT gens w) ∈ G := hgen ▸ wordT_mem gens w
      refine ⟨⟨ev (wordT gens w), hw⟩, ?_⟩
      change (⟨ev (wordT gens w), hw⟩ : G) • toCP (ev r) = _
      rw [smul_CP, ev_mul, ev_mul, ev_inv]
  have hnd : (O.map ev).Nodup := (nodup_map_ev O).2 (incT_nodup O 0 hI)
  have hcard : (MulAction.orbit G (toCP (ev r))).ncard = ws.length := by
    rw [horb, Set.ncard_image_of_injective _ toCP_injective, ← hOl, ← List.length_map (f := ev),
      ← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [V]
  have hstab : Nat.card (MulAction.stabilizer G (toCP (ev r))) =
      Nat.card {g : G // (g : Equiv.Perm (Fin n)) * ev r = ev r * g} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [MulAction.mem_stabilizer_iff, smul_CP]
    constructor
    · intro e
      have e' := toCP_injective e
      rwa [mul_inv_eq_iff_eq_mul] at e'
    · intro e
      rw [← mul_inv_eq_iff_eq_mul] at e
      rw [e]
  rw [count_eq_card Q hQ r, ← hstab, ← hcard, ← MulAction.index_stabilizer]
  exact Subgroup.card_mul_index _

end CFSG.Certificates.Kernel.PkCV

end
