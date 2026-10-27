module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZGlue
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZAbs
public import CFSG.Sporadic.J4.QT2LocX0NMainBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem commute_of_rows {x y : J} {A B : Array V2} (hx : Mx x = rowsMatrix A)
    (hy : Mx y = rowsMatrix B) (h : eqRows (mulRows A B) (mulRows B A) = true) : x * y = y * x := by
  apply Mx_injective
  rw [map_mul, map_mul, hx, hy, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, eqRows_iff.1 h]

theorem conj_eq_of_rows {y x z : J} {Y Yi A P : Array V2} (hy : Mx y = rowsMatrix Y)
    (hyi : Mx y⁻¹ = rowsMatrix Yi) (hx : Mx x = rowsMatrix A) (hz : Mx z = rowsMatrix P)
    (h : eqRows (mulRows (mulRows Y A) Yi) P = true) : y * x * y⁻¹ = z := by
  apply Mx_injective
  rw [map_mul, map_mul, hy, hyi, hx, hz, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows,
    eqRows_iff.1 h]

@[expose] def prodRows : List (Array V2) → Array V2
  | [] => idRows
  | r :: rs => mulRows r (prodRows rs)

theorem Mx_list_prod {ι : Type*} {f : ι → J} {R : ι → Array V2} (l : List ι)
    (hR : ∀ j ∈ l, Mx (f j) = rowsMatrix (R j)) :
    Mx ((l.map f).prod) = rowsMatrix (prodRows (l.map R)) := by
  induction l with
  | nil => simp [prodRows, rowsMatrix_idRows]
  | cons j l ih =>
    have h1 := hR j (List.mem_cons_self ..)
    have h2 := ih fun i hi => hR i (List.mem_cons_of_mem _ hi)
    simp only [List.map_cons, List.prod_cons, prodRows, map_mul, h1, h2, rowsMatrix_mulRows]

theorem exists_L_of_rows {Cl : List J} {R : List (Array V2)}
    (hR : List.Forall₂ (fun x r => Mx x = rowsMatrix r) Cl R) (hRwf : ∀ r ∈ R, wfRows r = true)
    {y : J} {Y : Array V2} (hY : Mx y = rowsMatrix Y) (hYwf : wfRows Y = true) {k : ℕ}
    (hk : (R.filter fun r => eqRows (mulRows r Y) (mulRows Y r)).length ≤ k) :
    ∃ L : List J, (∀ x ∈ Cl, x * y = y * x → x ∈ L) ∧ L.length ≤ k := by
  set Q : Array V2 → Bool := fun r => eqRows (mulRows r Y) (mulRows Y r) with hQ
  have key : ∀ (Cl : List J) (R : List (Array V2)),
      List.Forall₂ (fun x r => Mx x = rowsMatrix r) Cl R → (∀ r ∈ R, wfRows r = true) →
      ∃ L : List J, (∀ x ∈ Cl, x * y = y * x → x ∈ L) ∧ L.length = (R.filter Q).length := by
    intro Cl R h
    induction h with
    | nil => exact fun _ => ⟨[], by simp, rfl⟩
    | @cons x r Cl' R' hxr _ ih =>
      intro hwf
      obtain ⟨L', hL', hlen'⟩ := ih fun r' hr' => hwf r' (List.mem_cons_of_mem _ hr')
      have hrwf : wfRows r = true := hwf r (List.mem_cons_self ..)
      have hq : x * y = y * x → Q r = true := by
        intro hxy
        have hm : rowsMatrix (mulRows r Y) = rowsMatrix (mulRows Y r) := by
          rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← hxr, ← hY, ← map_mul, ← map_mul, hxy]
        exact eqRows_iff.2 (eq_of_rowsMatrix_eq (wfRows_mulRows hrwf hYwf)
          (wfRows_mulRows hYwf hrwf) hm)
      by_cases hQr : Q r = true
      · refine ⟨x :: L', ?_, ?_⟩
        · intro x' hx' hxy'
          rcases List.mem_cons.1 hx' with rfl | hx''
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hL' x' hx'' hxy')
        · rw [List.filter_cons_of_pos hQr, List.length_cons, List.length_cons, hlen']
      · refine ⟨L', ?_, ?_⟩
        · intro x' hx' hxy'
          rcases List.mem_cons.1 hx' with rfl | hx''
          · exact absurd (hq hxy') hQr
          · exact hL' x' hx'' hxy'
        · rw [List.filter_cons_of_neg hQr, hlen']
  obtain ⟨L, hL, hlen⟩ := key Cl R hR hRwf
  exact ⟨L, hL, hlen ▸ hk⟩

theorem orderOf_conj_eq {Y : Type*} [Group Y] (g x : Y) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := (MulAut.conj g).orderOf_eq x
  rwa [MulAut.conj_apply] at h

theorem classRad_of_gens_fin4 {Y : Type*} [Group Y] {V : Subgroup Y} {c vs : Fin 4 → Y}
    (hV : V = Subgroup.closure (Set.range c)) (g : Y)
    (h1 : ∀ i, vs i ∈ Subgroup.closure (Set.range fun j => g * c j * g⁻¹))
    (h2 : ∀ j, g * c j * g⁻¹ ∈ Subgroup.closure (Set.range vs))
    (h : ClassRad (Subgroup.closure (Set.range vs))) : ClassRad V := by
  refine classRad_of_map_cm g ?_
  have e : V.map (cm g) = Subgroup.closure (Set.range vs) := by
    rw [hV, map_cm_closure, ← Set.range_comp]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      exact h2 j
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact h1 i
  rw [e]
  exact h

theorem classRad_of_zData4 (vs : Fin 4 → J) (ms : Fin 4 → Array V2)
    (hms : ∀ i, Mx (vs i) = rowsMatrix (ms i)) (y : J) (Y Yi : Array V2)
    (hY : Mx y = rowsMatrix Y) (hYi : Mx y⁻¹ = rowsMatrix Yi) (hYwf : wfRows Y = true)
    (S : Fin 4 → List (Fin 4))
    (hcomm : ∀ i j, eqRows (mulRows (ms i) (ms j)) (mulRows (ms j) (ms i)) = true)
    (hS : ∀ i, eqRows (mulRows (mulRows Y (ms i)) Yi) (prodRows ((S i).map ms)) = true)
    (hy5 : orderOf y = 5) {m : ℕ} (Cl : List J) (R : List (Array V2))
    (hcl : ∀ x : J, (∀ i, x * vs i = vs i * x) → x ∈ Cl)
    (hsound : ∀ x ∈ Cl, ∀ i, x * vs i = vs i * x)
    (h2 : ∀ x ∈ Cl, x ^ (2 ^ m) = 1) (hnodup : Cl.Nodup)
    (hR : List.Forall₂ (fun x r => Mx x = rowsMatrix r) Cl R) (hRwf : ∀ r ∈ R, wfRows r = true)
    {k : ℕ} (hk : (R.filter fun r => eqRows (mulRows r Y) (mulRows Y r)).length ≤ k)
    (hidx : 16 * k < Cl.length) :
    ClassRad (Subgroup.closure (Set.range vs)) := by
  have hset : {x | x ∈ List.ofFn vs} = Set.range vs := by
    ext x
    exact List.mem_ofFn
  obtain ⟨L, hL, hLk⟩ := exists_L_of_rows hR hRwf hY hYwf hk
  have key := classRad_of_centralizer_list (List.ofFn vs) y Cl L (m := m)
    (fun a ha b hb => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      exact commute_of_rows (hms i) (hms j) (hcomm i j))
    (fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      have hz : Mx (((S i).map vs).prod) = rowsMatrix (prodRows ((S i).map ms)) :=
        Mx_list_prod (S i) fun j _ => hms j
      rw [conj_eq_of_rows hY hYi (hms i) hz (hS i), hset]
      refine Subgroup.list_prod_mem _ fun z hz' => ?_
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hz'
      exact Subgroup.subset_closure ⟨j, rfl⟩)
    hy5
    (fun x hx => hcl x fun i => hx (vs i) (List.mem_ofFn.2 ⟨i, rfl⟩))
    (fun x hx v hv => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
      exact hsound x hx i)
    h2 hnodup hL (by omega)
  rwa [hset] at key

end CFSG.QuasithinUnique.A5
