module

public import Certificates.Data.Kernel.Stroth77.NonSplitK

public section

namespace CFSG.KC.Stroth77NS

open Equiv Equiv.Perm CFSG.CGT.Stroth77.Core CFSG.Permutation.SymmetricCoxeter
  CFSG.HardMathSupport.Cooperstein.Coordinator

theorem sw_inv (k : Fin 5) : (sw k)⁻¹ = sw k := by
  unfold sw
  rw [adjSwap_of_lt k.isLt]
  exact swap_inv _ _

def phi (σ : Perm (Fin 6)) : List ℕ :=
  [(σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val, (σ 4).val, (σ 5).val]

theorem phi_mul_sw (σ : Perm (Fin 6)) (k : Fin 5) : phi (σ * sw k) = swapAt k.val (phi σ) := by
  fin_cases k <;> rfl

theorem phi_vtx : ∀ (w : List (Fin 5)) (τ : Perm (Fin 6)),
    phi (τ * vtx w) = w.foldl (fun l k => swapAt k.val l) (phi τ)
  | [], τ => by
    change phi (τ * 1) = phi τ
    rw [mul_one]
  | k :: w, τ => by
    have h : τ * vtx (k :: w) = (τ * sw k) * vtx w := by
      rw [mul_assoc]
      rfl
    rw [h, phi_vtx w, phi_mul_sw]
    rfl

theorem phi_vtx_one (w : List (Fin 5)) : phi (vtx w) = vtxJ w := by
  have h := phi_vtx w 1
  rw [one_mul] at h
  exact h

def codeE (e : Perm (Fin 6) × Fin 5) : ℕ := edgeJ (phi e.1) e.2

theorem digit6 {a b x y : ℕ} (ha : a < 6) (hb : b < 6) (h : a + 6 * x = b + 6 * y) :
    a = b ∧ x = y := by
  omega

theorem codeE_inj : Function.Injective codeE := by
  rintro ⟨σ, k⟩ ⟨τ, k'⟩ h
  have hk := k.isLt
  have hk' := k'.isLt
  change 5 * codeJ (phi σ) + k.val = 5 * codeJ (phi τ) + k'.val at h
  have h2 : k.val = k'.val ∧ codeJ (phi σ) = codeJ (phi τ) := by omega
  obtain ⟨h2k, hc⟩ := h2
  change (σ 0).val + 6 * ((σ 1).val + 6 * ((σ 2).val + 6 * ((σ 3).val + 6 * ((σ 4).val +
      6 * ((σ 5).val + 6 * 0))))) = (τ 0).val + 6 * ((τ 1).val + 6 * ((τ 2).val + 6 * ((τ 3).val +
      6 * ((τ 4).val + 6 * ((τ 5).val + 6 * 0))))) at hc
  obtain ⟨h0, hc⟩ := digit6 (σ 0).isLt (τ 0).isLt hc
  obtain ⟨h1, hc⟩ := digit6 (σ 1).isLt (τ 1).isLt hc
  obtain ⟨h2, hc⟩ := digit6 (σ 2).isLt (τ 2).isLt hc
  obtain ⟨h3, hc⟩ := digit6 (σ 3).isLt (τ 3).isLt hc
  obtain ⟨h4, hc⟩ := digit6 (σ 4).isLt (τ 4).isLt hc
  obtain ⟨h5, -⟩ := digit6 (σ 5).isLt (τ 5).isLt hc
  refine Prod.ext (Equiv.ext fun i => ?_) (Fin.ext h2k)
  fin_cases i
  exacts [Fin.ext h0, Fin.ext h1, Fin.ext h2, Fin.ext h3, Fin.ext h4, Fin.ext h5]

theorem walk_map : ∀ (r : List (Letter 5)) (σ : Perm (Fin 6)),
    (walk sw σ r).map codeE = walkJ (phi σ) r
  | [], _ => rfl
  | (k, true) :: w, σ => by
    change codeE (σ, k) :: (walk sw (σ * sw k) w).map codeE =
      edgeJ (phi σ) k :: walkJ (swapAt k.val (phi σ)) w
    rw [walk_map w, phi_mul_sw]
    rfl
  | (k, false) :: w, σ => by
    change codeE (σ * (sw k)⁻¹, k) :: (walk sw (σ * (sw k)⁻¹) w).map codeE =
      edgeJ (swapAt k.val (phi σ)) k :: walkJ (swapAt k.val (phi σ)) w
    rw [sw_inv, walk_map w]
    change edgeJ (phi (σ * sw k)) k :: _ = _
    rw [phi_mul_sw]

theorem mem_toggle {acc : List ℕ} (hnd : acc.Nodup) (y x : ℕ) :
    x ∈ toggleJ acc y ↔ (x ∈ acc ↔ x ≠ y) := by
  unfold toggleJ
  split
  · rename_i hy
    rw [hnd.mem_erase_iff]
    by_cases hxy : x = y
    · subst hxy
      simp [hy]
    · simp [hxy]
  · rename_i hy
    rw [List.mem_cons]
    by_cases hxy : x = y
    · subst hxy
      simp [hy]
    · simp [hxy]

theorem nodup_toggle {acc : List ℕ} (hnd : acc.Nodup) (y : ℕ) : (toggleJ acc y).Nodup := by
  unfold toggleJ
  split
  · exact hnd.erase y
  · rename_i hy
    exact List.nodup_cons.2 ⟨hy, hnd⟩

theorem mem_foldl_toggle : ∀ (L acc : List ℕ), acc.Nodup → ∀ x,
    (x ∈ L.foldl toggleJ acc ↔ (x ∈ acc ↔ Even (L.count x)))
  | [], acc, _, x => by simp
  | y :: L, acc, hnd, x => by
    rw [List.foldl_cons, mem_foldl_toggle L _ (nodup_toggle hnd y) x, mem_toggle hnd y x,
      List.count_cons]
    by_cases hxy : x = y
    · subst hxy
      simp only [ne_eq, not_true_eq_false, iff_false, beq_self_eq_true, if_true,
        Nat.even_add_one]
      tauto
    · have hyx : (y == x) = false := by simpa using Ne.symm hxy
      simp only [ne_eq, hxy, not_false_eq_true, iff_true, hyx, Bool.false_eq_true, if_false,
        add_zero]

theorem even_of_toggle (L : List ℕ) (h : (L.foldl toggleJ []).isEmpty = true) (x : ℕ) :
    Even (L.count x) := by
  have hx := mem_foldl_toggle L [] List.nodup_nil x
  rw [List.isEmpty_iff.1 h] at hx
  simpa using hx

theorem count_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (x : α) : ∀ l : List α, (l.map f).count (f x) = l.count x
  | [] => rfl
  | y :: l => by
    simp only [List.map_cons, List.count_cons, count_map_inj hf x l, beq_iff_eq, hf.eq_iff]

theorem getD_mem {α : Type*} : ∀ (l : List α) (n : ℕ) (d : α), n < l.length → l.getD n d ∈ l
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => List.mem_cons_self
  | _ :: l, n + 1, d, h => List.mem_cons_of_mem _ (getD_mem l n d (by simpa using h))

theorem cycles_even_k (h : cycOKt = true) : ∀ i, ∀ e ∈ ((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
    (fun c => walk sw c.1 c.2), Even ((((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
      (fun c => walk sw c.1 c.2)).count e) := by
  intro i e _
  have hL : (((cycles i).map fun c => (vtx c.1, rel c.2)).flatMap
      (fun c => walk sw c.1 c.2)).map codeE = edgesJ (cycles i) := by
    simp only [List.flatMap_map, List.map_flatMap, walk_map, phi_vtx_one, edgesJ]
  have hmem : cycles i ∈ cyclesL := getD_mem cyclesL i [] (by
    have hlen : cyclesL.length = 34 := rfl
    omega)
  have hc := List.all_eq_true.1 h (cycles i) hmem
  rw [← count_map_inj codeE_inj e, hL]
  exact even_of_toggle _ hc _

variable {n : ℕ}

def bas (q : Fin n) (e : Fin 4) : Fin n → U4 := Pi.single q (Pi.single e 1)

def RepU (F : (Fin n → U4) →+ U4) (l : List ℕ) : Prop :=
  ∀ (d : Fin 4) (q : Fin n) (e : Fin 4), F (bas q e) d = bitZ (l.getD d.val 0) (4 * q.val + e.val)

theorem bitZ_xor (a b i : ℕ) : bitZ (a ^^^ b) i = bitZ a i + bitZ b i := by
  unfold bitZ
  rw [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bitZ_zero (i : ℕ) : bitZ 0 i = 0 := by simp [bitZ]

theorem bitZ_ite (g c r i : ℕ) : bitZ (if g.testBit c then r else 0) i = bitZ g c * bitZ r i := by
  unfold bitZ
  cases g.testBit c <;> simp

theorem getD_xorRows : ∀ (l l' : List ℕ) (d : ℕ),
    (xorRows l l').getD d 0 = l.getD d 0 ^^^ l'.getD d 0
  | [], [], _ => by simp [xorRows]
  | [], _ :: _, _ => by simp [xorRows]
  | _ :: _, [], _ => by simp [xorRows]
  | _ :: l, _ :: l', 0 => by simp [xorRows]
  | _ :: l, _ :: l', d + 1 => by
    simp only [xorRows, List.getD_cons_succ]
    exact getD_xorRows l l' d

theorem getD_unitRows : ∀ (d0 r d : ℕ), (unitRows d0 r).getD d 0 = if d = d0 then r else 0
  | 0, _, 0 => by simp [unitRows]
  | 0, _, _ + 1 => by simp [unitRows]
  | _ + 1, _, 0 => by simp [unitRows]
  | d0 + 1, r, d + 1 => by
    simp only [unitRows, List.getD_cons_succ]
    rw [getD_unitRows d0 r d]
    simp

theorem bas_bit (q q0 : Fin n) (e d : Fin 4) :
    bas q e q0 d = bitZ (2 ^ (4 * q0.val + d.val)) (4 * q.val + e.val) := by
  have hd := d.isLt
  have he := e.isLt
  unfold bitZ bas
  rw [Nat.testBit_two_pow]
  by_cases h1 : q0 = q
  · subst h1
    rw [Pi.single_eq_same]
    by_cases h2 : d = e
    · subst h2
      simp
    · rw [Pi.single_eq_of_ne h2]
      have : ¬ 4 * q0.val + d.val = 4 * q0.val + e.val := fun h => h2 (Fin.ext (by omega))
      rw [decide_eq_false this]
      rfl
  · rw [Pi.single_eq_of_ne h1]
    have : ¬ 4 * q0.val + d.val = 4 * q.val + e.val := fun h => h1 (Fin.ext (by omega))
    rw [decide_eq_false this]
    rfl

theorem rep_congr {F F' : (Fin n → U4) →+ U4} {l : List ℕ} (h : ∀ x, F x = F' x)
    (hF : RepU F l) : RepU F' l := fun d q e => by rw [← h]; exact hF d q e

theorem rep_eval (q0 : Fin n) : RepU (Pi.evalAddMonoidHom (fun _ : Fin n => U4) q0) (selRows q0.val) := by
  intro d q e
  have h : (selRows q0.val).getD d.val 0 = 2 ^ (4 * q0.val + d.val) := by
    fin_cases d <;> rfl
  rw [h, Pi.evalAddMonoidHom_apply, bas_bit]

theorem rep_zero : RepU (0 : (Fin n → U4) →+ U4) [] := fun d q e => by
  simp [bitZ_zero]

theorem rep_add {F F' : (Fin n → U4) →+ U4} {l l' : List ℕ} (hF : RepU F l) (hF' : RepU F' l') :
    RepU (F + F') (xorRows l l') := fun d q e => by
  rw [AddMonoidHom.add_apply, Pi.add_apply, hF, hF', getD_xorRows, bitZ_xor]

theorem rep_sum {α : Type*} (f : α → (Fin n → U4) →+ U4) (rows : α → List ℕ) :
    ∀ L : List α, (∀ a ∈ L, RepU (f a) (rows a)) →
      RepU (L.map f).sum (L.foldr (fun a acc => xorRows (rows a) acc) [])
  | [], _ => rep_zero
  | a :: L, h => by
    rw [List.map_cons, List.sum_cons, List.foldr_cons]
    exact rep_add (h a List.mem_cons_self)
      (rep_sum f rows L fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem rep_comp_act (hg : gSpec) (k : Fin 5) {F : (Fin n → U4) →+ U4} {l : List ℕ}
    (hF : RepU F l) : RepU ((actC (sw k)).comp F) (mulG (gRows.getD k.val []) l) := by
  intro d q e
  rw [AddMonoidHom.comp_apply]
  have hu : F (bas q e) = ![F (bas q e) 0, F (bas q e) 1, F (bas q e) 2, F (bas q e) 3] := by
    funext i
    fin_cases i <;> rfl
  have h0 : F (bas q e) 0 = bitZ (l.getD 0 0) (4 * q.val + e.val) := hF 0 q e
  have h1 : F (bas q e) 1 = bitZ (l.getD 1 0) (4 * q.val + e.val) := hF 1 q e
  have h2 : F (bas q e) 2 = bitZ (l.getD 2 0) (4 * q.val + e.val) := hF 2 q e
  have h3 : F (bas q e) 3 = bitZ (l.getD 3 0) (4 * q.val + e.val) := hF 3 q e
  have hm : (mulG (gRows.getD k.val []) l).getD d.val 0 = comb4 ((gRows.getD k.val []).getD d.val 0) l := by
    fin_cases d <;> rfl
  rw [hu, hg, hm]
  unfold app4 comb4
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    h0, h1, h2, h3, bitZ_xor, bitZ_ite]
  rfl

theorem actC_mul (σ τ : Perm (Fin 6)) : actC (σ * τ) = (actC σ).comp (actC τ) := by
  refine AddMonoidHom.ext fun c => ?_
  obtain ⟨v, rfl⟩ := coordE.surjective c
  rw [AddMonoidHom.comp_apply, ← coordE_altAct, ← coordE_altAct, ← coordE_altAct, altAct_mul]

theorem actC_one : actC 1 = AddMonoidHom.id U4 := by
  refine AddMonoidHom.ext fun c => ?_
  obtain ⟨v, rfl⟩ := coordE.surjective c
  rw [← coordE_altAct, altAct_one]
  rfl

theorem rep_cell (hg : gSpec) (q : Fin 15) : ∀ w : List (Fin 5),
    RepU ((actC (vtx w)).comp (Pi.evalAddMonoidHom (fun _ : Fin 15 => U4) q)) (vRows w q.val)
  | [] => by
    change RepU ((actC 1).comp _) (selRows q.val)
    rw [actC_one, AddMonoidHom.id_comp]
    exact rep_eval q
  | k :: w => by
    change RepU ((actC (sw k * vtx w)).comp _) (mulG (gRows.getD k.val []) (vRows w q.val))
    rw [actC_mul, AddMonoidHom.comp_assoc]
    exact rep_comp_act hg k (rep_cell hg q w)

theorem rep_cyc (hg : gSpec) (i : Fin 34) : RepU (cycHom i) (cycRows (cycles i)) := by
  unfold cycHom cycRows
  exact rep_sum (fun c : List (Fin 5) × Fin 15 =>
    (actC (vtx c.1)).comp (Pi.evalAddMonoidHom (fun _ : Fin 15 => U4) c.2))
    (fun c => vRows c.1 c.2.val) (cycles i) fun c _ => rep_cell hg c.2 c.1

theorem rep_sparse {p q : ℕ} (g : (Fin n → U4) →+ (Fin q → U4)) (G : ℕ → List ℕ)
    (hG : ∀ q0 : Fin q, RepU ((Pi.evalAddMonoidHom (fun _ : Fin q => U4) q0).comp g) (G q0.val))
    (k : Fin p) : ∀ l : List (Fin p × Fin 4 × Fin q × Fin 4),
      RepU ((Pi.evalAddMonoidHom (fun _ : Fin p => U4) k).comp ((sparse l).comp g))
        (sparseRows l G k.val)
  | [] => fun d q1 e => by simp [sparse, sparseRows, bitZ_zero]
  | ⟨a1, a2, a3, a4⟩ :: l => fun d q1 e => by
    have hs : ∀ y, sparse (⟨a1, a2, a3, a4⟩ :: l) y = Pi.single a1 (Pi.single a2 (y a3 a4)) +
        sparse l y := fun y => by
      simp [sparse]
    have ih := rep_sparse g G hG k l d q1 e
    have hr : sparseRows (⟨a1, a2, a3, a4⟩ :: l) G k.val = if a1.val = k.val then
        xorRows (unitRows a2.val ((G a3.val).getD a4.val 0)) (sparseRows l G k.val)
        else sparseRows l G k.val := rfl
    simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply] at ih ⊢
    rw [hs, Pi.add_apply, Pi.add_apply, hr]
    by_cases h1 : a1 = k
    · subst h1
      rw [if_pos rfl, getD_xorRows, bitZ_xor, ih, getD_unitRows, Pi.single_eq_same]
      congr 1
      by_cases h2 : d = a2
      · subst h2
        rw [if_pos rfl, Pi.single_eq_same]
        have := hG a3 a4 q1 e
        simpa using this
      · rw [Pi.single_eq_of_ne h2, if_neg (fun h => h2 (Fin.ext h)), bitZ_zero]
    · rw [if_neg (fun h => h1 (Fin.ext h)), Pi.single_eq_of_ne (Ne.symm h1), Pi.zero_apply,
        zero_add, ih]

theorem rep_corr (k : Fin 5) :
    RepU ((Pi.evalAddMonoidHom (fun _ : Fin 5 => U4) k).comp corr) (corrBlk k.val) := by
  have h := rep_sparse (AddMonoidHom.id (Fin 15 → U4)) selRows
    (fun q0 => by rw [AddMonoidHom.comp_id]; exact rep_eval q0) k corrL
  rw [AddMonoidHom.comp_id] at h
  exact h

theorem neg_U4 (u : U4) : -u = u := by
  funext i
  exact ZMod.neg_eq_self_mod_two (u i)

theorem rep_fox (hg : gSpec) (c : (Fin 15 → U4) →+ (Fin 5 → U4))
    (hc : ∀ k : Fin 5, RepU ((Pi.evalAddMonoidHom (fun _ : Fin 5 => U4) k).comp c) (corrBlk k.val)) :
    ∀ w : List (Letter 5), RepU ((Ext.fox actC sw w).comp c) (foxRows w)
  | [] => rep_congr (fun _ => rfl) rep_zero
  | (k, true) :: w => rep_congr (fun _ => rfl) (rep_add (hc k) (rep_comp_act hg k (rep_fox hg c hc w)))
  | (k, false) :: w => rep_congr (fun x => by
      change actC (sw k) (c x k + Ext.fox actC sw w (c x)) =
        actC (sw k)⁻¹ (-(c x k) + Ext.fox actC sw w (c x))
      rw [sw_inv, neg_U4])
      (rep_comp_act hg k (rep_add (hc k) (rep_fox hg c hc w)))

theorem lam_bas (q : Fin 15) (e : Fin 4) : ∀ L : List (Fin 15 × Fin 4),
    ((L.map fun a => (Pi.evalAddMonoidHom (fun _ : Fin 4 => ZMod 2) a.2).comp
      (Pi.evalAddMonoidHom (fun _ : Fin 15 => U4) a.1)).sum) (bas q e) =
      bitZ (L.foldr (fun a acc => 2 ^ (4 * a.1.val + a.2.val) ^^^ acc) 0) (4 * q.val + e.val)
  | [] => by simp [bitZ_zero]
  | a :: L => by
    rw [List.map_cons, List.sum_cons, AddMonoidHom.add_apply, lam_bas q e L, List.foldr_cons,
      bitZ_xor, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, Pi.evalAddMonoidHom_apply,
      bas_bit]

theorem rep_lam (ht : titsSpec) (p : Fin 15) :
    RepU ((Pi.evalAddMonoidHom (fun _ : Fin 15 => U4) p).comp
      (((smulAddHom (ZMod 2) (Fin 15 → U4)).flip titsVal).comp lamHom)) (lamBlk p.val) := by
  intro d q e
  have hb : (lamBlk p.val).getD d.val 0 = lamC (titsN.getD p.val 0) d.val := by
    fin_cases d <;> rfl
  have hl : lamHom (bas q e) = bitZ lamRow (4 * q.val + e.val) := lam_bas q e lamL
  simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddMonoidHom.flip_apply,
    smulAddHom_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb, hl, ht, lamC, bitZ_ite, mul_comm]

theorem rep_lhs (hg : gSpec) (ht : titsSpec) (p : Fin 15) :
    RepU ((Pi.evalAddMonoidHom (fun _ : Fin 15 => U4) p).comp certLHS) (lhsBlk p.val) :=
  rep_congr (fun _ => (add_assoc _ _ _).symm)
    (rep_add (rep_eval p) (rep_add (rep_fox hg corr rep_corr (rel p)) (rep_lam ht p)))

theorem getD_map' {α β : Type*} (f : α → β) (d : α) : ∀ (l : List α) (i : ℕ),
    (l.map f).getD i (f d) = f (l.getD i d)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_map' f d l i

theorem rep_rhs (hg : gSpec) (p : Fin 15) :
    RepU ((Pi.evalAddMonoidHom (fun _ : Fin 15 => U4) p).comp certRHS) (rhsBlk certL p.val) :=
  rep_sparse (Pi.addMonoidHom cycHom) (fun q => cycBlocks.getD q []) (fun q0 => by
    have h : cycBlocks.getD q0.val [] = cycRows (cycles q0) := getD_map' cycRows [] cyclesL q0.val
    rw [h]
    exact rep_cyc hg q0) p certL

theorem allBelow_spec {f : ℕ → Bool} : ∀ m, allBelow m f = true → ∀ p < m, f p = true
  | 0, _, _, hp => absurd hp (Nat.not_lt_zero _)
  | m + 1, h, p, hp => by
    rw [allBelow, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · exact allBelow_spec m h.2 p hp
    · exact h.1

theorem getD_norm4 (l : List ℕ) (d : Fin 4) : (norm4 l).getD d.val 0 = l.getD d.val 0 := by
  fin_cases d <;> rfl

theorem ext_bas {m : ℕ} (f g : (Fin n → U4) →+ (Fin m → U4))
    (h : ∀ q e, f (bas q e) = g (bas q e)) : f = g := by
  refine AddMonoidHom.functions_ext _ _ _ fun q x => ?_
  have hx : x = (Pi.single 0 (x 0) : U4) + (Pi.single 1 (x 1) : U4) + (Pi.single 2 (x 2) : U4) +
      (Pi.single 3 (x 3) : U4) := by
    funext i
    fin_cases i <;> simp
  have hs : ∀ (e : Fin 4) (a : ZMod 2), f (Pi.single q (Pi.single e a)) =
      g (Pi.single q (Pi.single e a)) := by
    intro e a
    have h01 : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases h01 a with rfl | rfl
    · simp only [Pi.single_zero, map_zero]
    · exact h q e
  rw [hx]
  simp only [Pi.single_add, map_add, hs]

theorem certLHS_eq_certRHS_k (hg : gSpec) (ht : titsSpec) (h : certOKi = true) :
    certLHS = certRHS := by
  apply ext_bas
  intro q e
  funext p d
  have h' : allBelow 15 (fun p => decide (norm4 (lhsBlk p) = norm4 (rhsBlk certL p))) = true := h
  have hp := of_decide_eq_true
    (allBelow_spec (f := fun p => decide (norm4 (lhsBlk p) = norm4 (rhsBlk certL p))) 15 h'
      p.val p.isLt)
  have h1 := rep_lhs hg ht p d q e
  have h2 := rep_rhs hg p d q e
  simp only [AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply] at h1 h2
  rw [h1, h2, ← getD_norm4, hp, getD_norm4]

end CFSG.KC.Stroth77NS
