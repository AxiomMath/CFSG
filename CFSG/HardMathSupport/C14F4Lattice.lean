module

public import CFSG.HardMathSupport.C14IdxDet
public import CFSG.HardMathSupport.C14F4LatticeK3
public import CFSG.HardMathSupport.C14F4LatticeK2
public import CFSG.HardMathSupport.C14F4LatticeK1
public import CFSG.HardMathSupport.C14F4LatticeRootCert
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdxRee

public section

namespace CFSG.HardMathSupport.C14F4Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.C14IdxDet
  CFSG.HardMathSupport.C14F4LatticeCheck CFSG.HardMathSupport.C14F4LatticeCheck.Q4

instance : DecidableEq Q4 := fun x y => decidable_of_iff (beq x y = true) beq_iff

@[expose] def toF (x : Q4) : Fin Tag.F4.rank → ℤ := ![x.a, x.b, x.c, x.d]

@[expose] def ofF (v : Fin Tag.F4.rank → ℤ) : Q4 :=
  ⟨v ⟨0, by decide⟩, v ⟨1, by decide⟩, v ⟨2, by decide⟩, v ⟨3, by decide⟩⟩

theorem toF_ofF (v : Fin Tag.F4.rank → ℤ) : toF (ofF v) = v := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨n + 4, h⟩ => exact absurd h (by change ¬ n + 4 < 4; omega)

theorem ofF_toF (x : Q4) : ofF (toF x) = x := rfl

theorem toF_injective : Function.Injective toF := fun x y h => by
  rw [← ofF_toF x, h, ofF_toF]

theorem toF_add (x y : Q4) : toF (x + y) = toF x + toF y := by
  rw [← toF_ofF (toF x + toF y)]; rfl

theorem toF_sub (x y : Q4) : toF (x - y) = toF x - toF y := by
  rw [← toF_ofF (toF x - toF y)]; rfl

theorem toF_neg (x : Q4) : toF (-x) = -toF x := by
  rw [← toF_ofF (-toF x)]; rfl

theorem toF_smul (n : ℤ) (x : Q4) : toF (n • x) = n • toF x := by
  rw [← toF_ofF (n • toF x)]; rfl

theorem toF_zero : toF 0 = 0 := by
  rw [← toF_ofF 0]; rfl

theorem ofF_zero : ofF 0 = 0 := rfl

theorem sum_toF (x : Q4) (v : Fin Tag.F4.rank → ℤ) : ∑ i, toF x i * v i = dot x (ofF v) := by
  change ∑ i : Fin 4, toF x i * v i = _
  rw [Fin.sum_univ_four]
  rfl

theorem dot_comm (x y : Q4) : dot x y = dot y x := by simp only [dot]; ring

theorem dot_sub_left (x y z : Q4) : dot (x - y) z = dot x z - dot y z := by
  simp only [dot, sub_a, sub_b, sub_c, sub_d]; ring

theorem dot_neg_left (x z : Q4) : dot (-x) z = -dot x z := by
  simp only [dot, neg_a, neg_b, neg_c, neg_d]; ring

theorem dot_zero_right (x : Q4) : dot x 0 = 0 := by simp only [dot, zero_a, zero_b, zero_c, zero_d]; ring

theorem certRoots_all : (List.range 48).all (fun k =>
    f4Roots.any fun q => beq q (ofF (f4Certificate.root k))) = true := by decide +kernel

theorem roots_all : f4Roots.all (fun q =>
    (List.range 48).any fun k => beq q (ofF (f4Certificate.root k))) = true := by
  decide +kernel

theorem certRoots_length : f4Certificate.roots.length = 48 := rfl

theorem isRoot_iff (v : Fin Tag.F4.rank → ℤ) : IsRoot Tag.F4 v ↔ ∃ q ∈ f4Roots, toF q = v := by
  rw [RootCertificate.isRoot_iff (C := f4Certificate)
    CFSG.HardMathSupport.C14F4LatticeRootCert.f4Certificate_check', certRoots_length]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨q, hq, hqk⟩ :=
      List.any_eq_true.1 (List.all_eq_true.1 certRoots_all k (List.mem_range.2 hk))
    exact ⟨q, hq, by rw [beq_iff.1 hqk, toF_ofF]⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨k, hk, hqk⟩ := List.any_eq_true.1 (List.all_eq_true.1 roots_all q hq)
    exact ⟨k, List.mem_range.1 hk, by rw [beq_iff.1 hqk, toF_ofF]⟩

theorem f4Roots_nodup : f4Roots.Nodup := by decide +kernel

theorem f4Pos_nodup : f4Pos.Nodup := by decide +kernel

theorem mem_f4Roots {r : Q4} : r ∈ f4Roots ↔ r ∈ f4Pos ∨ ∃ q ∈ f4Pos, r = -q := by
  rw [f4Roots, List.mem_append, List.mem_map]
  exact or_congr Iff.rfl ⟨fun ⟨q, hq, h⟩ => ⟨q, hq, h.symm⟩, fun ⟨q, hq, h⟩ => ⟨q, hq, h.symm⟩⟩

theorem sum_sub_toF (u v lam : Fin Tag.F4.rank → ℤ) :
    ∑ i, (u i - v i) * lam i = dot (ofF u - ofF v) (ofF lam) := by
  rw [← sum_toF, toF_sub, toF_ofF, toF_ofF]
  rfl

theorem wtEquiv_iff_of_frame {Ψ : Set (Fin Tag.F4.rank → ℤ)} {B K : List Q4}
    (hΨ : ∀ lam, PerpOf (τ := Tag.F4) Ψ lam ↔ ∀ b ∈ B, dot b (ofF lam) = 0) (hF : Frame B K)
    (u v : Fin Tag.F4.rank → ℤ) :
    WtEquiv (τ := Tag.F4) Ψ u v ↔ ∀ k ∈ K, dot k (ofF u) = dot k (ofF v) := by
  constructor
  · intro h k hk
    have hk' : PerpOf (τ := Tag.F4) Ψ (toF k) := (hΨ _).2 fun b hb => by
      rw [ofF_toF]; exact hF.1 b hb k hk
    have := h _ hk'
    rw [sum_sub_toF, ofF_toF, dot_sub_left] at this
    rw [dot_comm k, dot_comm k]
    linarith
  · intro h lam hlam
    rw [sum_sub_toF]
    refine hF.2 _ _ ((hΨ lam).1 hlam) fun k hk => ?_
    rw [dot_comm, dot_sub_left, dot_comm _ k, dot_comm _ k, h k hk, sub_self]

theorem sum_map_ite_eq_length_filter (p : Q4 → Bool) (l : List Q4) :
    (l.map fun γ => if p γ = true then (1 : ℕ) else 0).sum = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    cases p a <;> simp [add_comm]

theorem barEq_iff (K : List Q4) (u v : Q4) :
    barEq K u v = true ↔ ∀ k ∈ K, dot k u = dot k v := by
  simp only [barEq, List.all_eq_true, beq_iff_eq]

theorem card_wtClass {Ψ : Set (Fin Tag.F4.rank → ℤ)} {K : List Q4}
    (hK : ∀ u v, WtEquiv (τ := Tag.F4) Ψ u v ↔ ∀ k ∈ K, dot k (ofF u) = dot k (ofF v))
    (β : Q4) (hβ : IsRoot Tag.F4 (toF β)) :
    Nat.card (wtClass (τ := Tag.F4) Ψ (Sum.inr ⟨toF β, hβ⟩)) = classSize K β := by
  classical
  let e : Fin f4Roots.length → {v // IsRoot Tag.F4 v} := fun j =>
    ⟨toF f4Roots[(j : ℕ)], (isRoot_iff _).2 ⟨_, List.getElem_mem _, rfl⟩⟩
  have he : Function.Bijective e := by
    refine ⟨fun j j' h => ?_, fun ⟨v, hv⟩ => ?_⟩
    · have h' : f4Roots[(j : ℕ)] = f4Roots[(j' : ℕ)] := toF_injective (congrArg Subtype.val h)
      exact Fin.ext ((f4Roots_nodup.getElem_inj_iff).1 h')
    · obtain ⟨q, hq, rfl⟩ := (isRoot_iff v).1 hv
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
      exact ⟨⟨j, hj⟩, rfl⟩
  let φ : Fin Tag.F4.rank ⊕ Fin f4Roots.length ≃ Label Tag.F4 :=
    Equiv.sumCongr (Equiv.refl _) (Equiv.ofBijective e he)
  rw [← Nat.card_congr (φ.subtypeEquiv fun _ => Iff.rfl), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have h0 : ∀ i, (φ (Sum.inl i) ∈ wtClass (τ := Tag.F4) Ψ (Sum.inr ⟨toF β, hβ⟩)) ↔
      K.all (fun k => dot k β == 0) = true := fun i => by
    change WtEquiv (τ := Tag.F4) Ψ 0 (toF β) ↔ _
    rw [hK, ofF_zero, ofF_toF]
    simp only [List.all_eq_true, beq_iff_eq, dot_zero_right]
    exact forall₂_congr fun _ _ => eq_comm
  have h1 : ∀ j, (φ (Sum.inr j) ∈ wtClass (τ := Tag.F4) Ψ (Sum.inr ⟨toF β, hβ⟩)) ↔
      barEq K f4Roots[(j : ℕ)] β = true := fun j => by
    change WtEquiv (τ := Tag.F4) Ψ (toF f4Roots[(j : ℕ)]) (toF β) ↔ _
    rw [hK, ofF_toF, ofF_toF, barEq_iff]
  simp only [h0, h1]
  rw [Fin.sum_univ_fun_getElem f4Roots (fun γ => if barEq K γ β = true then 1 else 0),
    sum_map_ite_eq_length_filter, classSize, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  split_ifs <;> rfl

theorem foldl_comb_mem {C : AddSubgroup (Fin Tag.F4.rank → ℤ)} (k : Q4) :
    ∀ (S : List Q4) (p : Q4), toF p ∈ C → (∀ s ∈ S, toF s ∈ C) →
      toF (S.foldl (comb k) p) ∈ C
  | [], _, hp, _ => hp
  | s :: S, p, hp, hS => by
    rw [List.foldl_cons]
    refine foldl_comb_mem k S _ ?_ fun s' hs' => hS s' (List.mem_cons_of_mem _ hs')
    rw [comb, toF_add, toF_smul, toF_smul]
    exact C.add_mem (C.zsmul_mem hp _) (C.zsmul_mem (hS s List.mem_cons_self) _)

theorem runK_mem {C : AddSubgroup (Fin Tag.F4.rank → ℤ)} :
    ∀ (K S : List Q4) (t : Q4), (∀ s ∈ S, toF s ∈ C) → toF t - toF (runK K S t) ∈ C
  | [], _, t, _ => by rw [runK, sub_self]; exact C.zero_mem
  | k :: K, S, t, hS => by
    rw [runK]
    have hp : toF (S.foldl (comb k) 0) ∈ C :=
      foldl_comb_mem k S 0 (by rw [toF_zero]; exact C.zero_mem) hS
    have hS' : ∀ s ∈ (stepK k S t).1, toF s ∈ C := by
      intro s hs
      simp only [stepK, List.mem_map] at hs
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      rw [toF_sub, toF_smul]
      exact C.sub_mem (hS s₀ hs₀) (C.zsmul_mem hp _)
    have h1 : toF t - toF (stepK k S t).2 ∈ C := by
      simp only [stepK]
      rw [toF_sub, toF_smul, sub_sub_cancel]
      exact C.zsmul_mem hp _
    have := C.add_mem h1 (runK_mem K _ (stepK k S t).2 hS')
    rwa [sub_add_sub_cancel] at this

theorem basis_six : ∀ i : Fin Tag.F4.rank,
    ∃ e ∈ basis, toF ((6 : ℤ) • e) = (6 • Pi.single i 1 : Fin Tag.F4.rank → ℤ) := by
  decide

theorem latOK_sound {Ψ : Set (Fin Tag.F4.rank → ℤ)} {K : List Q4}
    (hK : ∀ u v, WtEquiv (τ := Tag.F4) Ψ u v ↔ ∀ k ∈ K, dot k (ofF u) = dot k (ofF v))
    (hlat : latOK K = true) (i : Fin Tag.F4.rank) :
    (6 • Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ AddSubgroup.closure (latGen (τ := Tag.F4) Ψ) := by
  set C := AddSubgroup.closure (latGen (τ := Tag.F4) Ψ)
  have hker : ∀ w : Q4, (∀ k ∈ K, dot k w = 0) → toF w ∈ C := fun w hw =>
    AddSubgroup.subset_closure (Or.inl ((hK _ _).2 fun k hk => by
      rw [ofF_toF, ofF_zero, dot_zero_right, hw k hk]))
  have hgen : ∀ s ∈ f4Roots.map (fun β => (classSize K β : ℤ) • β), toF s ∈ C := by
    intro s hs
    obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hs
    have hr : IsRoot Tag.F4 (toF β) := (isRoot_iff _).2 ⟨β, hβ, rfl⟩
    refine AddSubgroup.subset_closure (Or.inr ⟨Sum.inr ⟨toF β, hr⟩, ?_⟩)
    change (Nat.card (wtClass (τ := Tag.F4) Ψ (Sum.inr ⟨toF β, hr⟩)) : ℤ) • toF β = _
    rw [card_wtClass hK β hr, toF_smul]
  obtain ⟨e, he, he6⟩ := basis_six i
  rw [← he6]
  unfold latOK at hlat
  simp only [List.all_eq_true, beq_iff_eq] at hlat
  have hf := hlat e he
  have h1 := runK_mem K _ ((6 : ℤ) • e) hgen
  have h2 := hker _ hf
  have := C.add_mem h1 h2
  rwa [sub_add_cancel] at this

@[expose] def vQ (q : Q4) : Fin 4 → ℚ := ![(q.a : ℚ), q.b, q.c, q.d]

theorem vQ_injective : Function.Injective vQ := fun x y h => by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [vQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Int.cast_inj] at h0 h1 h2 h3
  exact Q4.ext h0 h1 h2 h3

@[expose] def fL (w : Q4) : (Fin 4 → ℚ) →ₗ[ℚ] ℚ where
  toFun v := v 0 * w.a + v 1 * w.b + v 2 * w.c + v 3 * w.d
  map_add' _ _ := by simp only [Pi.add_apply]; ring
  map_smul' _ _ := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem fL_vQ (w q : Q4) : fL w (vQ q) = (dot q w : ℚ) := by
  simp only [fL, LinearMap.coe_mk, AddHom.coe_mk, vQ, dot, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Int.cast_add, Int.cast_mul]

theorem smul_vQ_sum3 {x y z : Q4} {a b c : ℤ} (h : a • x + b • y + c • z = 0) :
    ∑ j, (![(a : ℚ), b, c] j) • vQ (![x, y, z] j) = 0 := by
  have ha := congrArg Q4.a h
  have hb := congrArg Q4.b h
  have hc := congrArg Q4.c h
  have hd := congrArg Q4.d h
  simp only [add_a, add_b, add_c, add_d, smul_a, smul_b, smul_c, smul_d, zero_a, zero_b, zero_c,
    zero_d] at ha hb hc hd
  funext m
  fin_cases m <;> simp [vQ, Fin.sum_univ_three] <;>
    first | exact_mod_cast ha | exact_mod_cast hb | exact_mod_cast hc | exact_mod_cast hd

theorem smul_vQ_sum2 {x y : Q4} {a b : ℤ} (h : a • x + b • y = 0) :
    ∑ j, (![(a : ℚ), b] j) • vQ (![x, y] j) = 0 := by
  have ha := congrArg Q4.a h
  have hb := congrArg Q4.b h
  have hc := congrArg Q4.c h
  have hd := congrArg Q4.d h
  simp only [add_a, add_b, add_c, add_d, smul_a, smul_b, smul_c, smul_d, zero_a, zero_b, zero_c,
    zero_d] at ha hb hc hd
  funext m
  fin_cases m <;> simp [vQ, Fin.sum_univ_two] <;>
    first | exact_mod_cast ha | exact_mod_cast hb | exact_mod_cast hc | exact_mod_cast hd

theorem inj2 {x y : Q4} (h : x ≠ y) : Function.Injective ![x, y] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem inj3 {x y z : Q4} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem reduce (Ψ : Set (Fin Tag.F4.rank → ℤ)) (hΨ : ∀ α ∈ Ψ, IsRoot Tag.F4 α) :
    (∀ lam, PerpOf (τ := Tag.F4) Ψ lam → lam = 0) ∨
      ∃ B K : List Q4, latOK K = true ∧ Frame B K ∧
        ∀ lam, PerpOf (τ := Tag.F4) Ψ lam ↔ ∀ b ∈ B, dot b (ofF lam) = 0 := by
  classical
  set P : Set Q4 := {q | q ∈ f4Pos ∧ (toF q ∈ Ψ ∨ -toF q ∈ Ψ)} with hPdef
  have hP : ∀ lam, PerpOf (τ := Tag.F4) Ψ lam ↔ ∀ q ∈ P, dot q (ofF lam) = 0 := by
    intro lam
    constructor
    · rintro h q ⟨-, hq | hq⟩
      · rw [← sum_toF]; exact h _ hq
      · have := h _ hq
        rw [← toF_neg, sum_toF, dot_neg_left, neg_eq_zero] at this
        exact this
    · intro h α hα
      obtain ⟨r, hr, rfl⟩ := (isRoot_iff α).1 (hΨ α hα)
      rcases mem_f4Roots.1 hr with hr | ⟨q, hq, rfl⟩
      · rw [sum_toF]; exact h r ⟨hr, Or.inl hα⟩
      · rw [sum_toF, dot_neg_left, h q ⟨hq, Or.inr (by rw [← toF_neg]; exact hα)⟩, neg_zero]
  obtain ⟨t, hts, hcard, hspan, hli⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℚ (vQ '' P)
  have hT : ∀ w : Q4, (∀ q ∈ P, dot q w = 0) ↔ ∀ a ∈ t, fL w a = 0 := by
    intro w
    constructor
    · intro h a ha
      obtain ⟨q, hq, rfl⟩ := hts ha
      rw [fL_vQ, h q hq, Int.cast_zero]
    · intro h q hq
      have hle : Submodule.span ℚ (t : Set (Fin 4 → ℚ)) ≤ LinearMap.ker (fL w) :=
        Submodule.span_le.2 fun a ha => h a ha
      have hmem : vQ q ∈ Submodule.span ℚ (t : Set (Fin 4 → ℚ)) := by
        rw [hspan]; exact Submodule.subset_span ⟨q, hq, rfl⟩
      have := hle hmem
      rw [LinearMap.mem_ker, fL_vQ] at this
      exact_mod_cast this
  have hcard4 : t.card ≤ 4 := by
    rw [hcard]
    exact (Submodule.finrank_le _).trans (by simp)
  by_cases h4 : t.card = 4
  · left
    intro lam hlam
    have htop : Submodule.span ℚ (t : Set (Fin 4 → ℚ)) = ⊤ := by
      have := hli.span_eq_top_of_card_eq_finrank' (by simp [h4])
      simpa using this
    have hk : ∀ a, fL (ofF lam) a = 0 := fun a => by
      have hle : Submodule.span ℚ (t : Set (Fin 4 → ℚ)) ≤ LinearMap.ker (fL (ofF lam)) :=
        Submodule.span_le.2 fun a ha => (hT _).1 ((hP lam).1 hlam) a ha
      rw [htop] at hle
      exact hle (Submodule.mem_top (x := a))
    rw [← toF_ofF lam, ← toF_zero]
    congr 1
    have e0 := hk (Pi.single 0 1)
    have e1 := hk (Pi.single 1 1)
    have e2 := hk (Pi.single 2 1)
    have e3 := hk (Pi.single 3 1)
    simp [fL] at e0 e1 e2 e3
    exact Q4.ext e0 e1 e2 e3
  right
  set T := f4Pos.filter fun q => decide (vQ q ∈ t) with hTdef
  have hTsub : T.Sublist f4Pos := List.filter_sublist
  have hTnodup : T.Nodup := hTsub.nodup f4Pos_nodup
  have hmemT : ∀ q, q ∈ T ↔ vQ q ∈ t := fun q => by
    rw [hTdef, List.mem_filter, decide_eq_true_iff]
    refine ⟨And.right, fun h => ⟨?_, h⟩⟩
    obtain ⟨q', ⟨hq', -⟩, hq'q⟩ := hts h
    rwa [← vQ_injective hq'q]
  have hTlen : T.length = t.card := by
    have hnd : (T.map vQ).Nodup := hTnodup.map vQ_injective
    rw [← List.length_map (f := vQ), ← List.toFinset_card_of_nodup hnd]
    congr 1
    ext a
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩; exact (hmemT q).1 hq
    · intro ha
      obtain ⟨q, -, rfl⟩ := hts ha
      exact ⟨q, (hmemT q).2 ha, rfl⟩
  have hperp : ∀ lam, PerpOf (τ := Tag.F4) Ψ lam ↔ ∀ b ∈ T, dot b (ofF lam) = 0 := by
    intro lam
    rw [hP, hT]
    constructor
    · intro h b hb
      have := h _ ((hmemT b).1 hb)
      rw [fL_vQ] at this
      exact_mod_cast this
    · intro h a ha
      obtain ⟨q, -, rfl⟩ := hts ha
      rw [fL_vQ, h q ((hmemT q).2 ha), Int.cast_zero]
  have hli' : ∀ (n : ℕ) (g : Fin n → Q4), (∀ j, g j ∈ T) → Function.Injective g →
      LinearIndependent ℚ (fun j => vQ (g j)) := by
    intro n g hg hinj
    have := hli.comp (fun j => (⟨vQ (g j), (hmemT _).1 (hg j)⟩ : (t : Set (Fin 4 → ℚ))))
      fun j j' h => hinj (vQ_injective (congrArg Subtype.val h))
    exact this
  have hsl : T ∈ f4Pos.sublistsLen T.length := List.mem_sublistsLen.2 ⟨hTsub, rfl⟩
  match hT' : T, hsl with
  | [], _ => exact ⟨[], basis, rank0OK_eq, frame0, hperp⟩
  | [x], hsl =>
    have hx : x ∈ f4Pos := (List.mem_sublistsLen.1 hsl).1.subset List.mem_cons_self
    have hc : case1 x = true := List.all_eq_true.1 rank1OK_eq x hx
    rcases Bool.or_eq_true_iff.1 hc with h | h
    · obtain ⟨K, hK, hF⟩ := compl1_spec h
      exact ⟨[x], K, hK, hF, hperp⟩
    · exfalso
      have hLI := hli' 1 ![x] (fun j => by fin_cases j; simp) (fun i j _ => Subsingleton.elim i j)
      have := hLI.ne_zero 0
      simp [dep1_spec h, vQ] at this
  | [x, y], hsl =>
    have hc : case2 x y = true := by
      have := List.all_eq_true.1 rank2OK_eq _ hsl
      simpa using this
    rcases Bool.or_eq_true_iff.1 hc with h | h
    · obtain ⟨K, hK, hF⟩ := compl2_spec h
      exact ⟨[x, y], K, hK, hF, hperp⟩
    · exfalso
      obtain ⟨a, b, hne, heq⟩ := dep2_spec h
      have hxy : x ≠ y := by simpa using hTnodup
      have hLI := hli' 2 ![x, y] (fun j => by fin_cases j <;> simp) (inj2 hxy)
      have h0 := Fintype.linearIndependent_iff.1 hLI _ (smul_vQ_sum2 heq)
      exact hne ⟨by simpa using h0 0, by simpa using h0 1⟩
  | [x, y, z], hsl =>
    have hc : case3 x y z = true := by
      have := List.all_eq_true.1 rank3OK_eq _ hsl
      simpa using this
    rcases Bool.or_eq_true_iff.1 hc with h | h
    · obtain ⟨K, hK, hF⟩ := line3_spec h linesOK_eq
      exact ⟨[x, y, z], K, hK, hF, hperp⟩
    · exfalso
      obtain ⟨a, b, c, hne, heq⟩ := dep3_spec h
      have hnd : (x ≠ y ∧ x ≠ z) ∧ y ≠ z := by simpa using hTnodup
      have hLI := hli' 3 ![x, y, z] (fun j => by fin_cases j <;> simp)
        (inj3 hnd.1.1 hnd.1.2 hnd.2)
      have h0 := Fintype.linearIndependent_iff.1 hLI _ (smul_vQ_sum3 heq)
      exact hne ⟨by simpa using h0 0, by simpa using h0 1, by simpa using h0 2⟩
  | _ :: _ :: _ :: _ :: l, _ =>
    exfalso
    have := hTlen
    simp only [List.length_cons] at this
    omega

theorem f4ZSLattice : F4ZSLattice := by
  intro Ψ hΨ i
  rcases reduce Ψ hΨ with h0 | ⟨B, K, hlat, hF, hperp⟩
  · refine AddSubgroup.subset_closure (Or.inl fun lam hlam => ?_)
    rw [h0 lam hlam]
    simp
  · exact latOK_sound (wtEquiv_iff_of_frame hperp hF) hlat i

section Corollaries

variable {L : Type} [Field L] {ι : Type}

theorem pow_six_of_mem_famZ_famS_F4
    [IsAlgClosed L] (a : ι → Fin Tag.F4.rank → Lˣ)
    (g : adjointGroup Tag.F4 L) (hgZ : (g : ModGL Tag.F4 L) ∈ CFSG.HardMathSupport.C14Idx.famZ a)
    (hgS : g ∈ CFSG.HardMathSupport.C14Idx.famS a) : g ^ 6 = 1 :=
  pow_six_of_mem_famZ_famS_F4_of_lattice f4ZSLattice a g hgZ hgS

theorem excF4PowSixInput
    : CFSG.HardMathSupport.C14Idx.ExcF4PowSixInput :=
  fun _ _ _ _ a g hgZ hgS => pow_six_of_mem_famZ_famS_F4 a g hgZ hgS

end Corollaries

end CFSG.HardMathSupport.C14F4Lattice
