module

public import CFSG.ClassicalInvolution.Solomon73.YamakiPres
public import Certificates.Data.YamakiEnum

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open Matrix

theorem zmod2_val_le_one (a : ZMod 2) : a.val ≤ 1 := by
  have := ZMod.val_lt a
  omega

@[expose] def vec6 (x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2) : Fin 3 ⊕ Fin 3 → ZMod 2 :=
  Sum.elim ![x₀, x₁, x₂] ![x₃, x₄, x₅]

theorem eq_vec6 (v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    v = vec6 (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 0)) (v (.inr 1)) (v (.inr 2)) := by
  funext a
  rcases a with k | k <;> fin_cases k <;> rfl

theorem codeOf_vec6_lt : ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2, codeOf (vec6 x₀ x₁ x₂ x₃ x₄ x₅) < 64 := by
  decide

theorem vecOf_codeOf_vec6 : ∀ x₀ x₁ x₂ x₃ x₄ x₅ : ZMod 2,
    vecOf (codeOf (vec6 x₀ x₁ x₂ x₃ x₄ x₅)) = vec6 x₀ x₁ x₂ x₃ x₄ x₅ := by
  decide

theorem codeOf_lt (v : Fin 3 ⊕ Fin 3 → ZMod 2) : codeOf v < 64 := by
  rw [eq_vec6 v]
  exact codeOf_vec6_lt _ _ _ _ _ _

theorem vecOf_codeOf (v : Fin 3 ⊕ Fin 3 → ZMod 2) : vecOf (codeOf v) = v := by
  rw [eq_vec6 v]
  exact vecOf_codeOf_vec6 _ _ _ _ _ _

theorem codeOf_vecOf : ∀ n < 64, codeOf (vecOf n) = n := by
  decide

theorem getElem!_ofFn_nat {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem size_matArr (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (matArr A).size = 64 := Array.size_ofFn

theorem matArr_get (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) {n : ℕ} (hn : n < 64) :
    (matArr A)[n]! = codeOf (A *ᵥ vecOf n) :=
  getElem!_ofFn_nat _ hn

theorem size_compA (t u : Array ℕ) : (compA t u).size = 64 := Array.size_ofFn

theorem compA_get (t u : Array ℕ) {i : ℕ} (hi : i < 64) : (compA t u)[i]! = t[u[i]!]! :=
  getElem!_ofFn_nat _ hi

theorem size_idA : (idA ()).size = 64 := Array.size_ofFn

theorem idA_get {i : ℕ} (hi : i < 64) : (idA ())[i]! = i :=
  getElem!_ofFn_nat _ hi

theorem ext64 {t u : Array ℕ} (ht : t.size = 64) (hu : u.size = 64)
    (h : ∀ i < 64, t[i]! = u[i]!) : t = u := by
  refine Array.ext (ht.trans hu.symm) fun i hi₁ hi₂ => ?_
  have := h i (ht ▸ hi₁)
  rwa [getElem!_pos t i hi₁, getElem!_pos u i hi₂] at this

@[expose] def code (g : StatedSp 3 (ZMod 2)) : Array ℕ := matArr (spMat g)

theorem size_code (g : StatedSp 3 (ZMod 2)) : (code g).size = 64 := size_matArr _

theorem code_get (g : StatedSp 3 (ZMod 2)) {n : ℕ} (hn : n < 64) :
    (code g)[n]! = codeOf (spMat g *ᵥ vecOf n) :=
  matArr_get _ hn

theorem mulVec_vecOf (g : StatedSp 3 (ZMod 2)) {n : ℕ} (hn : n < 64) :
    spMat g *ᵥ vecOf n = vecOf (code g)[n]! := by
  rw [code_get g hn, vecOf_codeOf]

theorem code_mul (g h : StatedSp 3 (ZMod 2)) : code (g * h) = compA (code g) (code h) := by
  refine ext64 (size_code _) (size_compA _ _) fun i hi => ?_
  rw [compA_get _ _ hi, code_get h hi, code_get g (codeOf_lt _), vecOf_codeOf, code_get _ hi,
    map_mul, ← mulVec_mulVec]

theorem code_one : code 1 = idA () := by
  refine ext64 (size_code _) size_idA fun i hi => ?_
  rw [code_get _ hi, map_one, one_mulVec, codeOf_vecOf i hi, idA_get hi]

theorem code_injective : Function.Injective code := by
  intro g h hgh
  apply spMat_injective
  rw [ext_iff_mulVec]
  intro v
  rw [← vecOf_codeOf v, mulVec_vecOf g (codeOf_lt v), mulVec_vecOf h (codeOf_lt v), hgh]

theorem code_prod_map {s : ℕ → StatedSp 3 (ZMod 2)} {gs : Array (Array ℕ)} :
    ∀ w : List ℕ, (∀ i ∈ w, gs[i]! = code (s i)) → code (w.map s).prod = wordA gs w
  | [], _ => by rw [List.map_nil, List.prod_nil, code_one, wordA]
  | i :: w, hw => by
    rw [List.map_cons, List.prod_cons, code_mul, wordA, hw i List.mem_cons_self,
      code_prod_map w fun j hj => hw j (List.mem_cons_of_mem i hj)]

theorem code_yamakiSp (i : Fin 12) :
    code (yamakiSp i) = (genA ())[i.val]! := by
  rw [genA, getElem!_ofFn_nat _ i.2]
  rfl

theorem allLt_iff {n : ℕ} {p : ℕ → Bool} : allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h i _
    exact h i i.2

theorem getElem!_eq_of_getElem? {α : Type*} [Inhabited α] {a : Array α} {i : ℕ} {x : α}
    (h : a[i]? = some x) : a[i]! = x := by
  obtain ⟨hi, hx⟩ := Array.getElem?_eq_some_iff.mp h
  rw [getElem!_pos a i hi, hx]

theorem size_pos_of_getElem? {α : Type*} {a : Array α} {i : ℕ} {x : α} (h : a[i]? = some x) :
    i < a.size :=
  (Array.getElem?_eq_some_iff.mp h).1

theorem Enum.lookup_spec {E : Enum} {t : Array ℕ} {k : ℕ} (h : E.lookup t = some k) :
    k < E.elems.size ∧ E.elems[k]! = t := by
  unfold Enum.lookup at h
  split at h
  · split_ifs at h with hk
    obtain rfl := Option.some.inj h
    exact hk
  · cases h

variable {E : Enum} {gs : Array (Array ℕ)} {s : ℕ → StatedSp 3 (ZMod 2)}

theorem exists_mem_closure_of_treeOK (hgs : ∀ j < gs.size, gs[j]! = code (s j))
    (h : treeOK E gs = true) :
    ∀ i < E.elems.size, ∃ x ∈ Subgroup.closure (s '' Set.Iio gs.size), code x = E.elems[i]! := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, he⟩
    · exact ⟨1, one_mem _, by rw [code_one, getElem!_eq_of_getElem? h0]⟩
    · obtain ⟨x, hx, hxe⟩ := ih _ hp (hp.trans hi)
      refine ⟨x * s E.gen[i]!, mul_mem hx (Subgroup.subset_closure ⟨_, hg, rfl⟩), ?_⟩
      rw [code_mul, hxe, ← hgs _ hg, he]

theorem inv_eq_pow_sub_one (x : StatedSp 3 (ZMod 2)) : x⁻¹ = x ^ (orderOf x - 1) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [pow_sub_one_mul (orderOf_pos x).ne', pow_orderOf_eq_one]

theorem lookup_isSome_of_mem_closure (hgs : ∀ j < gs.size, gs[j]! = code (s j))
    (h : enumOK E gs = true) {x : StatedSp 3 (ZMod 2)}
    (hx : x ∈ Subgroup.closure (s '' Set.Iio gs.size)) : (E.lookup (code x)).isSome := by
  simp only [enumOK, Bool.and_eq_true] at h
  obtain ⟨⟨htree, hclosed⟩, hnodup⟩ := h
  have h0 : E.elems[0]? = some (idA ()) := by
    simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
    exact htree.1
  have h1 : (E.lookup (code 1)).isSome := by
    have := (allLt_iff.mp hnodup) 0 (size_pos_of_getElem? h0)
    rw [decide_eq_true_eq, getElem!_eq_of_getElem? h0] at this
    rw [code_one, this]
    rfl
  have hmul : ∀ y, (E.lookup (code y)).isSome → ∀ j < gs.size,
      (E.lookup (code (y * s j))).isSome := by
    intro y hy j hj
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hy
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have := (allLt_iff.mp ((allLt_iff.mp hclosed) k hks)) j hj
    rwa [hke, hgs j hj, ← code_mul] at this
  have hpow : ∀ y, (E.lookup (code y)).isSome → ∀ j < gs.size, ∀ m : ℕ,
      (E.lookup (code (y * s j ^ m))).isSome := by
    intro y hy j hj m
    induction m with
    | zero => rwa [pow_zero, mul_one]
    | succ m ih =>
      rw [pow_succ, ← mul_assoc]
      exact hmul _ ih j hj
  induction hx using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right y _ z hz ih =>
    obtain ⟨j, hj, rfl⟩ := hz
    exact hmul y ih j hj
  | mul_inv_cancel y _ z hz ih =>
    obtain ⟨j, hj, rfl⟩ := hz
    rw [inv_eq_pow_sub_one]
    exact hpow y ih j hj _

theorem mem_closure_iff_isSome (hgs : ∀ j < gs.size, gs[j]! = code (s j))
    (h : enumOK E gs = true) (x : StatedSp 3 (ZMod 2)) :
    x ∈ Subgroup.closure (s '' Set.Iio gs.size) ↔ (E.lookup (code x)).isSome := by
  refine ⟨lookup_isSome_of_mem_closure hgs h, fun hx => ?_⟩
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  obtain ⟨y, hy, hye⟩ := exists_mem_closure_of_treeOK hgs htree k hks
  rwa [code_injective (hke.symm.trans hye.symm)]

theorem card_closure_eq (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (h : enumOK E gs = true) :
    Nat.card (Subgroup.closure (s '' Set.Iio gs.size)) = E.elems.size := by
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  have hnodup : ∀ i < E.elems.size, E.lookup E.elems[i]! = some i := by
    simp only [enumOK, Bool.and_eq_true] at h
    simpa only [nodupOK, allLt_iff, decide_eq_true_eq] using h.2
  have hex := exists_mem_closure_of_treeOK hgs htree
  choose e he hec using hex
  have hbij : Function.Bijective fun i : Fin E.elems.size =>
      (⟨e i i.2, he i i.2⟩ : Subgroup.closure (s '' Set.Iio gs.size)) := by
    constructor
    · intro i j hij
      have hv : e i i.2 = e j j.2 := congrArg Subtype.val hij
      have hc : E.elems[i.val]! = E.elems[j.val]! := by
        rw [← hec i i.2, ← hec j j.2, hv]
      have h1 := hnodup i i.2
      rw [hc, hnodup j j.2] at h1
      exact Fin.ext (Option.some.inj h1).symm
    · intro x
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs h x.2)
      obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
      exact ⟨⟨k, hks⟩, Subtype.ext (code_injective ((hec k hks).trans hke))⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem map_mul_of_forall_mem {G G' : Type*} [Group G] [Group G'] {S : Set G} {f : G → G'}
    (h1 : f 1 = 1) (hS : ∀ x ∈ Subgroup.closure S, ∀ y ∈ S, f (x * y) = f x * f y) :
    ∀ y ∈ Subgroup.closure S, ∀ x ∈ Subgroup.closure S, f (x * y) = f x * f y := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact fun x hx => hS x hx y hy
  | one => exact fun x _ => by rw [mul_one, h1, mul_one]
  | mul y z hy hz ihy ihz =>
    intro x hx
    rw [← mul_assoc, ihz (x * y) (mul_mem hx hy), ihy x hx, ihz y hy, mul_assoc]
  | inv y hy ih =>
    intro x hx
    have e1 := ih (x * y⁻¹) (mul_mem hx (inv_mem hy))
    have e2 := ih y⁻¹ (inv_mem hy)
    rw [inv_mul_cancel_right] at e1
    rw [inv_mul_cancel, h1] at e2
    rw [eq_inv_of_mul_eq_one_left e2.symm, e1, mul_inv_cancel_right]

theorem exists_mem_closure_of_autOK {hs F : Array (Array ℕ)} {h : ℕ → StatedSp 3 (ZMod 2)}
    (hhs : ∀ j < gs.size, hs[j]! = code (h j)) (htree : treeOK E gs = true)
    (haut : autOK E gs hs F = true) :
    ∀ i < E.elems.size, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size), code m = F[i]! := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at htree
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at haut
  obtain ⟨-, hall⟩ := htree
  obtain ⟨⟨⟨⟨-, hF0⟩, hFt⟩, -⟩, -⟩ := haut
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, -⟩
    · exact ⟨1, one_mem _, by rw [code_one, getElem!_eq_of_getElem? hF0]⟩
    · rcases hFt i hi with hi0 | hFi
      · subst hi0
        exact ⟨1, one_mem _, by rw [code_one, getElem!_eq_of_getElem? hF0]⟩
      · obtain ⟨m, hm, hme⟩ := ih _ hp (hp.trans hi)
        refine ⟨m * h E.gen[i]!, mul_mem hm (Subgroup.subset_closure ⟨_, hg, rfl⟩), ?_⟩
        rw [code_mul, hme, ← hhs _ hg, hFi]

theorem exists_mulEquiv_of_autOK {hs F : Array (Array ℕ)} {h : ℕ → StatedSp 3 (ZMod 2)}
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (hhs : ∀ j < gs.size, hs[j]! = code (h j))
    (hmem : ∀ j < gs.size, h j ∈ Subgroup.closure (s '' Set.Iio gs.size))
    (henum : enumOK E gs = true) (haut : autOK E gs hs F = true) :
    ∃ φ : ↥(Subgroup.closure (s '' Set.Iio gs.size)) ≃* ↥(Subgroup.closure (s '' Set.Iio gs.size)),
      (∀ x, code (φ x : StatedSp 3 (ZMod 2)) = appF E F (code x)) ∧
      ∀ j (hj : j < gs.size), (φ ⟨s j, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩ :
        StatedSp 3 (ZMod 2)) = h j := by
  set L := Subgroup.closure (s '' Set.Iio gs.size)
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.1.1
  have hnodup : nodupOK E = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.2
  have hFcode := exists_mem_closure_of_autOK hhs htree haut
  have haut' := haut
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at haut'
  obtain ⟨⟨⟨⟨hsize, hF0⟩, -⟩, hcrit⟩, hinj⟩ := haut'
  have hL : Subgroup.closure (h '' Set.Iio gs.size) ≤ L :=
    (Subgroup.closure_le _).mpr fun _ ⟨j, hj, he⟩ => he ▸ hmem j hj
  have hpos : ∀ x ∈ L, ∃ k, E.lookup (code x) = some k :=
    fun x hx => Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hgs henum hx)
  have hex : ∀ x ∈ L, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size),
      code m = appF E F (code x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨m, hm, hme⟩ := hFcode k (Enum.lookup_spec hk).1
    exact ⟨m, hm, by rw [hme, appF, hk, Option.getD_some]⟩
  obtain ⟨f, hf, hfL⟩ : ∃ f : StatedSp 3 (ZMod 2) → StatedSp 3 (ZMod 2),
      (∀ x ∈ L, code (f x) = appF E F (code x)) ∧ ∀ x ∈ L, f x ∈ L := by
    classical
    refine ⟨fun x => if hx : ∃ m, code m = appF E F (code x) then hx.choose else 1, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, -, hme⟩ := hex x hx
      have hx' : ∃ m, code m = appF E F (code x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      exact hx'.choose_spec
    · intro x hx
      obtain ⟨m, hm, hme⟩ := hex x hx
      have hx' : ∃ m, code m = appF E F (code x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      rw [code_injective (hx'.choose_spec.trans hme.symm)]
      exact hL hm
  have hf1 : f 1 = 1 := by
    apply code_injective
    rw [hf 1 (one_mem _), code_one, appF]
    have h0 : E.elems[0]? = some (idA ()) := by
      simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
      exact htree.1
    have := (allLt_iff.mp hnodup) 0 (size_pos_of_getElem? h0)
    rw [decide_eq_true_eq, getElem!_eq_of_getElem? h0] at this
    rw [this, Option.getD_some, getElem!_eq_of_getElem? hF0]
  have hstep : ∀ x ∈ L, ∀ j < gs.size, f (x * s j) = f x * h j := by
    intro x hx j hj
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have hc := hcrit k hks j hj
    rw [hke, hgs j hj, ← code_mul] at hc
    apply code_injective
    rw [hf _ (mul_mem hx (Subgroup.subset_closure ⟨j, hj, rfl⟩)), code_mul (f x) (h j), hf x hx,
      appF, appF, hk, Option.getD_some, ← hhs j hj]
    split at hc
    · rename_i k' hk'
      rw [hk', Option.getD_some]
      exact of_decide_eq_true hc
    · cases hc
  have hgen : ∀ j < gs.size, f (s j) = h j := by
    intro j hj
    have := hstep 1 (one_mem _) j hj
    rwa [one_mul, hf1, one_mul] at this
  have hmulf := map_mul_of_forall_mem hf1 (S := s '' Set.Iio gs.size) (by
    rintro x hx _ ⟨j, hj, rfl⟩
    rw [hstep x hx j hj, hgen j hj])
  let ψ : L →* L :=
    { toFun := fun x => ⟨f x, hfL x x.2⟩
      map_one' := Subtype.ext hf1
      map_mul' := fun x y => Subtype.ext (hmulf y y.2 x x.2) }
  have hinj' : ∀ i < F.size, (firstIndex F)[F[i]!]? = some i := by
    unfold injOK at hinj
    simpa only [allLt_iff, decide_eq_true_eq] using hinj
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hxy' : f x = f y := congrArg Subtype.val hxy
    obtain ⟨k, hk⟩ := hpos x x.2
    obtain ⟨k', hk'⟩ := hpos y y.2
    have e := congrArg code hxy'
    rw [hf x x.2, hf y y.2, appF, appF, hk, hk', Option.getD_some, Option.getD_some] at e
    have hks := (Enum.lookup_spec hk).1
    have hks' := (Enum.lookup_spec hk').1
    have i1 := hinj' k (by rw [hsize]; exact hks)
    have i2 := hinj' k' (by rw [hsize]; exact hks')
    rw [e] at i1
    have hkk : k = k' := Option.some.inj (i1.symm.trans i2)
    subst hkk
    exact Subtype.ext (code_injective ((Enum.lookup_spec hk).2.symm.trans (Enum.lookup_spec hk').2))
  have hψbij : Function.Bijective ψ := (Finite.injective_iff_bijective).mp hψinj
  refine ⟨MulEquiv.ofBijective ψ hψbij, fun x => hf x x.2, fun j hj => hgen j hj⟩

end CFSG.ClassicalInvolution.Solomon73.Yamaki
