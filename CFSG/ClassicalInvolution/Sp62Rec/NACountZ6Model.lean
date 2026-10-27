module

public import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6Defs
public import CFSG.ClassicalInvolution.Sp62Rec.NACountZ6Enum
public import Certificates.Certificate550104

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open Z6NA

section Checks

theorem z6LbarCheck_holds : z6LbarCheck () = true := Certificates.certificate550104.1

theorem z6OrbCheck_holds : z6OrbCheck () = true := Certificates.certificate550104.2.1

theorem z6NormCheck_holds : z6NormCheck () = true := Certificates.certificate550104.2.2

end Checks

namespace Z6NA

section Positions

theorem size_enumA0 : (enumA0 ()).elems.size = 64 := a0EnumCheck_spec.2.1

@[expose] def a0Pos (a : ↥A0) : ℕ := z6Pos (enumA0 ()) (code (a : StatedSp 3 (ZMod 2)))

theorem a0Pos_spec (a : ↥A0) :
    a0Pos a < 64 ∧ (enumA0 ()).elems[a0Pos a]! = code (a : StatedSp 3 (ZMod 2)) := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp ((mem_A0_iff_isSome a).mp a.2)
  obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
  have : a0Pos a = k := by
    rw [a0Pos, z6Pos, hk]
    rfl
  rw [this]
  exact ⟨size_enumA0 ▸ hks, hke⟩

theorem a0Pos_lt (a : ↥A0) : a0Pos a < 64 := (a0Pos_spec a).1

theorem exists_a0El {k : ℕ} (hk : k < 64) :
    ∃ a : ↥A0, code (a : StatedSp 3 (ZMod 2)) = (enumA0 ()).elems[k]! := by
  have htree : treeOK (enumA0 ()) (gA0 ()) = true := by
    have := a0EnumCheck_spec.1
    simp only [enumOK, Bool.and_eq_true] at this
    exact this.1.1
  obtain ⟨x, hx, hxe⟩ :=
    CFSG.ClassicalInvolution.Solomon73.Yamaki.exists_mem_closure_of_treeOK gA0_get htree k
      (size_enumA0 ▸ hk)
  rw [← A0_eq_closure] at hx
  exact ⟨⟨x, hx⟩, hxe⟩

@[expose] noncomputable def a0El (k : ℕ) : ↥A0 :=
  if h : k < 64 then (exists_a0El h).choose else 1

theorem code_a0El {k : ℕ} (hk : k < 64) :
    code ((a0El k : ↥A0) : StatedSp 3 (ZMod 2)) = (enumA0 ()).elems[k]! := by
  rw [a0El, dif_pos hk]
  exact (exists_a0El hk).choose_spec

theorem a0Pos_a0El {k : ℕ} (hk : k < 64) : a0Pos (a0El k) = k := by
  obtain ⟨hlt, hspec⟩ := a0Pos_spec (a0El k)
  rw [code_a0El hk] at hspec
  have hnodup : ∀ i < (enumA0 ()).elems.size,
      (enumA0 ()).lookup (enumA0 ()).elems[i]! = some i := by
    have := a0EnumCheck_spec.1
    simp only [enumOK, Bool.and_eq_true] at this
    simpa only [nodupOK, allLt_iff, decide_eq_true_eq] using this.2
  have h1 := hnodup (a0Pos (a0El k)) (size_enumA0 ▸ hlt)
  rw [hspec, hnodup k (size_enumA0 ▸ hk)] at h1
  exact (Option.some.inj h1).symm

theorem a0El_a0Pos (a : ↥A0) : a0El (a0Pos a) = a := by
  apply Subtype.ext
  apply code_injective
  rw [code_a0El (a0Pos_lt a), (a0Pos_spec a).2]

theorem a0Pos_injective : Function.Injective a0Pos := fun a b h => by
  rw [← a0El_a0Pos a, h, a0El_a0Pos b]

end Positions

section AutArr

@[expose] noncomputable def autArr (φ : MulAut ↥A0) : Array ℕ :=
  Array.ofFn (n := 64) fun k => a0Pos (φ (a0El k.val))

theorem size_autArr (φ : MulAut ↥A0) : (autArr φ).size = 64 := Array.size_ofFn

theorem autArr_get (φ : MulAut ↥A0) {k : ℕ} (hk : k < 64) :
    (autArr φ)[k]! = a0Pos (φ (a0El k)) :=
  getElem!_ofFn_nat (fun k : Fin 64 => a0Pos (φ (a0El k.val))) hk

theorem autArr_apply (φ : MulAut ↥A0) (a : ↥A0) : (autArr φ)[a0Pos a]! = a0Pos (φ a) := by
  rw [autArr_get φ (a0Pos_lt a), a0El_a0Pos]

theorem autArr_lt (φ : MulAut ↥A0) {k : ℕ} (hk : k < 64) : (autArr φ)[k]! < 64 := by
  rw [autArr_get φ hk]
  exact a0Pos_lt _

theorem isArrCode_autArr : IsArrCode (autArr : MulAut ↥A0 → Array ℕ) where
  mul φ ψ := by
    refine ext64 (size_autArr _) (size_compA _ _) fun i hi => ?_
    rw [compA_get _ _ hi, autArr_get ψ hi, autArr_apply φ, autArr_get _ hi]
    rfl
  one := by
    refine ext64 (size_autArr _) size_idA fun i hi => ?_
    rw [autArr_get _ hi, idA_get hi]
    exact a0Pos_a0El hi
  injective φ ψ h := by
    refine MulEquiv.ext fun a => a0Pos_injective ?_
    rw [← autArr_apply φ, ← autArr_apply ψ, h]

theorem a0Pos_mul (a b : ↥A0) :
    a0Pos (a * b) = ((z6MulTab ())[a0Pos a]!)[a0Pos b]! := by
  have hi := a0Pos_lt a
  have hj := a0Pos_lt b
  rw [z6MulTab, getElem!_ofFn_nat _ hi, getElem!_ofFn_nat _ hj]
  simp only
  rw [(a0Pos_spec a).2, (a0Pos_spec b).2, ← code_mul]
  rfl

end AutArr

section Gen

theorem ysp_mem_N0 {i : ℕ} (hi : i ∈ idxN0) : ysp i ∈ N0 := by
  obtain ⟨h12, h⟩ := idxN0_spec hi
  rw [ysp, dif_pos h12]
  refine yamakiSp_mem_N0 ?_
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

@[expose] noncomputable def glEl (i : ℕ) : MulAut ↥A0 :=
  if h : i ∈ idxN0 then conjA0 ⟨ysp i, ysp_mem_N0 h⟩ else 1

theorem glEl_eq {i : ℕ} (hi : i ∈ idxN0) : glEl i = conjA0 ⟨ysp i, ysp_mem_N0 hi⟩ := by
  rw [glEl, dif_pos hi]

theorem glEl_mem_Lbar {i : ℕ} (hi : i ∈ idxN0) : glEl i ∈ Lbar :=
  ⟨⟨ysp i, ysp_mem_N0 hi⟩, (glEl_eq hi).symm⟩

theorem autArr_glEl {i : ℕ} (hi : i ∈ idxN0) : autArr (glEl i) = z6Gl i := by
  have h12 := (idxN0_spec hi).1
  refine ext64 (size_autArr _) Array.size_ofFn fun k hk => ?_
  rw [autArr_get _ hk, glEl_eq hi, z6Gl, getElem!_ofFn_nat _ hk]
  simp only
  rw [a0Pos, coe_conjA0_apply]
  have hinv : ((⟨ysp i, ysp_mem_N0 hi⟩ : ↥N0) : StatedSp 3 (ZMod 2))⁻¹ = ysp i :=
    inv_eq_of_mul_eq_one_right (ysp_mul_self i)
  rw [hinv, code_mul, code_mul, code_a0El hk, code_ysp h12]

@[expose] noncomputable def lS (j : ℕ) : MulAut ↥A0 :=
  if j = 0 then glEl 0 else glEl 9 * glEl 10

theorem z6GsL_get : ∀ j < (z6GsL ()).size, (z6GsL ())[j]! = autArr (lS j) := by
  intro j hj
  have hj2 : j < 2 := by simpa only [z6GsL, List.size_toArray, List.length_cons,
    List.length_nil] using hj
  interval_cases j
  · rw [lS, if_pos rfl, autArr_glEl (i := 0) (by decide)]
    rfl
  · rw [lS, if_neg (by decide), isArrCode_autArr.mul, autArr_glEl (i := 9) (by decide),
      autArr_glEl (i := 10) (by decide)]
    rfl

end Gen

section LbarMem

theorem z6LbarCheck_spec :
    enumOK (z6EnumL ()) (z6GsL ()) = true ∧ (z6EnumL ()).elems.size = 168 ∧
      (∀ i < 11, ((z6EnumL ()).lookup (z6Gl i)).isSome = true) ∧
      compA (z6GsL ())[0]! (z6GsL ())[0]! = idA () ∧
      compA (z6GsL ())[1]! (compA (z6GsL ())[1]! (z6GsL ())[1]!) = idA () := by
  have h := z6LbarCheck_holds
  simp only [z6LbarCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem lbarEnum_ok : enumOK (z6EnumL ()) (z6GsL ()) = true := z6LbarCheck_spec.1

theorem size_z6GsL : (z6GsL ()).size = 2 := rfl

theorem size_z6EnumL : (z6EnumL ()).elems.size = 168 := z6LbarCheck_spec.2.1

theorem lS_zero_sq : lS 0 * lS 0 = 1 := by
  apply isArrCode_autArr.injective
  rw [isArrCode_autArr.mul, isArrCode_autArr.one, ← z6GsL_get 0 (by decide)]
  exact z6LbarCheck_spec.2.2.2.1

theorem lS_one_cube : lS 1 * (lS 1 * lS 1) = 1 := by
  apply isArrCode_autArr.injective
  rw [isArrCode_autArr.mul, isArrCode_autArr.mul, isArrCode_autArr.one,
    ← z6GsL_get 1 (by decide)]
  exact z6LbarCheck_spec.2.2.2.2

theorem lS_mem_Lbar (j : ℕ) : lS j ∈ Lbar := by
  unfold lS
  split_ifs
  · exact glEl_mem_Lbar (by decide)
  · exact Lbar.mul_mem (glEl_mem_Lbar (by decide)) (glEl_mem_Lbar (by decide))

theorem Lbar_le_closure : Lbar ≤ Subgroup.closure (lS '' Set.Iio (z6GsL ()).size) := by
  set C := Subgroup.closure (lS '' Set.Iio (z6GsL ()).size) with hC
  have hgen : ∀ i, i ∈ idxN0 → glEl i ∈ C := by
    intro i hi
    have hi' : i < 11 := by
      have := idxN0_spec hi
      omega
    rw [hC, mem_closure_iff_isSome isArrCode_autArr z6GsL_get lbarEnum_ok, autArr_glEl hi]
    exact z6LbarCheck_spec.2.2.1 i hi'
  rintro _ ⟨⟨y, hy0⟩, rfl⟩
  have key : ∀ y (hy : y ∈ N0), conjA0 ⟨y, hy⟩ ∈ C := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      have hidx : i.val ∈ idxN0 := mem_idxN0 hi
      have : conjA0 ⟨yamakiSp i, yamakiSp_mem_N0 hi⟩ = glEl i.val := by
        rw [glEl_eq hidx]
        congr 1
        exact Subtype.ext (ysp_eq i).symm
      rw [this]
      exact hgen _ hidx
    | one =>
      have : (⟨1, N0.one_mem⟩ : ↥N0) = 1 := rfl
      rw [this, map_one]
      exact C.one_mem
    | mul a b ha hb iha ihb =>
      have : (⟨a * b, N0.mul_mem ha hb⟩ : ↥N0) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul]
      exact C.mul_mem iha ihb
    | inv a ha iha =>
      have : (⟨a⁻¹, N0.inv_mem ha⟩ : ↥N0) = (⟨a, ha⟩ : ↥N0)⁻¹ := rfl
      rw [this, map_inv]
      exact C.inv_mem iha
  exact key y hy0

theorem closure_le_Lbar : Subgroup.closure (lS '' Set.Iio (z6GsL ()).size) ≤ Lbar := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact lS_mem_Lbar j

theorem Lbar_eq_closure : Lbar = Subgroup.closure (lS '' Set.Iio (z6GsL ()).size) :=
  le_antisymm Lbar_le_closure closure_le_Lbar

theorem mem_Lbar_iff (x : MulAut ↥A0) : x ∈ Lbar ↔ ((z6EnumL ()).lookup (autArr x)).isSome := by
  rw [Lbar_eq_closure]
  exact mem_closure_iff_isSome isArrCode_autArr z6GsL_get lbarEnum_ok x

end LbarMem

section Trees

theorem treeOK_spec {E : Enum} {gs : Array (Array ℕ)} (h : treeOK E gs = true) :
    E.elems[0]? = some (idA ()) ∧ ∀ i < E.elems.size, i = 0 ∨ (E.parent[i]! < i ∧
      E.gen[i]! < gs.size ∧ E.elems[i]! = compA E.elems[E.parent[i]!]! gs[E.gen[i]!]!) := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  refine ⟨h0, fun i hi => ?_⟩
  rcases hall i hi with h | ⟨⟨hp, hg⟩, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨hp, hg, he⟩

theorem treeOK_enumA0 : treeOK (enumA0 ()) (gA0 ()) = true := by
  have := a0EnumCheck_spec.1
  simp only [enumOK, Bool.and_eq_true] at this
  exact this.1.1

theorem treeOK_z6EnumL : treeOK (z6EnumL ()) (z6GsL ()) = true := by
  have := lbarEnum_ok
  simp only [enumOK, Bool.and_eq_true] at this
  exact this.1.1

theorem a0El_zero : a0El 0 = 1 := by
  apply Subtype.ext
  apply code_injective
  rw [code_a0El (by norm_num), OneMemClass.coe_one, code_one]
  exact getElem!_eq_of_getElem? (treeOK_spec treeOK_enumA0).1

theorem a0Pos_one : a0Pos 1 = 0 := by
  rw [← a0El_zero]
  exact a0Pos_a0El (by norm_num)

@[expose] noncomputable def a0GenEl (j : ℕ) : ↥A0 :=
  if h : j < (gA0 ()).size then ⟨a0Gen j, a0Gen_mem_A0 h⟩ else 1

theorem code_a0GenEl {j : ℕ} (hj : j < (gA0 ()).size) :
    code ((a0GenEl j : ↥A0) : StatedSp 3 (ZMod 2)) = (gA0 ())[j]! := by
  rw [a0GenEl, dif_pos hj, gA0_get j hj]

theorem size_gA0' : (gA0 ()).size = 6 := size_gA0

theorem a0El_tree {k : ℕ} (hk : k < 64) (hk0 : k ≠ 0) :
    ((enumA0 ()).parent[k]! < k ∧ (enumA0 ()).gen[k]! < 6) ∧
      a0El k = a0El ((enumA0 ()).parent[k]!) * a0GenEl ((enumA0 ()).gen[k]!) := by
  rcases (treeOK_spec treeOK_enumA0).2 k (size_enumA0 ▸ hk) with h | ⟨hp, hg, he⟩
  · exact absurd h hk0
  · have hg6 : (enumA0 ()).gen[k]! < 6 := size_gA0' ▸ hg
    refine ⟨⟨hp, hg6⟩, ?_⟩
    apply Subtype.ext
    apply code_injective
    rw [code_a0El hk, he, Subgroup.coe_mul, code_mul, code_a0El (hp.trans hk),
      code_a0GenEl hg]

theorem z6EnumL_tree {m : ℕ} (hm : m < 168) (hm0 : m ≠ 0) :
    (z6EnumL ()).parent[m]! < m ∧ (z6EnumL ()).gen[m]! < 2 ∧
      (z6EnumL ()).elems[m]! = compA (z6EnumL ()).elems[(z6EnumL ()).parent[m]!]!
        (z6GsL ())[(z6EnumL ()).gen[m]!]! := by
  rcases (treeOK_spec treeOK_z6EnumL).2 m (size_z6EnumL ▸ hm) with h | ⟨hp, hg, he⟩
  · exact absurd h hm0
  · exact ⟨hp, size_z6GsL ▸ hg, he⟩

end Trees

section Orbit

theorem exists_lEl {m : ℕ} (hm : m < 168) :
    ∃ x ∈ Lbar, autArr x = (z6EnumL ()).elems[m]! := by
  obtain ⟨x, hx, hxe⟩ := exists_mem_closure_of_treeOK isArrCode_autArr z6GsL_get
    treeOK_z6EnumL m (size_z6EnumL ▸ hm)
  exact ⟨x, Lbar_eq_closure ▸ hx, hxe⟩

@[expose] noncomputable def lEl (m : ℕ) : MulAut ↥A0 :=
  if h : m < 168 then (exists_lEl h).choose else 1

theorem autArr_lEl {m : ℕ} (hm : m < 168) : autArr (lEl m) = (z6EnumL ()).elems[m]! := by
  rw [lEl, dif_pos hm]
  exact (exists_lEl hm).choose_spec.2

theorem lEl_zero : lEl 0 = 1 := by
  apply isArrCode_autArr.injective
  rw [autArr_lEl (by norm_num), isArrCode_autArr.one]
  exact getElem!_eq_of_getElem? (treeOK_spec treeOK_z6EnumL).1

theorem lEl_tree {m : ℕ} (hm : m < 168) (hm0 : m ≠ 0) :
    lEl m = lEl ((z6EnumL ()).parent[m]!) * lS ((z6EnumL ()).gen[m]!) := by
  obtain ⟨hp, hg, he⟩ := z6EnumL_tree hm hm0
  apply isArrCode_autArr.injective
  rw [autArr_lEl hm, isArrCode_autArr.mul, autArr_lEl (hp.trans hm),
    ← z6GsL_get _ (size_z6GsL ▸ hg), he]

@[expose] noncomputable def oEl (m : ℕ) : ↥A0 := (lEl m) (a0El z6Beta)

theorem z6Beta_lt : z6Beta < 64 := by decide

theorem a0Pos_oEl {m : ℕ} (hm : m < 168) :
    a0Pos (oEl m) = ((z6EnumL ()).elems[m]!)[z6Beta]! := by
  rw [← autArr_lEl hm, oEl, ← autArr_apply, a0Pos_a0El z6Beta_lt]

theorem a0Pos_list_prod (h : ℕ → ↥A0) (f : ℕ → ℕ) (J : List ℕ)
    (hJ : ∀ m ∈ J, a0Pos (h m) = f m) :
    a0Pos (J.map h).prod = J.foldr (fun m acc => ((z6MulTab ())[f m]!)[acc]!) 0 := by
  induction J with
  | nil => exact a0Pos_one
  | cons m J ih =>
    rw [List.map_cons, List.prod_cons, a0Pos_mul, List.foldr_cons,
      hJ m List.mem_cons_self, ih fun m' hm' => hJ m' (List.mem_cons_of_mem m hm')]

theorem z6Img_get (mul T : Array (Array ℕ)) (v : ℕ) {j : ℕ} (hj : j < 6) :
    (z6Img mul T v)[j]! =
      (z6J.getD j []).foldr (fun m acc => (mul[(T[m]!)[v]!]!)[acc]!) 0 := by
  interval_cases j <;> rfl

theorem a0Pos_a0GenEl {j : ℕ} (hj : j < 6) : a0Pos (a0GenEl j) = (z6BPos ())[j]! := by
  have hj' : j < (gA0 ()).size := size_gA0' ▸ hj
  have hb : (z6BPos ())[j]! = z6Pos (enumA0 ()) (gA0 ())[j]! := by
    have h1 : j < ((gA0 ()).map fun t => z6Pos (enumA0 ()) t).size := by simpa using hj'
    rw [z6BPos]
    rw [getElem!_pos _ j h1, Array.getElem_map, getElem!_pos _ j hj']
  rw [hb, ← code_a0GenEl hj']
  rfl

end Orbit

section Normalizer

theorem z6OrbCheck_spec :
    z6Img (z6MulTab ()) (z6EnumL ()).elems z6Beta = z6BPos () ∧
      (∀ J ∈ z6J, ∀ m ∈ J, m < 168) := by
  have h := z6OrbCheck_holds
  simp only [z6OrbCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  exact ⟨h1, h2⟩

theorem a0GenEl_eq_prod {j : ℕ} (hj : j < 6) :
    a0GenEl j = ((z6J.getD j []).map oEl).prod := by
  apply a0Pos_injective
  obtain ⟨hImg, hJlt⟩ := z6OrbCheck_spec
  have hJ : z6J.getD j [] ∈ z6J := getD_mem (by rw [show z6J.length = 6 from rfl]; exact hj)
  rw [a0Pos_list_prod oEl (fun m => ((z6EnumL ()).elems[m]!)[z6Beta]!) _
    (fun m hm => a0Pos_oEl (hJlt _ hJ m hm)), a0Pos_a0GenEl hj, ← hImg, z6Img_get _ _ _ hj]

theorem img_eq {g : MulAut ↥A0} {T : Array (Array ℕ)} {v : ℕ}
    (hT : ∀ m < 168, T[m]! = autArr (g * lEl m * g⁻¹)) (hv : v = (autArr g)[z6Beta]!) {j : ℕ}
    (hj : j < 6) : (z6Img (z6MulTab ()) T v)[j]! = a0Pos (g (a0GenEl j)) := by
  obtain ⟨-, hJlt⟩ := z6OrbCheck_spec
  have hJ : z6J.getD j [] ∈ z6J := getD_mem (by rw [show z6J.length = 6 from rfl]; exact hj)
  rw [z6Img_get _ _ _ hj, a0GenEl_eq_prod hj, map_list_prod, List.map_map]
  symm
  refine (a0Pos_list_prod (fun m => g (oEl m)) (fun m => (T[m]!)[v]!) _ fun m hm => ?_)
  have hm168 : m < 168 := hJlt _ hJ m hm
  have h1 : g (oEl m) = (g * lEl m * g⁻¹) (g (a0El z6Beta)) := by
    rw [oEl]
    simp only [MulAut.mul_apply]
    rw [MulAut.inv_apply_self]
  rw [h1, hT _ hm168, ← autArr_apply, ← autArr_get g z6Beta_lt, ← hv]

@[expose] def candT (a b : ℕ) : Array (Array ℕ) :=
  buildF (z6EnumL ()) #[(z6EnumL ()).elems[a]!, (z6EnumL ()).elems[b]!]

@[expose] def candImg (a b v : ℕ) : Array ℕ := z6Img (z6MulTab ()) (candT a b) v

@[expose] def candF (a b v : ℕ) : Array ℕ :=
  z6BuildF (z6MulTab ()) (enumA0 ()) (candImg a b v)

theorem z6TEqn_spec {EL : Enum} {tt T : Array (Array ℕ)} (h : z6TEqn EL tt T = true) :
    T.size = EL.elems.size ∧ T[0]? = some (idA ()) ∧
      ∀ m < EL.elems.size, m = 0 ∨ T[m]! = compA T[EL.parent[m]!]! tt[EL.gen[m]!]! := by
  simp only [z6TEqn, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem z6FEqn_spec {mul : Array (Array ℕ)} {E : Enum} {img F : Array ℕ}
    (h : z6FEqn mul E img F = true) :
    F.size = 64 ∧ F[0]? = some 0 ∧ ∀ k < 64, k = 0 ∨
      F[k]! = (mul[F[E.parent[k]!]!]!)[img[E.gen[k]!]!]! := by
  simp only [z6FEqn, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem normCheck_spec :
    ∀ a < 168, ∀ b < 168,
      compA (z6EnumL ()).elems[a]! (z6EnumL ()).elems[a]! = idA () →
      compA (z6EnumL ()).elems[b]! (compA (z6EnumL ()).elems[b]! (z6EnumL ()).elems[b]!) =
        idA () →
      z6TEqn (z6EnumL ()) #[(z6EnumL ()).elems[a]!, (z6EnumL ()).elems[b]!] (candT a b) = true ∧
      ∀ v < 64,
        z6FEqn (z6MulTab ()) (enumA0 ()) (candImg a b v) (candF a b v) = true ∧
        (z6Valid (z6MulTab ()) (z6GsL ()) #[(z6EnumL ()).elems[a]!, (z6EnumL ()).elems[b]!]
            (candF a b v) = true →
          ((z6EnumL ()).lookup (candF a b v)).isSome = true) := by
  have h := z6NormCheck_holds
  simp only [z6NormCheck, allLt_iff, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  intro a ha b hb hinv hcube
  have h1 := h a ha b hb
  simp only [decide_eq_false_iff_not] at h1
  rcases h1 with ⟨h1 | h1⟩ | ⟨h1, h2⟩
  · exact absurd hinv h1
  · exact absurd hcube h1
  · simp only [candF, candImg, candT]
    refine ⟨h1, fun v hv => ?_⟩
    obtain ⟨h3, h4⟩ := h2 v hv
    refine ⟨h3, fun hvalid => ?_⟩
    rcases h4 with h4 | h4
    · rw [h4] at hvalid
      cases hvalid
    · exact h4

theorem tTable_eq {g : MulAut ↥A0} {tt T : Array (Array ℕ)}
    (htt : ∀ j < 2, tt[j]! = autArr (g * lS j * g⁻¹)) (hT0 : T[0]? = some (idA ()))
    (hT : ∀ m < 168, m = 0 ∨
      T[m]! = compA T[(z6EnumL ()).parent[m]!]! tt[(z6EnumL ()).gen[m]!]!) :
    ∀ m < 168, T[m]! = autArr (g * lEl m * g⁻¹) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    by_cases hm0 : m = 0
    · subst hm0
      rw [getElem!_eq_of_getElem? hT0, lEl_zero, mul_one, mul_inv_cancel,
        isArrCode_autArr.one]
    · rcases hT m hm with h | h
      · exact absurd h hm0
      obtain ⟨hp, hg, -⟩ := z6EnumL_tree hm hm0
      have hmul : g * (lEl ((z6EnumL ()).parent[m]!) * lS ((z6EnumL ()).gen[m]!)) * g⁻¹ =
          (g * lEl ((z6EnumL ()).parent[m]!) * g⁻¹) *
            (g * lS ((z6EnumL ()).gen[m]!) * g⁻¹) := by group
      rw [h, ih _ hp (hp.trans hm), htt _ hg, lEl_tree hm hm0, hmul]
      exact (isArrCode_autArr.mul _ _).symm

theorem fTable_eq {g : MulAut ↥A0} {img F : Array ℕ}
    (himg : ∀ j < 6, img[j]! = a0Pos (g (a0GenEl j))) (hF0 : F[0]? = some 0)
    (hF : ∀ k < 64, k = 0 ∨
      F[k]! = ((z6MulTab ())[F[(enumA0 ()).parent[k]!]!]!)[img[(enumA0 ()).gen[k]!]!]!) :
    ∀ k < 64, F[k]! = (autArr g)[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0
      rw [getElem!_eq_of_getElem? hF0, autArr_get g hk, a0El_zero, map_one, a0Pos_one]
    · rcases hF k hk with h | h
      · exact absurd h hk0
      obtain ⟨⟨hp, hg6⟩, htree⟩ := a0El_tree hk hk0
      rw [h, ih _ hp (hp.trans hk), himg _ hg6, autArr_get g hk, htree, map_mul, a0Pos_mul,
        autArr_get g (hp.trans hk)]

theorem valid_autArr (g : MulAut ↥A0) {tt : Array (Array ℕ)}
    (htt : ∀ j < 2, tt[j]! = autArr (g * lS j * g⁻¹)) :
    z6Valid (z6MulTab ()) (z6GsL ()) tt (autArr g) = true := by
  have hnorm : z6IsNorm (z6GsL ()) tt (autArr g) = true := by
    simp only [z6IsNorm, allLt_iff, decide_eq_true_eq]
    intro j hj
    rw [z6GsL_get j hj, htt j (size_z6GsL ▸ hj), ← isArrCode_autArr.mul,
      ← isArrCode_autArr.mul]
    congr 1
    group
  have hperm : z6IsPerm (autArr g) = true := by
    simp only [z6IsPerm, Bool.and_eq_true, decide_eq_true_eq, allLt_iff]
    refine ⟨size_autArr g, fun i hi => ⟨autArr_lt g hi, fun j hj => ?_⟩⟩
    intro h
    have hji : j < 64 := hj.trans hi
    rw [autArr_get g hji, autArr_get g hi] at h
    have h1 := g.injective (a0Pos_injective h)
    have h2 := congrArg a0Pos h1
    rw [a0Pos_a0El hji, a0Pos_a0El hi] at h2
    omega
  have hmul : z6IsMul (z6MulTab ()) (autArr g) = true := by
    simp only [z6IsMul, allLt_iff, decide_eq_true_eq]
    intro i hi j hj
    have h1 : ((z6MulTab ())[i]!)[j]! = a0Pos (a0El i * a0El j) := by
      rw [a0Pos_mul, a0Pos_a0El hi, a0Pos_a0El hj]
    have h2 : ((z6MulTab ())[(autArr g)[i]!]!)[(autArr g)[j]!]! =
        a0Pos (g (a0El i) * g (a0El j)) := by
      rw [a0Pos_mul, autArr_get g hi, autArr_get g hj]
    rw [h1, h2, autArr_apply, map_mul]
  simp only [z6Valid, Bool.and_eq_true]
  exact ⟨⟨hnorm, hperm⟩, hmul⟩

theorem mem_Lbar_of_mem_normalizer {g : MulAut ↥A0}
    (hg : g ∈ Subgroup.normalizer (Lbar : Set (MulAut ↥A0))) : g ∈ Lbar := by
  have hmem : ∀ j < 2, ∃ τ < 168, (z6EnumL ()).elems[τ]! = autArr (g * lS j * g⁻¹) := by
    intro j hj
    have h1 : lS j ∈ Lbar := lS_mem_Lbar j
    have h2 : g * lS j * g⁻¹ ∈ Lbar := (Subgroup.mem_normalizer_iff.mp hg (lS j)).mp h1
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp ((mem_Lbar_iff _).mp h2)
    obtain ⟨hlt, hel⟩ := Enum.lookup_spec hτ
    exact ⟨τ, size_z6EnumL ▸ hlt, hel⟩
  obtain ⟨a, ha, hea⟩ := hmem 0 (by norm_num)
  obtain ⟨b, hb, heb⟩ := hmem 1 (by norm_num)
  have htt : ∀ j < 2, (#[(z6EnumL ()).elems[a]!, (z6EnumL ()).elems[b]!] : Array (Array ℕ))[j]! =
      autArr (g * lS j * g⁻¹) := by
    intro j hj
    interval_cases j
    · exact hea
    · exact heb
  have hinv : compA (z6EnumL ()).elems[a]! (z6EnumL ()).elems[a]! = idA () := by
    rw [hea, ← isArrCode_autArr.mul, show g * lS 0 * g⁻¹ * (g * lS 0 * g⁻¹) =
      g * (lS 0 * lS 0) * g⁻¹ by group, lS_zero_sq, mul_one, mul_inv_cancel,
      isArrCode_autArr.one]
  have hcube : compA (z6EnumL ()).elems[b]!
      (compA (z6EnumL ()).elems[b]! (z6EnumL ()).elems[b]!) = idA () := by
    rw [heb, ← isArrCode_autArr.mul, ← isArrCode_autArr.mul, show g * lS 1 * g⁻¹ *
      (g * lS 1 * g⁻¹ * (g * lS 1 * g⁻¹)) = g * (lS 1 * (lS 1 * lS 1)) * g⁻¹ by group,
      lS_one_cube, mul_one, mul_inv_cancel, isArrCode_autArr.one]
  obtain ⟨v, hvd⟩ : ∃ v, v = (autArr g)[z6Beta]! := ⟨_, rfl⟩
  have hv : v < 64 := hvd ▸ autArr_lt g z6Beta_lt
  obtain ⟨hTeq, hrest⟩ := normCheck_spec a ha b hb hinv hcube
  obtain ⟨hFeq, hcos⟩ := hrest v hv
  obtain ⟨-, hT0, hT⟩ := z6TEqn_spec hTeq
  have hT' := tTable_eq htt hT0 (size_z6EnumL ▸ hT)
  obtain ⟨hFsize, hF0, hF⟩ := z6FEqn_spec hFeq
  have hFg := fTable_eq (fun j hj => img_eq hT' hvd hj) hF0 hF
  have hFeq' : candF a b v = autArr g := ext64 hFsize (size_autArr g) hFg
  have hvalid := valid_autArr g htt
  rw [← hFeq'] at hvalid
  have hc := hcos hvalid
  rw [hFeq'] at hc
  exact (mem_Lbar_iff g).mpr hc

end Normalizer

end Z6NA

section Main

open Z6NA

theorem normalizer_Lbar_le :
    ∀ g : MulAut ↥A0, g ∈ Subgroup.normalizer (Lbar : Set (MulAut ↥A0)) → g ∈ Lbar :=
  fun _ hg => mem_Lbar_of_mem_normalizer hg

end Main

end CFSG.ClassicalInvolution.Sp62Rec
