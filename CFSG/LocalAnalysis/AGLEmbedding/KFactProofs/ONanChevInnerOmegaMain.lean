module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmega
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Universal.Spin QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4

theorem liftableNormalizerGen_of_inverters_F {L : Type*} [Group L] (h w : Fin 4 → L)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) (F : Subgroup L)
    (hFE : F ≤ Subgroup.closure (Set.range h)) (hF : 3 ^ 2 ≤ Nat.card F)
    (hgen : ⊤ ≤ Subgroup.normalizer (Subgroup.closure (Set.range h) : Set L) ⊔
      Subgroup.normalizer (F : Set L)) : LiftableNormalizerGen L := by
  obtain ⟨hEab, hEcard, hElift⟩ := liftsComm_of_inverters h w hcomm hord hinv hfix
  refine ⟨Subgroup.closure (Set.range h), {Subgroup.closure (Set.range h), F}, hEab.2, ?_,
    ⟨_, Set.mem_insert _ _⟩, ?_, hElift, ?_⟩
  · rw [hEcard]
    simp
  · rintro F' (rfl | rfl)
    · refine ⟨le_rfl, ?_⟩
      rw [hEcard]
      simp
    · exact ⟨hFE, hF⟩
  · refine hgen.trans (sup_le ?_ ?_)
    · exact le_iSup₂ (f := fun F' (_ : F' ∈ ({Subgroup.closure (Set.range h), F} :
        Set (Subgroup L))) => Subgroup.normalizer (F' : Set L)) (Subgroup.closure (Set.range h))
        (Set.mem_insert _ _)
    · exact le_iSup₂ (f := fun F' (_ : F' ∈ ({Subgroup.closure (Set.range h), F} :
        Set (Subgroup L))) => Subgroup.normalizer (F' : Set L)) F
        (Set.mem_insert_of_mem _ rfl)


section Torus

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem plusZ_mem_Om8 (i : Fin 4) : plusZ i ∈ Om8 := by
  have hA : plusA i ∈ Subgroup.closure {A : GL ι8 (ZMod 2) |
      ∀ v, StatedQuadPlus 4 (ZMod 2) ((A : Matrix ι8 ι8 (ZMod 2)) *ᵥ v) =
        StatedQuadPlus 4 (ZMod 2) v} := Subgroup.subset_closure fun v => isometry_plusA i v
  have hZ : plusZ i ∈ Subgroup.closure {A : GL ι8 (ZMod 2) |
      ∀ v, StatedQuadPlus 4 (ZMod 2) ((A : Matrix ι8 ι8 (ZMod 2)) *ᵥ v) =
        StatedQuadPlus 4 (ZMod 2) v} := Subgroup.subset_closure fun v => isometry_plusZ i v
  have := Subgroup.commutator_mem_commutator hA hZ
  rwa [plus_relations.2.2.2.2.2 i] at this

@[expose] def uA : Fin 4 → ℕ := ![1, 2, 4, 8]

@[expose] def wA : Fin 4 → ℕ := ![2, 16, 8, 64]

theorem plusA_act' : ∀ i : Fin 4, ∀ c < 256,
    applyB (colsB (plusA i)) c = eAct (uA i) (wA i) c := by
  decide +kernel

theorem plusA_act (i : Fin 4) {c : ℕ} (hc : c < 256) :
    actG (plusA i) c = eAct (uA i) (wA i) c := by
  rw [actG_eq_applyB _ hc]
  exact plusA_act' i c hc

theorem plusA_eq_eichGL (i : Fin 4) : plusA i = eichGL (bv (uA i)) (bv (wA i)) := by
  apply gl_ext_act
  intro c hc
  have hu : uA i < 256 := by fin_cases i <;> decide
  have hw : wA i < 256 := by fin_cases i <;> decide
  rw [actG_eichGL _ _ hc, bc_bv hu, bc_bv hw, plusA_act i hc]

theorem plusA_mem_Om8 (i : Fin 4) : plusA i ∈ Om8 := by
  rw [plusA_eq_eichGL]
  exact eichGL_mem _ _

@[expose] noncomputable def hZ (i : Fin 4) : Om8 := ⟨plusZ i, plusZ_mem_Om8 i⟩

@[expose] noncomputable def hA (i : Fin 4) : Om8 := ⟨plusA i, plusA_mem_Om8 i⟩

theorem hZ_comm (i j : Fin 4) : Commute (hZ i) (hZ j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · exact Subtype.ext (plus_relations.2.2.2.2.1 i j hij)

theorem hZ_ord (i : Fin 4) : orderOf (hZ i) = 3 := by
  obtain ⟨h3, h1, -, -, -, -⟩ := plus_relations
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext (h3 i)
  · intro h
    have h' : plusZ i = 1 := congrArg Subtype.val h
    apply h1 i
    rw [h', one_mul, mul_one]

theorem hA_inv (i : Fin 4) : hA i * hZ i * (hA i)⁻¹ = (hZ i)⁻¹ := by
  obtain ⟨h3, -, -, -, -, hZA'⟩ := plus_relations
  have hsq : plusA i * plusZ i * (plusA i)⁻¹ = plusZ i * plusZ i := by
    have hc := hZA' i
    rw [commutatorElement_def] at hc
    exact mul_inv_eq_iff_eq_mul.1 hc
  have hinv : plusA i * plusZ i * (plusA i)⁻¹ = (plusZ i)⁻¹ :=
    hsq.trans (eq_inv_of_mul_eq_one_left ((pow_three' _).symm.trans (h3 i)))
  exact Subtype.ext hinv

theorem hA_fix (i j : Fin 4) (hij : i ≠ j) : hA i * hZ j * (hA i)⁻¹ = hZ j := by
  have hfix : plusA i * plusZ j * (plusA i)⁻¹ = plusZ j :=
    mul_inv_eq_iff_eq_mul.2 (plus_relations.2.2.2.1 i j hij).symm
  exact Subtype.ext hfix


@[expose] noncomputable def zelH (i : ℕ) : Om8 := hZ ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def zprodH (l : List ℕ) : Om8 := (l.map zelH).prod

@[expose] def zactL (l : List ℕ) (c : ℕ) : ℕ :=
  l.foldr (fun i c => applyB (colsB (plusZ ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩)) c) c

theorem zactL_lt (l : List ℕ) {c : ℕ} (hc : c < 256) : zactL l c < 256 := by
  induction l with
  | nil => exact hc
  | cons i l ih =>
    show applyB (colsB (plusZ ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩)) (zactL l c) < 256
    rw [← actG_eq_applyB _ ih]
    exact actG_lt _ _

theorem actG_zprodH (l : List ℕ) {c : ℕ} (hc : c < 256) :
    actG ((zprodH l : Om8) : GL ι8 (ZMod 2)) c = zactL l c := by
  induction l with
  | nil =>
    show actG 1 c = c
    exact actG_one hc
  | cons i l ih =>
    show actG (((zelH i : Om8) : GL ι8 (ZMod 2)) * ((zprodH l : Om8) : GL ι8 (ZMod 2))) c = _
    rw [actG_mul, ih]
    exact actG_eq_applyB _ (zactL_lt l hc)

@[expose] noncomputable def Etor : Subgroup Om8 := Subgroup.closure (Set.range hZ)

@[expose] noncomputable def fgA : Om8 := hZ 0 * hZ 3

@[expose] noncomputable def fgB : Om8 := hZ 0 ^ 2 * hZ 2

@[expose] noncomputable def Fsub : Subgroup Om8 := Subgroup.closure {fgA, fgB}

theorem hZ_mem_Etor (i : Fin 4) : hZ i ∈ Etor := Subgroup.subset_closure (Set.mem_range_self i)

theorem zprodH_mem_Etor (l : List ℕ) : zprodH l ∈ Etor := by
  unfold zprodH
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact hZ_mem_Etor _

theorem Fsub_le_Etor : Fsub ≤ Etor := by
  unfold Fsub
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Etor.mul_mem (hZ_mem_Etor 0) (hZ_mem_Etor 3)
  · exact Etor.mul_mem (pow_mem (hZ_mem_Etor 0) 2) (hZ_mem_Etor 2)


@[expose] noncomputable def fe (a b : ℕ) : Om8 := fgA ^ a * fgB ^ b

theorem fe_mem (a b : ℕ) : fe a b ∈ Fsub :=
  Fsub.mul_mem (pow_mem (Subgroup.subset_closure (by simp)) a)
    (pow_mem (Subgroup.subset_closure (by simp)) b)

@[expose] def fAct (a b c : ℕ) : ℕ := (zactL [0, 3])^[a] ((zactL [0, 0, 2])^[b] c)

theorem zactL_iter_lt (l : List ℕ) (a : ℕ) {c : ℕ} (hc : c < 256) :
    (zactL l)^[a] c < 256 := by
  induction a with
  | zero => exact hc
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    exact zactL_lt l ih

theorem actG_fgA {c : ℕ} (hc : c < 256) :
    actG ((fgA : Om8) : GL ι8 (ZMod 2)) c = zactL [0, 3] c := by
  have h3 := actG_eq_applyB (plusZ 3) hc
  have h0 := actG_eq_applyB (plusZ 0) (actG_lt (plusZ 3) c)
  show actG (plusZ 0 * plusZ 3) c = _
  rw [actG_mul, h0, h3]
  rfl

theorem actG_fgB {c : ℕ} (hc : c < 256) :
    actG ((fgB : Om8) : GL ι8 (ZMod 2)) c = zactL [0, 0, 2] c := by
  have h2 := actG_eq_applyB (plusZ 2) hc
  have h0 := actG_eq_applyB (plusZ 0) (actG_lt (plusZ 2) c)
  have h0' := actG_eq_applyB (plusZ 0) (actG_lt (plusZ 0) (actG (plusZ 2) c))
  show actG ((hZ 0 ^ 2 * hZ 2 : Om8) : GL ι8 (ZMod 2)) c = _
  rw [pow_two, Subgroup.coe_mul, Subgroup.coe_mul, actG_mul, actG_mul]
  show actG (plusZ 0) (actG (plusZ 0) (actG (plusZ 2) c)) = _
  rw [h0', h0, h2]
  rfl

theorem actG_fgA_pow (a : ℕ) {c : ℕ} (hc : c < 256) :
    actG ((fgA ^ a : Om8) : GL ι8 (ZMod 2)) c = (zactL [0, 3])^[a] c := by
  induction a generalizing c with
  | zero =>
    show actG 1 c = c
    exact actG_one hc
  | succ a ih =>
    rw [pow_succ', Subgroup.coe_mul, actG_mul, ih hc, Function.iterate_succ_apply']
    exact actG_fgA (zactL_iter_lt _ a hc)

theorem actG_fgB_pow (a : ℕ) {c : ℕ} (hc : c < 256) :
    actG ((fgB ^ a : Om8) : GL ι8 (ZMod 2)) c = (zactL [0, 0, 2])^[a] c := by
  induction a generalizing c with
  | zero =>
    show actG 1 c = c
    exact actG_one hc
  | succ a ih =>
    rw [pow_succ', Subgroup.coe_mul, actG_mul, ih hc, Function.iterate_succ_apply']
    exact actG_fgB (zactL_iter_lt _ a hc)

theorem fe_act (a b : ℕ) {c : ℕ} (hc : c < 256) :
    actG ((fe a b : Om8) : GL ι8 (ZMod 2)) c = fAct a b c := by
  unfold fe fAct
  rw [Subgroup.coe_mul, actG_mul, actG_fgB_pow b hc, actG_fgA_pow a (zactL_iter_lt _ b hc)]

set_option synthInstance.maxSize 20000 in
theorem fAct_inj : ∀ a < 3, ∀ b < 3, ∀ a' < 3, ∀ b' < 3,
    (a = a' ∧ b = b') ∨ ∃ j < 8, fAct a b (2 ^ j) ≠ fAct a' b' (2 ^ j) := by
  decide +kernel

theorem Fsub_card : 3 ^ 2 ≤ Nat.card Fsub := by
  let φ : Fin 3 × Fin 3 → Fsub := fun p => ⟨fe p.1 p.2, fe_mem _ _⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have h1 : fe a b = fe a' b' := congrArg Subtype.val h
    rcases fAct_inj a a.2 b b.2 a' a'.2 b' b'.2 with ⟨ha, hb⟩ | ⟨j, hj, hne⟩
    · exact Prod.ext (Fin.ext ha) (Fin.ext hb)
    · exfalso
      apply hne
      have hc256 : 2 ^ j < 256 := by
        calc 2 ^ j < 2 ^ 8 := Nat.pow_lt_pow_right (by norm_num) hj
          _ = 256 := by norm_num
      rw [← fe_act a b hc256, ← fe_act a' b' hc256, h1]
  have := Nat.card_le_card_of_injective φ hφ
  simpa using this


structure OmegaData where
  words : List (List (ℕ × ℕ))
  nE : ℕ
  zconj : List (List (List ℕ))
  steps : List (ℕ × ℕ)
  zl : List ℕ

namespace OmegaData

variable (d : OmegaData)

@[expose] def startOf : ℕ :=
  ((d.words.getD 0 []).headD (0, 0)).1 + 256 * ((d.words.getD 0 []).headD (0, 0)).2

@[expose] def bfsOk : Bool :=
  match bfsAux (fun k pc => canon (actPair (wact (d.words.getD k [])) pc)) d.steps
    (1 <<< d.startOf) with
  | none => false
  | some m => eAllCheck m d.zl

@[expose] def Ok : Prop :=
  (∀ ps ∈ d.words, ∀ p ∈ ps, p.1 < 256 ∧ p.2 < 256) ∧ (d.words.getD 0 []).length = 1 ∧
  0 < d.nE ∧
  (∀ k < d.nE, ∀ c < 256, wact (d.words.getD k []) (wact (d.words.getD k []) c) = c) ∧
  (∀ k < d.nE, ∀ i < 4, ∀ c < 256, wact (d.words.getD k []) (zactL [i] c) =
    zactL ((d.zconj.getD k []).getD i []) (wact (d.words.getD k []) c)) ∧
  (∀ k, d.nE ≤ k → k < d.words.length → ∀ c < 256,
    wact (d.words.getD k []) (zactL [0, 3] c) = zactL [0, 3] (wact (d.words.getD k []) c) ∧
    wact (d.words.getD k []) (zactL [0, 0, 2] c) =
      zactL [0, 0, 2] (wact (d.words.getD k []) c)) ∧
  d.bfsOk = true

@[expose] def okCheck : Bool :=
  d.words.all (fun ps => ps.all fun p => decide (p.1 < 256) && decide (p.2 < 256)) &&
  ((d.words.getD 0 []).length == 1) && decide (0 < d.nE) &&
  (List.range d.nE).all (fun k => (List.range 256).all fun c =>
    wact (d.words.getD k []) (wact (d.words.getD k []) c) == c) &&
  (List.range d.nE).all (fun k => (List.range 4).all fun i => (List.range 256).all fun c =>
    wact (d.words.getD k []) (zactL [i] c) ==
      zactL ((d.zconj.getD k []).getD i []) (wact (d.words.getD k []) c)) &&
  (List.range d.words.length).all (fun k => decide (k < d.nE) || (List.range 256).all fun c =>
    (wact (d.words.getD k []) (zactL [0, 3] c) == zactL [0, 3] (wact (d.words.getD k []) c)) &&
    (wact (d.words.getD k []) (zactL [0, 0, 2] c) ==
      zactL [0, 0, 2] (wact (d.words.getD k []) c))) &&
  d.bfsOk

theorem Ok_of_check (h : d.okCheck = true) : d.Ok := by
  unfold okCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨fun ps hps p hp => ?_, h2, h3, fun k hk c hc => h4 k hk c hc,
    fun k hk i hi c hc => h5 k hk i hi c hc, fun k hk hk' c hc => ?_, h7⟩
  · have := h1 ps hps p hp
    simpa using this
  · rcases h6 k hk' with h | h
    · exact absurd h (not_lt.2 hk)
    · exact h c hc

section Main

variable {d : OmegaData}

theorem welt_lt (h : d.Ok) (k : ℕ) : ∀ p ∈ d.words.getD k [], p.1 < 256 ∧ p.2 < 256 := by
  by_cases hkw : k < d.words.length
  · exact h.1 _ (by
      rw [List.getD_eq_getElem _ _ hkw]
      exact List.getElem_mem hkw)
  · rw [List.getD_eq_default _ _ (not_lt.1 hkw)]
    simp

theorem welt_mul_self (h : d.Ok) {k : ℕ} (hk : k < d.nE) :
    welt (d.words.getD k []) * welt (d.words.getD k []) = 1 := by
  have hlt := welt_lt h k
  apply Subtype.ext
  apply gl_ext_act
  intro c hc
  rw [Subgroup.coe_mul, actG_mul, actG_welt _ hlt hc, actG_welt _ hlt (wact_lt _ hc),
    h.2.2.2.1 k hk c hc]
  exact (actG_one hc).symm

theorem zactL_single (i : Fin 4) {c : ℕ} (hc : c < 256) :
    zactL [(i : ℕ)] c = actG (plusZ i) c := by
  have : (⟨(i : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) = i :=
    Fin.ext (Nat.mod_eq_of_lt i.2)
  simp only [zactL, List.foldr_cons, List.foldr_nil, this]
  exact (actG_eq_applyB _ hc).symm

theorem actG_coe_mul (g g' : Om8) (c : ℕ) :
    actG ((g * g' : Om8) : GL ι8 (ZMod 2)) c =
      actG (g : GL ι8 (ZMod 2)) (actG (g' : GL ι8 (ZMod 2)) c) :=
  actG_mul _ _ _

theorem welt_mem_normalizer_Etor (h : d.Ok) {k : ℕ} (hk : k < d.nE) :
    welt (d.words.getD k []) ∈ Subgroup.normalizer (Etor : Set Om8) := by
  have hlt := welt_lt h k
  have hinv : (welt (d.words.getD k []))⁻¹ = welt (d.words.getD k []) :=
    inv_eq_of_mul_eq_one_right (welt_mul_self h hk)
  have hconj : ∀ i : Fin 4, welt (d.words.getD k []) * hZ i * (welt (d.words.getD k []))⁻¹ ∈
      Etor := by
    intro i
    set l := (d.zconj.getD k []).getD i [] with hl
    have key : welt (d.words.getD k []) * hZ i = zprodH l * welt (d.words.getD k []) := by
      apply Subtype.ext
      apply gl_ext_act
      intro c hc
      have hZi : actG ((hZ i : Om8) : GL ι8 (ZMod 2)) c = actG (plusZ i) c := rfl
      rw [actG_coe_mul, actG_coe_mul, hZi, actG_welt _ hlt hc,
        actG_welt _ hlt (actG_lt _ _), actG_zprodH _ (wact_lt _ hc)]
      have := h.2.2.2.2.1 k hk i i.2 c hc
      rw [zactL_single i hc] at this
      exact this
    rw [key, mul_assoc, mul_inv_cancel, mul_one]
    exact zprodH_mem_Etor l
  refine mem_normalizer_closure_of_conj_mem_inv (s := Set.range hZ) (fun t ht => ?_)
    (fun t ht => ?_)
  · obtain ⟨i, rfl⟩ := ht
    exact hconj i
  · obtain ⟨i, rfl⟩ := ht
    have := hconj i
    rw [hinv] at this ⊢
    exact this

theorem welt_mem_normalizer_Fsub (h : d.Ok) {k : ℕ} (hk : d.nE ≤ k) (hk' : k < d.words.length) :
    welt (d.words.getD k []) ∈ Subgroup.normalizer (Fsub : Set Om8) := by
  have hlt := welt_lt h k
  refine mem_normalizer_closure_of_commute (s := {fgA, fgB}) ?_
  rintro y (rfl | rfl)
  · apply Subtype.ext
    apply gl_ext_act
    intro c hc
    rw [actG_coe_mul, actG_coe_mul, actG_welt _ hlt (actG_lt _ _), actG_fgA hc,
      actG_welt _ hlt hc, actG_fgA (wact_lt _ hc)]
    exact (h.2.2.2.2.2.1 k hk hk' c hc).1
  · apply Subtype.ext
    apply gl_ext_act
    intro c hc
    rw [actG_coe_mul, actG_coe_mul, actG_welt _ hlt (actG_lt _ _), actG_fgB hc,
      actG_welt _ hlt hc, actG_fgB (wact_lt _ hc)]
    exact (h.2.2.2.2.2.1 k hk hk' c hc).2

theorem liftableNormalizerGen_Om8 (h : d.Ok) : LiftableNormalizerGen Om8 := by
  refine liftableNormalizerGen_of_inverters_F hZ hA hZ_comm hZ_ord hA_inv hA_fix Fsub
    Fsub_le_Etor Fsub_card ?_
  set M : Subgroup Om8 := Subgroup.closure {g | ∃ ps ∈ d.words, g = welt ps} with hM
  have hMmem : ∀ ps ∈ d.words, welt ps ∈ M := fun ps hps =>
    Subgroup.subset_closure ⟨ps, hps, rfl⟩
  obtain ⟨mask, hmask, hcomp⟩ : ∃ mask, bfsAux (fun k pc => canon (actPair
      (wact (d.words.getD k [])) pc)) d.steps (1 <<< d.startOf) = some mask ∧
      EAllOk mask d.zl := by
    have hbfs := h.2.2.2.2.2.2
    unfold OmegaData.bfsOk at hbfs
    split at hbfs
    · exact absurd hbfs (by simp)
    · rename_i m hm
      exact ⟨m, hm, eAllOk_of_check hbfs⟩
  obtain ⟨p, hp⟩ : ∃ p, d.words.getD 0 [] = [p] := List.length_eq_one_iff.1 h.2.1
  have hw0 : 0 < d.words.length := by
    by_contra hcon
    rw [List.getD_eq_default _ _ (not_lt.1 hcon)] at hp
    exact absurd hp (by simp)
  have hstart : eg d.startOf ∈ M := by
    have hmem : [p] ∈ d.words := by
      rw [← hp, List.getD_eq_getElem _ _ hw0]
      exact List.getElem_mem hw0
    have := hMmem _ hmem
    have e : eg d.startOf = welt [p] := by
      unfold OmegaData.startOf
      rw [hp]
      simp [welt]
    rw [e]
    exact this
  have hall := all_eichler_mem M (er_of_bfs M d.words hMmem (fun ps hps => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hps
    rw [← List.getD_eq_getElem _ _ hk]
    exact welt_lt h k) hstart d.steps hmask) hcomp
  have hMtop : M = ⊤ := om8_top_of_eichler M hall
  have hMle : M ≤ Subgroup.normalizer (Etor : Set Om8) ⊔ Subgroup.normalizer (Fsub : Set Om8) := by
    rw [hM, Subgroup.closure_le]
    rintro _ ⟨ps, hps, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hps
    rw [← List.getD_eq_getElem _ _ hk]
    by_cases hkE : k < d.nE
    · exact Subgroup.mem_sup_left (welt_mem_normalizer_Etor h hkE)
    · exact Subgroup.mem_sup_right (welt_mem_normalizer_Fsub h (not_lt.1 hkE) hk)
  rw [← hMtop]
  exact hMle

end Main

end OmegaData

end Torus

end CFSG.AGLEmbedding
