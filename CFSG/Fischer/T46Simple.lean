module

public import CFSG.Fischer.T46
public import CFSG.Fischer.T46SimpleCert

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Sporadic.Fi22.Native

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

structure T46SimpleFacts : Prop where
  words_size : t46Words.size = 53
  words_get : ∀ k : ℕ, k < 46 → t46Words[k]! = [(k : ℤ) + 1]
  tv_zero : t46FixAll (tvTable 0) = true
  x_sq : t46FixAll (powT 693 2 t46XT) = true
  x_ne : t46FixAll t46XT = false
  y_cube : t46FixAll (powT 693 3 t46YT) = true
  y_ne : t46FixAll t46YT = false
  xy_pow : t46FixAll (powT 693 11 (compT 693 t46XT t46YT)) = true
  xy_ne : t46FixAll (compT 693 t46XT t46YT) = false
  tv_words : ∀ k < 46, t46TblEq (wordT 693 t46XYGen t46TvWords[k]!) (tvTable tvGens[k]!) = true
  sub_tree : treeOK 693 t46SubRoot t46SubTree t46Letters t46Lv1 = true
  sub_size : t46SubTree.pts.size = 180
  cover : ∀ p < 693, p = 0 ∨ t46InTree t46Trees[1]! p = true ∨ t46InTree t46SubTree p = true

theorem t46SimpleFacts : T46SimpleFacts := by
  have h := t46_simple_certificate
  unfold t46SimpleCertificate at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, fun k hk => ?_, h3, h4, h5, h6, h7, h8, h9, fun k hk => ?_, h11, h12, fun p hp => ?_⟩
  · exact beq_iff_eq.1 ((allIn_eq_true.1 h2) k (Nat.zero_le _) hk)
  · exact (allIn_eq_true.1 h10) k (Nat.zero_le _) hk
  · have := (allIn_eq_true.1 h13) p (Nat.zero_le _) hp
    simpa only [Bool.or_eq_true, beq_iff_eq, or_assoc] using this

theorem t46_perm_eq_of_tblEq {P Q : Table} {g h : Equiv.Perm (Fin 693)} (hg : Rep 693 P g)
    (hh : Rep 693 Q h) (e : t46TblEq P Q = true) : g = h := by
  ext i
  have := (allIn_eq_true.1 e) i.val (Nat.zero_le _) i.isLt
  rw [beq_iff_eq, hg _ i.isLt, hh _ i.isLt, idx_of_lt _ i.isLt, idx_of_lt _ i.isLt] at this
  exact this

theorem t46_eq_one_of_fixAll {P : Table} {g : Equiv.Perm (Fin 693)} (hg : Rep 693 P g)
    (h : t46FixAll P = true) : g = 1 := by
  ext i
  have := (allIn_eq_true.1 h) i.val (Nat.zero_le _) i.isLt
  rw [beq_iff_eq, hg _ i.isLt, idx_of_lt _ i.isLt] at this
  exact this

theorem t46_ne_one_of_fixAll {P : Table} {g : Equiv.Perm (Fin 693)} (hg : Rep 693 P g)
    (h : t46FixAll P = false) : g ≠ 1 := by
  rintro rfl
  have : t46FixAll P = true := allIn_eq_true.2 fun i _ hi => by rw [beq_iff_eq, hg i hi, idx_one]
  rw [h] at this
  exact Bool.false_ne_true this

@[expose] noncomputable def t46x : Equiv.Perm (Fin 693) :=
  wordG t46G [30, 33, 16, 12, 9, 39, 39] ^ 3

@[expose] noncomputable def t46y : Equiv.Perm (Fin 693) := wordG t46G [41, 46, 21, 23, 36] ^ 2

theorem rep_t46x : Rep 693 t46XT t46x :=
  Rep.powT (by norm_num) (Rep.wordT (by norm_num) _ fun l _ => rep_t46G l) 3

theorem rep_t46y : Rep 693 t46YT t46y :=
  Rep.powT (by norm_num) (Rep.wordT (by norm_num) _ fun l _ => rep_t46G l) 2

@[expose] noncomputable def t46xyG (z : ℤ) : Equiv.Perm (Fin 693) := if z = 1 then t46x else t46y

theorem rep_t46xyG (z : ℤ) : Rep 693 (t46XYGen z) (t46xyG z) := by
  unfold t46XYGen t46xyG
  split_ifs
  · exact rep_t46x
  · exact rep_t46y

theorem t46_wordG_mem {P : Subgroup (Equiv.Perm (Fin 693))} {f : ℤ → Equiv.Perm (Fin 693)}
    (hf : ∀ z, f z ∈ P) (w : List ℤ) : wordG f w ∈ P := by
  induction w with
  | nil => exact P.one_mem
  | cons l w ih =>
    rw [show wordG f (l :: w) = f l * wordG f w by simp only [wordG, List.map_cons, List.prod_cons]]
    exact P.mul_mem (hf l) ih

theorem t46xyG_mem (z : ℤ) : t46xyG z ∈ Subgroup.closure {t46x, t46y} := by
  unfold t46xyG
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] noncomputable def t46Tv (k : ℕ) : Equiv.Perm (Fin 693) :=
  piGU (tvGU (vecOfCode tvGens[k]!) (tvGens_get_iso k))

theorem t46G_eq_tv (z : ℤ) : t46G z = t46Tv (z.natAbs - 1) := rfl

theorem t46G_congr {z z' : ℤ} (h : z.natAbs - 1 = z'.natAbs - 1) : t46G z = t46G z' := by
  rw [t46G_eq_tv, t46G_eq_tv, h]

theorem t46G_eq_one {z : ℤ} (hz : 46 ≤ z.natAbs - 1) : t46G z = 1 := by
  have h := rep_t46G z
  unfold t46Gen at h
  rw [getElem!_neg tvGens _ (by rw [tvGens_facts.1]; omega)] at h
  exact t46_eq_one_of_fixAll h t46SimpleFacts.tv_zero

theorem t46G_eq_word {z : ℤ} (hz : z.natAbs - 1 < 46) :
    t46G z = wordG t46xyG t46TvWords[z.natAbs - 1]! := by
  have h := rep_t46G z
  unfold t46Gen at h
  exact (t46_perm_eq_of_tblEq (Rep.wordT (by norm_num) _ fun l _ => rep_t46xyG l) h
    (t46SimpleFacts.tv_words _ hz)).symm

theorem t46G_mem_closure (z : ℤ) : t46G z ∈ Subgroup.closure {t46x, t46y} := by
  by_cases hz : z.natAbs - 1 < 46
  · rw [t46G_eq_word hz]
    exact t46_wordG_mem t46xyG_mem _
  · rw [t46G_eq_one (by omega)]
    exact Subgroup.one_mem _

theorem t46G_mem (z : ℤ) : t46G z ∈ T46 := by
  by_cases hz : z.natAbs - 1 < 46
  · have hg : t46gs (z.natAbs - 1) = t46G z := by
      rw [t46gs, t46SimpleFacts.words_get _ hz]
      simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact t46G_congr (by omega)
    have hp : pairG t46gs (2 * (z.natAbs - 1)) = t46G z := by
      unfold pairG
      rw [ite_eq_left (by omega), show 2 * (z.natAbs - 1) / 2 = z.natAbs - 1 by omega, hg]
    rw [← hp]
    apply lG_mem
    rw [mem_levelLetters_zero, t46Letters_size, t46SimpleFacts.words_size]
    omega
  · rw [t46G_eq_one (by omega)]
    exact Subgroup.one_mem _

theorem t46x_mem : t46x ∈ T46 := T46.pow_mem (t46_wordG_mem t46G_mem _) 3

theorem t46y_mem : t46y ∈ T46 := T46.pow_mem (t46_wordG_mem t46G_mem _) 2

theorem T46_le_closure : T46 ≤ Subgroup.closure {t46x, t46y} := by
  show lettersGroup (levelLetters t46Letters t46Base 0) (pairG t46gs) ≤ _
  unfold lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, -, rfl⟩
  unfold pairG
  split_ifs
  · exact t46_wordG_mem t46G_mem_closure _
  · exact Subgroup.inv_mem _ (t46_wordG_mem t46G_mem_closure _)

theorem closure_t46x_t46y : Subgroup.closure {t46x, t46y} = T46 := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) T46_le_closure
  rintro _ (rfl | rfl)
  · exact t46x_mem
  · exact t46y_mem

theorem t46x_sq : t46x ^ 2 = 1 :=
  t46_eq_one_of_fixAll (Rep.powT (by norm_num) rep_t46x 2) t46SimpleFacts.x_sq

theorem t46y_cube : t46y ^ 3 = 1 :=
  t46_eq_one_of_fixAll (Rep.powT (by norm_num) rep_t46y 3) t46SimpleFacts.y_cube

theorem t46xy_pow : (t46x * t46y) ^ 11 = 1 :=
  t46_eq_one_of_fixAll (Rep.powT (by norm_num) (Rep.compT rep_t46x rep_t46y) 11)
    t46SimpleFacts.xy_pow

theorem orderOf_t46x : orderOf t46x = 2 :=
  orderOf_eq_prime t46x_sq (t46_ne_one_of_fixAll rep_t46x t46SimpleFacts.x_ne)

theorem orderOf_t46y : orderOf t46y = 3 :=
  orderOf_eq_prime t46y_cube (t46_ne_one_of_fixAll rep_t46y t46SimpleFacts.y_ne)

theorem orderOf_t46xy : orderOf (t46x * t46y) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact orderOf_eq_prime t46xy_pow
    (t46_ne_one_of_fixAll (Rep.compT rep_t46x rep_t46y) t46SimpleFacts.xy_ne)

noncomputable abbrev t46xE : T46 := ⟨t46x, t46x_mem⟩

noncomputable abbrev t46yE : T46 := ⟨t46y, t46y_mem⟩

theorem closure_t46xE_t46yE : Subgroup.closure ({t46xE, t46yE} : Set T46) = ⊤ := by
  apply Subgroup.map_injective T46.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Set.image_insert_eq, Set.image_singleton]
  exact closure_t46x_t46y

theorem orderOf_t46xE : orderOf t46xE = 2 := by
  rw [Subgroup.orderOf_mk, orderOf_t46x]

theorem orderOf_t46yE : orderOf t46yE = 3 := by
  rw [Subgroup.orderOf_mk, orderOf_t46y]

theorem orderOf_t46xE_t46yE : orderOf (t46xE * t46yE) = 11 := by
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
  exact orderOf_t46xy

theorem t46Base_get_zero : t46Base[0]! = 0 := by decide

theorem t46Base_get_one : t46Base[1]! = 1 := by decide

theorem t46_treeFacts_zero :
    TreeFacts 693 t46Trees[0]! (levelLetters t46Letters t46Base 0) (pairG t46gs) 0 := by
  have := t46_chain_facts.1 0 (by rw [t46Base_size]; norm_num)
  rwa [t46Base_get_zero] at this

theorem t46_treeFacts_one :
    TreeFacts 693 t46Trees[1]! (levelLetters t46Letters t46Base 1) (pairG t46gs) 1 := by
  have := t46_chain_facts.1 1 (by rw [t46Base_size]; norm_num)
  rwa [t46Base_get_one] at this

instance isPretransitive_T46 : MulAction.IsPretransitive T46 (Fin 693) := by
  have hT := t46_treeFacts_zero
  have hcard := hT.card_orbit
  rw [t46_tree_size (l := 0) rfl] at hcard
  have huniv : MulAction.orbit (lettersGroup (levelLetters t46Letters t46Base 0) (pairG t46gs))
      (⟨0, hT.r_lt⟩ : Fin 693) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) _ (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin, ← Nat.card_coe_set_eq, hcard]
  have hreach : ∀ p : Fin 693, ∃ g : T46, g • (0 : Fin 693) = p := by
    intro p
    have hp : p ∈ MulAction.orbit (lettersGroup (levelLetters t46Letters t46Base 0)
        (pairG t46gs)) (⟨0, hT.r_lt⟩ : Fin 693) := by
      rw [huniv]; trivial
    obtain ⟨⟨g, hg⟩, hgp⟩ := hp
    exact ⟨⟨g, hg⟩, hgp⟩
  refine ⟨fun p q => ?_⟩
  obtain ⟨g, hg⟩ := hreach p
  obtain ⟨h, hh⟩ := hreach q
  exact ⟨h * g⁻¹, by rw [mul_smul, ← hg, inv_smul_smul, hh]⟩

theorem t46lvl_one_le : t46lvl 1 ≤ T46 := levelGroup_anti (pairG t46gs) (Nat.zero_le 1)

theorem t46_fix_zero_iff {g : Equiv.Perm (Fin 693)} (hg : g ∈ T46) :
    g (0 : Fin 693) = 0 ↔ g ∈ t46lvl 1 := by
  have := t46_chain_facts.2.1 0 (by rw [t46Base_size]; norm_num) g hg
  rw [t46Base_get_zero, idx_of_lt g (by norm_num : 0 < 693)] at this
  exact Fin.ext_iff.trans this

theorem t46lvl_one_fix {g : Equiv.Perm (Fin 693)} (hg : g ∈ t46lvl 1) : g • (0 : Fin 693) = 0 :=
  (t46_fix_zero_iff (t46lvl_one_le hg)).2 hg

theorem stabilizer_T46_zero :
    MulAction.stabilizer T46 (0 : Fin 693) = (t46lvl 1).subgroupOf T46 := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← t46_fix_zero_iff g.2]
  rfl

theorem card_t46lvl_one : Nat.card (t46lvl 1) = 13271040 := by
  rw [t46_chain_facts.2.2 1 (by rw [t46Base_size]; norm_num), t46Base_size]
  rw [show Finset.Ico 1 5 = {1, 2, 3, 4} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton, t46_tree_size (l := 1) rfl,
    t46_tree_size (l := 2) rfl, t46_tree_size (l := 3) rfl, t46_tree_size (l := 4) rfl]
  norm_num

theorem card_stabilizer_T46_zero :
    Nat.card (MulAction.stabilizer T46 (0 : Fin 693)) = 13271040 := by
  rw [stabilizer_T46_zero, Nat.card_congr (Subgroup.subgroupOfEquivOfLe t46lvl_one_le).toEquiv,
    card_t46lvl_one]

theorem rep_pairG_t46 : ∀ l < t46Letters.size, Rep 693 t46Letters[l]! (pairG t46gs l) :=
  rep_pairG rep_t46Letters (chainOK_parts localCert_parts.2.1).1
    (chainOK_parts localCert_parts.2.1).2.1

theorem t46_treeFacts_sub :
    TreeFacts 693 t46SubTree t46Lv1 (pairG t46gs) t46SubRoot :=
  treeOK_facts (fun l hl => rep_pairG_t46 l (levelLetters_lt hl)) t46SimpleFacts.sub_tree

theorem t46InTree_iff {T : Tree} {lv : Array ℕ} {r : ℕ}
    (hT : TreeFacts 693 T lv (pairG t46gs) r) (p : Fin 693) :
    t46InTree T p.val = true ↔
      p ∈ MulAction.orbit (lettersGroup lv (pairG t46gs)) (⟨r, hT.r_lt⟩ : Fin 693) := by
  rw [hT.mem_orbit_iff]
  simp only [t46InTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨k, hk, hkp⟩
    refine ⟨?_, ?_⟩
    · rw [← hkp, hT.pos_pts k hk]; exact hk
    · rw [← hkp, hT.pos_pts k hk]

theorem t46_inTree_one_iff (p : Fin 693) : t46InTree t46Trees[1]! p.val = true ↔
    p ∈ MulAction.orbit (t46lvl 1) (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693) :=
  t46InTree_iff t46_treeFacts_one p

theorem t46_inTree_sub_iff
    (p : Fin 693) : t46InTree t46SubTree p.val = true ↔
    p ∈ MulAction.orbit (t46lvl 1) (⟨t46SubRoot, t46_treeFacts_sub.r_lt⟩ : Fin 693) :=
  t46InTree_iff t46_treeFacts_sub p

@[expose] noncomputable def t46SubLab (p : Fin 693) : Fin 3 :=
  if p.val = 0 then 0 else if t46InTree t46Trees[1]! p.val = true then 1 else 2

theorem t46_orbit_smul_mem {H : Subgroup (Equiv.Perm (Fin 693))} {x p : Fin 693}
    (h : Equiv.Perm (Fin 693)) (hh : h ∈ H) (hp : p ∈ MulAction.orbit H x) :
    h • p ∈ MulAction.orbit H x := by
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  refine ⟨⟨h * k, H.mul_mem hh hk⟩, ?_⟩
  show (h * k) • x = h • (k • x)
  exact mul_smul h k x

theorem t46_orbit_one_ne_zero (p : Fin 693)
    (hp : p ∈ MulAction.orbit (t46lvl 1) (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693)) :
    p.val ≠ 0 := by
  intro h0
  obtain ⟨⟨k, hk⟩, hkp⟩ := hp
  have hp0 : p = 0 := Fin.ext h0
  have : (k⁻¹ : Equiv.Perm (Fin 693)) • p = (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693) := by
    rw [← hkp]
    exact inv_smul_smul k _
  rw [hp0, t46lvl_one_fix ((t46lvl 1).inv_mem hk)] at this
  exact Nat.zero_ne_one (congrArg Fin.val this)

theorem t46SubLab_eq_zero {p : Fin 693} : t46SubLab p = 0 ↔ p = 0 := by
  unfold t46SubLab
  constructor
  · intro h
    by_contra hp
    have hp' : p.val ≠ 0 := fun e => hp (Fin.ext e)
    rw [ite_eq_right hp'] at h
    split_ifs at h <;> exact absurd h (by decide)
  · rintro rfl; simp

theorem t46SubLab_eq_one {p : Fin 693} :
    t46SubLab p = 1 ↔ p ∈ MulAction.orbit (t46lvl 1) (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693) := by
  rw [← t46_inTree_one_iff p]
  unfold t46SubLab
  constructor
  · intro h
    split_ifs at h with h0 h1
    · exact absurd h (by decide)
    · exact h1
    · exact absurd h (by decide)
  · intro h
    have h0 : p.val ≠ 0 := t46_orbit_one_ne_zero p ((t46_inTree_one_iff p).1 h)
    rw [ite_eq_right h0, ite_eq_left h]

theorem t46SubLab_eq_two {p : Fin 693} : t46SubLab p = 2 ↔
    p ≠ 0 ∧ p ∉ MulAction.orbit (t46lvl 1) (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693) := by
  rw [← t46_inTree_one_iff p]
  unfold t46SubLab
  constructor
  · intro h
    split_ifs at h with h0 h1
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact ⟨fun e => h0 (congrArg Fin.val e), h1⟩
  · rintro ⟨h0, h1⟩
    have h0' : p.val ≠ 0 := fun e => h0 (Fin.ext e)
    rw [ite_eq_right h0', ite_eq_right h1]

theorem t46SubLab_two_mem_orbit
    {p : Fin 693} (h : t46SubLab p = 2) :
    p ∈ MulAction.orbit (t46lvl 1) (⟨t46SubRoot, t46_treeFacts_sub.r_lt⟩ : Fin 693) := by
  obtain ⟨h0, h1⟩ := t46SubLab_eq_two.1 h
  rw [← t46_inTree_one_iff p] at h1
  rcases t46SimpleFacts.cover p.val p.isLt with hc | hc | hc
  · exact absurd (Fin.ext hc) h0
  · exact absurd hc h1
  · exact (t46_inTree_sub_iff p).1 hc

theorem t46SubLab_inv : ∀ h ∈ t46lvl 1, ∀ p : Fin 693, t46SubLab (h • p) = t46SubLab p := by
  intro h hh p
  have hinv : h⁻¹ ∈ t46lvl 1 := (t46lvl 1).inv_mem hh
  by_cases hp0 : p = 0
  · rw [hp0, t46lvl_one_fix hh]
  by_cases hp1 : p ∈ MulAction.orbit (t46lvl 1) (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693)
  · rw [t46SubLab_eq_one.2 hp1, t46SubLab_eq_one.2 (t46_orbit_smul_mem h hh hp1)]
  · have h2 : t46SubLab p = 2 := t46SubLab_eq_two.2 ⟨hp0, hp1⟩
    rw [h2, t46SubLab_eq_two]
    refine ⟨fun e => hp0 ?_, fun e => hp1 ?_⟩
    · have := congrArg (fun q => h⁻¹ • q) e
      simp only [inv_smul_smul] at this
      rw [this, t46lvl_one_fix hinv]
    · have := t46_orbit_smul_mem h⁻¹ hinv e
      rwa [inv_smul_smul] at this

theorem t46SubLab_orb :
    ∀ p q : Fin 693, t46SubLab p = t46SubLab q → ∃ h ∈ t46lvl 1, h • p = q := by
  intro p q hpq
  have key : ∀ {x : Fin 693} {H : Subgroup (Equiv.Perm (Fin 693))},
      p ∈ MulAction.orbit H x → q ∈ MulAction.orbit H x → ∃ h ∈ H, h • p = q := by
    intro x H hp hq
    obtain ⟨⟨u, hu⟩, rfl⟩ := hp
    obtain ⟨⟨v, hv⟩, rfl⟩ := hq
    refine ⟨v * u⁻¹, H.mul_mem hv (H.inv_mem hu), ?_⟩
    show (v * u⁻¹) • (u • x) = v • x
    rw [mul_smul, inv_smul_smul]
  have hcases : t46SubLab p = 0 ∨ t46SubLab p = 1 ∨ t46SubLab p = 2 := by
    rcases t46SubLab p with ⟨_ | _ | _ | n, hn⟩
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · omega
  rcases hcases with h | h | h
  · have hq := hpq ▸ h
    rw [t46SubLab_eq_zero.1 h, t46SubLab_eq_zero.1 hq]
    exact ⟨1, (t46lvl 1).one_mem, one_smul _ _⟩
  · exact key (t46SubLab_eq_one.1 h) (t46SubLab_eq_one.1 (hpq ▸ h))
  · exact key (t46SubLab_two_mem_orbit h) (t46SubLab_two_mem_orbit (hpq ▸ h))

theorem card_t46SubLab_one :
    (Finset.univ.filter (fun p : Fin 693 => t46SubLab p = 1)).card = 512 := by
  have hc := t46_treeFacts_one.card_orbit
  rw [t46_tree_size (l := 1) rfl] at hc
  have hset : MulAction.orbit (lettersGroup (levelLetters t46Letters t46Base 1) (pairG t46gs))
      (⟨1, t46_treeFacts_one.r_lt⟩ : Fin 693) =
      ↑(Finset.univ.filter (fun p : Fin 693 => t46SubLab p = 1)) := by
    ext p
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
    exact t46SubLab_eq_one.symm
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  exact hc

theorem card_t46SubLab_zero :
    (Finset.univ.filter (fun p : Fin 693 => t46SubLab p = 0)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact t46SubLab_eq_zero

theorem card_t46SubLab_two :
    (Finset.univ.filter (fun p : Fin 693 => t46SubLab p = 2)).card = 180 := by
  have h := Finset.card_eq_sum_card_fiberwise (f := t46SubLab) (s := Finset.univ)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at h
  have h0 := card_t46SubLab_zero
  have h1 := card_t46SubLab_one
  omega

@[expose] def t46SubSizes : Fin 3 → ℕ := ![1, 512, 180]

theorem t46SubSizes_blocks : ∀ S : Finset (Fin 3), (0 : Fin 3) ∈ S →
    (∑ i ∈ S, t46SubSizes i) ∣ 693 → S = {0} ∨ S = Finset.univ := by
  decide

theorem card_t46SubLab (i : Fin 3) :
    (Finset.univ.filter (fun p : Fin 693 => t46SubLab p = i)).card = t46SubSizes i := by
  fin_cases i
  · exact card_t46SubLab_zero
  · exact card_t46SubLab_one
  · exact card_t46SubLab_two

instance isPreprimitive_T46 :
    MulAction.IsPreprimitive T46 (Fin 693) := by
  refine isPreprimitive_of_suborbit_labels (0 : Fin 693) ((t46lvl 1).subgroupOf T46)
    (fun h hh => t46lvl_one_fix (Subgroup.mem_subgroupOf.1 hh)) t46SubLab
    (fun h hh p => t46SubLab_inv h (Subgroup.mem_subgroupOf.1 hh) p) (fun p q hpq => ?_) ?_
  · obtain ⟨h, hh, hhp⟩ := t46SubLab_orb p q hpq
    exact ⟨⟨h, t46lvl_one_le hh⟩, Subgroup.mem_subgroupOf.2 hh, hhp⟩
  · intro S hS hdvd
    have h0 : t46SubLab 0 = 0 := t46SubLab_eq_zero.2 rfl
    rw [h0] at hS ⊢
    have hsum : (∑ i ∈ S, (Finset.univ.filter (fun p : Fin 693 => t46SubLab p = i)).card) =
        ∑ i ∈ S, t46SubSizes i := Finset.sum_congr rfl fun i _ => card_t46SubLab i
    rw [hsum, Fintype.card_fin] at hdvd
    exact t46SubSizes_blocks S hS hdvd

theorem isSimpleGroup_T46 :
    IsSimpleGroup T46 := by
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin 693) ?_ t46xE t46yE
    closure_t46xE_t46yE 0 ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  · rw [orderOf_t46xE, orderOf_t46yE]; norm_num
  · rw [orderOf_t46xE_t46yE, card_stabilizer_T46_zero]; norm_num

end CFSG.Fischer
