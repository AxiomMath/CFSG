module

public import CFSG.LieType.Chevalley.E6SignedGraphRoots
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.LieType.Chevalley.E6SignedGraph

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped Pointwise

@[expose] def orbitRefl
    (O : Finset E6Vec) : WeylGroup TwistTag.E6.tag :=
  (O.toList.map rootReflection).prod

@[expose] def gen
    (i : Fin 4) : WeylGroup TwistTag.E6.tag :=
  orbitRefl (simpleOrbit i)

@[expose] def weylGroup
    : Subgroup (WeylGroup TwistTag.E6.tag) :=
  Subgroup.closure (Set.range gen)

@[expose] def wordLength
    (w : WeylGroup TwistTag.E6.tag) : ℕ :=
  sInf {n | ∃ l : List (Fin 4), l.length = n ∧ (l.map gen).prod = w}

@[expose] def finWord (l : List ℕ) : List (Fin TwistTag.E6.tag.rank) :=
  l.filterMap fun i => if h : i < 6 then some ⟨i, h⟩ else none

@[expose] def genWord (i : Fin 4) : List (Fin TwistTag.E6.tag.rank) :=
  finWord (![[2, 3, 1, 3, 2, 4, 3, 1, 3, 4], [0, 5], [2, 4], [3]] i)

@[expose] def genAct (i : Fin 4) (v : E6Vec) : E6Vec :=
  (genWord i).foldr (reflect TwistTag.E6.tag) v

@[expose] def wordAct (l : List (Fin 4)) (v : E6Vec) : E6Vec :=
  l.foldr genAct v

@[expose] def reflVec (β v : E6Vec) : E6Vec :=
  v - corootPair β v • β

theorem orbitRefl_singleton
    (a : E6Vec) : orbitRefl {a} = rootReflection a := by
  simp [orbitRefl]

theorem orbitRefl_pair
    {a b : E6Vec} (hab : a ≠ b)
    (hc : Commute (rootReflection a) (rootReflection b)) :
    orbitRefl {a, b} = rootReflection a * rootReflection b := by
  have hperm : ({a, b} : Finset E6Vec).toList.Perm [a, b] := by
    rw [List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (by simp [hab])]
    intro x
    simp
  rw [orbitRefl, ← (hperm.map rootReflection).symm.prod_eq' (List.pairwise_pair.2 hc)]
  simp

theorem orbitRefl_eq_of_ne
    {a : E6Vec} (ha : IsRoot TwistTag.E6.tag a)
    (hb : IsRoot TwistTag.E6.tag (rho a)) (hne : rho a ≠ a) (ω : List (Fin TwistTag.E6.tag.rank))
    (hcomm : ∀ j, reflVec a (reflVec (rho a) (Pi.single j 1)) =
      reflVec (rho a) (reflVec a (Pi.single j 1)))
    (hω : ∀ j, reflVec a (reflVec (rho a) (Pi.single j 1)) =
      ω.foldr (reflect TwistTag.E6.tag) (Pi.single j 1)) :
    orbitRefl (TwistTag.E6.diagramOrbit a) = (coxeterSystem TwistTag.E6.tag).wordProd ω := by
  have hc : Commute (rootReflection a) (rootReflection (rho a)) := by
    change _ * _ = _ * _
    refine ext_single fun j => ?_
    simp only [mul_smul, rootReflection_smul ha, rootReflection_smul hb]
    exact hcomm j
  rw [diagramOrbit_eq, orbitRefl_pair (Ne.symm hne) hc]
  refine ext_single fun j => ?_
  simp only [mul_smul, rootReflection_smul ha, rootReflection_smul hb, wordProd_smul]
  exact hω j

theorem orbitRefl_eq_of_eq
    {a : E6Vec} (ha : IsRoot TwistTag.E6.tag a) (heq : rho a = a)
    (ω : List (Fin TwistTag.E6.tag.rank))
    (hω : ∀ j, reflVec a (Pi.single j 1) = ω.foldr (reflect TwistTag.E6.tag) (Pi.single j 1)) :
    orbitRefl (TwistTag.E6.diagramOrbit a) = (coxeterSystem TwistTag.E6.tag).wordProd ω := by
  rw [diagramOrbit_eq, heq, Finset.pair_eq_singleton, orbitRefl_singleton]
  refine ext_single fun j => ?_
  rw [rootReflection_smul ha, wordProd_smul]
  exact hω j

theorem gen_eq
    (i : Fin 4) : gen i = (coxeterSystem TwistTag.E6.tag).wordProd (genWord i) := by
  fin_cases i
  · exact orbitRefl_eq_of_ne (isRoot_simpleRoot 0) (isRoot_rho_simpleRoot 0) (by decide +kernel)
      _ (by decide +kernel) (by decide +kernel)
  · exact orbitRefl_eq_of_ne (isRoot_simpleRoot 1) (isRoot_rho_simpleRoot 1) (by decide +kernel)
      _ (by decide +kernel) (by decide +kernel)
  · exact orbitRefl_eq_of_ne (isRoot_simpleRoot 2) (isRoot_rho_simpleRoot 2) (by decide +kernel)
      _ (by decide +kernel) (by decide +kernel)
  · exact orbitRefl_eq_of_eq (isRoot_simpleRoot 3) (by decide +kernel) _ (by decide +kernel)

theorem gen_smul
    (i : Fin 4) (v : E6Vec) : gen i • v = genAct i v := by
  rw [gen_eq, wordProd_smul]
  rfl

theorem prod_smul
    (l : List (Fin 4)) (v : E6Vec) : (l.map gen).prod • v = wordAct l v := by
  induction l with
  | nil => simp [wordAct]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, gen_smul]
    rfl

theorem gen_mem_relWeylTwist
    (i : Fin 4) : gen i ∈ relWeylTwist TwistTag.E6 := by
  rw [mem_relWeylTwist, gen_eq, weylTwist_wordProd]
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul]
  revert i k
  decide +kernel

theorem gen_mul_gen
    (i : Fin 4) : gen i * gen i = 1 := by
  refine ext_single fun k => ?_
  rw [mul_smul, gen_smul, gen_smul, one_smul]
  revert i k
  decide +kernel

theorem gen_inv
    (i : Fin 4) : (gen i)⁻¹ = gen i :=
  inv_eq_of_mul_eq_one_right (gen_mul_gen i)

theorem gen_smul_gen_smul
    (i : Fin 4) (v : E6Vec) : gen i • gen i • v = v := by
  rw [← mul_smul, gen_mul_gen, one_smul]

theorem prod_mem_weylGroup
    (l : List (Fin 4)) : (l.map gen).prod ∈ weylGroup := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem gen_posList_check : ∀ i : Fin 4, ∀ v ∈ posList, v ≠ simpleVec i →
    genAct i v ∈ posList ∧ genAct i v ≠ simpleVec i := by
  decide +kernel

theorem gen_simpleVec_check : ∀ i : Fin 4, genAct i (simpleVec i) = -simpleVec i := by
  decide +kernel

theorem gen_smul_simpleVec
    (i : Fin 4) : gen i • simpleVec i = -simpleVec i := by
  rw [gen_smul]
  exact gen_simpleVec_check i

theorem gen_mapsTo
    (i : Fin 4) :
    Set.MapsTo (gen i • ·) (posVecs \ {simpleVec i}) (posVecs \ {simpleVec i}) := by
  rintro v ⟨hv, hne⟩
  rw [mem_posVecs_iff] at hv
  obtain ⟨h1, h2⟩ := gen_posList_check i v hv hne
  show gen i • v ∈ posVecs \ {simpleVec i}
  rw [gen_smul]
  exact ⟨mem_posVecs_iff.2 h1, h2⟩

theorem bijOn_gen
    (i : Fin 4) :
    Set.BijOn (gen i • ·) (posVecs \ {simpleVec i}) (posVecs \ {simpleVec i}) :=
  ⟨gen_mapsTo i, (MulAction.injective (gen i)).injOn,
    fun u hu => ⟨gen i • u, gen_mapsTo i hu, gen_smul_gen_smul i u⟩⟩

theorem smul_mem_fixedLattice
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    {x : E6Vec} (hx : x ∈ TwistTag.E6.fixedLattice) : w • x ∈ TwistTag.E6.fixedLattice := by
  rw [TwistTag.mem_fixedLattice] at hx ⊢
  rw [← (mem_relWeylTwist_iff_smul TwistTag.E6).1 hw, hx]

theorem rho_smul
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6) (v : E6Vec) :
    rho (w • v) = w • rho v :=
  ((mem_relWeylTwist_iff_smul TwistTag.E6).1 hw v).symm

@[expose] def parityGroup :
    Subgroup (WeylGroup TwistTag.E6.tag) where
  carrier := {w | w ∈ relWeylTwist TwistTag.E6 ∧ ∀ x ∈ TwistTag.E6.fixedLattice,
    Even ((w • x) ⟨1, by decide⟩ - x ⟨1, by decide⟩)}
  mul_mem' := by
    rintro w w' ⟨hw, hpw⟩ ⟨hw', hpw'⟩
    refine ⟨mul_mem hw hw', fun x hx => ?_⟩
    have h := (hpw _ (smul_mem_fixedLattice hw' hx)).add (hpw' x hx)
    rw [sub_add_sub_cancel] at h
    rwa [mul_smul]
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  inv_mem' := by
    rintro w ⟨hw, hpw⟩
    refine ⟨inv_mem hw, fun x hx => ?_⟩
    have h := (hpw _ (smul_mem_fixedLattice (inv_mem hw) hx)).neg
    rwa [smul_inv_smul, neg_sub] at h

theorem orbitSum_check :
    TwistTag.E6.orbitSum ⟨0, by decide⟩ =
        (Pi.single ⟨0, by decide⟩ 1 + Pi.single (TwistTag.E6.perm ⟨0, by decide⟩) 1 : E6Vec) ∧
      TwistTag.E6.orbitSum ⟨1, by decide⟩ =
        (Pi.single ⟨2, by decide⟩ 1 + Pi.single (TwistTag.E6.perm ⟨2, by decide⟩) 1 : E6Vec) ∧
      TwistTag.E6.orbitSum ⟨2, by decide⟩ = (Pi.single ⟨3, by decide⟩ 1 : E6Vec) ∧
      TwistTag.E6.orbitSum ⟨3, by decide⟩ = (Pi.single ⟨1, by decide⟩ 1 : E6Vec) := by
  decide +kernel

theorem even_smul_pair
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (j : Fin TwistTag.E6.tag.rank) :
    Even ((w • (Pi.single j 1 + Pi.single (TwistTag.E6.perm j) 1 : E6Vec)) ⟨1, by decide⟩) := by
  have h : (w • (Pi.single (TwistTag.E6.perm j) 1 : E6Vec)) ⟨1, by decide⟩ =
      (w • (Pi.single j 1 : E6Vec)) ⟨1, by decide⟩ := by
    rw [← permLattice_single, ← rho, ← rho_smul hw, rho_apply_one]
  rw [smul_add, Pi.add_apply, h]
  exact ⟨_, rfl⟩

theorem mem_parityGroup_of
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6)
    (h2 : Odd ((w • (Pi.single ⟨1, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩))
    (h4 : Even ((w • (Pi.single ⟨3, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩)) :
    w ∈ parityGroup := by
  obtain ⟨e0, e1, e2, e3⟩ := orbitSum_check
  have hf : ∀ a, Even ((w • TwistTag.E6.orbitSum a) ⟨1, by decide⟩ -
      TwistTag.E6.orbitSum a ⟨1, by decide⟩) := by
    intro a
    fin_cases a
    · rw [e0, show (Pi.single ⟨0, by decide⟩ 1 + Pi.single (TwistTag.E6.perm ⟨0, by decide⟩) 1 :
        E6Vec) ⟨1, by decide⟩ = 0 by decide +kernel, sub_zero]
      exact even_smul_pair hw _
    · rw [e1, show (Pi.single ⟨2, by decide⟩ 1 + Pi.single (TwistTag.E6.perm ⟨2, by decide⟩) 1 :
        E6Vec) ⟨1, by decide⟩ = 0 by decide +kernel, sub_zero]
      exact even_smul_pair hw _
    · rw [e2, show (Pi.single ⟨3, by decide⟩ 1 : E6Vec) ⟨1, by decide⟩ = 0 by decide +kernel,
        sub_zero]
      exact h4
    · rw [e3, show (Pi.single ⟨1, by decide⟩ 1 : E6Vec) ⟨1, by decide⟩ = 1 by decide +kernel]
      exact h2.sub_odd odd_one
  refine ⟨hw, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := TwistTag.E6.exists_foldMap_eq hx
  rw [TwistTag.foldMap_apply, Finset.smul_sum, Finset.sum_apply, Finset.sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.even_sum _ fun a _ => ?_
  rw [smul_comm, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub]
  exact (hf a).mul_left _

theorem single_one_mem_fixedLattice :
    (Pi.single ⟨1, by decide⟩ 1 : E6Vec) ∈ TwistTag.E6.fixedLattice := by
  rw [TwistTag.mem_fixedLattice]
  decide +kernel

theorem single_three_mem_fixedLattice :
    (Pi.single ⟨3, by decide⟩ 1 : E6Vec) ∈ TwistTag.E6.fixedLattice := by
  rw [TwistTag.mem_fixedLattice]
  decide +kernel

theorem parity_of_mem_parityGroup
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup) :
    Odd ((w • (Pi.single ⟨1, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) ∧
      Even ((w • (Pi.single ⟨3, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) := by
  have a := hw.2 _ single_one_mem_fixedLattice
  have b := hw.2 _ single_three_mem_fixedLattice
  rw [show (Pi.single ⟨1, by decide⟩ 1 : E6Vec) ⟨1, by decide⟩ = 1 by decide +kernel] at a
  rw [show (Pi.single ⟨3, by decide⟩ 1 : E6Vec) ⟨1, by decide⟩ = 0 by decide +kernel,
    sub_zero] at b
  obtain ⟨r, hr⟩ := a
  exact ⟨⟨r, by omega⟩, b⟩

theorem mem_parityGroup_iff
    {w : WeylGroup TwistTag.E6.tag} :
    w ∈ parityGroup ↔ w ∈ relWeylTwist TwistTag.E6 ∧
      Odd ((w • (Pi.single ⟨1, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) ∧
      Even ((w • (Pi.single ⟨3, by decide⟩ 1 : E6Vec)) ⟨1, by decide⟩) :=
  ⟨fun hw => ⟨hw.1, parity_of_mem_parityGroup hw⟩,
    fun ⟨hw, h2, h4⟩ => mem_parityGroup_of hw h2 h4⟩

theorem gen_parity_check : ∀ i : Fin 4,
    Odd ((genAct i (Pi.single ⟨1, by decide⟩ 1)) ⟨1, by decide⟩) ∧
      Even ((genAct i (Pi.single ⟨3, by decide⟩ 1)) ⟨1, by decide⟩) := by
  decide +kernel

theorem gen_mem_parityGroup
    (i : Fin 4) : gen i ∈ parityGroup := by
  refine mem_parityGroup_of (gen_mem_relWeylTwist i) ?_ ?_
  · rw [gen_smul]
    exact (gen_parity_check i).1
  · rw [gen_smul]
    exact (gen_parity_check i).2

theorem weylGroup_le_parityGroup :
    weylGroup ≤ parityGroup :=
  (Subgroup.closure_le _).2 (Set.range_subset_iff.2 gen_mem_parityGroup)

theorem smul_vecOf
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ relWeylTwist TwistTag.E6) (α : E6Vec) :
    w • vecOf α = vecOf (w • α) := by
  have hiff : rho (w • α) = w • α ↔ rho α = α := by
    rw [rho_smul hw]
    exact (MulAction.injective w).eq_iff
  unfold vecOf
  split_ifs with h1 h2 h2
  · exact smul_comm w 2 α
  · exact absurd (hiff.2 h1) h2
  · exact absurd (hiff.1 h2) h1
  · rw [smul_add, rho_smul hw]

theorem smul_mem_vecs
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup) {v : E6Vec}
    (hv : v ∈ vecs) : w • v ∈ vecs := by
  obtain ⟨α, hα, hk, rfl⟩ := mem_vecs.1 hv
  refine mem_vecs.2 ⟨w • α, IsRoot.smul hα w, ?_, (smul_vecOf hw.1 α).symm⟩
  unfold keep at hk ⊢
  by_cases h : rho α = α
  · have hfix : α ∈ TwistTag.E6.fixedLattice := h
    have he := hw.2 α hfix
    have hw' : rho (w • α) = w • α := by rw [rho_smul hw.1, h]
    simp only [h, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hk
    simp only [hw', decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq]
    have h2 := he.add hk
    rwa [sub_add_cancel] at h2
  · have hw' : rho (w • α) ≠ w • α := by
      rw [rho_smul hw.1]
      exact fun e => h (MulAction.injective w e)
    simp [hw']

@[expose] def posFinset : Finset E6Vec :=
  posList.toFinset

theorem mem_posFinset {v : E6Vec} : v ∈ posFinset ↔ v ∈ posVecs := by
  rw [posFinset, List.mem_toFinset, mem_posVecs_iff]

theorem card_posFinset : posFinset.card = 16 := by
  decide +kernel

@[expose] def invFinset
    (w : WeylGroup TwistTag.E6.tag) : Finset E6Vec :=
  posFinset.filter fun v => -(w • v) ∈ posFinset

theorem coe_invFinset
    (w : WeylGroup TwistTag.E6.tag) :
    (↑(invFinset w) : Set E6Vec) = {v | v ∈ posVecs ∧ w • v ∈ -posVecs} := by
  ext v
  simp only [invFinset, Finset.coe_filter, mem_posFinset, Set.mem_ofPred_eq, Set.mem_neg]

theorem invFinset_one
    : invFinset 1 = ∅ := by
  refine Finset.filter_false_of_mem fun v hv => ?_
  rw [one_smul, mem_posFinset]
  exact not_neg_mem_posVecs (mem_posFinset.1 hv)

theorem card_filter_split
    (P : E6Vec → Prop) [DecidablePred P] (i : Fin 4) :
    (posFinset.filter P).card =
      ((posFinset.erase (simpleVec i)).filter P).card + if P (simpleVec i) then 1 else 0 := by
  have hβ : simpleVec i ∈ posFinset := mem_posFinset.2 (simpleVec_mem_posVecs i)
  conv_lhs => rw [← Finset.insert_erase hβ]
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem card_invFinset_mul_gen
    {w : WeylGroup TwistTag.E6.tag} (hw : ∀ v ∈ vecs, w • v ∈ vecs)
    (i : Fin 4) :
    (-(w • simpleVec i) ∈ posVecs → (invFinset (w * gen i)).card + 1 = (invFinset w).card) ∧
      (w • simpleVec i ∈ posVecs → (invFinset (w * gen i)).card = (invFinset w).card + 1) := by
  have hbij : ((posFinset.erase (simpleVec i)).filter fun v => -((w * gen i) • v) ∈ posFinset).card
      = ((posFinset.erase (simpleVec i)).filter fun v => -(w • v) ∈ posFinset).card := by
    have hmaps : ∀ v ∈ posFinset.erase (simpleVec i),
        gen i • v ∈ posFinset.erase (simpleVec i) := by
      intro v hv
      rw [Finset.mem_erase, mem_posFinset] at hv ⊢
      obtain ⟨h1, h2⟩ := gen_mapsTo i ⟨hv.2, hv.1⟩
      exact ⟨h2, h1⟩
    refine Finset.card_nbij' (gen i • ·) (gen i • ·) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      rw [mul_smul] at hv
      exact ⟨hmaps v hv.1, hv.2⟩
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv ⊢
      refine ⟨hmaps v hv.1, ?_⟩
      rw [mul_smul, gen_smul_gen_smul]
      exact hv.2
    · intro v _
      exact gen_smul_gen_smul i v
    · intro v _
      exact gen_smul_gen_smul i v
  have hv := hw _ (simpleVec_mem_posVecs i).1
  have hwr : -((w * gen i) • simpleVec i) = w • simpleVec i := by
    rw [mul_smul, gen_smul_simpleVec, smul_neg, neg_neg]
  rw [invFinset, invFinset, card_filter_split _ i, card_filter_split _ i, hbij, hwr]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hn : w • simpleVec i ∉ posFinset := fun h' =>
      not_neg_mem_posVecs (mem_posFinset.1 h') h
    have hp : -(w • simpleVec i) ∈ posFinset := mem_posFinset.2 h
    simp only [hn, hp, ↓reduceIte, add_zero]
  · have hn : -(w • simpleVec i) ∉ posFinset := fun h' =>
      not_neg_mem_posVecs h (mem_posFinset.1 h')
    have hp : w • simpleVec i ∈ posFinset := mem_posFinset.2 h
    simp only [hn, hp, ↓reduceIte, add_zero]

theorem card_invFinset_mul_gen_le
    {w : WeylGroup TwistTag.E6.tag} (hw : ∀ v ∈ vecs, w • v ∈ vecs)
    (i : Fin 4) : (invFinset (w * gen i)).card ≤ (invFinset w).card + 1 := by
  obtain ⟨h1, h2⟩ := card_invFinset_mul_gen hw i
  rcases mem_posVecs_or_neg (hw _ (simpleVec_mem_posVecs i).1) with h | h
  · exact (h2 h).le
  · have := h1 h
    omega

theorem decomp_check : ∀ v ∈ posList, (∃ j, v = simpleVec j) ∨
    ∃ a ∈ posList, ∃ b ∈ posList, v = a + b := by
  decide +kernel

theorem indec_check : ∀ i : Fin 4, ∀ a ∈ posList, ∀ b ∈ posList, simpleVec i ≠ a + b := by
  decide +kernel

theorem gram_check3 : ∀ j : Fin 4, iform (simpleVec j) (simpleVec j) = 8 → j = 3 := by
  decide +kernel

theorem gram_check2 : ∀ j : Fin 4, iform (simpleVec j) (simpleVec 3) = -4 → j = 2 := by
  decide +kernel

theorem gram_check1 : ∀ j : Fin 4, iform (simpleVec j) (simpleVec 2) = -2 →
    iform (simpleVec j) (simpleVec 3) = 0 → j = 1 := by
  decide +kernel

theorem gram_check0 : ∀ j : Fin 4, iform (simpleVec j) (simpleVec 1) = -2 →
    iform (simpleVec j) (simpleVec 2) = 0 → j = 0 := by
  decide +kernel

theorem two_smul_orbitSum_check : ∀ a : Fin TwistTag.E6.foldedTag.rank,
    (2 : ℤ) • TwistTag.E6.orbitSum a = ∑ i : Fin 4,
      (![![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 1], ![1, 0, -1, -1]] a i) • simpleVec i := by
  decide +kernel

theorem eq_one_of_forall_pos
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup)
    (hpos : ∀ v ∈ posVecs, w • v ∈ posVecs) : w = 1 := by
  have hinv : ∀ v ∈ posVecs, w⁻¹ • v ∈ posVecs := by
    intro v hv
    have hu : w⁻¹ • v ∈ vecs := smul_mem_vecs (inv_mem hw) hv.1
    rcases mem_posVecs_or_neg hu with h | h
    · exact h
    · have := hpos _ h
      rw [smul_neg, smul_inv_smul] at this
      exact absurd this (not_neg_mem_posVecs hv)
  have hsimple : ∀ i, ∃ j, w • simpleVec i = simpleVec j := by
    intro i
    have hwi := hpos _ (simpleVec_mem_posVecs i)
    rcases decomp_check _ (mem_posVecs_iff.1 hwi) with ⟨j, hj⟩ | ⟨a, ha, b, hb, hab⟩
    · exact ⟨j, hj⟩
    · exfalso
      have ha' := hinv a (mem_posVecs_iff.2 ha)
      have hb' := hinv b (mem_posVecs_iff.2 hb)
      have e : simpleVec i = w⁻¹ • a + w⁻¹ • b := by rw [← smul_add, ← hab, inv_smul_smul]
      exact indec_check i _ (mem_posVecs_iff.1 ha') _ (mem_posVecs_iff.1 hb') e
  choose σ hσ using hsimple
  have hg : ∀ i j, iform (simpleVec (σ i)) (simpleVec (σ j)) = iform (simpleVec i) (simpleVec j) :=
    fun i j => by rw [← hσ, ← hσ, iform_smul]
  have h3 : σ 3 = 3 := gram_check3 _ (by rw [hg]; decide +kernel)
  have h2 : σ 2 = 2 := gram_check2 _ (by rw [← h3, hg]; decide +kernel)
  have h1 : σ 1 = 1 := gram_check1 _ (by rw [← h2, hg]; decide +kernel)
    (by rw [← h3, hg]; decide +kernel)
  have h0 : σ 0 = 0 := gram_check0 _ (by rw [← h1, hg]; decide +kernel)
    (by rw [← h2, hg]; decide +kernel)
  have hfixΔ : ∀ i, w • simpleVec i = simpleVec i := by
    intro i
    rw [hσ]
    fin_cases i
    · exact congrArg simpleVec h0
    · exact congrArg simpleVec h1
    · exact congrArg simpleVec h2
    · exact congrArg simpleVec h3
  have hf : ∀ a, w • TwistTag.E6.orbitSum a = TwistTag.E6.orbitSum a := by
    intro a
    refine smul_right_injective E6Vec (two_ne_zero : (2 : ℤ) ≠ 0) ?_
    change (2 : ℤ) • (w • TwistTag.E6.orbitSum a) = (2 : ℤ) • TwistTag.E6.orbitSum a
    rw [← smul_comm, two_smul_orbitSum_check, Finset.smul_sum]
    simp only [smul_comm w (_ : ℤ), hfixΔ]
  apply eq_one_of_forall_smul_fixedLattice TwistTag.E6 hw.1
  intro x hx
  obtain ⟨u, rfl⟩ := TwistTag.E6.exists_foldMap_eq hx
  rw [TwistTag.foldMap_apply, Finset.smul_sum]
  simp only [smul_comm w (u _), hf]

theorem eq_one_of_invFinset_eq_empty
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup)
    (h : invFinset w = ∅) : w = 1 := by
  refine eq_one_of_forall_pos hw fun v hv => ?_
  rcases mem_posVecs_or_neg (smul_mem_vecs hw hv.1) with h' | h'
  · exact h'
  · have : v ∈ invFinset w := Finset.mem_filter.2 ⟨mem_posFinset.2 hv, mem_posFinset.2 h'⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty v)

theorem smul_mem_posVecs_of_simple
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup)
    (h : ∀ i, w • simpleVec i ∈ posVecs) {v : E6Vec} (hv : v ∈ posVecs) : w • v ∈ posVecs := by
  obtain ⟨e, hsign⟩ := coeffs_spec hv.1
  have hc : ∀ i, 0 ≤ coeffs v i := by
    rcases hsign with ⟨-, hc⟩ | ⟨hneg, -⟩
    · exact hc
    · exact absurd hv.2 (by linarith)
  have hwv := smul_mem_vecs hw hv.1
  refine ⟨hwv, lt_of_le_of_ne ?_ (height_ne_zero_of_mem_vecs hwv).symm⟩
  rw [e, Finset.smul_sum, height_finset_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [smul_comm, height_zsmul]
  exact mul_nonneg (hc i) (h i).2.le

theorem exists_neg_simple
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup)
    (hne : invFinset w ≠ ∅) : ∃ i, -(w • simpleVec i) ∈ posVecs := by
  by_contra hn
  simp only [not_exists] at hn
  have hpos : ∀ i, w • simpleVec i ∈ posVecs := fun i =>
    (mem_posVecs_or_neg (smul_mem_vecs hw (simpleVec_mem_posVecs i).1)).resolve_right (hn i)
  refine hne (Finset.filter_false_of_mem fun v hv => ?_)
  exact not_neg_mem_posVecs (smul_mem_posVecs_of_simple hw hpos (mem_posFinset.1 hv)) ∘
    mem_posFinset.1

theorem exists_word
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ parityGroup) :
    ∃ l : List (Fin 4), l.length ≤ (invFinset w).card ∧ (l.map gen).prod = w := by
  induction h : (invFinset w).card using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h0 : invFinset w = ∅
    · refine ⟨[], Nat.zero_le _, ?_⟩
      rw [List.map_nil, List.prod_nil, eq_one_of_invFinset_eq_empty hw h0]
    · obtain ⟨i, hi⟩ := exists_neg_simple hw h0
      have hwi : w * gen i ∈ parityGroup := mul_mem hw (gen_mem_parityGroup i)
      have hc := (card_invFinset_mul_gen (fun v hv => smul_mem_vecs hw hv) i).1 hi
      obtain ⟨l, hl, hprod⟩ := ih _ (by omega) hwi rfl
      refine ⟨l ++ [i], by rw [List.length_append, List.length_singleton]; omega, ?_⟩
      rw [List.map_append, List.prod_append, hprod, List.map_singleton, List.prod_singleton,
        mul_assoc, gen_mul_gen, mul_one]

theorem parityGroup_le_weylGroup :
    parityGroup ≤ weylGroup := fun _ hw => by
  obtain ⟨l, -, rfl⟩ := exists_word hw
  exact prod_mem_weylGroup l

theorem weylGroup_eq_parityGroup :
    weylGroup = parityGroup :=
  le_antisymm weylGroup_le_parityGroup parityGroup_le_weylGroup

theorem card_invFinset_le
    (l : List (Fin 4)) : (invFinset (l.map gen).prod).card ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [invFinset_one]
  | append_singleton l i ih =>
    have hw : (l.map gen).prod ∈ parityGroup := weylGroup_le_parityGroup (prod_mem_weylGroup l)
    rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
      List.length_append, List.length_singleton]
    exact (card_invFinset_mul_gen_le (fun v hv => smul_mem_vecs hw hv) i).trans (by omega)

theorem wordLength_eq
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) :
    wordLength w = (invFinset w).card := by
  obtain ⟨l, hl, hprod⟩ := exists_word (weylGroup_le_parityGroup hw)
  unfold wordLength
  refine le_antisymm (le_trans (Nat.sInf_le ⟨l, rfl, hprod⟩) hl) (le_csInf ⟨_, l, rfl, hprod⟩ ?_)
  rintro n ⟨l', rfl, hl'⟩
  rw [← hl']
  exact card_invFinset_le l'

theorem wordLength_inv
    (w : WeylGroup TwistTag.E6.tag) : wordLength w⁻¹ = wordLength w := by
  have key : ∀ w : WeylGroup TwistTag.E6.tag, ∀ n,
      (∃ l : List (Fin 4), l.length = n ∧ (l.map gen).prod = w) →
        ∃ l : List (Fin 4), l.length = n ∧ (l.map gen).prod = w⁻¹ := by
    rintro w n ⟨l, rfl, rfl⟩
    refine ⟨l.reverse, List.length_reverse, ?_⟩
    rw [List.prod_inv_reverse, List.map_map, List.map_reverse]
    congr 2
    exact List.map_congr_left fun i _ => (gen_inv i).symm
  unfold wordLength
  congr 1
  ext n
  exact ⟨fun h => by simpa using key _ n h, key w n⟩

theorem wordLength_mul_gen
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) (i : Fin 4) :
    wordLength (w * gen i) = wordLength w - 1 ↔ height (w • simpleVec i) < 0 := by
  have hwp := weylGroup_le_parityGroup hw
  rw [wordLength_eq hw, wordLength_eq (mul_mem hw (Subgroup.subset_closure ⟨i, rfl⟩))]
  have hv : w • simpleVec i ∈ vecs := smul_mem_vecs hwp (simpleVec_mem_posVecs i).1
  obtain ⟨h1, h2⟩ := card_invFinset_mul_gen (fun v hv => smul_mem_vecs hwp hv) i
  rcases lt_or_gt_of_ne (height_ne_zero_of_mem_vecs hv) with h | h
  · have := h1 ((neg_mem_posVecs_iff hv).2 h)
    exact ⟨fun _ => h, fun _ => by omega⟩
  · have := h2 ⟨hv, h⟩
    exact ⟨fun e => by omega, fun e => absurd e (by linarith)⟩

theorem wordLength_gen_mul
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) (i : Fin 4) :
    wordLength (gen i * w) = wordLength w - 1 ↔ height (w⁻¹ • simpleVec i) < 0 := by
  rw [← wordLength_inv (gen i * w), mul_inv_rev, gen_inv, ← wordLength_inv w]
  exact wordLength_mul_gen (inv_mem hw) i

theorem wordLength_eq_ncard
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) :
    wordLength w = {v | v ∈ posVecs ∧ w • v ∈ -posVecs}.ncard := by
  rw [wordLength_eq hw, ← coe_invFinset, Set.ncard_coe_finset]

@[expose] def longestWord : List (Fin 4) :=
  [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]

theorem longest_check : ∀ v ∈ vecList, wordAct longestWord v = -v := by
  decide +kernel

theorem longest_smul
    {v : E6Vec} (hv : v ∈ vecs) : (longestWord.map gen).prod • v = -v := by
  rw [prod_smul]
  exact longest_check v (mem_vecs_iff.1 hv)

theorem longest_mem
    : (longestWord.map gen).prod ∈ weylGroup :=
  prod_mem_weylGroup _

theorem invFinset_longest :
    invFinset (longestWord.map gen).prod = posFinset := by
  refine Finset.filter_true_of_mem fun v hv => ?_
  rw [longest_smul (mem_posFinset.1 hv).1, neg_neg]
  exact hv

theorem wordLength_longest :
    wordLength (longestWord.map gen).prod = 16 := by
  rw [wordLength_eq longest_mem, invFinset_longest, card_posFinset]

theorem longest_mul_self
    : (longestWord.map gen).prod * (longestWord.map gen).prod = 1 := by
  refine eq_one_of_forall_pos (weylGroup_le_parityGroup (mul_mem longest_mem longest_mem))
    fun v hv => ?_
  rw [mul_smul, longest_smul hv.1, smul_neg, longest_smul hv.1, neg_neg]
  exact hv

theorem eq_longest
    {w : WeylGroup TwistTag.E6.tag} (hw : w ∈ weylGroup) (h : wordLength w = 16) :
    w = (longestWord.map gen).prod := by
  rw [wordLength_eq hw, ← card_posFinset] at h
  have hinv : invFinset w = posFinset :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h.ge
  have hneg : ∀ v ∈ posVecs, -(w • v) ∈ posVecs := fun v hv => by
    have : v ∈ invFinset w := by rw [hinv]; exact mem_posFinset.2 hv
    exact mem_posFinset.1 (Finset.mem_filter.1 this).2
  have h1 : (longestWord.map gen).prod * w = 1 := by
    refine eq_one_of_forall_pos (weylGroup_le_parityGroup (mul_mem longest_mem hw))
      fun v hv => ?_
    rw [mul_smul, longest_smul (smul_mem_vecs (weylGroup_le_parityGroup hw) hv.1)]
    exact hneg v hv
  calc w = (longestWord.map gen).prod * ((longestWord.map gen).prod * w) := by
        rw [← mul_assoc, longest_mul_self, one_mul]
    _ = (longestWord.map gen).prod := by rw [h1, mul_one]

@[expose] def orbitWords4 : List (List (Fin 4)) :=
  [[1, 2, 3, 2, 1, 0], [2, 3, 2, 1, 0], [3, 2, 1, 0], [2, 1, 0], [1, 0], [2, 3, 2, 0, 1, 0],
    [3, 2, 0, 1, 0], [2, 0, 1, 0], [0, 1, 0], [0], [3, 1, 2, 0, 1, 0], [1, 2, 0, 1, 0],
    [1, 2, 0, 1], [3, 1, 2, 0, 1], [], [0, 1], [2, 0, 1], [3, 2, 0, 1], [2, 3, 2, 0, 1], [1],
    [2, 1], [3, 2, 1], [2, 3, 2, 1], [1, 2, 3, 2, 1]]

@[expose] def orbitWords8 : List (List (Fin 4)) :=
  [[0, 1, 2, 3], [1, 2, 3], [2, 3], [3], [], [2], [1, 2], [0, 1, 2]]

theorem orbit_check : ∀ v ∈ vecList,
    (iform v v = 4 → ∃ l ∈ orbitWords4, wordAct l (simpleVec 0) = v) ∧
      (iform v v = 8 → ∃ l ∈ orbitWords8, wordAct l (simpleVec 3) = v) := by
  decide +kernel

theorem norm_check : ∀ v ∈ vecList, iform v v = 4 ∨ iform v v = 8 := by
  decide +kernel

theorem orbit_eq
    {s : Fin 4} {words : List (List (Fin 4))} {m : ℤ}
    (hs : iform (simpleVec s) (simpleVec s) = m)
    (hwords : ∀ v ∈ vecList, iform v v = m → ∃ l ∈ words, wordAct l (simpleVec s) = v) :
    {v | ∃ w ∈ weylGroup, w • simpleVec s = v} = {v | v ∈ vecs ∧ iform v v = m} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨smul_mem_vecs (weylGroup_le_parityGroup hw) (simpleVec_mem_posVecs s).1,
      by rw [iform_smul, hs]⟩
  · rintro ⟨hv, hm⟩
    obtain ⟨l, -, hl⟩ := hwords v (mem_vecs_iff.1 hv) hm
    exact ⟨_, prod_mem_weylGroup l, by rw [prod_smul, hl]⟩

theorem ncard_norm {m : ℤ} :
    {v | v ∈ vecs ∧ iform v v = m}.ncard = (vecList.filter fun v => iform v v = m).length := by
  have e : {v | v ∈ vecs ∧ iform v v = m} = {v | v ∈ vecList.filter fun v => iform v v = m} := by
    ext v
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, mem_vecs_iff, List.mem_filter, decide_eq_true_eq]
  rw [e, ncard_setOf_mem (vecList_nodup.filter _)]

end CFSG.LieType.Chevalley.E6SignedGraph
