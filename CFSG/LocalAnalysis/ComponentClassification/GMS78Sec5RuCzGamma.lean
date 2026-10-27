module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzModel
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmNA

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj
  CFSG.Sporadic.Bridge.SurjD.Native

theorem c2Ru_eq_one
    {v : List (ℕ × Bool)}
    (hv : v ∈ c2RuRels) : wordProd pi7L v = 1 := by
  refine pi7ToJ_bijective.1 ?_
  rw [map_one, map_wordProd, wordProd_congr (y := pi7Img) fun l hl =>
    pi7ToJ_pi7L ((cz_gamma v hv).1 l hl)]
  exact (cz_gamma v hv).2

theorem wordProd_gSubst {G : Type*} [Group G] (x : ℕ → G) (r : List (ℕ × Bool)) :
    wordProd x (gSubst r) = wordProd (fun p => wordProd x (gWord p)) r := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    unfold gSubst at ih ⊢
    rw [List.flatMap_cons, wordProd_append, ih, wordProd_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact wordProd_invNatWord x _
    · simp only [↓reduceIte]

theorem eq_of_cons_inv {x : ℕ} {v : List (ℕ × Bool)}
    (h : wordProd pi7L ((x, false) :: v) = 1) : pi7L x = wordProd pi7L v := by
  rw [wordProd_cons] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  exact inv_mul_eq_one.1 h

theorem eq_of_inv_append {u v : List (ℕ × Bool)}
    (h : wordProd pi7L (invNatWord u ++ v) = 1) : wordProd pi7L u = wordProd pi7L v := by
  rw [wordProd_append, wordProd_invNatWord] at h
  exact inv_mul_eq_one.1 h

theorem ruSub2_length : ruSub2.length = 6 := by decide

@[expose] noncomputable def p2Gen (i : ℕ) : RuP2 :=
  if h : i < 5 then PresentedGroup.of ⟨i, by rw [ruSub2_length]; omega⟩
  else if i = 6 then PresentedGroup.of ⟨5, by rw [ruSub2_length]; omega⟩ else 1

@[expose] def isM2 (i : ℕ) : Prop := i < 5 ∨ i = 6

theorem ruSub2_get_lt (j : Fin ruSub2.length) (h : j.val < 5) : (ruSub2.get j).val = j.val := by
  revert j
  decide

theorem ruSub2_get_five (j : Fin ruSub2.length) (h : j.val = 5) : (ruSub2.get j).val = 6 := by
  revert j
  decide

theorem p2Gen_of_lt {i : ℕ} (hi : i < 5) :
    p2Gen i = PresentedGroup.of ⟨i, by rw [ruSub2_length]; omega⟩ := by
  unfold p2Gen
  simp only [hi, ↓reduceDIte]

theorem p2Gen_six : p2Gen 6 = PresentedGroup.of ⟨5, by rw [ruSub2_length]; omega⟩ := by
  unfold p2Gen
  simp only [show ¬ (6 : ℕ) < 5 by norm_num, ↓reduceDIte, ↓reduceIte]

theorem ruP2ToPi7_p2Gen {i : ℕ} (hi : isM2 i) : ruP2ToPi7 (p2Gen i) = pi7L i := by
  rcases hi with hi | rfl
  · rw [p2Gen_of_lt hi, ruP2ToPi7_of, pi7L_of_lt (by omega)]
    exact congrArg PresentedGroup.of (Fin.ext (ruSub2_get_lt _ hi))
  · rw [p2Gen_six, ruP2ToPi7_of, pi7L_of_lt (by norm_num)]
    exact congrArg PresentedGroup.of (Fin.ext (ruSub2_get_five _ rfl))

theorem ruP2ToPi7_wordProd {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, isM2 l.1) :
    ruP2ToPi7 (wordProd p2Gen w) = wordProd pi7L w := by
  rw [map_wordProd]
  exact wordProd_congr fun l hl => ruP2ToPi7_p2Gen (hw l hl)

theorem gWord_isM2 : ∀ p < 7, ∀ l ∈ gWord p, isM2 l.1 := by
  unfold isM2
  decide

@[expose] noncomputable def gP2 (p : Fin 7) : RuP2 := wordProd p2Gen (gWord p.val)

theorem ruP2ToPi7_gP2 (p : Fin 7) : ruP2ToPi7 (gP2 p) = wordProd pi7L (gWord p.val) :=
  ruP2ToPi7_wordProd (gWord_isM2 p.val p.2)

theorem gP2_rel :
    ∀ r ∈ pi7Rels, (renumber ruSub2 r).isSome → FreeGroup.lift gP2 (FreeGroup.mk r) = 1 := by
  intro r hr hs
  refine ruP2ToPi7_injective ?_
  have e : ruP2ToPi7.comp (FreeGroup.lift gP2) =
      FreeGroup.lift fun p : Fin 7 => wordProd pi7L (gWord p.val) :=
    FreeGroup.ext_hom _ _ fun p => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, ruP2ToPi7_gP2]
  rw [map_one, ← MonoidHom.comp_apply, e, lift_mk_eq_wordProd (fun p => wordProd pi7L (gWord p)),
    ← wordProd_gSubst]
  refine c2Ru_eq_one ?_
  unfold c2RuRels
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_)))))
  exact List.mem_map.2 ⟨r, List.mem_filter.2 ⟨hr, hs⟩, rfl⟩

@[expose] noncomputable def gammaP2 :
    RuP2 →* RuP2 :=
  PresentedGroup.toGroup (lift_ruRels2 gP2 gP2_rel)

theorem gammaP2_p2Gen
    {i : ℕ} (hi : isM2 i) :
    gammaP2 (p2Gen i) = wordProd p2Gen (gWord i) := by
  rcases hi with hi | rfl
  · rw [p2Gen_of_lt hi, gammaP2, PresentedGroup.toGroup.of]
    show wordProd p2Gen (gWord (ruSub2.get _).val) = _
    rw [ruSub2_get_lt _ hi]
  · rw [p2Gen_six, gammaP2, PresentedGroup.toGroup.of]
    show wordProd p2Gen (gWord (ruSub2.get _).val) = _
    rw [ruSub2_get_five _ rfl]

theorem ruP2ToPi7_gammaP2
    {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, isM2 l.1) :
    ruP2ToPi7 (gammaP2 (wordProd p2Gen w)) = wordProd pi7L (gSubst w) := by
  rw [map_wordProd, wordProd_congr (y := fun i => wordProd p2Gen (gWord i)) fun l hl =>
    gammaP2_p2Gen (hw l hl), map_wordProd, wordProd_gSubst]
  refine wordProd_congr fun l hl => ?_
  have h7 : l.1 < 7 := by rcases hw l hl with h | h <;> omega
  exact ruP2ToPi7_wordProd (gWord_isM2 l.1 h7)

theorem m2Word_isM2 : ∀ k < 6, ∀ l ∈ m2Word (c2InvCodes.getD k []), isM2 l.1 := by
  unfold isM2
  decide

theorem m2Letter_isM2 : ∀ k < 6, isM2 (m2Letter k) := by
  unfold isM2
  decide

theorem gammaP2_surjective :
    Function.Surjective gammaP2 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  have hj : j.val < 6 := lt_of_lt_of_eq j.2 ruSub2_length
  refine ⟨wordProd p2Gen (m2Word (c2InvCodes.getD j.val [])), ruP2ToPi7_injective ?_⟩
  rw [ruP2ToPi7_gammaP2 (m2Word_isM2 j.val hj), ruP2ToPi7_of]
  have h := c2Ru_eq_one (v := (m2Letter j.val, false) :: gSubst (m2Word (c2InvCodes.getD j.val [])))
    (by
      unfold c2RuRels
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))))
      exact List.mem_map.2 ⟨j.val, List.mem_range.2 hj, rfl⟩)
  rw [← eq_of_cons_inv h]
  have key : ∀ j : Fin ruSub2.length, (ruSub2.get j).val = m2Letter j.val := by decide
  have h7 : m2Letter j.val < 7 := by
    rcases m2Letter_isM2 j.val hj with h | h <;> omega
  rw [pi7L_of_lt h7]
  exact congrArg PresentedGroup.of (Fin.ext (key j).symm)

@[expose] noncomputable def gammaP2Equiv :
    RuP2 ≃* RuP2 :=
  MulEquiv.ofBijective gammaP2 (by
    have := card_ruP2_le.1
    exact ⟨Finite.injective_iff_surjective.2 gammaP2_surjective, gammaP2_surjective⟩)

@[expose] noncomputable def ruP2EquivM2 :
    RuP2 ≃* ruM2 :=
  (MonoidHom.ofInjective ruP2ToPi7_injective).trans (MulEquiv.subgroupCongr range_ruP2ToPi7)

theorem coe_ruP2EquivM2
    (x : RuP2) :
    ((ruP2EquivM2 x : ruM2) : Pi7) = ruP2ToPi7 x :=
  rfl

@[expose] noncomputable def czGamma :
    ruM2 ≃* ruM2 :=
  (ruP2EquivM2.symm.trans gammaP2Equiv).trans ruP2EquivM2

theorem wordProd_mem_ruM2 {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, isM2 l.1) :
    wordProd pi7L w ∈ ruM2 := by
  refine wordProd_mem_letterSub fun e he => ⟨by rcases hw e he with h | h <;> omega, ?_⟩
  have := hw e he
  unfold isM2 at this
  simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  omega

theorem czGamma_wordProd
    {w : List (ℕ × Bool)} (hw : ∀ l ∈ w, isM2 l.1) :
    ((czGamma ⟨wordProd pi7L w, wordProd_mem_ruM2 hw⟩ : ruM2) : Pi7) =
      wordProd pi7L (gSubst w) := by
  have h1 : ruP2EquivM2.symm ⟨wordProd pi7L w, wordProd_mem_ruM2 hw⟩ = wordProd p2Gen w := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (ruP2ToPi7_wordProd hw).symm
  rw [czGamma, MulEquiv.trans_apply, MulEquiv.trans_apply, h1, coe_ruP2EquivM2]
  exact ruP2ToPi7_gammaP2 hw

theorem l10Word_isM2 : ∀ i < 9, ∀ l ∈ l10Word i, isM2 l.1 := by
  unfold isM2
  decide

theorem czImg_mem_ruM2 {i : ℕ} (hi : i < 9) : czImg i ∈ ruM2 :=
  wordProd_mem_ruM2 (l10Word_isM2 i hi)

theorem czGamma_q :
    ((czGamma ⟨czImg 6, czImg_mem_ruM2 (by norm_num)⟩ : ruM2) : Pi7) = czImg 6 := by
  rw [show (⟨czImg 6, czImg_mem_ruM2 (by norm_num)⟩ : ruM2) =
    ⟨wordProd pi7L (l10Word 6), wordProd_mem_ruM2 (l10Word_isM2 6 (by norm_num))⟩ from rfl,
    czGamma_wordProd (l10Word_isM2 6 (by norm_num))]
  refine (eq_of_inv_append (c2Ru_eq_one ?_)).symm
  unfold c2RuRels
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_singleton_self _))))

theorem czGamma_triv
    {y : ℕ} (hy : y < 9) :
    ((czGamma ⟨czImg y, czImg_mem_ruM2 hy⟩ : ruM2) : Pi7) =
      wordProd czImg (natWord (c2TrivCodes.getD y [])) * czImg y := by
  rw [show (⟨czImg y, czImg_mem_ruM2 hy⟩ : ruM2) =
    ⟨wordProd pi7L (l10Word y), wordProd_mem_ruM2 (l10Word_isM2 y hy)⟩ from rfl,
    czGamma_wordProd (l10Word_isM2 y hy)]
  have h := eq_of_inv_append (c2Ru_eq_one (v := invNatWord (substWord (natWord
    (c2TrivCodes.getD y [])) ++ l10Word y) ++ gSubst (l10Word y)) (by
      unfold c2RuRels
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.2 ⟨y, List.mem_range.2 hy, rfl⟩))))
  rw [← h, wordProd_append, wordProd_substWord]
  rfl

theorem czGamma_j
    {i : ℕ} (hi : i < 6) :
    ((czGamma ⟨czImg i, czImg_mem_ruM2 (by omega)⟩ : ruM2) : Pi7) =
      wordProd czImg (natWord (c2JCodes.getD i [])) := by
  rw [show (⟨czImg i, czImg_mem_ruM2 (by omega)⟩ : ruM2) =
    ⟨wordProd pi7L (l10Word i), wordProd_mem_ruM2 (l10Word_isM2 i (by omega))⟩ from rfl,
    czGamma_wordProd (l10Word_isM2 i (by omega))]
  have h := eq_of_inv_append (c2Ru_eq_one (v := invNatWord (substWord (natWord
    (c2JCodes.getD i []))) ++ gSubst (l10Word i)) (by
      unfold c2RuRels
      exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)))
  rw [← h, wordProd_substWord]
  rfl

theorem ruA0Words_isM2 : ∀ a ∈ ruA0Words, ∀ l ∈ a.map (fun l => (l.1.val, l.2)), isM2 l.1 := by
  unfold isM2
  decide

theorem czGamma_A0basis
    {a : List (Fin 7 × Bool)} (ha : a ∈ ruA0Words) :
    ((czGamma ⟨wordProd pi7L (a.map fun l => (l.1.val, l.2)),
      wordProd_mem_ruM2 (ruA0Words_isM2 a ha)⟩ : ruM2) : Pi7) =
      wordProd pi7L (a.map fun l => (l.1.val, l.2)) := by
  rw [czGamma_wordProd (ruA0Words_isM2 a ha)]
  refine (eq_of_inv_append (c2Ru_eq_one ?_)).symm
  unfold c2RuRels
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩)))))

theorem pi7Word_eq_wordProd (w : List (Fin 7 × Bool)) :
    pi7Word w = wordProd pi7L (w.map fun l => (l.1.val, l.2)) := by
  rw [pi7Word_eq_lift, ← lift_mk_eq_wordProd]
  have e : (fun i : Fin 7 => pi7L i.val) = fun i => (PresentedGroup.of i : Pi7) :=
    funext fun i => pi7L_of_lt i.2
  rw [e]

theorem ruA0_le_ruM2 : ruA0 ≤ ruM2 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, rfl⟩
  rw [pi7Word_eq_wordProd]
  exact wordProd_mem_ruM2 (ruA0Words_isM2 a ha)

theorem czGamma_fix_ruA0
    (m : ruM2) (hm : (m : Pi7) ∈ ruA0) : czGamma m = m := by
  set K : Subgroup ruM2 := MonoidHom.eqLocus czGamma.toMonoidHom (MonoidHom.id ruM2)
  have hle : ruA0 ≤ K.map ruM2.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨⟨pi7Word a, ruA0_le_ruM2 (Subgroup.subset_closure ⟨a, ha, rfl⟩)⟩, ?_, rfl⟩
    show czGamma _ = _
    apply Subtype.ext
    have e : (⟨pi7Word a, ruA0_le_ruM2 (Subgroup.subset_closure ⟨a, ha, rfl⟩)⟩ : ruM2) =
        ⟨wordProd pi7L (a.map fun l => (l.1.val, l.2)),
          wordProd_mem_ruM2 (ruA0Words_isM2 a ha)⟩ :=
      Subtype.ext (pi7Word_eq_wordProd a)
    rw [e]
    exact czGamma_A0basis ha
  obtain ⟨k, hk, hkm⟩ := hle hm
  rw [show m = k from Subtype.ext hkm.symm]
  exact hk

theorem czGamma_z0
    (m : ruM2) (hm : (m : Pi7) = ruZ0) : czGamma m = m :=
  czGamma_fix_ruA0 m (hm ▸ Subgroup.subset_closure ⟨ruZ0Word, by decide, rfl⟩)

theorem ruM12_eq_closure :
    ruM12 = Subgroup.closure (Set.range fun k : Fin 9 => czImg k.val) := by
  rw [← range_p12ToPi7, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of,
    MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.val, lt_of_lt_of_eq j.2 sub9_length⟩, (p12ToPi7_of j).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k.val, lt_of_lt_of_eq k.2 sub9_length.symm⟩, p12ToPi7_of _⟩

end CFSG.ComponentClassification.GMS78.RuCz
