module

public import Certificates.Certificate550871
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain
public import Certificates.Certificate550872
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2E64
public import CFSG.ClassicalInvolution.Q3.E64Ker.ModelCard

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P

open CFSG.CosetTable CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def memSet (k : Fin 14) : Finset (Fin 7) := (fanoLines.getD (k.val / 2) ∅)ᶜ

@[expose] def memB (k : Fin 14) : Bool := k.val % 2 == 0

@[expose] def memIdx (k : Fin 14) : Finset (Fin 7) × Bool := (memSet k, memB k)

theorem memSet_card (k : Fin 14) : (memSet k).card = 4 := by
  revert k
  decide +kernel

theorem memSet_mem (k : Fin 14) : memSet k ∈ e64Sets := by
  refine ⟨fanoLines.getD (k.val / 2) ∅, ?_, rfl⟩
  revert k
  decide +kernel

@[expose] def modelGen (g : Fin 28) : AEQ 7 := mkQ 7 (genW g)

@[expose] def memOf (g : Fin 28) : Fin 14 := ⟨g.val / 2, by omega⟩

theorem memOf_gIdx (k : Fin 14) {c : Nat} (hc : c < 2) : memOf (gIdx k.val c) = k := by
  apply Fin.ext
  simp only [memOf, gIdx, Fin.val_ofNat]
  omega

@[expose] def locQ : Nat → Wr 4
  | 0 => iQ
  | 1 => jQ
  | 2 => iQStar
  | _ => jQStar

theorem embed_vec4_swap (ι : Fin 4 ↪ Fin 7) (p q a b c d : Fin 4) :
    embed ι ⟨vec4 [p, q], Equiv.swap a b * Equiv.swap c d⟩ =
      wr22 (ι p) (ι q) (ι a) (ι b) (ι c) (ι d) := by
  refine Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · rw [embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedVec_apply]
      simp only [wr22, vec4, List.mem_cons, List.mem_nil_iff, or_false,
        EmbeddingLike.apply_eq_iff_eq]
    · rw [embedVec_of_not_mem ι _ hx]
      have hp : x ≠ ι p := fun h => hx ⟨p, h.symm⟩
      have hq : x ≠ ι q := fun h => hx ⟨q, h.symm⟩
      simp only [wr22, hp, hq, or_self, if_false]
  · rw [embed_perm]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      rw [embedPerm_apply]
      simp only [wr22, Equiv.Perm.mul_apply, ι.injective.swap_apply]
    · rw [embedPerm_of_not_mem ι _ hx]
      have hne : ∀ y, x ≠ ι y := fun y h => hx ⟨y, h.symm⟩
      simp only [wr22, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (hne c) (hne d),
        Equiv.swap_apply_of_ne_of_ne (hne a) (hne b)]

theorem embed_locQ (ι : Fin 4 ↪ Fin 7) (r : Nat) : embed ι (locQ r) = locW (fun i => ι i) r := by
  match r with
  | 0 => exact embed_vec4_swap ι 0 2 0 1 2 3
  | 1 => exact embed_vec4_swap ι 0 3 0 2 1 3
  | 2 => exact embed_vec4_swap ι 0 3 0 1 2 3
  | _ + 3 => exact embed_vec4_swap ι 0 1 0 2 1 3

theorem cplF_mem : ∀ g : Fin 28, ∀ i : Fin 4,
    cplF (Fin.ofNat 7 (g.val / 4)) i ∈ memSet (memOf g) := by
  decide +kernel

theorem cplF_strictMono (ℓ : Fin 7) : StrictMono (cplF ℓ) := by
  have h : ∀ ℓ : Fin 7, ∀ i j : Fin 4, i < j → cplF ℓ i < cplF ℓ j := by decide +kernel
  exact fun i j hij => h ℓ i j hij

theorem emb_memOf (g : Fin 28) (i : Fin 4) :
    emb (memSet (memOf g)) (memSet_card _) i = cplF (Fin.ofNat 7 (g.val / 4)) i :=
  (congrFun (Finset.orderEmbOfFin_unique (memSet_card (memOf g)) (cplF_mem g)
    (cplF_strictMono _)) i).symm

theorem genW_eq_embed (g : Fin 28) :
    genW g = embed (emb (memSet (memOf g)) (memSet_card _)) (locQ (g.val % 4)) := by
  rw [embed_locQ]
  have h : (fun i => emb (memSet (memOf g)) (memSet_card _) i) =
      cplF (Fin.ofNat 7 (g.val / 4)) := funext (emb_memOf g)
  rw [h, genW]

theorem locQ_mem : ∀ g : Fin 28,
    locQ (g.val % 4) ∈ (bif memB (memOf g) then kList else kStarList) := by
  decide +kernel

theorem genW_mem_memAt (g : Fin 28) :
    genW g ∈ memAt (memSet (memOf g)) (memSet_card _) (memB (memOf g)) := by
  rw [genW_eq_embed g]
  have h := locQ_mem g
  unfold memAt
  cases hb : memB (memOf g) <;> rw [hb] at h
  · exact ⟨_, h, rfl⟩
  · exact ⟨_, h, rfl⟩

theorem modelGen_mem_memBar (g : Fin 28) :
    modelGen g ∈ memBar (memSet (memOf g)) (memSet_card _) (memB (memOf g)) :=
  ⟨genW g, genW_mem_memAt g, rfl⟩

theorem modelGen_mem (g : Fin 28) : modelGen g ∈ e64Sub :=
  TwinThinPf.memBar_le_e64 _ (memSet_mem _) (memSet_card _) _ (modelGen_mem_memBar g)

theorem closure_iQ_jQ : Subgroup.closure {iQ, jQ} = kQ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact (by decide +kernel : iQ ∈ kList)
    · exact (by decide +kernel : jQ ∈ kList)
  · intro a ha
    obtain ⟨q, rfl⟩ := kQHom_surj a ha
    have hi : iQ ∈ Subgroup.closure {iQ, jQ} := Subgroup.subset_closure (Set.mem_insert _ _)
    have hj : jQ ∈ Subgroup.closure {iQ, jQ} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    cases q with
    | a n => exact Subgroup.pow_mem _ hi _
    | xa n => exact Subgroup.mul_mem _ hj (Subgroup.pow_mem _ hi _)

theorem closure_iQStar_jQStar : Subgroup.closure {iQStar, jQStar} = kQStar := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact (by decide +kernel : iQStar ∈ kStarList)
    · exact (by decide +kernel : jQStar ∈ kStarList)
  · intro a ha
    obtain ⟨q, rfl⟩ := kQStarHom_surj a ha
    have hi : iQStar ∈ Subgroup.closure {iQStar, jQStar} :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hj : jQStar ∈ Subgroup.closure {iQStar, jQStar} :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    cases q with
    | a n => exact Subgroup.pow_mem _ hi _
    | xa n => exact Subgroup.mul_mem _ hj (Subgroup.pow_mem _ hi _)

theorem locQ_gIdx : ∀ k : Fin 14,
    locQ ((gIdx k.val 0).val % 4) = (bif memB k then iQ else iQStar) ∧
      locQ ((gIdx k.val 1).val % 4) = (bif memB k then jQ else jQStar) := by
  decide +kernel

theorem closure_genW_pair (k : Fin 14) :
    Subgroup.closure {genW (gIdx k.val 0), genW (gIdx k.val 1)} =
      memAt (memSet k) (memSet_card k) (memB k) := by
  have e0 := genW_eq_embed (gIdx k.val 0)
  have e1 := genW_eq_embed (gIdx k.val 1)
  rw [memOf_gIdx k (by norm_num)] at e0
  rw [memOf_gIdx k (by norm_num)] at e1
  obtain ⟨h0, h1⟩ := locQ_gIdx k
  rw [h0] at e0
  rw [h1] at e1
  rw [e0, e1, ← Set.image_pair, ← MonoidHom.map_closure]
  unfold memAt
  cases memB k
  · exact congrArg (Subgroup.map _) closure_iQStar_jQStar
  · exact congrArg (Subgroup.map _) closure_iQ_jQ

theorem closure_modelGen_pair (k : Fin 14) :
    Subgroup.closure {modelGen (gIdx k.val 0), modelGen (gIdx k.val 1)} =
      memBar (memSet k) (memSet_card k) (memB k) := by
  rw [memBar, ← closure_genW_pair, MonoidHom.map_closure, Set.image_pair]
  rfl

theorem genW_pow_four : ∀ g : Fin 28, genW g ^ 4 = 1 := by
  decide +kernel

theorem genW_sq_ne : ∀ g : Fin 28, genW g ^ 2 ≠ 1 ∧ genW g ^ 2 ≠ allOnes 7 := by
  decide +kernel

theorem orderOf_genW (g : Fin 28) : orderOf (genW g) = 4 := by
  have h4 : genW g ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 4 by norm_num, genW_pow_four]
  have h2 : ¬ genW g ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact (genW_sq_ne g).1
  exact (orderOf_eq_prime_pow h2 h4).trans (by norm_num)

theorem orderOf_modelGen (g : Fin 28) : orderOf (modelGen g) = 4 := by
  have h4 : modelGen g ^ 2 ^ (1 + 1) = 1 := by
    rw [modelGen, ← map_pow, show 2 ^ (1 + 1) = 4 by norm_num, genW_pow_four, map_one]
  have h2 : ¬ modelGen g ^ 2 ^ 1 = 1 := by
    rw [modelGen, ← map_pow, pow_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_piSub]
    rintro (h | h)
    · exact (genW_sq_ne g).1 h
    · exact (genW_sq_ne g).2 h
  exact (orderOf_eq_prime_pow h2 h4).trans (by norm_num)

theorem genW_zero : genW 0 = TwinThinPf.aW := by
  decide +kernel

theorem genW_one : genW 1 = TwinThinPf.bW := by
  decide +kernel

theorem genW_hW : genW 3 * genW 13 * genW 20 * genW 21 = TwinThinPf.hW := by
  decide +kernel

theorem closure_modelGen : Subgroup.closure (Set.range modelGen) = e64Sub := by
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun y hy => ?_
  · rintro _ ⟨g, rfl⟩
    exact modelGen_mem g
  · set C := Subgroup.closure (Set.range modelGen)
    have hmem : ∀ g, modelGen g ∈ C := fun g => Subgroup.subset_closure ⟨g, rfl⟩
    have hle : Subgroup.closure {z | z ∈ [TwinThinPf.aH, TwinThinPf.bH, TwinThinPf.hH]} ≤
        C.subgroupOf e64Sub := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_nil_iff, or_false] at hz
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      rcases hz with rfl | rfl | rfl
      · have e : ((TwinThinPf.aH : ↥e64Sub) : AEQ 7) = modelGen 0 := by
          rw [modelGen, genW_zero]
          rfl
        rw [e]
        exact hmem 0
      · have e : ((TwinThinPf.bH : ↥e64Sub) : AEQ 7) = modelGen 1 := by
          rw [modelGen, genW_one]
          rfl
        rw [e]
        exact hmem 1
      · have e : ((TwinThinPf.hH : ↥e64Sub) : AEQ 7) =
            modelGen 3 * modelGen 13 * modelGen 20 * modelGen 21 := by
          simp only [modelGen]
          rw [← map_mul, ← map_mul, ← map_mul, genW_hW]
          rfl
        rw [e]
        exact C.mul_mem (C.mul_mem (C.mul_mem (hmem 3) (hmem 13)) (hmem 20)) (hmem 21)
    exact hle (TwinThinPf.gen_e64 ⟨y, hy⟩)

section Model


theorem rowsCheck_holds : rowsCheck () = true := Certificates.certificate550872.1

theorem relModelCheck_holds : relModelCheck () = true := Certificates.certificate550872.2

theorem relVal_eq_one {r : List (Fin 28 × Bool)} (hr : r ∈ e64MemberRels) : relVal r = 1 := by
  have h := relModelCheck_holds
  simp only [relModelCheck, List.all_eq_true, decide_eq_true_eq] at h
  exact h r hr

theorem lift_genW_mk (r : List (Fin 28 × Bool)) :
    FreeGroup.lift genW (FreeGroup.mk r) = relVal r := by
  rw [FreeGroup.lift_mk, relVal]

theorem lift_modelGen (f : FreeGroup (Fin 28)) :
    FreeGroup.lift modelGen f = mkQ 7 (FreeGroup.lift genW f) := by
  have h : FreeGroup.lift modelGen = (mkQ 7).comp (FreeGroup.lift genW) :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, modelGen]
  rw [h, MonoidHom.comp_apply]

theorem lift_modelGen_rel {r : List (Fin 28 × Bool)} (hr : r ∈ e64MemberRels) :
    FreeGroup.lift modelGen (FreeGroup.mk r) = 1 := by
  rw [lift_modelGen, lift_genW_mk, relVal_eq_one hr, map_one]

theorem exists_conjRow {g k c : Nat} (hg : g < 28) (hk : k < 14) (hc : c < 2) :
    ∃ k' w, (g, k, c, k', w) ∈ conjRows ∧ k' < 14 ∧ ∀ l ∈ w, l < 2 := by
  have h := rowsCheck_holds
  simp only [rowsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  have hrow := h.2 (28 * g + 2 * k + c) (by omega)
  split at hrow
  · rename_i d hd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hrow
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hrow
    have hmem : d ∈ conjRows := List.mem_of_getElem? hd
    obtain ⟨d1, d2, d3, d4, d5⟩ := d
    simp only at h1 h2 h3 h4 h5
    obtain rfl : d1 = g := by omega
    obtain rfl : d2 = k := by omega
    obtain rfl : d3 = c := by omega
    exact ⟨d4, d5, hmem, h4, h5⟩
  · exact absurd hrow (by simp)

end Model

section Relations

variable {G : Type*} [Group G]

theorem lift_mk_conjRel (x : Fin 28 → G) (d : Nat × Nat × Nat × Nat × List Nat) :
    FreeGroup.lift x (FreeGroup.mk (conjRel d)) =
      x (Fin.ofNat 28 d.1) * x (gIdx d.2.1 d.2.2.1) * (x (Fin.ofNat 28 d.1))⁻¹ *
        ((d.2.2.2.2.map fun l => x (gIdx d.2.2.2.1 l)).prod)⁻¹ := by
  obtain ⟨g, k, c, k', w⟩ := d
  rw [FreeGroup.lift_mk, conjRel, List.map_append, List.prod_append, List.prod_inv_reverse]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cond_true, cond_false,
    mul_one, List.map_reverse, List.map_map, Function.comp_def, mul_assoc]

theorem rels_of {x : Fin 28 → G}
    (hq : ∀ k < 14, x (gIdx k 0) ^ 4 = 1 ∧ x (gIdx k 0) ^ 2 = x (gIdx k 1) ^ 2 ∧
      x (gIdx k 1) * x (gIdx k 0) * (x (gIdx k 1))⁻¹ = (x (gIdx k 0))⁻¹)
    (hc : ∀ d ∈ conjRows,
      x (Fin.ofNat 28 d.1) * x (gIdx d.2.1 d.2.2.1) * (x (Fin.ofNat 28 d.1))⁻¹ =
        (d.2.2.2.2.map fun l => x (gIdx d.2.2.2.1 l)).prod)
    (ht : ∀ ℓ < 7, x (gIdx (2 * ℓ) 0) ^ 2 = x (gIdx (2 * ℓ + 1) 0) ^ 2) :
    ∀ r ∈ e64MemberRels, FreeGroup.lift x (FreeGroup.mk r) = 1 := by
  intro r hr
  simp only [e64MemberRels, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_map] at hr
  rcases hr with (⟨k, hk, hr⟩ | ⟨d, hd, rfl⟩) | ⟨ℓ, hℓ, rfl⟩
  · obtain ⟨h4, h2, hji⟩ := hq k hk
    simp only [q8Rels, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      simp only [FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        cond_true, cond_false, mul_one]
    · have e : x (gIdx k 0) * (x (gIdx k 0) * (x (gIdx k 0) * x (gIdx k 0))) =
          x (gIdx k 0) ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, h4]
    · have e : x (gIdx k 0) * (x (gIdx k 0) * ((x (gIdx k 1))⁻¹ * (x (gIdx k 1))⁻¹)) =
          x (gIdx k 0) ^ 2 * (x (gIdx k 1) ^ 2)⁻¹ := by
        simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
      rw [e, h2, mul_inv_cancel]
    · have e : x (gIdx k 1) * (x (gIdx k 0) * ((x (gIdx k 1))⁻¹ * x (gIdx k 0))) =
          x (gIdx k 1) * x (gIdx k 0) * (x (gIdx k 1))⁻¹ * x (gIdx k 0) := by group
      rw [e, hji, inv_mul_cancel]
  · rw [lift_mk_conjRel, hc d hd, mul_inv_cancel]
  · simp only [twinRel, FreeGroup.lift_mk, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, cond_true, cond_false, mul_one]
    have e : x (gIdx (2 * ℓ) 0) * (x (gIdx (2 * ℓ) 0) *
        ((x (gIdx (2 * ℓ + 1) 0))⁻¹ * (x (gIdx (2 * ℓ + 1) 0))⁻¹)) =
          x (gIdx (2 * ℓ) 0) ^ 2 * (x (gIdx (2 * ℓ + 1) 0) ^ 2)⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
    rw [e, ht ℓ hℓ, mul_inv_cancel]

theorem conjRel_mem {d : Nat × Nat × Nat × Nat × List Nat} (hd : d ∈ conjRows) :
    conjRel d ∈ e64MemberRels :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hd))

theorem model_conj {d : Nat × Nat × Nat × Nat × List Nat}
    (hd : d ∈ conjRows) :
    modelGen (Fin.ofNat 28 d.1) * modelGen (gIdx d.2.1 d.2.2.1) *
        (modelGen (Fin.ofNat 28 d.1))⁻¹ =
      (d.2.2.2.2.map fun l => modelGen (gIdx d.2.2.2.1 l)).prod := by
  have h := lift_modelGen_rel (conjRel_mem hd)
  rw [lift_mk_conjRel] at h
  exact mul_inv_eq_one.mp h

end Relations

section Order


theorem e64Pres_enum1344 :
    (genSub {r : FreeGroup (Fin 28) | r ∈ (e64MemberRels ()).map FreeGroup.mk}
        (subsetOf 28 [0, 1])).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin 28) | r ∈ (e64MemberRels ()).map FreeGroup.mk}
        (subsetOf 28 [0, 1])).index ≤ 1344 :=
  Certificates.certificate550871.1

theorem e64Pres_enum8 :
    Finite (PG (subsetOf 28 [0, 1]).length (restrictWords (subsetOf 28 [0, 1]) (e64MemberRels ()))) ∧
      Nat.card (PG (subsetOf 28 [0, 1]).length
        (restrictWords (subsetOf 28 [0, 1]) (e64MemberRels ()))) ≤ 8 :=
  Certificates.certificate550871.2

theorem card_PG_e64Rels :
    Finite (PG 28 e64MemberRels) ∧ Nat.card (PG 28 e64MemberRels) ≤ 10752 := by
  obtain ⟨hf, h⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict (e64MemberRels ())
    (subsetOf 28 [0, 1]) e64Pres_enum1344 e64Pres_enum8
  exact ⟨hf, h.trans (by norm_num)⟩

variable {G : Type*} [Group G]

theorem exists_hom_of_rels (x : Fin 28 → G)
    (hx : ∀ r ∈ e64MemberRels, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    ∃ φ : PG 28 e64MemberRels →* G, φ.range = Subgroup.closure (Set.range x) ∧
      ∀ i, φ (PresentedGroup.of i) = x i := by
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 28) | r ∈ (e64MemberRels ()).map FreeGroup.mk},
      FreeGroup.lift x r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact hx w hw
  refine ⟨PresentedGroup.toGroup hrel, ?_, fun i => PresentedGroup.toGroup.of hrel⟩
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2
  funext i
  exact PresentedGroup.toGroup.of hrel

theorem finite_card_closure_of_rels (x : Fin 28 → G)
    (hx : ∀ r ∈ e64MemberRels, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    Finite (Subgroup.closure (Set.range x)) ∧
      Nat.card (Subgroup.closure (Set.range x)) ≤ 10752 := by
  obtain ⟨φ, hrange, -⟩ := exists_hom_of_rels x hx
  obtain ⟨hfin, hcard⟩ := card_PG_e64Rels
  have hs : Function.Surjective φ.rangeRestrict := φ.rangeRestrict_surjective
  rw [← hrange]
  exact ⟨Finite.of_surjective _ hs, (Nat.card_le_card_of_surjective _ hs).trans hcard⟩

theorem card_closure_le_of_rels (x : Fin 28 → G)
    (hx : ∀ r ∈ e64MemberRels, FreeGroup.lift x (FreeGroup.mk r) = 1) :
    Nat.card (Subgroup.closure (Set.range x)) ≤ 10752 :=
  (finite_card_closure_of_rels x hx).2

theorem surjective_of_map_gen {x : Fin 28 → G}
    (f : ↥(Subgroup.closure (Set.range x)) →* ↥e64Sub)
    (hfx : ∀ i, (f ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : AEQ 7) = modelGen i) :
    Function.Surjective f := by
  intro y
  have hle : e64Sub ≤ f.range.map e64Sub.subtype := by
    refine closure_modelGen.symm.le.trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨f ⟨x i, _⟩, ⟨_, rfl⟩, hfx i⟩
  obtain ⟨z, ⟨w, rfl⟩, hz⟩ := hle y.2
  exact ⟨w, Subtype.ext hz⟩


theorem injective_of_rels (x : Fin 28 → G)
    (hx : ∀ r ∈ e64MemberRels, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (f : ↥(Subgroup.closure (Set.range x)) →* ↥e64Sub) (hf : Function.Surjective f) :
    Function.Injective f := by
  obtain ⟨hfin, hcard⟩ := finite_card_closure_of_rels x hx
  exact (hf.bijective_of_nat_card_le (hcard.trans E64Ker.le_card_e64Sub)).1

theorem injective_of_rels_of_map (x : Fin 28 → G)
    (hx : ∀ r ∈ e64MemberRels, FreeGroup.lift x (FreeGroup.mk r) = 1)
    (f : ↥(Subgroup.closure (Set.range x)) →* ↥e64Sub)
    (hfx : ∀ i, (f ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : AEQ 7) = modelGen i) :
    Function.Injective f :=
  injective_of_rels x hx f (surjective_of_map_gen f hfx)

end Order

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.E64P
