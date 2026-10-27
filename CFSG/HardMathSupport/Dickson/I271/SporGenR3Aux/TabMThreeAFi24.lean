module

public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAY442
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAWords
public import Certificates.Certificate17593
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.YGroups
open TauCeti.Sporadic (Fi24AutomorphismGroup)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons evalWord_append)

@[expose] noncomputable def kmGen (i : ℕ) : Fi24AutomorphismGroup :=
  if h : i < 12 then PresentedGroup.of ⟨i, h⟩ else 1

theorem kmGen_of_lt {i : ℕ} (h : i < 12) : kmGen i = PresentedGroup.of ⟨i, h⟩ := dif_pos h

theorem kmGen_mul_self (i : ℕ) : kmGen i * kmGen i = 1 := by
  unfold kmGen
  split_ifs with h
  · exact TauCeti.Sporadic.fi24AutomorphismGroup_of_mul_of_self _
  · exact mul_one 1

theorem kmGen_inv (i : ℕ) : (kmGen i)⁻¹ = kmGen i :=
  inv_eq_of_mul_eq_one_right (kmGen_mul_self i)

theorem kmLetter_lt (u : ℕ) : kmLetter u < 11 := by
  unfold kmLetter
  split <;> omega

@[expose] def kmFin (u : Fin 11) : Fin 12 := ⟨kmLetter u, by have := kmLetter_lt u; omega⟩

theorem kmGen_kmLetter {u : ℕ} (hu : u < 11) :
    kmGen (kmLetter u) = PresentedGroup.of (kmFin ⟨u, hu⟩) :=
  kmGen_of_lt _

theorem kmOfY_lt (w : List ℕ) : ∀ x ∈ kmOfY w, x < 12 := by
  intro x hx
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
  have := kmLetter_lt u
  omega

theorem evalWord_kmLetter (w : List ℕ) :
    evalWord (fun u => kmGen (kmLetter u)) w = evalWord kmGen (kmOfY w) := by
  unfold evalWord kmOfY
  rw [List.map_map]
  rfl

theorem km_pairExp : ∀ s t : Fin 11, s < t →
    pairExp 4 4 2 s t = TauCeti.Sporadic.fi24AutomorphismCoxeterMatrix (kmFin s) (kmFin t) := by
  simp only [TauCeti.Sporadic.fi24AutomorphismCoxeterMatrix_apply,
    TauCeti.Sporadic.fi24AutomorphismEdges_def]
  decide +kernel

theorem km_pair {s t : ℕ} (ht : t < 11) (hst : s < t) :
    (kmGen (kmLetter s) * kmGen (kmLetter t)) ^ pairExp 4 4 2 s t = 1 := by
  have h := TauCeti.Sporadic.fi24AutomorphismGroup_of_mul_of_pow (kmFin ⟨s, by omega⟩)
    (kmFin ⟨t, ht⟩)
  rw [← km_pairExp ⟨s, by omega⟩ ⟨t, ht⟩ (Fin.mk_lt_mk.2 hst)] at h
  rwa [kmGen_kmLetter (by omega : s < 11), kmGen_kmLetter ht]

section Bridge

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.Fi24

@[expose] noncomputable def kmX : ℕ → GL (Fin 781) (ZMod 3) :=
  Classical.choose bridge_x

theorem kmX_val :
    ∀ k < 11, (kmX k : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.KD.Fi24Img.img k :=
  (Classical.choose_spec bridge_x).1

theorem kmX_of_ge : ∀ k, 11 ≤ k → kmX k = 1 :=
  (Classical.choose_spec bridge_x).2.1

theorem kmX_rels :
    ∀ v ∈ TauCeti.Sporadic.fi24PrimePresentation.relatorLetters, wordProd kmX v = 1 :=
  (Classical.choose_spec bridge_x).2.2.1

private theorem presentation_eq' :
    TauCeti.SporadicName.Fi24Prime.presentation = TauCeti.Sporadic.fi24PrimePresentation := rfl

theorem card_fi24Prime_le :
    Finite TauCeti.Sporadic.fi24PrimePresentation.Group ∧
      Nat.card TauCeti.Sporadic.fi24PrimePresentation.Group ≤ 1255205709190661721292800 := by
  have h := CFSG.Sporadic.Presentation.Fi24Prime.finite_card_le_exact
  revert h
  show Finite TauCeti.SporadicName.Fi24Prime.presentation.Group ∧
      Nat.card TauCeti.SporadicName.Fi24Prime.presentation.Group ≤ 1255205709190661721292800 →
    Finite TauCeti.Sporadic.fi24PrimePresentation.Group ∧
      Nat.card TauCeti.Sporadic.fi24PrimePresentation.Group ≤ 1255205709190661721292800
  rw [presentation_eq']
  exact id

theorem range_presHom_kmX :
    (presHom TauCeti.Sporadic.fi24PrimePresentation kmX kmX_rels).range = J := by
  obtain ⟨hfin, hcard⟩ := card_fi24Prime_le
  have hJ : J ≤ (presHom TauCeti.Sporadic.fi24PrimePresentation kmX kmX_rels).range :=
    J_le_range fun g hg => closure_le_range kmX_rels ((Classical.choose_spec bridge_x).2.2.2 g hg)
  have hs := (presHom TauCeti.Sporadic.fi24PrimePresentation kmX kmX_rels).rangeRestrict_surjective
  have : Finite (presHom TauCeti.Sporadic.fi24PrimePresentation kmX kmX_rels).range :=
    Finite.of_surjective _ hs
  exact (Subgroup.eq_of_le_of_card_ge hJ
    ((Nat.card_le_card_of_surjective _ hs).trans (hcard.trans card_J.symm.le))).symm

theorem kmX_mem_J
    (k : ℕ) : kmX k ∈ J := by
  by_cases hk : k < 11
  · rw [← range_presHom_kmX]
    exact ⟨presGen _ k, presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩
  · rw [kmX_of_ge k (Nat.not_lt.1 hk)]
    exact J.one_mem

@[expose] noncomputable def kmJ
    (k : ℕ) : J :=
  ⟨kmX k, kmX_mem_J k⟩

theorem kmJ_rels :
    ∀ v ∈ TauCeti.Sporadic.fi24PrimePresentation.relatorLetters, wordProd kmJ v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd]
  exact kmX_rels v hv

theorem subtype_presHom_kmJ :
    J.subtype.comp (presHom TauCeti.Sporadic.fi24PrimePresentation kmJ kmJ_rels) =
      presHom TauCeti.Sporadic.fi24PrimePresentation kmX kmX_rels := by
  apply PresentedGroup.ext
  intro i
  rw [MonoidHom.comp_apply, presHom, presHom, PresentedGroup.toGroup.of,
    PresentedGroup.toGroup.of]
  rfl

theorem presHom_kmJ_surjective :
    Function.Surjective (presHom TauCeti.Sporadic.fi24PrimePresentation kmJ kmJ_rels) := by
  intro y
  have hy : (y : GL (Fin 781) (ZMod 3)) ∈
      (presHom TauCeti.Sporadic.fi24PrimePresentation kmX kmX_rels).range := by
    rw [range_presHom_kmX]
    exact y.2
  obtain ⟨p, hp⟩ := hy
  exact ⟨p, Subtype.ext ((DFunLike.congr_fun subtype_presHom_kmJ p).trans hp)⟩

theorem presHom_kmJ_bijective :
    Function.Bijective (presHom TauCeti.Sporadic.fi24PrimePresentation kmJ kmJ_rels) := by
  obtain ⟨hfin, hcard⟩ := card_fi24Prime_le
  exact presHom_kmJ_surjective.bijective_of_nat_card_le (hcard.trans card_J.symm.le)

@[expose] noncomputable def kmEquiv :
    ↥(commutator Fi24AutomorphismGroup) ≃* J :=
  TauCeti.Sporadic.fi24PrimeGroupMulEquivCommutator.symm.trans
    (MulEquiv.ofBijective _ presHom_kmJ_bijective)

theorem kmEquiv_symm_kmJ
    {i : ℕ} (hi : i < 11) :
    (kmEquiv.symm (kmJ i) : Fi24AutomorphismGroup) = kmGen 0 * kmGen (i + 1) := by
  have hg : i < TauCeti.Sporadic.fi24PrimePresentation.generatorCount := by
    rw [generatorCount_eq]
    exact hi
  have h1 : (MulEquiv.ofBijective _ presHom_kmJ_bijective).symm (kmJ i) =
      presGen TauCeti.Sporadic.fi24PrimePresentation i := by
    rw [MulEquiv.symm_apply_eq]
    exact (presHom_presGen _ _ kmJ_rels hg).symm
  rw [kmEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm, h1, presGen, dif_pos hg,
    kmGen_of_lt (by norm_num), kmGen_of_lt (by omega)]
  exact TauCeti.Sporadic.coe_fi24PrimeGroupMulEquivCommutator_of ⟨i, hi⟩

theorem km_wordProd_append {G : Type*} [Group G] (x : ℕ → G) (v w : List (ℕ × Bool)) :
    wordProd x (v ++ w) = wordProd x v * wordProd x w := by
  simp [wordProd, List.map_append, List.prod_append]

theorem km_letter_false
    {x : ℕ} (hx : x < 12) :
    (kmEquiv.symm (wordProd kmJ (if x = 0 then [] else [(x - 1, false)])) :
      Fi24AutomorphismGroup) = (kmGen 0 * kmGen x)⁻¹ := by
  split_ifs with h
  · subst h
    rw [kmGen_mul_self, inv_one]
    simp [wordProd]
  · have e := kmEquiv_symm_kmJ (i := x - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at e
    simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Bool.false_eq_true, ↓reduceIte, map_inv, InvMemClass.coe_inv]
    rw [e]

theorem km_letter_true
    {y : ℕ} (hy : y < 12) :
    (kmEquiv.symm (wordProd kmJ (if y = 0 then [] else [(y - 1, true)])) :
      Fi24AutomorphismGroup) = kmGen 0 * kmGen y := by
  split_ifs with h
  · subst h
    rw [kmGen_mul_self]
    simp [wordProd]
  · have e := kmEquiv_symm_kmJ (i := y - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at e
    simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      ↓reduceIte]
    exact e

theorem kmGen_mul_kmGen (x y : ℕ) :
    kmGen x * kmGen y = (kmGen 0 * kmGen x)⁻¹ * (kmGen 0 * kmGen y) := by
  rw [mul_inv_rev, kmGen_inv, kmGen_inv, mul_assoc, ← mul_assoc (kmGen 0) (kmGen 0),
    kmGen_mul_self, one_mul]

theorem evalWord_kmGen :
    ∀ w : List ℕ, w.length % 2 = 0 → (∀ x ∈ w, x < 12) →
      evalWord kmGen w = (kmEquiv.symm (wordProd kmJ (kmSchreier w)) : Fi24AutomorphismGroup)
  | [], _, _ => by simp [kmSchreier, wordProd]
  | [_], h, _ => by simp at h
  | x :: y :: w, h, hw => by
    rw [evalWord_cons, evalWord_cons, ← mul_assoc, kmGen_mul_kmGen,
      evalWord_kmGen w (by simp at h; omega) (fun z hz => hw z (by simp [hz])), kmSchreier,
      km_wordProd_append, km_wordProd_append, map_mul, map_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, km_letter_false (hw x (by simp)), km_letter_true (hw y (by simp))]

theorem kmSchreier_lt : ∀ w : List ℕ, (∀ x ∈ w, x < 12) → ∀ l ∈ kmSchreier w, l.1 < 11
  | [], _ => by simp [kmSchreier]
  | [_], _ => by simp [kmSchreier]
  | x :: y :: w, hw => by
    intro l hl
    have hx := hw x (by simp)
    have hy := hw y (by simp)
    rw [kmSchreier] at hl
    simp only [List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · split_ifs at hl <;> simp at hl
      subst hl
      simp only
      omega
    · split_ifs at hl <;> simp at hl
      subst hl
      simp only
      omega
    · exact kmSchreier_lt w (fun z hz => hw z (by simp [hz])) l hl

theorem kmJ_kmRels :
    ∀ v ∈ kmRels (), wordProd kmJ v = 1 := by
  intro v hv
  apply Subtype.ext
  rw [coe_wordProd]
  exact (Certificates.certificate17593 kmX kmX_val).1 v hv

theorem kmJ_kmMoves :
    ∀ v ∈ kmMoves (), wordProd kmJ v ≠ 1 := by
  intro v hv h
  apply (Certificates.certificate17593 kmX kmX_val).2 v hv
  have h' := congrArg Subtype.val h
  rw [coe_wordProd] at h'
  exact h'

theorem km_relWord
    {w : List ℕ}
    (hw : w ∈ kmRelWords ()) (hl : w.length % 2 = 0) (hlt : ∀ x ∈ w, x < 12) :
    evalWord kmGen w = 1 := by
  rw [evalWord_kmGen w hl hlt, kmJ_kmRels _ (List.mem_map_of_mem hw), map_one]
  rfl

theorem km_spider :
    evalWord kmGen [3, 2, 1, 3, 4, 5, 3, 7, 8] ^ 10 = 1 := by
  rw [← Y443.evalWord_replicate_flatten]
  exact km_relWord (List.mem_cons.2 (Or.inl rfl)) (by decide) (by decide)

theorem km_f0 :
    evalWord kmGen [3, 2, 1, 0, 4, 5, 7] ^ 9 = kmGen 11 := by
  have h := km_relWord (w := kmF0L) (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
    (by decide) (by decide)
  have e11 : evalWord kmGen [11] = kmGen 11 := by simp [evalWord]
  rw [kmF0L, evalWord_append, Y443.evalWord_replicate_flatten, e11] at h
  rw [eq_inv_of_mul_eq_one_left h, kmGen_inv]

theorem km_w23_pow :
    evalWord kmGen (kmOfY yW23) ^ 23 = 1 := by
  rw [← Y443.evalWord_replicate_flatten]
  refine km_relWord (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr
    (List.mem_cons.2 (Or.inl rfl)))))) (by decide +kernel) fun x hx => ?_
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
  rw [List.eq_of_mem_replicate hl] at hx
  exact kmOfY_lt _ x hx

theorem km_moves
    {u : List ℕ}
    (hu : u ∈ yMoves) : evalWord kmGen (kmOfY u) ≠ 1 := by
  have hev : ∀ u ∈ yMoves, u.length % 2 = 0 := by decide +kernel
  have hl : (kmOfY u).length % 2 = 0 := by
    rw [kmOfY, List.length_map]
    exact hev u hu
  rw [evalWord_kmGen _ hl (kmOfY_lt u)]
  intro h
  have h' : kmEquiv.symm (wordProd kmJ (kmSchreier (kmOfY u))) = 1 := Subtype.ext h
  exact kmJ_kmMoves _ (List.mem_map_of_mem hu) ((MulEquiv.map_eq_one_iff _).1 h')

@[expose] def kmLong : List ℕ := [3, 2, 1, 0, 10, 11, 3, 4, 5, 6, 9, 3, 7, 8]

theorem km_long : evalWord kmGen kmLong ^ 17 = 1 := by
  have hmem : TauCeti.Sporadic.fi24SourceLongRelator.toFreeGroup ∈
      TauCeti.Relator.relatorSet TauCeti.Sporadic.fi24AutomorphismRelators := by
    rw [TauCeti.Relator.mem_relatorSet]
    refine ⟨_, ?_, rfl⟩
    rw [TauCeti.Sporadic.fi24AutomorphismRelators_def,
      TauCeti.Sporadic.fi24AutomorphismAdditionalRelators_def]
    exact List.mem_append_right _ (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
  have h := PresentedGroup.one_of_mem hmem
  rw [TauCeti.Sporadic.fi24SourceLongRelator_def, TauCeti.Relator.toFreeGroup_pow, map_pow,
    TauCeti.Sporadic.fi24SourceLongWord_def] at h
  simp only [TauCeti.Relator.toFreeGroup_mul, TauCeti.Relator.toFreeGroup_gen, map_mul] at h
  refine Eq.trans ?_ h
  congr 1

theorem kmOfY_spider : kmOfY (spiderWord 4 4) = [3, 2, 1, 3, 4, 5, 3, 7, 8] := by decide

theorem km_yRels :
    ∀ w ∈ yRels 4 4 2, evalWord (fun u => kmGen (kmLetter u)) w = 1 :=
  Relabel.evalWord_yRels_eq_one _ (fun _ _ => kmGen_mul_self _)
    (fun t ht s hst => km_pair (by simpa [ngen] using ht) hst)
    (fun _ _ _ => by rw [evalWord_kmLetter, kmOfY_spider]; exact km_spider)

@[expose] noncomputable def yKM :
    YGroup 4 4 2 →* Fi24AutomorphismGroup :=
  yModelHom (fun u => kmGen (kmLetter u)) km_yRels

theorem yKM_yGen
    {u : ℕ} (hu : u < 11) :
    yKM (yGen 4 4 2 u) = kmGen (kmLetter u) :=
  yModelHom_yGen (hc := hu)

theorem yKM_evalWord
    (w : List ℕ)
    (hw : ∀ c ∈ w, c < 11) : yKM (evalWord (yGen 4 4 2) w) = evalWord kmGen (kmOfY w) := by
  rw [yKM, Relabel.yModelHom_evalWord w (fun c hc => by simpa [ngen] using hw c hc),
    evalWord_kmLetter]

theorem yKM_yF0 :
    yKM (evalWord (yGen 4 4 2) yF0) = kmGen 11 := by
  rw [yKM_evalWord _ (by decide),
    show kmOfY yF0 = (List.replicate 9 [3, 2, 1, 0, 4, 5, 7]).flatten by decide,
    Y443.evalWord_replicate_flatten, km_f0]

theorem yKM_yV :
    yKM (evalWord (yGen 4 4 2) yVWord) = evalWord kmGen kmLong := by
  rw [yVWord, evalWord_append, evalWord_append, map_mul, map_mul, yKM_yF0,
    yKM_evalWord _ (by decide), yKM_evalWord _ (by decide),
    show kmLong = kmOfY [0, 1, 2, 3, 4] ++ [11] ++ kmOfY [0, 5, 6, 7, 8, 0, 9, 10] by decide,
    evalWord_append, evalWord_append, evalWord_cons, evalWord_nil, mul_one]

theorem yKM_yV_pow :
    yKM (evalWord (yGen 4 4 2) yVWord) ^ 17 = 1 := by
  rw [yKM_yV, km_long]

theorem yKM_yW23_pow :
    yKM (evalWord (yGen 4 4 2) yW23) ^ 23 = 1 := by
  rw [yKM_evalWord _ (by decide +kernel), km_w23_pow]

theorem yKM_yMoves
    {u : List ℕ}
    (hu : u ∈ yMoves) : yKM (evalWord (yGen 4 4 2) u) ≠ 1 := by
  have hlt : ∀ u ∈ yMoves, ∀ c ∈ u, c < 11 := by decide +kernel
  rw [yKM_evalWord _ (hlt u hu)]
  exact km_moves hu

theorem yKM_surjective :
    Function.Surjective yKM := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  have hex : ∀ j < 11, ∃ u < 11, kmLetter u = j := by decide
  rintro _ ⟨⟨j, hj12⟩, rfl⟩
  by_cases hj : j < 11
  · obtain ⟨u, hu, he⟩ := hex j hj
    exact ⟨yGen 4 4 2 u, by rw [yKM_yGen hu, he, kmGen_of_lt hj12]⟩
  · obtain rfl : j = 11 := by omega
    exact ⟨evalWord (yGen 4 4 2) yF0, by rw [yKM_yF0, kmGen_of_lt hj12]⟩

theorem card_KM :
    Nat.card Fi24AutomorphismGroup = 2 * 1255205709190661721292800 := by
  have hs : Function.Surjective TauCeti.Sporadic.fi24ParityHom := by
    intro x
    rcases (show ∀ y : Multiplicative (ZMod 2), y = 1 ∨ y = Multiplicative.ofAdd 1 by decide) x
      with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨PresentedGroup.of 0, TauCeti.Sporadic.fi24ParityHom_of 0⟩
  have hidx : (commutator Fi24AutomorphismGroup).index = 2 := by
    rw [TauCeti.Sporadic.commutator_fi24AutomorphismGroup_eq_ker_fi24ParityHom,
      Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hc : Nat.card (commutator Fi24AutomorphismGroup) = 1255205709190661721292800 := by
    rw [Nat.card_congr kmEquiv.toEquiv, CFSG.Sporadic.Fi24.card_J]
  rw [← Subgroup.card_mul_index (commutator Fi24AutomorphismGroup), hc, hidx, mul_comm]

theorem card_ker_yKM_le :
    Finite yKM.ker ∧ Nat.card yKM.ker ≤ 3 := by
  obtain ⟨hfin, hY⟩ := y442_card_le
  have h := Subgroup.card_mul_index yKM.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 yKM_surjective, Subgroup.card_top,
    card_KM] at h
  exact ⟨inferInstance, by omega⟩

theorem map_commutator_yKM :
    (commutator (YGroup 4 4 2)).map yKM = commutator Fi24AutomorphismGroup := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 yKM_surjective]

theorem yKM_mem_commutator
    (y : ↥(commutator (YGroup 4 4 2))) :
    yKM (y : YGroup 4 4 2) ∈ commutator Fi24AutomorphismGroup := by
  rw [← map_commutator_yKM]
  exact Subgroup.mem_map_of_mem yKM y.2

@[expose] noncomputable def yKMc :
    ↥(commutator (YGroup 4 4 2)) →* ↥(commutator Fi24AutomorphismGroup) :=
  (yKM.comp (commutator (YGroup 4 4 2)).subtype).codRestrict _ yKM_mem_commutator

@[expose] noncomputable def yJ :
    ↥(commutator (YGroup 4 4 2)) →* CFSG.Sporadic.Fi24.J :=
  MonoidHom.comp (kmEquiv : ↥(commutator Fi24AutomorphismGroup) →* CFSG.Sporadic.Fi24.J) yKMc

theorem yJ_apply
    (y : ↥(commutator (YGroup 4 4 2))) : yJ y = kmEquiv (yKMc y) := rfl

theorem kmEquiv_symm_yJ
    (y : ↥(commutator (YGroup 4 4 2))) :
    (kmEquiv.symm (yJ y) : Fi24AutomorphismGroup) = yKM y := by
  rw [yJ_apply, MulEquiv.symm_apply_apply]
  rfl

theorem yJ_surjective :
    Function.Surjective yJ := by
  intro x
  obtain ⟨y, hy, hyx⟩ := (show ((kmEquiv.symm x : Fi24AutomorphismGroup)) ∈
    (commutator (YGroup 4 4 2)).map yKM by rw [map_commutator_yKM]; exact (kmEquiv.symm x).2)
  refine ⟨⟨y, hy⟩, ?_⟩
  apply kmEquiv.symm.injective
  exact Subtype.ext ((kmEquiv_symm_yJ ⟨y, hy⟩).trans hyx)

theorem kmEquiv_one :
    kmEquiv (1 : ↥(commutator Fi24AutomorphismGroup)) = 1 :=
  map_one (kmEquiv : ↥(commutator Fi24AutomorphismGroup) →* CFSG.Sporadic.Fi24.J)

theorem yJ_eq_one_iff
    (y : ↥(commutator (YGroup 4 4 2))) : yJ y = 1 ↔ yKM y = 1 := by
  rw [yJ_apply, ← kmEquiv_one, kmEquiv.injective.eq_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem card_ker_yJ_le :
    Finite yJ.ker ∧ Nat.card yJ.ker ≤ 3 := by
  obtain ⟨hfin, hk⟩ := card_ker_yKM_le
  have hinj : Function.Injective (fun y : yJ.ker => (⟨(y.1 : YGroup 4 4 2),
      (yJ_eq_one_iff y.1).1 y.2⟩ : yKM.ker)) := by
    intro y y' h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : yKM.ker => (z : YGroup 4 4 2)) h))
  exact ⟨Finite.of_injective _ hinj, (Nat.card_le_card_of_injective _ hinj).trans hk⟩

end Bridge

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
