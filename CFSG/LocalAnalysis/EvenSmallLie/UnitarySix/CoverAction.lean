module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionData
public import CFSG.LieType.Multipliers.U62Cover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.EvenSmallLie.UnitarySix

open Subgroup CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62 CFSG.CosetTable CFSG.Fischer
  CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi22.Native
  CFSG.RankThree.PerfectCover
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence
  centerQuotientOuterHom centerQuotient_outer_injective)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient
  onCenterQuotient_apply_mk)
open scoped commutatorElement

section Words

variable {m k : ℕ}

theorem mk_substWord (hs : List (List (Fin m × Bool))) (r : List (Fin k × Bool)) :
    FreeGroup.mk (substWord hs r) =
      FreeGroup.lift (fun i : Fin k => FreeGroup.mk (hs.getD i [])) (FreeGroup.mk r) := by
  induction r with
  | nil => rfl
  | cons l r ih =>
    obtain ⟨i, b⟩ := l
    rw [show FreeGroup.mk ((i, b) :: r) = FreeGroup.mk [(i, b)] * FreeGroup.mk r from
      by rw [FreeGroup.mul_mk]; rfl, map_mul, ← ih]
    simp only [substWord, List.flatMap_cons]
    rw [← FreeGroup.mul_mk]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← FreeGroup.inv_mk, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl,
        map_inv, FreeGroup.lift_apply_of]
    · simp only [↓reduceIte]
      rw [show FreeGroup.mk [(i, true)] = FreeGroup.of i from rfl, FreeGroup.lift_apply_of]

theorem lift_mk_substWord {G : Type*} [Group G] (g : Fin m → G) (hs : List (List (Fin m × Bool)))
    (r : List (Fin k × Bool)) :
    FreeGroup.lift g (FreeGroup.mk (substWord hs r)) =
      FreeGroup.lift (fun i : Fin k => FreeGroup.lift g (FreeGroup.mk (hs.getD i [])))
        (FreeGroup.mk r) := by
  rw [mk_substWord, ← MonoidHom.comp_apply]
  congr 1
  exact FreeGroup.ext_hom _ _ fun i => by simp

theorem eq_on_commutator {F L Q : Type*} [Group F] [Group L] [Group Q] (q : L →* Q)
    (hker : q.ker ≤ center L) (φ φ' : F →* L) (h : ∀ x, q (φ x) = q (φ' x)) {x : F}
    (hx : x ∈ commutator F) : φ x = φ' x := by
  have hc : ∀ y, (φ y)⁻¹ * φ' y ∈ center L := fun y => hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hle : commutator F ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc a) (hc b)]
  exact hle hx

theorem lift_eq_lift_substWord_of_lift {L Q : Type*} [Group L] [Group Q] (q : L →* Q)
    (hq : Function.Surjective q) (hker : q.ker ≤ center L) (g : Fin m → Q)
    (ds : List (List (Fin m × Bool))) (δ : Q →* Q)
    (hδ : ∀ i, δ (g i) = FreeGroup.lift g (FreeGroup.mk (ds.getD i []))) (ℓ : Fin m → L)
    (hℓ : ∀ i, q (ℓ i) = g i) (α : L →* L) (hfix : ∀ z ∈ q.ker, α z = z) (t : Q)
    (hα : ∀ x, q (α x) = δ (t * q x * t⁻¹)) (w : List (Fin m × Bool))
    (hw : FreeGroup.mk w ∈ commutator (FreeGroup (Fin m)))
    (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) :
    FreeGroup.lift ℓ (FreeGroup.mk w) = FreeGroup.lift ℓ (FreeGroup.mk (substWord ds w)) := by
  obtain ⟨s, hs⟩ := hq (δ t)
  set m' : Fin m → L := fun i => FreeGroup.lift ℓ (FreeGroup.mk (ds.getD i [])) with hm'
  have hqℓ : ∀ x, q (FreeGroup.lift ℓ x) = FreeGroup.lift g x := fun x => by
    rw [← MonoidHom.comp_apply]
    exact DFunLike.congr_fun (FreeGroup.ext_hom _ _ fun i => by simp [hℓ]) x
  have hqm : ∀ i, q (m' i) = δ (g i) := fun i => by rw [hδ, hqℓ]
  have hqδ : ∀ x, q (FreeGroup.lift m' x) = δ (FreeGroup.lift g x) := fun x => by
    rw [← MonoidHom.comp_apply, ← MonoidHom.comp_apply]
    exact DFunLike.congr_fun (FreeGroup.ext_hom _ _ fun i => by simp [hqm]) x
  set φ : FreeGroup (Fin m) →* L := α.comp (FreeGroup.lift ℓ)
  set φ' : FreeGroup (Fin m) →* L :=
    (MulAut.conj s).toMonoidHom.comp (FreeGroup.lift m')
  have hφ : ∀ x, q (φ x) = q (φ' x) := fun x => by
    have : q.comp φ = q.comp φ' := FreeGroup.ext_hom _ _ fun i => by
      simp only [φ, φ', MonoidHom.comp_apply, FreeGroup.lift_apply_of, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul, map_inv, hα, hℓ, hqm, hs]
    exact DFunLike.congr_fun this x
  have key := eq_on_commutator q hker φ φ' hφ hw
  have h1 : FreeGroup.lift ℓ (FreeGroup.mk w) ∈ q.ker := by
    rw [MonoidHom.mem_ker, hqℓ, hw1]
  have h2 : FreeGroup.lift m' (FreeGroup.mk w) ∈ center L := hker <| by
    rw [MonoidHom.mem_ker, hqδ, hw1, map_one]
  have hφw : φ (FreeGroup.mk w) = FreeGroup.lift ℓ (FreeGroup.mk w) := hfix _ h1
  have hφ'w : φ' (FreeGroup.mk w) = FreeGroup.lift m' (FreeGroup.mk w) := by
    change s * FreeGroup.lift m' (FreeGroup.mk w) * s⁻¹ = _
    rw [mem_center_iff.mp h2 s, mul_inv_cancel_right]
  rw [← hφw, key, hφ'w, hm', ← lift_mk_substWord]

end Words

noncomputable def deltaGen
    (i : Fin 5) : T46 :=
  FreeGroup.lift genE (FreeGroup.mk (deltaWords.getD i []))

theorem lift_genE_eq_one_of_fixAll
    {v : List (Fin 5 × Bool)}
    (h : t46FixAll (wordT 693 t46Gen (U62.expand v)) = true) :
    FreeGroup.lift genE (FreeGroup.mk v) = 1 := by
  apply Subtype.ext
  rw [lift_genE_val, lift_genP]
  exact t46_eq_one_of_fixAll (Rep.wordT (by norm_num) _ fun l _ => rep_t46G l) h

theorem deltaGen_rels
    : ∀ r ∈ wordSet rels, FreeGroup.lift deltaGen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  have h := deltaRel_check
  unfold deltaRelCheck at h
  rw [show FreeGroup.lift deltaGen (FreeGroup.mk v) =
    FreeGroup.lift genE (FreeGroup.mk (substWord deltaWords v)) from
      (lift_mk_substWord genE deltaWords v).symm]
  exact lift_genE_eq_one_of_fixAll (List.all_eq_true.1 h v hv)

noncomputable def deltaHom
    : T46 →* T46 :=
  (QuotientGroup.lift (FreeGroup.lift genE).ker (FreeGroup.lift deltaGen) (by
      rw [isPresentation_T46.ker_lift]
      exact normalClosure_le_normal fun r hr => deltaGen_rels r hr)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      isPresentation_T46.lift_surjective).symm.toMonoidHom

theorem deltaHom_lift
    (x : FreeGroup (Fin 5)) :
    deltaHom (FreeGroup.lift genE x) = FreeGroup.lift deltaGen x := by
  have e : (QuotientGroup.quotientKerEquivOfSurjective _ isPresentation_T46.lift_surjective).symm
      (FreeGroup.lift genE x) = (x : FreeGroup (Fin 5) ⧸ (FreeGroup.lift genE).ker) :=
    (MulEquiv.symm_apply_eq _).mpr rfl
  rw [deltaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, QuotientGroup.lift_mk]

theorem deltaHom_genE
    (i : Fin 5) : deltaHom (genE i) = deltaGen i := by
  simpa using deltaHom_lift (FreeGroup.of i)

theorem deltaGen_of_le_three
    (i : Fin 5) (hi : i ≠ 4) : deltaGen i = genE i := by
  fin_cases i
  · exact FreeGroup.lift_apply_of
  · exact FreeGroup.lift_apply_of
  · exact FreeGroup.lift_apply_of
  · exact FreeGroup.lift_apply_of
  · exact absurd rfl hi

theorem deltaGen_four :
    deltaGen 4 = genE 2 * genE 4 * (genE 2)⁻¹ := by
  change FreeGroup.lift genE (FreeGroup.of 2 * FreeGroup.of 4 * (FreeGroup.of 2)⁻¹) = _
  rw [map_mul, map_mul, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]

theorem deltaHom_surjective
    : Function.Surjective deltaHom := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_genE, closure_le]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i = 4
  · subst hi
    refine ⟨(genE 2)⁻¹ * genE 4 * genE 2, ?_⟩
    rw [map_mul, map_mul, map_inv, deltaHom_genE, deltaHom_genE, deltaGen_four,
      deltaGen_of_le_three 2 (by decide)]
    group
  · exact ⟨genE i, by rw [deltaHom_genE, deltaGen_of_le_three i hi]⟩

@[expose] noncomputable def diagonalAut :
    MulAut T46 :=
  MulEquiv.ofBijective deltaHom
    ⟨Finite.injective_iff_surjective.2 deltaHom_surjective, deltaHom_surjective⟩

theorem diagonalAut_apply
    (x : T46) : diagonalAut x = deltaHom x := rfl

theorem diagonalAut_genE
    (i : Fin 5) :
    diagonalAut (genE i) = FreeGroup.lift genE (FreeGroup.mk (deltaWords.getD i [])) :=
  deltaHom_genE i

theorem genE_two_pow_three :
    genE 2 ^ 3 = 1 := by
  have h := isPresentation_T46.lift_eq_one (r := FreeGroup.mk [(2, true), (2, true), (2, true)])
    (List.mem_map_of_mem (by decide))
  rw [show FreeGroup.mk [((2 : Fin 5), true), (2, true), (2, true)] =
    FreeGroup.of 2 * FreeGroup.of 2 * FreeGroup.of 2 from rfl, map_mul, map_mul,
    FreeGroup.lift_apply_of] at h
  rw [pow_three, ← mul_assoc]
  exact h

theorem diagonalAut_pow_three
    : diagonalAut ^ 3 = 1 := by
  have hext : (diagonalAut ^ 3 : MulAut T46).toMonoidHom = (1 : MulAut T46).toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense closure_genE (by
      rintro _ ⟨i, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, pow_three, MulAut.mul_apply,
        MulAut.mul_apply, MulAut.one_apply]
      by_cases hi : i = 4
      · subst hi
        simp only [diagonalAut_apply, map_mul, map_inv, deltaHom_genE, deltaGen_four,
          deltaGen_of_le_three 2 (by decide)]
        have h3 : genE 2 * genE 2 * genE 2 = 1 := by
          rw [mul_assoc, ← pow_three]
          exact genE_two_pow_three
        calc _ = genE 2 * genE 2 * genE 2 * genE 4 * (genE 2 * genE 2 * genE 2)⁻¹ := by group
          _ = genE 4 := by rw [h3, one_mul, inv_one, mul_one]
      · simp only [diagonalAut_apply, deltaHom_genE, deltaGen_of_le_three i hi])
  exact MulEquiv.ext fun x => DFunLike.congr_fun hext x

theorem commGenWords_getD (i : Fin 5) : commGenWords.getD i [] = commWords (coverPairs i) := by
  fin_cases i <;> rfl

theorem lift_mem_commutator {k : ℕ} (f : Fin 5 → FreeGroup (Fin k))
    (hf : ∀ i, f i ∈ commutator (FreeGroup (Fin k))) (x : FreeGroup (Fin 5)) :
    FreeGroup.lift f x ∈ commutator (FreeGroup (Fin k)) := by
  induction x using FreeGroup.induction_on with
  | one => rw [map_one]; exact one_mem _
  | of i => rw [FreeGroup.lift_apply_of]; exact hf i
  | inv_of i ih => rw [map_inv]; exact inv_mem ih
  | mul x y hx hy => rw [map_mul]; exact mul_mem hx hy

theorem mk_substWord_commGenWords_mem_commutator (r : List (Fin 5 × Bool)) :
    FreeGroup.mk (substWord commGenWords r) ∈ commutator (FreeGroup (Fin 5)) := by
  rw [mk_substWord]
  exact lift_mem_commutator _ (fun i => by
    rw [commGenWords_getD]
    exact mk_commWords_mem_commutator _) _

theorem lift_genE_substWord_commGenWords
    (r : List (Fin 5 × Bool)) :
    FreeGroup.lift genE (FreeGroup.mk (substWord commGenWords r)) =
      FreeGroup.lift genE (FreeGroup.mk r) := by
  rw [lift_mk_substWord]
  have : (fun i : Fin 5 => FreeGroup.lift genE (FreeGroup.mk (commGenWords.getD i []))) = genE :=
    funext fun i => by rw [commGenWords_getD, lift_genE_comm]
  rw [this]

theorem lift_genE_substWord_delta
    (w : List (Fin 5 × Bool)) :
    FreeGroup.lift genE (FreeGroup.mk (substWord deltaWords w)) =
      diagonalAut (FreeGroup.lift genE (FreeGroup.mk w)) := by
  rw [lift_mk_substWord, diagonalAut_apply, deltaHom_lift]
  rfl

theorem kerTwo_mem_rels : kerTwo ∈ rels := by decide

theorem kerSix_mem_rels : kerSix ∈ rels := by decide

theorem kerThree_mem_rels : kerThree ∈ rels := by decide

theorem lift_genE_rels_eq_one
    {r : List (Fin 5 × Bool)} (hr : r ∈ rels) :
    FreeGroup.lift genE (FreeGroup.mk r) = 1 :=
  isPresentation_T46.lift_eq_one (List.mem_map_of_mem hr)

theorem lift_genE_obsWordA
    : FreeGroup.lift genE (FreeGroup.mk obsWordA) = 1 := by
  rw [obsWordA, lift_genE_substWord_commGenWords, lift_genE_rels_eq_one kerTwo_mem_rels]

theorem lift_genE_obsWordB
    : FreeGroup.lift genE (FreeGroup.mk obsWordB) = 1 := by
  rw [obsWordB, lift_genE_substWord_commGenWords, lift_genE_rels_eq_one kerSix_mem_rels]

private def congrPres {ι : Type} {S T : Set (FreeGroup ι)} (h : S = T) :
    PresentedGroup S ≃* PresentedGroup T := by
  subst h
  exact MulEquiv.refl _

private theorem congrPres_mk {ι : Type} {S T : Set (FreeGroup ι)} (h : S = T)
    (x : FreeGroup ι) : congrPres h (PresentedGroup.mk S x) = PresentedGroup.mk T x := by
  subst h
  rfl

abbrev Cover : Type := PG 5 coverWs

noncomputable abbrev mkC (v : List (Fin 5 × Bool)) : Cover :=
  PresentedGroup.mk _ (FreeGroup.mk v)

theorem mkC_append (u v : List (Fin 5 × Bool)) : mkC (u ++ v) = mkC u * mkC v := by
  rw [mkC, mkC, mkC, ← FreeGroup.mul_mk, map_mul]

theorem mkC_invRev (v : List (Fin 5 × Bool)) : mkC (FreeGroup.invRev v) = (mkC v)⁻¹ := by
  rw [mkC, mkC, ← FreeGroup.inv_mk, map_inv]

private theorem coverRelators_eq :
    coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (coverPairs i))) =
      wordSet coverWs :=
  coverRelators_wordSet rels fun i => commWords (coverPairs i)

private theorem coverW_mem_commutator : ∀ i : Fin 5, FreeGroup.mk (commWords (coverPairs i)) ∈
    commutator (FreeGroup (Fin 5)) := fun _ => mk_commWords_mem_commutator _

private noncomputable def coverEquiv :
    Cover ≃* PresentedCover (wordSet rels) (fun i => FreeGroup.mk (commWords (coverPairs i))) :=
  congrPres coverRelators_eq.symm

noncomputable def coverπ :
    Cover →* T46 :=
  (coverMap isPresentation_T46 lift_genE_comm).comp coverEquiv.toMonoidHom

theorem coverπ_mk
    (x : FreeGroup (Fin 5)) :
    coverπ (PresentedGroup.mk _ x) = FreeGroup.lift genE x := by
  change coverMap isPresentation_T46 lift_genE_comm
    (congrPres coverRelators_eq.symm (PresentedGroup.mk _ x)) = _
  rw [congrPres_mk, coverMap_mk]

theorem coverπ_surjective :
    Function.Surjective coverπ :=
  (coverMap_surjective isPresentation_T46 lift_genE_comm).comp coverEquiv.surjective

theorem ker_coverπ_le_center :
    coverπ.ker ≤ center Cover := by
  intro x hx
  have hx' : coverEquiv x ∈ (coverMap isPresentation_T46 lift_genE_comm).ker := hx
  have hc := coverMap_ker_le_center isPresentation_T46 lift_genE_comm hx'
  refine mem_center_iff.2 fun y => coverEquiv.injective ?_
  rw [map_mul, map_mul]
  exact mem_center_iff.1 hc (coverEquiv y)

theorem card_ker_coverπ_le :
    Nat.card coverπ.ker ≤ 12 := by
  obtain ⟨hfin, hle⟩ := cover_card_le
  have hq : Nat.card (Cover ⧸ coverπ.ker) = Nat.card T46 :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ coverπ_surjective).toEquiv
  have h := coverπ.ker.card_eq_card_quotient_mul_card_subgroup
  rw [hq, card_T46] at h
  change Nat.card Cover ≤ _ at hle
  omega

theorem exists_cover_hom
    {L : Type*} [Group L] [Group.IsPerfect L] (q : L →* T46)
    (hq : Function.Surjective q) (hker : q.ker ≤ center L) :
    ∃ h : Cover →* L, Function.Surjective h ∧ ∀ x, q (h x) = coverπ x := by
  set e := presentedCoverEquiv isPresentation_T46 coverW_mem_commutator lift_genE_comm
  refine ⟨(hopfLift q hq hker).comp (e.toMonoidHom.comp coverEquiv.toMonoidHom),
    (hopfLift_surjective q hq hker).comp (e.surjective.comp coverEquiv.surjective), fun x => ?_⟩
  change q (hopfLift q hq hker (e (coverEquiv x))) = _
  rw [← MonoidHom.comp_apply, comp_hopfLift, hopfCoverMap_presentedCoverEquiv]
  rfl

theorem mkC_replicate (n : ℕ) (v : List (Fin 5 × Bool)) :
    mkC (List.replicate n v).flatten = mkC v ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, mkC_append, ih, pow_succ']

theorem mkC_zWord (a b c : ℕ) :
    mkC (zWord a b c) = mkC kerThree ^ a * (mkC kerTwo ^ b * mkC kerTwo' ^ c) := by
  rw [zWord, mkC_append, mkC_append, mkC_replicate, mkC_replicate, mkC_replicate]

theorem mkC_substWord (hs : List (List (Fin 5 × Bool))) (r : List (Fin 5 × Bool)) :
    mkC (substWord hs r) =
      FreeGroup.lift (fun i : Fin 5 => mkC (hs.getD i [])) (FreeGroup.mk r) := by
  rw [mkC, mk_substWord, ← MonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeGroup.ext_hom _ _ fun i => by simp) _

theorem mkC_commWords (i : Fin 5) :
    mkC (commWords (coverPairs i)) = PresentedGroup.of i := by
  have hmem : (i, false) :: commWords (coverPairs i) ∈ coverWs :=
    List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i))
  have h : mkC ((i, false) :: commWords (coverPairs i)) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem hmem)
  have hi : mkC [(i, false)] = (PresentedGroup.of i)⁻¹ := by
    rw [mkC, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv]
    rfl
  rw [show (i, false) :: commWords (coverPairs i) = [(i, false)] ++ commWords (coverPairs i) from
    rfl, mkC_append, hi, inv_mul_eq_one] at h
  exact h.symm

theorem mkC_lift_of (r : List (Fin 5 × Bool)) :
    FreeGroup.lift (fun i : Fin 5 => (PresentedGroup.of i : Cover)) (FreeGroup.mk r) = mkC r := by
  rw [mkC]
  exact DFunLike.congr_fun (FreeGroup.ext_hom (FreeGroup.lift fun i => PresentedGroup.of i)
    (PresentedGroup.mk _) fun i => FreeGroup.lift_apply_of) _

theorem mkC_substWord_commGenWords (r : List (Fin 5 × Bool)) :
    mkC (substWord commGenWords r) = mkC r := by
  rw [mkC_substWord]
  have : (fun i : Fin 5 => mkC (commGenWords.getD i [])) = fun i => PresentedGroup.of i :=
    funext fun i => by rw [commGenWords_getD, mkC_commWords]
  rw [this, mkC_lift_of]

theorem substWord_deltaWords_commGenWords (i : Fin 5) (hi : i ≠ 4) :
    substWord deltaWords (commGenWords.getD i []) = commGenWords.getD i [] := by
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · exact absurd rfl hi

theorem mkC_substWord_delta_commGenWords (hμ : mkC muWord = 1) (r : List (Fin 5 × Bool)) :
    mkC (substWord deltaWords (substWord commGenWords r)) = mkC (substWord deltaWords r) := by
  have key : (FreeGroup.lift fun i : Fin 5 => mkC (deltaWords.getD i [])).comp
      (FreeGroup.lift fun i : Fin 5 => FreeGroup.mk (commGenWords.getD i [])) =
      FreeGroup.lift fun i : Fin 5 => mkC (deltaWords.getD i []) := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of,
      ← mkC_substWord]
    by_cases hi : i = 4
    · subst hi
      rw [muWord, mkC_append, mul_eq_one_iff_eq_inv] at hμ
      rw [commGenWords_getD, hμ]
      change (mkC [(2, true), (4, false), (2, false)])⁻¹ =
        mkC (FreeGroup.invRev [(2, true), (4, false), (2, false)])
      rw [mkC_invRev]
    · rw [substWord_deltaWords_commGenWords i hi, commGenWords_getD, mkC_commWords]
      fin_cases i
      · rfl
      · rfl
      · rfl
      · rfl
      · exact absurd rfl hi
  rw [mkC_substWord deltaWords (substWord commGenWords r), mk_substWord, ← MonoidHom.comp_apply,
    key, ← mkC_substWord]

theorem cover_kernel_facts :
    (∀ x ∈ coverπ.ker, x ∈ closure {mkC kerTwo, mkC kerTwo', mkC kerThree}) ∧
      mkC kerTwo ∈ coverπ.ker ∧ mkC kerTwo' ∈ coverπ.ker ∧ mkC kerThree ∈ coverπ.ker ∧
      mkC kerThree ^ 3 = 1 ∧ mkC kerTwo ^ 2 = 1 ∧ mkC kerTwo' ^ 2 = 1 ∧ mkC kerTwo ≠ 1 ∧
      mkC kerTwo' ≠ 1 := by
  obtain ⟨E, _, ψ, hfix, hmove⟩ := kernel_hom
  have hfin : Finite Cover := cover_card_le.1
  have hrel : ∀ r ∈ rels, mkC r ∈ coverπ.ker := fun r hr => by
    rw [MonoidHom.mem_ker, coverπ_mk]
    exact lift_genE_rels_eq_one hr
  have hz₃ : mkC kerThree ∈ coverπ.ker := hrel _ kerThree_mem_rels
  have hz₂ : mkC kerTwo ∈ coverπ.ker := hrel _ kerTwo_mem_rels
  have hz₂' : mkC kerTwo' ∈ coverπ.ker := by
    rw [kerTwo', mkC_append, mkC_append]
    have h6 := hrel kerSix kerSix_mem_rels
    exact mul_mem (mul_mem h6 h6) h6
  have fx : ∀ u ∈ fixWords, ψ (mkC u) = 1 := hfix
  have mv : ∀ u ∈ moveWords, ψ (mkC u) ≠ 1 := hmove
  have f₃ : ψ (mkC kerThree) ^ 3 = 1 := by
    have := fx _ (List.mem_cons_self ..)
    rwa [mkC_append, mkC_append, map_mul, map_mul, ← pow_three'] at this
  have f₂ : ψ (mkC kerTwo) ^ 2 = 1 := by
    have := fx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rwa [mkC_append, map_mul, ← sq] at this
  have f₂' : ψ (mkC kerTwo') ^ 2 = 1 := by
    have := fx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    rwa [mkC_append, map_mul, ← sq] at this
  have m₃ : ψ (mkC kerThree) ≠ 1 := mv _ (List.mem_cons_self ..)
  have m₂ : ψ (mkC kerTwo) ≠ 1 := mv _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have m₂' : ψ (mkC kerTwo') ≠ 1 :=
    mv _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have m₂₂ : ψ (mkC kerTwo) * ψ (mkC kerTwo') ≠ 1 := by
    have := mv _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
    rwa [mkC_append, map_mul] at this
  have hcomm : ∀ a ∈ coverπ.ker, ∀ b ∈ coverπ.ker, Commute (ψ a) (ψ b) := fun a _ b hb =>
    (show Commute a b from mem_center_iff.1 (ker_coverπ_le_center hb) a).map ψ
  obtain ⟨φ, hφ, hrange⟩ := exists_injective_three_two_two (hcomm _ hz₂ _ hz₂')
    (hcomm _ hz₃ _ hz₂) (hcomm _ hz₃ _ hz₂') f₂ f₂' f₃ m₂ m₂' m₂₂ m₃
  set K := closure ({mkC kerTwo, mkC kerTwo', mkC kerThree} : Set Cover)
  have hKker : K ≤ coverπ.ker := by
    rw [closure_le]
    rintro _ (rfl | rfl | rfl)
    exacts [hz₂, hz₂', hz₃]
  have hφK : φ.range ≤ K.map ψ := hrange _
    (mem_map_of_mem _ (subset_closure (Set.mem_insert _ _)))
    (mem_map_of_mem _ (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
    (mem_map_of_mem _ (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _)))))
  have hcardφ : Nat.card φ.range = 12 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    simp
  have hM := card_ker_coverπ_le
  have hs : Function.Surjective
      (fun x : coverπ.ker => (⟨ψ x, x, x.2, rfl⟩ : coverπ.ker.map ψ)) :=
    fun ⟨_, x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have : Finite (coverπ.ker.map ψ) := Finite.of_surjective _ hs
  have hge : Nat.card coverπ.ker ≤ Nat.card (coverπ.ker.map ψ) := by
    have : φ.range ≤ coverπ.ker.map ψ := hφK.trans (map_mono hKker)
    have h12 := Subgroup.card_le_of_le this
    omega
  have hbij := hs.bijective_of_nat_card_le hge
  have hinj : ∀ a ∈ coverπ.ker, ∀ b ∈ coverπ.ker, ψ a = ψ b → a = b := fun a ha b hb hab => by
    have := hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext hab)
    exact congrArg Subtype.val this
  refine ⟨fun x hx => ?_, hz₂, hz₂', hz₃, ?_, ?_, ?_, fun h => m₂ (by rw [h, map_one]),
    fun h => m₂' (by rw [h, map_one])⟩
  ·
    have hmap : coverπ.ker.map ψ ≤ K.map ψ := by
      have hc1 : Nat.card (coverπ.ker.map ψ) ≤ 12 :=
        (Nat.card_le_card_of_surjective _ hs).trans hM
      have heq : φ.range = coverπ.ker.map ψ :=
        eq_of_le_of_card_ge (hφK.trans (map_mono hKker)) (by omega)
      rw [← heq]
      exact hφK
    obtain ⟨y, hy, hxy⟩ := hmap (mem_map_of_mem ψ hx)
    rw [hinj x hx y (hKker hy) hxy.symm]
    exact hy
  · exact hinj _ (pow_mem hz₃ 3) _ (one_mem _) (by rw [map_pow, f₃, map_one])
  · exact hinj _ (pow_mem hz₂ 2) _ (one_mem _) (by rw [map_pow, f₂, map_one])
  · exact hinj _ (pow_mem hz₂' 2) _ (one_mem _) (by rw [map_pow, f₂', map_one])

theorem exists_eq_zWord_of_mem_ker
    {x : Cover} (hx : x ∈ coverπ.ker) :
    ∃ a < 3, ∃ b < 2, ∃ c < 2, x = mkC (zWord a b c) := by
  obtain ⟨hgen, hz₂, hz₂', hz₃, h3, h2, h2', -, -⟩ := cover_kernel_facts
  have hc : ∀ a ∈ coverπ.ker, ∀ b ∈ coverπ.ker, Commute a b := fun a _ b hb =>
    mem_center_iff.1 (ker_coverπ_le_center hb) a
  let φ₂ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* Cover :=
    (powHom (mkC kerTwo) 2 h2).noncommCoprod (powHom (mkC kerTwo') 2 h2') fun a b => by
      simp only [powHom_apply]
      exact ((hc _ hz₂ _ hz₂').pow_left _).pow_right _
  let φ₃ : Multiplicative (ZMod 3) × (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) →*
      Cover :=
    (powHom (mkC kerThree) 3 h3).noncommCoprod φ₂ fun a b => by
      simp only [powHom_apply]
      exact (((hc _ hz₃ _ hz₂).pow_right _).mul_right ((hc _ hz₃ _ hz₂').pow_right _)).pow_left _
  have hφ : ∀ d, φ₃ d = mkC kerThree ^ d.1.toAdd.val *
      (mkC kerTwo ^ d.2.1.toAdd.val * mkC kerTwo' ^ d.2.2.toAdd.val) := fun _ => rfl
  have hle : closure ({mkC kerTwo, mkC kerTwo', mkC kerThree} : Set Cover) ≤ φ₃.range := by
    rw [closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨(1, Multiplicative.ofAdd 1, 1), by
        rw [hφ]; simp [show ZMod.val (1 : ZMod 2) = 1 from rfl]⟩
    · exact ⟨(1, 1, Multiplicative.ofAdd 1), by
        rw [hφ]; simp [show ZMod.val (1 : ZMod 2) = 1 from rfl]⟩
    · exact ⟨(Multiplicative.ofAdd 1, 1, 1), by
        rw [hφ]; simp [show ZMod.val (1 : ZMod 3) = 1 from rfl]⟩
  obtain ⟨d, hd⟩ := hle (hgen x hx)
  refine ⟨d.1.toAdd.val, ZMod.val_lt _, d.2.1.toAdd.val, ZMod.val_lt _, d.2.2.toAdd.val,
    ZMod.val_lt _, ?_⟩
  rw [← hd, hφ, mkC_zWord]

theorem eq_zWord_of_exclWords
    {E : Type*} [Group E] (ψ : Cover →* E) {u : List (Fin 5 × Bool)}
    (hu : mkC u ∈ coverπ.ker) (t : ℕ × ℕ × ℕ)
    (hmove : ∀ v ∈ exclWords u t, ψ (mkC v) ≠ 1) :
    mkC u = mkC (zWord t.1 t.2.1 t.2.2) := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := exists_eq_zWord_of_mem_ker hu
  by_cases ht : (a, b, c) = t
  · subst ht
    exact habc
  · exfalso
    have hmem : (a, b, c) ∈ zTriples := by
      interval_cases a <;> interval_cases b <;> interval_cases c <;> decide
    have hv := hmove _ (List.mem_map_of_mem (List.mem_filter.2 ⟨hmem, by simpa using ht⟩))
    apply hv
    rw [mkC_append, mkC_invRev, ← habc, mul_inv_cancel, map_one]

theorem cover_delta_facts
    :
    mkC muWord = 1 ∧ mkC deltaKerTwo = mkC kerTwo * mkC kerTwo' ∧
      mkC deltaKerSix = mkC kerThree ^ 2 * mkC kerTwo := by
  obtain ⟨E, _, ψ, hmove⟩ := obs_check
  have mv : ∀ u ∈ obsMoveWords, ψ (mkC u) ≠ 1 := hmove
  have hμ : mkC muWord ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, coverπ_mk, muWord, ← FreeGroup.mul_mk, map_mul,
      lift_genE_substWord_delta, lift_genE_comm, diagonalAut_genE]
    change FreeGroup.lift genE (FreeGroup.of 2 * FreeGroup.of 4 * (FreeGroup.of 2)⁻¹) *
      FreeGroup.lift genE (FreeGroup.of 2 * (FreeGroup.of 4)⁻¹ * (FreeGroup.of 2)⁻¹) = 1
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    group
  have hA : mkC deltaKerTwo ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, coverπ_mk, deltaKerTwo, lift_genE_substWord_delta,
      lift_genE_rels_eq_one kerTwo_mem_rels, map_one]
  have hB : mkC deltaKerSix ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, coverπ_mk, deltaKerSix, lift_genE_substWord_delta,
      lift_genE_rels_eq_one kerSix_mem_rels, map_one]
  refine ⟨?_, ?_, ?_⟩
  · have := eq_zWord_of_exclWords ψ hμ (0, 0, 0) fun v hv =>
      mv v (List.mem_append_left _ (List.mem_append_left _ hv))
    rw [this]
    rfl
  · have := eq_zWord_of_exclWords ψ hA (0, 1, 1) fun v hv =>
      mv v (List.mem_append_left _ (List.mem_append_right _ hv))
    rw [this, mkC_zWord]
    simp
  · have := eq_zWord_of_exclWords ψ hB (2, 1, 0) fun v hv => mv v (List.mem_append_right _ hv)
    rw [this, mkC_zWord]
    simp

private theorem eq_of_ne_one_of_card_eq_two {H : Type*} [Group H] (h2 : Nat.card H = 2)
    {a b : H} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : H)).1 h2
  rw [hy a ha, hy b hb]

private theorem hom_mkC_eq_lift {L : Type*} [Group L] (h : Cover →* L)
    (v : List (Fin 5 × Bool)) :
    h (mkC v) = FreeGroup.lift (fun i => h (PresentedGroup.of i)) (FreeGroup.mk v) := by
  rw [mkC, ← MonoidHom.comp_apply]
  exact DFunLike.congr_fun (FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    rfl) _

theorem mkC_obsWordA'
    : mkC obsWordA' = mkC kerTwo * mkC kerTwo' := by
  rw [obsWordA', obsWordA, mkC_substWord_delta_commGenWords cover_delta_facts.1,
    ← deltaKerTwo, cover_delta_facts.2.1]

theorem mkC_obsWordB'
    : mkC obsWordB' = mkC kerThree ^ 2 * mkC kerTwo := by
  rw [obsWordB', obsWordB, mkC_substWord_delta_commGenWords cover_delta_facts.1,
    ← deltaKerSix, cover_delta_facts.2.2]

theorem not_lift_diagonal
    {L : Type*} [Group L] [Group.IsPerfect L] (q : L →* T46)
    (hq : Function.Surjective q) (hker : q.ker = center L) (h2 : Nat.card (center L) = 2)
    (α : MulAut L) (t : T46) (hα : ∀ x, q (α x) = diagonalAut (t * q x * t⁻¹)) : False := by
  obtain ⟨h, hhs, hhq⟩ := exists_cover_hom q hq hker.le
  obtain ⟨hgen, -, -, hz₃, h3, -, -, -, -⟩ := cover_kernel_facts
  set ℓ : Fin 5 → L := fun i => h (PresentedGroup.of i)
  have hℓ : ∀ i, q (ℓ i) = genE i := fun i => by
    change q (h (PresentedGroup.of i)) = _
    rw [hhq]
    exact coverπ_mk (FreeGroup.of i) |>.trans (FreeGroup.lift_apply_of)
  have h2' : Nat.card q.ker = 2 := by rw [hker]; exact h2
  have hfix : ∀ z ∈ q.ker, α z = z := fun z hz => by
    by_cases hz1 : z = 1
    · rw [hz1, map_one]
    have hαz : α z ∈ q.ker := by
      rw [MonoidHom.mem_ker, hα, MonoidHom.mem_ker.1 hz, mul_one, mul_inv_cancel, map_one]
    have e := eq_of_ne_one_of_card_eq_two h2' (a := ⟨α z, hαz⟩) (b := ⟨z, hz⟩)
      (fun h' => hz1 (α.injective ((congrArg Subtype.val h').trans (map_one α).symm)))
      (fun h' => hz1 (congrArg Subtype.val h'))
    exact congrArg Subtype.val e
  have hδ : ∀ i, diagonalAut.toMonoidHom (genE i) =
      FreeGroup.lift genE (FreeGroup.mk (deltaWords.getD i [])) := diagonalAut_genE
  have key := fun (w : List (Fin 5 × Bool)) =>
    lift_eq_lift_substWord_of_lift q hq hker.le genE deltaWords diagonalAut.toMonoidHom hδ ℓ hℓ
      α.toMonoidHom hfix t hα w
  have eA : h (mkC obsWordA) = h (mkC obsWordA') := by
    rw [hom_mkC_eq_lift, hom_mkC_eq_lift]
    exact key obsWordA (mk_substWord_commGenWords_mem_commutator _) lift_genE_obsWordA
  have eB : h (mkC obsWordB) = h (mkC obsWordB') := by
    rw [hom_mkC_eq_lift, hom_mkC_eq_lift]
    exact key obsWordB (mk_substWord_commGenWords_mem_commutator _) lift_genE_obsWordB
  rw [obsWordA, mkC_substWord_commGenWords, mkC_obsWordA', map_mul] at eA
  rw [obsWordB, mkC_substWord_commGenWords, mkC_obsWordB', map_mul, map_pow] at eB
  have hcen : ∀ x ∈ coverπ.ker, h x ∈ center L := fun x hx => by
    rw [← hker, MonoidHom.mem_ker, hhq, MonoidHom.mem_ker.1 hx]
  have hsq : ∀ x ∈ coverπ.ker, h x ^ 2 = 1 := fun x hx => by
    have := pow_card_eq_one' (G := center L) (x := ⟨_, hcen x hx⟩)
    rw [h2] at this
    simpa using congrArg Subtype.val this
  have h31 : h (mkC kerThree) = 1 := by
    have hcube : h (mkC kerThree) ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    calc h (mkC kerThree) = h (mkC kerThree) ^ 3 * (h (mkC kerThree) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hcube, hsq _ hz₃, inv_one, mul_one]
  have hz₆ : mkC kerSix ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, coverπ_mk]
    exact lift_genE_rels_eq_one kerSix_mem_rels
  have h2'6 : h (mkC kerTwo') = h (mkC kerSix) := by
    rw [kerTwo', mkC_append, mkC_append, map_mul, map_mul, ← sq, hsq _ hz₆, one_mul]
  have h2'1 : h (mkC kerTwo') = 1 := by
    rwa [left_eq_mul] at eA
  have h21 : h (mkC kerTwo) = 1 := by
    rw [h31, one_pow, one_mul, ← h2'6, h2'1] at eB
    exact eB.symm
  have hK : ∀ x ∈ coverπ.ker, h x = 1 := fun x hx => by
    have hle : closure ({mkC kerTwo, mkC kerTwo', mkC kerThree} : Set Cover) ≤ h.ker := by
      rw [closure_le]
      rintro _ (rfl | rfl | rfl)
      exacts [h21, h2'1, h31]
    exact hle (hgen x hx)
  obtain ⟨z, hz⟩ : ∃ z : center L, z ≠ 1 := by
    obtain ⟨y, hy, -⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 h2
    exact ⟨y, hy⟩
  obtain ⟨p, hp⟩ := hhs (z : L)
  have hpk : p ∈ coverπ.ker := by
    rw [MonoidHom.mem_ker, ← hhq, hp, ← MonoidHom.mem_ker, hker]
    exact z.2
  exact hz (Subtype.ext ((hp.symm.trans (hK p hpk)).trans rfl))

theorem diagonalAut_not_mem_inner
    : diagonalAut ∉ inner T46 := by
  rintro ⟨t, ht⟩
  obtain ⟨-, -, -, -, -, -, -, -, hne'⟩ := cover_kernel_facts
  obtain ⟨t', rfl⟩ := coverπ_surjective t
  have hδ : ∀ i, diagonalAut.toMonoidHom (genE i) =
      FreeGroup.lift genE (FreeGroup.mk (deltaWords.getD i [])) := diagonalAut_genE
  have hℓ : ∀ i, coverπ (PresentedGroup.of i) = genE i := fun i =>
    (coverπ_mk (FreeGroup.of i)).trans FreeGroup.lift_apply_of
  have hfix : ∀ z ∈ coverπ.ker, (MulAut.conj t').toMonoidHom z = z := fun z hz => by
    change t' * z * t'⁻¹ = z
    rw [mem_center_iff.1 (ker_coverπ_le_center hz) t', mul_inv_cancel_right]
  have hα : ∀ x, coverπ ((MulAut.conj t').toMonoidHom x) =
      diagonalAut.toMonoidHom (1 * coverπ x * 1⁻¹) := fun x => by
    rw [← ht]
    simp
  have key := lift_eq_lift_substWord_of_lift coverπ coverπ_surjective ker_coverπ_le_center genE
    deltaWords diagonalAut.toMonoidHom hδ _ hℓ _ hfix 1 hα obsWordA
    (mk_substWord_commGenWords_mem_commutator _) lift_genE_obsWordA
  rw [mkC_lift_of, mkC_lift_of, ← obsWordA', mkC_obsWordA', obsWordA,
    mkC_substWord_commGenWords, left_eq_mul] at key
  exact hne' key

theorem orderOf_mk_diagonalAut
    : orderOf (QuotientGroup.mk diagonalAut : Outer T46) = 3 := by
  apply orderOf_eq_prime
  · rw [← QuotientGroup.mk_pow, diagonalAut_pow_three, QuotientGroup.mk_one]
  · intro h
    exact diagonalAut_not_mem_inner ((QuotientGroup.eq_one_iff _).1 h)

theorem card_outer_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSU 6 2 1) : Nat.card (Outer Q) = 6 := by
  rcases hQ with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have := (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound Q 6 2 1
      hM).2.2.1
    rw [this]
    norm_num
  all_goals exact absurd h0 (by norm_num)

theorem card_le_two_of_not_mem {O : Type*} [Group O] (hO : Nat.card O = 6) (I : Subgroup O)
    {d : O} (hd3 : d ^ 3 = 1) (hd : d ∉ I) : Nat.card I ≤ 2 := by
  have : Finite O := Nat.finite_of_card_ne_zero (by rw [hO]; norm_num)
  have hd1 : d ≠ 1 := fun h => hd (h ▸ one_mem I)
  set D := zpowers d
  have hD : Nat.card D = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hinf : ∀ x ∈ I, x ∈ D → x = 1 := by
    intro x hxI hxD
    by_contra hx1
    have hxD' : zpowers x ≤ D := zpowers_le.2 hxD
    have hcard : Nat.card (zpowers x) = 3 := by
      have hdvd : Nat.card (zpowers x) ∣ 3 := hD ▸ Subgroup.card_dvd_of_le hxD'
      rw [Nat.card_zpowers] at hdvd ⊢
      rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx1
      · exact h
    have heq : zpowers x = D := eq_of_le_of_card_ge hxD' (by rw [hcard, hD])
    exact hd ((zpowers_le.2 hxI) (heq ▸ mem_zpowers d))
  have hinj : Function.Injective (fun p : I × D => (p.1 : O) * p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only at hab
    have h1 : (a' : O)⁻¹ * a = b' * (b : O)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hab, mul_inv_cancel_right]
    have hI : (a' : O)⁻¹ * a ∈ I := mul_mem (inv_mem a'.2) a.2
    have hD' : (a' : O)⁻¹ * a ∈ D := h1 ▸ mul_mem b'.2 (inv_mem b.2)
    have e := hinf _ hI hD'
    have ha : a = a' := Subtype.ext (by rw [inv_mul_eq_one] at e; exact e.symm)
    have hb : b = b' := Subtype.ext (by
      rw [e] at h1
      exact (mul_inv_eq_one.1 h1.symm).symm)
    rw [ha, hb]
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hD, hO] at h
  omega

@[expose] noncomputable def outerToT46
    {L : Type*} [Group L] (e : L ⧸ center L ≃* T46) :
    Outer L →* Outer T46 :=
  (equivalence e).toMonoidHom.comp (centerQuotientOuterHom L)

theorem outerToT46_injective
    {L : Type*} [Group L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* T46) : Function.Injective (outerToT46 e) :=
  (equivalence e).injective.comp (centerQuotient_outer_injective L)

theorem outerToT46_mk
    {L : Type*} [Group L] (e : L ⧸ center L ≃* T46) (α : MulAut L) :
    outerToT46 e (QuotientGroup.mk α) =
      QuotientGroup.mk (MulAut.congr e (centerQuotientHom L α)) := rfl

theorem not_mem_range_outer_diagonal
    {L : Type*} [Group L] [Group.IsPerfect L]
    (h2 : Nat.card (center L) = 2) (e : L ⧸ center L ≃* T46) :
    (QuotientGroup.mk diagonalAut : Outer T46) ∉ (outerToT46 e).range := by
  rintro ⟨o, ho⟩
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective o
  rw [outerToT46_mk] at ho
  obtain ⟨t, ht⟩ := (QuotientGroup.eq.1 ho)
  set β := MulAut.congr e (centerQuotientHom L α)
  let q : L →* T46 := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hq : Function.Surjective q :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center L))
  have hker : q.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center L) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hβ : diagonalAut = β * MulAut.conj t := by
    rw [ht, mul_inv_cancel_left]
  have hα : ∀ x, q (α x) = diagonalAut (t⁻¹ * q x * t⁻¹⁻¹) := fun x => by
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply]
    simp only [mul_assoc, inv_inv, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    change e (QuotientGroup.mk' (center L) (α x)) =
      e (onCenterQuotient α (e.symm (e (QuotientGroup.mk' (center L) x))))
    rw [MulEquiv.symm_apply_apply, onCenterQuotient_apply_mk]
  exact not_lift_diagonal q hq hker h2 α t⁻¹ hα

theorem card_outer_le_two
    {L : Type} [Group L] [Group.IsPerfect L]
    (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    Finite (Outer L) ∧ Nat.card (Outer L) ≤ 2 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_T46 hQ
  have h6 : Nat.card (Outer T46) = 6 := by
    rw [← Nat.card_congr (equivalence e).toEquiv]
    exact card_outer_of_lieModel hQ
  have hfin : Finite (Outer T46) := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  refine ⟨Finite.of_injective _ (outerToT46_injective e), ?_⟩
  rw [Nat.card_congr (MonoidHom.ofInjective (outerToT46_injective e)).toEquiv]
  refine card_le_two_of_not_mem h6 _ ?_ (not_mem_range_outer_diagonal h2 e)
  rw [← QuotientGroup.mk_pow, diagonalAut_pow_three, QuotientGroup.mk_one]

theorem relIndex_sup_inf_centralizer_le_two
    {G : Type} [Group G] {L N : Subgroup G}
    (hLN : L ≤ N) (hN : N ≤ normalizer (L : Set G)) [Group.IsPerfect L]
    (h2 : Nat.card (center L) = 2)
    (hQ : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    (L ⊔ N ⊓ centralizer (L : Set G)).relIndex N ≤ 2 ∧
      (L ⊔ N ⊓ centralizer (L : Set G)).relIndex N ≠ 0 := by
  obtain ⟨hfin, hcard⟩ := card_outer_le_two h2 hQ
  set ρ : N →* Outer L :=
    (QuotientGroup.mk' (inner L)).comp ((normalizerMonoidHom L).comp (inclusion hN))
  have hker : ρ.ker ≤ (L ⊔ N ⊓ centralizer (L : Set G)).subgroupOf N := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn
    obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).1 hn
    have hc : (l : G)⁻¹ * n ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have := congrArg Subtype.val (DFunLike.congr_fun hl ⟨x, hx⟩)
      simp only [MulAut.conj_apply, MonoidHom.comp_apply, normalizerMonoidHom_apply_apply_coe,
        coe_inclusion, coe_mul, coe_inv] at this
      calc x * ((l : G)⁻¹ * n) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * n := by group
        _ = (l : G)⁻¹ * (n * x * (n : G)⁻¹) * n := by rw [this]
        _ = (l : G)⁻¹ * n * x := by group
    rw [mem_subgroupOf]
    have : (n : G) = (l : G) * ((l : G)⁻¹ * n) := by group
    rw [this]
    exact mul_mem_sup l.2 (mem_inf.2 ⟨mul_mem (inv_mem (hLN l.2)) n.2, hc⟩)
  have hidx : ρ.ker.index ≤ 2 := by
    rw [index_ker]
    exact (card_le_card_group _).trans hcard
  have hne : ρ.ker.index ≠ 0 := by
    rw [index_ker]
    exact Nat.card_pos.ne'
  have hdvd : ((L ⊔ N ⊓ centralizer (L : Set G)).subgroupOf N).index ∣ ρ.ker.index :=
    index_dvd_of_le hker
  refine ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd).trans hidx, fun h0 => ?_⟩
  have h0' : ((L ⊔ N ⊓ centralizer (L : Set G)).subgroupOf N).index = 0 := h0
  rw [h0'] at hdvd
  exact hne (Nat.eq_zero_of_zero_dvd hdvd)

end CFSG.EvenSmallLie.UnitarySix
