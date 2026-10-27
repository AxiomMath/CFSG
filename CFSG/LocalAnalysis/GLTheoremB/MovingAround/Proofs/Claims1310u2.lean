module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310u
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310t
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Dim
public import Certificates.Certificate231801

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

open Module
open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration.ExcWideThree (TwLangData twPlanePre diagG diagG_apply twistedTorus_le
  mem_twPlanePre_iff card_twPlanePre ringChar_eq_of_card_pow exists_twLangData exists_twE6HeisenbergFrame
  twE6HeisFrameNormalizesR_of_fixedElt twE6HeisFrameFixedElt_holds)
open CFSG.LieType.SeitzGeneration.ExcHighThree (rootCharHom exists_rootDiagUnit_of_mem_torusGroup
  twE6KillRoot_proof)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (twistedE6InndiagGL twistedE6InndiagConj
  twistedE6InndiagConj_apply twistedE6InndiagConj_injective range_twistedE6InndiagConj
  exists_cubeExt twistedE6PlaneToralLang_proved)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (TwistedE6DiagIsotropic)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (finrank_ker_rootDiag_sub_one_card
  finrank_ker_baseChangeEnd finrank_ker_conj_sub_one baseChangeEnd_sub_aux baseChangeEnd_one_aux)

set_option linter.unusedSectionVars false

section IndexNineDef

@[expose] def TwE6TwoStarIndexNine : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 2 ^ 2 → (∀ c, σ c = c ^ 2) →
    ∀ D : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), IsElemAbelian 3 D →
      ∃ E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), E ≤ D ∧ Nat.card D ≤ 9 * Nat.card E ∧
        ∃ V : Subgroup ↥(twistedE6RootGroup K σ), V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧
          ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V

end IndexNineDef

section Syl3Arr

@[expose] def syl3OfArr (a : Array ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun r c => a.getD (6 * r.val + c.val) 0

@[expose] def syl3Refl (k : Fin 6) : Matrix (Fin 6) (Fin 6) ℤ :=
  syl3OfArr (syl3ReflArr k.val)

@[expose] def syl3GenMat (k : Fin 4) : Matrix (Fin 6) (Fin 6) ℤ :=
  syl3OfArr (syl3GenArr.getD k.val #[])

@[expose] def syl3Mat (i : Fin 81) : Matrix (Fin 6) (Fin 6) ℤ :=
  syl3OfArr (syl3MatsArr.getD i.val #[])

@[expose] def syl3Vec (n : ℕ) : Fin 6 → ZMod 3 :=
  fun r => (((syl3VecArr n).getD r.val 0 : ℤ) : ZMod 3)

@[expose] def syl3Code (x : Fin 6 → ZMod 3) : ℕ :=
  (x 0).val + 3 * (x 1).val + 9 * (x 2).val + 27 * (x 3).val + 81 * (x 4).val + 243 * (x 5).val

@[expose] def syl3FixList (i : Fin 81) : List ℕ :=
  (syl3FixCodesW syl3MatsArr).getD i.val []

theorem syl3_getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (d : α) {e : ℕ} (he : e < n) :
    (Array.ofFn f).getD e d = f ⟨e, he⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos he, Option.getD_some]

theorem syl3Tabulate_getD {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (syl3Tabulate f).getD i.val d = f i := by
  simp [syl3Tabulate, Array.getD_eq_getD_getElem?]

theorem syl3OfArr_mul (a b : Array ℤ) : syl3OfArr (syl3MulArr a b) = syl3OfArr a * syl3OfArr b := by
  ext r c
  have hlt : 6 * r.val + c.val < 36 := by omega
  have h1 : (6 * r.val + c.val) / 6 = r.val := by omega
  have h2 : (6 * r.val + c.val) % 6 = c.val := by omega
  rw [Matrix.mul_apply, Fin.sum_univ_six]
  simp only [syl3OfArr, Matrix.of_apply, syl3MulArr]
  rw [syl3_getD_ofFn _ _ hlt]
  simp only [h1, h2]
  rfl

theorem syl3OfArr_one : syl3OfArr syl3OneArr = 1 := by
  ext r c
  have hlt : 6 * r.val + c.val < 36 := by omega
  have h1 : (6 * r.val + c.val) / 6 = r.val := by omega
  have h2 : (6 * r.val + c.val) % 6 = c.val := by omega
  simp only [syl3OfArr, Matrix.of_apply, syl3OneArr]
  rw [syl3_getD_ofFn _ _ hlt]
  simp only [h1, h2, Matrix.one_apply, Fin.val_inj]

theorem syl3_foldr_eq_prod {ι : Type} (f : ι → Array ℤ) (l : List ι) :
    syl3OfArr (l.foldr (fun a M => syl3MulArr (f a) M) syl3OneArr) =
      (l.map fun a => syl3OfArr (f a)).prod := by
  induction l with
  | nil => exact syl3OfArr_one
  | cons a l ih => rw [List.foldr_cons, syl3OfArr_mul, ih, List.map_cons, List.prod_cons]

theorem syl3Vec_code (x : Fin 6 → ZMod 3) : syl3Vec (syl3Code x) = x := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  have h3 := ZMod.val_lt (x 3)
  have h4 := ZMod.val_lt (x 4)
  have h5 := ZMod.val_lt (x 5)
  have key : ∀ (m : ℕ) (y : ZMod 3), m = y.val → (((m : ℤ)) : ZMod 3) = y := fun m y h => by
    rw [h, Int.cast_natCast, ZMod.natCast_zmod_val]
  funext r
  obtain ⟨r, hr⟩ := r
  interval_cases r
  · show ((((syl3Code x % 3 : ℕ) : ℤ)) : ZMod 3) = x 0
    exact key _ _ (by simp only [syl3Code]; omega)
  · show ((((syl3Code x / 3 % 3 : ℕ) : ℤ)) : ZMod 3) = x 1
    exact key _ _ (by simp only [syl3Code]; omega)
  · show ((((syl3Code x / 9 % 3 : ℕ) : ℤ)) : ZMod 3) = x 2
    exact key _ _ (by simp only [syl3Code]; omega)
  · show ((((syl3Code x / 27 % 3 : ℕ) : ℤ)) : ZMod 3) = x 3
    exact key _ _ (by simp only [syl3Code]; omega)
  · show ((((syl3Code x / 81 % 3 : ℕ) : ℤ)) : ZMod 3) = x 4
    exact key _ _ (by simp only [syl3Code]; omega)
  · show ((((syl3Code x / 243 % 3 : ℕ) : ℤ)) : ZMod 3) = x 5
    exact key _ _ (by simp only [syl3Code]; omega)

theorem syl3Code_lt (x : Fin 6 → ZMod 3) : syl3Code x < 729 := by
  have h0 := ZMod.val_lt (x 0)
  have h1 := ZMod.val_lt (x 1)
  have h2 := ZMod.val_lt (x 2)
  have h3 := ZMod.val_lt (x 3)
  have h4 := ZMod.val_lt (x 4)
  have h5 := ZMod.val_lt (x 5)
  simp only [syl3Code]
  omega

theorem syl3Code_injective : Function.Injective syl3Code := fun x y h => by
  rw [← syl3Vec_code x, ← syl3Vec_code y, h]

theorem syl3FixArr_of_fix (a : Array ℤ) (n : ℕ)
    (h : ∀ c : Fin 6, ∑ r : Fin 6, syl3Vec n r * ((syl3OfArr a r c : ℤ) : ZMod 3) = syl3Vec n c) :
    syl3FixArr a (syl3VecArr n) = true := by
  unfold syl3FixArr
  rw [List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  rw [decide_eq_true_eq]
  have hc' := h ⟨c, hc⟩
  rw [Fin.sum_univ_six] at hc'
  apply Int.emod_eq_zero_of_dvd
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 ?_
  rw [Int.cast_sub, Int.cast_add, Int.cast_add, Int.cast_add, Int.cast_add, Int.cast_add, Int.cast_mul,
    Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul, sub_eq_zero]
  exact hc'

theorem syl3MulIdxW_eq (i j : Fin 81) : syl3MulIdxW syl3TabArr syl3GenWordArr i j = syl3MulIdx i j :=
  rfl

theorem syl3Check_spec (h : syl3Check () = true) :
    (∀ k, syl3GenMat k = ((syl3SimpleWord k).map syl3Refl).prod) ∧
    (∀ i, syl3Mat i = ((syl3GenWord i).map syl3GenMat).prod) ∧
    (∀ i k, syl3Mat i * syl3GenMat k = syl3Mat (syl3Tab i k)) ∧
    (∀ k, syl3GenMat k * syl3GenMat (syl3Inv k) = 1) ∧
    (∀ i j, syl3Mat i = syl3Mat j → i = j) ∧
    (∃ i j, syl3MulIdx i j ≠ syl3MulIdx j i) ∧
    (∀ i j, syl3Ord3W syl3TabArr syl3GenWordArr i = true → syl3Ord3W syl3TabArr syl3GenWordArr j = true →
      syl3CommW syl3TabArr syl3GenWordArr i j = true → syl3IndepW syl3TabArr syl3GenWordArr i j = true →
        ((syl3FixList i).filter fun n => syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n)).length ≤ 9) ∧
    (∀ i j k, syl3Ord3W syl3TabArr syl3GenWordArr i = true → syl3Ord3W syl3TabArr syl3GenWordArr j = true →
      syl3CommW syl3TabArr syl3GenWordArr i j = true → syl3IndepW syl3TabArr syl3GenWordArr i j = true →
      syl3Ord3W syl3TabArr syl3GenWordArr k = true → syl3CommW syl3TabArr syl3GenWordArr i k = true →
      syl3CommW syl3TabArr syl3GenWordArr j k = true → syl3OutW syl3TabArr syl3GenWordArr i j k = true →
        (((syl3FixList i).filter fun n => syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n)).filter
          fun n => syl3FixArr (syl3MatsArr.getD k.val #[]) (syl3VecArr n)).length ≤ 3) := by
  simp only [syl3Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hGen, hElt⟩, hTab⟩, hInv⟩, hDist⟩, hNonab⟩, hP1⟩, hP2⟩ := h
  unfold syl3CheckGen at hGen
  unfold syl3CheckElt at hElt
  unfold syl3CheckTab at hTab
  unfold syl3CheckInv at hInv
  unfold syl3CheckDistinct at hDist
  unfold syl3CheckNonab at hNonab
  unfold syl3CheckP1 at hP1
  unfold syl3CheckP2 at hP2
  refine ⟨fun k => ?_, fun i => ?_, fun i k => ?_, fun k => ?_, fun i j hij => ?_, ?_,
    fun i j hi hj hc hd => ?_, fun i j k hi hj hc hd hk hik hjk hout => ?_⟩
  · have := (List.all_eq_true.1 hGen) k (List.mem_finRange k)
    rw [decide_eq_true_eq] at this
    rw [syl3GenMat, this, syl3_foldr_eq_prod]
    rfl
  · have := (List.all_eq_true.1 hElt) i (List.mem_finRange i)
    rw [decide_eq_true_eq] at this
    rw [syl3Mat, this, syl3_foldr_eq_prod, syl3GenWordArr, syl3Tabulate_getD]
    rfl
  · have := (List.all_eq_true.1 ((List.all_eq_true.1 hTab) i (List.mem_finRange i))) k
      (List.mem_finRange k)
    rw [decide_eq_true_eq] at this
    rw [syl3Mat, syl3GenMat, ← syl3OfArr_mul, this]
    rfl
  · have := (List.all_eq_true.1 hInv) k (List.mem_finRange k)
    rw [decide_eq_true_eq] at this
    rw [syl3GenMat, syl3GenMat, ← syl3OfArr_mul, this, syl3OfArr_one]
  · by_contra hne
    have := (List.all_eq_true.1 ((List.all_eq_true.1 hDist) i (List.mem_finRange i))) j
      (List.mem_finRange j)
    rw [Bool.or_eq_true, decide_eq_true_eq] at this
    rcases this with h1 | h1
    · exact hne h1
    obtain ⟨e, he, hne'⟩ := List.any_eq_true.1 h1
    rw [List.mem_range] at he
    rw [decide_eq_true_eq] at hne'
    apply hne'
    have h2 := congrFun (congrFun hij ⟨e / 6, by omega⟩) ⟨e % 6, by omega⟩
    have he' : 6 * (e / 6) + e % 6 = e := by omega
    simp only [syl3Mat, syl3OfArr, Matrix.of_apply, he'] at h2
    exact h2
  · obtain ⟨i, -, hi⟩ := List.any_eq_true.1 hNonab
    obtain ⟨j, -, hj⟩ := List.any_eq_true.1 hi
    refine ⟨i, j, ?_⟩
    simpa [syl3CommW, syl3MulIdx] using hj
  · have h1 := (List.all_eq_true.1 hP1) i (List.mem_finRange i)
    simp only [hi, Bool.not_true, Bool.false_or] at h1
    have h2 := (List.all_eq_true.1 h1) j (List.mem_finRange j)
    simp only [hj, hc, hd, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h2
    exact h2
  · have h1 := (List.all_eq_true.1 hP2) i (List.mem_finRange i)
    simp only [hi, Bool.not_true, Bool.false_or] at h1
    have h2 := (List.all_eq_true.1 h1) j (List.mem_finRange j)
    simp only [hj, hc, hd, Bool.and_self, Bool.not_true, Bool.false_or] at h2
    have h3 := (List.all_eq_true.1 h2) k (List.mem_finRange k)
    simp only [hk, hik, hjk, hout, Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h3
    exact h3

end Syl3Arr

section Syl3

open CFSG.LieType.Chevalley (WeylGroup simple simple_smul ext_single weylTuple weylTuple_weylTuple
  weylTuple_one)
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 (torV rootChar_torV)

@[expose] def syl3IdxEquiv : Fin 6 ≃ Fin Tag.E6.rank :=
  finCongr rfl

@[expose] noncomputable def syl3W (w : WeylGroup Tag.E6) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun r c => (w • (Pi.single (syl3IdxEquiv c) 1 : Fin Tag.E6.rank → ℤ)) (syl3IdxEquiv r)

theorem syl3W_smul (w : WeylGroup Tag.E6) (v : Fin Tag.E6.rank → ℤ) (r : Fin 6) :
    (w • v) (syl3IdxEquiv r) = ∑ c : Fin 6, syl3W w r c * v (syl3IdxEquiv c) := by
  have e : ∀ i : Fin Tag.E6.rank, (fun j => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
    intro i
    funext j
    simp [Pi.single_apply, eq_comm]
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [e, Finset.smul_sum]
  rw [Finset.sum_apply]
  symm
  refine Fintype.sum_equiv syl3IdxEquiv _ _ fun c => ?_
  rw [smul_comm, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem syl3W_mul (w w' : WeylGroup Tag.E6) : syl3W (w * w') = syl3W w * syl3W w' := by
  ext r c
  rw [Matrix.mul_apply]
  change ((w * w') • (Pi.single (syl3IdxEquiv c) 1 : Fin Tag.E6.rank → ℤ)) (syl3IdxEquiv r) = _
  rw [mul_smul, syl3W_smul]
  rfl

theorem syl3W_one : syl3W 1 = 1 := by
  ext r c
  change ((1 : WeylGroup Tag.E6) • (Pi.single (syl3IdxEquiv c) 1 : Fin Tag.E6.rank → ℤ))
    (syl3IdxEquiv r) = _
  rw [one_smul, Pi.single_apply, Matrix.one_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]

@[expose] noncomputable def syl3WHom : WeylGroup Tag.E6 →* Matrix (Fin 6) (Fin 6) ℤ where
  toFun := syl3W
  map_one' := syl3W_one
  map_mul' := syl3W_mul

theorem syl3WHom_apply (w : WeylGroup Tag.E6) : syl3WHom w = syl3W w :=
  rfl

theorem syl3W_injective : Function.Injective syl3W := by
  intro w w' h
  refine ext_single fun i => funext fun r => ?_
  obtain ⟨i', rfl⟩ := syl3IdxEquiv.surjective i
  obtain ⟨r', rfl⟩ := syl3IdxEquiv.surjective r
  exact congrFun (congrFun h r') i'

theorem syl3Cartan_eq (k c : Fin 6) :
    Tag.E6.cartan (syl3IdxEquiv k) (syl3IdxEquiv c) = syl3CartanArr.getD (6 * k.val + c.val) 0 := by
  fin_cases k <;> fin_cases c <;> rfl

theorem syl3W_simple (k : Fin 6) : syl3W (simple Tag.E6 (syl3IdxEquiv k)) = syl3Refl k := by
  ext r c
  have hlt : 6 * r.val + c.val < 36 := by omega
  have h1 : (6 * r.val + c.val) / 6 = r.val := by omega
  have h2 : (6 * r.val + c.val) % 6 = c.val := by omega
  change (simple Tag.E6 (syl3IdxEquiv k) • (Pi.single (syl3IdxEquiv c) 1 : Fin Tag.E6.rank → ℤ))
    (syl3IdxEquiv r) = _
  rw [simple_smul]
  simp only [syl3Refl, syl3OfArr, Matrix.of_apply, syl3ReflArr]
  rw [syl3_getD_ofFn _ _ hlt]
  simp only [h1, h2]
  simp only [CFSG.Blueprint.Chevalley.reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.sum_eq_single (syl3IdxEquiv c) (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ _) h), syl3Cartan_eq]
  simp only [EmbeddingLike.apply_eq_iff_eq, if_true, mul_one]
  by_cases hrc : r = c <;> by_cases hrk : r = k <;> simp [hrc, hrk, Fin.val_inj]

@[expose] noncomputable def syl3Gen (k : Fin 4) : WeylGroup Tag.E6 :=
  ((syl3SimpleWord k).map fun s => simple Tag.E6 (syl3IdxEquiv s)).prod

@[expose] noncomputable def syl3Elt (i : Fin 81) : WeylGroup Tag.E6 :=
  ((syl3GenWord i).map syl3Gen).prod

@[expose] noncomputable def syl3Sub : Subgroup (WeylGroup Tag.E6) :=
  Subgroup.closure (Set.range syl3Gen)

theorem syl3W_gen (k : Fin 4) : syl3W (syl3Gen k) = syl3GenMat k := by
  rw [(syl3Check_spec Certificates.certificate231801).1 k, syl3Gen, ← syl3WHom_apply,
    map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun s _ => ?_)
  rw [Function.comp_apply, syl3WHom_apply, syl3W_simple]

theorem syl3W_elt (i : Fin 81) : syl3W (syl3Elt i) = syl3Mat i := by
  rw [(syl3Check_spec Certificates.certificate231801).2.1 i, syl3Elt, ← syl3WHom_apply,
    map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, syl3WHom_apply, syl3W_gen]

theorem syl3Elt_zero : syl3Elt 0 = 1 := by
  have h : syl3GenWord 0 = [] := rfl
  rw [syl3Elt, h, List.map_nil, List.prod_nil]

theorem syl3Elt_mul_gen (i : Fin 81) (k : Fin 4) : syl3Elt i * syl3Gen k = syl3Elt (syl3Tab i k) := by
  apply syl3W_injective
  rw [syl3W_mul, syl3W_elt, syl3W_gen, syl3W_elt,
    (syl3Check_spec Certificates.certificate231801).2.2.1 i k]

theorem syl3Gen_mul_inv (k : Fin 4) : syl3Gen k * syl3Gen (syl3Inv k) = 1 := by
  apply syl3W_injective
  rw [syl3W_mul, syl3W_gen, syl3W_gen, syl3W_one,
    (syl3Check_spec Certificates.certificate231801).2.2.2.1 k]

theorem syl3Elt_injective : Function.Injective syl3Elt := by
  intro i j h
  have := congrArg syl3W h
  rw [syl3W_elt, syl3W_elt] at this
  exact (syl3Check_spec Certificates.certificate231801).2.2.2.2.1 i j this

theorem syl3Elt_foldl (l : List (Fin 4)) (i : Fin 81) :
    syl3Elt (l.foldl (fun m k => syl3Tab m k) i) = syl3Elt i * (l.map syl3Gen).prod := by
  induction l generalizing i with
  | nil => rw [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
  | cons k l ih => rw [List.foldl_cons, ih, ← syl3Elt_mul_gen, List.map_cons, List.prod_cons, mul_assoc]

theorem syl3Elt_mulIdx (i j : Fin 81) : syl3Elt (syl3MulIdx i j) = syl3Elt i * syl3Elt j := by
  rw [syl3MulIdx, syl3MulIdxW, syl3GenWordArr, syl3Tabulate_getD]
  exact syl3Elt_foldl (syl3GenWord j) i

theorem syl3Elt_mem (i : Fin 81) : syl3Elt i ∈ syl3Sub := by
  unfold syl3Elt
  refine Subgroup.list_prod_mem syl3Sub fun x hx => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨k, rfl⟩

theorem mem_syl3Sub_iff {w : WeylGroup Tag.E6} : w ∈ syl3Sub ↔ ∃ i, syl3Elt i = w := by
  refine ⟨fun hw => ?_, fun ⟨i, hi⟩ => hi ▸ syl3Elt_mem i⟩
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨0, syl3Elt_zero⟩
  | mul_right x _ y hy ih =>
    obtain ⟨i, rfl⟩ := ih
    obtain ⟨k, rfl⟩ := hy
    exact ⟨syl3Tab i k, (syl3Elt_mul_gen i k).symm⟩
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨i, rfl⟩ := ih
    obtain ⟨k, rfl⟩ := hy
    have hinv : (syl3Gen k)⁻¹ = syl3Gen (syl3Inv k) := (eq_inv_of_mul_eq_one_right (syl3Gen_mul_inv k)).symm
    exact ⟨syl3Tab i (syl3Inv k), by rw [hinv, syl3Elt_mul_gen]⟩

theorem card_syl3Sub : Nat.card syl3Sub = 81 := by
  have e : (syl3Sub : Set (WeylGroup Tag.E6)) = Set.range syl3Elt := by
    ext w
    simp only [SetLike.mem_coe, mem_syl3Sub_iff, Set.mem_range]
  rw [← SetLike.coe_sort_coe, e, Nat.card_range_of_injective syl3Elt_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem syl3Sub_not_comm : ∃ a ∈ syl3Sub, ∃ b ∈ syl3Sub, a * b ≠ b * a := by
  obtain ⟨i, j, hij⟩ := (syl3Check_spec Certificates.certificate231801).2.2.2.2.2.1
  refine ⟨syl3Elt i, syl3Elt_mem i, syl3Elt j, syl3Elt_mem j, fun h => hij ?_⟩
  apply syl3Elt_injective
  rw [syl3Elt_mulIdx, syl3Elt_mulIdx, h]

theorem weylTuple_torV_eq_iff {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    (w : WeylGroup Tag.E6) (e : Fin Tag.E6.rank → ZMod 3) :
    weylTuple w (torV ω e) = torV ω e ↔
      ∀ c : Fin 6, ∑ r : Fin 6, e (syl3IdxEquiv r) * ((syl3W w⁻¹ r c : ℤ) : ZMod 3) = e (syl3IdxEquiv c) := by
  have key : ∀ c : Fin 6, weylTuple w (torV ω e) (syl3IdxEquiv c) = torV ω e (syl3IdxEquiv c) ↔
      ∑ r : Fin 6, e (syl3IdxEquiv r) * ((syl3W w⁻¹ r c : ℤ) : ZMod 3) = e (syl3IdxEquiv c) := by
    intro c
    have h1 : weylTuple w (torV ω e) (syl3IdxEquiv c) =
        ω ^ (∑ r : Fin 6, ((e (syl3IdxEquiv r)).val : ℤ) * syl3W w⁻¹ r c) := by
      simp only [weylTuple, rootChar_torV]
      rfl
    have h2 : torV ω e (syl3IdxEquiv c) = ω ^ ((((e (syl3IdxEquiv c)).val : ℕ) : ℤ)) := by
      simp only [torV, zpow_natCast]
    rw [h1, h2, zpow_eq_zpow_iff_modEq, hω, ← ZMod.intCast_eq_intCast_iff]
    push_cast
    simp only [ZMod.natCast_zmod_val]
  constructor
  · intro h c
    exact (key c).1 (congrFun h _)
  · intro h
    funext c'
    obtain ⟨c, rfl⟩ := syl3IdxEquiv.surjective c'
    exact (key c).2 (h c)

theorem exists_torV_eq {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    {b : Fin Tag.E6.rank → Lˣ} (hb : ∀ i, b i ^ 3 = 1) : ∃ e, torV ω e = b := by
  have hζ : IsPrimitiveRoot ((ω : Lˣ) : L) 3 :=
    IsPrimitiveRoot.coe_units_iff.2 (hω ▸ IsPrimitiveRoot.orderOf ω)
  have hex : ∀ i, ∃ m : ℕ, m < 3 ∧ ω ^ m = b i := fun i => by
    obtain ⟨m, hm, hmb⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ((b i : Lˣ) : L))
      (by rw [← Units.val_pow_eq_pow_val, hb i, Units.val_one])
    exact ⟨m, hm, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hmb)⟩
  choose m hm hmb using hex
  refine ⟨fun i => (m i : ZMod 3), funext fun i => ?_⟩
  simp only [torV, ZMod.val_natCast, Nat.mod_eq_of_lt (hm i), hmb]

theorem weylTuple_pow_three {L : Type} [Field L] (g : WeylGroup Tag.E6)
    {b : Fin Tag.E6.rank → Lˣ} (hb : ∀ i, b i ^ 3 = 1) (i : Fin Tag.E6.rank) :
    weylTuple g b i ^ 3 = 1 := by
  simp only [weylTuple, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar]
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb j, one_zpow]

theorem syl3_card_fix_le {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    {R : Subgroup (WeylGroup Tag.E6)} (hRS : R ≤ syl3Sub) (hR : IsElemAbelian 3 R)
    (h9 : 9 ≤ Nat.card R) :
    Nat.card R * Nat.card {e : Fin Tag.E6.rank → ZMod 3 //
      ∀ w ∈ R, weylTuple w (torV ω e) = torV ω e} ≤ 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspec := syl3Check_spec Certificates.certificate231801
  have hpg : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hR.2 x x.2)⟩
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  have hle81 : Nat.card R ≤ 81 := (Subgroup.card_le_of_le hRS).trans_eq card_syl3Sub
  have hne81 : Nat.card R ≠ 81 := by
    intro h81
    have hRe : R = syl3Sub := Subgroup.eq_of_le_of_card_ge hRS (by rw [h81, card_syl3Sub])
    obtain ⟨a, ha, b, hb, hab⟩ := syl3Sub_not_comm
    rw [← hRe] at ha hb
    exact hab (congrArg Subtype.val (hR.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hm23 : m = 2 ∨ m = 3 := by
    rw [hm] at h9 hle81 hne81
    have h1 : 2 ≤ m := by
      by_contra h
      push Not at h
      have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
    have h2 : m ≤ 4 := by
      by_contra h
      push Not at h
      have : 3 ^ 5 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h
      norm_num at this
      omega
    rcases (show m = 2 ∨ m = 3 ∨ m = 4 by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      apply hne81
      rw [h]
      norm_num
  have hRfin : Finite R := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨w₁, hw₁R, hw₁1⟩ : ∃ w ∈ R, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 hcon
    rw [this, Subgroup.card_bot] at h9
    omega
  have hz3 : Nat.card (Subgroup.zpowers w₁) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hR.2 w₁ hw₁R))
  obtain ⟨w₂, hw₂R, hw₂z⟩ : ∃ w ∈ R, w ∉ Subgroup.zpowers w₁ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show R ≤ Subgroup.zpowers w₁ from fun w hw => hcon w hw)
    omega
  have hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨i, hi⟩ := mem_syl3Sub_iff.1 (hRS (inv_mem hw₁R))
  obtain ⟨j, hj⟩ := mem_syl3Sub_iff.1 (hRS (inv_mem hw₂R))
  have hsq : ∀ a : Fin 81, syl3Elt (syl3MulIdx a a) = syl3Elt a * syl3Elt a := fun a => syl3Elt_mulIdx a a
  have hord3 : ∀ {a : Fin 81} {w : WeylGroup Tag.E6}, syl3Elt a = w⁻¹ → w ∈ R → w ≠ 1 →
      syl3Ord3W syl3TabArr syl3GenWordArr a = true := by
    intro a w ha hw hw1
    simp only [syl3Ord3W, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun h0 => hw1 ?_, ?_⟩
    · rw [h0, syl3Elt_zero] at ha
      exact inv_eq_one.1 ha.symm
    · show syl3MulIdx (syl3MulIdx a a) a = 0
      apply syl3Elt_injective
      rw [syl3Elt_mulIdx, hsq, ha, syl3Elt_zero, ← mul_inv_rev, ← mul_inv_rev, inv_eq_one,
        ← pow_two, ← pow_succ']
      exact hR.2 w hw
  have hcommB : ∀ {a b : Fin 81} {w w' : WeylGroup Tag.E6}, syl3Elt a = w⁻¹ → syl3Elt b = w'⁻¹ →
      w ∈ R → w' ∈ R → syl3CommW syl3TabArr syl3GenWordArr a b = true := by
    intro a b w w' ha hb hw hw'
    simp only [syl3CommW, decide_eq_true_eq]
    show syl3MulIdx a b = syl3MulIdx b a
    apply syl3Elt_injective
    rw [syl3Elt_mulIdx, syl3Elt_mulIdx, ha, hb, ← mul_inv_rev, ← mul_inv_rev, hcomm w hw w' hw']
  have hindep : syl3IndepW syl3TabArr syl3GenWordArr i j = true := by
    simp only [syl3IndepW, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨fun h0 => hw₂z ?_, fun hji => hw₂z ?_⟩, fun hjs => hw₂z ?_⟩
    · rw [h0, syl3Elt_zero] at hj
      rw [inv_eq_one.1 hj.symm]
      exact one_mem _
    · rw [hji, hi] at hj
      rw [(inv_injective hj).symm]
      exact Subgroup.mem_zpowers w₁
    · rw [hjs, syl3MulIdxW_eq, hsq, hi, ← mul_inv_rev] at hj
      rw [(inv_injective hj).symm]
      exact mul_mem (Subgroup.mem_zpowers w₁) (Subgroup.mem_zpowers w₁)
  have hi3 := hord3 hi hw₁R hw₁1
  have hj3 := hord3 hj hw₂R (fun h => hw₂z (h ▸ one_mem _))
  have hij := hcommB hi hj hw₁R hw₂R
  have hfixW : ∀ {a : Fin 81} {w : WeylGroup Tag.E6}, syl3Elt a = w⁻¹ → ∀ e : Fin Tag.E6.rank → ZMod 3,
      weylTuple w (torV ω e) = torV ω e →
        syl3FixArr (syl3MatsArr.getD a.val #[]) (syl3VecArr (syl3Code (e ∘ syl3IdxEquiv))) = true := by
    intro a w ha e he
    apply syl3FixArr_of_fix
    rw [syl3Vec_code]
    have := (weylTuple_torV_eq_iff hω w e).1 he
    rw [← ha, syl3W_elt] at this
    exact this
  set Fx := {e : Fin Tag.E6.rank → ZMod 3 // ∀ w ∈ R, weylTuple w (torV ω e) = torV ω e}
  have hcard_le : ∀ (l : List ℕ), (∀ e : Fx, syl3Code (e.1 ∘ syl3IdxEquiv) ∈ l) →
      Nat.card Fx ≤ l.length := by
    intro l hl
    have hinj : Function.Injective fun e : Fx => syl3Code (e.1 ∘ syl3IdxEquiv) := fun e e' h =>
      Subtype.ext (syl3IdxEquiv.surjective.injective_comp_right (syl3Code_injective h))
    have h1 : Nat.card Fx ≤ Nat.card ↥(l.toFinset) :=
      Nat.card_le_card_of_injective
        (fun e => ⟨syl3Code (e.1 ∘ syl3IdxEquiv), List.mem_toFinset.2 (hl e)⟩)
        (fun e e' h => hinj (Subtype.mk.inj h))
    rw [Nat.card_eq_finsetCard] at h1
    exact h1.trans (List.toFinset_card_le l)
  have hmem2 : ∀ e : Fx, syl3Code (e.1 ∘ syl3IdxEquiv) ∈ (syl3FixList i).filter
      fun n => syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n) := by
    intro e
    rw [List.mem_filter]
    refine ⟨?_, hfixW hj e.1 (e.2 w₂ hw₂R)⟩
    rw [syl3FixList, syl3FixCodesW, syl3Tabulate_getD, List.mem_filter, List.mem_range]
    exact ⟨syl3Code_lt _, hfixW hi e.1 (e.2 w₁ hw₁R)⟩
  rcases hm23 with rfl | rfl
  ·
    have hP1 := hspec.2.2.2.2.2.2.1 i j hi3 hj3 hij hindep
    have := hcard_le _ hmem2
    rw [hm, show (3 : ℕ) ^ 2 = 9 by norm_num]
    omega
  ·
    set S₂ : Finset (WeylGroup Tag.E6) :=
      (Finset.univ : Finset (Fin 3 × Fin 3)).image fun ab => w₁ ^ ab.1.val * w₂ ^ ab.2.val with hS₂
    have hS₂card : S₂.card ≤ 9 := (Finset.card_image_le).trans (by simp)
    obtain ⟨w₃, hw₃R, hw₃S⟩ : ∃ w ∈ R, w ∉ S₂ := by
      by_contra hcon
      push Not at hcon
      have h1 : Nat.card R ≤ S₂.card := by
        have := Nat.card_le_card_of_injective (fun x : R => (⟨x.1, hcon x.1 x.2⟩ : S₂))
          (fun x y h => Subtype.ext (Subtype.mk.inj h))
        rwa [Nat.card_eq_finsetCard] at this
      rw [hm] at h1
      norm_num at h1
      omega
    obtain ⟨k, hk⟩ := mem_syl3Sub_iff.1 (hRS (inv_mem hw₃R))
    have hk3 := hord3 hk hw₃R (fun h => hw₃S (by
      rw [h]
      exact Finset.mem_image.2 ⟨(0, 0), Finset.mem_univ _, by simp⟩))
    have hik := hcommB hi hk hw₁R hw₃R
    have hjk := hcommB hj hk hw₂R hw₃R
    have hpow : ∀ (a : Fin 81) (w : WeylGroup Tag.E6), syl3Elt a = w⁻¹ → ∀ e : Fin 3,
        syl3Elt (syl3PowIdxW syl3TabArr syl3GenWordArr a e) = (w ^ e.val)⁻¹ := by
      intro a w ha e
      unfold syl3PowIdxW
      split_ifs with h0 h1
      · rw [h0, pow_zero, inv_one, syl3Elt_zero]
      · rw [h1, pow_one, ha]
      · have h2 : e.val = 2 := by omega
        rw [h2, syl3MulIdxW_eq, syl3Elt_mulIdx, ha, ← mul_inv_rev, ← pow_two]
    have hout : syl3OutW syl3TabArr syl3GenWordArr i j k = true := by
      simp only [syl3OutW, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
      intro a b hab
      apply hw₃S
      rw [Finset.mem_image]
      refine ⟨(a, b), Finset.mem_univ _, ?_⟩
      have := congrArg syl3Elt hab
      rw [hk, syl3MulIdxW_eq, syl3Elt_mulIdx, hpow i w₁ hi a, hpow j w₂ hj b, ← mul_inv_rev] at this
      show w₁ ^ a.val * w₂ ^ b.val = w₃
      rw [inv_injective this]
      exact hcomm _ (pow_mem hw₁R _) _ (pow_mem hw₂R _)
    have hP2 := hspec.2.2.2.2.2.2.2 i j k hi3 hj3 hij hindep hk3 hik hjk hout
    have hmem3 : ∀ e : Fx, syl3Code (e.1 ∘ syl3IdxEquiv) ∈ ((syl3FixList i).filter
        fun n => syl3FixArr (syl3MatsArr.getD j.val #[]) (syl3VecArr n)).filter
          fun n => syl3FixArr (syl3MatsArr.getD k.val #[]) (syl3VecArr n) := by
      intro e
      rw [List.mem_filter]
      exact ⟨hmem2 e, hfixW hk e.1 (e.2 w₃ hw₃R)⟩
    have := hcard_le _ hmem3
    rw [hm, show (3 : ℕ) ^ 3 = 27 by norm_num]
    omega

theorem syl3_card_le_81 {L : Type} [Field L] {ω : Lˣ} (hω : orderOf ω = 3)
    {R : Subgroup (WeylGroup Tag.E6)} (hR : IsElemAbelian 3 R) (h9 : 9 ≤ Nat.card R)
    {X : Type} [Finite X] (f : X → (Fin Tag.E6.rank → Lˣ)) (hf : Function.Injective f)
    (hf3 : ∀ x i, f x i ^ 3 = 1) (hfix : ∀ x, ∀ w ∈ R, weylTuple w (f x) = f x) :
    Nat.card R * Nat.card X ≤ 81 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have hW : Nat.card (WeylGroup Tag.E6) = 51840 := CFSG.RankThree.Chevalley.E6_weyl_length_polynomial.2
  have hfac : (Nat.card (WeylGroup Tag.E6)).factorization 3 = 4 := by
    rw [hW, show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  let S : Sylow 3 (WeylGroup Tag.E6) :=
    Sylow.ofCard syl3Sub (by rw [card_syl3Sub, hfac]; norm_num)
  have hpg : IsPGroup 3 R := fun x => ⟨1, Subtype.ext (by simpa using hR.2 x x.2)⟩
  obtain ⟨Q, hRQ⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) Q S
  have hconj : ∀ w ∈ R, g * w * g⁻¹ ∈ syl3Sub := by
    intro w hw
    have h1 : g * w * g⁻¹ ∈ ((g • Q : Sylow 3 (WeylGroup Tag.E6)) : Subgroup (WeylGroup Tag.E6)) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨w, hRQ hw, rfl⟩
    rw [hg] at h1
    exact h1
  set R' := R.map (MulAut.conj g).toMonoidHom with hR'
  have hR'S : R' ≤ syl3Sub := by
    rintro _ ⟨w, hw, rfl⟩
    exact hconj w hw
  have hR'el : IsElemAbelian 3 R' := hR.map _
  have hR'card : Nat.card R' = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hF : ∀ x : X, ∃ e : Fin Tag.E6.rank → ZMod 3, torV ω e = weylTuple g (f x) := fun x =>
    exists_torV_eq hω (weylTuple_pow_three g (hf3 x))
  choose F hFx using hF
  have hFfix : ∀ x : X, ∀ w ∈ R', weylTuple w (torV ω (F x)) = torV ω (F x) := by
    rintro x _ ⟨w, hw, rfl⟩
    rw [hFx x]
    change weylTuple (g * w * g⁻¹) (weylTuple g (f x)) = weylTuple g (f x)
    rw [weylTuple_weylTuple, inv_mul_cancel_right, ← weylTuple_weylTuple, hfix x w hw]
  have hFinj : Function.Injective fun x : X => (⟨F x, hFfix x⟩ : {e : Fin Tag.E6.rank → ZMod 3 //
      ∀ w ∈ R', weylTuple w (torV ω e) = torV ω e}) := by
    intro x y h
    have h1 : weylTuple g (f x) = weylTuple g (f y) := by
      rw [← hFx x, ← hFx y]
      exact congrArg (fun e => torV ω e.1) h
    have h2 := congrArg (weylTuple g⁻¹) h1
    rw [weylTuple_weylTuple, weylTuple_weylTuple, inv_mul_cancel, weylTuple_one, weylTuple_one] at h2
    exact hf h2
  have h1 := Nat.card_le_card_of_injective _ hFinj
  have h2 := syl3_card_fix_le hω hR'S hR'el (by rw [hR'card]; exact h9)
  rw [hR'card] at h2
  calc Nat.card R * Nat.card X ≤ Nat.card R * Nat.card {e : Fin Tag.E6.rank → ZMod 3 //
        ∀ w ∈ R', weylTuple w (torV ω e) = torV ω e} := Nat.mul_le_mul_left _ h1
    _ ≤ 81 := h2

end Syl3

section Main51

section Plane

theorem exists_diagHom_twLangData {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (Dt : TwLangData K σ q A) :
    ∃ a : ↥A →* (Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ), ∀ x : ↥A,
      rootDiagUnit TwistTag.E6.tag (a x) = Dt.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (Dt.c * (x : ModGL TwistTag.E6.tag K) * Dt.c⁻¹) * Dt.g0 := by
  set T₀ := (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)).range with hT₀
  have hdiagT : ∀ x ∈ A, diagG Dt.g0 Dt.c x ∈ T₀ := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (Dt.hc x hx)
    have hte' : Dt.g0 * t * Dt.g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
        (Dt.c * x * Dt.c⁻¹) := hte
    have hdt : diagG Dt.g0 Dt.c x = t := by
      change Dt.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (Dt.c * x * Dt.c⁻¹) * Dt.g0 = t
      rw [← hte']
      group
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_of_mem_torusGroup (twistedTorus_le _ _ ht)
    exact ⟨a, by rw [hdt, ← ha]; rfl⟩
  let φ : ↥A →* ↥T₀ := ((diagG Dt.g0 Dt.c).comp A.subtype).codRestrict T₀ fun x => hdiagT x x.2
  have hrinj : Function.Injective (rootDiagUnitHom Tag.E6 (AlgebraicClosure K)) :=
    fun a b h => CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h
  let ι : (Fin Tag.E6.rank → (AlgebraicClosure K)ˣ) ≃* ↥T₀ := MonoidHom.ofInjective hrinj
  refine ⟨ι.symm.toMonoidHom.comp φ, fun x => ?_⟩
  have e1 := congrArg Subtype.val (ι.apply_symm_apply (φ x))
  have e2 : ((ι (ι.symm (φ x)) : ↥T₀) : ModGL Tag.E6 (AlgebraicClosure K)) =
      rootDiagUnit Tag.E6 (ι.symm (φ x)) := rfl
  rw [e2] at e1
  exact e1.trans (diagG_apply Dt.g0 Dt.c x.1)

open scoped Classical in
theorem finrank_ker_eq_24_of_isRegular {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    {σ : K ≃+* K} {q : ℕ} {A : Subgroup (ModGL TwistTag.E6.tag K)} (hA9 : Nat.card A = 3 ^ 2)
    (hA3 : ∀ x ∈ A, x ^ 3 = 1) (Dt : TwLangData K σ q A) (hreg : Dt.IsRegular)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ A) (hx1 : x ≠ 1) :
    finrank K (LinearMap.ker ((x : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 := by
  obtain ⟨a, ha⟩ := exists_diagHom_twLangData Dt
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA9]; norm_num)
  haveI : Fintype ↥A := Fintype.ofFinite _
  have hcardA : Fintype.card ↥A = 9 := by rw [← Nat.card_eq_fintype_card, hA9]; norm_num
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective (ringChar K)
  have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 3).1 h0
    exact hK3 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 this)
  set N : ↥A → ℕ := fun y => ((rootFinset TwistTag.E6.tag).filter fun α => rootChar (a y) α = 1).card
    with hN
  have hfix : ∀ y : ↥A, finrank K (LinearMap.ker
      (((y : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 6 + N y := by
    intro y
    have hy := ha y
    set Y : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) Dt.c)⁻¹ * Dt.g0 with hY
    have hconj : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) =
        Y * rootDiagUnit TwistTag.E6.tag (a y) * Y⁻¹ := by
      rw [hy, hY, map_mul, map_mul, map_inv]
      group
    have h1 := finrank_ker_baseChangeEnd (L := AlgebraicClosure K)
      (((y : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)
    rw [baseChangeEnd_sub_aux, baseChangeEnd_one_aux, ← coe_baseChangeGL, hconj,
      finrank_ker_conj_sub_one] at h1
    rw [← h1]
    exact finrank_ker_rootDiag_sub_one_card (a y)
  have hN18 : ∀ y : ↥A, y ≠ 1 → 18 ≤ N y := by
    intro y hy1
    have ha3 : ∀ i, a y i ^ 3 = 1 := by
      have h1 : a y ^ 3 = 1 := by
        rw [← map_pow]
        have : y ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hA3 _ y.2, Subgroup.coe_one])
        rw [this, map_one]
      intro i
      simpa using congrFun h1 i
    have hne : rootDiagUnit TwistTag.E6.tag (a y) ≠ 1 := by
      intro h1
      apply hy1
      have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K))
          (Dt.c * (y : ModGL TwistTag.E6.tag K) * Dt.c⁻¹) = 1 := by
        have e : baseChangeGL (algebraMap K (AlgebraicClosure K))
            (Dt.c * (y : ModGL TwistTag.E6.tag K) * Dt.c⁻¹) =
            Dt.g0 * (Dt.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (Dt.c * (y : ModGL TwistTag.E6.tag K) * Dt.c⁻¹) * Dt.g0) * Dt.g0⁻¹ := by group
        rw [e, ← ha y, h1]
        group
      have h4 : Dt.c * (y : ModGL TwistTag.E6.tag K) * Dt.c⁻¹ = 1 :=
        baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K))
          (h2.trans (map_one _).symm)
      have h5 : (y : ModGL TwistTag.E6.tag K) = 1 := by
        have e : (y : ModGL TwistTag.E6.tag K) =
            Dt.c⁻¹ * (Dt.c * (y : ModGL TwistTag.E6.tag K) * Dt.c⁻¹) * Dt.c := by group
        rw [e, h4]
        group
      exact Subtype.ext h5
    have hmem := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.finrank_ker_rootDiag_mem
      h3L ha3 hne
    have hc := finrank_ker_rootDiag_sub_one_card (K := AlgebraicClosure K) (τ := Tag.E6) (a y)
    rw [hc] at hmem
    change 6 + N y ∈ ({24, 28, 30, 36, 46} : Set ℕ) at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    omega
  have hN1 : N 1 = 72 := by
    have hR : (rootFinset TwistTag.E6.tag).card = 72 := by rw [card_rootFinset]; rfl
    rw [hN]
    simp only [map_one]
    rw [Finset.filter_true_of_mem fun α _ => by simp [rootChar], hR]
  have hsum : ∑ y : ↥A, N y ≤ 72 * 3 := by
    have hswap : ∑ y : ↥A, N y = ∑ α ∈ rootFinset TwistTag.E6.tag,
        (Finset.univ.filter fun y : ↥A => rootChar (a y) α = 1).card := by
      simp only [hN, Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    have hR : (rootFinset TwistTag.E6.tag).card = 72 := by rw [card_rootFinset]; rfl
    calc ∑ α ∈ rootFinset TwistTag.E6.tag, (Finset.univ.filter fun y : ↥A => rootChar (a y) α = 1).card
        ≤ ∑ _α ∈ rootFinset TwistTag.E6.tag, 3 := by
          refine Finset.sum_le_sum fun α hα => ?_
          set χ : ↥A →* (AlgebraicClosure K)ˣ := (rootCharHom α).comp a with hχ
          have hcard : (Finset.univ.filter fun y : ↥A => rootChar (a y) α = 1).card = Nat.card χ.ker := by
            rw [Nat.card_eq_fintype_card]
            refine (Fintype.card_of_subtype _ fun y => ?_).symm
            rw [Finset.mem_filter, MonoidHom.mem_ker]
            exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
          rw [hcard]
          have hker : χ.ker ≠ ⊤ := by
            intro htop
            apply hreg
            refine ⟨α, mem_rootFinset.1 hα, fun z hz => ⟨a ⟨z, hz⟩, ha ⟨z, hz⟩, ?_⟩⟩
            have hm : (⟨z, hz⟩ : ↥A) ∈ χ.ker := by rw [htop]; exact Subgroup.mem_top _
            exact hm
          have hdvd : Nat.card χ.ker ∣ 3 ^ 2 := hA9 ▸ Subgroup.card_subgroup_dvd_card χ.ker
          obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
          have hm2 : m ≠ 2 := by
            rintro rfl
            exact hker ((Subgroup.card_eq_iff_eq_top χ.ker).1 (hm'.trans hA9.symm))
          rw [hm']
          calc 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 3 := by norm_num
      _ = 72 * 3 := by rw [Finset.sum_const, hR, smul_eq_mul]
  set x₀ : ↥A := ⟨x, hx⟩ with hx₀
  have hx₀1 : x₀ ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hsplit : ∑ y : ↥A, N y = N 1 + (N x₀ +
      ∑ y ∈ (Finset.univ.erase (1 : ↥A)).erase x₀, N y) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥A)),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hx₀1, Finset.mem_univ x₀⟩)]
  have hrest : 7 * 18 ≤ ∑ y ∈ (Finset.univ.erase (1 : ↥A)).erase x₀, N y := by
    have hc : ((Finset.univ.erase (1 : ↥A)).erase x₀).card = 7 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hx₀1, Finset.mem_univ x₀⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardA]
    have := Finset.card_nsmul_le_sum ((Finset.univ.erase (1 : ↥A)).erase x₀) N 18 fun y hy =>
      hN18 y (Finset.mem_erase.1 (Finset.mem_erase.1 hy).2).1
    rw [hc, smul_eq_mul] at this
    exact this
  have hle : N x₀ ≤ 18 := by omega
  have hge : 18 ≤ N x₀ := hN18 x₀ hx₀1
  have := hfix x₀
  rw [show N x₀ = 18 by omega] at this
  exact this

end Plane

section Main

theorem rank3CuResExcSeven_holds : Claims1310t.Rank3CuResExcSeven := by
  intro K _ _ σ hK hσ D hD hDcard
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK.trans (by norm_num)
  have hσ' : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ c, pow_one]
  have h2K : ringChar K = 2 := ringChar_eq_of_card_pow Nat.prime_two le_rfl K (hK.trans (by norm_num))
  have hD81 : Nat.card D = 81 := hDcard.trans (by norm_num)
  have hK3 : ringChar K ≠ 3 := by rw [h2K]; norm_num
  by_contra hcon
  have hno : Claims1310r.NoPlaneTwoSub D := fun F hFD hF9 V hV2 hVinv => by
    by_contra hV1
    exact hcon ⟨F, hFD, hF9, V, hV1, hV2, hVinv⟩
  have hDle : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun φ hφ =>
    Claims1310s.mem_inndiag_of_two hK' σ hσ' (hD.2 φ hφ)
  have hinj := twistedE6InndiagConj_injective Nat.prime_two le_rfl hK' σ hσ'
  have hplane : ∀ E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), E ≤ D → Nat.card E = 3 ^ 2 →
      ∀ x ∈ twPlanePre K σ E, x ≠ 1 →
        finrank K (LinearMap.ker ((x : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 := by
    intro E hED hE9 x hx hx1
    have hEIn : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := hED.trans hDle
    have hEel : IsElemAbelian 3 E := hD.mono hED
    have hEi : CFSG.IsElementaryAbelian 3 ↥E := Claims1310s.isElementaryAbelian_of_isElemAbelian' hEel
    have hE9' : 9 ≤ Nat.card E := by rw [hE9]; norm_num
    obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
    haveI := hK₁
    by_cases hiso : TwistedE6DiagIsotropic K σ K₁ E
    · obtain ⟨Dt⟩ := exists_twLangData twistedE6PlaneToralLang_proved 2 1 Nat.prime_two (by norm_num) le_rfl
        hK' σ hσ' K₁ hroot E hEi hE9 hEIn hiso
      have hreg : Dt.IsRegular := by
        rintro ⟨α, hα, hkill⟩
        obtain ⟨u, huC, hu1, ⟨n, hun⟩, huc⟩ :=
          twE6KillRoot_proof K σ (2 ^ 1) hK3 hσ' hK' (twPlanePre K σ E) Dt α hα hkill
        set uC : ↥(twistedE6RootGroup K σ) := ⟨u, huC⟩ with huCdef
        have hEfix : ∀ φ ∈ E, φ uC = uC := by
          intro φ hφ
          have hφr : φ ∈ (twistedE6InndiagConj K σ).range := by
            rw [range_twistedE6InndiagConj]
            exact hEIn hφ
          obtain ⟨g, rfl⟩ := hφr
          have hgP : (g : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
            (mem_twPlanePre_iff K σ E _).2 ⟨g, rfl, hφ⟩
          apply Subtype.ext
          rw [twistedE6InndiagConj_apply]
          have hcomm := huc _ hgP
          change (g : ModGL TwistTag.E6.tag K) * u * (g : ModGL TwistTag.E6.tag K)⁻¹ = u
          rw [← hcomm.eq, mul_inv_cancel_right]
        have hV2 : IsPGroup 2 ↥(Subgroup.zpowers uC) := by
          intro v
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 v.2
          refine ⟨n, Subtype.ext ?_⟩
          have huCn : uC ^ (2 ^ n) = 1 := Subtype.ext (by
            rw [Subgroup.coe_pow, huCdef, Subgroup.coe_one, ← h2K]
            exact hun)
          rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
            zpow_natCast, huCn, one_zpow]
        have hVinv : ∀ φ ∈ E, ∀ v ∈ Subgroup.zpowers uC, φ v ∈ Subgroup.zpowers uC := by
          intro φ hφ v hv
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
          rw [map_zpow, hEfix φ hφ]
          exact Subgroup.zpow_mem_zpowers uC k
        have hbot := hno E hED hE9' _ hV2 hVinv
        apply hu1
        have hmem : uC ∈ Subgroup.zpowers uC := Subgroup.mem_zpowers uC
        rw [hbot, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      have hA3 : ∀ y ∈ twPlanePre K σ E, y ^ 3 = 1 := by
        intro y hy
        obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ E y).1 hy
        have h3 : twistedE6InndiagConj K σ (g ^ 3) = 1 := by
          rw [map_pow]
          exact hEel.2 _ hg
        have hg3 : g ^ 3 = 1 := hinj (h3.trans (map_one _).symm)
        rw [← Subgroup.coe_pow, hg3, Subgroup.coe_one]
      exact finrank_ker_eq_24_of_isRegular hK3
        ((card_twPlanePre 2 1 Nat.prime_two le_rfl K hK' σ hσ' E hEIn).trans hE9) hA3 Dt hreg hx hx1
    ·
      exfalso
      obtain ⟨Fr⟩ := exists_twE6HeisenbergFrame 2 1 Nat.prime_two (by norm_num) le_rfl hK' σ hσ' K₁ hroot E
        hEi hE9 hEIn hiso
      obtain ⟨R, hR1, hRp, hRE⟩ := twE6HeisFrameNormalizesR_of_fixedElt twE6HeisFrameFixedElt_holds 2 1
        Nat.prime_two (by norm_num) le_rfl K hK' σ hσ' E hEIn hEi hE9 Fr
      rw [h2K] at hRp
      exact hR1 (hno E hED hE9' R hRp fun φ hφ v hv => by
        rw [← hRE φ hφ]
        exact ⟨v, hv, rfl⟩)
  set P := twPlanePre K σ D with hP
  have hPcard : Nat.card P = 81 :=
    (card_twPlanePre 2 1 Nat.prime_two le_rfl K hK' σ hσ' D hDle).trans hD81
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPcard]; norm_num)
  haveI : Fintype ↥P := Fintype.ofFinite _
  have hall : ∀ x : ↥P, x ≠ 1 → finrank K (LinearMap.ker
      (((x : ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) - 1)) = 24 := by
    intro x hx1
    obtain ⟨g, hgx, hgD⟩ := (mem_twPlanePre_iff K σ D x).1 x.2
    set φ := twistedE6InndiagConj K σ g with hφdef
    have hφ1 : φ ≠ 1 := by
      intro h1
      apply hx1
      have hg1 : g = 1 := hinj (h1.trans (map_one _).symm)
      apply Subtype.ext
      have hx1' : (x : ModGL TwistTag.E6.tag K) = 1 := by rw [← hgx, hg1, Subgroup.coe_one]
      rw [hx1', Subgroup.coe_one]
    obtain ⟨ψ, hψD, hψφ⟩ : ∃ ψ ∈ D, ψ ∉ Subgroup.zpowers φ := by
      by_contra hcon'
      push Not at hcon'
      have hle : D ≤ Subgroup.zpowers φ := fun ψ hψ => hcon' ψ hψ
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hD81] at h1
      have h2 : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one (hD.2 φ hgD)
      have h3 := Nat.le_of_dvd (by norm_num) h2
      omega
    set E := Subgroup.closure ({φ, ψ} : Set (MulAut ↥(twistedE6RootGroup K σ))) with hE
    have hED : E ≤ D := by
      rw [hE, Subgroup.closure_le]
      intro z hz
      rcases hz with rfl | hz
      · exact hgD
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hψD
    have hE9 : Nat.card E = 3 ^ 2 :=
      CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hD hgD hψD hφ1 hψφ
    have hxE : (x : ModGL TwistTag.E6.tag K) ∈ twPlanePre K σ E :=
      (mem_twPlanePre_iff K σ E _).2 ⟨g, hgx, Subgroup.subset_closure (Set.mem_insert φ _)⟩
    exact hplane E hED hE9 _ hxE fun h => hx1 (Subtype.ext h)
  obtain ⟨ω, hω1, hω3⟩ : ∃ ω : K, ω ≠ 1 ∧ ω ^ 3 = 1 := by
    obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
      by_contra hcon'
      push Not at hcon'
      have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun z _ => by
        by_cases hz : z = 0
        · exact Or.inl hz
        · exact Or.inr (hcon' z hz)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_univ, hK, Set.ncard_pair zero_ne_one] at hle
      norm_num at hle
    refine ⟨ω, hω1, ?_⟩
    haveI : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card_sub_one_eq_one ω hω0
    rw [← Nat.card_eq_fintype_card, hK] at h
    norm_num at h
    exact h
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by
      have h2 : (2 : K) = 0 := by
        haveI : CharP K 2 := h2K ▸ ringChar.charP K
        exact_mod_cast CharP.cast_eq_zero K 2
      linear_combination h2
    rw [this]
    exact one_ne_zero
  have hcomm : ∀ x y : ↥P, x * y = y * x := by
    intro x y
    obtain ⟨g, hgx, hgD⟩ := (mem_twPlanePre_iff K σ D x).1 x.2
    obtain ⟨h, hhy, hhD⟩ := (mem_twPlanePre_iff K σ D y).1 y.2
    have hc : twistedE6InndiagConj K σ (g * h) = twistedE6InndiagConj K σ (h * g) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hgD⟩ ⟨_, hhD⟩)
    have hgh := hinj hc
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hgx, ← hhy, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hgh]
  have hexp : ∀ x : ↥P, x ^ 3 = 1 := by
    intro x
    obtain ⟨g, hgx, hgD⟩ := (mem_twPlanePre_iff K σ D x).1 x.2
    have h3g : twistedE6InndiagConj K σ (g ^ 3) = 1 := by
      rw [map_pow]
      exact hD.2 _ hgD
    have hg3 : g ^ 3 = 1 := hinj (h3g.trans (map_one _).symm)
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hgx, ← Subgroup.coe_pow, hg3, Subgroup.coe_one, Subgroup.coe_one]
  set ρ : ↥P →* Module.End K (RootModule TwistTag.E6.tag K) := (Units.coeHom _).comp P.subtype with hρ
  have hineq := card_mul_finrank_le_three_mul_sum_ker h3 hω1 hω3 hcomm hexp ρ
  have hV : finrank K (RootModule TwistTag.E6.tag K) = 78 := by
    have h1 := finrank_ker_rootDiag_sub_one_card (K := K) (τ := Tag.E6) 1
    rw [rootDiag_one, sub_self, LinearMap.ker_zero, finrank_top] at h1
    change finrank K (RootModule Tag.E6 K) = 78
    rw [h1]
    have hR : (rootFinset Tag.E6).card = 72 := by rw [card_rootFinset]; rfl
    rw [Finset.filter_true_of_mem fun α _ => by simp [rootChar], hR]
    rfl
  have hsum : ∑ x : ↥P, finrank K (LinearMap.ker (ρ x - 1)) = 78 + 80 * 24 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥P))]
    have h1 : finrank K (LinearMap.ker (ρ 1 - 1)) = 78 := by
      rw [map_one, sub_self, LinearMap.ker_zero, finrank_top, hV]
    have h2 : ∑ x ∈ Finset.univ.erase (1 : ↥P), finrank K (LinearMap.ker (ρ x - 1)) =
        ∑ _x ∈ Finset.univ.erase (1 : ↥P), 24 :=
      Finset.sum_congr rfl fun x hx => hall x (Finset.mem_erase.1 hx).1
    have hc : (Finset.univ.erase (1 : ↥P)).card = 80 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card,
        hPcard]
    rw [h1, h2, Finset.sum_const, hc, smul_eq_mul]
  rw [hsum, hV, ← Nat.card_eq_fintype_card, hPcard] at hineq
  norm_num at hineq

end Main

section Large

open CFSG.LieType.Chevalley (WeylGroup weylTuple monomialSubgroup weylQuotientHom canonicalRep coxeterSystem
  monomialSubgroup_le_torusWeylCosets canonicalRep_one canonicalRep_conj_rootDiagUnit
  rootDiagUnit_mul_comm_of_mem_torusGroup baseChangeGL_injective)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (exists_conj_le_monomial_bar weylQuotientHom_torus_mul
  isAlgebraic_zmod_algebraicClosure_of_finite map_twistedE6InndiagGL_le
  map_twistedE6InndiagGL_le_twistedFixedGroup exists_lang_torus_of_conj_torus_twisted'
  torusGroup_le_range_rootDiagUnitHom)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three (KSNotAll24.exists_cube_root_algebraicClosure)

theorem exists_index_nine_of_large {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = 2 ^ 2) (hσ : ∀ c, σ c = c ^ 2)
    {D : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hD : IsElemAbelian 3 D)
    (h243 : 243 ≤ Nat.card D) :
    ∃ E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)), E ≤ D ∧ Nat.card D ≤ 9 * Nat.card E ∧
      ∃ V : Subgroup ↥(twistedE6RootGroup K σ), V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧
        ∀ φ ∈ E, ∀ v ∈ V, φ v ∈ V := by
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK.trans (by norm_num)
  have hσ' : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ c, pow_one]
  have h2K : ringChar K = 2 := ringChar_eq_of_card_pow Nat.prime_two le_rfl K (hK.trans (by norm_num))
  have hK3 : ringChar K ≠ 3 := by rw [h2K]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP K 2 := h2K ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hDle : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ := fun φ hφ =>
    Claims1310s.mem_inndiag_of_two hK' σ hσ' (hD.2 φ hφ)
  have hinj := twistedE6InndiagConj_injective Nat.prime_two le_rfl hK' σ hσ'
  set P := twPlanePre K σ D with hP
  have hPcard : Nat.card P = Nat.card D := card_twPlanePre 2 1 Nat.prime_two le_rfl K hK' σ hσ' D hDle
  haveI : Finite ↥P := Nat.finite_of_card_ne_zero (by rw [hPcard]; omega)
  have hPI : P ≤ twistedE6InndiagGL K σ := fun x hx => by
    obtain ⟨g, rfl, -⟩ := (mem_twPlanePre_iff K σ D x).1 hx
    exact g.2
  have hP3 : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ D x).1 hx
    have h3 : twistedE6InndiagConj K σ (g ^ 3) = 1 := by
      rw [map_pow]
      exact hD.2 _ hg
    have hg3 : g ^ 3 = 1 := hinj (h3.trans (map_one _).symm)
    rw [← Subgroup.coe_pow, hg3, Subgroup.coe_one]
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    obtain ⟨g, rfl, hgD⟩ := (mem_twPlanePre_iff K σ D x).1 hx
    obtain ⟨h, rfl, hhD⟩ := (mem_twPlanePre_iff K σ D y).1 hy
    have hc : twistedE6InndiagConj K σ (g * h) = twistedE6InndiagConj K σ (h * g) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hgD⟩ ⟨_, hhD⟩)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hinj hc]
  set B := P.map (baseChangeGL (algebraMap K (AlgebraicClosure K))) with hB
  have hBad : B ≤ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) :=
    (Subgroup.map_mono hPI).trans (map_twistedE6InndiagGL_le σ _
      KSNotAll24.exists_cube_root_algebraicClosure)
  have hBfin : (B : Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))).Finite := by
    rw [hB, Subgroup.coe_map]
    exact (Set.toFinite _).image _
  have hB3 : ∀ x ∈ B, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hP3 y hy, map_one]
  obtain ⟨c, hc, hcB⟩ := exists_conj_le_monomial_bar (τ := TwistTag.E6.tag) (ℓ := 2) (p := 3)
    (by norm_num) (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hBad hBfin hB3
  have hmono : ∀ x : ↥P, c * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * c⁻¹ ∈ monomialSubgroup TwistTag.E6.tag (AlgebraicClosure K) :=
    fun x => hcB _ (Subgroup.mem_map_of_mem _ x.2)
  let φ : ↥P →* ↥(monomialSubgroup TwistTag.E6.tag (AlgebraicClosure K)) :=
    ((MulAut.conj c).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp P.subtype)).codRestrict _ hmono
  let π : ↥P →* WeylGroup TwistTag.E6.tag := (weylQuotientHom TwistTag.E6.tag (AlgebraicClosure K)).comp φ
  have hdec : ∀ y : ↥P, ∃ k ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      c * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) * c⁻¹ =
        k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y) := by
    intro y
    obtain ⟨w, k, hk, hkw⟩ := monomialSubgroup_le_torusWeylCosets (hmono y)
    refine ⟨k, hk, ?_⟩
    have hφ : (φ y : ModGL TwistTag.E6.tag (AlgebraicClosure K)) = k * canonicalRep _ _ w := hkw
    have hπ : π y = w := by
      change weylQuotientHom _ _ (φ y) = w
      have e : φ y = ⟨k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w,
          hφ ▸ (φ y).2⟩ := Subtype.ext hφ
      rw [e]
      exact weylQuotientHom_torus_mul hk w _
    rw [hπ]
    exact hkw
  have htor : ∀ x : ↥P, π x = 1 → c * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * c⁻¹ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := hdec x
    rw [hkx, hx, canonicalRep_one, mul_one]
    exact hk
  have hdiag : ∀ x : ↥π.ker, ∃ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a =
        c * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : ↥P) : ModGL TwistTag.E6.tag K) * c⁻¹ :=
    fun x => exists_rootDiagUnit_of_mem_torusGroup (htor x x.2)
  choose a ha using hdiag
  have ha_inj : Function.Injective a := by
    intro x y hxy
    have h1 := congrArg (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag) hxy
    rw [ha, ha] at h1
    have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : ↥P) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) ((y : ↥P) : ModGL TwistTag.E6.tag K) := by
      have := congrArg (fun z => c⁻¹ * z * c) h1
      simpa [mul_assoc] using this
    exact Subtype.ext (Subtype.ext (baseChangeGL_injective (τ := TwistTag.E6.tag) _ h2))
  have ha3 : ∀ x i, a x i ^ 3 = 1 := by
    intro x
    have h1 : rootDiagUnit TwistTag.E6.tag (a x ^ 3) = rootDiagUnit TwistTag.E6.tag 1 := by
      have e1 : rootDiagUnit TwistTag.E6.tag (a x ^ 3) = (rootDiagUnit TwistTag.E6.tag (a x)) ^ 3 :=
        map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) (a x) 3
      have e2 : rootDiagUnit TwistTag.E6.tag (1 : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ) = 1 :=
        map_one (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K))
      rw [e1, e2, ha, conj_pow, ← map_pow, hP3 _ (x : ↥P).2, map_one, mul_one, mul_inv_cancel]
    have h2 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h1
    intro i
    have h3 := congrFun h2 i
    rwa [Pi.pow_apply, Pi.one_apply] at h3
  have hafix : ∀ x : ↥π.ker, ∀ w ∈ π.range, weylTuple w (a x) = a x := by
    rintro x _ ⟨y, rfl⟩
    obtain ⟨k, hk, hky⟩ := hdec y
    have hcomm : (c * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : ↥P) : ModGL TwistTag.E6.tag K) *
        c⁻¹) * (c * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) * c⁻¹) =
        (c * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) * c⁻¹) *
        (c * baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : ↥P) : ModGL TwistTag.E6.tag K) * c⁻¹) := by
      have h1 := congrArg (baseChangeGL (algebraMap K (AlgebraicClosure K)))
        (hPcomm _ (x : ↥P).2 _ y.2)
      rw [map_mul, map_mul] at h1
      calc _ = c * (baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : ↥P) : ModGL TwistTag.E6.tag K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K)) * c⁻¹ := by group
        _ = c * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) ((x : ↥P) : ModGL TwistTag.E6.tag K)) * c⁻¹ := by
              rw [h1]
        _ = _ := by group
    rw [← ha, hky] at hcomm
    have h2 : canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y) *
        rootDiagUnit TwistTag.E6.tag (a x) *
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y))⁻¹ =
        rootDiagUnit TwistTag.E6.tag (a x) := by
      have hkd := rootDiagUnit_mul_comm_of_mem_torusGroup (a x) hk
      have e : k * (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y) *
          rootDiagUnit TwistTag.E6.tag (a x) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y))⁻¹) * k⁻¹ =
          k * rootDiagUnit TwistTag.E6.tag (a x) * k⁻¹ := by
        calc _ = (k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y)) *
              rootDiagUnit TwistTag.E6.tag (a x) *
                (k * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) (π y))⁻¹ := by group
          _ = rootDiagUnit TwistTag.E6.tag (a x) := by
              rw [← hcomm]
              group
          _ = _ := by rw [← hkd]; group
      have := congrArg (fun z => k⁻¹ * z * k) e
      simpa [mul_assoc] using this
    rw [canonicalRep_conj_rootDiagUnit] at h2
    exact CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_injective h2
  have hRel : IsElemAbelian 3 π.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨y, rfl⟩⟩ := u
      obtain ⟨_, ⟨z, rfl⟩⟩ := v
      apply Subtype.ext
      change π y * π z = π z * π y
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hPcomm _ y.2 _ z.2)
    · rintro _ ⟨y, rfl⟩
      rw [← map_pow]
      have : y ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hP3 _ y.2, Subgroup.coe_one])
      rw [this, map_one]
  have hcardP : Nat.card π.ker * Nat.card π.range = Nat.card P := by
    exact Subgroup.card_ker_mul_card_range π
  obtain ⟨ω, hω⟩ : ∃ ω : (AlgebraicClosure K)ˣ, orderOf ω = 3 := by
    have h3L : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
      intro h0
      have := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 3).1 h0
      norm_num at this
    haveI : NeZero ((3 : ℕ) : AlgebraicClosure K) := ⟨h3L⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) 3
    have hu : IsUnit ζ := hζ.isUnit (by norm_num)
    refine ⟨hu.unit, ?_⟩
    have hζ' : IsPrimitiveRoot ((hu.unit : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) 3 := by
      simpa using hζ
    exact (IsPrimitiveRoot.coe_units_iff.1 hζ').eq_orderOf.symm
  have hR3 : Nat.card π.range ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have hpg : IsPGroup 3 π.range := fun x => ⟨1, Subtype.ext (by simpa using hRel.2 x x.2)⟩
    obtain ⟨m, hm⟩ := hpg.exists_card_eq
    have h9 : 9 ≤ Nat.card π.range := by
      rw [hm] at hcon ⊢
      by_contra h
      push Not at h
      have hm1 : m ≤ 1 := by
        by_contra hm2
        push Not at hm2
        have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        omega
      interval_cases m <;> norm_num at hcon
    have h81 : Nat.card π.range * Nat.card π.ker ≤ 81 := syl3_card_le_81 hω hRel h9 a ha_inj ha3 hafix
    have := h81
    rw [mul_comm, hcardP, hPcard] at this
    omega
  set A₀ : Subgroup (ModGL TwistTag.E6.tag K) := π.ker.map P.subtype with hA₀
  have hA₀P : A₀ ≤ P := Subgroup.map_subtype_le _
  have hA₀card : Nat.card A₀ = Nat.card π.ker := Subgroup.card_map_of_injective P.subtype_injective
  have hA₀mem : ∀ z ∈ A₀, ∃ x : ↥π.ker, ((x : ↥P) : ModGL TwistTag.E6.tag K) = z := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 1 with hFrdef
  have hFr : ∀ z, Fr z = z ^ (2 ^ 1) := fun z => by rw [hFrdef, iterateFrobenius_def]
  have hFix : ∀ z ∈ A₀.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      twistHom TwistTag.E6 (AlgebraicClosure K) (iterateFrobenius (AlgebraicClosure K) 2 1) z = z := by
    rintro _ ⟨z, hz, rfl⟩
    have hzF := map_twistedE6InndiagGL_le_twistedFixedGroup Nat.prime_two le_rfl hK' σ hσ' Fr hFr
      (Subgroup.mem_map_of_mem _ (hPI (hA₀P hz)))
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).1 hzF).2
  have hCA : ∀ z ∈ A₀.map (baseChangeGL (algebraMap K (AlgebraicClosure K))),
      c * z * c⁻¹ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := hA₀mem z hz
    exact htor x x.2
  obtain ⟨v, g0, hg0C, hg0, hin⟩ :=
    exists_lang_torus_of_conj_torus_twisted' 2 TwistTag.E6 1 le_rfl hFix hc hCA
  let Dt : TwLangData K σ 2 A₀ :=
    { v := v, Fr := iterateFrobenius (AlgebraicClosure K) 2 1,
      hFr := fun z => by rw [iterateFrobenius_def, pow_one],
      g0 := g0, hg0C := hg0C, hg0 := hg0, c := 1, hcI := one_mem _,
      hc := fun z hz => by
        rw [one_mul, inv_one, mul_one]
        exact hin _ (Subgroup.mem_map_of_mem _ hz) }
  obtain ⟨a', ha'⟩ := exists_diagHom_twLangData Dt
  set α : Fin TwistTag.E6.tag.rank → ℤ := Pi.single 0 1 with hα
  have hαr : IsRoot TwistTag.E6.tag α := isRoot_single _ _
  let χ : ↥A₀ →* (AlgebraicClosure K)ˣ := (rootCharHom (τ := TwistTag.E6.tag) α).comp a'
  have hχ3 : ∀ z : ↥A₀, χ z ^ 3 = 1 := fun z => by
    have hz3 : z ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hP3 _ (hA₀P z.2), Subgroup.coe_one])
    rw [← map_pow, hz3, map_one]
  have hidx : χ.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    refine (Subgroup.card_le_of_le (show χ.range ≤ rootsOfUnity 3 (AlgebraicClosure K) from ?_)).trans
      (card_rootsOfUnity (AlgebraicClosure K) 3)
    rintro _ ⟨z, rfl⟩
    exact (mem_rootsOfUnity 3 _).2 (hχ3 z)
  set Pα : Subgroup (ModGL TwistTag.E6.tag K) := χ.ker.map A₀.subtype with hPα
  have hPαA₀ : Pα ≤ A₀ := Subgroup.map_subtype_le _
  have hPαcard : Nat.card Pα = Nat.card χ.ker := Subgroup.card_map_of_injective A₀.subtype_injective
  have hkill : ∀ z ∈ Pα, ∃ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit TwistTag.E6.tag b = Dt.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (Dt.c * z * Dt.c⁻¹ : ModGL TwistTag.E6.tag K) * Dt.g0 ∧ rootChar b α = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨a' y, ha' y, hy⟩
  let Dα : TwLangData K σ 2 Pα := { Dt with hc := fun z hz => Dt.hc z (hPαA₀ hz) }
  obtain ⟨u, huC, hu1, ⟨n, hun⟩, huc⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K σ 2 hK3 hσ hK Pα Dα α hαr hkill
  set E : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    (Pα.subgroupOf (twistedE6InndiagGL K σ)).map (twistedE6InndiagConj K σ) with hE
  have hPαI : Pα ≤ twistedE6InndiagGL K σ := hPαA₀.trans (hA₀P.trans hPI)
  have hED : E ≤ D := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨g', hg'eq, hg'D⟩ := (mem_twPlanePre_iff K σ D _).1
      (hA₀P (hPαA₀ (Subgroup.mem_subgroupOf.1 hg)))
    have hgg : g' = g := Subtype.ext hg'eq
    rw [← hgg]
    exact hg'D
  have hEcard : Nat.card E = Nat.card Pα := by
    rw [hE, Subgroup.card_map_of_injective hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPαI).toEquiv]
  set uC : ↥(twistedE6RootGroup K σ) := ⟨u, huC⟩ with huCdef
  have hEfix : ∀ ψ ∈ E, ψ uC = uC := by
    rintro _ ⟨g, hg, rfl⟩
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    have hcomm := huc _ (Subgroup.mem_subgroupOf.1 hg)
    change (g : ModGL TwistTag.E6.tag K) * u * (g : ModGL TwistTag.E6.tag K)⁻¹ = u
    rw [← hcomm.eq, mul_inv_cancel_right]
  refine ⟨E, hED, ?_, Subgroup.zpowers uC, ?_, ?_, ?_⟩
  ·
    have h1 : Nat.card χ.ker * χ.ker.index = Nat.card A₀ := Subgroup.card_mul_index χ.ker
    have h2 : Nat.card D ≤ 3 * Nat.card A₀ := by
      rw [← hPcard, ← hcardP, hA₀card, mul_comm 3]
      exact Nat.mul_le_mul_left _ hR3
    rw [hEcard, hPαcard]
    calc Nat.card D ≤ 3 * Nat.card A₀ := h2
      _ = 3 * (Nat.card χ.ker * χ.ker.index) := by rw [h1]
      _ ≤ 3 * (Nat.card χ.ker * 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hidx)
      _ = 9 * Nat.card χ.ker := by ring
  · intro hbot
    apply hu1
    have hmem : uC ∈ Subgroup.zpowers uC := Subgroup.mem_zpowers uC
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · intro w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 w.2
    refine ⟨n, Subtype.ext ?_⟩
    have huCn : uC ^ (2 ^ n) = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, huCdef, Subgroup.coe_one, ← h2K]
      exact hun)
    rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, huCn, one_zpow]
  · intro ψ hψ w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [map_zpow, hEfix ψ hψ]
    exact Subgroup.zpow_mem_zpowers uC k

end Large

section IndexNine

theorem twE6TwoStarIndexNine_holds : TwE6TwoStarIndexNine := by
  intro K _ _ σ hK hσ D hD
  classical
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK.trans (by norm_num)
  have hσ' : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ c, pow_one]
  have hfix2 : ∀ β : MulAut ↥(twistedE6RootGroup K σ), β ^ 3 = 1 →
      ∃ V : Subgroup ↥(twistedE6RootGroup K σ), V ≠ ⊥ ∧ IsPGroup 2 ↥V ∧
        ∀ φ ∈ Subgroup.zpowers β, ∀ v ∈ V, φ v ∈ V := by
    intro β hβ
    obtain ⟨u, hu1, ⟨n, hun⟩, hβu⟩ := Claims1310s.exists_fixed_two_elem_of_two hK' σ hσ' β hβ
    refine ⟨Subgroup.zpowers u, ?_, ?_, ?_⟩
    · intro hbot
      apply hu1
      have hmem : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    · intro w
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 w.2
      refine ⟨n, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, ← hk, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hun, one_zpow]
    · intro φ hφ v hv
      have hle : Subgroup.zpowers β ≤ MulAction.stabilizer (MulAut ↥(twistedE6RootGroup K σ)) u :=
        Subgroup.zpowers_le.2 hβu
      have hφu : φ u = u := hle hφ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
      rw [map_zpow, hφu]
      exact Subgroup.zpow_mem_zpowers u k
  haveI : Finite ↥D := inferInstance
  have hpg : IsPGroup 3 D := fun x => ⟨1, Subtype.ext (by simpa using hD.2 x x.2)⟩
  obtain ⟨m, hm⟩ := hpg.exists_card_eq
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    obtain ⟨V, hV1, hV2, -⟩ := hfix2 1 (one_pow 3)
    refine ⟨⊥, bot_le, ?_, V, hV1, hV2, fun φ hφ v hv => ?_⟩
    · rw [Subgroup.card_bot, hm]
      calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 * 1 := by norm_num
    · rw [Subgroup.mem_bot.1 hφ]
      exact hv
  rcases Nat.lt_or_ge m 4 with hm4 | hm4
  ·
    have hm3' : m = 3 := by omega
    obtain ⟨d, hdD, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hcon
      rw [this, Subgroup.card_bot, hm3'] at hm
      norm_num at hm
    have hd3 := hD.2 d hdD
    obtain ⟨V, hV1, hV2, hVd⟩ := hfix2 d hd3
    refine ⟨Subgroup.zpowers d, Subgroup.zpowers_le.2 hdD, ?_, V, hV1, hV2, hVd⟩
    have hod : orderOf d = 3 := orderOf_eq_prime hd3 hd1
    rw [Nat.card_zpowers, hod, hm, hm3']
    norm_num
  rcases Nat.lt_or_ge m 5 with hm5 | hm5
  ·
    have hm4' : m = 4 := by omega
    obtain ⟨E, hED, hE9, V, hV1, hV2, hVE⟩ :=
      rank3CuResExcSeven_holds K σ hK hσ D hD (by rw [hm, hm4'])
    refine ⟨E, hED, ?_, V, hV1, hV2, hVE⟩
    have h81 : (3 : ℕ) ^ 4 = 81 := by norm_num
    rw [hm, hm4', h81]
    omega
  ·
    exact exists_index_nine_of_large hK hσ hD (by
      rw [hm]
      calc 243 = 3 ^ 5 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm5)

end IndexNine

end Main51

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1310u

end
