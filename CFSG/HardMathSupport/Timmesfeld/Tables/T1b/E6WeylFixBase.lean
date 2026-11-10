
module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylMat
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24Facts
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.AGLEmbedding.R3 CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.SporadicRank CFSG.SectionRank
open scoped Matrix Pointwise

def e6Fix (F : Subgroup (WeylGroup Tag.E6)) : Set (Fin 6 → ZMod 3) :=
  {v | ∀ w ∈ F, e6WeylMat w *ᵥ v = v}

def fixMat6 (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Set (Fin 6 → ZMod 3) :=
  {v | M *ᵥ v = v}

section Lists

theorem toMatL_mem_of_mem_wordsL {n : ℕ} (S : Submonoid (Matrix (Fin n) (Fin n) (ZMod 3))) :
    ∀ Bs : List (List ℕ), (∀ B ∈ Bs, toMatL 3 n B ∈ S) →
      ∀ A ∈ wordsL 3 n Bs, toMatL 3 n A ∈ S
  | [], _, A, hA => by
    rw [wordsL, List.mem_singleton] at hA
    subst hA
    rw [toMatL_midL]
    exact S.one_mem
  | B :: Bs, hB, A, hA => by
    simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range] at hA
    obtain ⟨M, hM, a, -, rfl⟩ := hA
    rw [toMatL_mmulL, toMatL_mpowL]
    exact S.mul_mem (S.pow_mem (hB B List.mem_cons_self) a)
      (toMatL_mem_of_mem_wordsL S Bs (fun B' hB' => hB B' (List.mem_cons_of_mem _ hB')) M hM)

theorem exists_mem_wordsL_eq_one {n : ℕ} :
    ∀ Bs : List (List ℕ), ∃ A ∈ wordsL 3 n Bs, toMatL 3 n A = 1
  | [] => ⟨midL 3 n, List.mem_singleton_self _, toMatL_midL 3 n⟩
  | B :: Bs => by
    obtain ⟨M, hM, hM1⟩ := exists_mem_wordsL_eq_one (n := n) Bs
    refine ⟨mmulL 3 n (mpowL 3 n B 0) M, ?_, ?_⟩
    · simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨M, hM, 0, by norm_num, rfl⟩
    · rw [toMatL_mmulL, toMatL_mpowL, hM1, pow_zero, mul_one]

theorem exists_mem_wordsL_eq {n : ℕ} :
    ∀ Bs : List (List ℕ), ∀ B ∈ Bs, ∃ A ∈ wordsL 3 n Bs, toMatL 3 n A = toMatL 3 n B
  | [], B, hB => absurd hB List.not_mem_nil
  | B' :: Bs, B, hB => by
    rcases List.mem_cons.1 hB with rfl | hB
    · obtain ⟨M, hM, hM1⟩ := exists_mem_wordsL_eq_one (n := n) Bs
      refine ⟨mmulL 3 n (mpowL 3 n B 1) M, ?_, ?_⟩
      · simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨M, hM, 1, by norm_num, rfl⟩
      · rw [toMatL_mmulL, toMatL_mpowL, hM1, pow_one, mul_one]
    · obtain ⟨M, hM, hMB⟩ := exists_mem_wordsL_eq (n := n) Bs B hB
      refine ⟨mmulL 3 n (mpowL 3 n B' 0) M, ?_, ?_⟩
      · simp only [wordsL, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨M, hM, 0, by norm_num, rfl⟩
      · rw [toMatL_mmulL, toMatL_mpowL, hMB, pow_zero, one_mul]

theorem e6SylL_spec : ∀ A ∈ e6SylL (), A.length = 6 * 6 ∧ ∀ x ∈ A, x < 3 :=
  wordsL_spec 3 6 (by norm_num) _

theorem toMatL_inj6 {A B : List ℕ} (hA : A.length = 6 * 6 ∧ ∀ x ∈ A, x < 3)
    (hB : B.length = 6 * 6 ∧ ∀ x ∈ B, x < 3) (h : toMatL 3 6 A = toMatL 3 6 B) : A = B :=
  toMatL_inj 3 6 hA.1 hB.1 hA.2 hB.2 h

theorem mmulL_spec (A B : List ℕ) :
    (mmulL 3 6 A B).length = 6 * 6 ∧ ∀ x ∈ mmulL 3 6 A B, x < 3 :=
  ⟨length_mmulL 3 6 A B, lt_mmulL 3 6 (by norm_num) A B⟩

theorem midL_spec : (midL 3 6).length = 6 * 6 ∧ ∀ x ∈ midL 3 6, x < 3 :=
  ⟨length_midL 3 6, lt_midL 3 6 (by norm_num)⟩

theorem matVecA6_toArray (M c : List ℕ) : matVecA6 M.toArray c = matVecL 3 6 M c := by
  simp only [matVecA6, matVecL, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]

def vecList6 (v : Fin 6 → ZMod 3) : List ℕ := List.ofFn fun k : Fin 6 => (v k).val

theorem vecList6_mem (v : Fin 6 → ZMod 3) : vecList6 v ∈ allVecs 3 6 := by
  rw [mem_allVecs]
  refine ⟨by simp [vecList6], fun x hx => ?_⟩
  simp only [vecList6, List.mem_ofFn'] at hx
  obtain ⟨k, rfl⟩ := hx
  exact ZMod.val_lt _

theorem vecOf_vecList6 (v : Fin 6 → ZMod 3) : vecOf 3 6 (vecList6 v) = v := by
  funext k
  have hk : (List.ofFn fun k : Fin 6 => (v k).val).getD k.val 0 = (v k).val := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  simp only [vecOf, vecList6, hk, ZMod.natCast_zmod_val]

theorem vecList6_injective : Function.Injective vecList6 := fun v w h => by
  rw [← vecOf_vecList6 v, ← vecOf_vecList6 w, h]

theorem card_fixMat6_le (A : List ℕ) : Nat.card (fixMat6 (toMatL 3 6 A)) ≤ nfix6 A := by
  classical
  have hsub : vecList6 '' fixMat6 (toMatL 3 6 A) ⊆
      ((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).toFinset := by
    rintro _ ⟨v, hv, rfl⟩
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_filter, beq_iff_eq]
    refine ⟨vecList6_mem v, ?_⟩
    rw [matVecA6_toArray]
    have hm : matVecL 3 6 A (vecList6 v) ∈ allVecs 3 6 :=
      (mem_allVecs 3 6 _).2 ⟨length_matVecL 3 6 A _, lt_matVecL (by norm_num) 6 A _⟩
    refine vecOf_inj hm (vecList6_mem v) ?_
    rw [vecOf_matVecL, vecOf_vecList6]
    exact hv
  calc Nat.card (fixMat6 (toMatL 3 6 A)) = Nat.card (vecList6 '' fixMat6 (toMatL 3 6 A)) :=
        (Nat.card_image_of_injective vecList6_injective _).symm
    _ ≤ Nat.card (((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).toFinset :
          Set (List ℕ)) := Nat.card_mono (Finset.finite_toSet _) hsub
    _ = (((allVecs 3 6).filter fun v => matVecA6 A.toArray v == v).toFinset).card :=
        Nat.card_coe_set_eq _ |>.trans (Set.ncard_coe_finset _)
    _ ≤ nfix6 A := List.toFinset_card_le _

end Lists

abbrev e6tL : List ℕ := e6WordL (e6SylWords.getD 0 [])

abbrev e6cL : List ℕ := e6WordL (e6SylWords.getD 1 [])

structure E6SylFacts : Prop where
  length : (e6SylL ()).length = 81
  nodup : (e6SylL ()).Nodup
  mul_mem : ∀ A ∈ e6SylL (), ∀ B ∈ e6SylL (), mmulL 3 6 A B ∈ e6SylL ()
  noncomm : mmulL 3 6 e6tL e6cL ≠ mmulL 3 6 e6cL e6tL
  nfix_le : ∀ A ∈ e6SylL (), isO3L A = true → nfix6 A ≤ 81
  count : (((e6SylL ()).filter isO3L).filter fun A => decide (27 < nfix6 A)).length ≤ 25

theorem e6SylFacts_of_check (h : e6SylCheck () = true) : E6SylFacts := by
  simp only [e6SylCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_iff_mem, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hlen, hnd⟩, hmul⟩, hnc⟩, hle⟩, hcnt⟩ := h
  refine ⟨hlen, hnd, hmul, hnc, fun A hA hO => hle _ (List.mem_map.2
    ⟨A, List.mem_filter.2 ⟨hA, hO⟩, rfl⟩), ?_⟩
  rw [List.filter_map, List.length_map] at hcnt
  exact hcnt

def e6SylWordsF : List (List (Fin Tag.E6.rank)) :=
  ([[3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3], [0, 2], [4, 5],
    [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3, 1]] : List (List (Fin 6))).map
    (List.map e6Idx)

theorem e6SylWordsF_val : e6SylWordsF.map (List.map Fin.val) = e6SylWords := by
  simp only [e6SylWordsF, List.map_map]
  decide

def e6SylMats : Finset (Matrix (Fin 6) (Fin 6) (ZMod 3)) :=
  ((e6SylL ()).map (toMatL 3 6)).toFinset

theorem mem_e6SylMats {M : Matrix (Fin 6) (Fin 6) (ZMod 3)} :
    M ∈ e6SylMats ↔ ∃ A ∈ e6SylL (), toMatL 3 6 A = M := by
  simp [e6SylMats]

theorem one_mem_e6SylMats : (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) ∈ e6SylMats :=
  mem_e6SylMats.2 (exists_mem_wordsL_eq_one _)

theorem mem_mrange_of_mem_e6SylL {A : List ℕ} (hA : A ∈ e6SylL ()) :
    toMatL 3 6 A ∈ MonoidHom.mrange e6WeylMat := by
  refine toMatL_mem_of_mem_wordsL _ _ (fun B hB => ?_) A hA
  rw [← e6SylWordsF_val, List.map_map, List.mem_map] at hB
  obtain ⟨ω, -, rfl⟩ := hB
  exact ⟨_, e6WeylMat_wordProd ω⟩

theorem card_weylGroup_E6' :
    Nat.card (WeylGroup Tag.E6) = 51840 := by
  have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
  exact CFSG.RankThree.Chevalley.E6_weyl_length_polynomial.2

theorem factorization_51840 : (51840 : ℕ).factorization 3 = 4 := by
  have h : (51840 : ℕ) = 3 ^ 4 * 640 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.prime_three.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem card_le_729 (X : Set (Fin 6 → ZMod 3)) : Nat.card X ≤ 3 ^ 6 := by
  calc Nat.card X ≤ Nat.card (Set.univ : Set (Fin 6 → ZMod 3)) :=
        Nat.card_mono (Set.toFinite _) (Set.subset_univ _)
    _ = 3 ^ 6 := by
        rw [Nat.card_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
          Fintype.card_fin]

theorem e6SylWordsF_getD_val (i : ℕ) (hi : i < 4) :
    (e6SylWordsF.getD i []).map Fin.val = e6SylWords.getD i [] := by
  interval_cases i <;> decide

theorem card_e6Fix_map_conj (F : Subgroup (WeylGroup Tag.E6)) (g : WeylGroup Tag.E6) :
    Nat.card (e6Fix (F.map (MulAut.conj g).toMonoidHom)) = Nat.card (e6Fix F) := by
  have hgg : ∀ v : Fin 6 → ZMod 3, e6WeylMat g⁻¹ *ᵥ (e6WeylMat g *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]
  have hgg' : ∀ v : Fin 6 → ZMod 3, e6WeylMat g *ᵥ (e6WeylMat g⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have hto : ∀ v ∈ e6Fix F, e6WeylMat g *ᵥ v ∈ e6Fix (F.map (MulAut.conj g).toMonoidHom) := by
    intro v hv x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_right, map_mul, ← Matrix.mulVec_mulVec,
      hv y hy]
  have hinv : ∀ v ∈ e6Fix (F.map (MulAut.conj g).toMonoidHom), e6WeylMat g⁻¹ *ᵥ v ∈ e6Fix F := by
    intro v hv y hy
    have hx : g * y * g⁻¹ ∈ F.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.2 ⟨y, hy, rfl⟩
    have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [e, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgg', hv _ hx]
  let e : e6Fix F ≃ e6Fix (F.map (MulAut.conj g).toMonoidHom) :=
    { toFun := fun v => ⟨_, hto v.1 v.2⟩
      invFun := fun v => ⟨_, hinv v.1 v.2⟩
      left_inv := fun v => Subtype.ext (hgg v.1)
      right_inv := fun v => Subtype.ext (hgg' v.1) }
  exact (Nat.card_congr e).symm

theorem card_le_card_e6Fix {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (F : Subgroup (WeylGroup Tag.E6)) (S : Subgroup (Fin Tag.E6.rank → Kˣ))
    (hS : IsElemAbelian 3 S) (hfix : ∀ a ∈ S, ∀ w ∈ F, weylAct w a = a) :
    Nat.card S ≤ Nat.card (e6Fix F) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h3)
  have hex : ∀ a : S, ∃ v, (a : Fin Tag.E6.rank → Kˣ) = cubeTuple ζ v := fun a =>
    exists_cubeTuple hζ h3 fun i => congrFun (hS.2 a a.2) i
  choose f hf using hex
  have hmem : ∀ a : S, f a ∈ e6Fix F := fun a w hw => by
    apply cubeTuple_injective hζ
    rw [← weylAct_cubeTuple hζ, ← hf a]
    exact hfix a a.2 w hw
  refine Nat.card_le_card_of_injective (fun a => (⟨f a, hmem a⟩ : e6Fix F)) fun a b hab => ?_
  apply Subtype.ext
  rw [hf a, hf b]
  exact congrArg (cubeTuple ζ) (congrArg Subtype.val hab)

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
