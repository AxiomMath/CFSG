module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticTransvection
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.MonE7Order
public import CFSG.ClassicalGroups.Alternating.Generation
public import Certificates.Certificate10093
public import Certificates.Certificate10097
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial

namespace SevenTransvectionE7

open LinearMap (BilinForm)
open CFSG.YGroups (YGroup yGen yRels)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)

@[expose] def pairing (x y : Fin 6 → ZMod 2) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 1 * y 2 + x 2 * y 1 + x 2 * y 3 + x 3 * y 2 + x 0 * y 4 + x 4 * y 0 +
    x 4 * y 5 + x 5 * y 4

@[expose] def b0 : BilinForm (ZMod 2) (Fin 6 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) pairing
    (fun x x' y => by simp only [pairing, Pi.add_apply]; ring)
    (fun c x y => by simp only [pairing, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [pairing, Pi.add_apply]; ring)
    (fun c x y => by simp only [pairing, Pi.smul_apply, smul_eq_mul]; ring)

theorem b0_apply (x y : Fin 6 → ZMod 2) : b0 x y = pairing x y :=
  rfl

@[expose] def e7Edges : Finset (Sym2 (Fin 7)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(0, 4), s(4, 5), s(0, 6)}

@[expose] def vE : Fin 7 → Fin 6 → ZMod 2 :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1, Pi.single 5 1,
    Pi.single 1 1 + Pi.single 3 1]

theorem b0_isAlt : b0.IsAlt := by
  intro x
  rw [b0_apply, pairing]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 0 * x 4 + x 4 * x 5) * h2

theorem b0_symm (x y : Fin 6 → ZMod 2) : b0 y x = b0 x y :=
  BinarySymplecticTransvection.symm_apply b0_isAlt x y

theorem eq_zero_of_forall_b0 {x : Fin 6 → ZMod 2} (h : ∀ y, b0 x y = 0) : x = 0 := by
  have h3 := h (Pi.single 3 1)
  have h5 := h (Pi.single 5 1)
  have h1 := h (Pi.single 1 1)
  have h4 := h (Pi.single 4 1)
  have h2 := h (Pi.single 2 1)
  have h0 := h (Pi.single 0 1)
  simp only [b0_apply, pairing, Pi.single_apply] at h3 h5 h1 h4 h2 h0
  norm_num at h3 h5 h1 h4 h2 h0
  rw [h3, add_zero] at h1
  rw [h1, zero_add] at h4
  rw [h5, add_zero] at h0
  rw [h0, zero_add] at h2
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4, h5]

theorem b0_nondegenerate : b0.Nondegenerate :=
  ⟨fun _ hx => eq_zero_of_forall_b0 hx,
    fun y hy => eq_zero_of_forall_b0 fun x => (b0_symm y x).symm.trans (hy x)⟩

theorem vE_pairing : ∀ i j : Fin 7, i ≠ j → (pairing (vE i) (vE j) = 1 ↔ s(i, j) ∈ e7Edges) := by
  decide

theorem vE_pairing_zero : ∀ i j : Fin 7, i ≠ j → s(i, j) ∉ e7Edges → pairing (vE i) (vE j) = 0 := by
  decide

theorem vE_ne_zero : ∀ i : Fin 7, vE i ≠ 0 := by
  decide

theorem vE_injective : ∀ i j : Fin 7, i ≠ j → vE i ≠ vE j := by
  decide

@[expose] def bitVec (n : ℕ) : Fin 6 → ZMod 2 :=
  fun i => if n.testBit i then 1 else 0

@[expose] def bitVal (v : Fin 6 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val + 16 * (v 4).val + 32 * (v 5).val

theorem bitVal_bitVec : ∀ n < 64, bitVal (bitVec n) = n := by
  decide

theorem bitVec_xor (a b : ℕ) : bitVec (a ^^^ b) = bitVec a + bitVec b := by
  funext i
  simp only [bitVec, Pi.add_apply, Nat.testBit_xor]
  generalize a.testBit i = p
  generalize b.testBit i = q
  revert p q
  decide

theorem bitVec_injOn {m n : ℕ} (hm : m < 64) (hn : n < 64) (h : bitVec m = bitVec n) : m = n := by
  rw [← bitVal_bitVec m hm, ← bitVal_bitVec n hn, h]

theorem exists_bitVec_eq {v : Fin 6 → ZMod 2} (hv : v ≠ 0) :
    ∃ n, n < 64 ∧ n ≠ 0 ∧ bitVec n = v := by
  classical
  have hS : ∀ n ∈ (Finset.range 64).erase 0, n < 64 ∧ n ≠ 0 := fun n hn => by
    rw [Finset.mem_erase, Finset.mem_range] at hn
    exact ⟨hn.2, hn.1⟩
  have hinj : Set.InjOn bitVec ((Finset.range 64).erase 0 : Set ℕ) := fun m hm n hn h =>
    bitVec_injOn (hS m hm).1 (hS n hn).1 h
  have hne : ∀ n ∈ (Finset.range 64).erase 0, bitVec n ≠ 0 := by
    intro n hn h0
    apply (hS n hn).2
    rw [← bitVal_bitVec n (hS n hn).1, h0]
    rfl
  have himg : ((Finset.range 64).erase 0).image bitVec = Finset.univ.erase 0 := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_erase.mpr ⟨hne n hn, Finset.mem_univ _⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
        Finset.card_erase_of_mem (by simp), Finset.card_range]
      norm_num
  have hvmem : v ∈ Finset.univ.erase 0 := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩
  rw [← himg] at hvmem
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hvmem
  exact ⟨n, (hS n hn).1, (hS n hn).2, rfl⟩

@[expose] def initLabels : List ℕ := [1, 2, 4, 8, 16, 32, 10]

theorem vE_eq_bitVec : ∀ i : Fin 7, vE i = bitVec (initLabels.getD i 0) := by
  decide

@[expose] def chainSteps : List (ℕ × ℕ × ℕ) :=
  [(3, 1, 2), (11, 1, 10), (17, 1, 16), (6, 2, 4), (7, 1, 6), (9, 2, 11), (19, 2, 17),
    (12, 4, 8), (14, 2, 12), (15, 1, 14), (13, 4, 9), (23, 4, 19), (5, 8, 13), (21, 5, 16),
    (20, 1, 21), (22, 2, 20), (18, 4, 22), (28, 8, 20), (29, 1, 28), (30, 2, 28), (24, 4, 28),
    (25, 1, 24), (27, 2, 25), (31, 8, 23), (48, 16, 32), (49, 1, 48), (51, 2, 49), (55, 4, 51),
    (53, 5, 48), (52, 1, 53), (54, 2, 52), (50, 4, 54), (60, 8, 52), (61, 1, 60), (62, 2, 60),
    (56, 4, 60), (57, 1, 56), (59, 2, 57), (63, 8, 55), (34, 16, 50), (35, 1, 34), (33, 2, 35),
    (38, 4, 34), (39, 1, 38), (36, 2, 38), (44, 8, 36), (46, 2, 44), (47, 1, 46), (40, 4, 44),
    (45, 5, 40), (41, 4, 45), (43, 2, 41), (42, 1, 43), (37, 8, 45), (58, 16, 42),
    (26, 32, 58)]

@[expose] def chainOK : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | known, (c, a, b) :: rest =>
    decide (a ∈ known ∧ b ∈ known ∧ c = a ^^^ b ∧ pairing (bitVec a) (bitVec b) = 1) &&
      chainOK (c :: known) rest

theorem chainOK_chainSteps : chainOK initLabels chainSteps = true := by
  decide

theorem chain_covers : ∀ n < 64, n ≠ 0 → n ∈ initLabels ++ chainSteps.map Prod.fst := by
  decide

theorem mem_of_chainOK {G : Type*} [Group G] (H : Subgroup G) (τ : (Fin 6 → ZMod 2) → G)
    (hstep : ∀ a b, τ a ∈ H → τ b ∈ H → pairing a b = 1 → τ (a + b) ∈ H) :
    ∀ (steps : List (ℕ × ℕ × ℕ)) (known : List ℕ), (∀ n ∈ known, τ (bitVec n) ∈ H) →
      chainOK known steps = true → ∀ n ∈ known ++ steps.map Prod.fst, τ (bitVec n) ∈ H
  | [], known, hk, _ => by simpa using hk
  | (c, a, b) :: rest, known, hk, hok => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨ha, hb, rfl, hab⟩, hrest⟩ := hok
    have hc : τ (bitVec (a ^^^ b)) ∈ H := by
      rw [bitVec_xor]
      exact hstep _ _ (hk a ha) (hk b hb) hab
    have hall := mem_of_chainOK H τ hstep rest ((a ^^^ b) :: known) (by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hc
      · exact hk n hn) hrest
    intro n hn
    apply hall
    simp only [List.mem_append, List.mem_cons, List.map_cons] at hn ⊢
    tauto

local notation "tau" => binarySymplecticTransvection b0 b0_isAlt

theorem tau_mem_closure (a : Fin 6 → ZMod 2) :
    tau a ∈ Subgroup.closure (Set.range fun i : Fin 7 => tau (vE i)) := by
  set H := Subgroup.closure (Set.range fun i : Fin 7 => tau (vE i)) with hH
  by_cases ha : a = 0
  · rw [ha, BinarySymplecticTransvection.zero_eq_one]
    exact one_mem H
  have hstep : ∀ a b, tau a ∈ H → tau b ∈ H → pairing a b = 1 → tau (a + b) ∈ H := by
    intro a b ha hb hab
    have h := BinarySymplecticTransvection.mul_mul_self b0_isAlt a b
    rw [b0_apply, hab, one_smul] at h
    rw [← h]
    exact mul_mem (mul_mem hb ha) hb
  have hinit : ∀ n ∈ initLabels, tau (bitVec n) ∈ H := by
    intro n hn
    obtain ⟨i, hi⟩ : ∃ i : Fin 7, initLabels.getD i 0 = n := by
      revert n
      decide
    rw [← hi, ← vE_eq_bitVec]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨n, hn, hn0, rfl⟩ := exists_bitVec_eq ha
  exact mem_of_chainOK H tau hstep chainSteps initLabels hinit chainOK_chainSteps n
    (chain_covers n hn hn0)

theorem symplecticTransvection_one (a : Fin 6 → ZMod 2) :
    CFSG.ClassicalGroups.Alternating.symplecticTransvection b0 b0_isAlt a 1 = tau a :=
  BinarySymplecticTransvection.gl_ext fun x => by
    rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
    rfl

theorem closure_tau_vE :
    Subgroup.closure (Set.range fun i : Fin 7 => tau (vE i)) = bilinIsometryGroup b0 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact BinarySymplecticTransvection.transvection_mem_bilinIsometryGroup b0_isAlt _
  · rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation b0_isAlt
      b0_nondegenerate, Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    rcases BinarySymplecticTransvection.zmod_two_cases c with rfl | rfl
    · rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_zero]
      exact one_mem _
    · rw [symplecticTransvection_one]
      exact tau_mem_closure a

theorem card_bilinIsometryGroup_b0 : Nat.card (bilinIsometryGroup b0) = 1451520 := by
  obtain ⟨e, he⟩ := BinarySymplecticSix.exists_isSymplecticBasis b0_isAlt b0_nondegenerate
    (n := 3) (by rw [Module.finrank_fin_fun])
  rw [Nat.card_congr (BinarySymplecticSix.spCoord he).toEquiv,
    (SymplecticFlag.symplectic_higher_order_and_Sylow (K := ZMod 2) 2 2 (Nat.card_zmod 2)
      (r := 3) (by norm_num)).1]
  decide

@[expose] def IsW7Family {H : Type*} [Group H] (y : Fin 7 → H) : Prop :=
  (∀ i, y i ^ 2 = 1) ∧ (∀ i j, s(i, j) ∈ e7Edges → (y i * y j) ^ 3 = 1) ∧
    ∀ i j, i ≠ j → s(i, j) ∉ e7Edges → (y i * y j) ^ 2 = 1

@[expose] def extendFam {H : Type*} [Group H] (y : Fin 7 → H) : ℕ → H :=
  fun c => if h : c < 7 then y ⟨c, h⟩ else 1

theorem evalWord_replicate_pair {H : Type*} [Group H] (img : ℕ → H) (m a b : ℕ) :
    evalWord img (List.replicate m [a, b]).flatten = (img a * img b) ^ m := by
  induction m with
  | zero => simp [evalWord]
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, CFSG.Certificates.CosetEnumeration.evalWord_append,
      ih, pow_succ']
    simp [evalWord, mul_assoc]

theorem yEdges_iff : ∀ i j : Fin 7, i < j →
    (((i : ℕ), (j : ℕ)) ∈ CFSG.YGroups.yEdges 3 2 1 ↔ s(i, j) ∈ e7Edges) := by
  decide

theorem rels_of_isW7Family {H : Type*} [Group H] {y : Fin 7 → H} (hy : IsW7Family y) :
    ∀ w ∈ yRels 3 2 1, evalWord (extendFam y) w = 1 := by
  obtain ⟨hsq, hedge, hnon⟩ := hy
  intro w hw
  simp only [yRels, CFSG.YGroups.ngen, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hw
  rcases hw with (⟨s, hs, rfl⟩ | ⟨s, hs, t, ⟨ht, hst⟩, rfl⟩) | hsp
  · have hs' : s < 7 := by omega
    simp only [evalWord_cons, evalWord_nil, mul_one, extendFam, hs', dite_true]
    rw [← pow_two, hsq]
  · have hs' : s < 7 := by omega
    have ht' : t < 7 := by omega
    rw [CFSG.YGroups.pairWord, evalWord_replicate_pair]
    simp only [extendFam, hs', ht', dite_true]
    have hlt : (⟨s, hs'⟩ : Fin 7) < ⟨t, ht'⟩ := hst
    unfold CFSG.YGroups.pairExp
    split_ifs with he
    · exact hedge _ _ ((yEdges_iff _ _ hlt).mp he)
    · exact hnon _ _ (ne_of_lt hlt) fun h => he ((yEdges_iff _ _ hlt).mpr h)
  · simp at hsp

@[expose] noncomputable def w7Hom {H : Type*} [Group H] {y : Fin 7 → H} (hy : IsW7Family y) :
    YGroup 3 2 1 →* H :=
  CFSG.YGroups.yModelHom (extendFam y) (rels_of_isW7Family hy)

theorem w7Hom_yGen {H : Type*} [Group H] {y : Fin 7 → H} (hy : IsW7Family y) (i : Fin 7) :
    w7Hom hy (yGen 3 2 1 i) = y i := by
  rw [w7Hom, CFSG.YGroups.yModelHom_yGen (by have := i.2; simp only [CFSG.YGroups.ngen]; omega)]
  simp [extendFam]

theorem range_w7Hom {H : Type*} [Group H] {y : Fin 7 → H} (hy : IsW7Family y) :
    (w7Hom hy).range = Subgroup.closure (Set.range y) := by
  rw [w7Hom, CFSG.YGroups.range_yModelHom]
  congr 1
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c < 7 := by simpa [CFSG.YGroups.ngen] using hc
    exact ⟨⟨c, hc'⟩, by simp [extendFam, hc']⟩
  · rintro ⟨i, rfl⟩
    refine ⟨i, by have := i.2; simp only [CFSG.YGroups.ngen, Set.mem_Iio]; omega, ?_⟩
    simp [extendFam]

theorem pairExp_eq : ∀ i j : Fin 7, i ≠ j →
    CFSG.YGroups.pairExp 3 2 1 (min (i : ℕ) j) (max (i : ℕ) j) =
      if s(i, j) ∈ e7Edges then 3 else 2 := by
  decide

theorem ne_of_mem_e7Edges : ∀ i j : Fin 7, s(i, j) ∈ e7Edges → i ≠ j := by
  decide

theorem isW7Family_yGen : IsW7Family fun i : Fin 7 => yGen 3 2 1 i := by
  refine ⟨fun i => by rw [pow_two, CFSG.YGroups.yGen_mul_self], fun i j hij => ?_,
    fun i j hne hij => ?_⟩
  · have hne := ne_of_mem_e7Edges i j hij
    have h := MonE7.yGen_pair_pow' i.2 j.2 (fun h => hne (Fin.ext h))
    rw [pairExp_eq i j hne] at h
    simpa only [hij, ite_true] using h
  · have h := MonE7.yGen_pair_pow' i.2 j.2 (fun h => hne (Fin.ext h))
    rw [pairExp_eq i j hne] at h
    simpa only [hij, ite_false] using h

theorem pow_eq_one_of_orderOf_eq {G : Type*} [Monoid G] {g : G} {n : ℕ} (h : orderOf g = n) :
    g ^ n = 1 := by
  rw [← h]
  exact pow_orderOf_eq_one g

theorem isW7Family_tau : IsW7Family fun i : Fin 7 => tau (vE i) := by
  refine ⟨fun i => by rw [pow_two]; exact BinarySymplecticTransvection.mul_self b0_isAlt (vE i),
    fun i j hij => ?_, fun i j hne hij => ?_⟩
  · exact pow_eq_one_of_orderOf_eq (BinarySymplecticTransvection.orderOf_mul_of_eq_one b0_isAlt
      b0_nondegenerate ((vE_pairing i j (ne_of_mem_e7Edges i j hij)).mpr hij))
  · exact pow_eq_one_of_orderOf_eq (BinarySymplecticTransvection.orderOf_mul_of_eq_zero b0_isAlt
      b0_nondegenerate (vE_ne_zero i) (vE_injective i j hne) (vE_pairing_zero i j hne hij))

theorem eq_of_pow_three {Q : Type*} [CommGroup Q] {a b : Q} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : (a * b) ^ 3 = 1) : a = b := by
  have h1 : a * b = 1 := by
    rwa [mul_pow, pow_succ, ha, one_mul, pow_succ, hb, one_mul] at h
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hb])
  rw [eq_inv_of_mul_eq_one_left h1, hb']

theorem card_commutator_w7 : Nat.card (commutator (YGroup 3 2 1)) = 1451520 := by
  have : Finite (YGroup 3 2 1) := CFSG.YGroups.y321.1
  have hW : Nat.card (YGroup 3 2 1) = 2903040 :=
    MonE7.e7_exact_order_and_central_involution.2.2.1
  set π := (Abelianization.of : YGroup 3 2 1 →* Abelianization (YGroup 3 2 1)) with hπ
  have hπs : ∀ i : Fin 7, π (yGen 3 2 1 i) ^ 2 = 1 := fun i => by
    rw [← map_pow, isW7Family_yGen.1 i, map_one]
  have hadj : ∀ i j : Fin 7, s(i, j) ∈ e7Edges → π (yGen 3 2 1 i) = π (yGen 3 2 1 j) :=
    fun i j h => eq_of_pow_three (hπs i) (hπs j) (by
      rw [← map_mul, ← map_pow, isW7Family_yGen.2.1 i j h, map_one])
  have hall : ∀ i : Fin 7, π (yGen 3 2 1 i) = π (yGen 3 2 1 0) := by
    have e01 := hadj 0 1 (by decide)
    have e12 := hadj 1 2 (by decide)
    have e23 := hadj 2 3 (by decide)
    have e04 := hadj 0 4 (by decide)
    have e45 := hadj 4 5 (by decide)
    have e06 := hadj 0 6 (by decide)
    intro i
    fin_cases i
    · rfl
    · exact e01.symm
    · exact (e01.trans e12).symm
    · exact ((e01.trans e12).trans e23).symm
    · exact e04.symm
    · exact (e04.trans e45).symm
    · exact e06.symm
  have hle : Nat.card (Abelianization (YGroup 3 2 1)) ≤ 2 := by
    have htop : (⊤ : Subgroup (Abelianization (YGroup 3 2 1))) ≤
        Subgroup.zpowers (π (yGen 3 2 1 0)) := by
      have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr fun q => by
        obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (s := commutator (YGroup 3 2 1)) q
        exact ⟨a, rfl⟩
      rw [← hrange, MonoidHom.range_eq_map, ← CFSG.YGroups.closure_yGen 3 2 1,
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      have hc' : c < 7 := by simpa [CFSG.YGroups.ngen] using hc
      have := hall ⟨c, hc'⟩
      simp only at this
      rw [SetLike.mem_coe, this]
      exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le htop
    rw [Subgroup.card_top, Nat.card_zpowers] at h1
    exact h1.trans (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hπs 0)))
  have hsign : IsW7Family fun _ : Fin 7 => (Multiplicative.ofAdd (1 : ZMod 2)) :=
    ⟨fun _ => by show Multiplicative.ofAdd (1 : ZMod 2) ^ 2 = 1; decide,
      fun _ _ _ => by
        show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1) ^ 3 = 1; decide,
      fun _ _ _ _ => by
        show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1) ^ 2 = 1; decide⟩
  set σ := w7Hom hsign with hσ
  have hσs : σ (yGen 3 2 1 0) = Multiplicative.ofAdd 1 := w7Hom_yGen hsign 0
  have hσrange : Nat.card σ.range = 2 := by
    have hσtop : σ.range = ⊤ := by
      rw [eq_top_iff]
      intro m _
      rcases BinarySymplecticTransvection.zmod_two_cases (Multiplicative.toAdd m) with h | h
      · have hm : m = 1 := h
        rw [hm]
        exact one_mem _
      · have hm : m = Multiplicative.ofAdd 1 := h
        rw [hm, ← hσs]
        exact ⟨_, rfl⟩
    rw [hσtop, Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  have hker : commutator (YGroup 3 2 1) ≤ σ.ker := Abelianization.commutator_subset_ker σ
  have hdvd : 2 ∣ (commutator (YGroup 3 2 1)).index := by
    have h := Subgroup.index_dvd_of_le hker
    rwa [Subgroup.index_ker, hσrange] at h
  have hidx : (commutator (YGroup 3 2 1)).index = 2 := by
    have hpos : (commutator (YGroup 3 2 1)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle' : (commutator (YGroup 3 2 1)).index ≤ 2 := hle
    obtain ⟨k, hk⟩ := hdvd
    omega
  have h := (commutator (YGroup 3 2 1)).card_mul_index
  rw [hidx, hW] at h
  omega

theorem card_le_of_perfect {Y : Type*} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    {y : Fin 7 → Y} (hgen : Subgroup.closure (Set.range y) = ⊤) (hy : IsW7Family y) :
    Nat.card Y ≤ 1451520 := by
  have : Finite (YGroup 3 2 1) := CFSG.YGroups.y321.1
  have hrange : (w7Hom hy).range = ⊤ := by rw [range_w7Hom, hgen]
  have hmap : (commutator (YGroup 3 2 1)).map (w7Hom hy) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, hrange,
      ← commutator_def]
    exact hperf.commutator_eq_top
  calc Nat.card Y = Nat.card (⊤ : Subgroup Y) := Subgroup.card_top.symm
    _ = Nat.card ((commutator (YGroup 3 2 1)).map (w7Hom hy)) := by rw [hmap]
    _ ≤ Nat.card (commutator (YGroup 3 2 1)) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ (w7Hom hy))
    _ = 1451520 := card_commutator_w7

end SevenTransvectionE7

universe u

end CFSG.LocalAnalysis.ComponentInitial
