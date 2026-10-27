module

public import CFSG.LieType.Chevalley.Canonical
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section Trace

variable {τ : Tag} {K : Type} [Field K]

theorem trace_eq_sum_coord (f : Module.End K (RootModule τ K)) :
    LinearMap.trace K (RootModule τ K) f = ∑ l : Label τ, f (Finsupp.single l 1) l := by
  classical
  rw [LinearMap.trace_eq_matrix_trace K (Finsupp.basisSingleOne (R := K) (ι := Label τ))]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply]

theorem trace_conj (g x : ModGL τ K) :
    LinearMap.trace K (RootModule τ K)
        ((g * x * g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) =
      LinearMap.trace K (RootModule τ K) (x : Module.End K (RootModule τ K)) := by
  rw [Units.val_mul, Units.val_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul]

theorem trace_rootDiagUnit (b : Fin τ.rank → Kˣ) :
    LinearMap.trace K (RootModule τ K)
        ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) =
      (τ.rank : K) + ∑ α : {v : Fin τ.rank → ℤ // IsRoot τ v}, ((rootChar b α.1 : Kˣ) : K) := by
  classical
  rw [trace_eq_sum_coord, Fintype.sum_sum_type]
  congr 1
  · have h : ∀ j : Fin τ.rank, ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K))
        (Finsupp.single (Sum.inl j) 1) (Sum.inl j) = 1 := fun j => by
      change rootDiag b _ _ = _
      rw [rootDiag_single_inl, Finsupp.single_eq_same]
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  · refine Finset.sum_congr rfl fun α _ => ?_
    change rootDiag b _ _ = _
    rw [rootDiag_single_inr, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rfl

theorem prod_weylElt_rootVec_exists (ω : List (Fin τ.rank)) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : ∃ ε : K,
      (((ω.map fun i => weylElt τ K i 1).prod : (Module.End K (RootModule τ K))ˣ) :
          Module.End K (RootModule τ K)) (rootVec τ K β) =
        ε • rootVec τ K ((coxeterSystem τ).wordProd ω • β) := by
  induction ω with
  | nil => exact ⟨1, by simp⟩
  | cons i ω ih =>
    obtain ⟨ε, h⟩ := ih
    refine ⟨((-1) ^ stringDown τ i ((coxeterSystem τ).wordProd ω • β) *
      (((1 : Kˣ) ^ (-∑ j, τ.cartan i j * ((coxeterSystem τ).wordProd ω • β) j) : Kˣ) : K)) * ε,
      ?_⟩
    have e : (coxeterSystem τ).wordProd (i :: ω) • β =
        reflect τ i ((coxeterSystem τ).wordProd ω • β) := by
      rw [CoxeterSystem.wordProd_cons, mul_smul]
      exact simple_smul i _
    rw [e, List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h, map_smul,
      weylElt_rootVec i 1 (IsRoot.smul hβ _), smul_smul, mul_comm ε]

theorem canonicalRep_rootVec_exists (w : WeylGroup τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ ε : K, (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
      (rootVec τ K β) = ε • rootVec τ K (w • β) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact prod_weylElt_rootVec_exists ω hβ

theorem hVecSum_apply_inl (c : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    RootWalk.hVecSum K c (Sum.inl j) = (c j : K) := by
  classical
  simp only [RootWalk.hVecSum, hVec, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, Sum.inl.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem rootDiag_hVecSum (b : Fin τ.rank → Kˣ) (c : Fin τ.rank → ℤ) :
    rootDiag b (RootWalk.hVecSum K c) = RootWalk.hVecSum K c := by
  simp only [RootWalk.hVecSum, map_sum, map_smul, hVec, rootDiag_single_inl]

theorem rootDiag_canonicalRep_coord_inr_of_ne (b : Fin τ.rank → Kˣ) (w : WeylGroup τ)
    (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) (hw : w • α.1 ≠ α.1) :
    rootDiag b ((canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K))
      (Finsupp.single (Sum.inr α) 1)) (Sum.inr α) = 0 := by
  classical
  obtain ⟨ε, hε⟩ := canonicalRep_rootVec_exists (K := K) w α.2
  rw [← FourGroupChevalley.rootVec_eq_single α.2, hε, map_smul,
    FourGroupChevalley.rootVec_eq_single (IsRoot.smul α.2 w), rootDiag_single_inr,
    Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg]
  · simp
  · intro h
    exact hw (congrArg Subtype.val (Sum.inr_injective h))

end Trace

section E8

variable {K : Type} [Field K]

@[expose] def e8Sign : Fin Tag.E8.rank → ℤ := ![1, -1, -1, 1, -1, 1, -1, 1]

theorem e8Sign_cartan : ∀ i j : Fin Tag.E8.rank,
    ((Tag.E8.cartan j i).natAbs : ℤ) * e8Sign j = e8Sign i * Tag.E8.cartan i j := by
  decide +kernel

theorem e8Sign_mul_self : ∀ i : Fin Tag.E8.rank, e8Sign i * e8Sign i = 1 := by
  decide +kernel

theorem e8Sign_eq : ∀ i : Fin Tag.E8.rank, e8Sign i = 1 ∨ e8Sign i = -1 := by
  decide +kernel

theorem hStep_e8Sign (i : Fin Tag.E8.rank) (c : Fin Tag.E8.rank → ℤ) :
    RootWalk.hStep Tag.E8 i (fun k => e8Sign k * c k) =
      fun k => e8Sign k * reflect Tag.E8 i c k := by
  classical
  funext k
  simp only [RootWalk.hStep, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : k = i
  · subst h
    simp only [if_true, mul_one, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, e8Sign_cartan k j, mul_assoc]
  · simp [h]

theorem foldr_hStep_e8Sign (ω : List (Fin Tag.E8.rank)) (c : Fin Tag.E8.rank → ℤ) :
    ω.foldr (RootWalk.hStep Tag.E8) (fun k => e8Sign k * c k) =
      fun k => e8Sign k * ω.foldr (reflect Tag.E8) c k := by
  induction ω with
  | nil => rfl
  | cons i ω ih => rw [List.foldr_cons, List.foldr_cons, ih, hStep_e8Sign]

theorem foldr_hStep_eq_E8 (ω : List (Fin Tag.E8.rank)) (c : Fin Tag.E8.rank → ℤ) :
    ω.foldr (RootWalk.hStep Tag.E8) c =
      fun k => e8Sign k * ω.foldr (reflect Tag.E8) (fun l => e8Sign l * c l) k := by
  have hc : c = fun k => e8Sign k * (e8Sign k * c k) := by
    funext k
    rw [← mul_assoc, e8Sign_mul_self, one_mul]
  have h := foldr_hStep_e8Sign ω (fun l => e8Sign l * c l)
  rw [← hc] at h
  exact h

theorem wordProd_smul_eq_foldr (ω : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    (coxeterSystem Tag.E8).wordProd ω • v = ω.foldr (reflect Tag.E8) v := by
  induction ω with
  | nil => simp
  | cons i ω ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem canonicalRep_hVec_inl_E8 (w : WeylGroup Tag.E8) (j : Fin Tag.E8.rank) :
    (canonicalRep (coxeterSystem Tag.E8) K w : Module.End K (RootModule Tag.E8 K))
        (hVec Tag.E8 K j) (Sum.inl j) =
      ((w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) j : K) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E8).exists_isReduced w
  rw [canonicalRep_wordProd hω, ← RootWalk.hVecSum_single, RootWalk.prod_weylElt_hVecSum,
    hVecSum_apply_inl]
  congr 1
  rw [foldr_hStep_eq_E8, ← wordProd_smul_eq_foldr]
  show e8Sign j * _ = _
  rcases e8Sign_eq j with h | h
  · have hs : (fun l => e8Sign l * (Pi.single j 1 : Fin Tag.E8.rank → ℤ) l) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl
        simp [h]
      · simp [hl]
    rw [hs, h, one_mul]
  · have hs : (fun l => e8Sign l * (Pi.single j 1 : Fin Tag.E8.rank → ℤ) l) =
        -Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl
        simp [h]
      · simp [hl]
    rw [hs, smul_neg, Pi.neg_apply, h, neg_one_mul, neg_neg]

theorem trace_rootDiagUnit_mul_canonicalRep_E8 (b : Fin Tag.E8.rank → Kˣ)
    (w : WeylGroup Tag.E8) (hw : ∀ α, IsRoot Tag.E8 α → w • α ≠ α) :
    LinearMap.trace K (RootModule Tag.E8 K)
        ((rootDiagUnit Tag.E8 b * canonicalRep (coxeterSystem Tag.E8) K w : ModGL Tag.E8 K) :
          Module.End K (RootModule Tag.E8 K)) =
      ((∑ j, (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) j : ℤ) : K) := by
  classical
  rw [trace_eq_sum_coord, Fintype.sum_sum_type, Int.cast_sum]
  have h2 : ∑ α : {v : Fin Tag.E8.rank → ℤ // IsRoot Tag.E8 v},
      ((rootDiagUnit Tag.E8 b * canonicalRep (coxeterSystem Tag.E8) K w : ModGL Tag.E8 K) :
        Module.End K (RootModule Tag.E8 K)) (Finsupp.single (Sum.inr α) 1) (Sum.inr α) = 0 := by
    refine Finset.sum_eq_zero fun α _ => ?_
    exact rootDiag_canonicalRep_coord_inr_of_ne b w α (hw α.1 α.2)
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  change rootDiag b ((canonicalRep (coxeterSystem Tag.E8) K w : Module.End K _)
    (hVec Tag.E8 K j)) (Sum.inl j) = _
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E8).exists_isReduced w
  have e := canonicalRep_hVec_inl_E8 (K := K) ((coxeterSystem Tag.E8).wordProd ω) j
  rw [canonicalRep_wordProd hω] at e ⊢
  rw [← RootWalk.hVecSum_single, RootWalk.prod_weylElt_hVecSum, rootDiag_hVecSum,
    ← RootWalk.prod_weylElt_hVecSum, RootWalk.hVecSum_single, e]

end E8

section Counts

variable {τ : Tag} {K : Type} [Field K]

@[expose] def charRes (k : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) : ZMod 3 :=
  ∑ i, k i * (v i : ZMod 3)

theorem rootChar_eq_pow_charRes {ω : Kˣ} (hω : ω ^ 3 = 1) (b : Fin τ.rank → Kˣ)
    (k : Fin τ.rank → ZMod 3) (hb : ∀ i, b i = ω ^ (k i).val) (v : Fin τ.rank → ℤ) :
    rootChar b v = ω ^ (charRes k v).val := by
  classical
  have hsum : ∀ s : Finset (Fin τ.rank),
      ∏ i ∈ s, b i ^ v i = ω ^ (∑ i ∈ s, ((k i).val : ℤ) * v i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add, ih, hb i, ← zpow_natCast,
        ← zpow_mul]
  rw [rootChar, hsum, zpow_eq_zpow_emod' _ hω, ← ZMod.val_intCast, zpow_natCast]
  congr 2
  simp only [charRes, Int.cast_sum, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

@[expose] noncomputable def resCount (k : Fin τ.rank → ZMod 3) (r : ZMod 3) : ℕ :=
  (Finset.univ.filter fun α : {v : Fin τ.rank → ℤ // IsRoot τ v} => charRes k α.1 = r).card

theorem trace_rootDiagUnit_of_counts {ω : Kˣ} (hω : ω ^ 3 = 1) (b : Fin τ.rank → Kˣ)
    (k : Fin τ.rank → ZMod 3) (hb : ∀ i, b i = ω ^ (k i).val) :
    LinearMap.trace K (RootModule τ K)
        ((rootDiagUnit τ b : ModGL τ K) : Module.End K (RootModule τ K)) =
      (τ.rank : K) + (resCount k 0 : K) + (resCount k 1 : K) * (ω : K) +
        (resCount k 2 : K) * (ω : K) ^ 2 := by
  classical
  rw [trace_rootDiagUnit]
  have h1 : ∀ α : {v : Fin τ.rank → ℤ // IsRoot τ v}, ((rootChar b α.1 : Kˣ) : K) =
      (ω : K) ^ (charRes k α.1).val := fun α => by
    rw [rootChar_eq_pow_charRes hω b k hb, Units.val_pow_eq_pow_val]
  simp only [h1]
  rw [← Finset.sum_fiberwise Finset.univ (fun α : {v : Fin τ.rank → ℤ // IsRoot τ v} =>
    charRes k α.1) fun α => (ω : K) ^ (charRes k α.1).val]
  have hfib : ∀ r : ZMod 3, ∑ α ∈ Finset.univ.filter
      (fun α : {v : Fin τ.rank → ℤ // IsRoot τ v} => charRes k α.1 = r),
        (ω : K) ^ (charRes k α.1).val = (resCount k r : K) * (ω : K) ^ r.val := by
    intro r
    rw [Finset.sum_congr rfl fun α hα => by rw [(Finset.mem_filter.1 hα).2],
      Finset.sum_const, nsmul_eq_mul]
    rfl
  simp only [hfib]
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h0 : (0 : ZMod 3).val = 0 := rfl
  have h1' : (1 : ZMod 3).val = 1 := rfl
  have h2' : (2 : ZMod 3).val = 2 := rfl
  rw [h0, h1', h2']
  ring

end Counts

theorem trace_rootDiagUnit_E8_of_counts {K : Type} [Field K] {ω : Kˣ}
    (hω : IsPrimitiveRoot ω 3) (b : Fin Tag.E8.rank → Kˣ) (k : Fin Tag.E8.rank → ZMod 3)
    (hb : ∀ i, b i = ω ^ (k i).val) (h0 : resCount k 0 = 78) (h1 : resCount k 1 = 81)
    (h2 : resCount k 2 = 81) :
    LinearMap.trace K (RootModule Tag.E8 K)
        ((rootDiagUnit Tag.E8 b : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K)) = 5 := by
  rw [trace_rootDiagUnit_of_counts hω.pow_eq_one b k hb, h0, h1, h2]
  have hω' : IsPrimitiveRoot (ω : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hω
  have hsum : (ω : K) ^ 2 + (ω : K) + 1 = 0 := by
    have := hω'.geom_sum_eq_zero (by norm_num)
    simpa [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc] using this
  have hr : ((Tag.E8.rank : ℕ) : K) = 8 := by norm_num [Tag.rank]
  rw [hr]
  push_cast
  linear_combination (81 : K) * hsum

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral
