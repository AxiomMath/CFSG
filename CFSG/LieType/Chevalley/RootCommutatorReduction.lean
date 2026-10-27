module

public import CFSG.LieType.Chevalley.RootCommutatorFamily
public import CFSG.LieType.Chevalley.RootCommutatorCheck
public import CFSG.LieType.Chevalley.LongestElement

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag}

namespace RootOps

theorem isRootB_iff
    {v : Fin τ.rank → ℤ} : isRootB τ v = true ↔ IsRoot τ v := by
  rw [isRootB, List.any_eq_true, RootCertificate.isRoot_iff τ.rootCertificate_check]
  simp only [List.mem_range, CFSG.LieType.Ree.vecBEq_iff]

theorem commPairsAt_eq (x y : ℕ) :
    commPairsAt τ x y = commPairs τ (τ.rootCertificate.root x) (τ.rootCertificate.root y) := by
  classical
  refine List.filter_congr fun p _ => ?_
  rw [Bool.eq_iff_iff, isRootB_iff, decide_eq_true_iff]
  exact Iff.rfl

theorem le_seven_of_isRoot
    {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) (j : Fin τ.rank) : v j ≤ 7 := by
  obtain ⟨k, -, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hv
  simp only [RootCertificate.root, decodeVec]
  generalize τ.rootCertificate.roots.getD k 0 / 16 ^ (j : ℕ) = m
  have : m % 16 < 16 := Nat.mod_lt _ (by norm_num)
  omega

theorem le_seven_of_isRoot_nsmul_add_nsmul
    {α β : Fin τ.rank → ℤ} (hα : ∀ j, 0 ≤ α j)
    (hβ : ∀ j, 0 ≤ β j) {k l : Fin τ.rank} (hk : 1 ≤ α k) (hl : 1 ≤ β l) {a b : ℕ}
    (h : IsRoot τ (a • α + b • β)) : a ≤ 7 ∧ b ≤ 7 := by
  have h1 := le_seven_of_isRoot h k
  have h2 := le_seven_of_isRoot h l
  simp only [Pi.add_apply, Pi.smul_apply] at h1 h2
  simp only [nsmul_eq_mul] at h1 h2
  have ha : (a : ℤ) ≤ 7 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℤ) a) (sub_nonneg.2 hk),
      mul_nonneg (Nat.cast_nonneg (α := ℤ) b) (hβ k)]
  have hb : (b : ℤ) ≤ 7 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℤ) b) (sub_nonneg.2 hl),
      mul_nonneg (Nat.cast_nonneg (α := ℤ) a) (hα l)]
  omega

theorem repShape_spec
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    r.1 < τ.rank ∧ 0 < height (τ.rootCertificate.root r.2.1) ∧
      r.2.2.map (fun f => (f.1, f.2.1)) =
        commPairs τ (τ.rootCertificate.root r.1) (τ.rootCertificate.root r.2.1) ∧
      boxCheck τ r.1 r.2.1 = true ∧
      ∀ f ∈ r.2.2, 1 ≤ |f.2.2.2| ∧ |f.2.2.2| ≤ commConstBound τ := by
  have h := repShapeCheck_repsOf τ
  rw [List.all_eq_true] at h
  have h' := h r hr
  simp only [repShapeCheck, Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, Nat.ble_eq] at h'
  obtain ⟨⟨⟨⟨hx, hy⟩, hkeys⟩, hbox⟩, hC⟩ := h'
  refine ⟨hx, hy, hkeys.trans (commPairsAt_eq _ _), hbox, fun f hf => ?_⟩
  obtain ⟨h1, h2⟩ := hC f hf
  rw [Int.abs_eq_natAbs]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem repCheck_of_mem
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    repCheck τ r.1 r.2.1 r.2.2 = true := by
  have h := repsCheck_repsOf τ
  simp only [repsCheck, List.all_eq_true] at h
  exact h r hr

theorem lt_length_of_mem_repsOf
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    r.1 < τ.rootCertificate.roots.length ∧ r.2.1 < τ.rootCertificate.roots.length := by
  have h := repCheck_of_mem hr
  simp only [repCheck, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

theorem mem_commPairs_rep
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) (p : ℕ × ℕ) :
    p ∈ commPairs τ (τ.rootCertificate.root r.1) (τ.rootCertificate.root r.2.1) ↔
      0 < p.1 ∧ 0 < p.2 ∧
        IsRoot τ (p.1 • τ.rootCertificate.root r.1 + p.2 • τ.rootCertificate.root r.2.1) := by
  obtain ⟨hx, hy, -, hbox, -⟩ := repShape_spec hr
  rw [mem_commPairs, mem_commCandidates]
  refine ⟨fun ⟨⟨⟨h1, _⟩, h2, _⟩, h⟩ => ⟨h1, h2, h⟩, fun ⟨h1, h2, h⟩ => ⟨?_, h⟩⟩
  obtain ⟨-, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have hα : τ.rootCertificate.root r.1 = Pi.single (⟨r.1, hx⟩ : Fin τ.rank) 1 := hb ⟨r.1, hx⟩
  have hyr := isRoot_rootCertificate_root (lt_length_of_mem_repsOf hr).2
  have hnn := (IsRoot.height_pos_iff hyr).1 hy
  obtain ⟨l, hl⟩ : ∃ l, 1 ≤ τ.rootCertificate.root r.2.1 l := by
    by_contra! hcon
    have : height (τ.rootCertificate.root r.2.1) ≤ 0 :=
      Finset.sum_nonpos fun j _ => by have := hcon j; omega
    omega
  obtain ⟨ha7, hb7⟩ := le_seven_of_isRoot_nsmul_add_nsmul (k := ⟨r.1, hx⟩)
    (fun j => by rw [hα, Pi.single_apply]; split_ifs <;> norm_num) hnn
    (by rw [hα]; simp) hl h
  simp only [boxCheck, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true, Bool.and_eq_true,
    Nat.ble_eq, Bool.not_eq_true'] at hbox
  rcases hbox p.1 ⟨h1, by omega⟩ p.2 ⟨h2, by omega⟩ with h3 | h3
  · omega
  · have h4 : isRootB τ (combAt τ r.1 r.2.1 (p.1, p.2)) = true := isRootB_iff.2 h
    rw [h3] at h4
    exact Bool.noConfusion h4

@[expose] def factorConst : List Factor → ℕ × ℕ → ℤ
  | [], _ => 0
  | f :: fs, p => if (f.1, f.2.1) = p then f.2.2.2 else factorConst fs p

theorem factorConst_of_mem {fs : List Factor} (hnd : (fs.map fun f => (f.1, f.2.1)).Nodup)
    {f : Factor} (hf : f ∈ fs) : factorConst fs (f.1, f.2.1) = f.2.2.2 := by
  induction fs with
  | nil => exact absurd hf List.not_mem_nil
  | cons g gs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [factorConst, ite_eq_left rfl]
    · have hne : (g.1, g.2.1) ≠ (f.1, f.2.1) := fun h =>
        hnd.1 (h ▸ List.mem_map.2 ⟨f, hf, rfl⟩)
      rw [factorConst, ite_eq_right hne]
      exact ih hnd.2 hf

section Family

variable {R : Type} [CommRing R]

theorem coe_prod_eltVec
    {fs : List Factor}
    (hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length) (c d : R) :
    (((fs.map fun f => (rootOperatorFamily τ).eltVec R (τ.rootCertificate.root f.2.2.1)
        ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod : (Module.End R (RootModule τ R))ˣ) :
        Module.End R (RootModule τ R)) = factorsProd τ R fs c d := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have hf := hfs f (List.mem_cons_self ..)
    rw [List.map_cons, List.prod_cons, Units.val_mul,
      ih fun g hg => hfs g (List.mem_cons_of_mem _ hg), factorsProd_cons, dite_eq_left hf,
      (rootOperatorFamily τ).eltVec_of_isRoot (isRoot_rootCertificate_root hf)]
    rfl

end Family

theorem coneOk_of_mem_repsOf
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    ∀ f ∈ r.2.2, coneOk τ r.1 r.2.1 f = true := by
  have hrep := repCheck_of_mem hr
  simp only [repCheck, Bool.and_eq_true, List.all_eq_true] at hrep
  exact hrep.1.2

theorem keys_nodup_of_mem_repsOf
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    (r.2.2.map fun f => (f.1, f.2.1)).Nodup :=
  (repShape_spec hr).2.2.1 ▸ commPairs_nodup _ _

theorem commFormula_rep
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    (rootOperatorFamily τ).CommFormula (τ.rootCertificate.root r.1)
      (τ.rootCertificate.root r.2.1) (factorConst r.2.2) := by
  have hcone := coneOk_of_mem_repsOf hr
  have hnd := keys_nodup_of_mem_repsOf hr
  obtain ⟨x, y, fs⟩ := r
  obtain ⟨-, -, hkeys, -, -⟩ := repShape_spec hr
  have hrep := repCheck_of_mem hr
  obtain ⟨hxl, hyl⟩ := lt_length_of_mem_repsOf hr
  simp only at hkeys hrep hxl hyl hcone hnd ⊢
  have hfs : ∀ f ∈ fs, f.2.2.1 < τ.rootCertificate.roots.length := fun f hf => by
    have := hcone f hf
    simp only [coneOk, Bool.and_eq_true, Nat.blt_eq] at this
    exact this.1.1.1
  intro R _ c d
  have hop := elt_mul_elt_of_repCheck (R := R) (RootOps.dataChecks τ).valid hrep
    (rootAt τ x hxl) (rootAt τ y hyl) (rootPos_rootAt _) (rootPos_rootAt _) c d
  have hunit : (rootOperatorFamily τ).eltVec R (τ.rootCertificate.root x) c *
      (rootOperatorFamily τ).eltVec R (τ.rootCertificate.root y) d =
      (fs.map fun f => (rootOperatorFamily τ).eltVec R (τ.rootCertificate.root f.2.2.1)
        ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod *
        (rootOperatorFamily τ).eltVec R (τ.rootCertificate.root y) d *
        (rootOperatorFamily τ).eltVec R (τ.rootCertificate.root x) c := by
    rw [(rootOperatorFamily τ).eltVec_of_isRoot (isRoot_rootCertificate_root hxl),
      (rootOperatorFamily τ).eltVec_of_isRoot (isRoot_rootCertificate_root hyl)]
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [coe_prod_eltVec hfs]
    exact hop
  rw [(rootOperatorFamily τ).eltVec_neg, (rootOperatorFamily τ).eltVec_neg, hunit]
  have e : ∀ P B A : (Module.End R (RootModule τ R))ˣ, P * B * A * A⁻¹ * B⁻¹ = P :=
    fun P B A => by group
  rw [e, ← hkeys, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun f hf => ?_)
  have hc := hcone f hf
  simp only [coneOk, Bool.and_eq_true, CFSG.LieType.Ree.vecBEq_iff] at hc
  rw [Function.comp_apply, hc.2, factorConst_of_mem hnd hf]

theorem hasCommFormula_rep
    {r : ℕ × ℕ × List Factor} (hr : r ∈ repsOf τ) :
    (rootOperatorFamily τ).HasCommFormula (commConstBound τ) (τ.rootCertificate.root r.1)
      (τ.rootCertificate.root r.2.1) := by
  obtain ⟨-, -, hkeys, -, hC⟩ := repShape_spec hr
  have hnd := keys_nodup_of_mem_repsOf hr
  refine ⟨factorConst r.2.2, fun p hp => ?_, commFormula_rep hr⟩
  rw [← hkeys, List.mem_map] at hp
  obtain ⟨f, hf, rfl⟩ := hp
  rw [factorConst_of_mem hnd hf]
  exact hC f hf

theorem exists_smul_rep_of_pos
    (j : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hpos : 0 < height β) (hne : β ≠ Pi.single j 1) :
    ∃ r ∈ repsOf τ, ∃ w : WeylGroup τ, w • τ.rootCertificate.root r.1 = Pi.single j 1 ∧
      w • τ.rootCertificate.root r.2.1 = β := by
  have hcover := coverCheck_coverOf τ
  simp only [coverCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at hcover
  obtain ⟨hpairs, hwalk⟩ := hcover
  have hmem := mem_neededPairs j ⟨β, hβ⟩ hpos fun h => hne (congrArg Subtype.val h)
  rw [← hpairs, List.mem_map] at hmem
  obtain ⟨e, he, hpe⟩ := hmem
  obtain ⟨hr, hw⟩ := hwalk e he
  set x := (repsOf τ).getD (coverRep e) (0, 0, []) with hx
  have hxmem : x ∈ repsOf τ := by
    rw [hx, List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  have hab := lt_length_of_mem_repsOf hxmem
  set w := decodeWord τ 64 (coverWord e)
  obtain ⟨-, -, h3, h4⟩ := walkPair_spec (RootOps.dataChecks τ).tab w hab.1 hab.2
  have hw' : walkPair τ w (x.1, x.2.1) = ((j : ℕ), rootPos ⟨β, hβ⟩) := by
    rw [← hpe]
    exact hw
  rw [hw'] at h3 h4
  obtain ⟨-, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  exact ⟨x, hxmem, (w.map (simple τ)).prod, h3.symm.trans (hb j),
    h4.symm.trans (root_rootPos ⟨β, hβ⟩)⟩

theorem longest_smul_single
    (j : Fin τ.rank) :
    ∃ k : Fin τ.rank, ((((longestWord τ).map τ.idx).map (simple τ)).prod •
      (Pi.single j 1 : Fin τ.rank → ℤ)) = -Pi.single k 1 := by
  have h := longestCheck_eq τ
  simp only [longestCheck, List.all_eq_true, List.mem_finRange, true_implies, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨k, -, hk⟩ := h j
  obtain ⟨hr, hb, -⟩ := rootCertificate_basis_table (τ := τ)
  have hj : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 hr
  obtain ⟨-, -, h3, -⟩ := walkPair_spec (RootOps.dataChecks τ).tab
    ((longestWord τ).map τ.idx) hj hj
  refine ⟨k, ?_⟩
  rw [← hb j, ← h3, hk, rootCertificate_root_image (lt_of_lt_of_le k.2 hr), hb k,
    reflect_single_self]

theorem exists_smul_rep_of_single
    (j : Fin τ.rank) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hne : β ≠ Pi.single j 1) (hne' : β ≠ -Pi.single j 1) :
    ∃ r ∈ repsOf τ, ∃ w : WeylGroup τ, w • τ.rootCertificate.root r.1 = Pi.single j 1 ∧
      w • τ.rootCertificate.root r.2.1 = β := by
  rcases IsRoot.height_pos_or_neg hβ with hpos | hneg
  · exact exists_smul_rep_of_pos j hβ hpos hne
  set u : WeylGroup τ := (((longestWord τ).map τ.idx).map (simple τ)).prod
  have hrev : ReversesSigns u := fun α hα hpos => height_smul_neg_of_forall_single (fun i => by
    obtain ⟨k, hk⟩ := longest_smul_single (τ := τ) i
    rw [hk, height_neg, height_single]
    norm_num) hα hpos
  obtain ⟨k, hk⟩ := longest_smul_single (τ := τ) j
  set v := u * simple τ j
  have hv1 : v • (Pi.single j 1 : Fin τ.rank → ℤ) = Pi.single k 1 := by
    rw [mul_smul, simple_smul, reflect_single_self, smul_neg, hk, neg_neg]
  have hsj : height (simple τ j • β) < 0 := by
    have := height_reflect_pos (IsRoot.neg hβ) (by rw [height_neg]; omega)
      fun h => hne' (neg_eq_iff_eq_neg.1 h)
    rw [← simple_smul, smul_neg, height_neg] at this
    omega
  have hv2 : 0 < height (v • β) := by
    rw [mul_smul]
    exact hrev.height_smul_pos (IsRoot.smul hβ _) hsj
  have hne2 : v • β ≠ Pi.single k 1 := fun h => hne (smul_left_cancel v (h.trans hv1.symm))
  obtain ⟨r, hr, w, hw1, hw2⟩ := exists_smul_rep_of_pos k (IsRoot.smul hβ v) hv2 hne2
  refine ⟨r, hr, v⁻¹ * w, ?_, ?_⟩
  · rw [mul_smul, hw1, ← hv1, inv_smul_smul]
  · rw [mul_smul, hw2, inv_smul_smul]

theorem exists_smul_rep
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ r ∈ repsOf τ, ∃ w : WeylGroup τ, w • τ.rootCertificate.root r.1 = α ∧
      w • τ.rootCertificate.root r.2.1 = β := by
  obtain ⟨w₁, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  have hne1 : w₁⁻¹ • β ≠ Pi.single j 1 := fun h => hne (by rw [← h, smul_inv_smul])
  have hne2 : w₁⁻¹ • β ≠ -Pi.single j 1 := fun h => by
    have : β = -(w₁ • Pi.single j 1) := by rw [← smul_neg, ← h, smul_inv_smul]
    exact hne' (by rw [this, neg_neg])
  obtain ⟨r, hr, w, h1, h2⟩ := exists_smul_rep_of_single j (IsRoot.smul hβ _) hne1 hne2
  exact ⟨r, hr, w₁ * w, by rw [mul_smul, h1], by rw [mul_smul, h2, smul_inv_smul]⟩

end RootOps

open RootOps

theorem hasCommFormula_of_isRoot
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) :
    (rootOperatorFamily τ).HasCommFormula (commConstBound τ) α β := by
  obtain ⟨r, hr, w, rfl, rfl⟩ := exists_smul_rep hα hβ hne hne'
  exact (hasCommFormula_rep hr).smul w

theorem mem_commPairs_iff_of_isRoot
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) (p : ℕ × ℕ) :
    p ∈ commPairs τ α β ↔ 0 < p.1 ∧ 0 < p.2 ∧ IsRoot τ (p.1 • α + p.2 • β) := by
  obtain ⟨r, hr, w, rfl, rfl⟩ := exists_smul_rep hα hβ hne hne'
  rw [commPairs_smul, ← smul_nsmul_add_nsmul_eq, isRoot_smul_iff]
  exact mem_commPairs_rep hr p

theorem exists_commPairs_eq_rep
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (hne : α ≠ β) (hne' : α ≠ -β) :
    ∃ r ∈ repsOf τ, commPairs τ α β = r.2.2.map fun f => (f.1, f.2.1) := by
  obtain ⟨r, hr, w, rfl, rfl⟩ := exists_smul_rep hα hβ hne hne'
  exact ⟨r, hr, by rw [commPairs_smul, (repShape_spec hr).2.2.1]⟩

end CFSG.LieType.Chevalley
