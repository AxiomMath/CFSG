module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Model

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem gen3_mul_self (s : Fin 12) : gen3 s * gen3 s = 1 := stT_mul_self _ _ _ _

theorem prod_reverse_of_mul_self {G : Type*} [Group G] (f : Fin 12 → G)
    (hf : ∀ s, f s * f s = 1) (w : List (Fin 12)) :
    (w.reverse.map f).prod = ((w.map f).prod)⁻¹ := by
  induction w with
  | nil => simp
  | cons x w ih =>
    simp only [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_cons,
      List.prod_cons, List.map_nil, List.prod_nil, mul_one, _root_.mul_inv_rev,
      inv_eq_of_mul_eq_one_right (hf x)]

theorem f4_ofNat_mul (c f : ℕ) (hc : c < 4) (hf : f < 4) :
    (⟨Fin.ofNat 4 (mulN c f)⟩ : F4) = ⟨Fin.ofNat 4 c⟩ * ⟨Fin.ofNat 4 f⟩ := by
  interval_cases c <;> interval_cases f <;> rfl

theorem prod_wordX {a b : Fin 3} (hab : a ≠ b) {k : ℕ} (hk : k < 4) :
    ((wordX a b k).map gen3).prod = st3 a b ⟨Fin.ofNat 4 k⟩ := by
  have h1 := gen3_genIdx hab 0
  have h2 := gen3_genIdx hab 1
  simp only [Fin.val_zero, Fin.val_one, zero_add, Fin.isValue] at h1 h2
  interval_cases k
  · rw [st3, show (⟨Fin.ofNat 4 0⟩ : F4) = 0 from rfl, stT_zero]; rfl
  · have : wordX a b 1 = [genIdx a b 0] := rfl
    rw [this, List.map_singleton, List.prod_singleton, h1]
  · have : wordX a b 2 = [genIdx a b 1] := rfl
    rw [this, List.map_singleton, List.prod_singleton, h2]
  · have : wordX a b 3 = [genIdx a b 0, genIdx a b 1] := rfl
    rw [this, List.map_cons, List.map_singleton, List.prod_cons, List.prod_singleton, h1, h2, st3,
      st3, st3, stT_add _ hab]
    rfl

theorem prod_relWord {a b d e : Fin 3} (hab : a ≠ b) (hde : d ≠ e) (hex : ¬ (d = b ∧ e = a))
    {c f : ℕ} (hc : c < 4) (hf : f < 4) : ((relWord a b c d e f).map gen3).prod = 1 := by
  have hmul : mulN c f < 4 := by
    rw [mulN]; omega
  rw [relWord]
  simp only [List.map_append, List.prod_append]
  rw [prod_reverse_of_mul_self gen3 gen3_mul_self, prod_reverse_of_mul_self gen3 gen3_mul_self,
    prod_reverse_of_mul_self gen3 gen3_mul_self, prod_wordX hab hc, prod_wordX hde hf]
  have hcomm := stT_comm (F := F4) (m := 2) (by norm_num) hab hde hex ⟨Fin.ofNat 4 c⟩
    ⟨Fin.ofNat 4 f⟩
  rw [← f4_ofNat_mul c f hc hf] at hcomm
  rw [commutatorElement_def] at hcomm
  have hneg : -(⟨Fin.ofNat 4 (mulN c f)⟩ : F4) = ⟨Fin.ofNat 4 (mulN c f)⟩ := rfl
  rw [hneg] at hcomm
  split_ifs with h1 h2
  · have hae : a ≠ e := fun h => hex ⟨h1.symm, h.symm⟩
    rw [prod_wordX hae hmul]
    rw [ite_eq_left h1] at hcomm
    rw [hcomm, mul_inv_cancel]
  · have hdb : d ≠ b := fun h => h1 h.symm
    rw [prod_wordX hdb hmul]
    rw [ite_eq_right h1, ite_eq_left h2] at hcomm
    rw [hcomm, mul_inv_cancel]
  · rw [ite_eq_right h1, ite_eq_right h2] at hcomm
    rw [List.map_nil, List.prod_nil, inv_one, mul_one]
    exact hcomm

theorem prod_commWord {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ}
    (ht : t ∈ commRels) : ((commWord t).map gen3).prod = 1 := by
  have h := commValid_eq_true
  simp only [commValid, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff, beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h t ht
  rw [commWord]
  refine prod_relWord ?_ ?_ ?_ h8 h9
  · intro e; apply h5
    have := congrArg Fin.val e
    simpa [Fin.ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] using this
  · intro e; apply h6
    have := congrArg Fin.val e
    simpa [Fin.ofNat, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] using this
  · rintro ⟨e1, e2⟩
    have e1' := congrArg Fin.val e1
    have e2' := congrArg Fin.val e2
    simp only [Fin.ofNat, Fin.val_mk, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
      Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4] at e1' e2'
    rcases h7 with h7 | h7 <;> exact h7 (by assumption)

theorem prod_gen3_eq_one {w : List (Fin 12)} (hw : w ∈ h1Rels3) :
    (w.map gen3).prod = 1 := by
  rw [h1Rels3, List.mem_append, List.mem_map, List.mem_map] at hw
  rcases hw with ⟨s, -, rfl⟩ | ⟨t, ht, rfl⟩
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact gen3_mul_self s
  · exact prod_commWord ht

@[expose] def urMat9 (C : Fin 12 → Mat9) : List (Fin 12) → Mat9 × Mat9
  | [] => (1, 0)
  | s :: w => (genA s * (urMat9 C w).1, genA s * (urMat9 C w).2 + C s * (urMat9 C w).1)

theorem toMat_id9 : toMat 9 9 id9 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_zero9 : toMat 9 9 zero9 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_urPair9 (C : Fin 12 → Array ℕ) (w : List (Fin 12)) :
    toMat 9 9 (urPair9 C w).1 = (urMat9 (fun s => toMat 9 9 (C s)) w).1 ∧
      toMat 9 9 (urPair9 C w).2 = (urMat9 (fun s => toMat 9 9 (C s)) w).2 := by
  induction w with
  | nil => exact ⟨toMat_id9, toMat_zero9⟩
  | cons s w ih =>
    simp only [urPair9, urMat9, toMat_bmul, toMat_bxor, ih.1, ih.2, genA, and_self]

theorem urMat9_fst (C C' : Fin 12 → Mat9) (w : List (Fin 12)) :
    (urMat9 C w).1 = (urMat9 C' w).1 := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [urMat9, ih]

theorem urMat9_add (C C' : Fin 12 → Mat9) (w : List (Fin 12)) :
    (urMat9 (C + C') w).2 = (urMat9 C w).2 + (urMat9 C' w).2 := by
  induction w with
  | nil => simp [urMat9]
  | cons s w ih =>
    simp only [urMat9, ih, Pi.add_apply, urMat9_fst (C + C') C w, urMat9_fst C' C w]
    noncomm_ring

theorem urMat9_smul (c : ZMod 2) (C : Fin 12 → Mat9) (w : List (Fin 12)) :
    (urMat9 (c • C) w).2 = c • (urMat9 C w).2 := by
  induction w with
  | nil => simp [urMat9]
  | cons s w ih =>
    simp only [urMat9, ih, Pi.smul_apply, urMat9_fst (c • C) C w, smul_add, mul_smul_comm,
      smul_mul_assoc]

@[expose] def urLin9 : (Fin 12 → Mat9) →ₗ[ZMod 2] (Fin 44 → Mat9) where
  toFun C k := (urMat9 C (h1Rels3.getD k [])).2
  map_add' C C' := by ext k : 1; exact urMat9_add C C' _
  map_smul' c C := by ext k : 1; exact urMat9_smul c C _

@[expose] def h1F9 : (Fin (12 * (9 * 9)) → ZMod 2) →ₗ[ZMod 2] (Fin (44 * (9 * 9)) → ZMod 2) :=
  (blocksEquivN 9 44).symm.toLinearMap ∘ₗ urLin9 ∘ₗ (blocksEquivN 9 12).toLinearMap

@[expose] def cobLin9 : Mat9 →ₗ[ZMod 2] (Fin 12 → Mat9) where
  toFun X s := genA s * X + X * genA s
  map_add' X X' := by ext s : 1; simp only [Pi.add_apply]; noncomm_ring
  map_smul' c X := by ext s : 1; simp [smul_add]

@[expose] def cobF9 : (Fin (1 * (9 * 9)) → ZMod 2) →ₗ[ZMod 2] (Fin (12 * (9 * 9)) → ZMod 2) :=
  (blocksEquivN 9 12).symm.toLinearMap ∘ₗ cobLin9 ∘ₗ
    (LinearMap.proj 0 ∘ₗ (blocksEquivN 9 1).toLinearMap)

theorem toVec_h1Fb9 (v : ℕ) : toVec (44 * (9 * 9)) (h1Fb9 v) = h1F9 (toVec (12 * (9 * 9)) v) := by
  rw [h1Fb9, toVec_packN]
  simp only [h1F9, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply]
  congr 1
  ext k : 1
  rw [(toMat_urPair9 _ _).2]
  simp only [urLin9, LinearMap.coe_mk, AddHom.coe_mk]
  congr 2
  ext s : 1
  exact toMat_unpackN 9 12 v s

theorem toVec_cobFb9 (v : ℕ) : toVec (12 * (9 * 9)) (cobFb9 v) = cobF9 (toVec (1 * (9 * 9)) v) := by
  rw [cobFb9, toVec_packN]
  simp only [cobF9, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply, LinearMap.proj_apply]
  congr 1
  ext s : 1
  simp only [toMat_bxor, toMat_bmul, cobLin9, LinearMap.coe_mk, AddHom.coe_mk, genA,
    Fin.ofNat_val_eq_self]
  rw [← toMat_unpackN 9 1 v 0]
  rfl

theorem exists_coboundary9 (C : Fin 12 → Mat9)
    (hC : ∀ w ∈ h1Rels3, (urMat9 C w).2 = 0) :
    ∃ X : Mat9, ∀ s, C s = genA s * X + X * genA s := by
  have hF : h1F9 (vecOfN 9 12 C) = 0 := by
    simp only [h1F9, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
      blocksOfN_vecOfN, blocksEquivN_symm_apply]
    have : urLin9 C = 0 := by
      ext k : 1
      simp only [urLin9, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      by_cases hk : (k : ℕ) < h1Rels3.length
      · rw [List.getD_eq_getElem _ _ hk]
        exact hC _ (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (not_lt.mp hk)]
        rfl
    rw [this]
    ext i
    simp [vecOfN]
  have hR : toMat (44 * (9 * 9)) (12 * (9 * 9)) (linBits (12 * (9 * 9)) (44 * (9 * 9)) h1Fb9) *ᵥ
      vecOfN 9 12 C = 0 := by
    rw [toMat_linBits_mulVec h1Fb9 h1F9 (fun j => by rw [toVec_h1Fb9, toVec_two_pow]), hF]
  obtain ⟨e, he⟩ := exists_eq_mulVec_of_certCheckWith h1Check9W_eq_true hR
  have hB : (toMat 81 (12 * (9 * 9)) (Array.ofFn (n := 81) fun j => cobFb9 (2 ^ (j : ℕ))))ᵀ *ᵥ e =
      cobF9 e := by
    rw [← toMat_btr]
    exact toMat_linBits_mulVec cobFb9 cobF9 (fun j => by rw [toVec_cobFb9, toVec_two_pow]) e
  rw [hB] at he
  refine ⟨blocksOfN 9 1 e 0, fun s => ?_⟩
  have := congrArg (fun y => blocksOfN 9 12 y s) he
  simp only [cobF9, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
    blocksEquivN_symm_apply, LinearMap.proj_apply, blocksOfN_vecOfN] at this
  exact this

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
