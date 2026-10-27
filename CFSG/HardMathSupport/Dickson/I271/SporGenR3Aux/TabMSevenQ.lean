module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMSevenNoComp
public import Certificates.Certificate17487
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMSeven

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

private theorem evalWord_append' (w₁ w₂ : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (w₁ ++ w₂) v = Native.evalWord w₂ (Native.evalWord w₁ v) := by
  simp only [Native.evalWord, Native.evalWordC, List.foldl_append]

private theorem evalWord_nil' (v : Native.DVec) : Native.evalWord [] v = v := rfl

private theorem evalWord_powL_succ (k : ℕ) (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL (k + 1) w) v = Native.evalWord (powL k w) (Native.evalWord w v) := by
  simp only [powL, List.replicate_succ, List.flatten_cons, evalWord_append']

private theorem evalWord_powL_zero (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL 0 w) v = v := rfl

private theorem evalWord_powL_two (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL 2 w) v = Native.evalWord w (Native.evalWord w v) := by
  simp only [evalWord_powL_succ, evalWord_powL_zero]

private theorem evalWord_powL_four (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL 4 w) v =
      Native.evalWord w (Native.evalWord w (Native.evalWord w (Native.evalWord w v))) := by
  simp only [evalWord_powL_succ, evalWord_powL_zero]

private theorem evalWord_powL_five (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL 5 w) v = Native.evalWord w (Native.evalWord w (Native.evalWord w
      (Native.evalWord w (Native.evalWord w v)))) := by
  simp only [evalWord_powL_succ, evalWord_powL_zero]

private theorem evalWord_powL_seven (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWord (powL 7 w) v = Native.evalWord w (Native.evalWord w (Native.evalWord w
      (Native.evalWord w (Native.evalWord w (Native.evalWord w (Native.evalWord w v)))))) := by
  simp only [evalWord_powL_succ, evalWord_powL_zero]

theorem qAt_rels {v : Native.DVec} (h : qAt v = true) :
    [qZ, qF, qA, qX, qT].all (fun w => w.all fun g => g.validB) = true ∧
    (Native.evalWord (powL 7 qZ) v).eqv (Native.evalWord [] v) = true ∧
    (Native.evalWord (powL 5 qF) v).eqv (Native.evalWord [] v) = true ∧
    (Native.evalWord (qT ++ qT) v).eqv (Native.evalWord [] v) = true ∧
    (Native.evalWord (qZ ++ qF) v).eqv (Native.evalWord (qF ++ qZ) v) = true ∧
    (Native.evalWord (qZ ++ qT) v).eqv (Native.evalWord (qT ++ qZ) v) = true ∧
    (Native.evalWord (qF ++ qT) v).eqv (Native.evalWord (qT ++ qF) v) = true ∧
    (Native.evalWord (qZ ++ qA) v).eqv (Native.evalWord (qA ++ qZ) v) = true ∧
    (Native.evalWord (qZ ++ qX) v).eqv (Native.evalWord (qX ++ qZ) v) = true ∧
    (Native.evalWord (powL 4 qA) v).eqv (Native.evalWord qT v) = true ∧
    (Native.evalWord (powL 2 qX) v).eqv (Native.evalWord qT v) = true ∧
    (Native.evalWord (qA ++ qX ++ qA) v).eqv (Native.evalWord qX v) = true := by
  simp only [qAt, qChecksAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  simp only [evalWord_append', evalWord_nil', evalWord_powL_two, evalWord_powL_four,
    evalWord_powL_five, evalWord_powL_seven]
  exact ⟨hv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

@[expose] noncomputable def qZG : Gmat := gw qZ

@[expose] noncomputable def qFG : Gmat := gw qF

@[expose] noncomputable def qAG : Gmat := gw qA

@[expose] noncomputable def qXG : Gmat := gw qX

theorem gw_qT : gw qT = tG := rfl

private theorem gw_powL' (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (wordLin_powL k w)

private theorem all_powL {w : List Native.Gen} (h : (w.all fun g => g.validB) = true) (k : ℕ) :
    ((powL k w).all fun g => g.validB) = true := by
  rw [List.all_eq_true] at h ⊢
  intro g hg
  rw [powL, List.mem_flatten] at hg
  obtain ⟨l, hl, hgl⟩ := hg
  rw [List.eq_of_mem_replicate hl] at hgl
  exact h g hgl


private theorem valid_of_mem {w : List Native.Gen} (hw : w ∈ [qZ, qF, qA, qX, qT]) :
    (w.all fun g => g.validB) = true :=
  List.all_eq_true.1 (qAt_rels (Certificates.certificate17487).1).1 w hw

private theorem gw_eq_of_rel {w₁ w₂ : List Native.Gen} (hv₁ : (w₁.all fun g => g.validB) = true)
    (hv₂ : (w₂.all fun g => g.validB) = true)
    (h : ∀ v : Native.DVec, qAt v = true →
      (Native.evalWord w₁ v).eqv (Native.evalWord w₂ v) = true) :
    gw w₁ = gw w₂ := by
  obtain ⟨ha, hb, hw, -⟩ := (Certificates.certificate17487)
  apply agree_sound
  simp only [agree, hv₁, hv₂, h _ ha, h _ hb, h _ hw, Bool.and_self]

private theorem vZ : (qZ.all fun g => g.validB) = true := valid_of_mem (by simp)
private theorem vF : (qF.all fun g => g.validB) = true := valid_of_mem (by simp)
private theorem vA : (qA.all fun g => g.validB) = true := valid_of_mem (by simp)
private theorem vX : (qX.all fun g => g.validB) = true := valid_of_mem (by simp)
private theorem vT : (qT.all fun g => g.validB) = true := valid_of_mem (by simp)

private theorem vApp {w₁ w₂ : List Native.Gen} (h₁ : (w₁.all fun g => g.validB) = true)
    (h₂ : (w₂.all fun g => g.validB) = true) : ((w₁ ++ w₂).all fun g => g.validB) = true := by
  simp only [List.all_append, h₁, h₂, Bool.and_self]

theorem qZG_pow_seven : qZG ^ 7 = 1 := by
  have e := gw_eq_of_rel (w₂ := []) (all_powL vZ 7) rfl fun v hv => (qAt_rels hv).2.1
  rwa [gw_powL', gw_nil] at e

theorem qFG_pow_five : qFG ^ 5 = 1 := by
  have e := gw_eq_of_rel (w₂ := []) (all_powL vF 5) rfl fun v hv => (qAt_rels hv).2.2.1
  rwa [gw_powL', gw_nil] at e

theorem tG_mul_tG : tG * tG = 1 := by
  have e := gw_eq_of_rel (w₂ := []) (vApp vT vT) rfl fun v hv => (qAt_rels hv).2.2.2.1
  rwa [gw_append, gw_nil, gw_qT] at e

theorem qZG_comm_qFG : qZG * qFG = qFG * qZG := by
  have e := gw_eq_of_rel (vApp vZ vF) (vApp vF vZ) fun v hv => (qAt_rels hv).2.2.2.2.1
  rw [gw_append, gw_append] at e
  exact e.symm

theorem qZG_comm_tG : qZG * tG = tG * qZG := by
  have e := gw_eq_of_rel (vApp vZ vT) (vApp vT vZ) fun v hv => (qAt_rels hv).2.2.2.2.2.1
  rw [gw_append, gw_append, gw_qT] at e
  exact e.symm

theorem qFG_comm_tG : qFG * tG = tG * qFG := by
  have e := gw_eq_of_rel (vApp vF vT) (vApp vT vF) fun v hv => (qAt_rels hv).2.2.2.2.2.2.1
  rw [gw_append, gw_append, gw_qT] at e
  exact e.symm

theorem qAG_mem_cent : qAG ∈ Subgroup.centralizer ({qZG} : Set Gmat) := by
  have e := gw_eq_of_rel (vApp vZ vA) (vApp vA vZ) fun v hv => (qAt_rels hv).2.2.2.2.2.2.2.1
  rw [gw_append, gw_append] at e
  exact Subgroup.mem_centralizer_singleton_iff.2 e

theorem qXG_mem_cent : qXG ∈ Subgroup.centralizer ({qZG} : Set Gmat) := by
  have e := gw_eq_of_rel (vApp vZ vX) (vApp vX vZ) fun v hv =>
    (qAt_rels hv).2.2.2.2.2.2.2.2.1
  rw [gw_append, gw_append] at e
  exact Subgroup.mem_centralizer_singleton_iff.2 e

theorem qAG_pow_four : qAG ^ 4 = tG := by
  have e := gw_eq_of_rel (all_powL vA 4) vT fun v hv => (qAt_rels hv).2.2.2.2.2.2.2.2.2.1
  rwa [gw_powL', gw_qT] at e

theorem qXG_sq : qXG ^ 2 = tG := by
  have e := gw_eq_of_rel (all_powL vX 2) vT fun v hv =>
    (qAt_rels hv).2.2.2.2.2.2.2.2.2.2.1
  rwa [gw_powL', gw_qT] at e

theorem qAG_mul_qXG_mul_qAG : qAG * (qXG * qAG) = qXG := by
  have e := gw_eq_of_rel (vApp (vApp vA vX) vA) vX fun v hv =>
    (qAt_rels hv).2.2.2.2.2.2.2.2.2.2.2
  rwa [gw_append, gw_append] at e

theorem qXG_conj_qAG : qXG * qAG * qXG⁻¹ = qAG⁻¹ := by
  have h : qXG * qAG = qAG⁻¹ * qXG := by
    calc qXG * qAG = qAG⁻¹ * (qAG * (qXG * qAG)) := by group
      _ = qAG⁻¹ * qXG := by rw [qAG_mul_qXG_mul_qAG]
  rw [h, mul_inv_cancel_right]

theorem tG_ne_one : tG ≠ 1 :=
  gw_qT ▸ gw_ne_one_of_moveCheck (Certificates.certificate17487).2.2.2.2.2

theorem orderOf_qZG : orderOf qZG = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime qZG_pow_seven
    (gw_ne_one_of_moveCheck (Certificates.certificate17487).2.2.2.1)

theorem orderOf_qFG : orderOf qFG = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime qFG_pow_five
    (gw_ne_one_of_moveCheck (Certificates.certificate17487).2.2.2.2.1)

theorem orderOf_qAG : orderOf qAG = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := qAG)
    (by rw [show 2 ^ 2 = 4 by norm_num, qAG_pow_four]; exact tG_ne_one)
    (by rw [show 2 ^ (2 + 1) = 4 * 2 by norm_num, pow_mul, qAG_pow_four, sq, tG_mul_tG])
  simpa using h

theorem exists_quat_le_cent_qZG : ∃ S : Subgroup Gmat,
    S ≤ Subgroup.centralizer ({qZG} : Set Gmat) ∧ Nonempty (↥S ≃* QuaternionGroup 4) := by
  set C := Subgroup.centralizer ({qZG} : Set Gmat)
  have h8 : orderOf (⟨qAG, qAG_mem_cent⟩ : C) = 8 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_qAG
  have hsq : (⟨qXG, qXG_mem_cent⟩ : C) ^ 2 = (⟨qAG, qAG_mem_cent⟩ : C) ^ 4 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, SubgroupClass.coe_pow]
    exact qXG_sq.trans qAG_pow_four.symm
  have hconj : (⟨qXG, qXG_mem_cent⟩ : C) * ⟨qAG, qAG_mem_cent⟩ * (⟨qXG, qXG_mem_cent⟩ : C)⁻¹ =
      (⟨qAG, qAG_mem_cent⟩ : C)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    exact qXG_conj_qAG
  obtain ⟨S', ⟨e⟩, -, -, -⟩ := tabMSeven_exists_quat h8 hsq hconj
  exact ⟨S'.map C.subtype, Subgroup.map_subtype_le S',
    ⟨(S'.equivMapOfInjective C.subtype C.subtype_injective).symm.trans e⟩⟩

theorem tabMSeven_sevenB_data : ∃ z f : Gmat, orderOf z = 7 ∧ orderOf f = 5 ∧
    z * f = f * z ∧
    z * CFSG.AGLEmbedding.Norton.MON5_7.tG = CFSG.AGLEmbedding.Norton.MON5_7.tG * z ∧
    f * CFSG.AGLEmbedding.Norton.MON5_7.tG = CFSG.AGLEmbedding.Norton.MON5_7.tG * f ∧
    ∃ S : Subgroup Gmat, S ≤ Subgroup.centralizer ({z} : Set Gmat) ∧
      Nonempty (↥S ≃* QuaternionGroup 4) :=
  ⟨qZG, qFG, orderOf_qZG, orderOf_qFG, qZG_comm_qFG, qZG_comm_tG, qFG_comm_tG,
    exists_quat_le_cent_qZG⟩

end CFSG.HardMathSupport.Dickson.I271.TabMSeven
