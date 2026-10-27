module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharBase
public import CFSG.Fischer.Classification.Symplectic.OrthoGenSymplectic
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedSymplectic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBStated
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.AGLEmbedding.OffCharSp

open Matrix CFSG.Fischer.Classification CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (GLBCore IsElemAbelian fischerMatrixGroup fischerTransvections)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem add_self_vec {ι : Type} (z : ι → ZMod 2) : z + z = 0 := by
  funext i
  exact add_self_zmod2 (z i)

section Isometry

variable {ι : Type} [Fintype ι] [DecidableEq ι] {b : LinearMap.BilinForm (ZMod 2) (ι → ZMod 2)}

omit [Fintype ι] [DecidableEq ι] in
theorem b_symm (halt : ∀ x, b x x = 0) (x y : ι → ZMod 2) : b x y = b y x := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  revert h
  generalize b x y = c
  generalize b y x = d
  revert c d
  decide

variable (b) in
noncomputable abbrev SpH : Subgroup (GL ι (ZMod 2)) :=
  fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y

noncomputable def act (g : SpH b) (x : ι → ZMod 2) : ι → ZMod 2 :=
  ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x

theorem act_mul (g h : SpH b) (x : ι → ZMod 2) : act (g * h) x = act g (act h x) := by
  simp only [act, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_one (x : ι → ZMod 2) : act (1 : SpH b) x = x := by
  simp only [act, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]

theorem act_add (g : SpH b) (x y : ι → ZMod 2) : act g (x + y) = act g x + act g y :=
  Matrix.mulVec_add _ _ _

theorem act_smul (g : SpH b) (c : ZMod 2) (x : ι → ZMod 2) : act g (c • x) = c • act g x :=
  Matrix.mulVec_smul _ _ _

theorem act_act_inv (g : SpH b) (x : ι → ZMod 2) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_ext {g h : SpH b} (e : ∀ x, act g x = act h x) : g = h :=
  Subtype.ext (Units.ext (Matrix.ext_of_mulVec_single fun _ => e _))

theorem b_act_act (g : SpH b) (x y : ι → ZMod 2) : b (act g x) (act g y) = b x y :=
  (mem_fischerMatrixGroup_bilin_iff b g).1 g.2 x y

variable (halt : ∀ x, b x x = 0)

include halt in
noncomputable def tr (w : ι → ZMod 2) : SpH b :=
  ⟨sympTransvectionGL b halt w, sympTransvectionGL_mem_fischerMatrixGroup w⟩

theorem act_tr (w x : ι → ZMod 2) : act (tr halt w) x = x + b x w • w :=
  sympTransvectionGL_mulVec w x

theorem tr_mul_self (w : ι → ZMod 2) : tr halt w * tr halt w = 1 := by
  refine act_ext fun x => ?_
  rw [act_mul, act_tr, act_tr, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    halt w, smul_eq_mul, mul_zero, add_zero, act_one, add_assoc, ← two_smul (ZMod 2) (b x w • w)]
  rw [two_smul, add_self_vec, add_zero]

theorem tr_inv (w : ι → ZMod 2) : (tr halt w)⁻¹ = tr halt w :=
  inv_eq_of_mul_eq_one_right (tr_mul_self halt w)

theorem conj_tr (g : SpH b) (w : ι → ZMod 2) : g * tr halt w * g⁻¹ = tr halt (act g w) := by
  refine act_ext fun x => ?_
  have h1 : b (act g⁻¹ x) w = b x (act g w) := by
    have := b_act_act g (act g⁻¹ x) w
    rw [act_act_inv] at this
    exact this.symm
  rw [act_mul, act_mul, act_tr, act_tr, act_add, act_smul, act_act_inv, h1]

theorem tr_comm {u w : ι → ZMod 2} (h : b u w = 0) :
    tr halt u * tr halt w = tr halt w * tr halt u := by
  have h' : b w u = 0 := by rw [b_symm halt, h]
  refine act_ext fun x => ?_
  rw [act_mul, act_mul, act_tr, act_tr, act_tr, act_tr, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, h', smul_eq_mul, mul_zero, add_zero, map_add, LinearMap.add_apply,
    map_smul, LinearMap.smul_apply, h, smul_eq_mul, mul_zero, add_zero, add_assoc, add_assoc,
    add_comm (b x w • w)]

theorem tr_braid {e f : ι → ZMod 2} (h : b e f = 1) :
    tr halt e * tr halt f * tr halt e = tr halt f * tr halt e * tr halt f := by
  have h' : b f e = 1 := by rw [b_symm halt, h]
  have h1 := conj_tr halt (tr halt e) f
  have h2 := conj_tr halt (tr halt f) e
  rw [tr_inv] at h1 h2
  rw [h1, h2, act_tr, act_tr, h', h, one_smul, one_smul, add_comm]

theorem tr_mul_tr_pow_three {e f : ι → ZMod 2} (h : b e f = 1) :
    (tr halt e * tr halt f) ^ 3 = 1 := by
  have hb := tr_braid halt h
  have hxx : tr halt e * tr halt e = 1 := tr_mul_self halt e
  have hyy : tr halt f * tr halt f = 1 := tr_mul_self halt f
  have h3 : (tr halt e * tr halt f) ^ 3 =
      (tr halt e * tr halt f * tr halt e) * (tr halt f * tr halt e * tr halt f) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h3, ← hb]
  calc tr halt e * tr halt f * tr halt e * (tr halt e * tr halt f * tr halt e)
      = tr halt e * tr halt f * (tr halt e * tr halt e) * tr halt f * tr halt e := by
        simp only [mul_assoc]
    _ = tr halt e * (tr halt f * tr halt f) * tr halt e := by
        rw [hxx, mul_one]
        simp only [mul_assoc]
    _ = 1 := by rw [hyy, mul_one, hxx]

end Isometry

section Paired

variable (n : ℕ)

theorem neg_zmod2 (a : ZMod 2) : -a = a := by
  revert a
  decide

theorem pairedSympForm_alt (x : Fin n ⊕ Fin n → ZMod 2) : pairedSympForm (ZMod 2) n x x = 0 :=
  pairedSympForm_self x

def eI (i : Fin n) : Fin n ⊕ Fin n → ZMod 2 := Pi.single (Sum.inl i) 1

def fI (i : Fin n) : Fin n ⊕ Fin n → ZMod 2 := Pi.single (Sum.inr i) 1

theorem b_eI (x : Fin n ⊕ Fin n → ZMod 2) (i : Fin n) :
    pairedSympForm (ZMod 2) n x (eI n i) = x (Sum.inr i) := by
  rw [pairedSympForm_apply, ← neg_zmod2 (x (Sum.inr i))]
  simp [eI, dotProduct, Pi.single_apply]

theorem b_fI (x : Fin n ⊕ Fin n → ZMod 2) (i : Fin n) :
    pairedSympForm (ZMod 2) n x (fI n i) = x (Sum.inl i) := by
  rw [pairedSympForm_apply]
  simp [fI, dotProduct, Pi.single_apply]

theorem b_eI_eI (i j : Fin n) : pairedSympForm (ZMod 2) n (eI n i) (eI n j) = 0 := by
  rw [b_eI]
  simp [eI]

theorem b_fI_fI (i j : Fin n) : pairedSympForm (ZMod 2) n (fI n i) (fI n j) = 0 := by
  rw [b_fI]
  simp [fI]

theorem b_eI_fI (i j : Fin n) :
    pairedSympForm (ZMod 2) n (eI n i) (fI n j) = if i = j then 1 else 0 := by
  rw [b_fI]
  by_cases h : i = j
  · subst h
    simp [eI]
  · simp [eI, h, Ne.symm h]

theorem b_fI_eI (i j : Fin n) :
    pairedSympForm (ZMod 2) n (fI n i) (eI n j) = if i = j then 1 else 0 := by
  rw [b_eI]
  by_cases h : i = j
  · subst h
    simp [fI]
  · simp [fI, h, Ne.symm h]

theorem pairedSympForm_nondeg (x : Fin n ⊕ Fin n → ZMod 2)
    (h : ∀ y, pairedSympForm (ZMod 2) n x y = 0) : x = 0 := by
  funext c
  rcases c with i | i
  · rw [← b_fI n x i]
    exact h _
  · rw [← b_eI n x i]
    exact h _

theorem closure_range_tr :
    Subgroup.closure (Set.range (tr (b := pairedSympForm (ZMod 2) n) (pairedSympForm_alt n))) =
      ⊤ := by
  have halt := pairedSympForm_alt n
  have hnd := pairedSympForm_nondeg n
  have hclos : SpH (pairedSympForm (ZMod 2) n) = Subgroup.closure
      (fischerTransvections (fun x y => pairedSympForm (ZMod 2) n x y) fun v => v ≠ 0) :=
    fischerMatrixGroup_bilin_eq_closure (pairedSympForm (ZMod 2) n) halt hnd
  set H : Subgroup (SpH (pairedSympForm (ZMod 2) n)) := Subgroup.closure (Set.range (tr halt))
    with hH
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hx' : x ∈ H.map (SpH (pairedSympForm (ZMod 2) n)).subtype := by
    have hx2 := hx
    rw [hclos] at hx2
    refine (Subgroup.closure_le _).2 ?_ hx2
    intro t ht
    obtain ⟨v, -, rfl⟩ := eq_sympTransvectionGL_of_mem_fischerTransvections halt ht
    exact ⟨tr halt v, Subgroup.subset_closure ⟨v, rfl⟩, rfl⟩
  obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp hx'
  have : h = ⟨x, hx⟩ := Subtype.ext hgh
  exact this ▸ hh

end Paired

section Elem

variable (n : ℕ)

noncomputable def zEl (i : Fin n) : SpH (pairedSympForm (ZMod 2) n) :=
  tr (pairedSympForm_alt n) (eI n i) * tr (pairedSympForm_alt n) (fI n i)

theorem b_eI_fI_self (i : Fin n) : pairedSympForm (ZMod 2) n (eI n i) (fI n i) = 1 := by
  rw [b_eI_fI]
  simp

theorem zEl_pow_three (i : Fin n) : zEl n i ^ 3 = 1 :=
  tr_mul_tr_pow_three (pairedSympForm_alt n) (b_eI_fI_self n i)

theorem zEl_ne_one (i : Fin n) : zEl n i ≠ 1 := by
  intro h
  have halt := pairedSympForm_alt n
  have h1 : tr halt (eI n i) = tr halt (fI n i) := by
    rw [zEl, mul_eq_one_iff_eq_inv, tr_inv] at h
    exact h
  have h2 := congrArg (fun g => act g (fI n i)) h1
  simp only [act_tr] at h2
  have h3 : pairedSympForm (ZMod 2) n (fI n i) (eI n i) = 1 := by
    rw [b_symm halt, b_eI_fI_self]
  rw [h3, halt, one_smul, zero_smul, add_zero, add_eq_left] at h2
  have := congrFun h2 (Sum.inl i)
  simp [eI] at this

theorem zEl_comm (i j : Fin n) : zEl n i * zEl n j = zEl n j * zEl n i := by
  by_cases h : i = j
  · rw [h]
  have halt := pairedSympForm_alt n
  have hac : Commute (tr halt (eI n i)) (tr halt (eI n j)) :=
    tr_comm halt (b_eI_eI n i j)
  have had : Commute (tr halt (eI n i)) (tr halt (fI n j)) :=
    tr_comm halt (by rw [b_eI_fI]; simp [h])
  have hbc : Commute (tr halt (fI n i)) (tr halt (eI n j)) :=
    tr_comm halt (by rw [b_fI_eI]; simp [h])
  have hbd : Commute (tr halt (fI n i)) (tr halt (fI n j)) :=
    tr_comm halt (b_fI_fI n i j)
  exact Commute.mul_left (Commute.mul_right hac had) (Commute.mul_right hbc hbd)

noncomputable def EEl : Subgroup (SpH (pairedSympForm (ZMod 2) n)) :=
  Subgroup.closure (Set.range (zEl n))

theorem EEl_elem : IsElemAbelian 3 (EEl n) :=
  isElemAbelian_closure
    (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact zEl_comm n i j)
    (by
      rintro _ ⟨i, rfl⟩
      exact zEl_pow_three n i)

theorem exists_partner (hn : 3 ≤ n) (v : Fin n ⊕ Fin n → ZMod 2)
    (hv : ∀ i, ¬ (v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0)) :
    ∃ u : Fin n ⊕ Fin n → ZMod 2, (∃ i, u (Sum.inl i) = 0 ∧ u (Sum.inr i) = 0) ∧
      (∃ i, (v + u) (Sum.inl i) = 0 ∧ (v + u) (Sum.inr i) = 0) ∧
        pairedSympForm (ZMod 2) n v u = 1 := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  refine ⟨v (Sum.inl i0) • eI n i0 + v (Sum.inr i0) • fI n i0 + (1 + v (Sum.inl i1)) • eI n i1 +
    v (Sum.inl i1) • fI n i1, ⟨i2, ?_, ?_⟩, ⟨i0, ?_, ?_⟩, ?_⟩
  · simp [eI, fI, h02.symm, h12.symm]
  · simp [eI, fI, h02.symm, h12.symm]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp [eI, fI, h01]
    exact add_self_zmod2 _
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp [eI, fI, h01]
    exact add_self_zmod2 _
  · simp only [map_add, map_smul, b_eI, b_fI, smul_eq_mul]
    have key : ∀ a0 c0 a1 c1 : ZMod 2, ¬ (a1 = 0 ∧ c1 = 0) →
        a0 * c0 + c0 * a0 + (1 + a1) * c1 + a1 * a1 = 1 := by
      decide
    exact key _ _ _ _ (hv i1)

theorem glbCore_EEl (hn : 3 ≤ n) : GLBCore 3 1 (EEl n) = ⊤ := by
  have halt := pairedSympForm_alt n
  refine glbCore_eq_top_of_conj_family Nat.prime_three (tr halt) (fun a b => act (tr halt a) b)
    (fun a b => conj_tr halt (tr halt a) b) (closure_range_tr n) (EEl_elem n)
    {v | ∃ i, v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0} ?_ ?_
  · rintro v ⟨i, hi1, hi2⟩
    refine ⟨zEl n i, Subgroup.subset_closure ⟨i, rfl⟩, zEl_ne_one n i, ?_⟩
    have h1 : Commute (tr halt v) (tr halt (eI n i)) := tr_comm halt (by rw [b_eI]; exact hi2)
    have h2 : Commute (tr halt v) (tr halt (fI n i)) := tr_comm halt (by rw [b_fI]; exact hi1)
    exact Commute.mul_right h1 h2
  · intro v
    by_cases hv : ∃ i, v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0
    · exact Derivable.base hv
    · have hv' : ∀ i, ¬ (v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0) := fun i h => hv ⟨i, h⟩
      obtain ⟨u, hu, hvu, hb⟩ := exists_partner n hn v hv'
      have hτ : act (tr halt u) (v + u) = v := by
        rw [act_tr, map_add, LinearMap.add_apply, hb, halt u, add_zero, one_smul, add_assoc,
          add_self_vec, add_zero]
      have h : Derivable (fun a b => act (tr halt a) b)
          {v : Fin n ⊕ Fin n → ZMod 2 | ∃ i, v (Sum.inl i) = 0 ∧ v (Sum.inr i) = 0}
          (act (tr halt u) (v + u)) := Derivable.step (Derivable.base hu) (Derivable.base hvu)
      rwa [hτ] at h

end Elem

section Stated

open CFSG.Assembly.LowTwoRank

variable (n : ℕ)

theorem statedSp_eq_spH :
    StatedSp n (ZMod 2) = SpH (pairedSympForm (ZMod 2) n) := by
  ext A
  rw [CFSG.ComponentClassification.CatalogueBSymplecticB.mem_statedSp_iff_isometry,
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff,
    mem_fischerMatrixGroup_bilin_iff]
  rfl

theorem statedScalars_zmod2 (ι : Type) [Fintype ι] [DecidableEq ι] :
    StatedScalars ι (ZMod 2) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι

noncomputable def statedProjEquivSp :
    StatedProj (StatedSp n (ZMod 2)) ≃* StatedSp n (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq
    (by rw [statedScalars_zmod2, Subgroup.bot_subgroupOf])).trans QuotientGroup.quotientBot

theorem nonempty_mulEquiv_spH {G : Type} [Group G] (h : StatedClassicalModel G .PSp n 2 1) :
    Nonempty (G ≃* SpH (pairedSympForm (ZMod 2) n)) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
    norm_num
  let φ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  let e₁ : StatedProj (StatedSp n F) ≃* StatedProj (StatedSp n (ZMod 2)) :=
    CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ n)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨((e.trans e₁).trans (statedProjEquivSp n)).trans
    (MulEquiv.subgroupCongr (statedSp_eq_spH n))⟩

theorem glbCore_eq_top_of_stated_sp {K : Type} [Group K] [Finite K] (hn : 3 ≤ n)
    (h : StatedClassicalModel K .PSp n 2 1) (T : Sylow 3 K) :
    GLBCore 3 1 (T : Subgroup K) = ⊤ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_spH n h
  exact glbCore_eq_top_of_mulEquiv Nat.prime_three e (isPGroup_of_isElemAbelian (EEl_elem n))
    (glbCore_EEl n hn) T

end Stated

end CFSG.AGLEmbedding.OffCharSp
