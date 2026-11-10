
module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane
public import Certificates.Data.TwE6Letters
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6TwoBase

@[expose] public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LieType.Chevalley.RootOps
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.Ree CFSG.LieType.SeitzGeneration.ExcHighThree.F4Two
  CFSG.LieType.SeitzGeneration.ExcHighThree.E6Two CFSG.LieType.SeitzGeneration.ExcHighThree.TwBits
  CFSG.LieType.SeitzGeneration.ExcHighThree.TwClose

section Field

variable {K : Type} [Field K] [Finite K]

theorem exists_omega [CharP K 2] (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, hK]
    exact lt_of_le_of_lt Finset.card_le_two (by norm_num)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hc0, hc1⟩ := hc
  refine ⟨c, ?_⟩
  have h3 : c ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hK] at this
  have hm : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.1 hm).resolve_left (sub_ne_zero.2 hc1)

theorem eq_zero_one_omega [CharP K 2] (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (c : K) : c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  have h3 : c ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one c hc0
    rwa [hK] at this
  have h3ω : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hprod : (c - 1) * (c - ω) * (c - ω ^ 2) = 0 := by
    linear_combination h3 - c ^ 2 * hω + c * hω + c * h3ω - h3ω
  right
  rcases mul_eq_zero.1 hprod with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h))

end Field

section BaseChange

variable {k K : Type} [Field k] [Field K] [CharP k 2] [CharP K 2]

theorem baseChange_toEnd (f : k →+* K) (A : ℕ) :
    CFSG.LieType.Steinberg.Adjoint.BaseChange (τ := Tag.E6) f (E6Bits.toEnd k A)
      (E6Bits.toEnd K A) := by
  intro b
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective (τ := Tag.E6) b
  have hp78 : p < 78 := by rwa [E6Bits.dim_E6] at hp
  rw [← posVec_eq_single hp, ← posVec_eq_single hp]
  refine TwBits.vec_ext_posCoord fun q hq => ?_
  have hq' : q < dim Tag.E6 := by rwa [E6Bits.dim_E6]
  have hcoord : posCoord Tag.E6 K q (Finsupp.mapRange f f.map_zero
      (E6Bits.toEnd k A (posVec Tag.E6 k p))) =
      f (posCoord Tag.E6 k q (E6Bits.toEnd k A (posVec Tag.E6 k p))) := by
    simp [posCoord, hq']
  rw [hcoord, E6Bits.posCoord_toEnd_posVec _ hp78 hq, E6Bits.posCoord_toEnd_posVec _ hp78 hq]
  cases A.testBit (78 * p + q) <;> simp [TwBits.bitK_true, TwBits.bitK_false]

theorem hasBits2_baseChange (f : k →+* K) (ω : K) {g : adjointGroup Tag.E6 k} {A : ℕ}
    (h : E6Bits.HasBits k g A) :
    HasBits2 K ω (baseChangeGL f (g : ModGL Tag.E6 k)) ⟨A, 0⟩ := by
  unfold HasBits2 toEnd2
  rw [coe_baseChangeGL, toEnd_zero, smul_zero, add_zero]
  have h' : ((g : ModGL Tag.E6 k) : Module.End k (RootModule Tag.E6 k)) = E6Bits.toEnd k A := h
  rw [h']
  exact (baseChange_baseChangeEnd f (E6Bits.toEnd k A)).unique
    (baseChange_toEnd f A)

end BaseChange

section Iota

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2] [CharP K 2]
  (σ : K ≃+* K) (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)

noncomputable def iota : adjointGroup .F4 k →* twistedE6RootGroup K σ :=
  (phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom

theorem coe_iota (g : adjointGroup .F4 k) :
    ((iota σ hfix g : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (algebraMap k K) ((embE6F4 k g : adjointGroup .E6 k) : ModGL Tag.E6 k) := by
  unfold iota embE6F4 isoE6F4
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
    Subgroup.coe_subtype]
  rfl

variable {σ} in
abbrev tmat (x : twistedE6RootGroup K σ) : ModGL Tag.E6 K :=
  (x : ModGL TwistTag.E6.tag K)

theorem hasBits2_iota (ω : K) {g : adjointGroup .F4 k} {A : ℕ}
    (h : E6Bits.HasBits k (embE6F4 k g) A) :
    HasBits2 K ω (tmat (iota σ hfix g)) ⟨A, 0⟩ := by
  have h1 := hasBits2_baseChange (algebraMap k K) ω h
  rw [← coe_iota σ hfix g] at h1
  exact h1

end Iota

section Orbits

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  (σ : K ≃+* K)

noncomputable def oX (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) : twistedE6RootGroup K σ :=
  ⟨(orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K),
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (orbitX_mem_graphFixedPosUnipotent _ _ _ _)⟩

noncomputable def oY (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) : twistedE6RootGroup K σ :=
  ⟨(orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K),
    graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
      (orbitY_mem_graphFixedNegUnipotent _ _ _ _)⟩

theorem vSL_eq_conj {L : Type} [Field L] (c : L) : vSL c = WSL * uSL (-c) * WSL⁻¹ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  change !![1, 0; c, 1] = !![0, 1; -1, 0] * !![1, -c; 0, 1] * Matrix.adjugate !![0, 1; -1, 0]
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable {k : Type} [Field k] [Algebra k K]

theorem eq_top_of_orbit (S : Subgroup (twistedE6RootGroup K σ))
    (hX : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      oX σ a c ∈ S)
    (hF : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a),
      (c : K) ∈ Set.range (algebraMap k K) → oY σ a c ∈ S) : S = ⊤ := by
  set M : Subgroup (ModGL TwistTag.E6.tag K) := S.map (twistedE6RootGroup K σ).subtype with hM
  have hMx : ∀ a c, (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ M :=
    fun a c => ⟨oX σ a c, hX a c, rfl⟩
  have hN : ∀ a, (orbitN TwistTag.E6 K σ.toRingHom a 1 : ModGL TwistTag.E6.tag K) ∈ M := by
    intro a
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    refine mul_mem (mul_mem (hMx a _) ?_) (hMx a _)
    refine ⟨oY σ a _, hF a _ ⟨-1, ?_⟩, rfl⟩
    simp only [map_neg, map_one, inv_one, Units.val_one, Subfield.coe_neg, Subfield.coe_one]
  have hYM : ∀ a c, (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) ∈ M := by
    intro a c
    rw [← orbitRankOneHom_vSL a c, vSL_eq_conj, map_mul, map_mul, orbitRankOneHom_WSL,
      orbitRankOneHom_uSL, map_inv, orbitRankOneHom_WSL]
    exact mul_mem (mul_mem (hN a) (hMx a (-c))) (inv_mem (hN a))
  have hG : twistedE6RootGroup K σ ≤ M := by
    have hgen' := graphFixedRootGroup_eq_iSup_orbitRankOneGroup (t := TwistTag.E6)
      (σ := σ.toRingHom) σ.surjective
    refine (le_of_eq hgen').trans (iSup_le fun a => (Subgroup.closure_le _).2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [hMx a c, hYM a c]
  refine (Subgroup.eq_top_iff' _).2 fun x => ?_
  obtain ⟨y, hy, hyx⟩ := hG x.2
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

end Orbits

section Rational

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2] [CharP K 2]
  (σ : K ≃+* K) (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)

include hfix

theorem pow_fix (n : ℕ) (c : k) : (σ.toRingHom ^ n) (algebraMap k K c) = algebraMap k K c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, RingHom.mul_def, RingHom.comp_apply]; exact (congrArg _ (hfix c)).trans ih

theorem coe_oX_range (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a)
    (c' : k) (hc : (c : K) = algebraMap k K c') :
    ((oX σ a c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((TwistTag.E6.orbitWord a).map fun i => xUnit TwistTag.E6.tag K i (algebraMap k K c')).prod := by
  show (orbitX TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) = _
  rw [coe_orbitX, TwistTag.E6.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun n _ => ?_)
  simp only [Function.comp, hc, pow_fix σ hfix]

theorem coe_oY_range (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a)
    (c' : k) (hc : (c : K) = algebraMap k K c') :
    ((oY σ a c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((TwistTag.E6.orbitWord a).map fun i => yUnit TwistTag.E6.tag K i (algebraMap k K c')).prod := by
  show (orbitY TwistTag.E6 K σ.toRingHom a c : ModGL TwistTag.E6.tag K) = _
  rw [coe_orbitY, TwistTag.E6.orbitWord_eq_map_range, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun n _ => ?_)
  simp only [Function.comp, hc, pow_fix σ hfix]

theorem coe_iota_xE (j : Fin Tag.F4.rank) (c' : k) :
    ((iota σ hfix (xE Tag.F4 k j c') : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun i =>
        xUnit TwistTag.E6.tag K i (algebraMap k K c')).prod := by
  have hT : (e6FixedF4EquivAll k).symm (xE Tag.F4 k j c') = OX j c' := by
    rw [MulEquiv.symm_apply_eq, psi_OX]
  show ((phiG σ hfix ((e6FixedF4EquivAll k).symm (xE Tag.F4 k j c')) : twistedE6RootGroup K σ) :
    ModGL TwistTag.E6.tag K) = _
  rw [hT, coe_phiG]
  show baseChangeGL (algebraMap k K) (f4OrbitXUnit k j c') = _
  rw [f4OrbitXUnit, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  exact baseChangeGL_xUnit _ _ _

theorem coe_iota_yE (j : Fin Tag.F4.rank) (c' : k) :
    ((iota σ hfix (yE Tag.F4 k j c') : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      ((TwistTag.E6.orbitWord (f4FoldedIndex j)).map fun i =>
        yUnit TwistTag.E6.tag K i (algebraMap k K c')).prod := by
  have hT : (e6FixedF4EquivAll k).symm (yE Tag.F4 k j c') = OY j c' := by
    rw [MulEquiv.symm_apply_eq, psi_OY]
  show ((phiG σ hfix ((e6FixedF4EquivAll k).symm (yE Tag.F4 k j c')) : twistedE6RootGroup K σ) :
    ModGL TwistTag.E6.tag K) = _
  rw [hT, coe_phiG]
  show baseChangeGL (algebraMap k K) (f4OrbitYUnit k j c') = _
  rw [f4OrbitYUnit, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  exact baseChangeGL_yUnit _ _ _

theorem oXY_mem_range (a : Fin TwistTag.E6.foldedTag.rank)
    (c : orbitField TwistTag.E6 K σ.toRingHom a) (hc : (c : K) ∈ Set.range (algebraMap k K)) :
    oX σ a c ∈ (iota σ hfix).range ∧ oY σ a c ∈ (iota σ hfix).range := by
  obtain ⟨c', hc'⟩ := hc
  have ha := f4FoldedIndex_f4UnfoldIndex a
  constructor
  · refine ⟨xE Tag.F4 k (f4UnfoldIndex a) c', ?_⟩
    apply Subtype.ext
    rw [coe_oX_range σ hfix a c c' hc'.symm]
    have := coe_iota_xE σ hfix (f4UnfoldIndex a) c'
    rw [ha] at this
    exact this
  · refine ⟨yE Tag.F4 k (f4UnfoldIndex a) c', ?_⟩
    apply Subtype.ext
    rw [coe_oY_range σ hfix a c c' hc'.symm]
    have := coe_iota_yE σ hfix (f4UnfoldIndex a) c'
    rw [ha] at this
    exact this

end Rational

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  (σ : K ≃+* K)

theorem pow4_eq (hK : Nat.card K = 4) (c : K) : c ^ 4 = c := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  have := FiniteField.pow_card c
  rwa [hK] at this

theorem card_orbit_zero : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide

theorem card_orbit_one : (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 := by decide

theorem orbitMin_zero : TwistTag.E6.orbitMin ⟨0, by decide⟩ =
    (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank) := by decide +kernel

theorem orbitMin_one : TwistTag.E6.orbitMin ⟨1, by decide⟩ =
    (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) := by decide +kernel

theorem perm_zero : TwistTag.E6.perm (0 : Fin TwistTag.E6.tag.rank) =
    (⟨5, by decide⟩ : Fin TwistTag.E6.tag.rank) := by decide +kernel

theorem perm_two : TwistTag.E6.perm (⟨2, by decide⟩ : Fin TwistTag.E6.tag.rank) =
    (⟨4, by decide⟩ : Fin TwistTag.E6.tag.rank) := by decide +kernel

theorem mem_orbitField_pair (hK : Nat.card K = 4) (hσ : ∀ c : K, σ c = c ^ 2)
    (a : Fin TwistTag.E6.foldedTag.rank) (ha : (TwistTag.E6.orbit a).card = 2) (c : K) :
    c ∈ orbitField TwistTag.E6 K σ.toRingHom a := by
  rw [mem_orbitField, ha]
  show (σ.toRingHom ^ 2) c = c
  rw [pow_two, RingHom.mul_def, RingHom.comp_apply]
  show σ (σ c) = c
  rw [hσ, hσ, ← pow_mul]
  exact pow4_eq hK c

theorem coe_orbitX_zero (c : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩) :
    (orbitX TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨0, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨5, by decide⟩ (σ c) := by
  rw [coe_orbitX, card_orbit_zero, orbitMin_zero]
  simp [List.range_succ, pow_succ, perm_zero]

theorem coe_orbitX_one (c : orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩) :
    (orbitX TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.E6.tag K) =
      xUnit TwistTag.E6.tag K ⟨2, by decide⟩ c * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ (σ c) := by
  rw [coe_orbitX, card_orbit_one, orbitMin_one]
  simp [List.range_succ, pow_succ, perm_two]

end Omega

section Alphabet

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2] [CharP K 2]
  (σ : K ≃+* K)

noncomputable def Xw0 (hK : Nat.card K = 4) (hσ : ∀ c : K, σ c = c ^ 2) (ω : K) :
    twistedE6RootGroup K σ :=
  oX σ ⟨0, by decide⟩ ⟨ω, mem_orbitField_pair σ hK hσ _ card_orbit_zero ω⟩

noncomputable def Xw1 (hK : Nat.card K = 4) (hσ : ∀ c : K, σ c = c ^ 2) (ω : K) :
    twistedE6RootGroup K σ :=
  oX σ ⟨1, by decide⟩ ⟨ω, mem_orbitField_pair σ hK hσ _ card_orbit_one ω⟩

theorem hasBits2_Xw0 (hK : Nat.card K = 4) (hσ : ∀ c : K, σ c = c ^ 2) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : HasBits2 K ω (tmat (Xw0 σ hK hσ ω)) (letterBits2 8) := by
  have h : tmat (Xw0 σ hK hσ ω) = xUnit Tag.E6 K (E6Bits.idx 0) ω * xUnit Tag.E6 K (E6Bits.idx 5) (ω ^ 2) := by
    show (orbitX TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ _ : ModGL TwistTag.E6.tag K) = _
    rw [coe_orbitX_zero]
    show xUnit TwistTag.E6.tag K ⟨0, by decide⟩ ω * xUnit TwistTag.E6.tag K ⟨5, by decide⟩ (σ ω) = _
    rw [hσ ω]
    rfl
  rw [h]
  have e : letterBits2 8 = Bits2.mul (xw1 0) (xw2 5) := by simp [letterBits2]
  rw [e]
  exact (hasBits2_xUnit_omega hω 0).mul hω (hasBits2_xUnit_omega_sq hω 5)

theorem hasBits2_Xw1 (hK : Nat.card K = 4) (hσ : ∀ c : K, σ c = c ^ 2) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) : HasBits2 K ω (tmat (Xw1 σ hK hσ ω)) (letterBits2 9) := by
  have h : tmat (Xw1 σ hK hσ ω) = xUnit Tag.E6 K (E6Bits.idx 2) ω * xUnit Tag.E6 K (E6Bits.idx 4) (ω ^ 2) := by
    show (orbitX TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ _ : ModGL TwistTag.E6.tag K) = _
    rw [coe_orbitX_one]
    show xUnit TwistTag.E6.tag K ⟨2, by decide⟩ ω * xUnit TwistTag.E6.tag K ⟨4, by decide⟩ (σ ω) = _
    rw [hσ ω]
    rfl
  rw [h]
  have e : letterBits2 9 = Bits2.mul (xw1 2) (xw2 4) := by simp [letterBits2]
  rw [e]
  exact (hasBits2_xUnit_omega hω 2).mul hω (hasBits2_xUnit_omega_sq hω 4)

end Alphabet

section Closing

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2] [CharP K 2]
  (σ : K ≃+* K)

structure Setup (k K : Type) [Field k] [Field K] [Algebra k K] (σ : K ≃+* K) where
  ω : K
  hω : ω ^ 2 + ω + 1 = 0
  hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c
  hK : Nat.card K = 4
  hσ : ∀ c : K, σ c = c ^ 2

variable (S : Setup k K σ)

noncomputable def eltT (c : ℕ) : twistedE6RootGroup K σ :=
  if c < 8 then iota σ S.hfix ((CFSG.RankThree.PartOne.SEITZX.letterOfCode c).elt k)
  else if c = 8 then Xw0 σ S.hK S.hσ S.ω else Xw1 σ S.hK S.hσ S.ω

theorem hasBits2_eltT (c : ℕ) : HasBits2 K S.ω (tmat (eltT σ S c)) (letterBits2 c) := by
  unfold eltT
  by_cases h1 : c < 8
  · rw [if_pos h1]
    have hb : E6Bits.HasBits k (embE6F4 k ((CFSG.RankThree.PartOne.SEITZX.letterOfCode c).elt k))
        (codeBits6 (f4ToE6Letter c)) := by
      rw [iota_letter h1]
      exact E6Bits.hasBits_evalG _
    have := hasBits2_iota σ S.hfix S.ω hb
    simpa [letterBits2, h1] using this
  · rw [if_neg h1]
    by_cases h2 : c = 8
    · subst h2
      rw [if_pos rfl]
      exact hasBits2_Xw0 σ S.hK S.hσ S.hω
    · rw [if_neg h2]
      have e : letterBits2 c = letterBits2 9 := by simp [letterBits2, h1, h2]
      rw [e]
      exact hasBits2_Xw1 σ S.hK S.hσ S.hω

end Closing

section Generation

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2] [CharP K 2]
  (σ : K ≃+* K) (S : Setup k K σ)

theorem oX_zero (a : Fin TwistTag.E6.foldedTag.rank) : oX σ a 0 = 1 := by
  apply Subtype.ext
  show (orbitX TwistTag.E6 K σ.toRingHom a 0 : ModGL TwistTag.E6.tag K) = 1
  rw [orbitX_zero]
  rfl

theorem oX_add (a : Fin TwistTag.E6.foldedTag.rank) (c c' : orbitField TwistTag.E6 K σ.toRingHom a) :
    oX σ a (c + c') = oX σ a c * oX σ a c' := by
  apply Subtype.ext
  show (orbitX TwistTag.E6 K σ.toRingHom a (c + c') : ModGL TwistTag.E6.tag K) = _
  rw [orbitX_add]
  rfl

theorem oX_mem (Sg : Subgroup (twistedE6RootGroup K σ))
    (hrange : ∀ x ∈ (iota σ S.hfix).range, x ∈ Sg)
    (hX0 : Xw0 σ S.hK S.hσ S.ω ∈ Sg) (hX1 : Xw1 σ S.hK S.hσ S.ω ∈ Sg)
    (a : Fin TwistTag.E6.foldedTag.rank) (c : orbitField TwistTag.E6 K σ.toRingHom a) :
    oX σ a c ∈ Sg := by
  have hone : ∀ (a : Fin TwistTag.E6.foldedTag.rank) (hc : (1 : K) ∈ orbitField TwistTag.E6 K σ.toRingHom a),
      oX σ a ⟨1, hc⟩ ∈ Sg := fun a hc =>
    hrange _ (oXY_mem_range σ S.hfix a ⟨1, hc⟩ ⟨1, by simp⟩).1
  have hω2 : S.ω ^ 2 = S.ω + 1 := by rw [sq]; exact sq_eq_of_root S.hω
  have hcases := eq_zero_one_omega S.hK S.hω (c : K)
  have fixed_case : ∀ (a' : Fin TwistTag.E6.foldedTag.rank)
      (c' : orbitField TwistTag.E6 K σ.toRingHom a'), σ (c' : K) = c' → oX σ a' c' ∈ Sg := by
    intro a' c' hfixc
    have hsq : (c' : K) ^ 2 = c' := by rw [← S.hσ]; exact hfixc
    have hc01 : (c' : K) = 0 ∨ (c' : K) = 1 := by
      have : (c' : K) * ((c' : K) - 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    rcases hc01 with h | h
    · have : c' = 0 := Subtype.ext h
      rw [this, oX_zero]; exact one_mem _
    · have : c' = ⟨1, by rw [← h]; exact c'.2⟩ := Subtype.ext h
      rw [this]; exact hone _ _
  obtain ⟨a, ha⟩ := a
  have ha4 : a < 4 := ha
  interval_cases a
  ·
    rcases hcases with h | h | h | h
    · have : c = 0 := Subtype.ext h
      rw [this, oX_zero]; exact one_mem _
    · have : c = ⟨1, by rw [← h]; exact c.2⟩ := Subtype.ext h
      rw [this]; exact hone _ _
    · have : c = ⟨S.ω, mem_orbitField_pair σ S.hK S.hσ _ card_orbit_zero S.ω⟩ := Subtype.ext h
      rw [this]; exact hX0
    · have : c = ⟨S.ω, mem_orbitField_pair σ S.hK S.hσ _ card_orbit_zero S.ω⟩ +
          ⟨1, mem_orbitField_pair σ S.hK S.hσ _ card_orbit_zero 1⟩ :=
        Subtype.ext (by rw [h, hω2]; rfl)
      rw [this, oX_add]
      exact mul_mem hX0 (hone _ _)
  ·
    rcases hcases with h | h | h | h
    · have : c = 0 := Subtype.ext h
      rw [this, oX_zero]; exact one_mem _
    · have : c = ⟨1, by rw [← h]; exact c.2⟩ := Subtype.ext h
      rw [this]; exact hone _ _
    · have : c = ⟨S.ω, mem_orbitField_pair σ S.hK S.hσ _ card_orbit_one S.ω⟩ := Subtype.ext h
      rw [this]; exact hX1
    · have : c = ⟨S.ω, mem_orbitField_pair σ S.hK S.hσ _ card_orbit_one S.ω⟩ +
          ⟨1, mem_orbitField_pair σ S.hK S.hσ _ card_orbit_one 1⟩ :=
        Subtype.ext (by rw [h, hω2]; rfl)
      rw [this, oX_add]
      exact mul_mem hX1 (hone _ _)
  ·
    refine fixed_case _ c ?_
    have := mem_orbitField.1 c.2
    rwa [card_orbit_two, pow_one] at this
  ·
    refine fixed_case _ c ?_
    have := mem_orbitField.1 c.2
    rwa [card_orbit_three, pow_one] at this

end Generation

section Plane

theorem closure_conj_eq_top_gen {G : Type*} [Group G] (R : Subgroup G) (k : G) (hk : k ∈ R) (z : G)
    (h : Subgroup.closure ((R : Set G) ∪ (Subgroup.centralizer ({z} : Set G) : Set G)) = ⊤) :
    Subgroup.closure ((R : Set G) ∪ (Subgroup.centralizer ({k⁻¹ * z * k} : Set G) : Set G)) = ⊤ := by
  classical
  set M := Subgroup.closure ((R : Set G) ∪ (Subgroup.centralizer ({k⁻¹ * z * k} : Set G) : Set G))
    with hM
  have hconj : ∀ x ∈ Subgroup.closure ((R : Set G) ∪
      (Subgroup.centralizer ({z} : Set G) : Set G)), k⁻¹ * x * k ∈ M := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hxR | hxC
      · apply Subgroup.subset_closure
        left
        have : k⁻¹ * x * k ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hk) hxR) hk
        exact this
      · apply Subgroup.subset_closure
        right
        simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
          forall_eq] at hxC ⊢
        calc k⁻¹ * z * k * (k⁻¹ * x * k) = k⁻¹ * (z * x) * k := by group
          _ = k⁻¹ * (x * z) * k := by rw [hxC]
          _ = (k⁻¹ * x * k) * (k⁻¹ * z * k) := by group
    | one => simp
    | mul x y _ _ hx hy =>
      have : k⁻¹ * (x * y) * k = (k⁻¹ * x * k) * (k⁻¹ * y * k) := by group
      rw [this]
      exact M.mul_mem hx hy
    | inv x _ hx =>
      have : k⁻¹ * x⁻¹ * k = (k⁻¹ * x * k)⁻¹ := by group
      rw [this]
      exact M.inv_mem hx
  rw [eq_top_iff]
  intro y _
  have hy : k * y * k⁻¹ ∈ Subgroup.closure ((R : Set G) ∪
      (Subgroup.centralizer ({z} : Set G) : Set G)) := by
    rw [h]
    exact Subgroup.mem_top _
  have := hconj _ hy
  have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  rwa [e] at this

end Plane

section Statement

def TwCloseAtTwo : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (k : Type) [Field k] [Finite k] [Algebra k K]
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c),
    Nat.card K = 2 ^ 2 → (∀ c : K, σ c = c ^ 2) → Nat.card k = 2 →
    ∀ E₃ : Subgroup (adjointGroup .F4 k), (∀ x ∈ E₃, x ^ 3 = 1) → Nat.card E₃ = 3 ^ 2 →
      ∃ e ∈ E₃, e ≠ 1 ∧ Subgroup.closure
        ((((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom).range :
            Set (twistedE6RootGroup K σ)) ∪
          (Subgroup.centralizer
            ({((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom) e} :
              Set (twistedE6RootGroup K σ)) : Set (twistedE6RootGroup K σ))) = ⊤

end Statement

section Main

end Main

end CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Two
