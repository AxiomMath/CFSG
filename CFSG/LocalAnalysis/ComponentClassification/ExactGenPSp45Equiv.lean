module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.ExactGen.PSp45Gens
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofPSp45Fact

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2.ExactPSp45

open Projectivization Matrix CFSG.Open CFSG.Adapters.RankTwoModelTransports CFSG.Monster.B.Co2
open scoped LinearAlgebra.Projectivization

@[expose] noncomputable def pspP : Subgroup (Equiv.Perm (Fin 156)) :=
  Subgroup.closure {CFSG.Monster.B.Co2.permOfArr 156 ExactGenData.psp45G1,
    CFSG.Monster.B.Co2.permOfArr 156 ExactGenData.psp45G2}

section Model

private instance factFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private def idx : Fin 2 ⊕ Fin 2 → ℕ
  | .inl i => (i : ℕ)
  | .inr i => 2 + (i : ℕ)

private abbrev Vec := Fin 2 ⊕ Fin 2 → ZMod 5

private def ptVec (n : ℕ) : Vec :=
  fun j => (((ExactGenData.psp45Pts[n]!)[idx j]! : ℕ) : ZMod 5)

private def tabMat (M : Array (Array ℕ)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  Matrix.of fun i j => (((M[idx i]!)[idx j]! : ℕ) : ZMod 5)

private def normIdx (v : Vec) : ℕ :=
  let a := v (.inl 0)
  let b := v (.inl 1)
  let c := v (.inr 0)
  let d := v (.inr 1)
  if a ≠ 0 then 31 + 25 * (a * a * a * b).val + 5 * (a * a * a * c).val + (a * a * a * d).val
  else if b ≠ 0 then 6 + 5 * (b * b * b * c).val + (b * b * b * d).val
  else if c ≠ 0 then 1 + (c * c * c * d).val
  else 0

private theorem ptVec_ne : ∀ n < 156, ptVec n ≠ 0 := by decide +kernel

private theorem normIdx_ptVec : ∀ i < 156, ∀ a : ZMod 5, a ≠ 0 → normIdx (a • ptVec i) = i := by
  decide +kernel

private theorem ptVec_inj {i j : ℕ} (hi : i < 156) (hj : j < 156) {a : ZMod 5}
    (h : a • ptVec j = ptVec i) : i = j := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact ptVec_ne i hi (by simpa using h.symm)
  have h1 := normIdx_ptVec j hj a ha
  have h2 := normIdx_ptVec i hi 1 one_ne_zero
  rw [h] at h1
  rw [one_smul] at h2
  exact h2.symm.trans h1

private theorem check1 : ∀ i < 156, ExactGenData.psp45G1[i]! < 156 ∧
    ∃ c : ZMod 5, c ≠ 0 ∧ c • ptVec ExactGenData.psp45G1[i]! =
      tabMat ExactGenData.psp45M1 *ᵥ ptVec i := by
  decide +kernel

private theorem check2 : ∀ i < 156, ExactGenData.psp45G2[i]! < 156 ∧
    ∃ c : ZMod 5, c ≠ 0 ∧ c • ptVec ExactGenData.psp45G2[i]! =
      tabMat ExactGenData.psp45M2 *ᵥ ptVec i := by
  decide +kernel

private theorem det1 : (tabMat ExactGenData.psp45M1).det ≠ 0 := by decide +kernel

private theorem det2 : (tabMat ExactGenData.psp45M2).det ≠ 0 := by decide +kernel

private theorem symp1 : (tabMat ExactGenData.psp45M1)ᵀ *
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) *
      tabMat ExactGenData.psp45M1 = fromBlocks 0 1 (-1) 0 := by decide +kernel

private theorem symp2 : (tabMat ExactGenData.psp45M2)ᵀ *
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) *
      tabMat ExactGenData.psp45M2 = fromBlocks 0 1 (-1) 0 := by decide +kernel

private noncomputable def gl1 : GL (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  GeneralLinearGroup.mkOfDetNeZero (tabMat ExactGenData.psp45M1) det1

private noncomputable def gl2 : GL (Fin 2 ⊕ Fin 2) (ZMod 5) :=
  GeneralLinearGroup.mkOfDetNeZero (tabMat ExactGenData.psp45M2) det2

private theorem gl1_coe : (gl1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
    tabMat ExactGenData.psp45M1 := rfl

private theorem gl2_coe : (gl2 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) =
    tabMat ExactGenData.psp45M2 := rfl

private theorem gl1_mem : gl1 ∈ StatedSp 2 (ZMod 5) := by
  rw [StatedAPI.mem_statedSp_iff, gl1_coe]
  exact symp1

private theorem gl2_mem : gl2 ∈ StatedSp 2 (ZMod 5) := by
  rw [StatedAPI.mem_statedSp_iff, gl2_coe]
  exact symp2

set_option backward.isDefEq.respectTransparency false

private noncomputable def ptFn (i : Fin 156) : ℙ (ZMod 5) Vec :=
  mk (ZMod 5) (ptVec i) (ptVec_ne i i.2)

private theorem ptFn_injective : Function.Injective ptFn := by
  intro i j h
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff' (ZMod 5) _ _ _ _).1 h
  exact Fin.ext (ptVec_inj i.2 j.2 ha)

private theorem card_proj : Nat.card (ℙ (ZMod 5) Vec) = 156 := by
  rw [Projectivization.card'', Nat.card_fun, Nat.card_zmod, Nat.card_sum]
  simp

private theorem ptFn_bijective : Function.Bijective ptFn := by
  have : Finite (ℙ (ZMod 5) Vec) := inferInstance
  exact ptFn_injective.bijective_of_nat_card_le (by rw [card_proj]; simp)

private noncomputable def ptEquiv : Fin 156 ≃ ℙ (ZMod 5) Vec :=
  Equiv.ofBijective ptFn ptFn_bijective

private noncomputable def actHom : GL (Fin 2 ⊕ Fin 2) (ZMod 5) →* Equiv.Perm (Fin 156) :=
  (ptEquiv.permCongrHom.symm :
    Equiv.Perm (ℙ (ZMod 5) Vec) ≃* Equiv.Perm (Fin 156)).toMonoidHom.comp
    (MulAction.toPermHom (GL (Fin 2 ⊕ Fin 2) (ZMod 5)) (ℙ (ZMod 5) Vec))

private theorem ptEquiv_actHom (g : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) (i : Fin 156) :
    ptEquiv (actHom g i) = g • ptEquiv i := by
  have : actHom g i = ptEquiv.symm (g • ptEquiv i) := rfl
  rw [this, Equiv.apply_symm_apply]

private theorem rep_actHom (M : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) (G : Array ℕ)
    (hG : ∀ i < 156, G[i]! < 156 ∧ ∃ c : ZMod 5, c ≠ 0 ∧ c • ptVec G[i]! =
      (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 5)) *ᵥ ptVec i) :
    Rep 156 G (actHom M) := by
  intro x
  obtain ⟨hlt, c, -, hc⟩ := hG x x.2
  have h : ptEquiv (actHom M x) = ptEquiv ⟨G[(x : ℕ)]!, hlt⟩ := by
    rw [ptEquiv_actHom]
    show M • mk (ZMod 5) (ptVec x) _ = mk (ZMod 5) (ptVec G[(x : ℕ)]!) _
    rw [smul_mk, mk_eq_mk_iff']
    exact ⟨c, hc⟩
  exact (congrArg Fin.val (ptEquiv.injective h)).symm

private theorem permOfArr_eq_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : Rep n t g) : permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => h.lt hi, fun i hi j hj hij => ?_⟩
    have h1 : g ⟨i, hi⟩ = g ⟨j, hj⟩ := Fin.ext ((h ⟨i, hi⟩).symm.trans (hij.trans (h ⟨j, hj⟩)))
    exact congrArg Fin.val (g.injective h1)
  rw [permOfArr, dif_pos hc]
  exact Equiv.ext fun x => Fin.ext (h x)

private theorem scalar_smul_vec (c : (ZMod 5)ˣ) (v : Vec) :
    GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c • v = (c : ZMod 5) • v := by
  funext j
  show ((GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c : Matrix _ _ (ZMod 5)) *ᵥ v) j = _
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mulVec_diagonal]
  simp

private theorem actHom_scalar (c : (ZMod 5)ˣ) :
    actHom (GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c) = 1 := by
  refine Equiv.ext fun i => ptEquiv.injective ?_
  rw [ptEquiv_actHom]
  show _ • mk (ZMod 5) (ptVec i) _ = mk (ZMod 5) (ptVec i) _
  rw [smul_mk, mk_eq_mk_iff']
  exact ⟨c, (scalar_smul_vec c _).symm⟩

private noncomputable def projAct :
    StatedProj (StatedSp 2 (ZMod 5)) →* Equiv.Perm (Fin 156) :=
  QuotientGroup.lift _ (actHom.comp (StatedSp 2 (ZMod 5)).subtype) (by
    intro x hx
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
    change actHom (x : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) = 1
    rw [← hc]
    exact actHom_scalar c)

private theorem projAct_mk (a : StatedSp 2 (ZMod 5)) :
    projAct (QuotientGroup.mk a) = actHom (a : GL (Fin 2 ⊕ Fin 2) (ZMod 5)) := rfl

private theorem psp45_equiv_zmod (hcard : Nat.card pspP = 4680000) :
    Nonempty (StatedProj (StatedSp 2 (ZMod 5)) ≃* pspP) := by
  have hG : Nat.card (StatedProj (StatedSp 2 (ZMod 5))) = 4680000 :=
    CFSG.RankThree.PartTwo.Sec21.Item221ResProof.PSp45.card_psp (by simp)
  haveI : Finite (StatedProj (StatedSp 2 (ZMod 5))) := Nat.finite_of_card_ne_zero (by omega)
  have hle : pspP ≤ projAct.range := by
    rw [pspP, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine ⟨QuotientGroup.mk ⟨gl1, gl1_mem⟩, ?_⟩
      rw [projAct_mk]
      exact (permOfArr_eq_of_rep (rep_actHom gl1 _ (by rw [gl1_coe]; exact check1))).symm
    · refine ⟨QuotientGroup.mk ⟨gl2, gl2_mem⟩, ?_⟩
      rw [projAct_mk]
      exact (permOfArr_eq_of_rep (rep_actHom gl2 _ (by rw [gl2_coe]; exact check2))).symm
  have hrange : Nat.card projAct.range ≤ 4680000 := by
    rw [← hG]
    exact Nat.card_le_card_of_surjective _ projAct.rangeRestrict_surjective
  haveI : Finite projAct.range := Finite.of_surjective _ projAct.rangeRestrict_surjective
  have heq : pspP = projAct.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard]; exact hrange)
  have hbij : Function.Bijective projAct.rangeRestrict :=
    projAct.rangeRestrict_surjective.bijective_of_nat_card_le (by rw [hG, ← heq]; exact hcard.ge)
  exact ⟨(MulEquiv.ofBijective projAct.rangeRestrict hbij).trans
    (MulEquiv.subgroupCongr heq.symm)⟩

end Model

theorem psp45_equiv (hcard : Nat.card pspP = 4680000) (S : Type) [Group S]
    (h : Blueprint.LieModel S .PSp 2 5 1) : Nonempty (S ≃* pspP) := by
  have hB : StatedClassicalModel S .PSp 2 5 1 :=
    Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  obtain ⟨-, K, _, _, hK, ⟨eS⟩⟩ := hB
  obtain ⟨eP⟩ := psp45_equiv_zmod hcard
  haveI : Fintype K := Fintype.ofFinite K
  have hKK : Fintype.card K = Fintype.card (ZMod 5) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, Nat.card_zmod]
    norm_num
  let eK : K ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq hKK
  exact ⟨eS.trans ((statedProjCongr (glCongr eK) (glCongr_statedSp eK 2)
    (glCongr_statedScalars eK)).trans eP)⟩

end CFSG.ComponentClassification.SolMax.SwapP2.ExactPSp45
