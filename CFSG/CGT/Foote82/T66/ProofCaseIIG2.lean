module

public import CFSG.CGT.Foote82.T66.CitedCaseII
public import Certificates.Certificate919101
import CFSG.CGT.Foote82.T66.MC2Arith
import CFSG.CGT.Foote82.T66.CertProofsOmegaSixA6Centralizer

public section

namespace CFSG.CGT.Foote82

namespace CaseIIG2Aux

open Matrix Equiv CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA
  CFSG.CGT.Foote82.OmegaSix CFSG.RankThree.PartTwo CFSG.PGLModel
open scoped commutatorElement

private theorem exists_mem_closure_of_autOK {K : Type*} [Group K] {cd' : K → Array ℕ}
    (hc' : IsArrCode cd') {E : Enum} {gs hs F : Array (Array ℕ)} {h : ℕ → K}
    (hhs : ∀ j < gs.size, hs[j]! = cd' (h j)) (htree : treeOK E gs = true)
    (haut : autOK E gs hs F = true) :
    ∀ i < E.elems.size, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size), cd' m = F[i]! := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at htree
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true] at haut
  obtain ⟨-, hall⟩ := htree
  obtain ⟨⟨⟨⟨-, hF0⟩, hFt⟩, -⟩, -⟩ := haut
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases hall i hi with rfl | ⟨⟨hp, hg⟩, -⟩
    · exact ⟨1, one_mem _, by rw [hc'.one, getElem!_eq_of_getElem? hF0]⟩
    · rcases hFt i hi with hi0 | hFi
      · subst hi0
        exact ⟨1, one_mem _, by rw [hc'.one, getElem!_eq_of_getElem? hF0]⟩
      · obtain ⟨m, hm, hme⟩ := ih _ hp (hp.trans hi)
        refine ⟨m * h E.gen[i]!, mul_mem hm (Subgroup.subset_closure ⟨_, hg, rfl⟩), ?_⟩
        rw [hc'.mul, hme, ← hhs _ hg, hFi]

private theorem exists_hom_of_autOK {H K : Type*} [Group H] [Finite H] [Group K]
    {cd : H → Array ℕ} {cd' : K → Array ℕ} (hc : IsArrCode cd) (hc' : IsArrCode cd')
    {E : Enum} {gs hs F : Array (Array ℕ)} {s : ℕ → H} {h : ℕ → K}
    (hgs : ∀ j < gs.size, gs[j]! = cd (s j)) (hhs : ∀ j < gs.size, hs[j]! = cd' (h j))
    (henum : enumOK E gs = true) (haut : autOK E gs hs F = true) :
    ∃ φ : ↥(Subgroup.closure (s '' Set.Iio gs.size)) →* K, Function.Injective φ ∧
      ∀ x, φ x ∈ Subgroup.closure (h '' Set.Iio gs.size) := by
  set L := Subgroup.closure (s '' Set.Iio gs.size)
  have htree : treeOK E gs = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.1.1
  have hnodup : nodupOK E = true := by
    simp only [enumOK, Bool.and_eq_true] at henum
    exact henum.2
  have hFw := exists_mem_closure_of_autOK hc' hhs htree haut
  have haut' := haut
  simp only [autOK, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at haut'
  obtain ⟨⟨⟨⟨hsize, hF0⟩, -⟩, hcrit⟩, hinj⟩ := haut'
  have hpos : ∀ x ∈ L, ∃ k, E.lookup (cd x) = some k :=
    fun x hx => Option.isSome_iff_exists.mp (lookup_isSome_of_mem_closure hc hgs henum hx)
  have hex : ∀ x ∈ L, ∃ m ∈ Subgroup.closure (h '' Set.Iio gs.size),
      cd' m = appF E F (cd x) := by
    intro x hx
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨m, hm, hme⟩ := hFw k (Enum.lookup_spec hk).1
    exact ⟨m, hm, by rw [hme, appF, hk, Option.getD_some]⟩
  obtain ⟨f, hf, hfm⟩ : ∃ f : H → K,
      (∀ x ∈ L, cd' (f x) = appF E F (cd x)) ∧
        ∀ x ∈ L, f x ∈ Subgroup.closure (h '' Set.Iio gs.size) := by
    classical
    refine ⟨fun x => if hx : ∃ m, cd' m = appF E F (cd x) then hx.choose else 1, ?_, ?_⟩
    · intro x hx
      obtain ⟨m, -, hme⟩ := hex x hx
      have hx' : ∃ m, cd' m = appF E F (cd x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      exact hx'.choose_spec
    · intro x hx
      obtain ⟨m, hm, hme⟩ := hex x hx
      have hx' : ∃ m, cd' m = appF E F (cd x) := ⟨m, hme⟩
      simp only [dif_pos hx']
      rw [hc'.injective (hx'.choose_spec.trans hme.symm)]
      exact hm
  have hf1 : f 1 = 1 := by
    apply hc'.injective
    rw [hf 1 (one_mem _), hc'.one, appF]
    have h0 : E.elems[0]? = some (idA ()) := by
      simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
      exact htree.1
    have := (allLt_iff.mp hnodup) 0 (size_pos_of_getElem? h0)
    rw [decide_eq_true_eq, getElem!_eq_of_getElem? h0] at this
    rw [hc.one, this, Option.getD_some, getElem!_eq_of_getElem? hF0]
  have hstep : ∀ x ∈ L, ∀ j < gs.size, f (x * s j) = f x * h j := by
    intro x hx j hj
    obtain ⟨k, hk⟩ := hpos x hx
    obtain ⟨hks, hke⟩ := Enum.lookup_spec hk
    have hc0 := hcrit k hks j hj
    rw [hke, hgs j hj, ← hc.mul] at hc0
    apply hc'.injective
    rw [hf _ (mul_mem hx (Subgroup.subset_closure ⟨j, hj, rfl⟩)), hc'.mul (f x) (h j),
      hf x hx, appF, appF, hk, Option.getD_some, ← hhs j hj]
    split at hc0
    · rename_i k' hk'
      rw [hk', Option.getD_some]
      exact of_decide_eq_true hc0
    · cases hc0
  have hgen : ∀ j < gs.size, f (s j) = h j := by
    intro j hj
    have := hstep 1 (one_mem _) j hj
    rwa [one_mul, hf1, one_mul] at this
  have hmulf := map_mul_of_forall_mem hf1 (S := s '' Set.Iio gs.size) (by
    rintro x hx _ ⟨j, hj, rfl⟩
    rw [hstep x hx j hj, hgen j hj])
  have hinj' : ∀ i < F.size, (firstIndex F)[F[i]!]? = some i := by
    unfold injOK at hinj
    simpa only [allLt_iff, decide_eq_true_eq] using hinj
  let φ : L →* K :=
    { toFun := fun x => f x
      map_one' := hf1
      map_mul' := fun x y => hmulf y y.2 x x.2 }
  refine ⟨φ, fun x y hxy => ?_, fun x => hfm x x.2⟩
  have hxy' : f x = f y := hxy
  obtain ⟨k, hk⟩ := hpos x x.2
  obtain ⟨k', hk'⟩ := hpos y y.2
  have e := congrArg cd' hxy'
  rw [hf x x.2, hf y y.2, appF, appF, hk, hk', Option.getD_some, Option.getD_some] at e
  have hks := (Enum.lookup_spec hk).1
  have hks' := (Enum.lookup_spec hk').1
  have i1 := hinj' k (by rw [hsize]; exact hks)
  have i2 := hinj' k' (by rw [hsize]; exact hks')
  rw [e] at i1
  have hkk : k = k' := Option.some.inj (i1.symm.trans i2)
  subst hkk
  exact Subtype.ext (hc.injective ((Enum.lookup_spec hk).2.symm.trans (Enum.lookup_spec hk').2))

private theorem permArr_get {n : ℕ} (σ : Perm (Fin n)) {i : ℕ} (hi : i < 64) :
    (permArr σ)[i]! = if h : i < n then (σ ⟨i, h⟩).val else i :=
  getElem!_ofFn_nat _ hi

private theorem isArrCode_permArr {n : ℕ} (hn : n ≤ 64) : IsArrCode (permArr (n := n)) where
  mul σ τ := by
    refine ext64 Array.size_ofFn (size_compA _ _) fun i hi => ?_
    rw [compA_get _ _ hi]
    by_cases h : i < n
    · have hτ : (τ ⟨i, h⟩).val < 64 := lt_of_lt_of_le (τ ⟨i, h⟩).isLt hn
      rw [permArr_get _ hi, permArr_get τ hi, dif_pos h, dif_pos h, permArr_get σ hτ,
        dif_pos (τ ⟨i, h⟩).isLt]
      rfl
    · rw [permArr_get _ hi, permArr_get τ hi, dif_neg h, dif_neg h, permArr_get σ hi, dif_neg h]
  one := by
    refine ext64 Array.size_ofFn size_idA fun i hi => ?_
    rw [permArr_get _ hi, idA_get hi]
    split_ifs <;> rfl
  injective σ τ h := by
    ext i
    have := congrArg (fun a : Array ℕ => a[i.val]!) h
    simp only [permArr_get _ (lt_of_lt_of_le i.isLt hn), dif_pos i.isLt] at this
    exact this

private theorem factorization_two (a m : ℕ) (hm : ¬ 2 ∣ m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hm0, Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

private theorem card_alternatingGroup_ten :
    Nat.card (alternatingGroup (Fin 10)) = 2 ^ 7 * 14175 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem card_alternatingGroup_eight :
    Nat.card (alternatingGroup (Fin 8)) = 2 ^ 6 * 315 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private noncomputable def sylowOfCard {G : Type*} [Group G] [Finite G] {a m : ℕ} (hm : ¬ 2 ∣ m)
    (hG : Nat.card G = 2 ^ a * m) (S : Subgroup G) (hS : Nat.card S = 2 ^ a) : Sylow 2 G :=
  Sylow.ofCard S (by rw [hS, hG, factorization_two a m hm])

section Checks


theorem pEnumCheck_holds : pEnumCheck () = true := Certificates.certificate919101.1

theorem pAutCheck_holds : pAutCheck () = true := Certificates.certificate919101.2.1

theorem qEnumCheck_holds : qEnumCheck () = true := Certificates.certificate919101.2.2.1

theorem qAutCheck_holds : qAutCheck () = true := Certificates.certificate919101.2.2.2

end Checks

section Orthogonal

private theorem pInvol_spec : pMat1 * pMat1 = 1 ∧ pMat2 * pMat2 = 1 ∧ pMat3 * pMat3 = 1 := by
  decide +kernel

private theorem pIsom_spec : isomB pMat1 = true ∧ isomB pMat2 = true ∧ isomB pMat3 = true := by
  decide +kernel

private def pGL (j : ℕ) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  if j = 0 then ⟨pMat1, pMat1, pInvol_spec.1, pInvol_spec.1⟩
  else if j = 1 then ⟨pMat2, pMat2, pInvol_spec.2.1, pInvol_spec.2.1⟩
  else ⟨pMat3, pMat3, pInvol_spec.2.2, pInvol_spec.2.2⟩

private def tPerm (j : ℕ) : Perm (Fin 10) :=
  if j = 0 then tPerm1 else if j = 1 then tPerm2 else tPerm3

private theorem genP_size : (genP ()).size = 3 := rfl

private theorem genP_get : ∀ j < (genP ()).size, (genP ())[j]! = glCode (pGL j) := by
  intro j hj
  rw [genP_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

private theorem genT_get : ∀ j < (genP ()).size, (genT ())[j]! = permArr (tPerm j) := by
  intro j hj
  rw [genP_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

private theorem closure_pGL_le :
    Subgroup.closure (pGL '' Set.Iio (genP ()).size) ≤ orthogonalMinus 2 (ZMod 2) 1 1 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  unfold pGL
  split_ifs
  · exact mem_orthogonalMinus_of_isomB pIsom_spec.1
  · exact mem_orthogonalMinus_of_isomB pIsom_spec.2.1
  · exact mem_orthogonalMinus_of_isomB pIsom_spec.2.2

private theorem closure_tPerm_le :
    Subgroup.closure (tPerm '' Set.Iio (genP ()).size) ≤ alternatingGroup (Fin 10) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
  unfold tPerm
  split_ifs
  · decide
  · decide
  · decide

private theorem card_closure_pGL :
    Nat.card (Subgroup.closure (pGL '' Set.Iio (genP ()).size)) = 128 := by
  have h := pEnumCheck_holds
  simp only [pEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [card_closure_eq_of_enumOK isArrCode_glCode genP_get h.1, h.2]

theorem exists_sylow_orthogonalMinus :
    ∃ (P : Sylow 2 ↥(orthogonalMinus 2 (ZMod 2) 1 1)) (Q : Sylow 2 ↥(alternatingGroup (Fin 10))),
      Nonempty (↥P ≃* ↥Q) := by
  have haut := pAutCheck_holds
  simp only [pAutCheck] at haut
  have henum := pEnumCheck_holds
  simp only [pEnumCheck, Bool.and_eq_true, beq_iff_eq] at henum
  obtain ⟨φ, hφ, hmem⟩ := exists_hom_of_autOK isArrCode_glCode (isArrCode_permArr (by norm_num))
    genP_get genT_get henum.1 haut
  have hle : φ.range ≤ alternatingGroup (Fin 10) := by
    rintro _ ⟨x, rfl⟩
    exact closure_tPerm_le (hmem x)
  have hcardR : Nat.card φ.range = 128 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, card_closure_pGL]
  refine ⟨sylowOfCard (a := 7) (m := 405) (by decide) (card_orthogonalMinus_two.trans (by norm_num))
      ((Subgroup.closure (pGL '' Set.Iio (genP ()).size)).subgroupOf
        (orthogonalMinus 2 (ZMod 2) 1 1)) ?_,
    sylowOfCard (a := 7) (m := 14175) (by decide) card_alternatingGroup_ten
      (φ.range.subgroupOf (alternatingGroup (Fin 10))) ?_, ⟨?_⟩⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe closure_pGL_le).toEquiv, card_closure_pGL]
    norm_num
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardR]
    norm_num
  · exact (Subgroup.subgroupOfEquivOfLe closure_pGL_le).trans
      ((MonoidHom.ofInjective hφ).trans (Subgroup.subgroupOfEquivOfLe hle).symm)

end Orthogonal

section Omega

private theorem qInv_spec :
    (cMat1 * cMat1 = 1 ∧ cMat2 * cMat2 = 1 ∧ cMat3 * cMat3 = 1) ∧
      (dMat1 * dInvMat1 = 1 ∧ dInvMat1 * dMat1 = 1) ∧
      (dMat2 * dInvMat2 = 1 ∧ dInvMat2 * dMat2 = 1) ∧
      (dMat3 * dInvMat3 = 1 ∧ dInvMat3 * dMat3 = 1) := by
  decide +kernel

private theorem qIsom_spec :
    (isomB cMat1 = true ∧ isomB cMat2 = true ∧ isomB cMat3 = true) ∧
      isomB dMat1 = true ∧ isomB dMat2 = true ∧ isomB dMat3 = true := by
  decide +kernel

private def cGL (j : ℕ) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  if j = 0 then ⟨cMat1, cMat1, qInv_spec.1.1, qInv_spec.1.1⟩
  else if j = 1 then ⟨cMat2, cMat2, qInv_spec.1.2.1, qInv_spec.1.2.1⟩
  else ⟨cMat3, cMat3, qInv_spec.1.2.2, qInv_spec.1.2.2⟩

private def dGL (j : ℕ) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  if j = 0 then ⟨dMat1, dInvMat1, qInv_spec.2.1.1, qInv_spec.2.1.2⟩
  else if j = 1 then ⟨dMat2, dInvMat2, qInv_spec.2.2.1.1, qInv_spec.2.2.1.2⟩
  else ⟨dMat3, dInvMat3, qInv_spec.2.2.2.1, qInv_spec.2.2.2.2⟩

private def qGL (j : ℕ) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) := ⁅cGL j, dGL j⁆

private def uPerm (j : ℕ) : Perm (Fin 8) :=
  if j = 0 then uPerm1 else if j = 1 then uPerm2 else uPerm3

private theorem genQ_size : (genQ ()).size = 3 := rfl

private theorem genQ_get : ∀ j < (genQ ()).size, (genQ ())[j]! = glCode (qGL j) := by
  intro j hj
  rw [genQ_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

private theorem genU_get : ∀ j < (genQ ()).size, (genU ())[j]! = permArr (uPerm j) := by
  intro j hj
  rw [genQ_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

private theorem closure_qGL_le :
    Subgroup.closure (qGL '' Set.Iio (genQ ()).size) ≤ omegaMinusTwo 2 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  obtain ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩ := qIsom_spec
  have hc : cGL j ∈ orthogonalMinus 2 (ZMod 2) 1 1 := by
    unfold cGL
    split_ifs
    · exact mem_orthogonalMinus_of_isomB h1
    · exact mem_orthogonalMinus_of_isomB h2
    · exact mem_orthogonalMinus_of_isomB h3
  have hd : dGL j ∈ orthogonalMinus 2 (ZMod 2) 1 1 := by
    unfold dGL
    split_ifs
    · exact mem_orthogonalMinus_of_isomB h4
    · exact mem_orthogonalMinus_of_isomB h5
    · exact mem_orthogonalMinus_of_isomB h6
  exact Subgroup.commutator_mem_commutator hc hd

private theorem closure_uPerm_le :
    Subgroup.closure (uPerm '' Set.Iio (genQ ()).size) ≤ alternatingGroup (Fin 8) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  rw [SetLike.mem_coe, Perm.mem_alternatingGroup]
  unfold uPerm
  split_ifs
  · decide
  · decide
  · decide

private theorem card_closure_qGL :
    Nat.card (Subgroup.closure (qGL '' Set.Iio (genQ ()).size)) = 64 := by
  have h := qEnumCheck_holds
  simp only [qEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  rw [card_closure_eq_of_enumOK isArrCode_glCode genQ_get h.1, h.2]

theorem exists_sylow_omegaMinusTwo :
    ∃ (P : Sylow 2 ↥(omegaMinusTwo 2)) (Q : Sylow 2 ↥(alternatingGroup (Fin 8))),
      Nonempty (↥P ≃* ↥Q) := by
  have haut := qAutCheck_holds
  simp only [qAutCheck] at haut
  have henum := qEnumCheck_holds
  simp only [qEnumCheck, Bool.and_eq_true, beq_iff_eq] at henum
  obtain ⟨φ, hφ, hmem⟩ := exists_hom_of_autOK isArrCode_glCode (isArrCode_permArr (by norm_num))
    genQ_get genU_get henum.1 haut
  have hle : φ.range ≤ alternatingGroup (Fin 8) := by
    rintro _ ⟨x, rfl⟩
    exact closure_uPerm_le (hmem x)
  have hcardR : Nat.card φ.range = 64 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, card_closure_qGL]
  have hΩ : Nat.card ↥(omegaMinusTwo 2) = 2 ^ 6 * 405 :=
    MC2.card_omegaMinusTwo_two.trans (by norm_num)
  refine ⟨sylowOfCard (a := 6) (m := 405) (by decide) hΩ
      ((Subgroup.closure (qGL '' Set.Iio (genQ ()).size)).subgroupOf (omegaMinusTwo 2)) ?_,
    sylowOfCard (a := 6) (m := 315) (by decide) card_alternatingGroup_eight
      (φ.range.subgroupOf (alternatingGroup (Fin 8))) ?_, ⟨?_⟩⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe closure_qGL_le).toEquiv, card_closure_qGL]
    norm_num
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcardR]
    norm_num
  · exact (Subgroup.subgroupOfEquivOfLe closure_qGL_le).trans
      ((MonoidHom.ofInjective hφ).trans (Subgroup.subgroupOfEquivOfLe hle).symm)

end Omega

end CaseIIG2Aux

open CFSG.PGLModel CFSG.RankThree.PartTwo

theorem caseIIG2_holds : CaseIIG2 := by
  obtain ⟨P₀, Q₀, ⟨e⟩⟩ := CaseIIG2Aux.exists_sylow_orthogonalMinus
  obtain ⟨P₁, Q₁, ⟨e'⟩⟩ := CaseIIG2Aux.exists_sylow_omegaMinusTwo
  exact ⟨fun P Q => ⟨(Sylow.equiv P P₀).trans (e.trans (Sylow.equiv Q₀ Q))⟩,
    fun P Q => ⟨(Sylow.equiv P P₁).trans (e'.trans (Sylow.equiv Q₁ Q))⟩⟩

end CFSG.CGT.Foote82
