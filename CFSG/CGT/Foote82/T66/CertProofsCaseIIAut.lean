module

public import CFSG.CGT.Foote82.T66.CitedCaseII
public import CFSG.CGT.Foote82.T66.CertProofsOmegaSixA6Centralizer
public import Certificates.Certificate919150

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA
  CFSG.RankThree.PartTwo

theorem fiveCheck_holds : fiveCheck () = true :=
  Certificates.certificate919150.1

theorem pairCheck_holds : pairCheck () = true :=
  Certificates.certificate919150.2

theorem pow_five_eq_mul {M : Type*} [Monoid M] (y : M) : y ^ 5 = y * (y * (y * (y * y))) := by
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  simp only [mul_assoc]

theorem glCode_pow_five (y : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    glCode (y ^ 5) = compA (glCode y) (compA (glCode y) (compA (glCode y)
      (compA (glCode y) (glCode y)))) := by
  rw [← isArrCode_glCode.mul, ← isArrCode_glCode.mul, ← isArrCode_glCode.mul,
    ← isArrCode_glCode.mul, pow_five_eq_mul]

theorem getElem!_pair_zero (u v : Array ℕ) : (#[u, v] : Array (Array ℕ))[0]! = u := rfl

theorem getElem!_pair_one (u v : Array ℕ) : (#[u, v] : Array (Array ℕ))[1]! = v := rfl

theorem aGL_ne_one : aGL ≠ 1 := by
  intro h
  have h1 : ((aGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) (.inl 1) (.inl 0) = 1 := by
    show aMat (.inl 1) (.inl 0) = 1
    decide
  rw [h, Units.val_one] at h1
  exact absurd h1 (by decide)

theorem bGL_ne_one : bGL ≠ 1 := by
  intro h
  have h1 : ((bGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) (.inl 0) (.inl 0) = 0 := by
    show bMat (.inl 0) (.inl 0) = 0
    decide
  rw [h, Units.val_one] at h1
  exact absurd h1 (by decide)

theorem exists_conj_bGL
    {y : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hy : y ∈ omegaMinusTwo 2) (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) :
    ∃ g ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1, g * bGL * g⁻¹ = y := by
  have h := fiveCheck_holds
  simp only [fiveCheck, Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨hT, hall⟩ := h
  obtain ⟨k, hk, hke⟩ := exists_omegaEnum hy
  have hx := hall k hk
  rw [← getElem!_pos, hke] at hx
  have hne : (glCode y == idA ()) = false := by
    rw [beq_eq_false_iff_ne, ← isArrCode_glCode.one]
    exact fun h => hy1 (isArrCode_glCode.injective h)
  have hw : (compA (glCode y) (compA (glCode y) (compA (glCode y)
      (compA (glCode y) (glCode y)))) == idA ()) = true := by
    rw [beq_iff_eq, ← glCode_pow_five, hy5, isArrCode_glCode.one]
  rw [hne, hw, Bool.false_or, Bool.not_true, Bool.false_or] at hx
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨his, hie⟩ := Enum.lookup_spec hi
  obtain ⟨g, hg, hge⟩ := exists_conj_of_conjTreeOK isArrCode_glCode genO_get genOInv_get
    (x := bGL) hT i his
  exact ⟨g, closure_genOGL_le hg, isArrCode_glCode.injective (hge.trans hie)⟩

theorem exists_mem_of_oEnum
    {j : ℕ} (hj : j < (oEnum ()).elems.size) :
    ∃ t ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1, glCode t = (oEnum ()).elems[j]! := by
  have htree : treeOK (oEnum ()) (genO ()) = true := by
    have h := oEnum_spec.1
    simp only [enumOK, Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨t, ht, hte⟩ :=
    CFSG.ClassicalInvolution.Sp62Rec.Z6NA.exists_mem_closure_of_treeOK isArrCode_glCode genO_get
      htree j hj
  exact ⟨t, closure_genOGL_le ht, hte⟩

@[expose] def pairGen (x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))
    (i : ℕ) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  if i = 0 then x else bGL

theorem exists_conj_aGL
    {x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hx : x ∈ omegaMinusTwo 2) (hx1 : x ≠ 1)
    (hrel : ∀ w ∈ relators, (w.map (pairGen x)).prod = 1) :
    ∃ o ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1, o * bGL = bGL * o ∧
      o * aGL * o⁻¹ = x := by
  have h := pairCheck_holds
  simp only [pairCheck, Array.all_eq_true] at h
  obtain ⟨k, hk, hke⟩ := exists_omegaEnum hx
  have hxk := h k hk
  rw [← getElem!_pos, hke] at hxk
  have hne : (glCode x == idA ()) = false := by
    rw [beq_eq_false_iff_ne, ← isArrCode_glCode.one]
    exact fun h => hx1 (isArrCode_glCode.injective h)
  have hall : (relators.all fun w => wordA #[glCode x, marr bMat] w == idA ()) = true := by
    rw [List.all_eq_true]
    intro w hw
    rw [beq_iff_eq, ← arr_prod_map isArrCode_glCode (s := pairGen x) w fun i hi => ?_, hrel w hw,
      isArrCode_glCode.one]
    rcases (by have := relators_letters w hw i hi; omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [getElem!_pair_zero]
      rfl
    · rw [getElem!_pair_one]
      rfl
  rw [hne, hall, Bool.false_or, Bool.not_true, Bool.false_or, Array.any_eq_true'] at hxk
  obtain ⟨o', ho'C, hja⟩ := hxk
  rw [Array.mem_filter] at ho'C
  obtain ⟨ho'mem, hjb⟩ := ho'C
  obtain ⟨j, hj, hjo⟩ := Array.mem_iff_getElem.mp ho'mem
  obtain ⟨t, ht, hte⟩ := exists_mem_of_oEnum hj
  have hto : glCode t = o' := by
    rw [hte, getElem!_pos (oEnum ()).elems j hj, hjo]
  rw [beq_iff_eq] at hja hjb
  rw [← hto] at hja hjb
  have hb : t * bGL = bGL * t := by
    apply isArrCode_glCode.injective
    rw [isArrCode_glCode.mul, isArrCode_glCode.mul]
    exact hjb
  have ha : t * aGL = x * t := by
    apply isArrCode_glCode.injective
    rw [isArrCode_glCode.mul, isArrCode_glCode.mul]
    exact hja
  refine ⟨t, ht, hb, ?_⟩
  rw [ha, mul_inv_cancel_right]

end CFSG.CGT.Foote82.OmegaSix

namespace CFSG.CGT.Foote82

open Matrix OmegaSix CFSG.RankThree.PartTwo CFSG.ClassicalInvolution.Solomon73.Yamaki

theorem caseIIAut_holds :
    CaseIIAut := by
  intro θ
  have hθrel : ∀ w ∈ relators, (w.map fun i =>
      ((θ (gen6 i) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))).prod = 1 := by
    intro w hw
    have h1 := congrArg ((omegaMinusTwo 2).subtype.comp θ.toMonoidHom) (relators_spec w hw).2
    rw [map_list_prod, map_one, List.map_map] at h1
    exact h1
  have ha0 : ((gen6 0 : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = aGL := rfl
  have hb0 : ((gen6 1 : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) = bGL := rfl
  have hy5 : ((θ (gen6 1) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) ^ 5 = 1 := by
    have h := hθrel [1, 1, 1, 1, 1] (by decide)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
    rw [pow_five_eq_mul]
    exact h
  have hy1 : ((θ (gen6 1) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) ≠ 1 := by
    intro h
    have h2 : θ (gen6 1) = 1 := Subtype.ext h
    rw [map_eq_one_iff θ θ.injective] at h2
    exact bGL_ne_one (hb0.symm.trans (congrArg Subtype.val h2))
  have hx1 : ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) ≠ 1 := by
    intro h
    have h2 : θ (gen6 0) = 1 := Subtype.ext h
    rw [map_eq_one_iff θ θ.injective] at h2
    exact aGL_ne_one (ha0.symm.trans (congrArg Subtype.val h2))
  obtain ⟨g, hg, hgb⟩ := exists_conj_bGL (θ (gen6 1)).2 hy5 hy1
  have hx'mem : g⁻¹ * ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * g ∈
      omegaMinusTwo 2 := by
    have h := conj_mem_omegaMinusTwo (inv_mem hg) (θ (gen6 0)).2
    rwa [inv_inv] at h
  have hx'1 : g⁻¹ * ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * g ≠
      1 := by
    intro h
    apply hx1
    calc ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))
        = g * (g⁻¹ * ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * g) *
          g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hrel : ∀ w ∈ relators, (w.map (pairGen
      (g⁻¹ * ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * g))).prod =
      1 := by
    intro w hw
    have hcongr : ∀ i ∈ w, pairGen
        (g⁻¹ * ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * g) i =
        MulAut.conj g⁻¹
          ((θ (gen6 i) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) := by
      intro i hi
      rw [MulAut.conj_apply, inv_inv]
      rcases (by have := relators_letters w hw i hi; omega : i = 0 ∨ i = 1) with rfl | rfl
      · rfl
      · rw [← hgb]
        show bGL = _
        group
    have h3 := congrArg (MulAut.conj g⁻¹) (hθrel w hw)
    rw [map_list_prod, map_one, List.map_map] at h3
    rw [List.map_congr_left hcongr]
    exact h3
  obtain ⟨o, ho, hob, hoa⟩ := exists_conj_aGL hx'mem hx'1 hrel
  refine ⟨g * o, mul_mem hg ho, fun w => ?_⟩
  have hfg : (omegaMinusTwo 2).subtype.comp θ.toMonoidHom =
      (MulAut.conj (g * o)).toMonoidHom.comp (omegaMinusTwo 2).subtype := by
    refine MonoidHom.eq_of_eqOn_dense closure_gen6 ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_Iio] at hi
    show ((θ (gen6 i) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) =
      MulAut.conj (g * o) ((gen6 i : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))
    rw [MulAut.conj_apply]
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · rw [ha0]
      calc ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2))
          = g * (g⁻¹ * ((θ (gen6 0) : ↥(omegaMinusTwo 2)) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *
            g) * g⁻¹ := by group
        _ = g * (o * aGL * o⁻¹) * g⁻¹ := by rw [hoa]
        _ = g * o * aGL * (g * o)⁻¹ := by group
    · rw [hb0, ← hgb]
      calc g * bGL * g⁻¹ = g * (o * bGL * o⁻¹) * g⁻¹ := by rw [hob, mul_inv_cancel_right]
        _ = g * o * bGL * (g * o)⁻¹ := by group
  exact DFunLike.congr_fun hfg w

end CFSG.CGT.Foote82
