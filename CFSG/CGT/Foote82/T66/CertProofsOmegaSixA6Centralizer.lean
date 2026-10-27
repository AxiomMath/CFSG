module

public import CFSG.CGT.Foote82.T66.CitedBB
public import CFSG.CGT.Foote82.T66.OmegaSixModel
public import Certificates.Certificate919004
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.Timmesfeld.Orders.ClassicalOrthogonal
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.ClassicalInvolution.Sp62Rec.Z6NA
  CFSG.RankThree.PartTwo Equiv
open scoped commutatorElement

theorem reflCheck_holds : reflCheck () = true :=
  Certificates.certificate919004.1

theorem oEnumCheck_holds : oEnumCheck () = true :=
  Certificates.certificate919004.2.1

theorem classCheck_holds : classCheck () = true :=
  Certificates.certificate919004.2.2.2.1

theorem centCheck_holds : centCheck () = true :=
  Certificates.certificate919004.2.2.2.2

theorem reflCheck_spec :
    isomB rMat = true ∧ rMat * rMat = 1 ∧ rAMat * rAMat = 1 ∧ rBMat * rBMat = 1 := by
  have h := reflCheck_holds
  simp only [reflCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

@[expose] def rGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨rMat, rMat, reflCheck_spec.2.1, reflCheck_spec.2.1⟩

@[expose] def rAGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨rAMat, rAMat, reflCheck_spec.2.2.1, reflCheck_spec.2.2.1⟩

@[expose] def rBGL : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  ⟨rBMat, rBMat, reflCheck_spec.2.2.2, reflCheck_spec.2.2.2⟩

theorem rGL_mem :
    rGL ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 :=
  mem_orthogonalMinus_of_isomB reflCheck_spec.1

theorem card_orthogonalMinus_two :
    Nat.card ↥(CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1) = 51840 := by
  have hQ := CFSG.LieType.Universal.Spin.coe_quadMinus 3 (ZMod 2) (1 : ZMod 2) 1
  have hO := (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus (K := ZMod 2) 2
    Sec19.SimsTheoremC.irreducible_one_one).2
  rw [Nat.card_zmod] at hO
  have h1 : CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 =
      (TauCeti.QuadraticMap.orthogonalGroup
        (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) (1 : ZMod 2) 1)).comap
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 2)).toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hQ
  rw [h1, show ∀ H : Subgroup ((Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2)),
      H.comap (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 2)).toMonoidHom =
        H.map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 2)).symm.toMonoidHom from
      fun H => Subgroup.comap_equiv_eq_map_symm
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) H,
    Nat.card_congr (Subgroup.equivMapOfInjective _ _
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv _ (ZMod 2)).symm.injective).symm.toEquiv]
  have : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 2) (1 : ZMod 2) 1)) : ℤ) = 51840 := by
    rw [hO]
    decide
  exact_mod_cast this

@[expose] def genOGL (i : ℕ) :
    GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  if i = 0 then aGL else if i = 1 then bGL else rGL

theorem genO_size : (genO ()).size = 3 := rfl

theorem genO_get :
    ∀ j < (genO ()).size, (genO ())[j]! = glCode (genOGL j) := by
  intro j hj
  rw [genO_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

theorem genOInv_get :
    ∀ j < (genO ()).size, (genOInv ())[j]! = glCode (genOGL j)⁻¹ := by
  intro j hj
  rw [genO_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> rfl

theorem closure_genOGL_le :
    Subgroup.closure (genOGL '' Set.Iio (genO ()).size) ≤
      CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [Set.mem_Iio, genO_size] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · exact omegaMinusTwo_le_orthogonalMinus aGL_mem
  · exact omegaMinusTwo_le_orthogonalMinus bGL_mem
  · exact rGL_mem

theorem oEnum_spec :
    enumOK (oEnum ()) (genO ()) = true ∧ (oEnum ()).elems.size = 51840 := by
  have h := oEnumCheck_holds
  simp only [oEnumCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem closure_genO :
    Subgroup.closure (genOGL '' Set.Iio (genO ()).size) =
      CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 := by
  have hcard := card_closure_eq_of_enumOK isArrCode_glCode genO_get oEnum_spec.1
  rw [oEnum_spec.2] at hcard
  refine Subgroup.eq_of_le_of_card_ge closure_genOGL_le ?_
  rw [hcard, card_orthogonalMinus_two]

theorem exists_oEnum
    {t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (ht : t ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1) :
    ∃ k < (oEnum ()).elems.size, (oEnum ()).elems[k]! = glCode t := by
  rw [← closure_genO] at ht
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
    (lookup_isSome_of_mem_closure isArrCode_glCode genO_get oEnum_spec.1 ht)
  exact ⟨k, Enum.lookup_spec hk⟩

theorem exists_omegaEnum {y : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hy : y ∈ omegaMinusTwo 2) :
    ∃ k < (omegaEnum ()).elems.size, (omegaEnum ()).elems[k]! = glCode y := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (lookup_glArr_isSome ⟨y, hy⟩)
  exact ⟨k, Enum.lookup_spec hk⟩

theorem exists_conj_rep
    {X : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)} (hX : X ∈ omegaMinusTwo 2) (hX2 : X * X = 1)
    (hX1 : X ≠ 1) :
    ∃ g ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1, g * rAGL * g⁻¹ = X ∨ g * rBGL * g⁻¹ = X := by
  have h := classCheck_holds
  simp only [classCheck, Bool.and_eq_true, Array.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, beq_eq_false_iff_ne] at h
  obtain ⟨⟨hA, hB⟩, hall⟩ := h
  obtain ⟨k, hk, hke⟩ := exists_omegaEnum hX
  have hx := hall k hk
  rw [← getElem!_pos, hke] at hx
  have hsq : compA (glCode X) (glCode X) = idA () := by
    rw [← isArrCode_glCode.mul, hX2, isArrCode_glCode.one]
  have hne : glCode X ≠ idA () := by
    rw [← isArrCode_glCode.one]
    exact fun h => hX1 (isArrCode_glCode.injective h)
  rcases hx with ((hx | hx) | hx) | hx
  · exact absurd hsq hx
  · exact absurd hx hne
  · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨his, hie⟩ := Enum.lookup_spec hi
    obtain ⟨g, hg, hge⟩ := exists_conj_of_conjTreeOK isArrCode_glCode genO_get genOInv_get
      (x := rAGL) hA i his
    exact ⟨g, closure_genOGL_le hg, Or.inl (isArrCode_glCode.injective (hge.trans hie))⟩
  · obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hx
    obtain ⟨his, hie⟩ := Enum.lookup_spec hi
    obtain ⟨g, hg, hge⟩ := exists_conj_of_conjTreeOK isArrCode_glCode genO_get genOInv_get
      (x := rBGL) hB i his
    exact ⟨g, closure_genOGL_le hg, Or.inr (isArrCode_glCode.injective (hge.trans hie))⟩

theorem cvec_ne_zero {c : ℕ} (hc : c < 64) (hc0 : c ≠ 0) : cvec c ≠ 0 := by
  intro h
  have := vcode_cvec c hc
  rw [h] at this
  exact hc0 (this.symm.trans (by decide))

theorem sub_one_mulVec_cvec (t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) {k : ℕ} (hk : k < 64) :
    ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1) *ᵥ cvec k =
      cvec ((glCode t)[k]! ^^^ k) := by
  rw [sub_mulVec, one_mulVec, cvec_xor, glCode, ← mulVec_cvec _ hk]
  exact (isVecCode.add_eq_sub _ _).symm

theorem rank_sub_one_of_rank1 {t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (h : rank1 (glCode t) = true) :
    ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1).rank = 1 := by
  simp only [rank1, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨c, hc, ⟨hc0, k, hk, hkc⟩, hall⟩ := h
  have hrange : LinearMap.range (mulVecLin
      ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1)) =
      Submodule.span (ZMod 2) {cvec c} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [mulVecLin_apply, ← cvec_vcode v, sub_one_mulVec_cvec t (vcode_lt v)]
      rcases hall (vcode v) (vcode_lt v) with h0 | h1
      · rw [h0, isVecCode.vec_zero]
        exact Submodule.zero_mem _
      · rw [h1]
        exact Submodule.subset_span rfl
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨cvec k, by rw [mulVecLin_apply, sub_one_mulVec_cvec t hk, hkc]⟩
  rw [Matrix.rank, hrange]
  exact finrank_span_singleton (K := ZMod 2) (cvec_ne_zero hc hc0)

theorem rank_conj_sub_one (g t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    (((g * t * g⁻¹ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1).rank =
      ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1).rank := by
  have hg : IsUnit (g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have hg' : IsUnit ((g⁻¹ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp g⁻¹.isUnit
  have h : ((g * t * g⁻¹ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1 =
      (g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *
        ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1) *
        ((g⁻¹ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Units.val_mul, ← Units.val_mul,
      Units.mul_inv]
  rw [h, rank_mul_eq_left_of_isUnit_det _ _ hg', rank_mul_eq_right_of_isUnit_det _ _ hg]

@[expose] def a6x : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, by
    rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    decide⟩

@[expose] def a6y : alternatingGroup (Fin 6) :=
  ⟨swap 0 4 * swap 0 2 * swap 0 1 * swap 3 5, by
    rw [Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, Perm.sign_swap (by decide),
      Perm.sign_swap (by decide), Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
    decide⟩

@[expose] def a6s (i : ℕ) : alternatingGroup (Fin 6) := if i = 0 then a6x else a6y

theorem a6Rels_hold : ∀ w ∈ a6Rels, (w.map a6s).prod = 1 := by
  decide +kernel

theorem a6x_mul_self : a6x * a6x = 1 := by
  decide +kernel

theorem a6x_ne_one : a6x ≠ 1 := by
  decide +kernel

theorem rank_of_centCheck
    {x y t : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)} (hx : x = rAGL ∨ x = rBGL)
    (hy : y ∈ omegaMinusTwo 2)
    (hrel : ∀ w ∈ a6Rels, (w.map fun i => if i = 0 then x else y).prod = 1)
    (ht : t ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1) (ht1 : t ≠ 1)
    (htx : t * x = x * t) (hty : t * y = y * t) :
    ((t : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) - 1).rank = 1 := by
  apply rank_sub_one_of_rank1
  have h := centCheck_holds
  unfold centCheck at h
  rw [List.all_eq_true] at h
  have hxm : glCode x ∈ [marr rAMat, marr rBMat] := by
    rcases hx with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
  have h1 := h _ hxm
  simp only [Array.all_eq_true_iff_forall_mem, Bool.or_eq_true, Bool.not_eq_true'] at h1
  obtain ⟨k, hk, hke⟩ := exists_omegaEnum hy
  have h2 := h1 (glCode y) (by rw [← hke, getElem!_pos _ k hk]; exact Array.getElem_mem hk)
  have hwords : (a6Rels.all fun w => wordA #[glCode x, glCode y] w == idA ()) = true := by
    rw [List.all_eq_true]
    intro w hw
    rw [beq_iff_eq, ← arr_prod_map isArrCode_glCode (s := fun i => if i = 0 then x else y) w,
      hrel w hw, isArrCode_glCode.one]
    intro i hi
    have hi2 : i < 2 := by
      revert i
      revert w
      decide
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
  rw [hwords] at h2
  replace h2 := h2.resolve_left (by decide)
  obtain ⟨k', hk', hk'e⟩ := exists_oEnum ht
  have hmem : glCode t ∈ (oEnum ()).elems.filter fun s =>
      compA s (glCode x) == compA (glCode x) s && !(s == idA ()) := by
    rw [Array.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [← hk'e, getElem!_pos _ k' hk']
      exact Array.getElem_mem hk'
    · rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
        ← isArrCode_glCode.mul, ← isArrCode_glCode.mul, htx, ← isArrCode_glCode.one]
      exact ⟨rfl, fun h => ht1 (isArrCode_glCode.injective h)⟩
  have h3 := h2 _ hmem
  rw [beq_eq_false_iff_ne, ← isArrCode_glCode.mul, ← isArrCode_glCode.mul, hty] at h3
  exact h3.resolve_left (fun h => h rfl)

end CFSG.CGT.Foote82.OmegaSix

namespace CFSG.CGT.Foote82

open Matrix OmegaSix CFSG.RankThree.PartTwo

theorem omegaMinusSixA6Centralizer_holds :
    OmegaMinusSixA6Centralizer := by
  intro A hA ⟨φ⟩ t ht ht1 htA
  set X : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
    ((φ.symm a6x : ↥A) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) with hXdef
  set Y : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
    ((φ.symm a6y : ↥A) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) with hYdef
  have hX : X ∈ omegaMinusTwo 2 := hA (φ.symm a6x).2
  have hY : Y ∈ omegaMinusTwo 2 := hA (φ.symm a6y).2
  have hX2 : X * X = 1 := by
    rw [hXdef, ← Subgroup.coe_mul, ← map_mul, a6x_mul_self, map_one, Subgroup.coe_one]
  have hX1 : X ≠ 1 := by
    intro h
    apply a6x_ne_one
    apply φ.symm.injective
    rw [map_one]
    exact Subtype.ext h
  obtain ⟨g, hg, hgX⟩ := exists_conj_rep hX hX2 hX1
  have hginv := inv_mem hg
  have hrel : ∀ w ∈ a6Rels,
      (w.map fun i => if i = 0 then g⁻¹ * X * g else g⁻¹ * Y * g).prod = 1 := by
    intro w hw
    let f : alternatingGroup (Fin 6) →* GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
      (MulAut.conj g⁻¹).toMonoidHom.comp (A.subtype.comp φ.symm.toMonoidHom)
    have hf : ∀ z, f z = g⁻¹ * ((φ.symm z : A) : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) * g :=
      fun z => by
        simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
          MulAut.conj_apply, inv_inv]
    have hw' : (w.map fun i => if i = 0 then g⁻¹ * X * g else g⁻¹ * Y * g) =
        (w.map a6s).map f := by
      rw [List.map_map]
      refine List.map_congr_left fun i _ => ?_
      rw [Function.comp_apply, hf, a6s]
      split_ifs <;> rfl
    rw [hw', ← map_list_prod, a6Rels_hold w hw, map_one]
  have hY' : g⁻¹ * Y * g ∈ omegaMinusTwo 2 := by
    have := conj_mem_omegaMinusTwo hginv hY
    rwa [inv_inv] at this
  have ht' : g⁻¹ * t * g ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 :=
    mul_mem (mul_mem hginv ht) hg
  have ht1' : g⁻¹ * t * g ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun z => g * z * g⁻¹) h
    simpa [mul_assoc] using this
  have htX : t * X = X * t := htA _ (φ.symm a6x).2
  have htY : t * Y = Y * t := htA _ (φ.symm a6y).2
  have hcomm : ∀ z, t * z = z * t → (g⁻¹ * t * g) * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (g⁻¹ * t * g) := by
    intro z hz
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc t, hz, mul_assoc]
  have hx : g⁻¹ * X * g = rAGL ∨ g⁻¹ * X * g = rBGL := by
    rcases hgX with h | h
    · left
      rw [← h]
      group
    · right
      rw [← h]
      group
  have hrank := rank_of_centCheck hx hY' hrel ht' ht1' (hcomm X htX) (hcomm Y htY)
  have h := rank_conj_sub_one g (g⁻¹ * t * g)
  rw [show g * (g⁻¹ * t * g) * g⁻¹ = t by group, hrank] at h
  exact h
end CFSG.CGT.Foote82
