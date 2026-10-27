module

public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.Monster.B.Geometry.F4Weyl

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem

section CoxeterMaps

variable {B B' : Type*} {M : CoxeterMatrix B} {M' : CoxeterMatrix B'} {W W' : Type*} [Group W]
  [Group W'] (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')

theorem map_wordProd_of_simple (φ : W →* W') (f : B → B')
    (hs : ∀ i, φ (cs.simple i) = cs'.simple (f i)) (ω : List B) :
    φ (cs.wordProd ω) = cs'.wordProd (ω.map f) := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, ih, hs, List.map_cons, CoxeterSystem.wordProd_cons]

theorem length_map_le_of_simple (φ : W →* W') (f : B → B')
    (hs : ∀ i, φ (cs.simple i) = cs'.simple (f i)) (w : W) : cs'.length (φ w) ≤ cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [map_wordProd_of_simple cs cs' φ f hs]
  calc cs'.length (cs'.wordProd (ω.map f)) ≤ (ω.map f).length := cs'.length_wordProd_le _
    _ = cs.length (cs.wordProd ω) := (List.length_map _).trans hω.symm

theorem length_map_of_simple (φ : W ≃* W') (e : B ≃ B')
    (hs : ∀ i, φ (cs.simple i) = cs'.simple (e i)) (w : W) : cs'.length (φ w) = cs.length w := by
  refine le_antisymm (length_map_le_of_simple cs cs' φ.toMonoidHom e hs w) ?_
  have hs' : ∀ j, φ.symm (cs'.simple j) = cs.simple (e.symm j) := fun j => by
    rw [MulEquiv.symm_apply_eq, hs, Equiv.apply_symm_apply]
  have h := length_map_le_of_simple cs' cs φ.symm.toMonoidHom e.symm hs' (φ w)
  rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h

@[expose] def coxeterSystemOfEq {M₁ M₂ : CoxeterMatrix B} (h : M₁ = M₂)
    (c : CoxeterSystem M₁ W) : CoxeterSystem M₂ W :=
  h ▸ c

theorem coxeterSystemOfEq_simple {M₁ M₂ : CoxeterMatrix B} (h : M₁ = M₂)
    (c : CoxeterSystem M₁ W) (i : B) : (coxeterSystemOfEq h c).simple i = c.simple i := by
  subst h
  rfl

end CoxeterMaps

theorem cartan_foldedTag_rev : ∀ a b : Fin TwistTag.E6.foldedTag.rank,
    TwistTag.E6.foldedTag.cartan (Fin.rev a) (Fin.rev b) *
        TwistTag.E6.foldedTag.cartan (Fin.rev b) (Fin.rev a) =
      TwistTag.E6.foldedTag.cartan a b * TwistTag.E6.foldedTag.cartan b a := by
  decide

theorem coxeterMatrix_foldedTag_rev
    (a b : Fin TwistTag.E6.foldedTag.rank) :
    (coxeterMatrix (isFiniteType_cartan TwistTag.E6.foldedTag)).M (Fin.rev a) (Fin.rev b) =
      (coxeterMatrix (isFiniteType_cartan TwistTag.E6.foldedTag)).M a b := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, cartan_foldedTag_rev]

theorem isLiftable_simple_rev :
    (coxeterMatrix (isFiniteType_cartan TwistTag.E6.foldedTag)).IsLiftable
      fun a => simple TwistTag.E6.foldedTag (Fin.rev a) := fun a b => by
  have h := (coxeterSystem TwistTag.E6.foldedTag).simple_mul_simple_pow (Fin.rev a) (Fin.rev b)
  rwa [coxeterMatrix_foldedTag_rev] at h

@[expose] def foldedRevHom
    : WeylGroup TwistTag.E6.foldedTag →* WeylGroup TwistTag.E6.foldedTag :=
  (coxeterSystem TwistTag.E6.foldedTag).lift
    ⟨fun a => simple TwistTag.E6.foldedTag (Fin.rev a), isLiftable_simple_rev⟩

theorem foldedRevHom_simple
    (a : Fin TwistTag.E6.foldedTag.rank) :
    foldedRevHom (simple TwistTag.E6.foldedTag a) = simple TwistTag.E6.foldedTag (Fin.rev a) :=
  (coxeterSystem TwistTag.E6.foldedTag).lift_apply_simple isLiftable_simple_rev a

theorem foldedRevHom_comp_foldedRevHom :
    foldedRevHom.comp foldedRevHom = MonoidHom.id (WeylGroup TwistTag.E6.foldedTag) :=
  (coxeterSystem TwistTag.E6.foldedTag).ext_simple fun a => by
    rw [MonoidHom.comp_apply, foldedRevHom_simple, foldedRevHom_simple, Fin.rev_rev,
      MonoidHom.id_apply]

@[expose] def foldedRev
    : WeylGroup TwistTag.E6.foldedTag ≃* WeylGroup TwistTag.E6.foldedTag :=
  MonoidHom.toMulEquiv foldedRevHom foldedRevHom foldedRevHom_comp_foldedRevHom
    foldedRevHom_comp_foldedRevHom

theorem foldedRev_simple
    (a : Fin TwistTag.E6.foldedTag.rank) :
    foldedRev (simple TwistTag.E6.foldedTag a) =
      (coxeterSystem TwistTag.E6.foldedTag).simple (Fin.revPerm a) :=
  foldedRevHom_simple a

@[expose] def nativeSimple
    (i : Fin 4) : relWeylTwist TwistTag.E6 :=
  ⟨TwistTag.E6.orbitReflection (foldedIndex i), TwistTag.E6.orbitReflection_mem _⟩

theorem coe_nativeSimple
    (i : Fin 4) :
    (nativeSimple i : WeylGroup TwistTag.E6.tag) = TwistTag.E6.orbitReflection (foldedIndex i) :=
  rfl

theorem coe_nativeSimple_eq_nativeRefl
    (i : Fin 4) :
    (nativeSimple i : WeylGroup TwistTag.E6.tag) = nativeRefl i :=
  (nativeRefl_eq i).symm

@[expose] def nativeIdx : Fin 4 ≃ Fin TwistTag.E6.foldedTag.rank :=
  finCongr rfl

theorem val_nativeIdx (i : Fin 4) : (nativeIdx i : ℕ) = i :=
  rfl

theorem rev_foldedIndex (i : Fin 4) : Fin.rev (foldedIndex i) = nativeIdx i := by
  fin_cases i <;> rfl

@[expose] def nativeWeylEquiv :
    relWeylTwist TwistTag.E6 ≃* WeylGroup TwistTag.E6.foldedTag :=
  (foldedWeylEquiv TwistTag.E6).trans foldedRev

theorem nativeWeylEquiv_apply
    (w : relWeylTwist TwistTag.E6) :
    nativeWeylEquiv w = foldedRev (foldedWeylEquiv TwistTag.E6 w) :=
  rfl

theorem nativeWeylEquiv_nativeSimple
    (i : Fin 4) :
    nativeWeylEquiv (nativeSimple i) =
      (coxeterSystem TwistTag.E6.foldedTag).simple (nativeIdx i) := by
  rw [nativeWeylEquiv_apply, nativeSimple, foldedWeylEquiv_orbitReflection, foldedRev_simple,
    Fin.revPerm_apply, rev_foldedIndex]

theorem coxeterMatrix_reindex_eq :
    (coxeterMatrix (isFiniteType_cartan TwistTag.E6.foldedTag)).reindex nativeIdx.symm =
      CoxeterMatrix.F₄ := by
  ext i j
  rw [CoxeterMatrix.reindex_apply, Equiv.symm_symm]
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    RootWalk.coxeterOrder_eq_braidLength]
  fin_cases i <;> fin_cases j <;> decide

@[expose] def nativeCoxeterSystem :
    CoxeterSystem CoxeterMatrix.F₄ (relWeylTwist TwistTag.E6) :=
  coxeterSystemOfEq coxeterMatrix_reindex_eq
    (((coxeterSystem TwistTag.E6.foldedTag).map nativeWeylEquiv.symm).reindex nativeIdx.symm)

theorem nativeCoxeterSystem_simple
    (i : Fin 4) : nativeCoxeterSystem.simple i = nativeSimple i := by
  rw [nativeCoxeterSystem, coxeterSystemOfEq_simple, CoxeterSystem.reindex_simple,
    CoxeterSystem.map_simple, Equiv.symm_symm, MulEquiv.symm_apply_eq,
    nativeWeylEquiv_nativeSimple]

theorem nativeWeylEquiv_simple
    (i : Fin 4) :
    nativeWeylEquiv (nativeCoxeterSystem.simple i) =
      (coxeterSystem TwistTag.E6.foldedTag).simple (nativeIdx i) := by
  rw [nativeCoxeterSystem_simple, nativeWeylEquiv_nativeSimple]

theorem length_nativeWeylEquiv
    (w : relWeylTwist TwistTag.E6) :
    (coxeterSystem TwistTag.E6.foldedTag).length (nativeWeylEquiv w) =
      nativeCoxeterSystem.length w :=
  length_map_of_simple _ _ nativeWeylEquiv nativeIdx nativeWeylEquiv_simple w

theorem nativeCoxeterSystem_length
    (w : relWeylTwist TwistTag.E6) :
    nativeCoxeterSystem.length w = TwistTag.E6.orbitLength w := by
  rw [← length_nativeWeylEquiv, nativeWeylEquiv_apply,
    length_map_of_simple _ _ foldedRev Fin.revPerm foldedRev_simple, orbitLength_eq]

theorem orderOf_nativeRefl_mul
    (i j : Fin 4) :
    orderOf (nativeRefl i * nativeRefl j) = CoxeterMatrix.F₄ i j := by
  have h := nativeCoxeterSystem.orderOf_simple_mul_simple i j
  rw [nativeCoxeterSystem_simple, nativeCoxeterSystem_simple, ← Subgroup.orderOf_coe,
    Subgroup.coe_mul, coe_nativeSimple_eq_nativeRefl, coe_nativeSimple_eq_nativeRefl] at h
  exact h

theorem card_relWeylTwist_E6 :
    Nat.card (relWeylTwist TwistTag.E6) = 1152 :=
  (Nat.card_congr nativeWeylEquiv.toEquiv).trans CFSG.Monster.B.Geometry.card_f4WeylGroup

end CFSG.LieType.Chevalley.C2E6Std
