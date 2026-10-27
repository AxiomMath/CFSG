module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22L
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFiGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Small

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Certificates CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent

section ClassA

theorem nonempty_lSub_equiv : Nonempty (↥lSub ≃* CFSG.LieType.Multipliers.U43.X₀) := by
  have h := nonempty_mulEquiv_X₀_of_rels lGen rels_lGen (by rw [closure_lGen]; exact card_lSub)
  rw [closure_lGen] at h
  exact h

theorem isSimpleGroup_lSub : IsSimpleGroup ↥lSub := by
  obtain ⟨e⟩ := nonempty_lSub_equiv
  haveI := isSimpleGroup_X₀
  exact e.isSimpleGroup_congr.2 inferInstance

theorem nonabelian_lSub : ∃ a b : ↥lSub, a * b ≠ b * a := by
  obtain ⟨e⟩ := nonempty_lSub_equiv
  obtain ⟨a, b, hab⟩ := nonabelian_X₀
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem leafType_lSub : LeafType 3 ↥lSub := by
  obtain ⟨e⟩ := nonempty_lSub_equiv
  exact leafType_three_of_equiv_X₀ e

@[expose] noncomputable def xP : ↥fi22P := ⟨xPerm, xPerm_mem⟩

theorem shapeRkAt_xP
    (hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥) :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) xP := by
  refine shapeRkAt_of_subgroup_data_solvable Nat.prime_three
    (fun _ _ _ _ e h => LeafType.of_equiv e h) (fun _ _ _ _ _ h => h) fi22P xP lSub ?_
    lSub_normalized_cent isSimpleGroup_lSub nonabelian_lSub ?_ hcore (m := 6) ?_ (by norm_num)
    leafType_lSub trivial
  · intro l hl
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (lSub_comm_x l hl),
      ((mem_lev2_iff _).1 (lSub_le_lev2 hl)).1⟩
  · rw [card_lSub]; norm_num
  · refine card_cent_eq.trans ?_
    rw [card_lSub]

end ClassA

section ClassAJ

open CFSG.Sporadic.Fi22 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump
  CFSG.HardMathSupport.Dickson.I271.TabFi22Small

theorem orderOf_xP : orderOf xP = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext xPerm_pow_three
  · intro h
    exact xPerm_ne_one (congrArg Subtype.val h)

theorem fixCard_xPerm : fixCard xPerm = 126 := card_fix_xPerm

@[expose] noncomputable def eJP : J ≃* ↥fi22P :=
  MulEquiv.ofBijective (Fi22Copy.iotaJ.codRestrict fi22P Fi22Copy.iotaJ_mem)
    ⟨fun s t h => Fi22Copy.iotaJ_injective (congrArg Subtype.val h), fun Y => by
      obtain ⟨t, ht⟩ := exists_iotaJ_eq Y.2
      exact ⟨t, Subtype.ext ht⟩⟩

theorem eJP_apply (g : J) : ((eJP g : ↥fi22P) : Equiv.Perm (Fin 3510)) = Fi22Copy.iotaJ g := rfl

theorem shapeRkAt_xRep_three : ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (xRep 3) := by
  haveI := finite_J_tab
  have hOP : OPrimeCoreTrivialAt 3 ↥fi22P :=
    @OPrimeCoreTrivialAt.of_mulEquiv 3 ↥fi22P _ ↥J inferInstance eJP.symm oPrimeCoreTrivialAt_Fi22J
  have hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥ :=
    (glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore 3 _).1 (hOP xP orderOf_xP)
  have hshape := shapeRkAt_xP hcore
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hJ := @ShapeRkAt.of_equiv ↥fi22P ↥J _ _ inferInstance 3 Nat.prime_three (LeafType 3)
    (fun _ _ => True) hGood hRk finite_J_tab eJP.symm xP hshape
  set t : J := eJP.symm xP with ht
  have hord : orderOf t = 3 := by rw [MulEquiv.orderOf_eq]; exact orderOf_xP
  have hiota : Fi22Copy.iotaJ t = xPerm := by
    have h1 := eJP_apply t
    rw [ht, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  obtain ⟨k, hk4, hconj⟩ := fi22_classify t hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hfix : fixCard (Fi22Copy.iotaJ (xRep k)) = 126 := by
    rw [← hc, map_mul, map_mul, map_inv, hiota, fixCard_conj]
    exact fixCard_xPerm
  have hk3 : k = 3 := by
    have hf := Fi22Copy.fixN_xRep
    simp only [fixN_eq_card] at hf
    interval_cases k <;> omega
  subst hk3
  have h2 := @ShapeRkAt.of_equiv ↥J ↥J _ finite_J_tab inferInstance 3 Nat.prime_three
    (LeafType 3) (fun _ _ => True) hGood hRk finite_J_tab (MulAut.conj c) t hJ
  rw [MulAut.conj_apply, hc] at h2
  exact h2

theorem shapeRkAt_xRep {k : ℕ} (hk : k < 4) :
    ShapeRkAt 3 (LeafType 3) (fun _ _ => True) (xRep k) := by
  by_cases h3 : k = 3
  · subst h3
    exact shapeRkAt_xRep_three
  · exact Or.inl (tabFi22_pConstrained_xRep (by omega))

theorem centShapeRk_J : CentShapeRk 3 (LeafType 3) (fun _ _ => True) J := by
  haveI := finite_J_tab
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨j, hj4, hconj⟩ := fi22_classify k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := @ShapeRkAt.of_equiv ↥J ↥J _ finite_J_tab inferInstance 3 Nat.prime_three
    (LeafType 3) (fun _ _ => True) hGood hRk finite_J_tab (MulAut.conj c⁻¹) (xRep j)
    (shapeRkAt_xRep hj4)
  have hk : (MulAut.conj c⁻¹) (xRep j) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

theorem leafShape_Fi22 : LeafShape .Fi22 3 := by
  haveI := finite_J_tab
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi22 :=
    Finite.of_equiv J (CFSG.Sporadic.Fi22.fi22EquivJ.symm.toEquiv)
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → LeafType 3 T → LeafType 3 T' :=
    fun _ _ _ _ e h => LeafType.of_equiv e h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  exact CentShape.of_centShapeRk (@CentShapeRk.of_equiv ↥J CFSG.Blueprint.NativeSporadic.Fi22
    inferInstance finite_J_tab inferInstance 3 Nat.prime_three (LeafType 3) (fun _ _ => True)
    hGood hRk inferInstance CFSG.Sporadic.Fi22.fi22EquivJ.symm centShapeRk_J)

end ClassAJ

end CFSG.HardMathSupport.Dickson.I271
