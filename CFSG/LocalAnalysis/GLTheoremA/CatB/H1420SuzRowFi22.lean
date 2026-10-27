module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowCent
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Shape

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Certificates CFSG.Monster.B.Fischer CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent CFSG.HardMathSupport.Dickson.I271

private theorem center_bot_of_equiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : Subgroup.center T = ⊥) : Subgroup.center T' = ⊥ := by
  rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]

section ClassA


theorem suzFi22_shapeRkAt_xP
    (hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥) :
    ShapeRkAt 3 (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) xP := by
  haveI := isSimpleGroup_lSub
  refine shapeRkAt_of_subgroup_data_solvable Nat.prime_three
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ e h => center_bot_of_equiv e h) fi22P xP lSub ?_
    lSub_normalized_cent isSimpleGroup_lSub nonabelian_lSub ?_ hcore (m := 6) ?_ (by norm_num)
    trivial (center_eq_bot_of_simple_nonab nonabelian_lSub)
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


theorem suzFi22_shapeRkAt_xRep_three :
    ShapeRkAt 3 (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) (xRep 3) := by
  haveI := finite_J_tab
  have hOP : OPrimeCoreTrivialAt 3 ↥fi22P :=
    @OPrimeCoreTrivialAt.of_mulEquiv 3 ↥fi22P _ ↥CFSG.Sporadic.Fi22.J inferInstance eJP.symm oPrimeCoreTrivialAt_Fi22J
  have hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥ :=
    (glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore 3 _).1 (hOP xP orderOf_xP)
  have hshape := suzFi22_shapeRkAt_xP hcore
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Subgroup.center T = ⊥ →
      Subgroup.center T' = ⊥ := fun _ _ _ _ e h => center_bot_of_equiv e h
  have hJ := @ShapeRkAt.of_equiv ↥fi22P ↥CFSG.Sporadic.Fi22.J _ _ inferInstance 3 Nat.prime_three
    (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) hGood hRk finite_J_tab eJP.symm xP hshape
  set t : CFSG.Sporadic.Fi22.J := eJP.symm xP with ht
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
  have h2 := @ShapeRkAt.of_equiv ↥CFSG.Sporadic.Fi22.J ↥CFSG.Sporadic.Fi22.J _ finite_J_tab inferInstance 3 Nat.prime_three
    (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) hGood hRk finite_J_tab (MulAut.conj c) t hJ
  rw [MulAut.conj_apply, hc] at h2
  exact h2

theorem suzFi22_centShapeRk :
    CentShapeRk 3 (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) CFSG.Sporadic.Fi22.J := by
  haveI := finite_J_tab
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Subgroup.center T = ⊥ →
      Subgroup.center T' = ⊥ := fun _ _ _ _ e h => center_bot_of_equiv e h
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨j, hj4, hconj⟩ := fi22_classify k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hsh : ShapeRkAt 3 (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) (xRep j) := by
    by_cases h3 : j = 3
    · subst h3
      exact suzFi22_shapeRkAt_xRep_three
    · exact Or.inl (tabFi22_pConstrained_xRep (by omega))
  have h := @ShapeRkAt.of_equiv ↥CFSG.Sporadic.Fi22.J ↥CFSG.Sporadic.Fi22.J _ finite_J_tab inferInstance 3 Nat.prime_three
    (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥) hGood hRk finite_J_tab
    (MulAut.conj c⁻¹) (xRep j) hsh
  have hk : (MulAut.conj c⁻¹) (xRep j) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

theorem suzFi22_centShapeRk_native :
    CentShapeRk 3 (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥)
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := by
  haveI := finite_J_tab
  haveI : Finite CFSG.Blueprint.NativeSporadic.Fi22 :=
    Finite.of_equiv CFSG.Sporadic.Fi22.J (CFSG.Sporadic.Fi22.fi22EquivJ.symm.toEquiv)
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Subgroup.center T = ⊥ →
      Subgroup.center T' = ⊥ := fun _ _ _ _ e h => center_bot_of_equiv e h
  exact @CentShapeRk.of_equiv ↥CFSG.Sporadic.Fi22.J CFSG.Blueprint.NativeSporadic.Fi22 inferInstance finite_J_tab
    inferInstance 3 Nat.prime_three (fun _ _ => True) (fun T _ => Subgroup.center T = ⊥)
    hGood hRk inferInstance CFSG.Sporadic.Fi22.fi22EquivJ.symm suzFi22_centShapeRk

theorem centRow_fi22 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CentRow .Fi22 fun (T : Type) [Group T] => Subgroup.center T = ⊥ := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) :=
    CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  exact centRow_of_centShapeRk hOut (hbr .Fi22).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ e h => center_bot_of_equiv e h)
    suzFi22_centShapeRk_native

end ClassAJ

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
